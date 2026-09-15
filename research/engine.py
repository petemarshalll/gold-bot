"""
engine.py -- cost-aware, bar-based backtest engine for the gold research harness.

Conventions
- CSV prices are BID. Longs fill at ask (bid + spread), exit at bid.
  Shorts fill at bid, exit at ask. Spread comes from the CSV 'spread'
  column when populated (MT5 points * point_size), else from a
  per-session table in CostModel.
- All results are in R (multiples of initial risk), so they are
  account-size independent. R = (exit - entry) / |entry - stop|.
- If a bar touches both stop and target, the stop is assumed hit
  (pessimistic on purpose).
- One open position per strategy at a time.

Strategy interface: a strategy is any object with
    params: dict
    param_grid(): dict of {name: [values]} used by walk-forward
    generate(df) -> list[Signal]
where df is the M5 bid DataFrame (UTC index) and every Signal is
decided using only bars up to and including signal.time.
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field
from datetime import timedelta
from typing import Iterable

import numpy as np
import pandas as pd


# ---------------------------------------------------------------- data ----
def load_candles(path: str) -> pd.DataFrame:
    df = pd.read_csv(path, parse_dates=["time"])
    df["time"] = pd.to_datetime(df["time"], utc=True)
    df = df.drop_duplicates("time").set_index("time").sort_index()
    for c in ("open", "high", "low", "close"):
        df[c] = df[c].astype(float)
    if "spread" in df.columns:
        df["spread"] = pd.to_numeric(df["spread"], errors="coerce")
    return df


def resample(df: pd.DataFrame, rule: str) -> pd.DataFrame:
    """M5 -> any pandas offset ('15min', '1h', '1D'). Bars are labelled by open time."""
    o = df["open"].resample(rule, label="left", closed="left").first()
    h = df["high"].resample(rule, label="left", closed="left").max()
    l = df["low"].resample(rule, label="left", closed="left").min()
    c = df["close"].resample(rule, label="left", closed="left").last()
    out = pd.DataFrame({"open": o, "high": h, "low": l, "close": c}).dropna()
    return out


def atr(df: pd.DataFrame, n: int = 14) -> pd.Series:
    prev_close = df["close"].shift(1)
    tr = pd.concat([df["high"] - df["low"],
                    (df["high"] - prev_close).abs(),
                    (df["low"] - prev_close).abs()], axis=1).max(axis=1)
    return tr.rolling(n).mean()


# --------------------------------------------------------------- costs ----
@dataclass
class CostModel:
    """
    All values in price units (dollars per ounce for XAUUSD).
    Defaults are deliberately conservative for a retail 'XAUUSD.m' feed;
    replace session spreads with what you observe live on B.
    """
    spread_by_session: dict = field(default_factory=lambda: {
        "asian": 0.35, "london": 0.22, "ny": 0.20, "late": 0.45})
    point_size: float = 0.01          # MT5 'spread' field is in points
    use_csv_spread: bool = True
    commission_per_lot_rt: float = 7.0  # dollars, round turn
    contract_size: float = 100.0
    stop_slippage: float = 0.15        # extra adverse move when a stop fills
    entry_slippage: float = 0.05       # adverse fill vs intended entry for stop/market entries

    @staticmethod
    def session(ts: pd.Timestamp) -> str:
        h = ts.hour
        if 0 <= h < 7:
            return "asian"
        if 7 <= h < 13:
            return "london"
        if 13 <= h < 20:
            return "ny"
        return "late"

    def spread_at(self, ts: pd.Timestamp, bar: pd.Series) -> float:
        if self.use_csv_spread and "spread" in bar.index:
            s = bar["spread"]
            if s is not None and not (isinstance(s, float) and math.isnan(s)) and s > 0:
                return float(s) * self.point_size
        return self.spread_by_session[self.session(ts)]

    @property
    def commission_price_units(self) -> float:
        return self.commission_per_lot_rt / self.contract_size


# ------------------------------------------------------------- signals ----
@dataclass
class Signal:
    time: pd.Timestamp          # bar close time at which the decision is made
    direction: str              # 'LONG' | 'SHORT'
    entry: float                # intended entry (bid terms)
    stop: float
    target: float
    order_type: str = "stop"    # 'stop' (breakout), 'limit' (pullback), 'market'
    ttl_bars: int = 12          # cancel unfilled order after this many M5 bars
    exit_at: pd.Timestamp | None = None   # force-flat time (e.g. session end)
    meta: dict = field(default_factory=dict)

    @property
    def risk(self) -> float:
        return abs(self.entry - self.stop)


@dataclass
class Trade:
    signal: Signal
    fill_time: pd.Timestamp
    fill_price: float
    exit_time: pd.Timestamp
    exit_price: float
    exit_reason: str
    r: float
    session: str


# ---------------------------------------------------------- simulation ----
def _spread_array(df: pd.DataFrame, costs: CostModel) -> np.ndarray:
    hours = df.index.hour.values
    sess = np.where(hours < 7, costs.spread_by_session["asian"],
            np.where(hours < 13, costs.spread_by_session["london"],
             np.where(hours < 20, costs.spread_by_session["ny"], costs.spread_by_session["late"])))
    if costs.use_csv_spread and "spread" in df.columns:
        csv = pd.to_numeric(df["spread"], errors="coerce").values * costs.point_size
        return np.where(np.isnan(csv) | (csv <= 0), sess, csv)
    return sess


def simulate(df: pd.DataFrame, signals: Iterable[Signal], costs: CostModel,
             max_hold_bars: int = 288) -> list[Trade]:
    """
    Bar-by-bar fill simulation on the M5 DataFrame. Several pending
    orders may be live at once (e.g. a long and a short breakout on the
    same range); the first to fill cancels the others. One position at a
    time; signals that arrive while in a position are dropped.
    """
    signals = sorted(signals, key=lambda s: s.time)
    trades: list[Trade] = []
    idx = df.index
    n = len(df)
    O = df["open"].values; H = df["high"].values; L = df["low"].values; C = df["close"].values
    SPR = _spread_array(df, costs)
    # bar index at which each signal becomes live (first bar strictly after its decision bar)
    sig_live = idx.searchsorted([s.time for s in signals], side="right") if signals else []
    si = 0
    pending: list[tuple[Signal, int]] = []
    open_sig: Signal | None = None
    fill_px = fill_t = None
    bars_held = 0
    comm = costs.commission_price_units
    stop_slip, entry_slip = costs.stop_slippage, costs.entry_slippage

    i = int(sig_live[0]) if len(sig_live) else n
    while i < n:
        spr = SPR[i]
        o, h, l, c = O[i], H[i], L[i], C[i]

        # ---- activate signals whose decision bar has closed
        while si < len(signals) and sig_live[si] <= i:
            sig = signals[si]
            si += 1
            stale = (i - sig_live[si - 1]) > sig.ttl_bars
            if open_sig is not None or stale or sig.risk <= 0 or \
               sig.order_type not in ("stop", "limit", "market"):
                continue
            pending.append((sig, int(sig_live[si - 1]) + sig.ttl_bars))

        # ---- manage open position
        if open_sig is not None:
            long = open_sig.direction == "LONG"
            stop, target = open_sig.stop, open_sig.target
            exit_px = reason = None
            if long:
                if l <= stop:
                    exit_px, reason = stop - stop_slip, "stop"
                elif h >= target:
                    exit_px, reason = target, "target"
            else:
                if h + spr >= stop:
                    exit_px, reason = stop + stop_slip, "stop"
                elif l + spr <= target:
                    exit_px, reason = target, "target"
            bars_held += 1
            ts = idx[i]
            if exit_px is None and (
                (open_sig.exit_at is not None and ts >= open_sig.exit_at) or bars_held >= max_hold_bars):
                exit_px = c if long else c + spr
                reason = "time"
            if exit_px is not None:
                gross = (exit_px - fill_px) if long else (fill_px - exit_px)
                trades.append(Trade(open_sig, fill_t, fill_px, ts, exit_px, reason,
                                    (gross - comm) / open_sig.risk, costs.session(fill_t)))
                open_sig = None
            i += 1
            continue

        if not pending:
            # nothing live: jump to the next signal's activation bar
            i = int(sig_live[si]) if si < len(signals) else n
            continue

        # ---- try to fill pending orders on this bar
        still = []
        for sig, expiry in pending:
            if open_sig is not None:
                break
            long = sig.direction == "LONG"
            filled = None
            if sig.order_type == "market":
                filled = (o + spr + entry_slip) if long else (o - entry_slip)
            elif sig.order_type == "stop":
                if long and h + spr >= sig.entry:
                    filled = max(sig.entry, o + spr) + entry_slip
                elif not long and l <= sig.entry:
                    filled = min(sig.entry, o) - entry_slip
            else:
                if long and l + spr <= sig.entry:
                    filled = min(sig.entry, o + spr)
                elif not long and h >= sig.entry:
                    filled = max(sig.entry, o)
            if filled is not None:
                bad = (long and (filled <= sig.stop or filled >= sig.target)) or \
                      (not long and (filled >= sig.stop or filled <= sig.target))
                if bad:
                    continue
                ts = idx[i]
                open_sig = Signal(**{**sig.__dict__, "entry": filled - (spr if long else 0.0)})
                fill_px, fill_t, bars_held = filled, ts, 0
                same_bar_stop = (long and l <= sig.stop) or (not long and h + spr >= sig.stop)
                if same_bar_stop:
                    exit_px = (sig.stop - stop_slip) if long else (sig.stop + stop_slip)
                    gross = (exit_px - fill_px) if long else (fill_px - exit_px)
                    trades.append(Trade(open_sig, ts, fill_px, ts, exit_px, "stop",
                                        (gross - comm) / open_sig.risk, costs.session(ts)))
                    open_sig = None
            elif i < expiry:
                still.append((sig, expiry))
        pending = [] if open_sig is not None else still
        i += 1

    return trades


# ------------------------------------------------------------- metrics ----
def metrics(trades: list[Trade]) -> dict:
    if not trades:
        return {"n": 0, "win_rate": 0.0, "avg_r": 0.0, "total_r": 0.0, "profit_factor": 0.0,
                "max_dd_r": 0.0, "t_stat": 0.0, "r_per_month": 0.0}
    rs = np.array([t.r for t in trades])
    wins, losses = rs[rs > 0], rs[rs <= 0]
    eq = np.cumsum(rs)
    dd = np.max(np.maximum.accumulate(eq) - eq) if len(eq) else 0.0
    months = max(1.0, (trades[-1].exit_time - trades[0].fill_time).days / 30.44)
    t = rs.mean() / (rs.std(ddof=1) / math.sqrt(len(rs))) if len(rs) > 2 and rs.std(ddof=1) > 0 else 0.0
    return {
        "n": int(len(rs)),
        "win_rate": float((rs > 0).mean()),
        "avg_r": float(rs.mean()),
        "total_r": float(rs.sum()),
        "profit_factor": float(wins.sum() / -losses.sum()) if losses.sum() < 0 else float("inf"),
        "max_dd_r": float(dd),
        "t_stat": float(t),
        "r_per_month": float(rs.sum() / months),
    }


def by_key(trades: list[Trade], key) -> dict[str, dict]:
    groups: dict[str, list[Trade]] = {}
    for t in trades:
        groups.setdefault(key(t), []).append(t)
    return {k: metrics(v) for k, v in sorted(groups.items())}


# ---------------------------------------------------------- walk-forward ----
def _grid(param_grid: dict) -> list[dict]:
    if not param_grid:
        return [{}]
    keys = list(param_grid)
    out = [{}]
    for k in keys:
        out = [{**o, k: v} for o in out for v in param_grid[k]]
    return out


def run_strategy(strategy, df: pd.DataFrame, costs: CostModel, params: dict | None = None,
                 start=None, end=None) -> list[Trade]:
    if params:
        strategy = strategy.with_params(params)
    sub = df
    if start is not None or end is not None:
        sub = df.loc[start:end]
    signals = strategy.generate(sub)
    return simulate(sub, signals, costs)


def walk_forward(strategy, df: pd.DataFrame, costs: CostModel,
                 fit_months: int = 12, test_months: int = 3,
                 select_by: str = "total_r", min_fit_trades: int = 30) -> dict:
    """
    Roll a fit/test window across the data. In each fit window every
    grid combination is scored; the best is applied to the following
    test window. Returns the concatenated out-of-sample trades and the
    per-window log. This is the number to believe.
    """
    grid = _grid(strategy.param_grid())
    t0, t1 = df.index[0], df.index[-1]
    windows = []
    oos: list[Trade] = []
    fit_start = t0
    while True:
        fit_end = fit_start + pd.DateOffset(months=fit_months)
        test_end = fit_end + pd.DateOffset(months=test_months)
        if fit_end >= t1:
            break
        best, best_score, best_m = None, -float("inf"), None
        for p in grid:
            m = metrics(run_strategy(strategy, df, costs, p, fit_start, fit_end))
            if m["n"] < min_fit_trades:
                continue
            score = m[select_by] if m[select_by] != float("inf") else 1e9
            if score > best_score:
                best, best_score, best_m = p, score, m
        if best is None:
            windows.append({"fit_start": fit_start, "fit_end": fit_end, "params": None, "note": "too few fit trades"})
        else:
            test_trades = run_strategy(strategy, df, costs, best, fit_end, min(test_end, t1))
            oos.extend(test_trades)
            windows.append({"fit_start": fit_start, "fit_end": fit_end, "test_end": test_end,
                            "params": best, "fit": best_m, "test": metrics(test_trades)})
        fit_start = fit_start + pd.DateOffset(months=test_months)
    return {"oos_trades": oos, "oos": metrics(oos), "windows": windows}


def robustness(strategy, df: pd.DataFrame, costs: CostModel, params: dict, pct: float = 0.2) -> dict:
    """Perturb each numeric parameter by +/- pct and report avg_r. A real edge survives this."""
    base = metrics(run_strategy(strategy, df, costs, params))
    out = {"base": base, "perturbed": {}}
    for k, v in params.items():
        if not isinstance(v, (int, float)) or isinstance(v, bool):
            continue
        for sign in (-1, 1):
            nv = round(v * (1 + sign * pct), 4)
            if isinstance(v, int):
                nv = max(1, int(round(nv)))
                if nv == v:
                    nv = v + sign
            m = metrics(run_strategy(strategy, df, costs, {**params, k: nv}))
            out["perturbed"][f"{k}={nv}"] = {"avg_r": m["avg_r"], "n": m["n"], "profit_factor": m["profit_factor"]}
    return out


def regime_split(trades: list[Trade], df: pd.DataFrame) -> dict:
    """
    Tag each calendar month as 'trend' or 'range' by efficiency ratio on
    daily closes (net move / sum of abs daily moves), then report
    performance in each. An edge that only works in one regime needs a
    switch, not more parameters.
    """
    daily = resample(df, "1D")["close"]
    daily.index = daily.index.tz_localize(None)
    er = {}
    for month, s in daily.groupby(daily.index.to_period("M")):
        moves = s.diff().dropna()
        path = moves.abs().sum()
        er[str(month)] = abs(s.iloc[-1] - s.iloc[0]) / path if path > 0 else 0.0
    if not er:
        return {}
    median = float(np.median(list(er.values())))
    tag = {m: ("trend" if v >= median else "range") for m, v in er.items()}
    return by_key(trades, lambda t: tag.get(str(t.fill_time.tz_localize(None).to_period("M")), "unknown"))
