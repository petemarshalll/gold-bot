"""Strategy base class and the volatility-regime filter wrapper."""
from __future__ import annotations

import pandas as pd

from engine import Signal, atr, resample


class Strategy:
    name = "base"
    defaults: dict = {}

    def __init__(self, **params):
        self.params = {**self.defaults, **params}

    def with_params(self, params: dict) -> "Strategy":
        return self.__class__(**{**self.params, **params})

    def param_grid(self) -> dict:
        return {}

    def generate(self, df: pd.DataFrame) -> list[Signal]:
        raise NotImplementedError

    def describe(self) -> str:
        return f"{self.name} {self.params}"


class VolRegimeFilter(Strategy):
    """
    Wraps any strategy and only passes signals when H1 ATR sits inside a
    rolling percentile band. Tests the hypothesis 'this edge only works
    in normal volatility' without touching the inner strategy.
    """
    name = "vol_filter"
    defaults = {"atr_n": 14, "lookback_bars": 500, "p_low": 0.2, "p_high": 0.9}

    def __init__(self, inner: Strategy, **params):
        super().__init__(**params)
        self.inner = inner
        self.name = f"vol_filter({inner.name})"

    def with_params(self, params: dict) -> "VolRegimeFilter":
        mine = {k: v for k, v in params.items() if k in self.defaults}
        theirs = {k: v for k, v in params.items() if k not in self.defaults}
        return VolRegimeFilter(self.inner.with_params(theirs), **{**self.params, **mine})

    def param_grid(self) -> dict:
        return {**self.inner.param_grid(), "p_low": [0.1, 0.3], "p_high": [0.8, 0.95]}

    def generate(self, df: pd.DataFrame) -> list[Signal]:
        p = self.params
        h1 = resample(df, "1h")
        a = atr(h1, p["atr_n"])
        rank = a.rolling(p["lookback_bars"]).rank(pct=True)
        ok = rank.between(p["p_low"], p["p_high"])
        out = []
        for s in self.inner.generate(df):
            h = s.time.floor("1h")
            pos = ok.index.get_indexer([h], method="ffill")[0]
            if pos >= 0 and bool(ok.iloc[pos]):
                out.append(s)
        return out


class TrendGate(Strategy):
    """
    Real-time trend filter: passes LONG signals only when, as of the
    previous completed day, daily close is above EMA(`ema_days`), the
    EMA has risen over the last `slope_days`, and the trailing
    `er_days` efficiency ratio (net move / path length) is at least
    `er_min`. Mirror for SHORT. Uses only past bars, unlike the
    diagnostic monthly regime split in the report.
    """
    name = "trend_gate"
    defaults = {"ema_days": 20, "slope_days": 5, "er_days": 20, "er_min": 0.25, "allow": "BOTH"}

    def __init__(self, inner: Strategy, **params):
        super().__init__(**params)
        self.inner = inner
        self.name = f"trend_gate({inner.name})"

    def with_params(self, params: dict) -> "TrendGate":
        mine = {k: v for k, v in params.items() if k in self.defaults}
        theirs = {k: v for k, v in params.items() if k not in self.defaults}
        return TrendGate(self.inner.with_params(theirs), **{**self.params, **mine})

    def param_grid(self) -> dict:
        return {**self.inner.param_grid(), "er_min": [0.15, 0.3]}

    def generate(self, df: pd.DataFrame) -> list[Signal]:
        p = self.params
        d1 = resample(df, "1D")
        close = d1["close"]
        ema = close.ewm(span=p["ema_days"], adjust=False).mean()
        moves = close.diff().abs().rolling(p["er_days"]).sum()
        net = (close - close.shift(p["er_days"])).abs()
        er = net / moves.replace(0, float("nan"))
        up = (close > ema) & (ema > ema.shift(p["slope_days"])) & (er >= p["er_min"])
        dn = (close < ema) & (ema < ema.shift(p["slope_days"])) & (er >= p["er_min"])
        up, dn = up.shift(1).fillna(False), dn.shift(1).fillna(False)  # previous completed day only
        out = []
        for s in self.inner.generate(df):
            day = s.time.normalize()
            if day not in up.index:
                continue
            if s.direction == "LONG" and p["allow"] in ("BOTH", "LONG") and bool(up[day]):
                out.append(s)
            elif s.direction == "SHORT" and p["allow"] in ("BOTH", "SHORT") and bool(dn[day]):
                out.append(s)
        return out
