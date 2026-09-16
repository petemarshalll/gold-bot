"""
Hypothesis 3 -- Trend pullback.

Mechanism: in a strongly trending market (gold spent this whole dataset
rising), the highest-probability entries are with the trend after a
shallow pullback, not fades. Tests whether 'wait for a dip to the
moving average and buy the turn back up' beats costs.

Rules
- Daily trend: close above EMA(`daily_ema`) and the EMA rising -> UP,
  mirror -> DOWN, else no trades. Uses the previous completed day.
- Pullback on H1: within the last `pullback_bars` H1 bars, price
  touched EMA(`h1_ema`) (low <= EMA for longs), and the latest H1 bar
  closes back above the EMA after closing at or below it.
- Entry: stop order `buffer` above that H1 bar's high. Stop: lowest
  low of the pullback bars minus `buffer`, but at least
  `min_stop_atr` * H1 ATR. Target: `rr` * risk. Time stop after
  `max_hold_h` hours. Max one entry per H1 bar, longs only if
  `longs_only` (the by-direction split tells us whether shorts belong).
"""
from __future__ import annotations

from datetime import timedelta

import pandas as pd

from engine import Signal, atr, resample
from strategies.base import Strategy


class TrendPullback(Strategy):
    name = "trend_pullback"
    defaults = {
        "daily_ema": 20, "h1_ema": 20, "pullback_bars": 6, "buffer": 0.3,
        "min_stop_atr": 0.5, "rr": 2.0, "max_hold_h": 24, "ttl_bars": 12,
        "longs_only": 0, "session_start": 6, "session_end": 20,
    }

    def param_grid(self) -> dict:
        return {"h1_ema": [10, 20, 50], "rr": [1.5, 2.0, 3.0], "pullback_bars": [4, 8]}

    def generate(self, df: pd.DataFrame) -> list[Signal]:
        p = self.params
        d1 = resample(df, "1D")
        d_ema = d1["close"].ewm(span=p["daily_ema"], adjust=False).mean()
        trend = pd.Series("NONE", index=d1.index)
        up = (d1["close"] > d_ema) & (d_ema > d_ema.shift(1))
        dn = (d1["close"] < d_ema) & (d_ema < d_ema.shift(1))
        trend[up] = "UP"
        trend[dn] = "DOWN"
        trend = trend.shift(1)  # only the previous completed day is known

        h1 = resample(df, "1h")
        ema = h1["close"].ewm(span=p["h1_ema"], adjust=False).mean()
        a = atr(h1, 14)
        signals: list[Signal] = []
        n_pb = p["pullback_bars"]
        for i in range(max(n_pb, 20), len(h1)):
            ts = h1.index[i]
            if not (p["session_start"] <= ts.hour < p["session_end"]):
                continue
            day = ts.normalize()
            t = trend.get(day, "NONE")
            if t == "NONE" or pd.isna(a.iloc[i]):
                continue
            bar, prev = h1.iloc[i], h1.iloc[i - 1]
            e, e_prev = ema.iloc[i], ema.iloc[i - 1]
            window = h1.iloc[i - n_pb:i + 1]
            decision = ts + timedelta(minutes=55)  # H1 bar close, in M5 label terms
            flat = ts + timedelta(hours=p["max_hold_h"])
            if t == "UP":
                touched = (window["low"] <= ema.iloc[i - n_pb:i + 1]).any()
                if touched and prev["close"] <= e_prev and bar["close"] > e:
                    entry = bar["high"] + p["buffer"]
                    stop = min(window["low"].min() - p["buffer"], entry - p["min_stop_atr"] * a.iloc[i])
                    risk = entry - stop
                    signals.append(Signal(decision, "LONG", entry, stop, entry + p["rr"] * risk,
                                          "stop", p["ttl_bars"], flat, {"atr": float(a.iloc[i])}))
            elif t == "DOWN" and not p["longs_only"]:
                touched = (window["high"] >= ema.iloc[i - n_pb:i + 1]).any()
                if touched and prev["close"] >= e_prev and bar["close"] < e:
                    entry = bar["low"] - p["buffer"]
                    stop = max(window["high"].max() + p["buffer"], entry + p["min_stop_atr"] * a.iloc[i])
                    risk = stop - entry
                    signals.append(Signal(decision, "SHORT", entry, stop, entry - p["rr"] * risk,
                                          "stop", p["ttl_bars"], flat, {"atr": float(a.iloc[i])}))
        return signals
