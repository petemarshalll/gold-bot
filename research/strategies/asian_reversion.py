"""
Hypothesis 2 -- Asian-range false-break reversion.

Mechanism: the Asian session (00:00-07:00 UTC) builds a range in thin
liquidity. Early London often pushes through one side to run stops,
then reverses back into the range. This is the 'sweep' idea from the
existing bot, but defined mechanically on a fixed range rather than a
TradingView indicator, so it can be backtested exactly.

Rules
- Asian range = high/low between `asian_start` and `asian_end` UTC.
- Between `asian_end` and `window_end`, if an M5 bar's high exceeds the
  Asian high by at least `min_pierce` * H1 ATR and the bar CLOSES back
  below the Asian high, go SHORT (limit at the Asian high) with stop
  at that bar's high + `stop_buffer`, target = range midpoint (or
  `rr` * risk if that's closer). Mirror for longs.
- One trade per day per direction. Flat at `flat_utc`.
"""
from __future__ import annotations

from datetime import timedelta

import pandas as pd

from engine import Signal, atr, resample
from strategies.base import Strategy


class AsianReversion(Strategy):
    name = "asian_reversion"
    defaults = {
        "asian_start": 0, "asian_end": 7, "window_end": 11, "flat_utc": 16,
        "min_pierce": 0.15, "stop_buffer": 0.3, "rr": 1.5,
        "min_range_atr": 0.4, "ttl_bars": 6,
    }

    def param_grid(self) -> dict:
        return {"min_pierce": [0.1, 0.2, 0.35], "rr": [1.0, 1.5, 2.5], "window_end": [10, 12]}

    def generate(self, df: pd.DataFrame) -> list[Signal]:
        p = self.params
        h1 = resample(df, "1h")
        h1_atr = atr(h1, 14)
        signals: list[Signal] = []
        for day in pd.Series(df.index.normalize()).unique():
            a0 = day + timedelta(hours=p["asian_start"])
            a1 = day + timedelta(hours=p["asian_end"])
            w1 = day + timedelta(hours=p["window_end"])
            flat = day + timedelta(hours=p["flat_utc"])
            rng = df.loc[a0:a1 - timedelta(seconds=1)]
            if len(rng) < 30:
                continue
            hi, lo = rng["high"].max(), rng["low"].min()
            mid = (hi + lo) / 2
            a_idx = h1_atr.index.get_indexer([a1.floor("1h")], method="ffill")[0]
            if a_idx < 0 or pd.isna(h1_atr.iloc[a_idx]):
                continue
            a = float(h1_atr.iloc[a_idx])
            if (hi - lo) < p["min_range_atr"] * a:
                continue
            window = df.loc[a1:w1 - timedelta(seconds=1)]
            done_short = done_long = False
            for ts, bar in window.iterrows():
                if not done_short and bar["high"] >= hi + p["min_pierce"] * a and bar["close"] < hi:
                    stop = bar["high"] + p["stop_buffer"]
                    risk = stop - hi
                    target = max(mid, hi - p["rr"] * risk)
                    if risk > 0 and target < hi:
                        signals.append(Signal(ts, "SHORT", hi, stop, target, "limit", p["ttl_bars"], flat,
                                              {"range": hi - lo, "atr": a, "pierce": bar["high"] - hi}))
                    done_short = True
                if not done_long and bar["low"] <= lo - p["min_pierce"] * a and bar["close"] > lo:
                    stop = bar["low"] - p["stop_buffer"]
                    risk = lo - stop
                    target = min(mid, lo + p["rr"] * risk)
                    if risk > 0 and target > lo:
                        signals.append(Signal(ts, "LONG", lo, stop, target, "limit", p["ttl_bars"], flat,
                                              {"range": hi - lo, "atr": a, "pierce": lo - bar["low"]}))
                    done_long = True
                if done_short and done_long:
                    break
        return signals
