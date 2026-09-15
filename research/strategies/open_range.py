"""
Hypothesis 1 -- Open-range breakout.

Mechanism: the first N minutes after a major session open set a range
as overnight orders are absorbed; a break of that range with the
session behind it tends to continue. Long documented in index futures,
tested here on gold for London (07:00 UTC) and New York (13:30 UTC).

Rules
- Range = high/low of the first `range_min` minutes after `open_utc`.
- Stop-entry `buffer` above the range high (long) / below the low (short).
- Stop = opposite side of the range (or `atr_stop_mult` * H1 ATR if smaller,
  so a huge range doesn't make a tiny position).
- Target = `rr` * risk. Force-flat `flat_after_min` after the open.
- Max one long and one short attempt per session. Range must be at least
  `min_range_atr` * H1 ATR so we're not trading noise.
Note: sessions are fixed UTC. UK/US clock changes shift the real open by
an hour for part of the year; a param sweep on `open_utc` handles that.
"""
from __future__ import annotations

from datetime import timedelta

import pandas as pd

from engine import Signal, atr, resample
from strategies.base import Strategy


class OpenRangeBreakout(Strategy):
    name = "open_range"
    defaults = {
        "open_utc": 7.0,        # hours; 13.5 = 13:30
        "range_min": 30,
        "buffer": 0.3,
        "rr": 2.0,
        "atr_stop_mult": 1.0,
        "min_range_atr": 0.25,
        "flat_after_min": 300,
        "ttl_bars": 24,
    }

    def param_grid(self) -> dict:
        return {"range_min": [15, 30, 60], "rr": [1.5, 2.0, 3.0], "buffer": [0.2, 0.5]}

    def generate(self, df: pd.DataFrame) -> list[Signal]:
        p = self.params
        h1 = resample(df, "1h")
        h1_atr = atr(h1, 14)
        signals: list[Signal] = []
        open_h = int(p["open_utc"])
        open_m = int(round((p["open_utc"] - open_h) * 60))
        days = pd.Series(df.index.normalize()).unique()
        for day in days:
            t_open = day + timedelta(hours=open_h, minutes=open_m)
            t_range_end = t_open + timedelta(minutes=p["range_min"])
            rng = df.loc[t_open:t_range_end - timedelta(seconds=1)]
            if len(rng) < max(2, p["range_min"] // 5 - 1):
                continue
            hi, lo = rng["high"].max(), rng["low"].min()
            a_idx = h1_atr.index.get_indexer([t_open.floor("1h")], method="ffill")[0]
            if a_idx < 0 or pd.isna(h1_atr.iloc[a_idx]):
                continue
            a = float(h1_atr.iloc[a_idx])
            if (hi - lo) < p["min_range_atr"] * a:
                continue
            decision_bar = rng.index[-1]
            flat = t_open + timedelta(minutes=p["flat_after_min"])
            stop_dist = min(hi - lo, p["atr_stop_mult"] * a)
            # long breakout
            entry = hi + p["buffer"]
            signals.append(Signal(decision_bar, "LONG", entry, entry - stop_dist,
                                  entry + p["rr"] * stop_dist, "stop", p["ttl_bars"], flat,
                                  {"session_open": p["open_utc"], "range": hi - lo, "atr": a}))
            entry = lo - p["buffer"]
            signals.append(Signal(decision_bar, "SHORT", entry, entry + stop_dist,
                                  entry - p["rr"] * stop_dist, "stop", p["ttl_bars"], flat,
                                  {"session_open": p["open_utc"], "range": hi - lo, "atr": a}))
        return signals
