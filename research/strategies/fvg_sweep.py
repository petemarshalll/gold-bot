"""
Hypothesis 4 -- The live bot's own patterns, tested honestly.

Detection is ported line-for-line from app.py detect_raw_signals(),
on 15-minute bars:
- BEARISH_FVG: low of candle i-2 is above high of candle i (gap down)
- BULLISH_FVG: high of candle i-2 is below low of candle i (gap up)
- BEARISH_SWEEP: high above the prior 10-bar high, close back below it
- BULLISH_SWEEP: low below the prior 10-bar low, close back above it

Live, Claude picks entry/stop/target and a rule (session, DXY,
confidence) decides. Here the levels are mechanical so the pattern
itself gets judged:
- Sweep: `sweep_entry`="retest" -> limit at the swept level (needs a
  pullback to fill); "market" -> in at the next bar's open, like the
  live bot. Stop beyond the sweep wick plus `stop_buffer`, target
  `rr` * risk.
- FVG: stop entry beyond the signal candle (continuation), stop at the
  far side of the gap candle i-2 plus `stop_buffer`, target `rr` * risk.
Params `use_fvg` / `use_sweep` / `asian_only` switch the pieces so the
existing variant rules (B = Asian session, A = sweeps only) can be
reproduced without DXY.
"""
from __future__ import annotations

from datetime import timedelta

import pandas as pd

from engine import Signal, atr, resample
from strategies.base import Strategy


class FvgSweep(Strategy):
    name = "fvg_sweep"
    defaults = {
        "tf_min": 15, "lookback": 10, "stop_buffer": 0.3, "rr": 1.6,
        "use_fvg": 1, "use_sweep": 1, "asian_only": 0,
        "ttl_bars": 6, "max_hold_h": 8, "min_risk_atr": 0.3, "sweep_entry": "retest",
    }

    def param_grid(self) -> dict:
        return {"rr": [1.0, 1.6, 2.5], "lookback": [10, 20], "stop_buffer": [0.2, 0.5]}

    def generate(self, df: pd.DataFrame) -> list[Signal]:
        p = self.params
        tf = resample(df, f"{p['tf_min']}min")
        a = atr(resample(df, "1h"), 14)
        H, L, C = tf["high"].values, tf["low"].values, tf["close"].values
        idx = tf.index
        lb = p["lookback"]
        signals: list[Signal] = []
        for i in range(max(3, lb), len(tf)):
            ts = idx[i]
            if p["asian_only"] and not (0 <= ts.hour < 7):
                continue
            ai = a.index.get_indexer([ts.floor("1h")], method="ffill")[0]
            if ai < 0 or pd.isna(a.iloc[ai]):
                continue
            atr_v = float(a.iloc[ai])
            decision = ts + timedelta(minutes=p["tf_min"] - 5)
            flat = ts + timedelta(hours=p["max_hold_h"])
            high, low, close = H[i], L[i], C[i]
            meta = {"atr": atr_v}

            if p["use_fvg"]:
                if L[i - 2] > high:  # bearish gap
                    entry, stop = low - p["stop_buffer"], H[i - 2] + p["stop_buffer"]
                    risk = stop - entry
                    if risk >= p["min_risk_atr"] * atr_v:
                        signals.append(Signal(decision, "SHORT", entry, stop, entry - p["rr"] * risk,
                                              "stop", p["ttl_bars"], flat, {**meta, "type": "BEARISH_FVG"}))
                if H[i - 2] < low:  # bullish gap
                    entry, stop = high + p["stop_buffer"], L[i - 2] - p["stop_buffer"]
                    risk = entry - stop
                    if risk >= p["min_risk_atr"] * atr_v:
                        signals.append(Signal(decision, "LONG", entry, stop, entry + p["rr"] * risk,
                                              "stop", p["ttl_bars"], flat, {**meta, "type": "BULLISH_FVG"}))

            if p["use_sweep"]:
                lb_high = H[i - lb:i].max()
                mode = "limit" if p["sweep_entry"] == "retest" else "market"
                if high > lb_high and close < lb_high:
                    entry = lb_high if mode == "limit" else close
                    stop = high + p["stop_buffer"]
                    risk = stop - entry
                    if risk >= p["min_risk_atr"] * atr_v:
                        signals.append(Signal(decision, "SHORT", entry, stop, entry - p["rr"] * risk,
                                              mode, p["ttl_bars"], flat, {**meta, "type": "BEARISH_SWEEP"}))
                lb_low = L[i - lb:i].min()
                if low < lb_low and close > lb_low:
                    entry = lb_low if mode == "limit" else close
                    stop = low - p["stop_buffer"]
                    risk = entry - stop
                    if risk >= p["min_risk_atr"] * atr_v:
                        signals.append(Signal(decision, "LONG", entry, stop, entry + p["rr"] * risk,
                                              mode, p["ttl_bars"], flat, {**meta, "type": "BULLISH_SWEEP"}))
        return signals
