import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

import numpy as np
import pandas as pd
import pytest

from engine import CostModel, Signal, load_candles, metrics, resample, simulate

T0 = pd.Timestamp("2025-03-03 08:00", tz="UTC")


def bars(rows, spread=20):
    """rows: list of (open, high, low, close). 5-minute bars from T0."""
    idx = pd.date_range(T0, periods=len(rows), freq="5min")
    df = pd.DataFrame(rows, columns=["open", "high", "low", "close"], index=idx)
    df["spread"] = spread
    return df


ZERO = CostModel(commission_per_lot_rt=0, stop_slippage=0, entry_slippage=0, use_csv_spread=False,
                 spread_by_session={"asian": 0, "london": 0, "ny": 0, "late": 0})


def test_long_stop_entry_fills_at_ask_and_hits_target():
    df = bars([(100, 101, 99, 100), (100, 103, 100.5, 102), (102, 106, 101, 105)])
    sig = Signal(df.index[0], "LONG", 102, 100, 106, "stop", 10)
    costs = CostModel(commission_per_lot_rt=0, stop_slippage=0, entry_slippage=0,
                      use_csv_spread=True, point_size=0.01)
    tr = simulate(df, [sig], costs)
    assert len(tr) == 1
    # ask = bid + 0.20; fills at max(entry, open+spread) = 102.0
    assert tr[0].fill_price == pytest.approx(102.0)
    assert tr[0].exit_reason == "target"
    # risk recomputed on real bid entry (101.8): (106-102)/(101.8-100)
    assert tr[0].r == pytest.approx((106 - 102.0) / (101.8 - 100))


def test_stop_and_target_same_bar_is_a_loss():
    df = bars([(100, 101, 99, 100), (100, 110, 90, 100)])
    sig = Signal(df.index[0], "LONG", 100.5, 99, 105, "stop", 10)
    tr = simulate(df, [sig], ZERO)
    assert len(tr) == 1 and tr[0].exit_reason == "stop"
    assert tr[0].r == pytest.approx(-1.0)


def test_short_pays_spread_on_exit():
    df = bars([(100, 101, 99, 100), (100, 100.5, 95.8, 96), (96, 97, 95.4, 95.5)], spread=50)
    sig = Signal(df.index[0], "SHORT", 99.5, 102, 96, "stop", 10)
    costs = CostModel(commission_per_lot_rt=0, stop_slippage=0, entry_slippage=0, use_csv_spread=True)
    tr = simulate(df, [sig], costs)
    assert len(tr) == 1
    # target 96 requires ask (bid + 0.5) <= 96, i.e. bid low <= 95.5: bar 2 (95.8) misses, bar 3 (95.4) fills
    assert tr[0].exit_time == df.index[2] and tr[0].exit_reason == "target"


def test_commission_and_slippage_reduce_r():
    df = bars([(100, 101, 99, 100), (100, 101, 98, 99)])
    sig = Signal(df.index[0], "LONG", 100.5, 99, 104, "stop", 10)
    costs = CostModel(commission_per_lot_rt=7, stop_slippage=0.15, entry_slippage=0.05, use_csv_spread=False,
                      spread_by_session={"asian": 0, "london": 0, "ny": 0, "late": 0})
    tr = simulate(df, [sig], costs)
    assert len(tr) == 1 and tr[0].exit_reason == "stop"
    assert tr[0].r < -1.0  # worse than a clean 1R loss


def test_oco_first_fill_cancels_other_and_ttl_expires():
    df = bars([(100, 101, 99, 100), (100, 100.5, 99.5, 100), (100, 103, 100, 102), (102, 104, 101, 103)])
    long = Signal(df.index[0], "LONG", 102, 100, 110, "stop", 10)
    short = Signal(df.index[0], "SHORT", 98, 100, 90, "stop", 10)
    tr = simulate(df, [long, short], ZERO)
    assert len(tr) == 1 and tr[0].signal.direction == "LONG"
    # long entry never reached within ttl of 1 bar -> no trades
    tr2 = simulate(df, [Signal(df.index[0], "LONG", 105, 100, 110, "stop", 1)], ZERO)
    assert tr2 == []


def test_forced_flat_exit_at_time():
    df = bars([(100, 101, 99, 100), (100, 101, 100, 100.8), (100.8, 101, 100.5, 100.9), (100.9, 101, 100.5, 100.7)])
    sig = Signal(df.index[0], "LONG", 100.5, 99, 110, "stop", 10, exit_at=df.index[3])
    tr = simulate(df, [sig], ZERO)
    assert len(tr) == 1 and tr[0].exit_reason == "time"


def test_signals_while_in_position_are_dropped():
    rows = [(100, 101, 99, 100)] + [(100, 101, 99.5, 100)] * 5
    df = bars(rows)
    s1 = Signal(df.index[0], "LONG", 100.5, 99, 105, "stop", 10)
    s2 = Signal(df.index[1], "LONG", 100.5, 99, 105, "stop", 10)
    tr = simulate(df, [s1, s2], ZERO, max_hold_bars=3)
    assert len(tr) == 1


def test_metrics_basic():
    class T:  # minimal stand-in
        def __init__(self, r, t):
            self.r, self.fill_time, self.exit_time = r, t, t
    ts = pd.Timestamp("2025-01-01", tz="UTC")
    m = metrics([T(1, ts), T(-1, ts), T(2, ts), T(-1, ts + pd.Timedelta(days=30))])
    assert m["n"] == 4 and m["win_rate"] == 0.5
    assert m["total_r"] == pytest.approx(1.0)
    assert m["profit_factor"] == pytest.approx(1.5)
    assert m["max_dd_r"] == pytest.approx(1.0)


def test_random_data_has_no_edge(tmp_path):
    """Sanity: on a random walk, the breakout strategy must not show a positive avg R after costs."""
    from strategies.open_range import OpenRangeBreakout
    rng = np.random.default_rng(1)
    idx = pd.date_range("2024-01-01", periods=12 * 24 * 260, freq="5min", tz="UTC")
    idx = idx[idx.dayofweek < 5]
    close = 2300 + np.cumsum(rng.normal(0, 0.6, len(idx)))
    open_ = np.concatenate([[close[0]], close[:-1]])
    high = np.maximum(open_, close) + np.abs(rng.normal(0, 0.6, len(idx)))
    low = np.minimum(open_, close) - np.abs(rng.normal(0, 0.6, len(idx)))
    df = pd.DataFrame({"open": open_, "high": high, "low": low, "close": close, "spread": 25}, index=idx)
    df.index.name = "time"
    trades = simulate(df, OpenRangeBreakout().generate(df), CostModel())
    m = metrics(trades)
    assert m["n"] > 50
    assert m["avg_r"] < 0.15  # random walk plus costs should not look like an edge
