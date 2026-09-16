"""
sweep.py -- run a small, pre-registered grid of fixed parameter variants
and print one comparison table. Not an optimizer: the grid is decided
before running and every cell is shown, including the losers.

    python sweep.py fvg_sweep --data data/XAUUSD.m_M5.csv --trend-gate \
        --set use_sweep=0 direction=LONG \
        --grid rr=1.0,1.6,2.5 stop_buffer=0.2,0.5 be_at_r=0,1 trail_r=0,1

Columns: n, avg R, PF, max DD, t-stat, then avg R in the first and
second half of the data. A setting is only believable if both halves
agree in sign.
"""
from __future__ import annotations

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from engine import CostModel, _grid, load_candles, metrics, run_strategy
from run import STRATEGIES, parse_set
from strategies.base import TrendGate, VolRegimeFilter


def parse_grid(items):
    grid = {}
    for kv in items or []:
        k, vs = kv.split("=", 1)
        vals = []
        for v in vs.split(","):
            try:
                vals.append(int(v) if v.lstrip("-").isdigit() else float(v))
            except ValueError:
                vals.append(v)
        grid[k] = vals
    return grid


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("strategy", choices=STRATEGIES)
    ap.add_argument("--data", required=True)
    ap.add_argument("--set", nargs="*")
    ap.add_argument("--grid", nargs="+", required=True)
    ap.add_argument("--trend-gate", action="store_true")
    ap.add_argument("--vol-filter", action="store_true")
    args = ap.parse_args()

    df = load_candles(args.data)
    mid = df.index[len(df) // 2]
    costs = CostModel()
    strat = STRATEGIES[args.strategy](**parse_set(args.set))
    if args.vol_filter:
        strat = VolRegimeFilter(strat)
    if args.trend_gate:
        strat = TrendGate(strat)
    grid = parse_grid(args.grid)
    combos = _grid(grid)
    print(f"{strat.describe()}\n{len(combos)} variants, split at {mid.date()}\n")
    hdr = "  ".join(f"{k:>10s}" for k in grid) + "  |    n   avgR    PF  maxDD     t | 1st-half 2nd-half"
    print(hdr)
    print("-" * len(hdr))
    rows = []
    for p in combos:
        tr = run_strategy(strat, df, costs, p)
        m = metrics(tr)
        a = metrics([t for t in tr if t.fill_time < mid])
        b = metrics([t for t in tr if t.fill_time >= mid])
        pf = "inf" if m["profit_factor"] == float("inf") else f"{m['profit_factor']:.2f}"
        rows.append((m["avg_r"], p, m, a, b, pf))
    for avg, p, m, a, b, pf in rows:
        cells = "  ".join(f"{str(p[k]):>10s}" for k in grid)
        print(f"{cells}  | {m['n']:4d} {m['avg_r']:+.3f} {pf:>5s} {m['max_dd_r']:5.1f}R {m['t_stat']:+5.2f} | "
              f"{a['avg_r']:+.3f}({a['n']:3d}) {b['avg_r']:+.3f}({b['n']:3d})")
    print("\nTable shows every variant; do not pick the top row without checking both halves agree.")


if __name__ == "__main__":
    main()
