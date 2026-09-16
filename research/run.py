"""
run.py -- test one hypothesis end to end.

    python run.py open_range --data data/XAUUSD.m_M5.csv
    python run.py asian_reversion --data data/XAUUSD.m_M5.csv --vol-filter
    python run.py open_range --data data/XAUUSD.m_M5.csv --set open_utc=13.5 --no-wf

Prints: full-history metrics with fixed params, per-session and per-year
breakdowns, regime split, walk-forward out-of-sample result per window,
and a +/-20% parameter robustness table. Writes trades to
results/<name>_<timestamp>.csv for inspection.

The only number that counts for go/no-go is the walk-forward OOS row.
"""
from __future__ import annotations

import argparse
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import pandas as pd

from engine import (CostModel, by_key, load_candles, metrics, regime_split, robustness,
                    run_strategy, walk_forward)
from strategies.asian_reversion import AsianReversion
from strategies.base import VolRegimeFilter
from strategies.fvg_sweep import FvgSweep
from strategies.open_range import OpenRangeBreakout
from strategies.trend_pullback import TrendPullback

STRATEGIES = {"open_range": OpenRangeBreakout, "asian_reversion": AsianReversion,
              "trend_pullback": TrendPullback, "fvg_sweep": FvgSweep}


def fmt(m: dict) -> str:
    pf = m["profit_factor"]
    pf_s = "inf" if pf == float("inf") else f"{pf:.2f}"
    return (f"n={m['n']:4d}  WR={m['win_rate']*100:5.1f}%  avgR={m['avg_r']:+.3f}  "
            f"totalR={m['total_r']:+7.1f}  PF={pf_s}  maxDD={m['max_dd_r']:.1f}R  "
            f"t={m['t_stat']:+.2f}  R/mo={m['r_per_month']:+.2f}")


def parse_set(items):
    out = {}
    for kv in items or []:
        k, v = kv.split("=", 1)
        try:
            out[k] = int(v) if v.lstrip("-").isdigit() else float(v)
        except ValueError:
            out[k] = v  # string params like sweep_entry=market
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("strategy", choices=STRATEGIES)
    ap.add_argument("--data", required=True)
    ap.add_argument("--set", nargs="*", help="override params, e.g. rr=2.5 range_min=15")
    ap.add_argument("--vol-filter", action="store_true")
    ap.add_argument("--no-wf", action="store_true", help="skip walk-forward (fast look)")
    ap.add_argument("--fit-months", type=int, default=12)
    ap.add_argument("--test-months", type=int, default=3)
    ap.add_argument("--no-csv-spread", action="store_true", help="ignore CSV spread column, use session table")
    ap.add_argument("--commission", type=float, default=7.0, help="$ per lot round turn")
    ap.add_argument("--slippage", type=float, default=0.15, help="$ adverse slippage on stop fills")
    args = ap.parse_args()

    t0 = time.time()
    df = load_candles(args.data)
    print(f"Loaded {len(df):,} M5 bars  {df.index[0]} -> {df.index[-1]}  ({(df.index[-1]-df.index[0]).days} days)")
    if "spread" in df.columns and df["spread"].notna().any():
        print(f"CSV spread present: median {df['spread'].median():.0f} points")
    else:
        print("CSV spread absent: using per-session spread table")

    costs = CostModel(use_csv_spread=not args.no_csv_spread,
                      commission_per_lot_rt=args.commission, stop_slippage=args.slippage)
    strat = STRATEGIES[args.strategy](**parse_set(args.set))
    if args.vol_filter:
        strat = VolRegimeFilter(strat)
    print(f"Strategy: {strat.describe()}\n")

    # 1. fixed-parameter full history (the optimistic view)
    trades = run_strategy(strat, df, costs)
    print("FULL HISTORY, fixed params (in-sample, do not trust on its own)")
    print("  ", fmt(metrics(trades)))
    if trades:
        print("  by session:")
        for k, m in by_key(trades, lambda t: t.session).items():
            print(f"    {k:7s}", fmt(m))
        print("  by year:")
        for k, m in by_key(trades, lambda t: str(t.fill_time.year)).items():
            print(f"    {k:7s}", fmt(m))
        print("  by direction:")
        for k, m in by_key(trades, lambda t: t.signal.direction).items():
            print(f"    {k:7s}", fmt(m))
        if any("type" in t.signal.meta for t in trades):
            print("  by signal type:")
            for k, m in by_key(trades, lambda t: t.signal.meta.get("type", "?")).items():
                print(f"    {k:13s}", fmt(m))
        print("  by exit:")
        for k, m in by_key(trades, lambda t: t.exit_reason).items():
            print(f"    {k:7s}", fmt(m))
        print("  by regime (monthly efficiency ratio):")
        for k, m in regime_split(trades, df).items():
            print(f"    {k:7s}", fmt(m))

    # 2. walk-forward (the number that counts)
    if not args.no_wf:
        print(f"\nWALK-FORWARD  fit {args.fit_months}m / test {args.test_months}m  "
              f"grid={strat.param_grid()}")
        wf = walk_forward(strat, df, costs, args.fit_months, args.test_months)
        for w in wf["windows"]:
            if w.get("params") is None:
                print(f"  {w['fit_start'].date()} -> {w['fit_end'].date()}: {w.get('note')}")
                continue
            print(f"  test {w['fit_end'].date()} -> {w['test_end'].date()}  params={w['params']}")
            print(f"     fit : {fmt(w['fit'])}")
            print(f"     test: {fmt(w['test'])}")
        print("  OOS TOTAL:", fmt(wf["oos"]))
        pos = sum(1 for w in wf["windows"] if w.get("test") and w["test"]["total_r"] > 0)
        tot = sum(1 for w in wf["windows"] if w.get("test"))
        print(f"  positive test windows: {pos}/{tot}")

    # 3. robustness of the fixed params
    print("\nROBUSTNESS (+/-20% on each param, full history)")
    rb = robustness(strat, df, costs, strat.params)
    print(f"  base            avgR={rb['base']['avg_r']:+.3f}  n={rb['base']['n']}")
    for k, m in rb["perturbed"].items():
        print(f"  {k:16s} avgR={m['avg_r']:+.3f}  n={m['n']}")

    os.makedirs("results", exist_ok=True)
    out = f"results/{args.strategy}_{int(t0)}.csv"
    pd.DataFrame([{
        "fill_time": t.fill_time, "exit_time": t.exit_time, "direction": t.signal.direction,
        "fill": t.fill_price, "stop": t.signal.stop, "target": t.signal.target,
        "exit": t.exit_price, "reason": t.exit_reason, "r": t.r, "session": t.session,
        **{f"meta_{k}": v for k, v in t.signal.meta.items()},
    } for t in trades]).to_csv(out, index=False)
    print(f"\nTrades written to {out}   ({time.time()-t0:.1f}s)")


if __name__ == "__main__":
    main()
