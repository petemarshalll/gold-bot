"""
mc.py -- position sizing by Monte Carlo on a real trade list.

    python mc.py results/fvg_sweep_<timestamp>.csv --account 50000 --max-dd 6 --daily-dd 5 --months 6

Resamples the trades (with replacement, preserving the observed trade
rate per month) into thousands of alternative 6-month paths, then for
each risk-per-trade setting reports:
- median and 10th-percentile total return
- worst drawdown (median and 95th percentile)
- probability of breaching the trailing max-drawdown rule
- probability of breaching the daily-loss rule at least once
Trailing DD is measured from the running peak of closed balance, which
is how FTUK/FTMO-style rules work. Same-day trades are summed for the
daily rule. This is a survival calculation, not a profit forecast.
"""
from __future__ import annotations

import argparse

import numpy as np
import pandas as pd


def simulate_paths(rs: np.ndarray, days: np.ndarray, months: int, risk_pct: float,
                   account: float, max_dd: float, daily_dd: float, n_paths: int, rng,
                   static: bool = False) -> dict:
    n_trades = len(rs)
    span_days = max(1, (days.max() - days.min()) + 1)
    trades_per_day = n_trades / span_days
    horizon = int(months * 30.44)
    # group real trades by day so daily clustering is preserved
    by_day = pd.Series(rs).groupby(days).apply(list).values
    results = {"ret": [], "dd": [], "breach_max": 0, "breach_daily": 0}
    for _ in range(n_paths):
        bal = account
        peak = account
        worst_dd = 0.0
        breached_max = breached_daily = False
        # each simulated day: draw a real day's trade list with probability matching trade rate
        n_days_with_trades = rng.binomial(horizon, min(1.0, len(by_day) / span_days))
        for _d in range(n_days_with_trades):
            day_rs = by_day[rng.integers(len(by_day))]
            day_pnl = 0.0
            for r in day_rs:
                pnl = r * risk_pct / 100 * bal
                bal += pnl
                day_pnl += pnl
                peak = max(peak, bal)
                dd = (account - bal) / account * 100 if static else (peak - bal) / peak * 100
                worst_dd = max(worst_dd, dd)
                if dd >= max_dd:
                    breached_max = True
            if -day_pnl >= daily_dd / 100 * (bal - day_pnl):
                breached_daily = True
        results["ret"].append((bal - account) / account * 100)
        results["dd"].append(worst_dd)
        results["breach_max"] += breached_max
        results["breach_daily"] += breached_daily
    ret, dd = np.array(results["ret"]), np.array(results["dd"])
    return {
        "median_ret": np.median(ret), "p10_ret": np.percentile(ret, 10), "p90_ret": np.percentile(ret, 90),
        "median_dd": np.median(dd), "p95_dd": np.percentile(dd, 95),
        "p_breach_max": results["breach_max"] / n_paths, "p_breach_daily": results["breach_daily"] / n_paths,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("trades_csv")
    ap.add_argument("--account", type=float, default=50000)
    ap.add_argument("--max-dd", type=float, default=6.0, help="trailing max drawdown rule, percent")
    ap.add_argument("--daily-dd", type=float, default=5.0, help="daily loss rule, percent")
    ap.add_argument("--months", type=int, default=6)
    ap.add_argument("--paths", type=int, default=3000)
    ap.add_argument("--risks", default="0.25,0.35,0.5,0.75,1.0")
    ap.add_argument("--static", action="store_true",
                    help="max-dd is a fixed floor below the starting balance rather than trailing the peak")
    ap.add_argument("--haircut", type=float, default=0.0,
                    help="subtract this many R from every trade first (e.g. 0.05 = assume live is worse than backtest)")
    args = ap.parse_args()

    df = pd.read_csv(args.trades_csv, parse_dates=["fill_time"])
    rs = df["r"].values - args.haircut
    days = (df["fill_time"].dt.normalize() - df["fill_time"].dt.normalize().min()).dt.days.values
    rng = np.random.default_rng(42)
    print(f"{len(rs)} trades, avg {rs.mean():+.3f}R (haircut {args.haircut}), "
          f"{len(rs) / max(1, days.max() / 30.44):.1f} trades/month\n")
    kind = "static" if args.static else "trailing"
    print(f"Account {args.account:,.0f}, rules: {args.max_dd}% {kind} max DD, {args.daily_dd}% daily. "
          f"{args.months}-month paths x {args.paths}\n")
    print(f"{'risk%':>6} | {'median ret':>10} {'p10 ret':>8} {'p90 ret':>8} | {'med DD':>7} {'p95 DD':>7} | "
          f"{'P(max DD)':>9} {'P(daily)':>8}")
    print("-" * 86)
    for r in [float(x) for x in args.risks.split(",")]:
        m = simulate_paths(rs, days, args.months, r, args.account, args.max_dd, args.daily_dd, args.paths, rng,
                           static=args.static)
        print(f"{r:6.2f} | {m['median_ret']:+9.1f}% {m['p10_ret']:+7.1f}% {m['p90_ret']:+7.1f}% | "
              f"{m['median_dd']:6.1f}% {m['p95_dd']:6.1f}% | {m['p_breach_max']:9.1%} {m['p_breach_daily']:8.1%}")
    print("\nPick the largest risk% whose P(max DD) you can live with; 5% or less is the usual bar for a funded account.")


if __name__ == "__main__":
    main()