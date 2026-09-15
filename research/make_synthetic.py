"""
make_synthetic.py -- generate a fake XAUUSD M5 CSV (random walk with a
session-volatility profile) so the harness can be smoke-tested before
the real export finishes. Random data has NO edge by construction: any
strategy scoring positive on it after costs is a bug in the engine.

    python make_synthetic.py --years 2 --out data/SYNTH_M5.csv
"""
import argparse

import numpy as np
import pandas as pd


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--years", type=float, default=2.0)
    ap.add_argument("--out", default="data/SYNTH_M5.csv")
    ap.add_argument("--seed", type=int, default=7)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    idx = pd.date_range("2024-01-01", periods=int(args.years * 365 * 24 * 12), freq="5min", tz="UTC")
    idx = idx[idx.dayofweek < 5]
    hours = idx.hour.values
    vol = np.where((hours >= 0) & (hours < 7), 0.35, np.where((hours >= 7) & (hours < 20), 0.8, 0.3))
    rets = rng.normal(0, 1, len(idx)) * vol
    close = 2300 + np.cumsum(rets)
    open_ = np.concatenate([[close[0]], close[:-1]])
    wick = np.abs(rng.normal(0, 1, len(idx))) * vol
    high = np.maximum(open_, close) + wick
    low = np.minimum(open_, close) - np.abs(rng.normal(0, 1, len(idx))) * vol
    spread = np.where((hours >= 0) & (hours < 7), 35, 20) + rng.integers(0, 6, len(idx))
    pd.DataFrame({"time": idx, "open": open_, "high": high, "low": low, "close": close,
                  "tick_volume": rng.integers(50, 500, len(idx)), "spread": spread}
                 ).to_csv(args.out, index=False)
    print(f"wrote {len(idx):,} bars to {args.out}")


if __name__ == "__main__":
    main()
