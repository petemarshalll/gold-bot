"""
shadow.py -- run the locked rule against B's live MT5 feed, paper only.

Every 5 minutes it pulls the last 90 days of M5 candles from the MT5
MCP server, runs EXACTLY the backtest code (TrendGate(FvgSweep)) over
that window, and diffs the resulting trade list against what it has
already logged. New pending orders, fills and exits are appended to
shadow/shadow_trades.csv and sent to Telegram. It never places an order.

Because the same simulate() produces the backtest and the shadow, any
difference between the two later is a data or fill question, not a
code question.

Run on the VPS from the research folder (needs pandas + numpy:
    python -m pip install pandas numpy requests):
    set MCP_PORT=22347
    set MCP_API_KEY=...
    set SYMBOL=XAUUSD.m
    set TELEGRAM_BOT_TOKEN=...      (optional)
    set TELEGRAM_CHAT_ID=...        (optional)
    python shadow.py
"""
from __future__ import annotations

import csv
import json
import os
import sys
import time
import traceback
from datetime import datetime, timedelta, timezone

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import pandas as pd
import requests

from engine import CostModel, all_params, run_strategy
from export_mt5_history import mcp_call_tool, mcp_initialize, parse_time  # same MCP session code
from strategies.base import TrendGate
from strategies.fvg_sweep import FvgSweep

SYMBOL = os.environ.get("SYMBOL", "XAUUSD.m")
WINDOW_DAYS = int(os.environ.get("SHADOW_WINDOW_DAYS", "90"))
OUT_DIR = os.environ.get("SHADOW_DIR", "shadow")
TG_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN")
TG_CHAT = os.environ.get("TELEGRAM_CHAT_ID")
RULE_NAME = "bullish_fvg_trend_gated_v1"

# ---- THE LOCKED RULE. Do not edit without a new research pass. ----
def build_strategy():
    return TrendGate(FvgSweep(use_sweep=0, direction="LONG"))
# --------------------------------------------------------------------

TRADES_CSV = os.path.join(OUT_DIR, "shadow_trades.csv")
STATE_JSON = os.path.join(OUT_DIR, "shadow_state.json")
CANDLES_CSV = os.path.join(OUT_DIR, "shadow_candles.csv")


def tg(msg: str):
    print(msg)
    if not (TG_TOKEN and TG_CHAT):
        return
    try:
        requests.post(f"https://api.telegram.org/bot{TG_TOKEN}/sendMessage",
                      json={"chat_id": TG_CHAT, "text": msg}, timeout=10)
    except Exception as e:
        print(f"[tg] failed: {e}")


def load_state():
    if os.path.exists(STATE_JSON):
        with open(STATE_JSON) as f:
            return json.load(f)
    return {"started": datetime.now(timezone.utc).isoformat(), "logged_fills": [],
            "announced_signals": [], "last_open_key": None}


def save_state(st):
    os.makedirs(OUT_DIR, exist_ok=True)
    tmp = STATE_JSON + ".tmp"
    with open(tmp, "w") as f:
        json.dump(st, f, indent=1)
    os.replace(tmp, STATE_JSON)


def fetch_candles(days: int) -> pd.DataFrame:
    now = datetime.now(timezone.utc)
    rows = []
    chunk_end = now
    while chunk_end > now - timedelta(days=days):
        chunk_start = chunk_end - timedelta(days=7)
        resp = mcp_call_tool("get_chart_history", {
            "symbol": SYMBOL, "period": "M5",
            "datetime_from": chunk_start.isoformat(), "datetime_to": chunk_end.isoformat()})
        for c in resp.get("history", []) or []:
            rows.append({"time": parse_time(c["time"]), "open": c["open"], "high": c["high"],
                         "low": c["low"], "close": c["close"], "spread": c.get("spread")})
        chunk_end = chunk_start
    df = pd.DataFrame(rows).drop_duplicates("time").set_index("time").sort_index()
    for col in ("open", "high", "low", "close"):
        df[col] = df[col].astype(float)
    df["spread"] = pd.to_numeric(df["spread"], errors="coerce")
    return df


def drop_forming_bar(df: pd.DataFrame) -> pd.DataFrame:
    """The last M5 bar is still forming; the backtest only ever saw closed bars."""
    now = datetime.now(timezone.utc)
    last_closed = now.replace(second=0, microsecond=0) - timedelta(minutes=now.minute % 5) - timedelta(minutes=5)
    return df.loc[:last_closed]


def append_trade_row(t, kind: str):
    os.makedirs(OUT_DIR, exist_ok=True)
    new = not os.path.exists(TRADES_CSV)
    with open(TRADES_CSV, "a", newline="") as f:
        w = csv.writer(f)
        if new:
            w.writerow(["logged_at", "kind", "rule", "signal_time", "fill_time", "exit_time", "direction",
                        "intended_entry", "stop", "target", "fill", "exit", "reason", "r"])
        w.writerow([datetime.now(timezone.utc).isoformat(), kind, RULE_NAME, t.signal.time.isoformat(),
                    t.fill_time.isoformat(), t.exit_time.isoformat(), t.signal.direction,
                    round(t.signal.entry, 2), round(t.signal.stop, 2), round(t.signal.target, 2),
                    round(t.fill_price, 2), round(t.exit_price, 2), t.exit_reason, round(t.r, 3)])


def once(strategy, state, costs):
    df = drop_forming_bar(fetch_candles(WINDOW_DAYS))
    os.makedirs(OUT_DIR, exist_ok=True)
    df.to_csv(CANDLES_CSV)  # keep the exact feed the shadow saw, for later reconciliation
    started = pd.Timestamp(state["started"])
    last_bar = df.index[-1]

    # 1. fresh signals decided on the newest closed 15m bar -> "order would be placed now"
    signals = strategy.generate(df)
    for s in signals:
        key = f"{s.time.isoformat()}|{s.direction}|{round(s.entry, 2)}"
        if s.time >= last_bar - timedelta(minutes=15) and key not in state["announced_signals"]:
            state["announced_signals"].append(key)
            tg(f"[SHADOW {RULE_NAME}] {s.direction} {s.order_type.upper()} order would be placed\n"
               f"entry {s.entry:.2f}  stop {s.stop:.2f}  target {s.target:.2f}  risk {s.risk:.2f}\n"
               f"cancel if unfilled by {(s.time + timedelta(minutes=5 * (s.ttl_bars + 1))).strftime('%H:%M')} UTC")

    # 2. completed paper trades since the shadow started
    trades = run_strategy(strategy, df, costs)
    for t in trades:
        if t.fill_time < started:
            continue
        key = f"{t.fill_time.isoformat()}|{round(t.fill_price, 2)}"
        if key in state["logged_fills"]:
            continue
        state["logged_fills"].append(key)
        append_trade_row(t, "closed")
        tg(f"[SHADOW {RULE_NAME}] trade closed: {t.exit_reason.upper()} {t.r:+.2f}R\n"
           f"filled {t.fill_price:.2f} @ {t.fill_time.strftime('%d %b %H:%M')}  "
           f"exit {t.exit_price:.2f} @ {t.exit_time.strftime('%d %b %H:%M')}")
    state["announced_signals"] = state["announced_signals"][-200:]
    state["last_run"] = datetime.now(timezone.utc).isoformat()
    state["last_bar"] = last_bar.isoformat()
    save_state(state)
    return len(trades)


def main():
    os.makedirs(OUT_DIR, exist_ok=True)
    mcp_initialize()
    strategy = build_strategy()
    costs = CostModel()
    state = load_state()
    tg(f"[SHADOW {RULE_NAME}] started on {SYMBOL}. Params: {json.dumps(all_params(strategy))}. Paper only.")
    while True:
        try:
            n = once(strategy, state, costs)
            print(f"{datetime.now(timezone.utc):%H:%M:%S} ok, {n} trades in window, last bar {state['last_bar']}")
        except Exception as e:
            print(f"[shadow] error: {e}\n{traceback.format_exc()}")
            try:
                mcp_initialize()
            except Exception:
                pass
        # sleep to 20s past the next 5-minute boundary
        now = datetime.now(timezone.utc)
        nxt = now.replace(second=20, microsecond=0) + timedelta(minutes=5 - now.minute % 5)
        time.sleep(max(5, (nxt - now).total_seconds()))


if __name__ == "__main__":
    main()
