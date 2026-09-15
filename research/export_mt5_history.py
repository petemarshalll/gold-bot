"""
export_mt5_history.py -- pull full XAUUSD.m candle history off a live MT5
terminal via its MCP server, into CSVs for the research harness.

Run on the VPS next to the B bridge, with the same env vars:
    set MCP_PORT=<B's port>
    set MCP_API_KEY=<B's key>
    set SYMBOL=XAUUSD.m
    python export_mt5_history.py

Writes data/XAUUSD.m_M1.csv and data/XAUUSD.m_M5.csv (UTC timestamps,
bid OHLC + tick volume + spread where the broker supplies it). Resumable:
re-running only fetches candles newer than what's already saved.
"""
import csv
import json
import os
import sys
import time
from datetime import datetime, timedelta, timezone

import requests

MCP_PORT = os.environ.get("MCP_PORT", "22346")
MCP_URL = f"http://127.0.0.1:{MCP_PORT}/mcp"
MCP_API_KEY = os.environ.get("MCP_API_KEY", "")
SYMBOL = os.environ.get("SYMBOL", "XAUUSD.m")
PERIODS = os.environ.get("PERIODS", "M1,M5").split(",")
YEARS_BACK = int(os.environ.get("YEARS_BACK", "5"))
CHUNK_DAYS = int(os.environ.get("CHUNK_DAYS", "7"))
OUT_DIR = os.environ.get("OUT_DIR", "data")

if not MCP_API_KEY:
    sys.exit("MCP_API_KEY must be set (MT5 Options > MCP tab).")

session_id = None


def mcp_initialize():
    global session_id
    headers = {"Content-Type": "application/json", "Authorization": f"Bearer {MCP_API_KEY}"}
    payload = {"jsonrpc": "2.0", "id": 1, "method": "initialize",
               "params": {"protocolVersion": "2025-06-18", "capabilities": {},
                          "clientInfo": {"name": "gold-bot-exporter", "version": "1.0"}}}
    resp = requests.post(MCP_URL, json=payload, headers=headers, timeout=15)
    session_id = resp.headers.get("Mcp-Session-Id")
    headers["Mcp-Session-Id"] = session_id
    requests.post(MCP_URL, json={"jsonrpc": "2.0", "method": "notifications/initialized", "params": {}},
                  headers=headers, timeout=15)


def mcp_call_tool(name, arguments, retries=3):
    last = None
    for attempt in range(retries):
        headers = {"Content-Type": "application/json", "Authorization": f"Bearer {MCP_API_KEY}",
                   "Mcp-Session-Id": session_id}
        payload = {"jsonrpc": "2.0", "id": 2, "method": "tools/call",
                   "params": {"name": name, "arguments": arguments}}
        try:
            resp = requests.post(MCP_URL, json=payload, headers=headers, timeout=60)
            if resp.status_code != 200:
                raise Exception(f"status {resp.status_code}: {resp.text[:200]}")
            outer = resp.json()
            if "error" in outer:
                raise Exception(outer["error"])
            return json.loads(outer["result"]["content"][0]["text"])
        except Exception as e:
            last = e
            mcp_initialize()
            time.sleep(2 * (attempt + 1))
    raise Exception(f"MCP tool {name} failed after {retries} attempts: {last}")


def parse_time(s):
    return datetime.strptime(s, "%Y.%m.%d %H:%M:%S").replace(tzinfo=timezone.utc)


def last_saved_time(path):
    if not os.path.exists(path):
        return None
    with open(path, "rb") as f:
        f.seek(0, os.SEEK_END)
        size = f.tell()
        f.seek(max(0, size - 4096))
        tail = f.read().decode(errors="ignore").strip().splitlines()
    for line in reversed(tail):
        if line and not line.startswith("time"):
            return datetime.fromisoformat(line.split(",")[0])
    return None


def export_period(period):
    os.makedirs(OUT_DIR, exist_ok=True)
    path = os.path.join(OUT_DIR, f"{SYMBOL}_{period}.csv")
    now = datetime.now(timezone.utc)
    resume_from = last_saved_time(path)
    start = (resume_from + timedelta(minutes=1)) if resume_from else (now - timedelta(days=365 * YEARS_BACK))
    new_file = not os.path.exists(path)
    print(f"[{period}] exporting from {start.isoformat()} to now -> {path}")

    written = 0
    empty_chunks = 0
    with open(path, "a", newline="") as f:
        w = csv.writer(f)
        if new_file:
            w.writerow(["time", "open", "high", "low", "close", "tick_volume", "spread"])
        chunk_start = start
        while chunk_start < now:
            chunk_end = min(chunk_start + timedelta(days=CHUNK_DAYS), now)
            resp = mcp_call_tool("get_chart_history", {
                "symbol": SYMBOL, "period": period,
                "datetime_from": chunk_start.isoformat(),
                "datetime_to": chunk_end.isoformat(),
            })
            candles = resp.get("history", [])
            if not candles:
                empty_chunks += 1
                if empty_chunks >= 8 and written == 0:
                    print(f"[{period}] {empty_chunks} empty chunks in a row and nothing written yet: "
                          f"broker history probably starts later than {chunk_start.date()}. Moving on.")
                    empty_chunks = 0
            else:
                empty_chunks = 0
                for c in candles:
                    t = parse_time(c["time"])
                    if t < chunk_start:
                        continue
                    w.writerow([t.isoformat(), c["open"], c["high"], c["low"], c["close"],
                                c.get("tick_volume", c.get("volume", "")), c.get("spread", "")])
                    written += 1
                f.flush()
                print(f"[{period}] {chunk_start.date()} -> {chunk_end.date()}: {len(candles)} candles ({written} total)")
            chunk_start = chunk_end
            time.sleep(0.3)
    print(f"[{period}] done: {written} new candles written to {path}")


if __name__ == "__main__":
    mcp_initialize()
    specs = mcp_call_tool("get_marketwatch_symbols", {"symbol": SYMBOL})
    s = (specs.get("symbols") or [{}])[0]
    print(f"Symbol {SYMBOL}: bid={s.get('bid')} ask={s.get('ask')} contract_size={s.get('contract_size')} "
          f"digits={s.get('digits')} -- note the live spread now as a sanity reference")
    for p in PERIODS:
        export_period(p.strip())
