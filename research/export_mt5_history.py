"""
export_mt5_history.py -- pull full XAUUSD.m candle history off a live MT5
terminal via its MCP server, into CSVs for the research harness.

Run on the VPS next to the B bridge, with the same env vars:
    set MCP_PORT=<B's port>
    set MCP_API_KEY=<B's key>
    set SYMBOL=XAUUSD.m
    python export_mt5_history.py

Writes data/XAUUSD.m_M5.csv and data/XAUUSD.m_M1.csv (UTC timestamps,
bid OHLC + tick volume + spread where the broker supplies it). Walks
BACKWARDS from now in weekly chunks and stops when the broker's history
runs out, so rows are newest-first; the harness sorts on load.
Re-running appends only candles newer than the first row in the file.
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
PERIODS = os.environ.get("PERIODS", "M5,M1").split(",")
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


def newest_saved_time(path):
    """File is newest-first: the first data row is the most recent candle."""
    if not os.path.exists(path):
        return None
    with open(path) as f:
        next(f, None)
        line = next(f, "").strip()
    return datetime.fromisoformat(line.split(",")[0]) if line else None


def fetch_chunk(period, t_from, t_to):
    resp = mcp_call_tool("get_chart_history", {
        "symbol": SYMBOL, "period": period,
        "datetime_from": t_from.isoformat(), "datetime_to": t_to.isoformat(),
    })
    return resp.get("history", []) or []


def export_period(period):
    os.makedirs(OUT_DIR, exist_ok=True)
    path = os.path.join(OUT_DIR, f"{SYMBOL}_{period}.csv")
    now = datetime.now(timezone.utc)
    floor = now - timedelta(days=365 * YEARS_BACK)
    newest = newest_saved_time(path)
    new_file = not os.path.exists(path)
    if newest:
        floor = newest + timedelta(minutes=1)
        print(f"[{period}] resuming: fetching candles newer than {newest.isoformat()}")
    else:
        print(f"[{period}] exporting backwards from now until history ends (max {YEARS_BACK}y) -> {path}")

    rows = []
    chunk_end = now
    empty = 0
    while chunk_end > floor:
        chunk_start = max(chunk_end - timedelta(days=CHUNK_DAYS), floor)
        candles = fetch_chunk(period, chunk_start, chunk_end)
        candles = [c for c in candles if floor <= parse_time(c["time"]) < chunk_end]
        if candles:
            empty = 0
            candles.sort(key=lambda c: c["time"], reverse=True)
            rows.extend(candles)
            print(f"[{period}] {chunk_start.date()} -> {chunk_end.date()}: {len(candles)} candles ({len(rows)} total)")
        else:
            empty += 1
            print(f"[{period}] {chunk_start.date()} -> {chunk_end.date()}: empty ({empty})")
            if empty >= 4:
                print(f"[{period}] history appears to end around {chunk_end.date()}. Stopping.")
                break
        chunk_end = chunk_start
        time.sleep(0.2)

    if not rows:
        print(f"[{period}] nothing new to write")
        return
    # newest-first file: new rows go above the existing content
    old = ""
    if not new_file:
        with open(path) as f:
            next(f, None)
            old = f.read()
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["time", "open", "high", "low", "close", "tick_volume", "spread"])
        for c in rows:
            w.writerow([parse_time(c["time"]).isoformat(), c["open"], c["high"], c["low"], c["close"],
                        c.get("tick_volume", c.get("volume", "")), c.get("spread", "")])
        f.write(old)
    print(f"[{period}] done: {len(rows)} candles written, oldest {parse_time(rows[-1]['time']).date()}, newest {parse_time(rows[0]['time']).date()}")


if __name__ == "__main__":
    mcp_initialize()
    specs = mcp_call_tool("get_marketwatch_symbols", {"symbol": SYMBOL})
    s = (specs.get("symbols") or [{}])[0]
    print(f"Symbol {SYMBOL}: bid={s.get('bid')} ask={s.get('ask')} contract_size={s.get('contract_size')} "
          f"digits={s.get('digits')} -- note the live spread now as a sanity reference")
    for p in PERIODS:
        export_period(p.strip())