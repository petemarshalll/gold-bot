# ============================================================
# GOLD TRADING ALERT SYSTEM
# TradingView → Claude Analysis → Telegram Notification
# ============================================================

from flask import Flask, request, jsonify
import anthropic
import requests
import os
import json
import csv
import re
import zipfile
import io
import threading
import time
import uuid
from datetime import datetime, timezone, timedelta
from dotenv import load_dotenv
from apscheduler.schedulers.background import BackgroundScheduler
import atexit
import yfinance as yf
import pandas as pd
import numpy as np

load_dotenv()

app = Flask(__name__)

claude_client = anthropic.Anthropic(api_key=os.getenv("ANTHROPIC_API_KEY"))
TELEGRAM_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID")
# Shared secret the MT5 bridge script must send (X-Bridge-Secret header)
# to poll /mt5/pending or report back via /mt5/ack. Set this on Railway
# and on the VPS bridge's own config -- without it, anyone with the
# Railway URL could read pending trade instructions or post fake acks.
MT5_BRIDGE_SECRET = os.getenv("MT5_BRIDGE_SECRET")

# ============================================================
# PERSISTENT DATA DIRECTORY
# Set DATA_DIR env var on Railway to the mount path of an attached
# Volume (e.g. /data) so state survives container restarts/redeploys.
# Falls back to the working directory if not set (NOT safe across
# restarts on Railway's default ephemeral filesystem).
# ============================================================
DATA_DIR = os.getenv("DATA_DIR", ".")
os.makedirs(DATA_DIR, exist_ok=True)

def data_path(filename):
    return os.path.join(DATA_DIR, filename)

# ============================================================
# MEMORY
# ============================================================
recent_alerts = []

# ============================================================
# A/B/C VARIANT TESTING (9 Aug)
# Same incoming signal, same shared Claude analysis -- three
# independent judgment calls on whether to act on it, each routed to
# its own real MT5 account so every variant gets genuine, real
# execution data, not a shadow approximation.
#
# A: current system exactly as-is (control).
# B: same, but the FVG/SWEEP confidence-override rules never run --
#    confidence stays at Claude's own raw, original value.
# C: same as A (override included), but additionally requires a real
#    confluence-score floor before taking the trade -- there isn't
#    one today.
#
# Every one of the ten pieces of state below is keyed by variant, so
# each account's trades, balance, and daily/consecutive-loss counters
# are genuinely isolated from the other two -- a bad day on B can't
# touch A or C's own limits, same as three separate real accounts.
# ============================================================
VARIANTS = ["A", "B", "C"]
VARIANT_MIN_CONFLUENCE_SCORE = 6  # C's explicit floor -- A and B have none

paper_trades = {v: [] for v in VARIANTS}
active_trades = {v: {} for v in VARIANTS}
consecutive_losses = {v: 0 for v in VARIANTS}
shadow_trades = {v: [] for v in VARIANTS}
active_shadow_trades = {v: {} for v in VARIANTS}
mt5_pending_trades = {v: {} for v in VARIANTS}
current_balance = {v: 10000 for v in VARIANTS}
daily_pnl = {v: 0 for v in VARIANTS}
total_pnl = {v: 0 for v in VARIANTS}
trading_days = {v: 0 for v in VARIANTS}

drawdown_protection = {v: False for v in VARIANTS}

# Set False to re-enable drawdown protection's real effects (reduced
# sizing, raised confidence bar) once past pure data-gathering and
# real capital is actually at stake. consecutive_losses itself still
# gets tracked normally either way -- this only controls whether that
# count is allowed to actually change trade behavior.
DRAWDOWN_PROTECTION_DISABLED = True
# Re-enabled (8 Aug) after its absence directly caused a real FTMO
# breach: disabled during 5 Aug, 5 real losses totalled -$519.64
# against the -$500 daily limit with nothing to stop new trades once
# the day's losses got close -- account was auto-closed and locked
# read-only as a direct result. This is the real enforcement
# (check_risk_cap_before_trade) -- separate from the daily loss
# WARNING messages sent to Telegram, which are purely informational
# either way and fire regardless of this flag.
DAILY_LOSS_LIMIT_DISABLED = False
last_trading_day = {v: None for v in VARIANTS}
last_pnl_reset_day = None
daily_alert_count = 0
scheduler = None

# ============================================================
# VERSION TAGGING
# Every trade (real and shadow) stores which version of the bot
# produced it, so results stay comparable across future changes
# instead of silently mixing data generated under different logic.
# Bump this whenever a change could meaningfully affect trade
# decisions (confidence gating, entry logic, risk sizing, etc).
# ============================================================
# 1.1.0 (16 Aug): variant A's entry-gate/exclude/target-scaling rebuild.
# The comment above the A-rebuild code in the per-variant loop already
# promised old-vs-new A trades would be separable by this bump; it
# just never actually happened until now. (In the meantime,
# target_scaled_to_pct's presence on a trade record is an equivalent
# way to tell them apart.)
# 1.2.0 (17 Aug): B and C rebuilt the same way A was -- B on
# B-exact-OR-zone-strict excluding confluence-only/stacked; C on
# sweep-OR-zone-strict excluding confluence-only/killzone-only. Both
# at an 80% scaled target. Built from replay testing on the same real
# 15m/60d and 1h/2y batches used for A. B's combo held up on both
# datasets; C's did not (0.29R on 15m/60d vs 0.05R on 1h/2y) and
# shipped anyway as a live continuation of that test, Pete's explicit
# call.
BOT_VERSION = "1.2.0"

# ============================================================
# SHADOW TRACKING
# Tracks the outcome of alerts that DIDN'T become real trades —
# rejected for low confidence, or because price never reached the
# stated entry zone — but where Claude gave real, extractable
# stop/target numbers. Kept completely separate from real trades:
# separate storage, separate monitoring, never touches daily_pnl,
# total_pnl, current_balance, or drawdown_protection. An explicit
# "No trade" / N/A response has nothing to test and is correctly
# never tracked here.
# ============================================================
# SHADOW TRACKING
# Tracks the outcome of alerts that DIDN'T become real trades —
# rejected for low confidence, or because price never reached the
# stated entry zone — but where Claude gave real, extractable
# stop/target numbers. Kept completely separate from real trades:
# separate storage, separate monitoring, never touches daily_pnl,
# total_pnl, current_balance, or drawdown_protection. An explicit
# "No trade" / N/A response has nothing to test and is correctly
# never tracked here. (Declared above, keyed by variant.)
# ============================================================

# ============================================================
# MT5 BRIDGE QUEUE
# Every trade that passes the SAME would_log gate as a normal paper
# trade also gets dropped here for the Windows-VPS bridge script to
# pick up and place on a real MT5 terminal. This is deliberately
# additive only -- it reuses the exact decision Claude already made
# for the paper trade (same confidence gate, same entry/stop/target),
# rather than introducing any new logic that could disagree with it.
# Status flow: PENDING -> DISPATCHED (served via GET, not yet
# confirmed) -> PLACED (bridge confirmed a real ticket) or FAILED
# (bridge reported an error, e.g. market closed, invalid symbol).
# (Declared above, keyed by variant.)
# ============================================================

# ============================================================
# PROP FIRM RULES
# ============================================================
PROP_FIRM_RULES = {
    "account_size": 10000,
    # FTMO 2-Step Challenge real published rules (verified 2 Aug 2026,
    # previously rough placeholders from early in the project).
    "max_daily_loss_pct": 5.0,
    "max_total_drawdown_pct": 10.0,   # static/non-trailing on the 2-Step path
    "min_trading_days": 4,             # per phase -- matches FTMO's number already
    "max_loss_per_trade_pct": 0.5,     # halved from 1.0% (8 Aug), directly
    # because of a real breach: 5 real losses on 5 Aug totalled -$519.64
    # against FTMO's -$500 (5%) daily limit -- at 0.5% risk, the same
    # 5-loss streak would only total ~-$260, comfortably inside the
    # limit even with the daily-loss-limit enforcement re-disabled.
}

# Computed once, when this process starts -- the actual empirical test
# for whether Railway is running more than one instance of this app.
# A single process always returns the same ID; if repeated calls to
# /mt5/status show different IDs, that's direct proof of more than
# one process independently handling requests, each with its own
# separate in-memory state (confirmed as the likely explanation for
# a genuine, repeated symptom, 5 Aug -- admin/recent-trades showing
# stale data even after a real closure had already been correctly
# reported by the bridge).
INSTANCE_ID = str(uuid.uuid4())[:8]
INSTANCE_STARTED_AT = datetime.now(timezone.utc).isoformat()

# Bridge watchdog state -- tracks whether the local MT5 bridge is
# still alive and polling, so a silent crash/disconnect/PC sleep
# during an open position doesn't go unnoticed. Tightened from 3min to
# 1min (5 Aug) -- while Task Scheduler auto-recovery is paused for
# reliability testing, this alert is the entire recovery mechanism,
# not just a backup notification, so the gap before it fires matters
# much more than it used to. The bridge heartbeats every 20s, so 1min
# still tolerates a couple of missed beats before firing.
#
# One watchdog entry PER VARIANT (9 Aug) -- three separate bridges now,
# each needs its own liveness tracking; one going quiet shouldn't be
# masked by the other two still heartbeating fine.
last_bridge_heartbeat = {v: None for v in VARIANTS}
bridge_watchdog_alerted = {v: False for v in VARIANTS}
BRIDGE_HEARTBEAT_TIMEOUT_MINUTES = 1

# Live price/candles relayed from the bridge -- genuinely shared
# across all three variants (gold's real price is the same number
# regardless of which account it's viewed from), so only ONE bridge
# needs to relay this (variant A's, by convention) rather than three
# redundant copies of identical market data. Falls back to yfinance
# if the bridge hasn't sent an update recently -- e.g. bridge briefly
# down -- so monitoring never just stops working.
mt5_live_price = {"bid": None, "ask": None, "updated_at": None}
MT5_PRICE_STALENESS_SECONDS = 60

# ============================================================
# KEY LEVELS
# ============================================================
KEY_LEVELS = {
    "weekly_high": 4200.00,
    "weekly_low": 3950.00,
    "major_resistance": 4100.00,
    "major_support": 3975.00,
    "daily_high": 4091.00,
    "daily_low": 4064.00,
    "dealing_range_high": 4100.00,
    "dealing_range_low": 3975.00,
}

# ============================================================
# PERSISTENT DATA
# ============================================================
def save_state():
    try:
        state = {
            "key_levels": KEY_LEVELS,
            "paper_trades": paper_trades,
            "active_trades": active_trades,
            "shadow_trades": shadow_trades,
            "active_shadow_trades": active_shadow_trades,
            "daily_pnl": daily_pnl,
            "total_pnl": total_pnl,
            "current_balance": current_balance,
            "trading_days": trading_days,
            "consecutive_losses": consecutive_losses,
            "last_trading_day": last_trading_day,
            "last_pnl_reset_day": last_pnl_reset_day,
            "daily_alert_count": daily_alert_count,
        }
        with open(data_path('bot_state.json'), 'w') as f:
            json.dump(state, f, indent=2)
        print("State saved successfully")
    except Exception as e:
        print(f"State save error: {e}")


def load_state():
    global KEY_LEVELS, paper_trades, active_trades, daily_pnl, total_pnl
    global current_balance, trading_days, consecutive_losses, last_trading_day
    global last_pnl_reset_day, daily_alert_count, shadow_trades, active_shadow_trades
    try:
        with open(data_path('bot_state.json'), 'r') as f:
            state = json.load(f)
        KEY_LEVELS.update(state.get('key_levels', {}))
        saved_paper_trades = state.get('paper_trades', {})
        if isinstance(saved_paper_trades, list):
            # Old, pre-variant flat format (from the now-ended FTMO
            # account) -- deliberately NOT migrated into any one
            # variant, since guessing which of A/B/C it "belongs" to
            # would be arbitrary and misleading. Starts fresh instead.
            print("Old flat-format state found (pre-A/B/C) -- starting fresh for the new variant structure, not migrating it")
        else:
            paper_trades = {v: saved_paper_trades.get(v, []) for v in VARIANTS}
            active_trades = {v: state.get('active_trades', {}).get(v, {}) for v in VARIANTS}
            shadow_trades = {v: state.get('shadow_trades', {}).get(v, []) for v in VARIANTS}
            active_shadow_trades = {v: state.get('active_shadow_trades', {}).get(v, {}) for v in VARIANTS}
            daily_pnl = {v: state.get('daily_pnl', {}).get(v, 0) for v in VARIANTS}
            total_pnl = {v: state.get('total_pnl', {}).get(v, 0) for v in VARIANTS}
            current_balance = {v: state.get('current_balance', {}).get(v, 10000) for v in VARIANTS}
            trading_days = {v: state.get('trading_days', {}).get(v, 0) for v in VARIANTS}
            consecutive_losses = {v: state.get('consecutive_losses', {}).get(v, 0) for v in VARIANTS}
            # Was loaded unconditionally below, outside this guard --
            # the one per-variant field that skipped the same
            # old-format safety net every field above it goes through.
            # Harmless while bot_state.json already has this in the
            # current per-variant shape (true today, since real trades
            # have been closing correctly all week, which apply_trade_pnl
            # couldn't do if this were ever the wrong type), but a
            # latent break if the state file is ever reset or hand-
            # edited: last_trading_day[variant] would then be indexing
            # into None or a bare string instead of a dict. Moved inside
            # this branch and loaded defensively like its siblings.
            last_trading_day = {v: state.get('last_trading_day', {}).get(v) for v in VARIANTS}
        last_pnl_reset_day = state.get('last_pnl_reset_day', None)
        daily_alert_count = state.get('daily_alert_count', 0)
        # Self-heal immediately on load, not just on the next risk
        # check — keeps /health, /prop-status etc accurate right away
        # after any restart, e.g. after several idle days.
        ensure_daily_reset()
        # drawdown_protection itself isn't persisted (only the
        # consecutive_losses count is) — recompute it here, per
        # variant, so a restart can't show a misleading "OFF" status
        # when the underlying loss streak actually hasn't cleared.
        for v in VARIANTS:
            check_drawdown_protection(v)
        counts = {v: len(paper_trades[v]) for v in VARIANTS}
        print(f"State loaded — trades per variant: {counts}, balances: {current_balance}")
    except FileNotFoundError:
        print("No saved state found — starting fresh")
    except Exception as e:
        print(f"State load error: {e}")
    load_mt5_queue()

# ============================================================
# MARKET HOURS CHECK
# ============================================================
def is_market_open():
    # Real gold market schedule (confirmed 2 Aug 2026): opens Sunday
    # 22:00 UTC, closes Friday 22:00 UTC -- was previously 21:00,
    # quietly wrong by an hour, which is directly why tonight's
    # 21:12 UTC check looked "past reopen" when the market was
    # genuinely still closed. Note: 22:00 reflects current US/UK
    # daylight saving -- may need revisiting once DST ends (~Nov).
    now = datetime.now(timezone.utc)
    hour = now.hour
    weekday = now.weekday()
    if weekday == 5:
        return False
    if weekday == 6 and hour < 22:
        return False
    if weekday == 4 and hour >= 22:
        return False
    return True

# ============================================================
# PRICE DATA FRESHNESS CHECK
# yfinance's free intraday feed can lag or briefly stall — most
# often seen around gold's daily settlement/rollover window
# (~22:00-23:00 UTC) or thin Asian-session liquidity. Without this
# check, a stale "latest" candle gets silently trusted as the
# current price, which can produce a wrong current-price readout in
# alerts and a wrong basis for SL/TP or entry-zone checks. This
# skips acting on the data for one cycle rather than risk that.
# ============================================================
def is_price_data_stale(gold_df, max_age_minutes=15):
    try:
        last_ts = gold_df.index[-1]
        if getattr(last_ts, 'tzinfo', None) is None:
            last_ts = last_ts.tz_localize('UTC')
        else:
            last_ts = last_ts.tz_convert('UTC')
        age_seconds = (datetime.now(timezone.utc) - last_ts.to_pydatetime()).total_seconds()
        return age_seconds > max_age_minutes * 60
    except Exception:
        return False  # fail open — don't block a check over a parsing issue

# ============================================================
# SESSION DETECTION
# ============================================================
def get_session():
    hour = datetime.now(timezone.utc).hour
    if 22 <= hour or hour < 7:
        return "Asian Session", "low liquidity — be cautious", False
    elif 7 <= hour < 9:
        return "London Open Killzone", "HIGH PROBABILITY WINDOW — institutional orders firing", True
    elif 9 <= hour < 12:
        return "London Session", "good activity — valid setups", True
    elif 12 <= hour < 14:
        return "New York Open Killzone", "HIGH PROBABILITY WINDOW — institutional orders firing", True
    elif 14 <= hour < 17:
        return "New York Session", "high volatility — valid setups", True
    elif 17 <= hour < 20:
        return "London Close", "watch for reversals and stop hunts", False
    else:
        return "Dead Zone", "NY close — avoid new trades", False

# ============================================================
# PREMIUM / DISCOUNT ZONE
# ============================================================
def get_premium_discount(price):
    try:
        price = float(price)
        high = KEY_LEVELS["dealing_range_high"]
        low = KEY_LEVELS["dealing_range_low"]
        # dealing_range only gets a full recalculation once a week
        # (Sunday auto-levels). If price breaks outside that range
        # before the next refresh, expand it to include the breakout
        # rather than silently showing a percentage below 0% or above
        # 100% against a now-stale range.
        if price > high:
            KEY_LEVELS["dealing_range_high"] = price
            high = price
        if price < low:
            KEY_LEVELS["dealing_range_low"] = price
            low = price
        midpoint = (high + low) / 2
        percentage = ((price - low) / (high - low)) * 100 if high != low else 50.0
        if price > midpoint:
            zone = "PREMIUM"
            advice = "price is expensive — favour shorts, be cautious on longs"
        else:
            zone = "DISCOUNT"
            advice = "price is cheap — favour longs, be cautious on shorts"
        return zone, round(percentage, 1), advice
    except:
        return "UNKNOWN", 0, "unable to calculate"

# ============================================================
# SPREAD MONITOR
# ============================================================
def check_spread(high, low, price):
    try:
        high = float(high)
        low = float(low)
        price = float(price)
        candle_range = high - low
        spread_pct = (candle_range / price) * 100
        if spread_pct > 0.5:
            return True, f"⚠️ VERY WIDE spread ({spread_pct:.2f}%) — high slippage risk, avoid entry"
        elif spread_pct > 0.3:
            return True, f"⚠️ Wide spread ({spread_pct:.2f}%) — reduce position size if entering"
        else:
            return False, f"Spread normal ({spread_pct:.2f}%) — good entry conditions"
    except Exception as e:
        return False, "Spread check unavailable"

# ============================================================
# NEWS RISK CHECK
# ============================================================
def check_news_risk():
    finnhub_key = os.getenv("FINNHUB_API_KEY")  # outside the try so it's always defined for the except block's redaction below
    try:
        if not finnhub_key:
            return check_news_risk_fallback()
        today = datetime.now(timezone.utc).strftime('%Y-%m-%d')
        url = f"https://finnhub.io/api/v1/calendar/economic?from={today}&to={today}&token={finnhub_key}"
        response = requests.get(url, timeout=5)
        if response.status_code != 200:
            return check_news_risk_fallback()
        data = response.json()
        events = data.get('economicCalendar', [])
        high_impact_keywords = ['NFP', 'Non-Farm', 'CPI', 'Fed', 'FOMC', 'Interest Rate', 'GDP', 'Unemployment', 'Inflation', 'Powell', 'Treasury']
        now_utc = datetime.now(timezone.utc)
        current_minutes = now_utc.hour * 60 + now_utc.minute
        for event in events:
            impact = event.get('impact', '').lower()
            event_name = event.get('event', '')
            event_time = event.get('time', '')
            if impact not in ['high', '3']:
                continue
            is_relevant = any(kw.lower() in event_name.lower() for kw in high_impact_keywords)
            if not is_relevant:
                continue
            try:
                if event_time:
                    event_dt = datetime.strptime(f"{today} {event_time}", '%Y-%m-%d %H:%M')
                    event_minutes = event_dt.hour * 60 + event_dt.minute
                    time_diff = abs(current_minutes - event_minutes)
                    if time_diff <= 30:
                        return True, f"⚠️ HIGH IMPACT: {event_name} at {event_time} UTC — avoid new trades"
            except:
                continue
        return False, "No major news risk detected"
    except Exception as e:
        # requests' own connection/timeout exceptions often embed the
        # full request URL in str(e) -- redact the key so a Finnhub
        # blip can't dump it into Railway's console in plaintext.
        safe_error = str(e).replace(finnhub_key, "[REDACTED]") if finnhub_key else str(e)
        print(f"News calendar error: {safe_error}")
        return check_news_risk_fallback()


def check_news_risk_fallback():
    hour = datetime.now(timezone.utc).hour
    minute = datetime.now(timezone.utc).minute
    weekday = datetime.now(timezone.utc).weekday()
    high_risk_times = [(13, 30), (15, 0), (12, 0)]
    for risk_hour, risk_minute in high_risk_times:
        time_diff = abs((hour * 60 + minute) - (risk_hour * 60 + risk_minute))
        if time_diff <= 30:
            return True, f"High impact news window — within 30 mins of {risk_hour}:{risk_minute:02d} UTC"
    if weekday == 4 and 13 <= hour <= 14:
        return True, "NFP Friday risk window — avoid new trades"
    return False, "No major news risk detected"

# ============================================================
# HOUR QUALITY FILTER
# ============================================================
def check_hour_quality():
    hour = datetime.now(timezone.utc).hour
    best_hours = [21, 22, 23]
    worst_hours = [3, 6, 14]
    if hour in best_hours:
        return "OPTIMAL", f"Hour {hour}:00 UTC historically shows 55-56% win rate — weight signals higher"
    elif hour in worst_hours:
        return "POOR", f"Hour {hour}:00 UTC historically shows 44-45% win rate — reduce confidence"
    else:
        return "NORMAL", f"Hour {hour}:00 UTC — standard win rate expected"

# ============================================================
# DRAWDOWN PROTECTION
# ============================================================
def check_drawdown_protection(variant):
    global consecutive_losses, drawdown_protection
    if DRAWDOWN_PROTECTION_DISABLED:
        drawdown_protection[variant] = False
        return False, "Normal trading mode (drawdown protection disabled for data-gathering phase)"
    if consecutive_losses[variant] >= 3:
        drawdown_protection[variant] = True
        return True, f"⚠️ DRAWDOWN PROTECTION ACTIVE — {consecutive_losses[variant]} consecutive losses."
    drawdown_protection[variant] = False
    return False, "Normal trading mode"

# ============================================================
# DXY CORRELATION
# ============================================================
def get_dxy_bias():
    try:
        dxy = yf.download('DX-Y.NYB', period='5d', interval='1h', progress=False, timeout=10)
        if dxy.empty:
            return "UNKNOWN", "DXY data unavailable", "NEUTRAL"
        if isinstance(dxy.columns, pd.MultiIndex):
            dxy.columns = [col[0] for col in dxy.columns]
        dxy = dxy.dropna(subset=['Close'])
        if len(dxy) < 5:
            return "UNKNOWN", "DXY insufficient data", "NEUTRAL"
        closes = dxy['Close'].values
        current = float(closes[-1])
        previous = float(closes[-5])
        change_pct = ((current - previous) / previous) * 100
        if change_pct > 0.15:
            direction = "BULLISH"
            desc = f"DXY rising +{change_pct:.2f}% — BEARISH for gold"
            implication = "BEARISH"
        elif change_pct < -0.15:
            direction = "BEARISH"
            desc = f"DXY falling {change_pct:.2f}% — BULLISH for gold"
            implication = "BULLISH"
        else:
            direction = "NEUTRAL"
            desc = f"DXY flat ({change_pct:.2f}%) — no strong gold bias"
            implication = "NEUTRAL"
        return direction, desc, implication
    except Exception as e:
        return "UNKNOWN", f"DXY check failed: {str(e)}", "NEUTRAL"


def get_dxy_confluence(direction, dxy_implication):
    """
    Checks DXY against the ACTUAL trade direction Claude settles on,
    not the raw alert_type keyword. Sweep-type alerts are frequently
    reversal signals where the real direction is the opposite of the
    alert label (e.g. BEARISH_SWEEP -> LONG) — checking against
    alert_type would show backwards confluence/conflict information
    whenever DXY has a real directional bias.
    """
    if direction == "SHORT" and dxy_implication == "BEARISH":
        return "✅ STRONG CONFLUENCE — DXY rising confirms bearish gold bias", 2
    elif direction == "LONG" and dxy_implication == "BULLISH":
        return "✅ STRONG CONFLUENCE — DXY falling confirms bullish gold bias", 2
    elif dxy_implication == "NEUTRAL":
        return "⚠️ NEUTRAL — DXY flat, no additional confluence", 0
    else:
        return "❌ CONFLICT — DXY opposes this gold signal, reduce confidence", -1

# ============================================================
# COT REPORT
# ============================================================
def get_cot_fallback():
    return {
        "date": "unavailable",
        "spec_bias": "UNKNOWN",
        "spec_desc": "COT data unavailable this week",
        "change_desc": "Check cftc.gov for latest positioning",
        "net_position": 0,
        "net_change": 0
    }


def get_cot_data():
    try:
        year = datetime.now(timezone.utc).year
        url = f"https://www.cftc.gov/files/dea/history/fut_fin_xls_{year}.zip"
        response = requests.get(url, timeout=15)
        if response.status_code != 200:
            return get_cot_fallback()
        z = zipfile.ZipFile(io.BytesIO(response.content))
        filename = z.namelist()[0]
        with z.open(filename) as f:
            df = pd.read_excel(f)
        if df.empty:
            return get_cot_fallback()
        gold = df[df['Market and Exchange Names'].str.contains('GOLD', case=False, na=False)]
        if gold.empty:
            return get_cot_fallback()
        gold = gold.sort_values('As of Date in Form YYYY-MM-DD', ascending=False)
        latest = gold.iloc[0]
        previous = gold.iloc[1] if len(gold) > 1 else gold.iloc[0]
        noncomm_long = int(latest.get('Noncommercial Positions-Long (All)', 0))
        noncomm_short = int(latest.get('Noncommercial Positions-Short (All)', 0))
        prev_long = int(previous.get('Noncommercial Positions-Long (All)', 0))
        prev_short = int(previous.get('Noncommercial Positions-Short (All)', 0))
        date = str(latest.get('As of Date in Form YYYY-MM-DD', 'unknown'))
        net_spec = noncomm_long - noncomm_short
        prev_net = prev_long - prev_short
        net_change = net_spec - prev_net
        if net_spec > 0:
            spec_bias = "NET LONG"
            spec_desc = f"Speculators net long {net_spec:,} contracts — bullish institutional bias"
        else:
            spec_bias = "NET SHORT"
            spec_desc = f"Speculators net short {abs(net_spec):,} contracts — bearish institutional bias"
        if net_change > 0:
            change_desc = f"Increasing longs (+{net_change:,} contracts this week)"
        else:
            change_desc = f"Increasing shorts ({net_change:,} contracts this week)"
        return {
            "date": date,
            "spec_bias": spec_bias,
            "spec_desc": spec_desc,
            "change_desc": change_desc,
            "net_position": net_spec,
            "net_change": net_change
        }
    except Exception as e:
        print(f"COT error: {e}")
        return get_cot_fallback()

# ============================================================
# CLAUDE API CALL WITH RETRY
# Wraps every claude_client.messages.create() call with a couple of
# short retries on transient failures (rate limits, momentary 5xx,
# network blips). The bot runs unattended for days at a time, so a
# single dropped API call shouldn't silently lose an alert's
# analysis or a scheduled report.
# ============================================================
def call_claude(messages, max_tokens=400, thinking=None, retries=2, base_delay=2):
    last_error = None
    for attempt in range(retries + 1):
        try:
            kwargs = {
                "model": "claude-sonnet-4-6",
                "max_tokens": max_tokens,
                "messages": messages,
            }
            if thinking:
                kwargs["thinking"] = thinking
            return claude_client.messages.create(**kwargs)
        except Exception as e:
            last_error = e
            if attempt < retries:
                wait = base_delay * (2 ** attempt)
                print(f"Claude API error (attempt {attempt + 1}/{retries + 1}): {e} — retrying in {wait}s")
                time.sleep(wait)
            else:
                print(f"Claude API error — all {retries + 1} attempts failed: {e}")
    raise last_error

# ============================================================
# SEND TELEGRAM
# ============================================================
def send_telegram(message):
    url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"

    def split_message(text, limit=3800):
        if len(text) <= limit:
            return [text]
        chunks = []
        while len(text) > limit:
            split_point = text[:limit].rfind('\n')
            if split_point < 2000:
                split_point = limit
            chunks.append(text[:split_point])
            text = text[split_point:].strip()
        if text:
            chunks.append(text)
        return chunks

    chunks = split_message(message)
    for i, chunk in enumerate(chunks):
        if len(chunks) > 1:
            chunk = f"_{i+1}/{len(chunks)}_\n\n" + chunk
        payload = {
            "chat_id": TELEGRAM_CHAT_ID,
            "text": chunk,
            "parse_mode": "Markdown"
        }
        try:
            response = requests.post(url, json=payload, timeout=10)
            print(f"Telegram sent: {response.status_code}")
            if response.status_code == 400:
                # Was setting parse_mode to the STRING "None" here, which
                # Telegram validates strictly (it even treats "Markdown"
                # and "markdown" differently) and almost certainly also
                # rejected -- meaning this retry silently failed the same
                # way the original attempt did, with nothing anywhere to
                # show it happened. Popping the key entirely is a genuine
                # plain-text fallback: no parse_mode means Telegram can't
                # choke on the message's formatting, whatever it contains.
                payload.pop("parse_mode", None)
                retry_response = requests.post(url, json=payload, timeout=10)
                print(f"Telegram retry (plain text, original parse failed): {retry_response.status_code}")
        except Exception as e:
            print(f"Telegram error: {e}")

# ============================================================
# LOG TO CSV
# ============================================================
def log_to_csv(alert_type, price, confidence, analysis):
    try:
        with open(data_path('trade_log.csv'), 'a', newline='') as f:
            writer = csv.writer(f)
            writer.writerow([
                datetime.utcnow().strftime('%Y-%m-%d %H:%M'),
                alert_type, price, confidence, analysis[:150]
            ])
    except Exception as e:
        print(f"CSV log error: {e}")

# ============================================================
# PAPER TRADE TRACKER
# ============================================================
def log_paper_trade(variant, alert_type, price, direction, entry, stop, target, confidence, alert_time, context=None):
    trade_id = f"{variant}_{alert_type}_{alert_time.replace(':', '').replace(' ', '_')}"
    trade = {
        "id": trade_id,
        "variant": variant,
        "time": alert_time,
        "opened_at": datetime.now(timezone.utc).isoformat(),
        "type": alert_type,
        "price": price,
        "direction": direction,
        "entry": float(entry),
        "stop": float(stop),
        "target": float(target),
        "confidence": confidence,
        "result": "OPEN",
        "bot_version": BOT_VERSION,
    }
    # Extra market context at the moment the trade was logged — session,
    # killzone, premium/discount zone, DXY confluence, confluence score
    # etc — so self-review can find patterns beyond just "alert type",
    # e.g. "BEARISH_FVG wins 80% in a killzone but 35% outside one".
    if context:
        trade.update(context)
    paper_trades[variant].append(trade)
    active_trades[variant][trade_id] = trade
    queue_mt5_trade(variant, trade)
    try:
        with open(data_path('paper_trades.json'), 'w') as f:
            json.dump(paper_trades, f, indent=2)
    except Exception as e:
        print(f"Paper trade log error: {e}")
    return trade_id


def save_mt5_queue():
    try:
        with open(data_path('mt5_queue.json'), 'w') as f:
            json.dump(mt5_pending_trades, f, indent=2)
    except Exception as e:
        print(f"MT5 queue save error: {e}")


def load_mt5_queue():
    global mt5_pending_trades
    try:
        with open(data_path('mt5_queue.json'), 'r') as f:
            loaded = json.load(f)
        mt5_pending_trades = {v: loaded.get(v, {}) for v in VARIANTS} if isinstance(loaded, dict) and any(v in loaded for v in VARIANTS) else {v: {} for v in VARIANTS}
    except FileNotFoundError:
        mt5_pending_trades = {v: {} for v in VARIANTS}
    except Exception as e:
        print(f"MT5 queue load error: {e}")
        mt5_pending_trades = {v: {} for v in VARIANTS}


def queue_mt5_trade(variant, trade):
    """
    Adds a trade that already passed the normal would_log gate to the
    MT5 bridge queue for that specific variant's account. Deliberately
    does NOT re-derive or re-check confidence/validity here -- it
    reuses whatever log_paper_trade was just called with, so this can
    never disagree with the paper-trade decision. risk_pct is read the
    same way apply_trade_pnl() reads it, so a reduced-risk trade during
    drawdown queues at the correct (already-halved) size automatically.
    """
    risk_pct = trade.get('risk_pct', PROP_FIRM_RULES["max_loss_per_trade_pct"])
    mt5_pending_trades[variant][trade['id']] = {
        "trade_id": trade['id'],
        "status": "PENDING",
        "queued_at": datetime.now(timezone.utc).isoformat(),
        "alert_type": trade['type'],
        "direction": trade['direction'],
        "entry": trade['entry'],
        "stop": trade['stop'],
        "target": trade['target'],
        "confidence": trade['confidence'],
        "risk_pct": risk_pct,
        "ticket": None,
        "fill_price": None,
        "error": None,
    }
    save_mt5_queue()


def log_shadow_trade(variant, alert_type, price, direction, entry, stop, target, confidence, rejection_reason, context=None):
    """
    Records an alert that did NOT become a real trade for this
    specific variant, but where Claude gave real, extractable
    stop/target numbers — so its outcome can still be tracked and
    learned from. Completely separate storage from real trades; never
    touches daily_pnl, total_pnl, current_balance, or
    drawdown_protection.
    """
    trade_id = f"SHADOW_{variant}_{alert_type}_{datetime.now(timezone.utc).strftime('%Y%m%d%H%M%S%f')}"
    trade = {
        "id": trade_id,
        "variant": variant,
        "time": datetime.utcnow().strftime('%H:%M UTC'),
        "opened_at": datetime.now(timezone.utc).isoformat(),
        "type": alert_type,
        "price": price,
        "direction": direction,
        "entry": float(entry),
        "stop": float(stop),
        "target": float(target),
        "confidence": confidence,
        "rejection_reason": rejection_reason,
        "result": "OPEN",
        "bot_version": BOT_VERSION,
    }
    if context:
        trade.update(context)
    shadow_trades[variant].append(trade)
    active_shadow_trades[variant][trade_id] = trade
    try:
        with open(data_path('shadow_trades.json'), 'w') as f:
            json.dump(shadow_trades, f, indent=2)
    except Exception as e:
        print(f"Shadow trade log error: {e}")
    return trade_id


def monitor_shadow_trades(variant, gold_df):
    """
    Wick-aware monitoring for shadow trades, reusing the exact same
    scan_candles_for_hit() logic already validated for real trades —
    that function is pure (reads only the trade dict and candle data,
    never touches global state), so it's safe to reuse here unchanged.
    Computes pnl/r_multiple independently for each shadow trade
    without ever calling apply_trade_pnl(), which is what guarantees
    this can never affect real balance, daily_pnl, total_pnl, or
    drawdown_protection.
    """
    trades_to_close = []
    for trade_id, trade in list(active_shadow_trades[variant].items()):
        if trade.get('result') != 'OPEN':
            continue
        hit_type, hit_price, hit_time = scan_candles_for_hit(trade, gold_df)
        if hit_type is None:
            continue
        account = PROP_FIRM_RULES["account_size"]
        risk_amount = account * (PROP_FIRM_RULES["max_loss_per_trade_pct"] / 100)
        if hit_type == 'WIN':
            points = abs(trade['target'] - trade['entry'])
            stop_distance = abs(trade['entry'] - trade['stop'])
            dollar_per_point = (risk_amount / stop_distance) if stop_distance > 0 else 0
            pnl = dollar_per_point * points
        else:
            pnl = -risk_amount
        trade['result'] = hit_type
        trade['pnl'] = round(pnl, 2)
        trade['r_multiple'] = round(pnl / risk_amount, 2) if risk_amount > 0 else 0
        trades_to_close.append(trade_id)
    for trade_id in trades_to_close:
        del active_shadow_trades[variant][trade_id]
    if trades_to_close:
        try:
            with open(data_path('shadow_trades.json'), 'w') as f:
                json.dump(shadow_trades, f, indent=2)
        except Exception as e:
            print(f"Shadow trade update error: {e}")

# ============================================================
# CONFLUENCE SCORE EXTRACTION
# ============================================================
def variant_confluence_ok(variant, confluence_score):
    """C's OLD confluence-score floor (pre-17-Aug) -- superseded by
    variant_c_included/variant_c_excluded, which replaced C's live
    logic entirely. No longer called anywhere in the live decision
    path; left in place (rather than deleted) since it's still the
    correct lens for interpreting any C trade with BOT_VERSION <
    1.2.0, and VARIANT_MIN_CONFLUENCE_SCORE only exists for this."""
    if variant != "C":
        return True
    return confluence_score is not None and confluence_score >= VARIANT_MIN_CONFLUENCE_SCORE


def variant_a_excluded(overridden_confidence, raw_confidence, confluence_score, is_killzone, direction, dxy_implication):
    """
    A's real-time "emergency brake" (16 Aug) -- given a signal that
    already has a real, valid, reachable trade (checked separately by
    the caller), this returns True if it should be excluded anyway
    because it independently satisfies one of the three specific
    patterns the full 2-year replay showed performing worse: C's own
    gate, the raw confluence-only gate, or the maximally-selective
    "everything stacked" gate.

    Deliberately mirrors filter_C_exact / filter_confluence_only /
    filter_stacked (used throughout the /replay-* endpoints) piece by
    piece, on the same real fields under different names -- so the
    live rule and the tested rule can never silently drift apart.
    Caller is expected to have already confirmed valid_trade,
    entry_zone_reached, and has_real_trade_params are all True; this
    function only adds the three exclude checks on top of that.
    """
    # Mirrors filter_C_exact: A's own gate (confidence HIGH/MEDIUM)
    # plus a 6+ confluence score.
    passes_c = (overridden_confidence in ("HIGH", "MEDIUM")
                and confluence_score is not None and confluence_score >= 6)

    # Mirrors filter_confluence_only: ignores confidence entirely,
    # just a 7+ confluence score.
    passes_confluence_only = confluence_score is not None and confluence_score >= 7

    # Mirrors filter_stacked: raw (un-overridden) HIGH confidence,
    # confluence 7+, inside a killzone, and DXY not actively
    # conflicting with the trade direction.
    dxy_conflict = ((direction == "LONG" and dxy_implication == "BEARISH")
                     or (direction == "SHORT" and dxy_implication == "BULLISH"))
    passes_stacked = (raw_confidence == "HIGH"
                       and confluence_score is not None and confluence_score >= 7
                       and is_killzone and not dxy_conflict)

    return passes_c or passes_confluence_only or passes_stacked


def variant_b_included(raw_confidence, overridden_confidence, direction, zone):
    """
    B's new live entry gate (17 Aug) -- built from the same real,
    saved 15m/60d and 1h/2y batches used to validate A's own rebuild,
    replicated across both before shipping (0.17R / 0.13R avg R,
    n=80 / n=87). Mirrors filter_B_exact / filter_zone_strict piece
    by piece, on the same real fields under different names, so the
    live rule and the tested rule can never silently drift apart.
    Caller is expected to have already confirmed valid_trade,
    entry_zone_reached, and has_real_trade_params are all True.

    Include: passes B's own raw-confidence gate (no FVG/SWEEP
    override), OR passes the zone-strict gate (A's gate plus strict
    premium/discount alignment -- longs only in discount, shorts only
    in premium).
    """
    passes_b_exact = raw_confidence in ("HIGH", "MEDIUM")
    passes_zone_strict = (
        overridden_confidence in ("HIGH", "MEDIUM")
        and ((direction == "LONG" and zone == "DISCOUNT") or (direction == "SHORT" and zone == "PREMIUM"))
    )
    return passes_b_exact or passes_zone_strict


def variant_b_excluded(confluence_score, raw_confidence, is_killzone, direction, dxy_implication):
    """
    B's exclude/"emergency brake" (17 Aug), checked only on signals
    that already passed variant_b_included. Mirrors
    filter_confluence_only / filter_stacked -- the two filters that
    the replay comparison showed contributing nothing (or worse) on
    top of zone-strict, same reasoning as A's own exclude list.
    """
    passes_confluence_only = confluence_score is not None and confluence_score >= 7
    dxy_conflict = ((direction == "LONG" and dxy_implication == "BEARISH")
                     or (direction == "SHORT" and dxy_implication == "BULLISH"))
    passes_stacked = (raw_confidence == "HIGH"
                       and confluence_score is not None and confluence_score >= 7
                       and is_killzone and not dxy_conflict)
    return passes_confluence_only or passes_stacked


def variant_c_included(raw_confidence, overridden_confidence, direction, zone, alert_type):
    """
    C's new live entry gate (17 Aug) -- replaces the old hard 6/10
    confluence floor entirely. Built the same way as B's, off the
    same saved batches, but this specific combination (sweep+zone,
    excluding confluence+killzone) is the one that did NOT replicate
    between the two datasets during testing (0.29R on 15m/60d vs
    0.05R on 1h/2y) -- shipped anyway at Pete's explicit call, as a
    live continuation of that same test rather than a validated edge.
    Worth revisiting once C has real live data of its own. Mirrors
    filter_sweep_only_no_override / filter_zone_strict.
    """
    passes_sweep_only = raw_confidence in ("HIGH", "MEDIUM") and "SWEEP" in alert_type
    passes_zone_strict = (
        overridden_confidence in ("HIGH", "MEDIUM")
        and ((direction == "LONG" and zone == "DISCOUNT") or (direction == "SHORT" and zone == "PREMIUM"))
    )
    return passes_sweep_only or passes_zone_strict


def variant_c_excluded(confluence_score, is_killzone):
    """
    C's exclude/"emergency brake" (17 Aug), checked only on signals
    that already passed variant_c_included. Mirrors
    filter_confluence_only / filter_killzone_only. Note the killzone
    exclusion specifically is what drove most of this combo's failure
    to replicate on the 1h/2y batch (blocked 44 of 49 candidates on
    the 60-day window alone) -- a timing-based cut on a narrow sample,
    the classic shape of overfitting. Flagging again here since it's
    baked into C's live logic now, not just a backtest footnote.
    """
    passes_confluence_only = confluence_score is not None and confluence_score >= 7
    passes_killzone_only = is_killzone
    return passes_confluence_only or passes_killzone_only


def extract_confluence_score(analysis):
    """Pulls the numeric X/10 confluence score out of Claude's analysis
    text so it can be logged alongside the trade, instead of being
    thrown away after the Telegram message is sent."""
    match = re.search(r'CONFLUENCE SCORE[^\d]{0,20}(\d{1,2})\s*/\s*10', analysis, re.IGNORECASE)
    if match:
        score = int(match.group(1))
        if 0 <= score <= 10:
            return score
    return None

# ============================================================
# ENTRY ZONE EXTRACTION
# Pulls the low/high of Claude's stated ENTRY ZONE so the bot can
# check whether current price has actually reached it, instead of
# always assuming the live webhook price IS the entry — even when
# Claude is describing a retest at a level price hasn't reached (or
# has already moved well past), which is a completely different,
# not-yet-actionable trade.
# ============================================================
def extract_entry_zone(analysis):
    match = re.search(
        r'ENTRY ZONE\**\s*\n+\s*\**\s*([\d.]+)\s*[-–—]\s*([\d.]+)',
        analysis, re.IGNORECASE
    )
    if match:
        try:
            a = float(match.group(1))
            b = float(match.group(2))
            return (min(a, b), max(a, b))
        except ValueError:
            return None
    return None

# ============================================================
# CONFIDENCE EXTRACTION
# Reads the actual word (HIGH/MEDIUM/LOW) directly under the
# "CONFIDENCE LEVEL" header, instead of checking whether "HIGH" or
# "LOW" appear ANYWHERE in the whole analysis text. The old approach
# misfired constantly in SMC trading text specifically, since "high"
# and "low" are core price-structure vocabulary (Daily High, candle
# high, liquidity low) that show up regardless of the actual stated
# confidence.
# ============================================================
def extract_confidence(analysis):
    match = re.search(r'CONFIDENCE LEVEL\**\s*\n+\s*\**\s*(HIGH|MEDIUM|LOW)\b', analysis, re.IGNORECASE)
    if match:
        return match.group(1).upper()
    # If the header format is ever unparseable, default to LOW rather
    # than MEDIUM. LOW is genuinely the safe choice here — it's the
    # one value that does NOT pass the "would_log" gate. Defaulting
    # to MEDIUM (the old behaviour) would silently let a trade through
    # whenever we don't actually know what Claude said, which is
    # exactly the failure shape of the "No trade" bug just fixed.
    return "LOW"

# ============================================================
# PRE-TRADE RISK EXPOSURE CHECK
# Checks whether logging a new paper trade would push total open
# risk across all currently-open trades past the prop firm's daily
# loss limit, BEFORE logging it — rather than only catching it
# reactively after trades close (which is what daily_pnl/
# drawdown_protection already do via apply_trade_pnl).
# ============================================================
def get_open_risk_exposure(variant):
    account = PROP_FIRM_RULES["account_size"]
    risk_per_trade = account * (PROP_FIRM_RULES["max_loss_per_trade_pct"] / 100)
    open_count = sum(1 for t in active_trades[variant].values() if t.get('result') == 'OPEN')
    return open_count * risk_per_trade, open_count

def ensure_daily_reset():
    """
    Resets daily_pnl (for every variant) and daily_alert_count if the
    UTC day has rolled over since the last reset. Centralised so every
    caller — the scheduled midnight job, the pre-trade risk check,
    each incoming webhook, and load_state on restart — shares one
    source of truth for "is it a new day yet" instead of drifting out
    of sync. last_pnl_reset_day and daily_alert_count stay shared
    across variants deliberately — they're about incoming signals,
    which are identical for all three variants (one signal triggers
    all three at once), not about any one variant's own trading.
    Called from multiple places deliberately: if any one of them
    fails to run for some reason, the others still guarantee this
    can't silently get stuck the way the old single-path reset did.
    """
    global daily_pnl, last_pnl_reset_day, daily_alert_count
    today_str = datetime.now(timezone.utc).strftime('%Y-%m-%d')
    if last_pnl_reset_day != today_str:
        for v in VARIANTS:
            daily_pnl[v] = 0
        daily_alert_count = 0
        last_pnl_reset_day = today_str
        print(f"Daily counters reset for new UTC day: {today_str}")


def check_risk_cap_before_trade(variant):
    """Returns (allowed: bool, message: str) for a specific variant.
    Disallows opening a new paper trade if doing so — combined with
    the worst case of all that variant's currently open trades hitting
    stop loss — would exceed that variant's own account's daily loss
    limit. Entirely independent per variant: a bad day on one account
    can't block or be blocked by the other two.

    Checks and self-heals the daily reset on every single call,
    independent of the scheduled midnight job or a trade closing.
    Without this, a full day's losses freeze daily_pnl at its last
    value forever: if no new trade can open because daily_pnl is at
    the limit, no trade can ever close to reset it either — a
    permanent lockout with no way out. This one check is what
    actually guarantees that can't happen, regardless of whether
    the other two reset mechanisms (scheduled job, apply_trade_pnl)
    ran correctly.
    """
    global daily_pnl, last_pnl_reset_day
    ensure_daily_reset()

    if DAILY_LOSS_LIMIT_DISABLED:
        return True, ""

    account = PROP_FIRM_RULES["account_size"]
    risk_per_trade = account * (PROP_FIRM_RULES["max_loss_per_trade_pct"] / 100)
    daily_loss_limit = account * (PROP_FIRM_RULES["max_daily_loss_pct"] / 100)
    existing_risk, open_count = get_open_risk_exposure(variant)
    already_lost_today = abs(min(daily_pnl[variant], 0))
    projected_worst_case = already_lost_today + existing_risk + risk_per_trade
    if projected_worst_case > daily_loss_limit:
        return False, (f"⚠️ [{variant}] Trade NOT logged — opening it would risk a worst-case "
                        f"${projected_worst_case:,.2f} today (across {open_count} open "
                        f"trade(s) + today's losses already taken), beyond the "
                        f"{PROP_FIRM_RULES['max_daily_loss_pct']}% daily limit "
                        f"(${daily_loss_limit:,.2f}). Skipped to protect the account.")
    return True, ""

# ============================================================
# MONITOR ACTIVE TRADES
# ============================================================
def apply_trade_pnl(variant, trade, result, real_pnl_override=None):
    """
    Converts a closed paper trade's points result into account-level
    PnL for a specific variant's own account, using the trade's OWN
    stored risk percentage — normally the standard 0.5% (PROP_FIRM_
    RULES), but a reduced-risk drawdown trade stores half that at
    logging time. Using the trade's own stored value (rather than
    always reading the current global rate) matters because a trade
    can close well after it opened, potentially after drawdown status
    has changed — PnL must reflect what THIS trade was actually risked
    at, not whatever the rate happens to be now.

    real_pnl_override: when a trade was placed via the MT5 bridge and
    MT5 itself reports the real closed profit (real execution, real
    spread/swap included), pass that dollar figure here to use it
    directly instead of recomputing from points — strictly more
    accurate for that trade. Every existing caller (the Telegram-only
    monitoring path) omits this and keeps the original points-based
    behavior unchanged.

    Updates daily_pnl / total_pnl / current_balance / trading_days /
    consecutive_losses for THIS variant only so /prop-status and
    drawdown protection reflect real trade outcomes on that specific
    account — completely isolated from the other two variants.
    """
    global daily_pnl, total_pnl, current_balance, trading_days
    global consecutive_losses, last_trading_day, last_pnl_reset_day

    account = PROP_FIRM_RULES["account_size"]
    risk_pct = trade.get('risk_pct', PROP_FIRM_RULES["max_loss_per_trade_pct"])
    risk_amount = account * (risk_pct / 100)

    if real_pnl_override is not None:
        pnl = real_pnl_override
        if result == 'WIN':
            consecutive_losses[variant] = 0
        else:
            consecutive_losses[variant] += 1
    else:
        stop_distance = abs(trade['entry'] - trade['stop'])
        dollar_per_point = (risk_amount / stop_distance) if stop_distance > 0 else 0
        if result == 'WIN':
            points = abs(trade['target'] - trade['entry'])
            pnl = dollar_per_point * points
            consecutive_losses[variant] = 0
        else:
            pnl = -risk_amount
            consecutive_losses[variant] += 1

    # Store the actual outcome magnitude on the trade record itself —
    # not just result WIN/LOSS, but the real dollar pnl and R multiple
    # achieved. Without this, self-review and any future analysis can
    # see a trade won or lost, but never by how much — a 1.2R win and
    # a 4.5R win are indistinguishable in the stored data otherwise.
    trade['pnl'] = round(pnl, 2)
    trade['r_multiple'] = round(pnl / risk_amount, 2) if risk_amount > 0 else 0

    today_str = datetime.now(timezone.utc).strftime('%Y-%m-%d')
    ensure_daily_reset()
    if last_trading_day[variant] != today_str:
        trading_days[variant] += 1
        last_trading_day[variant] = today_str

    daily_pnl[variant] += pnl
    total_pnl[variant] += pnl
    current_balance[variant] += pnl

    check_drawdown_protection(variant)

    daily_loss_limit = account * (PROP_FIRM_RULES["max_daily_loss_pct"] / 100)
    total_drawdown_limit = account * (PROP_FIRM_RULES["max_total_drawdown_pct"] / 100)
    warnings = []
    if abs(min(daily_pnl[variant], 0)) >= daily_loss_limit:
        warnings.append(f"🚨 [{variant}] DAILY LOSS LIMIT HIT — STOP TRADING TODAY")
    elif abs(min(daily_pnl[variant], 0)) >= daily_loss_limit * 0.8:
        warnings.append(f"⚠️ [{variant}] DAILY LOSS WARNING — at {(abs(min(daily_pnl[variant], 0)) / account) * 100:.1f}% of limit")
    if abs(min(total_pnl[variant], 0)) >= total_drawdown_limit:
        warnings.append(f"🚨 [{variant}] TOTAL DRAWDOWN LIMIT HIT — ACCOUNT AT RISK")
    if consecutive_losses[variant] == 3:
        warnings.append(f"⚠️ [{variant}] DRAWDOWN PROTECTION ACTIVE — {consecutive_losses[variant]} consecutive losses, confidence threshold raised")
    if warnings:
        send_telegram("\n".join(warnings))

    return pnl

# ============================================================
# WICK-AWARE TRADE SCANNING
# The quick check in monitor_active_trades() only ever compares the
# latest candle's CLOSE against stop/target — it can completely miss
# a stop or target that was briefly touched (a "wick") and then
# recovered before the next 2-minute poll. A real resting stop-loss
# order on a broker fills the instant price touches it, wick or not.
# This scans every 5-minute candle's actual High/Low since the trade
# opened, so a stop that got touched and recovered is correctly
# caught as a loss, instead of the trade being left open to
# eventually — and wrongly — record a win later on.
# ============================================================
def scan_candles_for_hit(trade, gold_df):
    """
    Returns (hit_type, hit_price, hit_time) — hit_type is 'WIN' or
    'LOSS' — for the FIRST candle (chronologically) since the trade
    opened whose High/Low breaches its stop or target. Returns
    (None, None, None) if no breach is found in the available candle
    history (trade genuinely still open), or if the trade has no
    'opened_at' timestamp (older trade logged before this fix —
    skipped rather than guessed at).
    """
    opened_at = trade.get('opened_at')
    if not opened_at:
        return None, None, None
    try:
        open_ts = pd.Timestamp(opened_at)
    except Exception:
        return None, None, None

    idx = gold_df.index
    idx_tz = getattr(idx, 'tz', None)
    if idx_tz is not None:
        # yfinance intraday data is timezone-aware (often the
        # exchange's local timezone, not UTC) — align open_ts to it.
        if open_ts.tzinfo is None:
            open_ts = open_ts.tz_localize('UTC')
        open_ts = open_ts.tz_convert(idx_tz)
    else:
        if open_ts.tzinfo is not None:
            open_ts = open_ts.tz_convert('UTC').tz_localize(None)

    relevant = gold_df[gold_df.index >= open_ts]
    if relevant.empty:
        return None, None, None

    direction = trade['direction']
    stop = trade['stop']
    target = trade['target']

    for ts, row in relevant.iterrows():
        try:
            low = float(row['Low'])
            high = float(row['High'])
        except Exception:
            continue
        if direction == 'LONG':
            hit_target = high >= target
            hit_stop = low <= stop
        else:
            hit_target = low <= target
            hit_stop = high >= stop
        if hit_stop:
            # If a single candle's range spans BOTH levels, there's no
            # way to know from OHLC alone which was touched first —
            # assume the stop, since that's the safer assumption for
            # judging real trading readiness.
            return 'LOSS', stop, ts
        if hit_target:
            return 'WIN', target, ts
    return None, None, None


def thorough_scan_active_trades(variant, gold_df):
    """
    Runs after the normal quick check in /monitor-trades, for one
    specific variant's own account. Only looks at trades still OPEN
    after that check, and catches any that were actually hit via a
    wick the latest-close check missed.
    """
    trades_to_close = []
    for trade_id, trade in list(active_trades[variant].items()):
        if trade.get('result') != 'OPEN':
            continue
        if trade.get('mt5_ticket'):
            # Same real-ticket exclusion as monitor_active_trades() --
            # confirmed live (5 Aug) that this second, independent scan
            # closed the exact same still-genuinely-open real position
            # (ticket #512156384) via wick-detection, right after the
            # first fix stopped the live-price check from doing it.
            # Two separate closure paths both need this, not just one.
            continue
        hit_type, hit_price, hit_time = scan_candles_for_hit(trade, gold_df)
        if hit_type is None:
            continue
        entry = trade['entry']
        direction = trade['direction']
        points = abs(hit_price - entry)
        trade['result'] = hit_type
        pnl = apply_trade_pnl(variant, trade, hit_type)
        emoji = "✅" if hit_type == "WIN" else "❌"
        label = "TARGET HIT" if hit_type == "WIN" else "STOP HIT"
        level_label = "Target" if hit_type == "WIN" else "Stop"
        try:
            if getattr(hit_time, 'tzinfo', None) is not None:
                hit_time_str = hit_time.tz_convert('UTC').strftime('%H:%M UTC')
            else:
                hit_time_str = hit_time.strftime('%H:%M UTC')
        except Exception:
            hit_time_str = str(hit_time)
        sign = "+" if hit_type == "WIN" else "-"
        pnl_sign = "+" if pnl >= 0 else ""
        send_telegram(f"""
{emoji} *[{variant}] TRADE CLOSED — {label} (wick-detected)*
Alert: {trade['type']} | {trade['time']}
Direction: {direction}
Entry: {entry}
{level_label}: {hit_price} ← touched around {hit_time_str}
Result: {hit_type} {emoji} {sign}{points:.2f} points ({pnl_sign}${pnl:.2f}) | Balance: ${current_balance[variant]:,.2f}

ℹ️ Caught via candle high/low scan, not the live 2-minute price check — price touched this level and may have moved elsewhere since. A real resting stop/limit order would have filled here regardless.
""")
        trades_to_close.append(trade_id)
    for trade_id in trades_to_close:
        del active_trades[variant][trade_id]
    if trades_to_close:
        try:
            with open(data_path('paper_trades.json'), 'w') as f:
                json.dump(paper_trades, f, indent=2)
        except Exception as e:
            print(f"Paper trade update error: {e}")


def monitor_active_trades(variant, current_price):
    current_price = float(current_price)
    # A single 2-minute price reading isn't trusted enough on its own to
    # credit a WIN/LOSS anymore -- confirmed via two real cases (4 Aug)
    # where a bad reading got credited as a real close. A fixed
    # point-threshold turned out not to reliably tell a bad reading
    # apart from a real fast move (tried it, one of the two real cases
    # only overshot by 5pts despite the reading being clearly wrong).
    # Instead: require the SAME crossing to show up on two consecutive
    # polls before it's trusted. A genuinely bad, one-off reading won't
    # repeat; a real move will still be past the level 2 minutes later.
    trades_to_close = []
    for trade_id, trade in active_trades[variant].items():
        if trade['result'] != 'OPEN':
            continue
        if trade.get('mt5_ticket'):
            # A confirmed real MT5 order exists for this trade -- it
            # belongs exclusively to the real bridge's closure detection
            # now (get_trading_history_positions, real data). Confirmed
            # real problem, not theoretical: this simulated monitor
            # closed a still-genuinely-open real position (ticket
            # #512156384, 5 Aug) off a bad reading, not once but twice
            # in a row -- even undoing a manual correction within
            # seconds. It has no business touching a trade with a real
            # ticket at all.
            continue
        entry = trade['entry']
        stop = trade['stop']
        target = trade['target']
        direction = trade['direction']
        hit_tp = False
        hit_sl = False
        if direction == 'LONG':
            if current_price >= target:
                hit_tp = True
            elif current_price <= stop:
                hit_sl = True
        elif direction == 'SHORT':
            if current_price <= target:
                hit_tp = True
            elif current_price >= stop:
                hit_sl = True
        if hit_tp:
            if trade.get('_pending_close') == 'WIN':
                points = abs(target - entry)
                trade['result'] = 'WIN'
                pnl = apply_trade_pnl(variant, trade, 'WIN')
                # points/pnl correctly use `target`, not current_price --
                # this note only clarifies the DISPLAYED price, since a
                # 2-minute poll can catch price a little past the exact
                # level rather than landing on it precisely.
                gap_note = f"\n_Price check ran at {current_price} -- {abs(current_price - target):.2f}pts past target_" if abs(current_price - target) > (target * 0.001) else ""
                send_telegram(f"""
✅ *[{variant}] TRADE CLOSED — TARGET HIT*
Alert: {trade['type']} | {trade['time']}
Direction: {direction}
Entry: {entry}
Target: {target} ✅ reached
Result: WIN ✅ +{points:.2f} points (+${pnl:.2f}) | Balance: ${current_balance[variant]:,.2f}{gap_note}
""")
                trades_to_close.append(trade_id)
            else:
                trade['_pending_close'] = 'WIN'
                send_telegram(f"""
⏳ *[{variant}] Target level reached, confirming*
Alert: {trade['type']} | {trade['time']}
Direction: {direction}
Target: {target} -- price check showed {current_price}. Holding off crediting until the next poll confirms this wasn't a one-off bad reading.
""")
        elif hit_sl:
            if trade.get('_pending_close') == 'LOSS':
                points = abs(stop - entry)
                trade['result'] = 'LOSS'
                pnl = apply_trade_pnl(variant, trade, 'LOSS')
                gap_note = f"\n_Price check ran at {current_price} -- {abs(current_price - stop):.2f}pts past stop_" if abs(current_price - stop) > (stop * 0.001) else ""
                send_telegram(f"""
❌ *[{variant}] TRADE CLOSED — STOP HIT*
Alert: {trade['type']} | {trade['time']}
Direction: {direction}
Entry: {entry}
Stop: {stop} ❌ hit
Result: LOSS ❌ -{points:.2f} points (${pnl:.2f}) | Balance: ${current_balance[variant]:,.2f}{gap_note}
""")
                trades_to_close.append(trade_id)
            else:
                trade['_pending_close'] = 'LOSS'
                send_telegram(f"""
⏳ *[{variant}] Stop level reached, confirming*
Alert: {trade['type']} | {trade['time']}
Direction: {direction}
Stop: {stop} -- price check showed {current_price}. Holding off crediting until the next poll confirms this wasn't a one-off bad reading.
""")
        else:
            # Neither level hit this cycle -- if a prior poll had flagged
            # a pending close, that reading didn't hold up. Clear it
            # rather than let a stale flag silently linger.
            trade.pop('_pending_close', None)
    for trade_id in trades_to_close:
        del active_trades[variant][trade_id]
    try:
        with open(data_path('paper_trades.json'), 'w') as f:
            json.dump(paper_trades, f, indent=2)
    except Exception as e:
        print(f"Paper trade update error: {e}")

# ============================================================
# LEARNED RULES
# ============================================================
def get_learned_rules():
    """
    Feeds into the single shared analysis prompt (analyse_with_claude),
    so -- same reasoning as drawdown_active_a below -- reads variant
    A's own approved rules as the representative value, since there's
    only one shared Claude call per alert, not one per variant.

    Previously read a bare 'learned_rules.txt', which nothing else in
    this file ever writes to -- /approve-rules, /reset-learned-rules,
    and /view-rules all correctly use the per-variant
    learned_rules_{variant}.txt naming, but this function was missed
    during the A/B/C migration (9 Aug) and kept reading the old,
    single-account filename. Practical effect: every approval made
    through /approve-rules since 9 Aug has been silently inert --
    this always hit the except below and returned "No learned rules
    yet", regardless of what had actually been approved. Fixed 16 Aug.
    """
    try:
        with open(data_path('learned_rules_A.txt'), 'r') as f:
            return f.read()
    except FileNotFoundError:
        return "No learned rules yet — system will develop rules after first self-review."

# ============================================================
# POINT-IN-TIME HISTORICAL CONTEXT (for the sampled live-judgment
# replay). Every function here is explicitly parametrized by a
# historical timestamp/dataset — none of them touch datetime.now()
# or any live global state (KEY_LEVELS, learned_rules.txt, etc).
# That's deliberate: the live equivalents of these functions read
# "right now", which would leak future information into a historical
# analysis and make the replay's results meaningless.
# ============================================================
def get_session_at(hour):
    if 22 <= hour or hour < 7:
        return "Asian Session", "low liquidity — be cautious", False
    elif 7 <= hour < 9:
        return "London Open Killzone", "HIGH PROBABILITY WINDOW — institutional orders firing", True
    elif 9 <= hour < 12:
        return "London Session", "good activity — valid setups", True
    elif 12 <= hour < 14:
        return "New York Open Killzone", "HIGH PROBABILITY WINDOW — institutional orders firing", True
    elif 14 <= hour < 17:
        return "New York Session", "high volatility — valid setups", True
    elif 17 <= hour < 20:
        return "London Close", "watch for reversals and stop hunts", False
    else:
        return "Dead Zone", "NY close — avoid new trades", False


def get_news_risk_at(hour, minute, weekday):
    high_risk_times = [(13, 30), (15, 0), (12, 0)]
    for risk_hour, risk_minute in high_risk_times:
        time_diff = abs((hour * 60 + minute) - (risk_hour * 60 + risk_minute))
        if time_diff <= 30:
            return True, f"High impact news window — within 30 mins of {risk_hour}:{risk_minute:02d} UTC"
    if weekday == 4 and 13 <= hour <= 14:
        return True, "NFP Friday risk window — avoid new trades"
    return False, "No major news risk detected"


def get_hour_quality_at(hour):
    best_hours = [21, 22, 23]
    worst_hours = [3, 6, 14]
    if hour in best_hours:
        return "OPTIMAL", f"Hour {hour}:00 UTC historically shows 55-56% win rate — weight signals higher"
    elif hour in worst_hours:
        return "POOR", f"Hour {hour}:00 UTC historically shows 44-45% win rate — reduce confidence"
    else:
        return "NORMAL", f"Hour {hour}:00 UTC — standard win rate expected"


def get_dxy_bias_at(dxy_df, timestamp):
    """Same logic as get_dxy_bias(), but using only DXY data at or
    before `timestamp` — never data from after it."""
    try:
        visible = dxy_df[dxy_df.index <= timestamp]
        if len(visible) < 5:
            return "UNKNOWN", "DXY insufficient historical data", "NEUTRAL"
        closes = visible['Close'].values
        current = float(closes[-1])
        previous = float(closes[-5])
        change_pct = ((current - previous) / previous) * 100
        if change_pct > 0.15:
            return "BULLISH", f"DXY rising +{change_pct:.2f}% — BEARISH for gold", "BEARISH"
        elif change_pct < -0.15:
            return "BEARISH", f"DXY falling {change_pct:.2f}% — BULLISH for gold", "BULLISH"
        else:
            return "NEUTRAL", f"DXY flat ({change_pct:.2f}%) — no strong gold bias", "NEUTRAL"
    except Exception as e:
        return "UNKNOWN", f"DXY historical check failed: {str(e)}", "NEUTRAL"


def get_premium_discount_at(gold_df, signal_index, price, lookback_candles=240):
    """Same concept as get_premium_discount(), but the dealing range
    is a trailing window ending at the signal itself (roughly 10 days
    of hourly candles), never the live global KEY_LEVELS and never
    including any candle after the signal."""
    try:
        start = max(0, signal_index - lookback_candles)
        window = gold_df.iloc[start:signal_index + 1]
        high = float(window['High'].max())
        low = float(window['Low'].min())
        price = float(price)
        if price > high:
            high = price
        if price < low:
            low = price
        midpoint = (high + low) / 2
        percentage = ((price - low) / (high - low)) * 100 if high != low else 50.0
        zone = "PREMIUM" if price > midpoint else "DISCOUNT"
        advice = "price is expensive — favour shorts, be cautious on longs" if zone == "PREMIUM" else "price is cheap — favour longs, be cautious on shorts"
        return zone, round(percentage, 1), advice, high, low
    except Exception:
        return "UNKNOWN", 0, "unable to calculate", price, price


def get_key_levels_at(gold_df, signal_index, lookback_candles=240, daily_candles=24):
    """Builds a KEY_LEVELS-style dict from a trailing historical
    window only, to feed the historical prompt instead of reading
    the live global KEY_LEVELS (which reflects today, not the
    signal's actual point in time). daily_candles defaults to 24 --
    correct for 1h candles (24 = one real day) but needs scaling for
    any other interval, same reasoning as lookback_candles."""
    start = max(0, signal_index - lookback_candles)
    window = gold_df.iloc[start:signal_index + 1]
    daily_window = gold_df.iloc[max(0, signal_index - daily_candles):signal_index + 1]
    return {
        "weekly_high": round(float(window['High'].max()), 2),
        "weekly_low": round(float(window['Low'].min()), 2),
        "major_resistance": round(float(window['High'].max()), 2),
        "major_support": round(float(window['Low'].min()), 2),
        "daily_high": round(float(daily_window['High'].max()), 2),
        "daily_low": round(float(daily_window['Low'].min()), 2),
    }


def build_historical_prompt(alert_data, recent_context, session_name, session_desc, is_killzone,
                             zone, zone_pct, zone_advice, news_risk, news_msg, historical_key_levels,
                             timestamp_str, dxy_direction="UNKNOWN", dxy_desc="DXY data unavailable"):
    """
    Same structure and headers as analyse_with_claude()'s live prompt,
    but built entirely from explicit historical values — no reference
    to datetime.now(), live KEY_LEVELS, or get_learned_rules() (rules
    learned from later performance would contaminate an earlier
    historical judgment).
    """
    killzone_text = "✅ YES — weight this signal higher" if is_killzone else "❌ NO — standard session, normal weighting"
    levels_text = "\n".join([f"- {k.replace('_', ' ').title()}: {v}" for k, v in historical_key_levels.items()])
    return f"""
You are an expert XAUUSD (Gold) trader with 20 years experience in Smart Money Concepts (SMC).
A live market alert has fired. Analyse it thoroughly and give a clear trading assessment.

## LIVE ALERT
- Alert Type: {alert_data.get('type', 'Unknown')}
- Current Price: {alert_data.get('price', 'Unknown')}
- Candle High: {alert_data.get('high', 'Unknown')}
- Candle Low: {alert_data.get('low', 'Unknown')}
- Timeframe: {alert_data.get('timeframe', '15m')}
- Time: {timestamp_str}

## SESSION CONTEXT
- Session: {session_name}
- Conditions: {session_desc}
- Inside Killzone: {killzone_text}

## PREMIUM / DISCOUNT
- Zone: {zone} ({zone_pct}% of dealing range)
- Implication: {zone_advice}

## KEY LEVELS THIS WEEK
{levels_text}

## NEWS RISK
- {news_msg}

## DXY CORRELATION
- {dxy_desc}
- Implication: {"DXY confirms bearish gold bias" if dxy_direction == "BULLISH" else "DXY confirms bullish gold bias" if dxy_direction == "BEARISH" else "No directional confluence from DXY"}

## RECENT ALERT HISTORY
{recent_context if recent_context else "No prior alerts this session"}

## DRAWDOWN STATUS
Normal mode — standard confidence thresholds apply

## LEARNED RULES FROM PAST PERFORMANCE
No learned rules available for this historical point in time.

## YOUR ANALYSIS — use exactly these headers:

**SETUP VALIDITY**
Is this a genuine SMC setup or noise? 2-3 sentences max.

**CONFLUENCE SCORE**
Rate out of 10:
- Killzone alignment (2 pts)
- Premium/Discount alignment (2 pts)
- Key level proximity (2 pts)
- Timeframe alignment (2 pts)
- Clean structure (2 pts)

**TRADE DIRECTION**
Long or Short? One sentence reason.

**ENTRY ZONE**
One line — specific price zone only.

**STOP LOSS**
One line — specific level only.

**TARGET**
One line — primary target only.

**RISK:REWARD**
One line — Entry / SL / TP / RR ratio.

**CONFIDENCE LEVEL**
One line — LOW / MEDIUM / HIGH and single reason.

**AVOID IF**
One line — single most important reason only.

Total response must be under 200 words. Every section one line maximum.
"""


def derive_trade_decision(analysis, alert_type, entry_price, apply_override=True):
    """
    Exact copy of the live decision logic from process_webhook_alert
    (SL/TP extraction, direction-from-SL/TP, valid_trade check,
    entry-zone-actionability check) — deliberately duplicated rather
    than refactored out of the live webhook path, to avoid touching
    live-critical code unnecessarily. If the live logic changes later,
    this copy needs updating to match.

    apply_override: True (default, existing behavior unchanged for the
    backtest-replay caller) applies the FVG/SWEEP confidence-override
    rules. False skips them, returning Claude's raw confidence as-is —
    this is what variant B (the A/B/C test's override-removed variant)
    needs for its own shadow-tracking to correctly reflect its own
    judgment, not variant A/C's.
    """
    direction = "SHORT" if "BEARISH" in alert_type else "LONG"
    stop_price = entry_price * 1.005 if direction == "SHORT" else entry_price * 0.995
    target_price = entry_price * 0.99 if direction == "SHORT" else entry_price * 1.01

    sl_found = False
    sl_patterns = [r'Stop(?:\s+Loss)?[:\s]+(\d+\.?\d*)', r'SL[:\s]+(\d+\.?\d*)']
    for pattern in sl_patterns:
        match = re.search(pattern, analysis, re.IGNORECASE)
        if match:
            extracted = float(match.group(1))
            if 3000 < extracted < 5500:
                stop_price = extracted
                sl_found = True
                break

    tp_found = False
    tp_patterns = [r'Target(?:\s+1)?[:\s]+(\d+\.?\d*)', r'TP[:\s]+(\d+\.?\d*)']
    for pattern in tp_patterns:
        match = re.search(pattern, analysis, re.IGNORECASE)
        if match:
            extracted = float(match.group(1))
            if 3000 < extracted < 5500:
                target_price = extracted
                tp_found = True
                break

    if target_price > stop_price:
        direction = "LONG"
    elif target_price < stop_price:
        direction = "SHORT"
    else:
        direction = "LONG"

    confidence = extract_confidence(analysis)
    if apply_override:
        if "FVG" in alert_type and confidence == "LOW":
            confidence = "MEDIUM"
        if "BEARISH_SWEEP" in alert_type and confidence == "HIGH":
            confidence = "MEDIUM"

    valid_trade = False
    if direction == "LONG" and target_price > entry_price > stop_price:
        valid_trade = True
    elif direction == "SHORT" and target_price < entry_price < stop_price:
        valid_trade = True

    entry_zone = extract_entry_zone(analysis)
    entry_zone_reached = True
    if entry_zone:
        zone_low, zone_high = entry_zone
        buffer = entry_price * 0.003
        if not (zone_low - buffer <= entry_price <= zone_high + buffer):
            entry_zone_reached = False

    # If Claude didn't give a real, extractable stop AND target (e.g. it
    # explicitly wrote "No trade" / N/A), the fallback percentages above
    # were never Claude's recommendation — they're arbitrary defaults.
    # Without this check, an explicit rejection could still get logged
    # as a fabricated trade using those defaults.
    has_real_trade_params = sl_found and tp_found

    return {
        "confidence": confidence,
        "direction": direction,
        "stop_price": stop_price,
        "target_price": target_price,
        "valid_trade": valid_trade,
        "entry_zone_reached": entry_zone_reached,
        "has_real_trade_params": has_real_trade_params,
        "would_log": confidence in ["HIGH", "MEDIUM"] and valid_trade and entry_zone_reached and has_real_trade_params,
    }


def detect_raw_signals(gold_df):
    """
    Same pattern-detection as detect_and_simulate_signals(), but
    returns only the detected signal locations (index, type,
    direction, price, high, low) without running the mechanical
    entry/stop/target simulation — the replay uses Claude's own
    stated entry/stop/target instead of the fixed 1:2 assumption.
    """
    detected_signals = []
    for i in range(3, len(gold_df) - 10):
        candle = gold_df.iloc[i]
        prev2 = gold_df.iloc[i-2]
        high = float(candle['High'])
        low = float(candle['Low'])
        close = float(candle['Close'])
        if float(prev2['Low']) > high:
            detected_signals.append({"index": i, "type": "BEARISH_FVG", "direction": "SHORT", "price": close, "high": high, "low": low})
        if float(prev2['High']) < low:
            detected_signals.append({"index": i, "type": "BULLISH_FVG", "direction": "LONG", "price": close, "high": high, "low": low})
        lookback_high = float(gold_df.iloc[i-10:i]['High'].max())
        if high > lookback_high and close < lookback_high:
            detected_signals.append({"index": i, "type": "BEARISH_SWEEP", "direction": "SHORT", "price": close, "high": high, "low": low})
        lookback_low = float(gold_df.iloc[i-10:i]['Low'].min())
        if low < lookback_low and close > lookback_low:
            detected_signals.append({"index": i, "type": "BULLISH_SWEEP", "direction": "LONG", "price": close, "high": high, "low": low})
    return detected_signals


def stratified_sample_signals(gold_df, per_type=50, seed=42, exclude_indices=None):
    """
    Detects every signal across the full dataset, then samples
    `per_type` of each signal type, evenly spaced across the whole
    time range (not clustered at the start, end, or wherever signals
    happen to be densest) — so the sample represents the full 2
    years, not just one period of it.

    exclude_indices (14 Aug): optional set of signal indices to skip
    entirely before sampling -- lets run_replay_generate top up an
    existing saved batch with genuinely new signals across multiple
    sessions/days, never wasting real API cost re-analyzing one
    that's already in it. Defaults to None (nothing excluded), so
    every existing caller of this function is unaffected.
    """
    all_signals = detect_raw_signals(gold_df)
    if exclude_indices:
        all_signals = [s for s in all_signals if s["index"] not in exclude_indices]
    by_type = {}
    for s in all_signals:
        by_type.setdefault(s["type"], []).append(s)

    sampled = []
    for sig_type, sigs in by_type.items():
        sigs_sorted = sorted(sigs, key=lambda s: s["index"])
        n = len(sigs_sorted)
        if n <= per_type:
            sampled.extend(sigs_sorted)
        else:
            positions = np.linspace(0, n - 1, per_type)
            picked_indices = sorted(set(int(round(p)) for p in positions))
            sampled.extend([sigs_sorted[i] for i in picked_indices])
    sampled.sort(key=lambda s: s["index"])
    return sampled

# ============================================================
# MAIN CLAUDE ANALYSIS
# ============================================================
def analyse_with_claude(alert_data, recent_context, session_name, session_desc, is_killzone, zone, zone_pct, zone_advice, news_risk, news_msg, drawdown_active, dxy_direction="UNKNOWN", dxy_desc="DXY data unavailable"):
    killzone_text = "✅ YES — weight this signal higher" if is_killzone else "❌ NO — standard session, normal weighting"
    levels_text = "\n".join([f"- {k.replace('_', ' ').title()}: {v}" for k, v in KEY_LEVELS.items()])

    prompt = f"""
You are an expert XAUUSD (Gold) trader with 20 years experience in Smart Money Concepts (SMC).
A live market alert has fired. Analyse it thoroughly and give a clear trading assessment.

## LIVE ALERT
- Alert Type: {alert_data.get('type', 'Unknown')}
- Current Price: {alert_data.get('price', 'Unknown')}
- Candle High: {alert_data.get('high', 'Unknown')}
- Candle Low: {alert_data.get('low', 'Unknown')}
- Timeframe: {alert_data.get('timeframe', '15m')}
- Time: {datetime.utcnow().strftime('%H:%M UTC')}

## SESSION CONTEXT
- Session: {session_name}
- Conditions: {session_desc}
- Inside Killzone: {killzone_text}

## PREMIUM / DISCOUNT
- Zone: {zone} ({zone_pct}% of dealing range)
- Implication: {zone_advice}

## KEY LEVELS THIS WEEK
{levels_text}

## NEWS RISK
- {news_msg}

## DXY CORRELATION
- {dxy_desc}
- Implication: {"DXY confirms bearish gold bias" if dxy_direction == "BULLISH" else "DXY confirms bullish gold bias" if dxy_direction == "BEARISH" else "No directional confluence from DXY"}

## RECENT ALERT HISTORY
{recent_context if recent_context else "No prior alerts this session"}

## DRAWDOWN STATUS
{"⚠️ DRAWDOWN PROTECTION ACTIVE — HIGH confidence trades size normally; MEDIUM confidence trades are still taken but automatically sized at half risk; LOW confidence is skipped entirely" if drawdown_active else "Normal mode — standard confidence thresholds apply"}

## LEARNED RULES FROM PAST PERFORMANCE
{get_learned_rules()}

## YOUR ANALYSIS — use exactly these headers:

**SETUP VALIDITY**
Is this a genuine SMC setup or noise? 2-3 sentences max.

**CONFLUENCE SCORE**
Rate out of 10:
- Killzone alignment (2 pts)
- Premium/Discount alignment (2 pts)
- Key level proximity (2 pts)
- Timeframe alignment (2 pts)
- Clean structure (2 pts)

**TRADE DIRECTION**
Long or Short? One sentence reason.

**ENTRY ZONE**
One line — specific price zone only.

**STOP LOSS**
One line — specific level only.

**TARGET**
One line — primary target only.

**RISK:REWARD**
One line — Entry / SL / TP / RR ratio.

**CONFIDENCE LEVEL**
One line — LOW / MEDIUM / HIGH and single reason.

**AVOID IF**
One line — single most important reason only.

Total response must be under 200 words. Every section one line maximum.
"""

    try:
        message = call_claude(
            messages=[{"role": "user", "content": prompt}],
            max_tokens=16000,
            thinking={"type": "enabled", "budget_tokens": 10000}
        )
        for block in message.content:
            if block.type == "text":
                return block.text
        return "No analysis returned"
    except Exception as e:
        return f"Claude analysis error: {str(e)}"

# ============================================================
# WEBHOOK — responds instantly, processes in background thread
# ============================================================
@app.route('/webhook', methods=['POST'])
def webhook():
    try:
        data = request.get_json(silent=True)
        if data is None:
            return jsonify({"status": "error", "message": "request body must be valid JSON with Content-Type: application/json"}), 400
        print(f"Alert received: {data}")
        alert_type = data.get('type', '')

        if alert_type == "BULLISH_SWEEP":
            log_to_csv(alert_type, data.get('price'), "FILTERED", "BULLISH_SWEEP filtered — 39% historical win rate")
            return jsonify({"status": "filtered", "reason": "BULLISH_SWEEP has 39% win rate over 2 years"})

        thread = threading.Thread(target=process_webhook_alert, args=(data,))
        thread.start()

        return jsonify({"status": "received", "processing": "background"})

    except Exception as e:
        print(f"Webhook receive error: {e}")
        return jsonify({"status": "error", "message": str(e)}), 500


def process_webhook_alert(data):
    global recent_alerts, daily_alert_count
    try:
        ensure_daily_reset()
        daily_alert_count += 1

        alert_type = data.get('type', '')

        session_name, session_desc, is_killzone = get_session()
        zone, zone_pct, zone_advice = get_premium_discount(data.get('price', 0))
        news_risk, news_msg = check_news_risk()
        # Variant A's drawdown status specifically feeds the shared
        # analysis prompt -- Claude needs SOME single representative
        # value to reason about, and the underlying signal/analysis
        # itself is genuinely shared across all three variants. Each
        # variant's OWN drawdown status still independently governs
        # its own sizing/filtering decision later in this function.
        drawdown_active_a, drawdown_msg = check_drawdown_protection("A")
        dxy_direction, dxy_desc, dxy_implication = get_dxy_bias()
        hour_quality, hour_msg = check_hour_quality()
        spread_risk, spread_msg = check_spread(
            data.get('high', 0),
            data.get('low', 0),
            data.get('price', 0)
        )

        recent_alerts.append({
            "type": alert_type,
            "price": data.get('price', 'Unknown'),
            "timeframe": data.get('timeframe', '15m'),
            "time": datetime.utcnow().strftime('%H:%M UTC')
        })
        if len(recent_alerts) > 10:
            recent_alerts.pop(0)

        # Annotate each historical alert with how far price has moved
        # since it fired, so Claude has an explicit signal for how
        # stale a reference level is, instead of citing an old FVG
        # from hours ago and 70+ points away as if it were still live.
        current_price_val = None
        try:
            current_price_val = float(data.get('price', 0))
        except (TypeError, ValueError):
            pass
        context_lines = []
        for a in recent_alerts[:-1]:
            moved_str = ""
            if current_price_val is not None:
                try:
                    a_price = float(a['price'])
                    moved = current_price_val - a_price
                    direction_word = "up" if moved > 0 else "down" if moved < 0 else "flat"
                    moved_str = f" — price has since moved {abs(moved):.1f}pts {direction_word}"
                except (TypeError, ValueError):
                    pass
            context_lines.append(f"- {a['time']}: {a['type']} at {a['price']} ({a['timeframe']}){moved_str}")
        context = "\n".join(context_lines)

        # ============================================================
        # SHARED, ONCE PER SIGNAL: one Claude analysis, one Telegram
        # alert -- identical to before A/B/C existed. Everything below
        # this point is where the three variants' judgment diverges.
        # ============================================================
        analysis = analyse_with_claude(
            data, context, session_name, session_desc,
            is_killzone, zone, zone_pct, zone_advice,
            news_risk, news_msg, drawdown_active_a,
            dxy_direction, dxy_desc
        )

        raw_confidence = extract_confidence(analysis)
        overridden_confidence = raw_confidence
        if "FVG" in alert_type and overridden_confidence == "LOW":
            overridden_confidence = "MEDIUM"
        if "BEARISH_SWEEP" in alert_type and overridden_confidence == "HIGH":
            overridden_confidence = "MEDIUM"

        entry_price = float(data.get('price', 0))
        direction = "SHORT" if "BEARISH" in alert_type else "LONG"
        stop_price = entry_price * 1.005 if direction == "SHORT" else entry_price * 0.995
        target_price = entry_price * 0.99 if direction == "SHORT" else entry_price * 1.01

        sl_found = False
        sl_patterns = [r'Stop(?:\s+Loss)?[:\s]+(\d+\.?\d*)', r'SL[:\s]+(\d+\.?\d*)']
        for pattern in sl_patterns:
            match = re.search(pattern, analysis, re.IGNORECASE)
            if match:
                extracted = float(match.group(1))
                if 3000 < extracted < 5500:
                    stop_price = extracted
                    sl_found = True
                    break

        tp_found = False
        tp_patterns = [r'Target(?:\s+1)?[:\s]+(\d+\.?\d*)', r'TP[:\s]+(\d+\.?\d*)']
        for pattern in tp_patterns:
            match = re.search(pattern, analysis, re.IGNORECASE)
            if match:
                extracted = float(match.group(1))
                if 3000 < extracted < 5500:
                    target_price = extracted
                    tp_found = True
                    break

        if target_price > stop_price:
            direction = "LONG"
        elif target_price < stop_price:
            direction = "SHORT"
        else:
            direction = "LONG"

        dxy_confluence_msg, dxy_score = get_dxy_confluence(direction, dxy_implication)
        emoji = "🔴" if direction == "SHORT" else "🟢" if direction == "LONG" else "🟡"
        killzone_badge = "🎯 KILLZONE" if is_killzone else ""

        telegram_message = f"""
{emoji} *XAUUSD — {alert_type}* {killzone_badge}
📍 Price: {data.get('price', 'N/A')}
📊 Zone: {zone} ({zone_pct}%)
⏰ {datetime.utcnow().strftime('%H:%M UTC')} | {session_name}
⚠️ News: {news_msg}
💵 DXY: {dxy_confluence_msg}
📊 Spread: {spread_msg}
🕐 Hour Quality: {hour_msg}

{analysis}

_Timeframe: {data.get('timeframe', '15m')} | Log this trade in your journal_
"""

        send_telegram(telegram_message)
        log_to_csv(alert_type, data.get('price'), overridden_confidence, analysis)

        valid_trade = False
        if direction == "LONG" and target_price > entry_price > stop_price:
            valid_trade = True
        elif direction == "SHORT" and target_price < entry_price < stop_price:
            valid_trade = True

        confluence_score = extract_confluence_score(analysis)

        # Only treat this as a filled trade if current price has actually
        # reached the entry zone Claude described. A small buffer (0.3%
        # of price) allows for the normal few-points overshoot seen on
        # genuinely-triggered setups, without allowing a "wait for a
        # retest" idea 20+ points away to be silently logged as if it
        # filled at the current market price.
        entry_zone = extract_entry_zone(analysis)
        entry_zone_reached = True
        if entry_zone:
            zone_low, zone_high = entry_zone
            buffer = entry_price * 0.003
            if not (zone_low - buffer <= entry_price <= zone_high + buffer):
                entry_zone_reached = False

        # ============================================================
        # PER VARIANT: same shared analysis above, three independent
        # judgment calls on whether to act on it. Each wrapped in its
        # own try/except so one variant's failure can't block the
        # other two from processing the same signal.
        # ============================================================
        for variant in VARIANTS:
            try:
                # ============================================================
                # VARIANT A (16 Aug) -- new live logic, replacing the old
                # confidence-gated approach entirely. Directly applies the
                # single best-evidenced result from the full replay
                # exploration (14-16 Aug, real 200-signal historical
                # batch): no confidence/confluence requirement at all --
                # just a real, valid trade whose entry zone has genuinely
                # been reached -- EXCEPT signals that independently match
                # C/confluence-only/stacked's own gates, which get
                # excluded even though they'd otherwise qualify. Target
                # scaled to 80% of the original entry-to-target distance;
                # stop deliberately, completely untouched.
                #
                # Historical trades logged under A with BOT_VERSION < 1.1.0
                # used the old confidence-gated approach; B and C's own
                # pre-17-Aug logic is similarly only preserved in trades
                # with BOT_VERSION < 1.2.0 (see the B/C blocks further
                # below, rebuilt 17 Aug the same way A was).
                # ============================================================
                if variant == "A":
                    has_real_trade_params = sl_found and tp_found

                    # Shadow tracking: what happens to the signals A
                    # specifically excludes, so this keeps getting
                    # validated on fresh, live data, not just the
                    # historical replay it was built from.
                    try:
                        if valid_trade and entry_zone_reached and has_real_trade_params:
                            if variant_a_excluded(overridden_confidence, raw_confidence, confluence_score, is_killzone, direction, dxy_implication):
                                shadow_context = {
                                    "session": session_name, "killzone": is_killzone, "zone": zone,
                                    "zone_pct": zone_pct, "dxy_direction": dxy_direction,
                                    "dxy_implication": dxy_implication, "news_risk": news_risk,
                                    "spread_risk": spread_risk, "hour_quality": hour_quality,
                                    "confluence_score": confluence_score,
                                }
                                log_shadow_trade(variant, alert_type, data.get('price'), direction, entry_price,
                                                  stop_price, target_price, overridden_confidence,
                                                  "EXCLUDED_BY_A_RULE", context=shadow_context)
                    except Exception as e:
                        print(f"[{variant}] Shadow tracking error (non-fatal, real trade path unaffected): {e}")

                    if valid_trade and entry_zone_reached and has_real_trade_params:
                        if variant_a_excluded(overridden_confidence, raw_confidence, confluence_score, is_killzone, direction, dxy_implication):
                            send_telegram(f"⚠️ *[{variant}] Signal excluded* — matches a known-weaker pattern (C-style, high-confluence-only, or the maximally-selective stacked criteria), skipped even though it reached its entry zone.\nAlert type: {alert_type} at {data.get('price')}")
                            monitor_active_trades(variant, data.get('price', 0))
                            continue
                        risk_ok, risk_msg = check_risk_cap_before_trade(variant)
                        if risk_ok:
                            alert_time = datetime.utcnow().strftime('%H:%M UTC')
                            # 80% target scaling -- stop deliberately
                            # unchanged. The single most consistent,
                            # best-evidenced result across every fraction
                            # tested (50-100%) against the real, saved
                            # historical batch, confirmed sharpest and
                            # most consistent on the two largest samples.
                            scaled_target_price = round(entry_price + (target_price - entry_price) * 0.8, 2)
                            trade_context = {
                                "session": session_name, "killzone": is_killzone, "zone": zone,
                                "zone_pct": zone_pct, "dxy_direction": dxy_direction,
                                "dxy_implication": dxy_implication, "news_risk": news_risk,
                                "spread_risk": spread_risk, "hour_quality": hour_quality,
                                "confluence_score": confluence_score,
                                "risk_pct": PROP_FIRM_RULES["max_loss_per_trade_pct"],
                                "original_target": target_price,
                                "target_scaled_to_pct": 80,
                            }
                            if entry_zone:
                                trade_context["entry_zone_low"] = entry_zone[0]
                                trade_context["entry_zone_high"] = entry_zone[1]
                            log_paper_trade(variant, alert_type, data.get('price'), direction, entry_price, stop_price,
                                             scaled_target_price, overridden_confidence, alert_time, context=trade_context)
                        else:
                            print(f"[{variant}] {risk_msg}")
                            send_telegram(risk_msg)
                    elif valid_trade and entry_zone_reached and not has_real_trade_params:
                        print(f"[{variant}] Skipped logging paper trade — Claude did not provide a real extractable stop/target (likely an explicit 'No trade' response). Alert:{alert_type}")
                    elif valid_trade and not entry_zone_reached:
                        msg = (f"⏳ *[{variant}] Setup noted — not logged as a trade*\n"
                               f"Current price (${entry_price:,.2f}) hasn't reached the proposed "
                               f"entry zone (${entry_zone[0]:,.2f}–${entry_zone[1]:,.2f}) yet. "
                               f"This is a level to watch, not a live trade.")
                        print(msg)
                        send_telegram(msg)
                    elif not valid_trade:
                        print(f"[{variant}] Skipped logging paper trade — SL/TP inconsistent. Dir:{direction} Entry:{entry_price} SL:{stop_price} TP:{target_price}")

                    monitor_active_trades(variant, data.get('price', 0))
                    continue

                # Old A (pre-16-Aug confidence-override logic) lives on
                # only in historical trades with BOT_VERSION < 1.1.0.
                # B and C's own pre-17-Aug logic is similarly preserved
                # only in their own historical trades (BOT_VERSION <
                # 1.2.0) -- both now replaced below, same rebuild
                # philosophy as A: entry gate + exclude list, built and
                # cross-checked against the same real, saved 15m/60d and
                # 1h/2y batches before shipping.
                # ============================================================
                if variant == "B":
                    has_real_trade_params = sl_found and tp_found

                    # Shadow tracking: what happens to the signals B
                    # specifically excludes, same reasoning as A -- keeps
                    # getting validated on fresh, live data.
                    try:
                        if valid_trade and entry_zone_reached and has_real_trade_params:
                            if variant_b_included(raw_confidence, overridden_confidence, direction, zone):
                                if variant_b_excluded(confluence_score, raw_confidence, is_killzone, direction, dxy_implication):
                                    shadow_context = {
                                        "session": session_name, "killzone": is_killzone, "zone": zone,
                                        "zone_pct": zone_pct, "dxy_direction": dxy_direction,
                                        "dxy_implication": dxy_implication, "news_risk": news_risk,
                                        "spread_risk": spread_risk, "hour_quality": hour_quality,
                                        "confluence_score": confluence_score,
                                    }
                                    log_shadow_trade(variant, alert_type, data.get('price'), direction, entry_price,
                                                      stop_price, target_price, overridden_confidence,
                                                      "EXCLUDED_BY_B_RULE", context=shadow_context)
                    except Exception as e:
                        print(f"[{variant}] Shadow tracking error (non-fatal, real trade path unaffected): {e}")

                    if news_risk and overridden_confidence != "HIGH":
                        send_telegram(f"⚠️ *[{variant}] Alert suppressed — news risk active*\n{news_msg}\nAlert type: {alert_type} at {data.get('price')}")
                        monitor_active_trades(variant, data.get('price', 0))
                        continue

                    if valid_trade and entry_zone_reached and has_real_trade_params and variant_b_included(raw_confidence, overridden_confidence, direction, zone):
                        if variant_b_excluded(confluence_score, raw_confidence, is_killzone, direction, dxy_implication):
                            send_telegram(f"⚠️ *[{variant}] Signal excluded* — matches a known-weaker pattern (high-confluence-only, or the maximally-selective stacked criteria), skipped even though it reached its entry zone.\nAlert type: {alert_type} at {data.get('price')}")
                            monitor_active_trades(variant, data.get('price', 0))
                            continue
                        risk_ok, risk_msg = check_risk_cap_before_trade(variant)
                        if risk_ok:
                            alert_time = datetime.utcnow().strftime('%H:%M UTC')
                            scaled_target_price = round(entry_price + (target_price - entry_price) * 0.8, 2)
                            trade_context = {
                                "session": session_name, "killzone": is_killzone, "zone": zone,
                                "zone_pct": zone_pct, "dxy_direction": dxy_direction,
                                "dxy_implication": dxy_implication, "news_risk": news_risk,
                                "spread_risk": spread_risk, "hour_quality": hour_quality,
                                "confluence_score": confluence_score,
                                "risk_pct": PROP_FIRM_RULES["max_loss_per_trade_pct"],
                                "original_target": target_price,
                                "target_scaled_to_pct": 80,
                            }
                            if entry_zone:
                                trade_context["entry_zone_low"] = entry_zone[0]
                                trade_context["entry_zone_high"] = entry_zone[1]
                            log_paper_trade(variant, alert_type, data.get('price'), direction, entry_price, stop_price,
                                             scaled_target_price, overridden_confidence, alert_time, context=trade_context)
                        else:
                            print(f"[{variant}] {risk_msg}")
                            send_telegram(risk_msg)
                    elif valid_trade and entry_zone_reached and not has_real_trade_params:
                        print(f"[{variant}] Skipped logging paper trade — Claude did not provide a real extractable stop/target (likely an explicit 'No trade' response). Alert:{alert_type}")
                    elif valid_trade and not entry_zone_reached:
                        msg = (f"⏳ *[{variant}] Setup noted — not logged as a trade*\n"
                               f"Current price (${entry_price:,.2f}) hasn't reached the proposed "
                               f"entry zone (${entry_zone[0]:,.2f}–${entry_zone[1]:,.2f}) yet. "
                               f"This is a level to watch, not a live trade.")
                        print(msg)
                        send_telegram(msg)
                    elif not valid_trade:
                        print(f"[{variant}] Skipped logging paper trade — SL/TP inconsistent. Dir:{direction} Entry:{entry_price} SL:{stop_price} TP:{target_price}")

                    monitor_active_trades(variant, data.get('price', 0))
                    continue

                if variant == "C":
                    has_real_trade_params = sl_found and tp_found

                    try:
                        if valid_trade and entry_zone_reached and has_real_trade_params:
                            if variant_c_included(raw_confidence, overridden_confidence, direction, zone, alert_type):
                                if variant_c_excluded(confluence_score, is_killzone):
                                    shadow_context = {
                                        "session": session_name, "killzone": is_killzone, "zone": zone,
                                        "zone_pct": zone_pct, "dxy_direction": dxy_direction,
                                        "dxy_implication": dxy_implication, "news_risk": news_risk,
                                        "spread_risk": spread_risk, "hour_quality": hour_quality,
                                        "confluence_score": confluence_score,
                                    }
                                    log_shadow_trade(variant, alert_type, data.get('price'), direction, entry_price,
                                                      stop_price, target_price, overridden_confidence,
                                                      "EXCLUDED_BY_C_RULE", context=shadow_context)
                    except Exception as e:
                        print(f"[{variant}] Shadow tracking error (non-fatal, real trade path unaffected): {e}")

                    if news_risk and overridden_confidence != "HIGH":
                        send_telegram(f"⚠️ *[{variant}] Alert suppressed — news risk active*\n{news_msg}\nAlert type: {alert_type} at {data.get('price')}")
                        monitor_active_trades(variant, data.get('price', 0))
                        continue

                    if valid_trade and entry_zone_reached and has_real_trade_params and variant_c_included(raw_confidence, overridden_confidence, direction, zone, alert_type):
                        if variant_c_excluded(confluence_score, is_killzone):
                            send_telegram(f"⚠️ *[{variant}] Signal excluded* — matches a known-weaker pattern (high-confluence-only, or inside a killzone), skipped even though it reached its entry zone.\nAlert type: {alert_type} at {data.get('price')}")
                            monitor_active_trades(variant, data.get('price', 0))
                            continue
                        risk_ok, risk_msg = check_risk_cap_before_trade(variant)
                        if risk_ok:
                            alert_time = datetime.utcnow().strftime('%H:%M UTC')
                            scaled_target_price = round(entry_price + (target_price - entry_price) * 0.8, 2)
                            trade_context = {
                                "session": session_name, "killzone": is_killzone, "zone": zone,
                                "zone_pct": zone_pct, "dxy_direction": dxy_direction,
                                "dxy_implication": dxy_implication, "news_risk": news_risk,
                                "spread_risk": spread_risk, "hour_quality": hour_quality,
                                "confluence_score": confluence_score,
                                "risk_pct": PROP_FIRM_RULES["max_loss_per_trade_pct"],
                                "original_target": target_price,
                                "target_scaled_to_pct": 80,
                            }
                            if entry_zone:
                                trade_context["entry_zone_low"] = entry_zone[0]
                                trade_context["entry_zone_high"] = entry_zone[1]
                            log_paper_trade(variant, alert_type, data.get('price'), direction, entry_price, stop_price,
                                             scaled_target_price, overridden_confidence, alert_time, context=trade_context)
                        else:
                            print(f"[{variant}] {risk_msg}")
                            send_telegram(risk_msg)
                    elif valid_trade and entry_zone_reached and not has_real_trade_params:
                        print(f"[{variant}] Skipped logging paper trade — Claude did not provide a real extractable stop/target (likely an explicit 'No trade' response). Alert:{alert_type}")
                    elif valid_trade and not entry_zone_reached:
                        msg = (f"⏳ *[{variant}] Setup noted — not logged as a trade*\n"
                               f"Current price (${entry_price:,.2f}) hasn't reached the proposed "
                               f"entry zone (${entry_zone[0]:,.2f}–${entry_zone[1]:,.2f}) yet. "
                               f"This is a level to watch, not a live trade.")
                        print(msg)
                        send_telegram(msg)
                    elif not valid_trade:
                        print(f"[{variant}] Skipped logging paper trade — SL/TP inconsistent. Dir:{direction} Entry:{entry_price} SL:{stop_price} TP:{target_price}")

                    monitor_active_trades(variant, data.get('price', 0))
                    continue
            except Exception as e:
                error_msg = f"⚠️ [{variant}] SYSTEM ERROR (other variants unaffected): {str(e)}"
                print(error_msg)
                send_telegram(error_msg)

        save_state()

    except Exception as e:
        error_msg = f"⚠️ SYSTEM ERROR: {str(e)}"
        print(error_msg)
        send_telegram(error_msg)

# ============================================================
# MORNING BRIEFING
# ============================================================
@app.route('/morning-briefing', methods=['GET'])
def morning_briefing():
    try:
        dxy_direction, dxy_desc, dxy_implication = get_dxy_bias()
        levels_text = "\n".join([f"- {k.replace('_', ' ').title()}: {v}" for k, v in KEY_LEVELS.items()])
        prompt = f"""
You are an expert XAUUSD analyst. Concise morning briefing for a gold SMC trader.

Today: {datetime.utcnow().strftime('%A %d %B %Y')}
Key levels: {levels_text}
DXY: {dxy_desc}
Recent alerts: {str(recent_alerts[-3:]) if recent_alerts else "None yet"}

Cover in under 300 words:
1. Key levels to watch today
2. Session focus (London vs NY)
3. Directional bias (bullish/bearish/neutral) and why
4. Best setup to look for
5. What to avoid
6. One sentence summary
"""
        message = call_claude(
            messages=[{"role": "user", "content": prompt}],
            max_tokens=900
        )
        send_telegram(f"☀️ *XAUUSD Morning Briefing — {datetime.utcnow().strftime('%d %b %Y')}*\n\n{message.content[0].text}")
        return jsonify({"status": "briefing sent"})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# WEEKLY BIAS REPORT
# ============================================================
@app.route('/weekly-bias', methods=['GET'])
def weekly_bias_report():
    try:
        dxy_direction, dxy_desc, dxy_implication = get_dxy_bias()
        cot_data = get_cot_data()
        cot_summary = f"{cot_data['spec_bias']} — {cot_data['spec_desc']} | {cot_data['change_desc']}"
        levels_text = "\n".join([f"- {k.replace('_', ' ').title()}: {v}" for k, v in KEY_LEVELS.items()])
        prompt = f"""
You are an expert XAUUSD analyst. Weekly bias report for an SMC trader.

Date: {datetime.utcnow().strftime('%A %d %B %Y')}
Key levels: {levels_text}
DXY: {dxy_desc}
COT Positioning: {cot_summary}

Cover in under 350 words:
**WEEKLY BIAS** — bullish/bearish/neutral and why
**KEY LEVELS** — most important 3 levels this week
**SESSION FOCUS** — London or NY and why
**BEST SETUP** — specific setup type to look for
**AVOID** — what not to trade
**SUMMARY** — one sentence
"""
        message = call_claude(
            messages=[{"role": "user", "content": prompt}],
            max_tokens=1000
        )
        send_telegram(f"📊 *XAUUSD Weekly Bias — {datetime.utcnow().strftime('%d %b %Y')}*\n\n{message.content[0].text}")
        return jsonify({"status": "weekly bias sent"})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# MONDAY GAP ANALYSIS
# ============================================================
@app.route('/monday-gap', methods=['GET'])
def monday_gap_analysis():
    try:
        prompt = f"""
You are an expert XAUUSD analyst. Monday morning before London open.

Key levels:
Weekly High: {KEY_LEVELS['weekly_high']}
Weekly Low: {KEY_LEVELS['weekly_low']}
Major Resistance: {KEY_LEVELS['major_resistance']}
Major Support: {KEY_LEVELS['major_support']}

Cover in under 250 words:
**GAP STRATEGY** — what to look for at Monday open
**FIRST SETUP** — ideal first trade conditions
**ASIAN SESSION** — likely direction before London
**AVOID** — traps smart money sets at Monday open
"""
        message = call_claude(
            messages=[{"role": "user", "content": prompt}],
            max_tokens=800
        )
        send_telegram(f"🌅 *XAUUSD Monday Gap Analysis — {datetime.utcnow().strftime('%d %b %Y')}*\n\n{message.content[0].text}")
        return jsonify({"status": "monday gap sent"})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# COT WEEKLY REPORT
# ============================================================
@app.route('/cot-report', methods=['GET'])
def cot_report():
    try:
        cot_data = get_cot_data()
        prompt = f"""
You are an expert gold analyst interpreting the weekly Commitment of Traders report.

## LATEST COT DATA — GOLD FUTURES
Date: {cot_data['date']}
Speculator Position: {cot_data['spec_bias']}
Detail: {cot_data['spec_desc']}
Weekly Change: {cot_data['change_desc']}
Net Position: {cot_data['net_position']:,} contracts

## YOUR ANALYSIS

**INSTITUTIONAL BIAS**
What does this positioning tell us about smart money's view on gold?

**CONFLUENCE WITH TECHNICAL PICTURE**
Key levels: High {KEY_LEVELS['weekly_high']} | Low {KEY_LEVELS['weekly_low']} | Resistance {KEY_LEVELS['major_resistance']} | Support {KEY_LEVELS['major_support']}
Does institutional positioning support or conflict with current technical structure?

**TRADING IMPLICATION**
Should we favour longs or shorts next week based on COT data?

**WARNING SIGNS**
Any extreme positioning that historically precedes reversals?

Keep it concise and actionable. Maximum 200 words.
"""
        message = call_claude(
            messages=[{"role": "user", "content": prompt}],
            max_tokens=700
        )
        analysis = message.content[0].text
        telegram_message = f"""
📊 *COT Report Analysis — Gold Futures*
_Week of {cot_data['date']}_

*Institutional Position:* {cot_data['spec_bias']}
*Detail:* {cot_data['spec_desc']}
*Weekly Change:* {cot_data['change_desc']}

{analysis}
"""
        send_telegram(telegram_message)
        return jsonify({"status": "COT report sent", "spec_bias": cot_data['spec_bias'], "net_position": cot_data['net_position']})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# PROP FIRM MONITOR
# ============================================================
@app.route('/prop-status', methods=['GET'])
def prop_status():
    try:
        account = PROP_FIRM_RULES["account_size"]
        daily_loss_limit = account * (PROP_FIRM_RULES["max_daily_loss_pct"] / 100)
        total_drawdown_limit = account * (PROP_FIRM_RULES["max_total_drawdown_pct"] / 100)
        sections = []
        statuses = {}
        for v in VARIANTS:
            daily_used_pct = (abs(min(daily_pnl[v], 0)) / account) * 100
            total_used_pct = (abs(min(total_pnl[v], 0)) / account) * 100
            daily_remaining = daily_loss_limit - abs(min(daily_pnl[v], 0))
            total_remaining = total_drawdown_limit - abs(min(total_pnl[v], 0))
            daily_status = "🔴 DANGER" if daily_used_pct >= 80 else "🟡 CAUTION" if daily_used_pct >= 50 else "🟢 SAFE"
            total_status = "🔴 DANGER" if total_used_pct >= 80 else "🟡 CAUTION" if total_used_pct >= 50 else "🟢 SAFE"
            statuses[v] = {"daily_status": daily_status, "total_status": total_status}
            sections.append(f"""
*[{v}]* Balance: ${current_balance[v]:,.2f} | Today: ${daily_pnl[v]:,.2f} | Total: ${total_pnl[v]:,.2f} | Days: {trading_days[v]}/{PROP_FIRM_RULES['min_trading_days']}
Daily Loss: {daily_status} ({daily_used_pct:.1f}% used, ${daily_remaining:,.2f} left)
Drawdown: {total_status} ({total_used_pct:.1f}% used, ${total_remaining:,.2f} left)""")
        message = f"""
📊 *Prop Firm Status Report — A/B/C*

*Account Size (each):* ${account:,.2f}
*Max Risk Per Trade:* {PROP_FIRM_RULES['max_loss_per_trade_pct']}% (${account * PROP_FIRM_RULES['max_loss_per_trade_pct'] / 100:,.2f})
{"".join(sections)}
"""
        send_telegram(message)
        return jsonify({"status": "ok", "variants": statuses})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# UPDATE P&L (manual override — paper trades from TradingView
# alerts now auto-track PnL via apply_trade_pnl() when they hit
# SL/TP. Use this endpoint only for manually logging trades placed
# outside the automated system, e.g. real broker/demo fills.)
# ============================================================
@app.route('/update-pnl', methods=['POST'])
def update_pnl():
    global daily_pnl, total_pnl, current_balance, trading_days
    try:
        data = request.get_json(silent=True) or {}
        variant = data.get('variant', '')
        if variant not in VARIANTS:
            return jsonify({"status": "error", "message": f"'variant' required in body, must be one of {VARIANTS}"}), 400
        trade_pnl = float(data.get('pnl', 0))
        daily_pnl[variant] += trade_pnl
        total_pnl[variant] += trade_pnl
        current_balance[variant] += trade_pnl
        account = PROP_FIRM_RULES["account_size"]
        daily_loss_limit = account * (PROP_FIRM_RULES["max_daily_loss_pct"] / 100)
        total_drawdown_limit = account * (PROP_FIRM_RULES["max_total_drawdown_pct"] / 100)
        warnings = []
        if abs(min(daily_pnl[variant], 0)) >= daily_loss_limit * 0.8:
            warnings.append(f"⚠️ [{variant}] DAILY LOSS WARNING — at {(abs(min(daily_pnl[variant],0))/account)*100:.1f}% of limit")
        if abs(min(daily_pnl[variant], 0)) >= daily_loss_limit:
            warnings.append(f"🚨 [{variant}] DAILY LOSS LIMIT HIT — STOP TRADING TODAY")
        if abs(min(total_pnl[variant], 0)) >= total_drawdown_limit:
            warnings.append(f"🚨 [{variant}] TOTAL DRAWDOWN LIMIT HIT — ACCOUNT AT RISK")
        if warnings:
            send_telegram("\n".join(warnings))
        return jsonify({"status": "updated", "variant": variant, "daily_pnl": daily_pnl[variant], "total_pnl": total_pnl[variant]})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# AUTO LEVEL DETECTION
# ============================================================
@app.route('/auto-levels', methods=['GET'])
def auto_update_levels():
    global KEY_LEVELS
    try:
        gold = yf.download('GC=F', period='30d', interval='1d', progress=False, timeout=10)
        if gold.empty:
            send_telegram("⚠️ Auto level update failed — no data returned")
            return jsonify({"status": "error", "message": "no data"})
        gold.columns = [col[0] for col in gold.columns]
        weekly = gold.tail(5)
        today = gold.tail(1)
        recent = gold.tail(5)
        full_range = gold.tail(10)
        weekly_high = round(float(weekly['High'].max()), 2)
        weekly_low = round(float(weekly['Low'].min()), 2)
        daily_high = round(float(today['High'].iloc[-1]), 2)
        daily_low = round(float(today['Low'].iloc[-1]), 2)
        major_resistance = round(float(recent['High'].max()), 2)
        major_support = round(float(recent['Low'].min()), 2)
        dealing_range_high = round(float(full_range['High'].max()), 2)
        dealing_range_low = round(float(full_range['Low'].min()), 2)
        KEY_LEVELS = {
            "weekly_high": weekly_high,
            "weekly_low": weekly_low,
            "major_resistance": major_resistance,
            "major_support": major_support,
            "daily_high": daily_high,
            "daily_low": daily_low,
            "dealing_range_high": dealing_range_high,
            "dealing_range_low": dealing_range_low,
        }
        levels_text = "\n".join([f"- {k.replace('_', ' ').title()}: {v}" for k, v in KEY_LEVELS.items()])
        send_telegram(f"🤖 *Auto Level Update Complete*\n_{datetime.utcnow().strftime('%d %b %Y — %H:%M UTC')}_\n\n{levels_text}\n\n_Claude will use these levels until next Sunday_ ✅")
        return jsonify({"status": "levels auto updated", "levels": KEY_LEVELS})
    except Exception as e:
        error_msg = f"⚠️ Auto level update error: {str(e)}"
        send_telegram(error_msg)
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# INTRADAY LEVEL UPDATER
# ============================================================
@app.route('/update-intraday', methods=['GET'])
def update_intraday():
    global KEY_LEVELS
    try:
        gold = get_mt5_candles_if_fresh()
        if gold is None:
            gold = yf.download('GC=F', period='1d', interval='5m', progress=False, timeout=10)
            if gold.empty:
                return jsonify({"status": "no data"})
            gold.columns = [col[0] for col in gold.columns]
        todays_high = round(float(gold['High'].max()), 2)
        todays_low = round(float(gold['Low'].min()), 2)
        current_price = round(float(gold['Close'].iloc[-1]), 2)
        KEY_LEVELS['daily_high'] = todays_high
        KEY_LEVELS['daily_low'] = todays_low
        print(f"Intraday update: High {todays_high} | Low {todays_low} | Current {current_price}")
        return jsonify({"status": "intraday levels updated", "daily_high": todays_high, "daily_low": todays_low, "current_price": current_price})
    except Exception as e:
        print(f"Intraday update error: {e}")
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# UPDATE KEY LEVELS MANUALLY
# ============================================================
@app.route('/update-levels', methods=['POST'])
def update_levels():
    global KEY_LEVELS
    try:
        new_levels = request.get_json(silent=True)
        if new_levels is None:
            return jsonify({"status": "error", "message": "request body must be valid JSON with Content-Type: application/json"}), 400
        KEY_LEVELS.update(new_levels)
        send_telegram(f"📊 *Key Levels Updated*\n" + "\n".join([f"- {k}: {v}" for k, v in KEY_LEVELS.items()]))
        return jsonify({"status": "levels updated", "levels": KEY_LEVELS})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# CONTINUOUS TRADE MONITOR
# ============================================================
@app.route('/monitor-trades', methods=['GET'])
def monitor_trades_endpoint():
    try:
        any_active = any(active_trades[v] for v in VARIANTS)
        any_shadow = any(active_shadow_trades[v] for v in VARIANTS)
        if not any_active and not any_shadow:
            return jsonify({"status": "no active trades"})
        gold = get_mt5_candles_if_fresh()
        if gold is None:
            gold = yf.download('GC=F', period='1d', interval='5m', progress=False, timeout=10)
            if gold.empty:
                return jsonify({"status": "no price data"})
            gold.columns = [col[0] for col in gold.columns]
            if is_price_data_stale(gold):
                print(f"Price data stale (last candle: {gold.index[-1]}) — skipping this monitor-trades cycle")
                return jsonify({"status": "price data stale, skipped"})
        current_price = get_mt5_price_if_fresh()
        if current_price is None:
            current_price = round(float(gold['Close'].iloc[-1]), 2)
        for variant in VARIANTS:
            if active_trades[variant]:
                monitor_active_trades(variant, current_price)
                # Catch anything the quick check above missed — a stop or
                # target briefly touched (wicked through) between polls.
                thorough_scan_active_trades(variant, gold)
            if active_shadow_trades[variant]:
                monitor_shadow_trades(variant, gold)
        shadow_open = {v: len(active_shadow_trades[v]) for v in VARIANTS}
        return jsonify({"status": "checked", "current_price": current_price, "shadow_trades_open": shadow_open})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# MT5 BRIDGE
# Polled by a small Python script running on a Windows VPS alongside
# the actual MT5 terminal. Deliberately dumb on this side -- Railway
# never decides WHAT to trade here, only exposes decisions Claude
# already made via the normal would_log gate. All position sizing,
# order placement, and SL/TP execution happens on the bridge/broker
# side, not here.
# ============================================================
def check_bridge_secret():
    """
    Header is still the primary, intended method (curl -H, the bridge
    script itself). The query-param fallback (15 Aug) exists purely
    so a read-only endpoint can be reached from a plain phone browser
    address bar, which can't set custom headers at all. Applies to
    every bridge-protected endpoint, not just the read-only ones,
    since this is the one shared check they all use -- worth knowing
    if ever pasting a URL with ?secret=... into a browser for one of
    the endpoints that actually places or changes something for real,
    since the secret would then sit in that browser's own history.
    """
    if not MT5_BRIDGE_SECRET:
        return False, "MT5_BRIDGE_SECRET not configured on the server"
    provided = request.headers.get('X-Bridge-Secret', '') or request.args.get('secret', '')
    if provided != MT5_BRIDGE_SECRET:
        return False, "invalid or missing X-Bridge-Secret header (or ?secret= query param)"
    return True, ""


@app.route('/mt5/pending', methods=['GET'])
def mt5_pending():
    ok, msg = check_bridge_secret()
    if not ok:
        return jsonify({"status": "error", "message": msg}), 401
    variant = request.args.get('variant', '')
    if variant not in VARIANTS:
        return jsonify({"status": "error", "message": f"variant query param required, must be one of {VARIANTS}"}), 400
    to_return = []
    for trade_id, entry in mt5_pending_trades[variant].items():
        if entry["status"] == "PENDING":
            to_return.append(entry)
            # Mark as dispatched immediately on read, not on ack --
            # avoids the same trade being handed to the bridge twice
            # just because it's slow to report back. If the bridge
            # genuinely never places it (crash mid-flight), it stays
            # DISPATCHED rather than silently retrying with real
            # money -- a stuck trade is safer than a duplicated one.
            entry["status"] = "DISPATCHED"
            entry["dispatched_at"] = datetime.now(timezone.utc).isoformat()
    if to_return:
        save_mt5_queue()
    return jsonify({"status": "ok", "trades": to_return})


@app.route('/mt5/ack', methods=['POST'])
def mt5_ack():
    ok, msg = check_bridge_secret()
    if not ok:
        return jsonify({"status": "error", "message": msg}), 401
    try:
        data = request.get_json(silent=True) or {}
        variant = data.get('variant', '')
        if variant not in VARIANTS:
            return jsonify({"status": "error", "message": f"'variant' required in body, must be one of {VARIANTS}"}), 400
        trade_id = data.get('trade_id')
        entry = mt5_pending_trades[variant].get(trade_id)
        if not entry:
            return jsonify({"status": "error", "message": f"unknown trade_id {trade_id} for variant {variant}"}), 404
        if data.get('success'):
            entry["status"] = "PLACED"
            entry["ticket"] = data.get('ticket')
            entry["fill_price"] = data.get('fill_price')
            # Tag the real MT5 ticket onto the matching paper trade too,
            # so the paper record and the real execution can be
            # reconciled later (predicted vs actual entry, slippage etc).
            if trade_id in active_trades[variant]:
                active_trades[variant][trade_id]['mt5_ticket'] = data.get('ticket')
                active_trades[variant][trade_id]['mt5_fill_price'] = data.get('fill_price')
            send_telegram(f"🔗 *[{variant}] MT5 order placed* — {entry['alert_type']} {entry['direction']} | ticket #{data.get('ticket')} @ {data.get('fill_price')}")
        else:
            entry["status"] = "FAILED"
            entry["error"] = data.get('error', 'unknown error')
            send_telegram(f"⚠️ *[{variant}] MT5 order failed* — {entry['alert_type']} {entry['direction']}: {entry['error']}")
        save_mt5_queue()
        return jsonify({"status": "ok"})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500


@app.route('/mt5/status', methods=['GET'])
def mt5_status():
    """Human-readable snapshot of all three variants' bridge status
    at a glance -- no secret required, read-only, no trade details
    beyond counts. Price/candle data is genuinely shared market data
    (only variant A's bridge relays it), so that part stays a single
    value rather than duplicated three ways."""
    per_variant = {}
    for v in VARIANTS:
        counts = {}
        for entry in mt5_pending_trades[v].values():
            counts[entry["status"]] = counts.get(entry["status"], 0) + 1
        heartbeat_info = {"last_heartbeat": None, "seconds_ago": None}
        if last_bridge_heartbeat[v] is not None:
            heartbeat_info["last_heartbeat"] = last_bridge_heartbeat[v].isoformat()
            heartbeat_info["seconds_ago"] = int((datetime.now(timezone.utc) - last_bridge_heartbeat[v]).total_seconds())
        per_variant[v] = {
            "queue_counts": counts, "total_queued": len(mt5_pending_trades[v]),
            "bridge_heartbeat": heartbeat_info,
            "current_balance": current_balance[v],
        }
    price_info = {"bid": mt5_live_price.get("bid"), "ask": mt5_live_price.get("ask"), "seconds_ago": None, "trusted_right_now": False}
    if mt5_live_price.get("updated_at") is not None:
        age = int((datetime.now(timezone.utc) - mt5_live_price["updated_at"]).total_seconds())
        price_info["seconds_ago"] = age
        price_info["trusted_right_now"] = age <= MT5_PRICE_STALENESS_SECONDS
    candle_info = {"count": 0, "seconds_ago": None, "trusted_right_now": False, "most_recent_candle_time": None}
    if mt5_candle_history.get("updated_at") is not None:
        age = int((datetime.now(timezone.utc) - mt5_candle_history["updated_at"]).total_seconds())
        candle_info["seconds_ago"] = age
        candle_info["trusted_right_now"] = age <= MT5_CANDLE_STALENESS_SECONDS
        candle_info["count"] = len(mt5_candle_history.get("candles", []))
        if candle_info["count"] > 0:
            candle_info["most_recent_candle_time"] = mt5_candle_history["candles"][-1]["time"]
    return jsonify({
        "status": "ok",
        "variants": per_variant,
        "mt5_live_price": price_info,
        "mt5_candles": candle_info,
        "app_instance": {"id": INSTANCE_ID, "started_at": INSTANCE_STARTED_AT},
        "safety_toggles": {
            "drawdown_protection_disabled": DRAWDOWN_PROTECTION_DISABLED,
            "daily_loss_limit_disabled": DAILY_LOSS_LIMIT_DISABLED,
        },
    })


@app.route('/mt5/test-queue', methods=['POST'])
def mt5_test_queue():
    """
    Queues a synthetic trade directly into mt5_pending_trades WITHOUT
    going through log_paper_trade() -- never touches paper_trades,
    active_trades, current_balance, or any real stats at all. Every
    earlier bridge test used the real /webhook path instead, which
    logged as a genuine trade each time and needed manual cleanup
    afterward (see /admin/remove-trade). This tests the exact same
    bridge round trip -- place, ack, close -- with nothing real to
    clean up once it's done. Defaults to a deliberately tiny risk_pct
    unless overridden.
    """
    ok, msg = check_bridge_secret()
    if not ok:
        return jsonify({"status": "error", "message": msg}), 401
    try:
        data = request.get_json(silent=True) or {}
        variant = data.get('variant', '')
        if variant not in VARIANTS:
            return jsonify({"status": "error", "message": f"'variant' required in body, must be one of {VARIANTS}"}), 400
        trade_id = f"TESTONLY_{variant}_{datetime.now(timezone.utc).strftime('%Y%m%d%H%M%S%f')}"
        mt5_pending_trades[variant][trade_id] = {
            "trade_id": trade_id,
            "status": "PENDING",
            "queued_at": datetime.now(timezone.utc).isoformat(),
            "alert_type": "TEST",
            "direction": data.get("direction", "LONG"),
            "entry": data.get("entry", 4070.0),
            "stop": data.get("stop", 4059.0),
            "target": data.get("target", 4080.0),
            "risk_pct": data.get("risk_pct", 0.1),
            "confidence": "TEST",
            "ticket": None,
            "fill_price": None,
            "error": None,
        }
        save_mt5_queue()
        return jsonify({
            "status": "ok", "variant": variant, "trade_id": trade_id,
            "message": "Queued for the bridge -- never touches paper_trades or balance, nothing to clean up after"
        })
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500


@app.route('/mt5/heartbeat', methods=['POST'])
def mt5_heartbeat():
    """
    Each of the three bridges calls this every poll cycle while it's
    alive, tagged with its own variant. A separate scheduled check
    watches each variant's heartbeat independently for going stale --
    see check_bridge_watchdog() below.
    """
    global last_bridge_heartbeat, bridge_watchdog_alerted
    ok, msg = check_bridge_secret()
    if not ok:
        return jsonify({"status": "error", "message": msg}), 401
    try:
        data = request.get_json(silent=True) or {}
        variant = data.get('variant', '')
        if variant not in VARIANTS:
            return jsonify({"status": "error", "message": f"'variant' required in body, must be one of {VARIANTS}"}), 400
        last_bridge_heartbeat[variant] = datetime.now(timezone.utc)
        bridge_watchdog_alerted[variant] = False  # a fresh heartbeat means it's back, if it had gone quiet before
        return jsonify({"status": "ok"})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500


@app.route('/mt5/price-update', methods=['POST'])
def mt5_price_update():
    """The bridge calls this every poll cycle alongside the heartbeat,
    relaying MT5's own live bid/ask -- the real price, not a separate
    third-party feed. See get_mt5_price_if_fresh() for how this gets
    used and when it's trusted. Validates the values themselves, not
    just that the fields are present -- a degenerate reading (e.g.
    bid/ask of 0 during some transient glitch) must never get stored,
    since a $0 gold price would make every open trade look like it hit
    both its stop and target simultaneously."""
    global mt5_live_price
    ok, msg = check_bridge_secret()
    if not ok:
        return jsonify({"status": "error", "message": msg}), 401
    try:
        data = request.get_json(silent=True) or {}
        bid, ask = data.get('bid'), data.get('ask')
        if bid is None or ask is None:
            return jsonify({"status": "error", "message": "bid and ask are both required"}), 400
        bid, ask = float(bid), float(ask)
        if bid <= 0 or ask <= 0:
            return jsonify({"status": "error", "message": "bid and ask must both be positive"}), 400
        if ask < bid:
            return jsonify({"status": "error", "message": "ask cannot be below bid"}), 400
        mt5_live_price = {"bid": bid, "ask": ask, "updated_at": datetime.now(timezone.utc)}
        return jsonify({"status": "ok"})
    except (TypeError, ValueError) as e:
        return jsonify({"status": "error", "message": f"bid/ask must be numeric: {e}"}), 400


mt5_candle_history = {"candles": [], "updated_at": None}
MT5_CANDLE_STALENESS_SECONDS = 300  # candles relay every 2 min; this gives real headroom


@app.route('/mt5/candle-update', methods=['POST'])
def mt5_candle_update():
    """The bridge relays recent M5 candle history here, already
    converted to genuine UTC on its side. Validated again here too --
    same defense-in-depth principle as /mt5/price-update -- rather
    than trust a single validation layer for data this consequential."""
    global mt5_candle_history
    ok, msg = check_bridge_secret()
    if not ok:
        return jsonify({"status": "error", "message": msg}), 401
    try:
        data = request.get_json(silent=True) or {}
        candles = data.get('candles')
        if not candles or not isinstance(candles, list):
            return jsonify({"status": "error", "message": "candles must be a non-empty list"}), 400
        cleaned = []
        for c in candles:
            t, o, h, l, cl = c.get('time'), c.get('open'), c.get('high'), c.get('low'), c.get('close')
            if None in (t, o, h, l, cl):
                return jsonify({"status": "error", "message": f"candle missing a required field: {c}"}), 400
            o, h, l, cl = float(o), float(h), float(l), float(cl)
            if min(o, h, l, cl) <= 0:
                return jsonify({"status": "error", "message": f"candle has a non-positive price: {c}"}), 400
            if h < l:
                return jsonify({"status": "error", "message": f"candle high is below its low: {c}"}), 400
            try:
                datetime.fromisoformat(t)
            except ValueError:
                return jsonify({"status": "error", "message": f"candle time isn't valid ISO format: {t!r}"}), 400
            cleaned.append({"time": t, "Open": o, "High": h, "Low": l, "Close": cl})
        mt5_candle_history = {"candles": cleaned, "updated_at": datetime.now(timezone.utc)}
        return jsonify({"status": "ok", "count": len(cleaned)})
    except (TypeError, ValueError) as e:
        return jsonify({"status": "error", "message": f"invalid candle data: {e}"}), 400


def get_mt5_candles_if_fresh():
    """Returns MT5's real relayed candle history as a DataFrame in the
    exact shape existing code already expects (DatetimeIndex, Open/
    High/Low/Close columns) -- matching what yfinance produces after
    its own column-flattening -- if fresh enough to trust, else None."""
    try:
        updated_at = mt5_candle_history.get("updated_at")
        if updated_at is None:
            return None
        age = (datetime.now(timezone.utc) - updated_at).total_seconds()
        if age > MT5_CANDLE_STALENESS_SECONDS:
            return None
        candles = mt5_candle_history.get("candles")
        if not candles:
            return None
        df = pd.DataFrame(candles)
        df.index = pd.to_datetime(df['time'], utc=True)
        df = df[['Open', 'High', 'Low', 'Close']]
        return df
    except Exception:
        return None


def get_mt5_price_if_fresh():
    """Returns MT5's real mid price if the bridge has reported it
    recently enough to trust, else None -- caller should fall back to
    yfinance. Never raises; a malformed or missing value is treated
    the same as no data at all."""
    try:
        updated_at = mt5_live_price.get("updated_at")
        if updated_at is None:
            return None
        age = (datetime.now(timezone.utc) - updated_at).total_seconds()
        if age > MT5_PRICE_STALENESS_SECONDS:
            return None
        bid, ask = mt5_live_price.get("bid"), mt5_live_price.get("ask")
        if bid is None or ask is None:
            return None
        return round((bid + ask) / 2, 2)
    except Exception:
        return None


def check_bridge_watchdog():
    """
    Runs on an interval (see scheduler setup). Checks each of the three
    variants' bridges independently, alerting once per outage per
    variant via Telegram -- not repeatedly, so it doesn't spam, and not
    masked by the other two bridges still checking in fine. Says
    nothing at all for a variant whose bridge simply hasn't been
    started yet (no heartbeat ever received) -- that's not a failure,
    just not running.
    """
    global bridge_watchdog_alerted
    for variant in VARIANTS:
        if last_bridge_heartbeat[variant] is None:
            continue  # never started this session -- nothing to alert about

        quiet_for = datetime.now(timezone.utc) - last_bridge_heartbeat[variant]
        if quiet_for > timedelta(minutes=BRIDGE_HEARTBEAT_TIMEOUT_MINUTES) and not bridge_watchdog_alerted[variant]:
            minutes = int(quiet_for.total_seconds() // 60)
            send_telegram(
                f"⚠️ *[{variant}] MT5 bridge watchdog* — no heartbeat for {minutes} min "
                f"(last seen {last_bridge_heartbeat[variant].strftime('%H:%M UTC')}). "
                f"If a position is open, it may not be getting tracked right now."
            )
            bridge_watchdog_alerted[variant] = True


@app.route('/mt5/trade-closed', methods=['POST'])
def mt5_trade_closed():
    """
    Reports a real MT5-placed trade's closure back into the same
    tracking self-review and counterfactual reporting already read from
    (active_trades / paper_trades) -- without this, an MT5-placed trade
    closes silently and is invisible to every report the rest of the
    system relies on.
    """
    ok, msg = check_bridge_secret()
    if not ok:
        return jsonify({"status": "error", "message": msg}), 401
    try:
        data = request.get_json(silent=True) or {}
        variant = data.get('variant', '')
        if variant not in VARIANTS:
            return jsonify({"status": "error", "message": f"'variant' required in body, must be one of {VARIANTS}"}), 400
        trade_id = data.get('trade_id')
        trade = active_trades[variant].get(trade_id)
        if not trade:
            # Fall back to this variant's own paper_trades directly --
            # active_trades is a convenience view, not the real source
            # of truth. A trade can end up open in paper_trades but
            # missing here (e.g. if it was reopened via
            # /admin/reopen-trade and this request landed on a
            # different app instance than that one did).
            trade = next((t for t in paper_trades[variant] if t.get('id') == trade_id), None)
            if trade and trade.get('result') != 'OPEN':
                trade = None  # exists, but genuinely already closed -- not a fallback case
        if not trade:
            return jsonify({"status": "error", "message": f"unknown or already-closed trade_id {trade_id} for variant {variant}"}), 404

        result = data.get('result')
        if result not in ("WIN", "LOSS"):
            return jsonify({"status": "error", "message": "result must be WIN or LOSS"}), 400
        real_pnl = data.get('real_pnl')

        trade['result'] = result
        trade['close_price'] = data.get('close_price')
        trade['mt5_closed_via_bridge'] = True
        pnl = apply_trade_pnl(variant, trade, result, real_pnl_override=real_pnl)

        active_trades[variant].pop(trade_id, None)
        try:
            with open(data_path('paper_trades.json'), 'w') as f:
                json.dump(paper_trades, f, indent=2)
        except Exception as e:
            print(f"Paper trade save error on MT5 close: {e}")
        save_state()

        emoji = "✅" if result == "WIN" else "❌"
        send_telegram(
            f"{emoji} *[{variant}] MT5 trade closed* — {trade.get('type', '')} {trade.get('direction', '')} | "
            f"{result} | ${pnl:.2f} | ticket #{trade.get('mt5_ticket')}"
        )
        return jsonify({"status": "ok", "pnl": round(pnl, 2)})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500


@app.route('/admin/recent-trades', methods=['GET'])
def admin_recent_trades():
    """Read-only -- last N paper trades (default 5, override with
    ?limit=20) for one specific variant (?variant=A/B/C, required) with
    enough detail to spot a manually-injected test trade and get its
    exact trade_id."""
    ok, msg = check_bridge_secret()
    if not ok:
        return jsonify({"status": "error", "message": msg}), 401
    variant = request.args.get('variant', '')
    if variant not in VARIANTS:
        return jsonify({"status": "error", "message": f"variant query param required, must be one of {VARIANTS}"}), 400
    try:
        limit = int(request.args.get('limit', 5))
    except ValueError:
        limit = 5
    recent = paper_trades[variant][-limit:]
    return jsonify({"status": "ok", "variant": variant, "trades": [
        {
            "trade_id": t.get("id"), "type": t.get("type"), "direction": t.get("direction"),
            "entry": t.get("entry"), "stop": t.get("stop"), "target": t.get("target"),
            "result": t.get("result"), "pnl": t.get("pnl"), "time": t.get("time"),
            "opened_at": t.get("opened_at"), "risk_pct": t.get("risk_pct"),
            "mt5_ticket": t.get("mt5_ticket"), "confidence": t.get("confidence"),
            "confluence_score": t.get("confluence_score"),
        } for t in recent
    ]})


@app.route('/admin/recent-shadow-trades', methods=['GET'])
def admin_recent_shadow_trades():
    """Read-only -- last N shadow trades (default 20, override with
    ?limit=N) for one specific variant (?variant=A/B/C, required) with
    confidence/confluence data, for analysing whether the scoring
    system is actually well-calibrated."""
    ok, msg = check_bridge_secret()
    if not ok:
        return jsonify({"status": "error", "message": msg}), 401
    variant = request.args.get('variant', '')
    if variant not in VARIANTS:
        return jsonify({"status": "error", "message": f"variant query param required, must be one of {VARIANTS}"}), 400
    try:
        limit = int(request.args.get('limit', 20))
    except ValueError:
        limit = 20
    recent = shadow_trades[variant][-limit:]
    return jsonify({"status": "ok", "variant": variant, "shadow_trades": [
        {
            "trade_id": t.get("id"), "type": t.get("type"), "direction": t.get("direction"),
            "result": t.get("result"), "pnl": t.get("pnl"), "r_multiple": t.get("r_multiple"),
            "confidence": t.get("confidence"), "confluence_score": t.get("confluence_score"),
            "rejection_reason": t.get("rejection_reason"), "session": t.get("session"),
            "opened_at": t.get("opened_at"),
        } for t in recent
    ]})


@app.route('/admin/remove-trade', methods=['POST'])
def admin_remove_trade():
    """
    Removes one trade by exact trade_id, for a specific variant -- for
    cleaning up a manually injected test alert (e.g. a curl webhook
    test) that got logged through the same pipeline as a real trade.
    If it was already closed, precisely reverses its stored pnl from
    that variant's own current_balance/total_pnl/daily_pnl using the
    exact figure apply_trade_pnl() saved on the trade record, rather
    than recomputing it.
    NOTE: does not attempt to rewind trading_days or consecutive_losses
    -- low-stakes fields for a rare manual cleanup, worth a manual
    glance afterward rather than automated here.
    """
    global current_balance, total_pnl, daily_pnl
    ok, msg = check_bridge_secret()
    if not ok:
        return jsonify({"status": "error", "message": msg}), 401
    try:
        data = request.get_json(silent=True) or {}
        variant = data.get('variant', '')
        if variant not in VARIANTS:
            return jsonify({"status": "error", "message": f"'variant' required in body, must be one of {VARIANTS}"}), 400
        trade_id = data.get('trade_id')
        trade = next((t for t in paper_trades[variant] if t.get('id') == trade_id), None)
        if not trade:
            return jsonify({"status": "error", "message": f"no trade found with id {trade_id} for variant {variant}"}), 404

        reversed_pnl = None
        if trade.get('pnl') is not None:
            reversed_pnl = trade['pnl']
            current_balance[variant] -= reversed_pnl
            total_pnl[variant] -= reversed_pnl
            daily_pnl[variant] -= reversed_pnl

        paper_trades[variant].remove(trade)
        active_trades[variant].pop(trade_id, None)
        mt5_pending_trades[variant].pop(trade_id, None)

        with open(data_path('paper_trades.json'), 'w') as f:
            json.dump(paper_trades, f, indent=2)
        save_mt5_queue()
        save_state()

        return jsonify({
            "status": "ok", "variant": variant, "removed_trade_id": trade_id,
            "reversed_pnl": reversed_pnl,
            "current_balance": round(current_balance[variant], 2),
            "total_pnl": round(total_pnl[variant], 2),
        })
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500


@app.route('/admin/restore-trade', methods=['POST'])
def admin_restore_trade():
    """
    The inverse of /admin/remove-trade -- for putting back a real,
    legitimate trade (on a specific variant's own account) whose
    signal was genuine but got removed because its recorded CLOSE was
    unreliable (e.g. the single-reading feed-gap bug), once the actual
    outcome has been independently verified some other way (e.g.
    checked directly against the real chart). Requires every field
    explicitly rather than inferring anything, so a restoration is
    always a deliberate, fully-specified action, not a guess.
    """
    global current_balance, total_pnl, daily_pnl
    ok, msg = check_bridge_secret()
    if not ok:
        return jsonify({"status": "error", "message": msg}), 401
    try:
        data = request.get_json(silent=True) or {}
        variant = data.get('variant', '')
        if variant not in VARIANTS:
            return jsonify({"status": "error", "message": f"'variant' required in body, must be one of {VARIANTS}"}), 400
        trade_id = data['trade_id']
        if any(t.get('id') == trade_id for t in paper_trades[variant]):
            return jsonify({"status": "error", "message": f"trade_id {trade_id} already exists for variant {variant}"}), 409

        result = data['result']
        if result not in ("WIN", "LOSS"):
            return jsonify({"status": "error", "message": "result must be WIN or LOSS"}), 400
        pnl = float(data['pnl'])

        trade = {
            "id": trade_id,
            "variant": variant,
            "time": data['time'],
            "opened_at": data.get('opened_at', datetime.now(timezone.utc).isoformat()),
            "type": data['type'],
            "direction": data['direction'],
            "entry": float(data['entry']),
            "stop": float(data['stop']),
            "target": float(data['target']),
            "confidence": data.get('confidence', 'MEDIUM'),
            "result": result,
            "pnl": round(pnl, 2),
            "bot_version": BOT_VERSION,
            "restored_note": "Restored after independent verification -- original close was via the single-reading feed-gap bug, fixed 4 Aug",
        }
        paper_trades[variant].append(trade)
        current_balance[variant] += pnl
        total_pnl[variant] += pnl
        daily_pnl[variant] += pnl

        with open(data_path('paper_trades.json'), 'w') as f:
            json.dump(paper_trades, f, indent=2)
        save_state()

        return jsonify({
            "status": "ok", "variant": variant, "restored_trade_id": trade_id,
            "current_balance": round(current_balance[variant], 2),
            "total_pnl": round(total_pnl[variant], 2),
        })
    except KeyError as e:
        return jsonify({"status": "error", "message": f"missing required field: {e}"}), 400
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500


@app.route('/admin/reopen-trade', methods=['POST'])
def admin_reopen_trade():
    """
    For a trade (on a specific variant's own account) incorrectly
    marked closed (e.g. the simulated monitor crediting a result off a
    bad price feed) while it's genuinely still open on the real
    account. Reverses the incorrectly-applied pnl (same exact math as
    /admin/remove-trade), resets the trade back to OPEN, and puts it
    back in that variant's active_trades so it can be picked up and
    correctly reported by the real MT5-bridge closure detection later
    -- rather than deleting it outright, which would leave no record
    at all of a trade that's genuinely still live.
    """
    global current_balance, total_pnl, daily_pnl
    ok, msg = check_bridge_secret()
    if not ok:
        return jsonify({"status": "error", "message": msg}), 401
    try:
        data = request.get_json(silent=True) or {}
        variant = data.get('variant', '')
        if variant not in VARIANTS:
            return jsonify({"status": "error", "message": f"'variant' required in body, must be one of {VARIANTS}"}), 400
        trade_id = data.get('trade_id')
        trade = next((t for t in paper_trades[variant] if t.get('id') == trade_id), None)
        if not trade:
            return jsonify({"status": "error", "message": f"no trade found with id {trade_id} for variant {variant}"}), 404
        if trade.get('result') == 'OPEN':
            return jsonify({"status": "error", "message": f"trade_id {trade_id} is already OPEN, nothing to reopen"}), 409

        reversed_pnl = None
        if trade.get('pnl') is not None:
            reversed_pnl = trade['pnl']
            current_balance[variant] -= reversed_pnl
            total_pnl[variant] -= reversed_pnl
            daily_pnl[variant] -= reversed_pnl

        trade['result'] = 'OPEN'
        trade.pop('pnl', None)
        trade.pop('r_multiple', None)
        active_trades[variant][trade_id] = trade

        with open(data_path('paper_trades.json'), 'w') as f:
            json.dump(paper_trades, f, indent=2)
        save_state()

        return jsonify({
            "status": "ok", "variant": variant, "reopened_trade_id": trade_id,
            "reversed_pnl": reversed_pnl,
            "current_balance": round(current_balance[variant], 2),
            "total_pnl": round(total_pnl[variant], 2),
        })
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# SMART ENTRY TIMER
# ============================================================
@app.route('/check-entries', methods=['GET'])
def check_entries():
    try:
        if not is_market_open():
            return jsonify({"status": "market closed — entry monitor paused"})
        if not any(active_trades[v] for v in VARIANTS):
            return jsonify({"status": "no active trades to monitor"})
        gold = get_mt5_candles_if_fresh()
        if gold is None:
            gold = yf.download('GC=F', period='1d', interval='5m', progress=False, timeout=10)
            if gold.empty:
                return jsonify({"status": "no price data"})
            gold.columns = [col[0] for col in gold.columns]
            if is_price_data_stale(gold):
                print(f"Price data stale (last candle: {gold.index[-1]}) — skipping this check-entries cycle")
                return jsonify({"status": "price data stale, skipped"})
        current_price = round(float(gold['Close'].iloc[-1]), 2)
        alerts_sent = 0
        active_counts = {}
        for variant in VARIANTS:
            active_counts[variant] = len(active_trades[variant])
            for trade_id, trade in active_trades[variant].items():
                if trade.get('result') != 'OPEN':
                    continue
                entry = trade.get('entry', 0)
                stop = trade.get('stop', 0)
                target = trade.get('target', 0)
                direction = trade.get('direction', '')
                # Prefer Claude's actual stated entry zone (stored on trades
                # logged after the entry-zone fix) over a synthetic ±0.1%
                # band around the recorded entry price — that band could
                # reference a price level that was never really the
                # intended entry in the first place.
                if trade.get('entry_zone_low') is not None and trade.get('entry_zone_high') is not None:
                    entry_zone_low = trade['entry_zone_low']
                    entry_zone_high = trade['entry_zone_high']
                else:
                    entry_zone_high = entry * 1.001
                    entry_zone_low = entry * 0.999
                in_entry_zone = entry_zone_low <= current_price <= entry_zone_high
                already_notified = trade.get('entry_notified', False)
                if in_entry_zone and not already_notified:
                    risk = abs(entry - stop)
                    reward = abs(target - entry)
                    rr = round(reward / risk, 1) if risk > 0 else 0
                    send_telegram(f"""
⏰ *[{variant}] ENTRY ZONE ALERT*
_{trade['type']} | {trade['time']}_

Price is NOW in your entry zone!

📍 Current Price: {current_price}
🎯 Entry Zone: {round(entry_zone_low, 2)} — {round(entry_zone_high, 2)}
{'▲ LONG' if direction == 'LONG' else '▼ SHORT'}

Stop Loss: {stop}
Target: {target}
R:R = 1:{rr}

_Act now or wait for next candle close confirmation_
""")
                    alerts_sent += 1
                    trade['entry_notified'] = True
        return jsonify({"status": "checked", "current_price": current_price, "active_trades": active_counts, "entry_alerts_sent": alerts_sent})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# SELF LEARNING
# ============================================================
def run_self_review(variant):
    """
    Core self-review logic for one variant. Pulled out of the
    /self-review route (16 Aug fix) so the weekly scheduled job can
    call it directly, once per variant. APScheduler invokes scheduled
    jobs outside of any Flask request context, so the old code's
    request.args.get('variant', ...) crashed every single time the
    schedule fired -- RuntimeError: Working outside of request
    context -- silently caught by run_in_context()'s own except
    clause and never surfaced anywhere but Railway's console. This
    function never touches `request` or `jsonify`, so it's safe to
    call from either the route below or the scheduler. Returns a
    plain dict; the route wrapper is responsible for jsonify-ing it.
    """
    try:
        trades = []
        try:
            with open(data_path('trade_log.csv'), 'r') as f:
                reader = csv.reader(f)
                for row in reader:
                    if len(row) >= 4:
                        trades.append({"time": row[0], "type": row[1], "price": row[2], "confidence": row[3], "analysis": row[4] if len(row) > 4 else ""})
        except FileNotFoundError:
            trades = []

        paper = []
        try:
            with open(data_path('paper_trades.json'), 'r') as f:
                loaded = json.load(f)
            paper = loaded.get(variant, []) if isinstance(loaded, dict) else []
        except FileNotFoundError:
            paper = []

        if len(trades) < 5:
            send_telegram(f"⚠️ [{variant}] Self review skipped — not enough trade data yet. Need at least 5 alerts logged.")
            return {"status": "insufficient data", "variant": variant}

        wins = [t for t in paper if t.get('result') == 'WIN']
        losses = [t for t in paper if t.get('result') == 'LOSS']
        open_trades = [t for t in paper if t.get('result') == 'OPEN']
        win_rate = len(wins) / (len(wins) + len(losses)) * 100 if (wins or losses) else 0

        type_performance = {}
        for trade in paper:
            t_type = trade.get('type', 'UNKNOWN')
            if t_type not in type_performance:
                type_performance[t_type] = {"wins": 0, "losses": 0, "total_r": 0.0, "r_count": 0}
            if trade.get('result') == 'WIN':
                type_performance[t_type]['wins'] += 1
            elif trade.get('result') == 'LOSS':
                type_performance[t_type]['losses'] += 1
            if trade.get('r_multiple') is not None:
                type_performance[t_type]['total_r'] += trade['r_multiple']
                type_performance[t_type]['r_count'] += 1

        high_conf = [t for t in paper if t.get('confidence') == 'HIGH']
        med_conf = [t for t in paper if t.get('confidence') == 'MEDIUM']
        high_wins = len([t for t in high_conf if t.get('result') == 'WIN'])
        med_wins = len([t for t in med_conf if t.get('result') == 'WIN'])

        # Killzone vs non-killzone breakdown — only meaningful for trades
        # logged after the richer-logging update, older trades won't have
        # a 'killzone' field and are simply excluded from this split.
        kz_wins = len([t for t in paper if t.get('killzone') is True and t.get('result') == 'WIN'])
        kz_losses = len([t for t in paper if t.get('killzone') is True and t.get('result') == 'LOSS'])
        non_kz_wins = len([t for t in paper if t.get('killzone') is False and t.get('result') == 'WIN'])
        non_kz_losses = len([t for t in paper if t.get('killzone') is False and t.get('result') == 'LOSS'])
        kz_wr = round(kz_wins / (kz_wins + kz_losses) * 100, 1) if (kz_wins + kz_losses) > 0 else None
        non_kz_wr = round(non_kz_wins / (non_kz_wins + non_kz_losses) * 100, 1) if (non_kz_wins + non_kz_losses) > 0 else None

        type_summary = "\n".join([
            f"- {k}: {v['wins']}W / {v['losses']}L ({round(v['wins']/(v['wins']+v['losses'])*100) if v['wins']+v['losses'] > 0 else 0}% win rate) | "
            f"Avg R: {round(v['total_r']/v['r_count'], 2) if v['r_count'] > 0 else 'n/a'}"
            for k, v in type_performance.items()
        ])

        killzone_summary = (
            f"- Inside killzone: {kz_wins}W/{kz_losses}L ({kz_wr}% win rate)\n"
            f"- Outside killzone: {non_kz_wins}W/{non_kz_losses}L ({non_kz_wr}% win rate)"
            if kz_wr is not None or non_kz_wr is not None
            else "No killzone data yet (only trades logged since the richer-logging update have this)"
        )

        # Per-trade detail now includes confluence score, killzone status,
        # DXY implication and premium/discount zone — this is what lets
        # Claude actually spot cross-factor patterns instead of only
        # alert-type win rates.
        trades_summary = "\n".join([
            f"- {t['time']}: {t['type']} | Conf:{t['confidence']} | Score:{t.get('confluence_score', '-')}/10 | "
            f"KZ:{t.get('killzone', '-')} | DXY:{t.get('dxy_implication', '-')} | Zone:{t.get('zone', '-')} | "
            f"Result:{t['result']} | R:{t.get('r_multiple', '-')}"
            for t in paper[-20:]
        ])

        prompt = f"""
You are a trading system analyst reviewing the performance of an automated XAUUSD alert system.

Total Alerts Logged: {len(trades)}
Closed Paper Trades: {len(wins) + len(losses)}
Wins: {len(wins)} | Losses: {len(losses)} | Win Rate: {win_rate:.1f}%
HIGH Confidence: {len(high_conf)} total | {high_wins} wins
MEDIUM Confidence: {len(med_conf)} total | {med_wins} wins

Performance by type:
{type_summary if type_summary else "No completed trades yet"}

Performance by killzone status:
{killzone_summary}

Recent trades (Score = Claude's confluence score out of 10, KZ = was it inside a killzone, DXY = DXY implication at entry, Zone = premium/discount zone):
{trades_summary if trades_summary else "No trades logged yet"}

IMPORTANT — small sample caveat: with only {len(wins) + len(losses)} closed trades total, most subgroup splits above (by type, by killzone, by zone) are based on somewhere between 2 and 10 trades each. At this size, a 0% or 100% win rate in any one bucket is exactly what normal variance looks like, not proof that setup does or doesn't work — 3 losses in a row happens by chance alone roughly 1 time in 8 even for a genuinely profitable setup. State the actual N for every claim you make. Do NOT recommend suspending, hard-gating, or otherwise permanently restricting a setup type based on a bucket with fewer than 15-20 resolved trades — flag it as "worth watching" instead, and say so explicitly. Before finalizing, double-check that no individual trade (by its timestamp) is cited as evidence for two different or contradictory conclusions elsewhere in the same report.

Provide:
**WHAT IS WORKING** — best performing setups, and which session/killzone/DXY/zone conditions correlate with wins
**WHAT IS NOT WORKING** — consistently losing setups, and which conditions correlate with losses
**KEY PATTERN** — single most important finding, ideally one that combines alert type with session/killzone/DXY/confluence score
**RECOMMENDED RULE CHANGES** — specific improvements, each labeled with the sample size it's based on
**UPDATED TRADING RULES** — 3-5 rules for next week
**NEXT WEEK FOCUS** — one priority

Be direct and data driven, but calibrate confidence to sample size — a pattern from 3 trades is an early hint worth tracking, not a rule worth enforcing.
"""

        message = call_claude(
            messages=[{"role": "user", "content": prompt}],
            max_tokens=3000
        )
        review = message.content[0].text

        try:
            with open(data_path(f'pending_rules_{variant}.txt'), 'w') as f:
                f.write(f"Generated: {datetime.utcnow().strftime('%Y-%m-%d %H:%M UTC')}\n\n")
                f.write(review)
        except Exception as e:
            print(f"Rules save error: {e}")

        send_telegram(f"""
🧠 *[{variant}] Gold Bot Self-Review Report*
_{datetime.utcnow().strftime('%d %b %Y — %H:%M UTC')}_

📊 Stats: {len(trades)} alerts | {len(wins)}W {len(losses)}L | {win_rate:.1f}% win rate

{review}

---
⚠️ *These rules are PENDING YOUR APPROVAL*

Approve: https://web-production-387c47.up.railway.app/approve-rules?variant={variant}
Reject: https://web-production-387c47.up.railway.app/reject-rules?variant={variant}
""")

        return {"status": "self review complete", "variant": variant, "win_rate": win_rate, "total_trades": len(trades)}

    except Exception as e:
        error_msg = f"⚠️ [{variant}] Self review error: {str(e)}"
        print(error_msg)
        send_telegram(error_msg)
        return {"status": "error", "variant": variant, "message": str(e)}


@app.route('/self-review', methods=['GET'])
def self_review():
    variant = request.args.get('variant', 'A')
    if variant not in VARIANTS:
        return jsonify({"status": "error", "message": f"variant must be one of {VARIANTS}"}), 400
    result = run_self_review(variant)
    status_code = 500 if result.get("status") == "error" else 200
    return jsonify(result), status_code


def run_scheduled_self_review():
    """
    Weekly scheduled entry point (Sunday 19:00 UTC). Runs self-review
    for all three variants in turn, not just A -- the old code
    implicitly only ever ran for A by virtue of request.args.get
    defaulting to 'A', but since this always runs outside a real HTTP
    request anyway, and the whole point of this phase is comparing A/
    B/C against each other, there's no reason the weekly automated
    review shouldn't cover all three the same way the 19:30
    counterfactual report already does. Needs no Flask app/request
    context at all -- run_self_review only touches globals, file I/O,
    Claude, and Telegram, none of which need one.
    """
    for v in VARIANTS:
        run_self_review(v)

# ============================================================
# RULE APPROVAL SYSTEM
# ============================================================
@app.route('/approve-rules', methods=['GET'])
def approve_rules():
    try:
        variant = request.args.get('variant', 'A')
        if variant not in VARIANTS:
            return jsonify({"status": "error", "message": f"variant must be one of {VARIANTS}"}), 400
        with open(data_path(f'pending_rules_{variant}.txt'), 'r') as f:
            pending = f.read()
        with open(data_path(f'learned_rules_{variant}.txt'), 'w') as f:
            f.write(f"Approved: {datetime.utcnow().strftime('%Y-%m-%d %H:%M UTC')}\n\n")
            f.write(pending)
        with open(data_path(f'pending_rules_{variant}.txt'), 'w') as f:
            f.write("No pending rules")
        send_telegram(f"✅ *[{variant}] Rule Update Approved*\n_{datetime.utcnow().strftime('%d %b %Y — %H:%M UTC')}_\n\nNew learned rules applied.")
        return jsonify({"status": "rules approved and applied", "variant": variant})
    except FileNotFoundError:
        return jsonify({"status": "no pending rules to approve"})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500


@app.route('/reject-rules', methods=['GET'])
def reject_rules():
    try:
        variant = request.args.get('variant', 'A')
        if variant not in VARIANTS:
            return jsonify({"status": "error", "message": f"variant must be one of {VARIANTS}"}), 400
        with open(data_path(f'pending_rules_{variant}.txt'), 'w') as f:
            f.write("No pending rules")
        send_telegram(f"❌ *[{variant}] Rule Update Rejected*\n_{datetime.utcnow().strftime('%d %b %Y — %H:%M UTC')}_\n\nProposed changes discarded. Live rules unchanged.")
        return jsonify({"status": "rules rejected — live rules unchanged", "variant": variant})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500


@app.route('/reset-learned-rules', methods=['GET'])
def reset_learned_rules():
    """
    Clears one variant's currently ACTIVE learned rules back to empty.
    Distinct from /reject-rules, which only discards a pending proposal
    that hasn't been approved yet -- there was previously no way to
    undo a rule set that had already been approved and applied.
    """
    try:
        variant = request.args.get('variant', 'A')
        if variant not in VARIANTS:
            return jsonify({"status": "error", "message": f"variant must be one of {VARIANTS}"}), 400
        with open(data_path(f'learned_rules_{variant}.txt'), 'w') as f:
            f.write("No learned rules yet — system will develop rules after first self-review.")
        send_telegram(f"🔄 *[{variant}] Learned Rules Reset*\n_{datetime.utcnow().strftime('%d %b %Y — %H:%M UTC')}_\n\nActive learned rules cleared back to empty.")
        return jsonify({"status": "learned rules reset to empty", "variant": variant})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500


@app.route('/view-rules', methods=['GET'])
def view_rules():
    try:
        variant = request.args.get('variant', 'A')
        if variant not in VARIANTS:
            return f"variant must be one of {VARIANTS}", 400
        active = ""
        pending = ""
        try:
            with open(data_path(f'learned_rules_{variant}.txt'), 'r') as f:
                active = f.read()
        except FileNotFoundError:
            active = "No approved rules yet"
        try:
            with open(data_path(f'pending_rules_{variant}.txt'), 'r') as f:
                pending = f.read()
        except FileNotFoundError:
            pending = "No pending rules"
        return f"""
<html>
<head><title>Gold Bot Rules — {variant}</title></head>
<body style="background:#0a0a1a;color:#eee;font-family:monospace;padding:30px;max-width:800px;margin:0 auto;">
<h1 style="color:#ffd700">🧠 Gold Bot — Rule Manager [{variant}]</h1>
<h2 style="color:#44ff88">✅ Active Rules (live)</h2>
<pre style="background:#111;padding:20px;border-radius:8px;white-space:pre-wrap;">{active}</pre>
<h2 style="color:#ffaa00">⏳ Pending Rules (awaiting approval)</h2>
<pre style="background:#111;padding:20px;border-radius:8px;white-space:pre-wrap;">{pending}</pre>
<div style="margin-top:30px;display:flex;gap:20px;">
    <a href="/approve-rules?variant={variant}" style="background:#44ff88;color:#000;padding:15px 30px;border-radius:8px;text-decoration:none;font-weight:bold;">✅ Approve Pending Rules</a>
    <a href="/reject-rules?variant={variant}" style="background:#ff4444;color:#fff;padding:15px 30px;border-radius:8px;text-decoration:none;font-weight:bold;">❌ Reject Pending Rules</a>
</div>
</body>
</html>
"""
    except Exception as e:
        return f"Error: {str(e)}", 500

# ============================================================
# BACKTESTING
# ============================================================
def interval_scale(interval):
    """
    How many `interval`-sized candles fit in one hour. Used to scale
    every candle-count parameter in the replay pipeline that's
    secretly a REAL-TIME assumption in disguise -- how many candles
    of forward room to give a trade before calling it inconclusive,
    how many trailing candles count as "this week" or "today" -- so
    switching interval doesn't silently shrink those windows to a
    fraction of their intended real-world meaning (16 Aug, added
    alongside 15m/60d support).

    Deliberately does NOT get applied to detect_raw_signals' own FVG
    (2-candle) or SWEEP (10-candle) lookback -- those define the
    actual strategy/pattern, and Pine Script's own idiomatic
    convention (ta.highest(high, N) and friends) is bar-count based,
    not time-based, so that lookback is left as a raw candle count
    unchanged across intervals rather than reinterpreted as time.
    This is a judgment call made without visibility into the actual
    live Pine Script -- flag it if that assumption is wrong.
    """
    return {"15m": 4, "30m": 2, "1h": 1, "60m": 1}.get(interval, 1)


def replay_batch_filename(interval, period):
    """
    replay_batch.json stays the filename for the original, default
    1h/2y batch -- full backward compatibility, every existing saved
    batch and habit keeps working unchanged. Any other interval/
    period gets its own file (e.g. replay_batch_15m_60d.json) so a
    differently-timeframed batch can never be silently mixed with, or
    overwrite, one built from different underlying data.
    """
    if interval == "1h" and period == "2y":
        return "replay_batch.json"
    return f"replay_batch_{interval}_{period}.json"


def simulate_backtest_trade(gold_df, signal_index, direction, entry, stop, target, max_lookahead=50):
    """
    Scans forward candle-by-candle from the signal, checking each
    candle's actual High/Low for whichever of stop/target was hit
    FIRST, chronologically — the same honest, wick-aware method
    already validated for live trading (scan_candles_for_hit),
    applied here so a backtest 'WIN' means a real trade with this
    entry/stop/target would genuinely have won, not just "price
    happened to net move further in one direction over N candles."
    Returns 'WIN', 'LOSS', or None if neither level was reached
    within the lookahead window (excluded from stats as
    inconclusive, rather than forcing a result).
    """
    end = min(signal_index + 1 + max_lookahead, len(gold_df))
    for j in range(signal_index + 1, end):
        row = gold_df.iloc[j]
        high = float(row['High'])
        low = float(row['Low'])
        if direction == 'LONG':
            hit_target = high >= target
            hit_stop = low <= stop
        else:
            hit_target = low <= target
            hit_stop = high >= stop
        if hit_stop:
            return 'LOSS'
        if hit_target:
            return 'WIN'
    return None


@app.route('/backtest', methods=['GET'])
def backtest_endpoint():
    thread = threading.Thread(target=run_backtest)
    thread.start()
    return jsonify({"status": "backtest started", "note": "runs in the background — results (including any error) will be sent to Telegram in roughly 30-90 seconds"})


@app.route('/replay-sample', methods=['GET'])
def replay_sample_endpoint():
    per_type = request.args.get('per_type', default=25, type=int)
    thread = threading.Thread(target=run_live_judgment_replay, args=(per_type,))
    thread.start()
    est_calls = per_type * 4
    return jsonify({
        "status": "replay started",
        "sample_size": est_calls,
        "note": f"makes ~{est_calls} REAL Claude API calls (real cost — see Telegram for a running estimate). This will take roughly {(est_calls * 8 + est_calls * 1.5) // 60:.0f}-{(est_calls * 15 + est_calls * 1.5) // 60:.0f} minutes, not seconds. Add ?per_type=N to change the sample size (default 25/type, 100 total)."
    })


@app.route('/replay-generate', methods=['GET'])
def replay_generate_endpoint():
    """
    Step 1 of 2 for multi-filter comparison (14 Aug). Generates real
    Claude analysis for a large historical sample ONCE and saves the
    full structured result of each -- NOT filtered by any one
    decision rule yet. Step 2 (/replay-filters) reads this saved
    batch and checks it against as many different filter definitions
    as wanted, entirely free of further API cost, since it's just
    reading data that already exists.

    This is the expensive, slow step -- the one that makes real,
    billed Claude calls. Only needs running once per desired sample
    size; re-run only to grow the sample, never to test a new filter.

    interval/period (16 Aug): optional, default to the original 1h/2y
    (matches every existing saved batch and habit exactly). The whole
    point of adding these: the live TradingView alerts are on a 15m
    chart, but every replay/backtest function here has always run on
    1h candles -- a genuinely different underlying process, not just
    a coarser view of the same one. interval=15m&period=60d builds a
    batch that actually matches what's live, capped at 60 days
    because that's yfinance's own hard limit on intraday data, not a
    choice. Saved to its own file (see replay_batch_filename) --
    never mixed with the original 1h/2y batch.
    """
    per_type = request.args.get('per_type', default=25, type=int)
    interval = request.args.get('interval', default='1h')
    period = request.args.get('period', default='2y')
    if interval not in ('15m', '30m', '1h', '60m'):
        return jsonify({"status": "error", "message": "interval must be one of 15m, 30m, 1h, 60m"}), 400
    thread = threading.Thread(target=run_replay_generate, args=(per_type, interval, period))
    thread.start()
    est_calls = per_type * 4
    return jsonify({
        "status": "generation started",
        "interval": interval,
        "period": period,
        "batch_file": replay_batch_filename(interval, period),
        "sample_size": est_calls,
        "note": f"makes ~{est_calls} REAL Claude API calls (real cost — see Telegram for a running estimate and the final real cost). Roughly {(est_calls * 8 + est_calls * 1.5) // 60:.0f}-{(est_calls * 15 + est_calls * 1.5) // 60:.0f} minutes. Once done, /replay-filters?interval={interval}&period={period} can be run against this saved batch as many times as wanted at zero further cost."
    })


def _score_trade(gold_df, signal_index, direction, entry, stop, target, risk_amount, max_lookahead=50):
    """
    Shared by run_replay_generate and run_replay_half_tp (14 Aug) --
    runs the same proven simulate_backtest_trade check and computes
    the same dollar-risk-fixed R-multiple, for whatever entry/stop/
    target is passed in. Kept as one small, pure function so both
    callers can never silently drift out of sync with each other on
    this math. max_lookahead defaults to simulate_backtest_trade's
    own default (50, correct for 1h candles = ~50 real hours) --
    callers on a different interval should pass a scaled value so a
    trade still gets roughly the same amount of real time to resolve
    before being called inconclusive.
    Returns (outcome, r_multiple) -- both None if inconclusive.
    """
    outcome = simulate_backtest_trade(gold_df, signal_index, direction, entry, stop, target, max_lookahead=max_lookahead)
    if outcome is None:
        return None, None
    stop_distance = abs(entry - stop)
    if outcome == 'WIN':
        points = abs(target - entry)
        dollar_per_point = (risk_amount / stop_distance) if stop_distance > 0 else 0
        trade_pnl = dollar_per_point * points
    else:
        trade_pnl = -risk_amount
    r_multiple = round(trade_pnl / risk_amount, 2) if risk_amount > 0 else 0
    return outcome, r_multiple


def run_replay_generate(per_type=25, interval='1h', period='2y'):
    """
    Same historical sampling and point-in-time context as
    run_live_judgment_replay, but saves the FULL structured result of
    each signal -- both raw and override-applied confidence, the
    confluence score, killzone/zone/DXY context, the derived trade
    parameters, and the single real backtest outcome for those
    parameters -- rather than checking it against one fixed filter
    inline. Every one of the 12+ filter definitions in
    run_replay_filters() only differs in WHICH signals they'd have
    accepted; none of them change the underlying entry/stop/target,
    so one saved outcome per signal is enough to evaluate all of them
    -- this is what makes step 2 free.

    interval/period (16 Aug): default to the original 1h/2y. Passing
    e.g. interval='15m', period='60d' builds a batch that actually
    matches the live TradingView alerts' own timeframe (every replay/
    backtest function here had always run on 1h candles regardless of
    what's live -- a different underlying process, not a coarser view
    of the same one). scale = interval_scale(interval) is used
    throughout below to keep every candle-count parameter that's
    secretly a real-time assumption (lookahead room before a trade
    counts as inconclusive, how many trailing candles count as "this
    week"/"today") representing the same real time regardless of
    interval. detect_raw_signals' own FVG/SWEEP lookback is
    deliberately left unscaled -- see interval_scale's docstring.
    """
    try:
        scale = interval_scale(interval)
        batch_filename = replay_batch_filename(interval, period)
        est_calls = per_type * 4
        send_telegram(f"🧪 *Replay generation started (step 1/2)*\nSampling ~{est_calls} signals spread across {period} of {interval} candles, running each through the real live Claude analysis with point-in-time historical context. This makes real API calls — expect roughly {est_calls * 8 // 60}-{est_calls * 15 // 60} minutes and a real charge to your Anthropic account. Once this finishes, /replay-filters?interval={interval}&period={period} can check the saved result against any number of filter definitions for free. Progress updates every 25 signals.")

        gold = yf.download('GC=F', period=period, interval=interval, progress=False, timeout=20)
        if gold.empty:
            send_telegram(f"⚠️ Replay generation error: no gold price data returned for interval={interval}, period={period}")
            return
        gold.columns = [col[0] for col in gold.columns]
        gold = gold.dropna()

        dxy = yf.download('DX-Y.NYB', period=period, interval=interval, progress=False, timeout=20)
        if not dxy.empty:
            if isinstance(dxy.columns, pd.MultiIndex):
                dxy.columns = [col[0] for col in dxy.columns]
            dxy = dxy.dropna(subset=['Close'])

        all_raw_signals = detect_raw_signals(gold)

        # Load any existing saved batch FIRST -- if this is a top-up
        # run (e.g. a smaller amount today, more added tomorrow), the
        # new sample must skip everything already analyzed, both to
        # avoid wasting real API cost re-analyzing the same signal
        # twice and to avoid silently double-counting it in the
        # eventual filter report.
        existing_batch = None
        existing_indices = set()
        try:
            with open(data_path(batch_filename), 'r') as f:
                existing_batch = json.load(f)
            existing_indices = {r["index"] for r in existing_batch.get("records", [])}
        except FileNotFoundError:
            pass

        sample = stratified_sample_signals(gold, per_type=per_type, exclude_indices=existing_indices)
        if existing_indices:
            send_telegram(f"📎 Found an existing saved batch with {len(existing_indices)} signals already analyzed — this run will only add genuinely new ones on top of it, nothing gets re-paid for or duplicated.")
        send_telegram(f"📊 {len(gold)} candles loaded, {len(all_raw_signals)} total signals detected, sampled {len(sample)} new signals spread across the full period. Starting analysis...")

        records = []
        errors = 0
        total_input_tokens = 0
        total_output_tokens = 0
        account = PROP_FIRM_RULES["account_size"]
        risk_amount = account * (PROP_FIRM_RULES["max_loss_per_trade_pct"] / 100)

        for n, sig in enumerate(sample):
            i = sig["index"]
            sig_type = sig["type"]
            price = sig["price"]
            high = sig["high"]
            low = sig["low"]
            timestamp = gold.index[i]

            try:
                session_name, session_desc, is_killzone = get_session_at(timestamp.hour)
                news_risk, news_msg = get_news_risk_at(timestamp.hour, timestamp.minute, timestamp.weekday())
                zone, zone_pct, zone_advice, _, _ = get_premium_discount_at(gold, i, price, lookback_candles=240 * scale)
                historical_key_levels = get_key_levels_at(gold, i, lookback_candles=240 * scale, daily_candles=24 * scale)
                if not dxy.empty:
                    dxy_direction, dxy_desc, dxy_implication = get_dxy_bias_at(dxy, timestamp)
                else:
                    dxy_direction, dxy_desc, dxy_implication = "UNKNOWN", "DXY data unavailable", "NEUTRAL"

                prior = [s for s in all_raw_signals if s["index"] < i][-5:]
                context_lines = []
                for p in prior:
                    moved = price - p["price"]
                    context_lines.append(f"- {gold.index[p['index']].strftime('%H:%M UTC')}: {p['type']} at {round(p['price'],2)} — price has since moved {abs(moved):.1f}pts {'up' if moved>0 else 'down' if moved<0 else 'flat'}")
                recent_context = "\n".join(context_lines)

                alert_data = {"type": sig_type, "price": price, "high": high, "low": low, "timeframe": interval}  # was hardcoded "15" regardless of the real interval used
                prompt = build_historical_prompt(
                    alert_data, recent_context, session_name, session_desc, is_killzone,
                    zone, zone_pct, zone_advice, news_risk, news_msg, historical_key_levels,
                    timestamp.strftime('%H:%M UTC %d %b %Y'), dxy_direction, dxy_desc
                )

                message = call_claude(
                    messages=[{"role": "user", "content": prompt}],
                    max_tokens=16000,
                    thinking={"type": "enabled", "budget_tokens": 10000},
                    retries=4,
                    base_delay=5,
                )
                analysis = None
                for block in message.content:
                    if block.type == "text":
                        analysis = block.text
                        break
                if analysis is None:
                    errors += 1
                    continue

                usage = getattr(message, 'usage', None)
                if usage:
                    total_input_tokens += getattr(usage, 'input_tokens', 0)
                    total_output_tokens += getattr(usage, 'output_tokens', 0)

                # apply_override=False -- only the confidence value differs
                # between the two modes, so one call gives everything else
                # (direction/stop/target/valid_trade/entry_zone_reached/
                # has_real_trade_params) while raw_confidence and
                # overridden_confidence are both derived from it below,
                # exactly matching the live webhook's own override rule.
                decision = derive_trade_decision(analysis, sig_type, price, apply_override=False)
                raw_confidence = decision["confidence"]
                overridden_confidence = raw_confidence
                if "FVG" in sig_type and overridden_confidence == "LOW":
                    overridden_confidence = "MEDIUM"
                if "BEARISH_SWEEP" in sig_type and overridden_confidence == "HIGH":
                    overridden_confidence = "MEDIUM"

                confluence_score = extract_confluence_score(analysis)

                outcome = None
                r_multiple = None
                if decision["has_real_trade_params"] and decision["valid_trade"]:
                    outcome, r_multiple = _score_trade(
                        gold, i, decision["direction"], price,
                        decision["stop_price"], decision["target_price"], risk_amount,
                        max_lookahead=50 * scale
                    )

                records.append({
                    "index": i,
                    "timestamp": timestamp.isoformat(),
                    "type": sig_type,
                    "direction": decision["direction"],
                    "entry": price,
                    "stop": decision["stop_price"],
                    "target": decision["target_price"],
                    "raw_confidence": raw_confidence,
                    "overridden_confidence": overridden_confidence,
                    "confluence_score": confluence_score,
                    "is_killzone": is_killzone,
                    "zone": zone,
                    "dxy_implication": dxy_implication,
                    "valid_trade": decision["valid_trade"],
                    "entry_zone_reached": decision["entry_zone_reached"],
                    "has_real_trade_params": decision["has_real_trade_params"],
                    "outcome": outcome,
                    "r_multiple": r_multiple,
                    "analysis_text": analysis,
                })

            except Exception as e:
                errors += 1
                print(f"Replay generate signal {n} error: {e}")

            time.sleep(1.5)

            if (n + 1) % 25 == 0:
                est_cost_so_far = (total_input_tokens / 1_000_000 * REPLAY_INPUT_COST_PER_M) + (total_output_tokens / 1_000_000 * REPLAY_OUTPUT_COST_PER_M)
                send_telegram(f"⏳ {n + 1}/{len(sample)} processed | est. cost so far: ${est_cost_so_far:.2f}")

        total_cost = (total_input_tokens / 1_000_000 * REPLAY_INPUT_COST_PER_M) + (total_output_tokens / 1_000_000 * REPLAY_OUTPUT_COST_PER_M)

        # Merge into any existing batch rather than overwrite it --
        # every top-up run (any day, any budget) adds to the same
        # growing, cumulative sample instead of discarding whatever
        # was already paid for.
        if existing_batch:
            combined_records = existing_batch.get("records", []) + records
            combined_cost = round(existing_batch.get("total_cost", 0) + total_cost, 2)
            combined_errors = existing_batch.get("errors", 0) + errors
        else:
            combined_records = records
            combined_cost = round(total_cost, 2)
            combined_errors = errors

        batch = {
            "generated_at": datetime.now(timezone.utc).isoformat(),
            "interval": interval,
            "period": period,
            "sample_size": len(combined_records),
            "records": combined_records,
            "errors": combined_errors,
            "total_cost": combined_cost,
        }
        with open(data_path(batch_filename), 'w') as f:
            json.dump(batch, f, indent=2)

        resolved = len([r for r in records if r["outcome"] is not None])
        total_resolved = len([r for r in combined_records if r["outcome"] is not None])
        send_telegram(f"""
✅ *Replay generation complete (step 1/2)*
Interval: {interval} | Period: {period}
This run: {len(records)} new signals analysed | {resolved} resolved | {errors} errors | real cost this run: ${total_cost:.2f}
Cumulative batch: {len(combined_records)} total signals | {total_resolved} total resolved | total real cost so far: ${combined_cost:.2f}

Saved to {batch_filename} — run /replay-filters?interval={interval}&period={period} any time to check this batch against any set of filters, at zero further cost. Run /replay-generate?interval={interval}&period={period} again any time (today, tomorrow, whenever) to add more on top, at zero risk of paying twice for the same signal.
""")
    except Exception as e:
        error_msg = f"⚠️ Replay generation error: {str(e)}"
        print(error_msg)
        send_telegram(error_msg)


# Sonnet pricing used for the live cost estimate shown in Telegram.
# Verify against current rates at https://claude.com/pricing before
# relying on this for budgeting — pricing can change.
REPLAY_INPUT_COST_PER_M = 3.00
REPLAY_OUTPUT_COST_PER_M = 15.00


def run_live_judgment_replay(per_type=25):
    """
    Samples signals spread across the full 2-year history and runs
    each one through the REAL live Claude analysis (same prompt
    structure, same model, same extended thinking budget as the live
    bot), using only point-in-time historical context so nothing from
    after each signal leaks into its own analysis. This tests the
    actual question the raw backtest can't answer: does Claude's live
    judgment (confidence, confluence, entry-zone gating) turn the flat
    ~33% raw baseline into something better — or not.

    This makes real, billed API calls. Cost is tracked and reported
    from actual token usage, not just estimated in advance.
    """
    try:
        est_calls = per_type * 4
        send_telegram(f"🧪 *Live-judgment replay started*\nSampling ~{est_calls} signals spread across 2 years, running each through the real live Claude analysis with point-in-time historical context (no lookahead). This makes real API calls — expect roughly {est_calls * 8 // 60}-{est_calls * 15 // 60} minutes and a real, small charge to your Anthropic account. Progress updates every 25 signals.")

        gold = yf.download('GC=F', period='2y', interval='1h', progress=False, timeout=20)
        if gold.empty:
            send_telegram("⚠️ Replay error: no gold price data returned")
            return
        gold.columns = [col[0] for col in gold.columns]
        gold = gold.dropna()

        dxy = yf.download('DX-Y.NYB', period='2y', interval='1h', progress=False, timeout=20)
        if not dxy.empty:
            if isinstance(dxy.columns, pd.MultiIndex):
                dxy.columns = [col[0] for col in dxy.columns]
            dxy = dxy.dropna(subset=['Close'])

        all_raw_signals = detect_raw_signals(gold)
        sample = stratified_sample_signals(gold, per_type=per_type)
        send_telegram(f"📊 {len(gold)} candles loaded, {len(all_raw_signals)} total signals detected, sampled {len(sample)} spread across the full period. Starting analysis...")

        claude_logged = []
        claude_skipped_gate = 0
        claude_inconclusive = 0
        baseline_results = []
        errors = 0
        total_input_tokens = 0
        total_output_tokens = 0
        RISK_REWARD = RISK_REWARD_TARGET
        BUFFER = BUFFER_PCT

        for n, sig in enumerate(sample):
            i = sig["index"]
            sig_type = sig["type"]
            direction = sig["direction"]
            price = sig["price"]
            high = sig["high"]
            low = sig["low"]
            timestamp = gold.index[i]

            try:
                # Point-in-time historical context only.
                session_name, session_desc, is_killzone = get_session_at(timestamp.hour)
                news_risk, news_msg = get_news_risk_at(timestamp.hour, timestamp.minute, timestamp.weekday())
                zone, zone_pct, zone_advice, _, _ = get_premium_discount_at(gold, i, price)
                historical_key_levels = get_key_levels_at(gold, i)
                if not dxy.empty:
                    dxy_direction, dxy_desc, dxy_implication = get_dxy_bias_at(dxy, timestamp)
                else:
                    dxy_direction, dxy_desc, dxy_implication = "UNKNOWN", "DXY data unavailable", "NEUTRAL"

                prior = [s for s in all_raw_signals if s["index"] < i][-5:]
                context_lines = []
                for p in prior:
                    moved = price - p["price"]
                    context_lines.append(f"- {gold.index[p['index']].strftime('%H:%M UTC')}: {p['type']} at {round(p['price'],2)} — price has since moved {abs(moved):.1f}pts {'up' if moved>0 else 'down' if moved<0 else 'flat'}")
                recent_context = "\n".join(context_lines)

                alert_data = {"type": sig_type, "price": price, "high": high, "low": low, "timeframe": "15"}
                prompt = build_historical_prompt(
                    alert_data, recent_context, session_name, session_desc, is_killzone,
                    zone, zone_pct, zone_advice, news_risk, news_msg, historical_key_levels,
                    timestamp.strftime('%H:%M UTC %d %b %Y'), dxy_direction, dxy_desc
                )

                message = call_claude(
                    messages=[{"role": "user", "content": prompt}],
                    max_tokens=16000,
                    thinking={"type": "enabled", "budget_tokens": 10000},
                    retries=4,
                    base_delay=5,
                )
                analysis = None
                for block in message.content:
                    if block.type == "text":
                        analysis = block.text
                        break
                if analysis is None:
                    errors += 1
                    continue

                usage = getattr(message, 'usage', None)
                if usage:
                    total_input_tokens += getattr(usage, 'input_tokens', 0)
                    total_output_tokens += getattr(usage, 'output_tokens', 0)

                decision = derive_trade_decision(analysis, sig_type, price)

                if decision["would_log"]:
                    outcome = simulate_backtest_trade(gold, i, decision["direction"], price, decision["stop_price"], decision["target_price"])
                    if outcome is not None:
                        # Compute the real R multiple for THIS trade using
                        # Claude's own stop/target, not the baseline's fixed
                        # 1:2 assumption — win rate alone can't tell you if
                        # a set of trades with mixed, Claude-chosen R:Rs
                        # (seen ranging 1.6:1 to 7.5:1 in real live alerts)
                        # is actually profitable.
                        account = PROP_FIRM_RULES["account_size"]
                        risk_amount = account * (PROP_FIRM_RULES["max_loss_per_trade_pct"] / 100)
                        stop_distance = abs(price - decision["stop_price"])
                        if outcome == 'WIN':
                            points = abs(decision["target_price"] - price)
                            dollar_per_point = (risk_amount / stop_distance) if stop_distance > 0 else 0
                            trade_pnl = dollar_per_point * points
                        else:
                            trade_pnl = -risk_amount
                        trade_r = round(trade_pnl / risk_amount, 2) if risk_amount > 0 else 0
                        claude_logged.append({"type": sig_type, "outcome": outcome, "confidence": decision["confidence"], "r_multiple": trade_r})
                    else:
                        claude_inconclusive += 1
                else:
                    claude_skipped_gate += 1

                # Mechanical baseline on this EXACT same signal, for a direct apples-to-apples comparison.
                buffer = price * BUFFER
                if direction == "SHORT":
                    b_stop = high + buffer
                    b_target = price - (b_stop - price) * RISK_REWARD
                else:
                    b_stop = low - buffer
                    b_target = price + (price - b_stop) * RISK_REWARD
                b_outcome = simulate_backtest_trade(gold, i, direction, price, b_stop, b_target)
                if b_outcome is not None:
                    baseline_results.append(b_outcome)

            except Exception as e:
                errors += 1
                print(f"Replay signal {n} error: {e}")

            time.sleep(1.5)  # pace requests -- reduces the chance of hitting a rate limit in the first place, especially right after another heavy run

            if (n + 1) % 25 == 0:
                est_cost_so_far = (total_input_tokens / 1_000_000 * REPLAY_INPUT_COST_PER_M) + (total_output_tokens / 1_000_000 * REPLAY_OUTPUT_COST_PER_M)
                send_telegram(f"⏳ {n + 1}/{len(sample)} processed | {len(claude_logged)} logged by Claude so far | est. cost so far: ${est_cost_so_far:.2f}")

        total_cost = (total_input_tokens / 1_000_000 * REPLAY_INPUT_COST_PER_M) + (total_output_tokens / 1_000_000 * REPLAY_OUTPUT_COST_PER_M)

        baseline_wins = len([o for o in baseline_results if o == 'WIN'])
        baseline_wr = round(baseline_wins / len(baseline_results) * 100, 1) if baseline_results else None
        # Baseline always uses the fixed 1:2 R:R, so expectancy is fully
        # determined by win rate alone: (win% * 2) - (loss% * 1).
        baseline_expectancy = round((baseline_wr / 100 * 2) - (1 - baseline_wr / 100), 2) if baseline_wr is not None else None

        claude_wins = len([c for c in claude_logged if c["outcome"] == 'WIN'])
        claude_wr = round(claude_wins / len(claude_logged) * 100, 1) if claude_logged else None
        # Claude-filtered trades use whatever R:R Claude actually proposed
        # per trade (seen ranging 1.6:1 to 7.5:1 live) -- win rate alone
        # can't tell you if this is profitable, so this averages the real
        # per-trade R multiple computed from Claude's own stop/target.
        claude_avg_r = round(sum(c.get('r_multiple', 0) for c in claude_logged) / len(claude_logged), 2) if claude_logged else None

        report = f"""
🧪 *Live-Judgment Replay Report*
_{datetime.utcnow().strftime('%d %b %Y')}_

Sampled: {len(sample)} signals spread across 2 years | Errors/skipped: {errors}
Real API cost incurred: ${total_cost:.2f} ({total_input_tokens:,} input + {total_output_tokens:,} output tokens)

*Raw baseline* (same {len(baseline_results)} resolved signals, mechanical 1:2 R:R, no filtering):
Win rate: {f"{baseline_wr}%" if baseline_wr is not None else "n/a"} | Expectancy: {f"{baseline_expectancy}R/trade" if baseline_expectancy is not None else "n/a"}

*Claude-filtered* ({len(claude_logged)} of {len(sample)} signals Claude would have actually logged, using Claude's own stop/target — {claude_skipped_gate} skipped by confidence/entry-zone gating, {claude_inconclusive} logged but never resolved stop/target within the lookahead window):
Win rate: {f"{claude_wr}%" if claude_wr is not None else "n/a — too few logged to be meaningful"} | Avg R: {f"{claude_avg_r}R/trade" if claude_avg_r is not None else "n/a"}

_This uses point-in-time historical context only — no live KEY_LEVELS, no learned rules from later performance, DXY computed only from data available at each signal's actual moment. If Claude-filtered beats the raw baseline here, that's genuine early evidence its judgment adds value — not proof, and still no substitute for real accumulating live trades, but a real signal worth taking seriously. If it doesn't beat the baseline, that's equally real and worth taking seriously in the other direction._
"""
        send_telegram(report)
    except Exception as e:
        error_msg = f"⚠️ Replay error: {str(e)}"
        print(error_msg)
        send_telegram(error_msg)


@app.route('/backtest-validate', methods=['GET'])
def backtest_validate_endpoint():
    thread = threading.Thread(target=run_backtest_validation)
    thread.start()
    return jsonify({"status": "validation started", "note": "runs in the background — results will be sent to Telegram in roughly 30-90 seconds"})


# ============================================================
# MULTI-FILTER COMPARISON (14 Aug) -- step 2 of 2
# Every function here takes one saved record from replay_batch.json
# and returns True/False: would this specific filter have taken this
# trade? None of them touch the API, the saved analysis, or each
# other -- pure, fast, free functions over data that already exists.
# Add a new filter by writing one more function in this shape and
# adding it to FILTER_DEFINITIONS below -- no need to regenerate the
# batch to test it.
# ============================================================
def _passes_base_gate(r, confidence_field):
    return (r[confidence_field] in ("HIGH", "MEDIUM") and r["valid_trade"]
            and r["entry_zone_reached"] and r["has_real_trade_params"])


def filter_A_control(r):
    """Current live system, unchanged -- override applied, no
    confluence floor. The reference point everything else is judged
    against."""
    return _passes_base_gate(r, "overridden_confidence")


def filter_B_exact(r):
    """Variant B's real, live logic exactly -- FVG/SWEEP override
    never applied, Claude's own raw confidence used as-is."""
    return _passes_base_gate(r, "raw_confidence")


def filter_C_exact(r):
    """Variant C's real, live logic exactly -- A's gate plus a hard
    6/10 minimum confluence score."""
    return filter_A_control(r) and r["confluence_score"] is not None and r["confluence_score"] >= 6


def filter_dxy_strict(r):
    """A's gate, plus reject outright if DXY actively conflicts with
    the trade direction -- neutral DXY still passes."""
    if not filter_A_control(r):
        return False
    conflict = ((r["direction"] == "LONG" and r["dxy_implication"] == "BEARISH")
                or (r["direction"] == "SHORT" and r["dxy_implication"] == "BULLISH"))
    return not conflict


def filter_confluence_only(r):
    """Ignores Claude's stated confidence label entirely -- takes
    anything with a real, valid trade and a confluence score of 7+,
    testing whether the structured score alone is more reliable than
    the subjective HIGH/MEDIUM/LOW label."""
    return (r["confluence_score"] is not None and r["confluence_score"] >= 7
            and r["valid_trade"] and r["entry_zone_reached"] and r["has_real_trade_params"])


def filter_zone_strict(r):
    """A's gate, plus textbook SMC positioning only -- longs strictly
    in discount, shorts strictly in premium, no exceptions."""
    if not filter_A_control(r):
        return False
    return ((r["direction"] == "LONG" and r["zone"] == "DISCOUNT")
            or (r["direction"] == "SHORT" and r["zone"] == "PREMIUM"))


def filter_fvg_only(r):
    """A's gate, restricted to FVG signals -- SWEEP excluded
    entirely."""
    return filter_A_control(r) and "FVG" in r["type"]


def filter_sweep_only_no_override(r):
    """B's raw-confidence gate, restricted to SWEEP signals only --
    isolates this type cleanly, given how much confusion it caused
    this week (the accidental blanket filter, the override debate)."""
    return _passes_base_gate(r, "raw_confidence") and "SWEEP" in r["type"]


def filter_stacked(r):
    """Maximally selective -- raw HIGH confidence AND confluence 7+
    AND inside a killzone AND no DXY conflict. Fewer trades by
    design; tests whether quality beats quantity."""
    if r["raw_confidence"] != "HIGH":
        return False
    if r["confluence_score"] is None or r["confluence_score"] < 7:
        return False
    if not r["is_killzone"]:
        return False
    conflict = ((r["direction"] == "LONG" and r["dxy_implication"] == "BEARISH")
                or (r["direction"] == "SHORT" and r["dxy_implication"] == "BULLISH"))
    if conflict:
        return False
    return r["valid_trade"] and r["entry_zone_reached"] and r["has_real_trade_params"]


def filter_inverse_confidence(r):
    """Deliberately EXCLUDES HIGH confidence -- MEDIUM only. Tests
    whether Claude's own "HIGH" label is actually earning its name,
    or whether MEDIUM-labeled signals perform just as well or
    better."""
    return (r["overridden_confidence"] == "MEDIUM" and r["valid_trade"]
            and r["entry_zone_reached"] and r["has_real_trade_params"])


def filter_entry_zone_only(r):
    """No confidence or confluence requirement at all -- takes
    anything with a real, valid trade where price genuinely reached
    the stated entry zone. Isolates just that one check's value on
    its own."""
    return r["valid_trade"] and r["entry_zone_reached"] and r["has_real_trade_params"]


def filter_killzone_only(r):
    """No confidence or confluence requirement -- pure timing filter,
    inside a killzone or not."""
    return r["is_killzone"] and r["valid_trade"] and r["entry_zone_reached"] and r["has_real_trade_params"]


FILTER_DEFINITIONS = [
    ("A", "A (control)", filter_A_control),
    ("B", "B-exact (no override)", filter_B_exact),
    ("C", "C-exact (confluence floor)", filter_C_exact),
    ("dxy", "DXY-strict", filter_dxy_strict),
    ("confluence", "Confluence-only (7+)", filter_confluence_only),
    ("zone", "Zone-strict", filter_zone_strict),
    ("fvg", "FVG-only", filter_fvg_only),
    ("sweep", "SWEEP-only, no override", filter_sweep_only_no_override),
    ("stacked", "Everything stacked", filter_stacked),
    ("inverse", "Inverse-confidence (MEDIUM only)", filter_inverse_confidence),
    ("entryzone", "Entry-zone-only", filter_entry_zone_only),
    ("killzone", "Killzone-only", filter_killzone_only),
]


@app.route('/replay-filters', methods=['GET'])
def replay_filters_endpoint():
    """
    Step 2 of 2. Reads the saved batch (produced by /replay-generate)
    matching the given interval/period -- defaults to the original
    1h/2y batch, exactly as before -- and reports every filter in
    FILTER_DEFINITIONS against it. No API calls, no cost, safe to run
    as many times as wanted, including right after adding a brand new
    filter function above.
    """
    interval = request.args.get('interval', default='1h')
    period = request.args.get('period', default='2y')
    batch_filename = replay_batch_filename(interval, period)
    try:
        with open(data_path(batch_filename), 'r') as f:
            batch = json.load(f)
    except FileNotFoundError:
        return jsonify({"status": "error", "message": f"No saved batch found for interval={interval}, period={period} ({batch_filename}) — run /replay-generate first."}), 404

    records = batch.get("records", [])
    resolved = [r for r in records if r["outcome"] is not None]
    if len(resolved) < 5:
        return jsonify({"status": "error", "message": f"Only {len(resolved)} resolved signals in the saved batch — not enough to report on."}), 400

    thread = threading.Thread(target=run_replay_filters_report, args=(batch,))
    thread.start()
    return jsonify({
        "status": "report started",
        "batch_generated_at": batch.get("generated_at"),
        "batch_size": len(records),
        "resolved": len(resolved),
        "note": "no API calls, no cost — results in Telegram shortly."
    })


def _aggregate_stats(taken_records):
    """
    Shared by the per-filter report loop and the new filter-
    combination report (16 Aug) -- win rate, avg R, and long/short
    split for whatever already-selected list of records is passed
    in. Returns None for an empty list rather than dividing by zero.
    """
    n = len(taken_records)
    if n == 0:
        return None
    wins = len([r for r in taken_records if r["outcome"] == "WIN"])
    wr = round(wins / n * 100, 1)
    avg_r = round(sum(r["r_multiple"] for r in taken_records) / n, 2)
    longs = len([r for r in taken_records if r["direction"] == "LONG"])
    shorts = n - longs
    return {"n": n, "wr": wr, "avg_r": avg_r, "longs": longs, "shorts": shorts}


def run_replay_filters_report(batch, records_override=None, title="Multi-Filter Comparison Report", extra_note=""):
    """
    records_override (15 Aug): lets a caller (e.g. the half-TP variant
    below) supply a modified version of the batch's records -- same
    signals, same Claude analysis, just a different derived outcome
    -- and get the exact same filter aggregation and report format,
    without duplicating this logic.
    """
    try:
        records = records_override if records_override is not None else batch.get("records", [])
        resolved = [r for r in records if r["outcome"] is not None]

        sections = []
        for key, name, filter_fn in FILTER_DEFINITIONS:
            taken = [r for r in resolved if filter_fn(r)]
            stats = _aggregate_stats(taken)
            if stats is None:
                sections.append(f"*{name}*\nNo signals in this batch matched — 0 trades")
                continue
            sections.append(
                f"*{name}*\n"
                f"n={stats['n']} | WR: {stats['wr']}% | Avg R: {stats['avg_r']} | Long/Short: {stats['longs']}/{stats['shorts']}"
            )

        report = f"""
📊 *{title}*
_{datetime.utcnow().strftime('%d %b %Y')}_

Batch: {batch.get("sample_size", len(batch.get("records", [])))} signals analysed {batch.get('generated_at', '')[:10]} | {len(resolved)} resolved | real cost when generated: ${batch.get('total_cost', 0):.2f}
{extra_note}
{chr(10).join(sections)}

_Every filter above was checked against the exact same {len(resolved)} resolved signals and the exact same Claude analysis of each — the only thing that differs between rows is which ones each filter would have accepted. Small per-filter sample sizes (especially the more selective ones) limit how much confidence to place in any single row — read this as a comparative first look, not a final verdict on any one filter._
"""
        send_telegram(report)
    except Exception as e:
        error_msg = f"⚠️ Filter report error: {str(e)}"
        print(error_msg)
        send_telegram(error_msg)


# ============================================================
# SCALED-TP VARIANT (15-16 Aug) -- same saved batch, same filters,
# stop left completely untouched, target moved to any chosen
# fraction of the way between entry and Claude's original target.
# Generalizes the original half-TP idea (which tested exactly 50%)
# after that result came back genuinely mixed, not a clean win --
# entirely free either way, since it reuses the same already-paid-for
# Claude analysis and just re-derives the outcome against a different
# level using the same real candle data.
# ============================================================
def recompute_outcomes_scaled_tp(records, gold_df, tp_fraction, max_lookahead=50):
    """
    For each record with a real outcome, moves the target to
    tp_fraction of the distance from entry to Claude's original
    target (stop unchanged) and re-runs the exact same
    simulate_backtest_trade/_score_trade logic already proven
    throughout this project, against the same real price data. Looks
    up each signal's position by its saved TIMESTAMP, not its saved
    positional index -- yfinance's "2y" window rolls forward every
    day, so a positional index from an earlier download can silently
    point at the wrong candle by the time this runs later. A signal
    whose timestamp can't be found in the freshly-downloaded data
    (should be rare) is left with outcome=None rather than guessed at.
    tp_fraction=0.5 reproduces the original half-TP test exactly;
    0.75 moves it most of the way back out toward the original;
    values above 1.0 would extend past the original target instead
    of shrinking it, if that's ever worth testing too. max_lookahead
    defaults to simulate_backtest_trade's own default (50, correct
    for 1h candles); callers re-scoring a batch built on a different
    interval should pass a scaled value -- see interval_scale.
    """
    account = PROP_FIRM_RULES["account_size"]
    risk_amount = account * (PROP_FIRM_RULES["max_loss_per_trade_pct"] / 100)
    new_records = []
    for r in records:
        new_r = dict(r)
        if r["outcome"] is None:
            new_records.append(new_r)
            continue
        try:
            ts = pd.Timestamp(r["timestamp"])
            real_index = gold_df.index.get_loc(ts)
        except KeyError:
            new_r["outcome"] = None
            new_r["r_multiple"] = None
            new_records.append(new_r)
            continue

        entry = r["entry"]
        stop = r["stop"]  # deliberately unchanged
        scaled_target = round(entry + (r["target"] - entry) * tp_fraction, 2)

        outcome, r_multiple = _score_trade(gold_df, real_index, r["direction"], entry, stop, scaled_target, risk_amount, max_lookahead=max_lookahead)
        new_r["target"] = scaled_target
        new_r["outcome"] = outcome
        new_r["r_multiple"] = r_multiple
        new_records.append(new_r)
    return new_records


def recompute_outcomes_half_tp(records, gold_df, max_lookahead=50):
    """Thin wrapper -- the original, exact-50% test. Kept unchanged
    so the existing /replay-filters-half-tp endpoint (already run for
    real, already documented) keeps working exactly as before."""
    return recompute_outcomes_scaled_tp(records, gold_df, 0.5, max_lookahead=max_lookahead)


@app.route('/replay-filters-half-tp', methods=['GET'])
def replay_filters_half_tp_endpoint():
    """
    Same saved batch, same 12 filters, target halved (stop untouched).
    Only cost is one free yfinance re-download to get real price data
    to re-run the outcome check against -- no Claude calls at all.
    """
    interval = request.args.get('interval', default='1h')
    period = request.args.get('period', default='2y')
    batch_filename = replay_batch_filename(interval, period)
    try:
        with open(data_path(batch_filename), 'r') as f:
            batch = json.load(f)
    except FileNotFoundError:
        return jsonify({"status": "error", "message": f"No saved batch found for interval={interval}, period={period} ({batch_filename}) — run /replay-generate first."}), 404

    records = batch.get("records", [])
    resolved = [r for r in records if r["outcome"] is not None]
    if len(resolved) < 5:
        return jsonify({"status": "error", "message": f"Only {len(resolved)} resolved signals in the saved batch — not enough to report on."}), 400

    thread = threading.Thread(target=run_replay_filters_half_tp_report, args=(batch,))
    thread.start()
    return jsonify({
        "status": "report started",
        "batch_generated_at": batch.get("generated_at"),
        "batch_size": len(records),
        "resolved": len(resolved),
        "note": "no API calls, no cost — one free price re-download, results in Telegram shortly."
    })


def run_replay_filters_half_tp_report(batch):
    try:
        # Batches saved since 16 Aug carry their own interval/period;
        # older ones predate that field and were always 1h/2y, so that
        # remains the correct fallback for them specifically.
        interval = batch.get("interval", "1h")
        period = batch.get("period", "2y")
        scale = interval_scale(interval)
        gold = yf.download('GC=F', period=period, interval=interval, progress=False, timeout=20)
        if gold.empty:
            send_telegram(f"⚠️ Half-TP report error: no price data returned for interval={interval}, period={period}")
            return
        gold.columns = [col[0] for col in gold.columns]
        gold = gold.dropna()

        records = batch.get("records", [])
        half_tp_records = recompute_outcomes_half_tp(records, gold, max_lookahead=50 * scale)

        original_resolved = len([r for r in records if r["outcome"] is not None])
        half_resolved = len([r for r in half_tp_records if r["outcome"] is not None])
        note = (f"\n_Interval: {interval}, period: {period}. Stop left completely unchanged — only the target moved, to exactly halfway "
                f"between entry and Claude's original target. {half_resolved} of {original_resolved} "
                f"originally-resolved signals still resolved under the new, closer target "
                f"(a signal can end up unresolved here if price never reached either level within "
                f"the same lookahead window once the target moved this much closer)._\n")

        run_replay_filters_report(
            batch,
            records_override=half_tp_records,
            title="Multi-Filter Comparison — Target Halved",
            extra_note=note,
        )
    except Exception as e:
        error_msg = f"⚠️ Half-TP report error: {str(e)}"
        print(error_msg)
        send_telegram(error_msg)


@app.route('/replay-filters-scaled-tp', methods=['GET'])
def replay_filters_scaled_tp_endpoint():
    """
    Generalized version of /replay-filters-half-tp -- any target
    distance, not just exactly half. ?fraction=0.75 moves the target
    75% of the way from entry to Claude's original target; stop
    always left completely untouched. Same free, zero-Claude-cost
    design as the half-TP variant -- reuses the same saved batch, one
    free price re-download to re-check against.
    """
    ok, msg = check_bridge_secret()
    if not ok:
        return jsonify({"status": "error", "message": msg}), 401
    try:
        fraction = float(request.args.get('fraction', 0.5))
    except ValueError:
        return jsonify({"status": "error", "message": "fraction must be a number, e.g. ?fraction=0.75"}), 400
    if not (0 < fraction <= 2.0):
        return jsonify({"status": "error", "message": "fraction should be between 0 and 2.0 (above 1.0 extends past the original target rather than shrinking it)"}), 400
    interval = request.args.get('interval', default='1h')
    period = request.args.get('period', default='2y')

    try:
        with open(data_path(replay_batch_filename(interval, period)), 'r') as f:
            batch = json.load(f)
    except FileNotFoundError:
        return jsonify({"status": "error", "message": f"No saved batch found for interval={interval}, period={period} — run /replay-generate first."}), 404

    records = batch.get("records", [])
    resolved = [r for r in records if r["outcome"] is not None]
    if len(resolved) < 5:
        return jsonify({"status": "error", "message": f"Only {len(resolved)} resolved signals in the saved batch — not enough to report on."}), 400

    thread = threading.Thread(target=run_replay_filters_scaled_tp_report, args=(batch, fraction))
    thread.start()
    return jsonify({
        "status": "report started",
        "fraction": fraction,
        "batch_generated_at": batch.get("generated_at"),
        "batch_size": len(records),
        "resolved": len(resolved),
        "note": "no API calls, no cost — one free price re-download, results in Telegram shortly."
    })


def run_replay_filters_scaled_tp_report(batch, fraction):
    try:
        interval = batch.get("interval", "1h")
        period = batch.get("period", "2y")
        scale = interval_scale(interval)
        gold = yf.download('GC=F', period=period, interval=interval, progress=False, timeout=20)
        if gold.empty:
            send_telegram(f"⚠️ Scaled-TP report error: no price data returned for interval={interval}, period={period}")
            return
        gold.columns = [col[0] for col in gold.columns]
        gold = gold.dropna()

        records = batch.get("records", [])
        scaled_records = recompute_outcomes_scaled_tp(records, gold, fraction, max_lookahead=50 * scale)

        original_resolved = len([r for r in records if r["outcome"] is not None])
        scaled_resolved = len([r for r in scaled_records if r["outcome"] is not None])
        pct_label = f"{fraction * 100:.0f}%"
        note = (f"\n_Interval: {interval}, period: {period}. Stop left completely unchanged — only the target moved, to {pct_label} of the way "
                f"from entry to Claude's original target. {scaled_resolved} of {original_resolved} "
                f"originally-resolved signals still resolved under this target "
                f"(a signal can end up unresolved here if price never reached either level within "
                f"the same lookahead window once the target moved)._\n")

        run_replay_filters_report(
            batch,
            records_override=scaled_records,
            title=f"Multi-Filter Comparison — Target at {pct_label}",
            extra_note=note,
        )
    except Exception as e:
        error_msg = f"⚠️ Scaled-TP report error: {str(e)}"
        print(error_msg)
        send_telegram(error_msg)


# ============================================================
# FILTER COMBINATION (16 Aug) -- merges multiple existing filters
# into one, two ways. AND: a signal only counts if it passes every
# selected filter (a tight, high-conviction intersection). OR: a
# signal counts if it passes any selected filter, counted once even
# if several would separately have accepted it -- no genuine
# duplication risk here, since each real signal only ever has one
# saved outcome regardless of how many filters agree on it. Entirely
# free, same saved batch, no new Claude calls.
# ============================================================
def combine_filters(resolved_records, filter_keys, mode, exclude_keys=None):
    """
    Returns (combined_records, per_filter_breakdown, exclude_breakdown).
    exclude_keys (16 Aug) -- optional "emergency brake" list: a
    record that would otherwise be included gets dropped if it ALSO
    matches ANY filter in this list, applied strictly on top of the
    normal include logic, never instead of it. exclude_breakdown
    shows how many records each individual block filter actually
    blocked, for transparency on which one is doing the real work.
    """
    lookup = {key: (name, fn) for key, name, fn in FILTER_DEFINITIONS}
    selected = [(key, lookup[key][0], lookup[key][1]) for key in filter_keys]
    excluded = [(key, lookup[key][0], lookup[key][1]) for key in (exclude_keys or [])]

    included_pool = []
    for r in resolved_records:
        passes = [fn(r) for _, _, fn in selected]
        if (mode == "and" and all(passes)) or (mode == "or" and any(passes)):
            included_pool.append(r)

    combined = []
    exclude_blocked_counts = {key: 0 for key, _, _ in excluded}
    for r in included_pool:
        blocked_by = [key for key, _, fn in excluded if fn(r)]
        if blocked_by:
            for key in blocked_by:
                exclude_blocked_counts[key] += 1
            continue
        combined.append(r)

    breakdown = {}
    for key, name, fn in selected:
        breakdown[key] = {"name": name, "count": len([r for r in combined if fn(r)])}

    exclude_breakdown = {key: {"name": name, "blocked_count": exclude_blocked_counts[key]} for key, name, _ in excluded}

    return combined, breakdown, exclude_breakdown


@app.route('/replay-combine', methods=['GET'])
def replay_combine_endpoint():
    """
    ?filters=A,B,C&mode=or  or  ?filters=A,B,C&mode=and
    Optional &exclude=C,confluence,stacked -- "emergency brake": a
    trade otherwise included gets dropped if it ALSO matches any
    filter in this list, regardless of the include mode.
    Optional &fraction=0.8 (or &tp_pct=80, same thing, different
    convention -- use one or the other, not both) -- combines
    against a scaled target instead of the original, full one.
    Free -- reads the same saved batch; fraction/tp_pct costs one
    extra free price re-download, no new Claude calls either way.
    Returns the full stats directly in this response AND sends the
    same summary to Telegram.
    """
    ok, msg = check_bridge_secret()
    if not ok:
        return jsonify({"status": "error", "message": msg}), 401

    filters_param = request.args.get('filters', '')
    mode = request.args.get('mode', '').lower()
    exclude_param = request.args.get('exclude', '')
    if not filters_param:
        return jsonify({"status": "error", "message": "filters query param required, e.g. ?filters=A,B,C"}), 400
    if mode not in ('and', 'or'):
        return jsonify({"status": "error", "message": "mode must be exactly 'and' or 'or'"}), 400

    valid_keys = {key for key, _, _ in FILTER_DEFINITIONS}
    filter_keys = [k.strip() for k in filters_param.split(',') if k.strip()]
    invalid = [k for k in filter_keys if k not in valid_keys]
    if invalid:
        return jsonify({"status": "error", "message": f"Unknown filter key(s): {', '.join(invalid)}. Valid keys: {', '.join(sorted(valid_keys))}"}), 400
    if len(filter_keys) < 2:
        return jsonify({"status": "error", "message": "Need at least 2 filters to combine -- for a single filter's own results, use /replay-filters instead"}), 400

    exclude_keys = [k.strip() for k in exclude_param.split(',') if k.strip()] if exclude_param else []
    invalid_exclude = [k for k in exclude_keys if k not in valid_keys]
    if invalid_exclude:
        return jsonify({"status": "error", "message": f"Unknown exclude filter key(s): {', '.join(invalid_exclude)}. Valid keys: {', '.join(sorted(valid_keys))}"}), 400

    fraction_param = request.args.get('fraction', None)
    tp_pct_param = request.args.get('tp_pct', None)
    if fraction_param is not None and tp_pct_param is not None:
        return jsonify({"status": "error", "message": "Use either fraction or tp_pct, not both"}), 400
    fraction = None
    try:
        if fraction_param is not None:
            fraction = float(fraction_param)
        elif tp_pct_param is not None:
            fraction = float(tp_pct_param) / 100.0
    except ValueError:
        return jsonify({"status": "error", "message": "fraction/tp_pct must be a number, e.g. &fraction=0.8 or &tp_pct=80"}), 400
    if fraction is not None and not (0 < fraction <= 2.0):
        return jsonify({"status": "error", "message": "fraction should be between 0 and 2.0 (tp_pct between 0 and 200)"}), 400
    interval = request.args.get('interval', default='1h')
    period = request.args.get('period', default='2y')

    try:
        with open(data_path(replay_batch_filename(interval, period)), 'r') as f:
            batch = json.load(f)
    except FileNotFoundError:
        return jsonify({"status": "error", "message": f"No saved batch found for interval={interval}, period={period} — run /replay-generate first."}), 404

    records = batch.get("records", [])
    resolved = [r for r in records if r["outcome"] is not None]
    if len(resolved) < 5:
        return jsonify({"status": "error", "message": f"Only {len(resolved)} resolved signals in the saved batch — not enough to report on."}), 400

    result = run_replay_combine_report(batch, filter_keys, mode, exclude_keys, fraction)
    status_code = 200 if result.get("status") == "ok" else 500
    return jsonify(result), status_code


def run_replay_combine_report(batch, filter_keys, mode, exclude_keys=None, fraction=None):
    try:
        records = batch.get("records", [])
        resolved = [r for r in records if r["outcome"] is not None]
        batch_interval = batch.get("interval", "1h")
        batch_period = batch.get("period", "2y")

        target_note = ""
        if fraction is not None:
            gold = yf.download('GC=F', period=batch_period, interval=batch_interval, progress=False, timeout=20)
            if gold.empty:
                error = f"No price data returned for the TP-scaling step (interval={batch_interval}, period={batch_period})"
                send_telegram(f"⚠️ Combine report error: {error}")
                return {"status": "error", "message": error}
            gold.columns = [col[0] for col in gold.columns]
            gold = gold.dropna()
            resolved = recompute_outcomes_scaled_tp(resolved, gold, fraction, max_lookahead=50 * interval_scale(batch_interval))
            resolved = [r for r in resolved if r["outcome"] is not None]
            pct_label = f"{fraction * 100:.0f}%"
            target_note = f"Target scaled to {pct_label} of the way from entry to the original target, stop unchanged."

        combined, breakdown, exclude_breakdown = combine_filters(resolved, filter_keys, mode, exclude_keys)
        stats = _aggregate_stats(combined)
        total_r = round(sum(r["r_multiple"] for r in combined), 2)

        if stats is None:
            n, wr, avg_r, long_short = 0, None, None, "0/0"
            result_line = "No signals passed — 0 trades"
        else:
            n, wr, avg_r = stats['n'], stats['wr'], stats['avg_r']
            long_short = f"{stats['longs']}/{stats['shorts']}"
            result_line = f"n={n} | WR: {wr}% | Avg R: {avg_r} | Total R: {total_r} | Long/Short: {long_short}"

        mode_label = "ALL selected filters must agree (tight intersection)" if mode == "and" else "ANY selected filter is enough (broader union, no duplicates)"
        breakdown_lines = "\n".join([f"  - {info['name']}: {info['count']} of these" for key, info in breakdown.items()])
        exclude_lines = ""
        if exclude_keys:
            exclude_lines = "\n*Blocked by the exclude list (would otherwise have been included):*\n" + "\n".join(
                [f"  - {info['name']}: blocked {info['blocked_count']}" for key, info in exclude_breakdown.items()]
            )

        explain = ("A trade only counts here if it passed every one of the selected filters."
                   if mode == "and" else
                   "A trade counts here if it passed at least one selected filter — counted once "
                   "even if several would separately have accepted it, since each real signal only "
                   "has one saved outcome regardless of how many filters agree on it.")
        if exclude_keys:
            explain += " Any trade also matching an exclude-list filter is dropped regardless, even if it passed the include pool."

        report = f"""
📊 *Combined Filter Report — {mode_label}*
_{datetime.utcnow().strftime('%d %b %Y')}_

Filters combined: {', '.join(filter_keys)}{f' | Excluded if also matching: {", ".join(exclude_keys)}' if exclude_keys else ''}
Batch: {len(resolved)} resolved signals total
{target_note}

*Combined result:*
{result_line}

*Per-filter breakdown (how many of the combined set each filter individually also accepts):*
{breakdown_lines}
{exclude_lines}

_{explain} Small sample sizes limit how much confidence to place in this — read as a comparative first look, not a final verdict._
"""
        send_telegram(report)

        return {
            "status": "ok",
            "n": n,
            "win_rate": wr,
            "avg_R": avg_r,
            "total_R": total_r,
            "long_short_ratio": long_short,
            "per_filter_breakdown": {key: info["count"] for key, info in breakdown.items()},
            "exclude_breakdown": {key: info["blocked_count"] for key, info in exclude_breakdown.items()} if exclude_keys else None,
            "target_scaling": target_note or None,
        }
    except Exception as e:
        error_msg = f"⚠️ Combine report error: {str(e)}"
        print(error_msg)
        send_telegram(error_msg)
        return {"status": "error", "message": str(e)}


def run_backtest_validation():
    """
    Out-of-sample check: splits the 2-year dataset chronologically into
    the first 18 months (in-sample) and the final 6 months (holdout),
    runs the identical detection + simulation on each independently,
    and checks whether specific subgroup findings from the full
    backtest — BULLISH_SWEEP underperformance, the 21-23 UTC window —
    actually hold up on data that was never used to find them. That's
    the real test for whether a subgroup result is signal or just
    noise from comparing too many slices of the same dataset.
    """
    try:
        send_telegram("🔬 *Out-of-sample validation started*\nSplitting 2 years into an 18-month training period and a 6-month holdout, then checking whether the backtest's subgroup findings hold up on data that wasn't used to find them. ~60-90 seconds.")
        gold = yf.download('GC=F', period='2y', interval='1h', progress=False, timeout=20)
        if gold.empty:
            send_telegram("⚠️ Validation error: no price data returned")
            return
        gold.columns = [col[0] for col in gold.columns]
        gold = gold.dropna()

        split_date = gold.index[0] + pd.DateOffset(months=18)
        in_sample = gold[gold.index < split_date]
        out_sample = gold[gold.index >= split_date]

        if len(in_sample) < 100 or len(out_sample) < 100:
            send_telegram("⚠️ Validation error: not enough data on one side of the split to be meaningful")
            return

        send_telegram(f"📊 Split at {split_date.strftime('%d %b %Y')} — {len(in_sample)} in-sample candles, {len(out_sample)} holdout candles. Running simulation on both...")

        in_signals, in_inconclusive = detect_and_simulate_signals(in_sample)
        out_signals, out_inconclusive = detect_and_simulate_signals(out_sample)

        in_stats = compute_backtest_stats(in_signals)
        out_stats = compute_backtest_stats(out_signals)

        if in_stats is None or out_stats is None:
            send_telegram("⚠️ Validation error: not enough resolved signals on one side of the split")
            return

        def type_wr(stats, sig_type, min_n=20):
            t = stats["type_stats"].get(sig_type)
            total = t["total"] if t else 0
            if not t or total < min_n:
                return None, total
            return round(t["wins"] / t["total"] * 100, 1), total

        def hour_window_wr(stats, hours, min_n=20):
            wins = sum(stats["hour_stats"].get(h, {"wins": 0})["wins"] for h in hours)
            total = sum(stats["hour_stats"].get(h, {"total": 0})["total"] for h in hours)
            if total < min_n:
                return None, total
            return round(wins / total * 100, 1), total

        in_overall = in_stats["overall_wr"]
        out_overall = out_stats["overall_wr"]

        in_sweep_wr, in_sweep_n = type_wr(in_stats, "BULLISH_SWEEP")
        out_sweep_wr, out_sweep_n = type_wr(out_stats, "BULLISH_SWEEP")

        in_hours_wr, in_hours_n = hour_window_wr(in_stats, [21, 22, 23])
        out_hours_wr, out_hours_n = hour_window_wr(out_stats, [21, 22, 23])

        def verdict(in_wr, out_wr, breakeven=33.3):
            if in_wr is None or out_wr is None:
                return "⚪ Not enough holdout data to test"
            if (in_wr > breakeven) == (out_wr > breakeven):
                return "✅ Held up — same side of breakeven in both periods"
            return "❌ Did NOT replicate — flipped sides of breakeven out-of-sample"

        sweep_verdict = verdict(in_sweep_wr, out_sweep_wr)
        hours_verdict = verdict(in_hours_wr, out_hours_wr)

        report = f"""
🔬 *Out-of-Sample Validation Report*
_{datetime.utcnow().strftime('%d %b %Y')}_

Training period (first 18mo): {in_stats['total_signals']} resolved signals
Holdout period (final 6mo): {out_stats['total_signals']} resolved signals

*Overall win rate:*
In-sample: {in_overall}% | Out-of-sample: {out_overall}%

*BULLISH_SWEEP win rate* (flagged as weakest setup, {in_sweep_n} in-sample signals):
In-sample: {f"{in_sweep_wr}%" if in_sweep_wr is not None else "n/a"} | Out-of-sample: {f"{out_sweep_wr}% (n={out_sweep_n})" if out_sweep_wr is not None else f"n/a (only {out_sweep_n} holdout signals)"}
Verdict: {sweep_verdict}

*21-23 UTC window win rate* (flagged as best hours, {in_hours_n} in-sample signals):
In-sample: {f"{in_hours_wr}%" if in_hours_wr is not None else "n/a"} | Out-of-sample: {f"{out_hours_wr}% (n={out_hours_n})" if out_hours_wr is not None else f"n/a (only {out_hours_n} holdout signals)"}
Verdict: {hours_verdict}

_A "held up" verdict means the pattern stayed on the same side of breakeven in both periods — supportive evidence, not proof. "Did not replicate" is a real sign the original finding was noise from comparing too many subgroups. Small holdout sample sizes limit how confident either verdict can be — treat this as a second opinion, not a final answer._
"""
        send_telegram(report)
    except Exception as e:
        error_msg = f"⚠️ Validation error: {str(e)}"
        print(error_msg)
        send_telegram(error_msg)


RISK_REWARD_TARGET = 2.0
BUFFER_PCT = 0.001


def detect_and_simulate_signals(gold_df, risk_reward=RISK_REWARD_TARGET, buffer_pct=BUFFER_PCT):
    """
    Runs the same signal detection + honest wick-aware entry/stop/
    target simulation used by the main backtest, on whatever
    DataFrame slice is passed in. Shared by both the full 2-year
    backtest and the out-of-sample validation split, so the two can
    never silently drift out of sync with each other.
    """
    signals = []
    inconclusive_count = 0
    for i in range(3, len(gold_df) - 10):
        candle = gold_df.iloc[i]
        prev2 = gold_df.iloc[i-2]
        high = float(candle['High'])
        low = float(candle['Low'])
        close = float(candle['Close'])
        buffer = close * buffer_pct

        detected = []
        if float(prev2['Low']) > high:
            detected.append(("BEARISH_FVG", "SHORT"))
        if float(prev2['High']) < low:
            detected.append(("BULLISH_FVG", "LONG"))
        lookback_high = float(gold_df.iloc[i-10:i]['High'].max())
        if high > lookback_high and close < lookback_high:
            detected.append(("BEARISH_SWEEP", "SHORT"))
        lookback_low = float(gold_df.iloc[i-10:i]['Low'].min())
        if low < lookback_low and close > lookback_low:
            detected.append(("BULLISH_SWEEP", "LONG"))

        for sig_type, direction in detected:
            entry = close
            if direction == "SHORT":
                stop = high + buffer
                risk = stop - entry
                target = entry - (risk * risk_reward)
            else:
                stop = low - buffer
                risk = entry - stop
                target = entry + (risk * risk_reward)

            outcome = simulate_backtest_trade(gold_df, i, direction, entry, stop, target)
            if outcome is None:
                inconclusive_count += 1
                continue
            signals.append({"type": sig_type, "time": str(gold_df.index[i]), "price": close, "hour": gold_df.index[i].hour, "outcome": outcome})
    return signals, inconclusive_count


def compute_backtest_stats(signals, risk_reward=RISK_REWARD_TARGET):
    """Compiles overall/type/session/hour win-rate breakdowns and
    expectancy from a list of resolved signals. Returns None if the
    list is empty, so callers can handle "not enough data" cleanly."""
    total_signals = len(signals)
    if total_signals == 0:
        return None
    wins = len([s for s in signals if s['outcome'] == 'WIN'])
    overall_wr = round(wins / total_signals * 100, 1)

    type_stats = {}
    for s in signals:
        t = s['type']
        if t not in type_stats:
            type_stats[t] = {'wins': 0, 'total': 0}
        type_stats[t]['total'] += 1
        if s['outcome'] == 'WIN':
            type_stats[t]['wins'] += 1

    session_stats = {"Asian (22-07)": {"wins": 0, "total": 0}, "London (07-12)": {"wins": 0, "total": 0}, "NY (12-17)": {"wins": 0, "total": 0}, "Other (17-22)": {"wins": 0, "total": 0}}
    for s in signals:
        hour = s['hour']
        session = "Asian (22-07)" if (hour >= 22 or hour < 7) else "London (07-12)" if 7 <= hour < 12 else "NY (12-17)" if 12 <= hour < 17 else "Other (17-22)"
        session_stats[session]['total'] += 1
        if s['outcome'] == 'WIN':
            session_stats[session]['wins'] += 1

    hour_stats = {}
    for s in signals:
        h = s['hour']
        if h not in hour_stats:
            hour_stats[h] = {'wins': 0, 'total': 0}
        hour_stats[h]['total'] += 1
        if s['outcome'] == 'WIN':
            hour_stats[h]['wins'] += 1

    expectancy_r = round((overall_wr / 100 * risk_reward) - ((1 - overall_wr / 100) * 1), 2)
    return {
        "total_signals": total_signals,
        "overall_wr": overall_wr,
        "expectancy_r": expectancy_r,
        "type_stats": type_stats,
        "session_stats": session_stats,
        "hour_stats": hour_stats,
    }


def run_backtest():
    try:
        send_telegram("🔍 *Backtesting started — pulling 2 years of XAUUSD data...*\nThis will take about 60 seconds.")
        gold = yf.download('GC=F', period='2y', interval='1h', progress=False, timeout=20)
        if gold.empty:
            send_telegram("⚠️ Backtest error: no price data returned")
            return
        gold.columns = [col[0] for col in gold.columns]
        gold = gold.dropna()
        total_candles = len(gold)
        send_telegram(f"📊 Data loaded — {total_candles} candles over 2 years. Detecting signals...")

        # Mechanical, disclosed risk setup applied identically to every
        # signal — a small buffer beyond the signal candle's high/low
        # for the stop (matching how stops are typically set live), and
        # a fixed 1:2 risk:reward target. This is a stated assumption,
        # not a discovered one — real live trades use whatever Claude
        # actually proposes per setup, which varies.
        signals, inconclusive_count = detect_and_simulate_signals(gold)

        total_signals = len(signals)
        if total_signals == 0:
            send_telegram(f"⚠️ No signals resolved within the lookahead window ({inconclusive_count} detected but inconclusive)")
            return

        send_telegram(f"✅ {total_signals} signals resolved (stop or target actually hit) | {inconclusive_count} inconclusive and excluded. Compiling statistics...")
        stats = compute_backtest_stats(signals)
        overall_wr = stats["overall_wr"]
        expectancy_r = stats["expectancy_r"]
        type_stats = stats["type_stats"]
        session_stats = stats["session_stats"]
        hour_stats = stats["hour_stats"]
        type_summary = "\n".join([f"- {k}: {v['wins']}/{v['total']} ({round(v['wins']/v['total']*100)}% win rate)" for k, v in type_stats.items()])
        session_summary = "\n".join([f"- {k}: {v['wins']}/{v['total']} ({round(v['wins']/v['total']*100) if v['total'] > 0 else 0}% win rate)" for k, v in session_stats.items()])
        hour_wr = {h: round(v['wins']/v['total']*100) for h, v in hour_stats.items() if v['total'] >= 5}
        best_hours = sorted(hour_wr.items(), key=lambda x: x[1], reverse=True)[:3]
        worst_hours = sorted(hour_wr.items(), key=lambda x: x[1])[:3]
        best_hours_str = ", ".join([f"{h}:00 UTC ({wr}%)" for h, wr in best_hours])
        worst_hours_str = ", ".join([f"{h}:00 UTC ({wr}%)" for h, wr in worst_hours])
        prompt = f"""
You are analysing 2 years of XAUUSD backtesting data. Every signal below was
simulated with a REAL entry, stop, and target (fixed 1:{RISK_REWARD_TARGET:.0f} risk:reward,
stop set just beyond the signal candle's high/low) — WIN/LOSS was determined
by scanning forward through actual subsequent candle highs/lows to see
which level was hit first. {inconclusive_count} additional signals were
detected but never resolved either level within 50 candles and were
excluded, not forced into a result.

Total candles: {total_candles} | Resolved signals: {total_signals} | Overall win rate: {overall_wr}%
Fixed risk:reward used: 1:{RISK_REWARD_TARGET:.0f}
Expectancy: {expectancy_r}R per trade (this already accounts for the win rate and R:R — a small positive number here is meaningful, a large one is a red flag worth real skepticism, not excitement)
By signal type: {type_summary}
By session: {session_summary}
Best hours: {best_hours_str}
Worst hours: {worst_hours_str}

IMPORTANT — multiple comparisons caveat: this data was cut 4 ways by signal
type, 4 ways by session, and 24 ways by hour — roughly 32 separate
comparisons against the same ~33% baseline. Individually-striking
subgroups (especially single-hour buckets) are exactly what you'd expect
to see by chance alone at this many comparisons, even with zero real
effect. Explicitly flag this when discussing "best hours" or any small
subgroup — do not present them with the same confidence as the overall
win rate, which is not subject to this problem. Signal-type and session
splits (4-way) are more trustworthy than the 24-way hour split.

Provide: OVERALL ASSESSMENT, STRONGEST SETUP, WEAKEST SETUP, BEST SESSION, SESSION TO AVOID, OPTIMAL HOURS, RECOMMENDED FILTERS.
Do NOT estimate or restate a different R:R or expected performance figure — the expectancy above is already computed from real simulation, just interpret it honestly. Be direct and data driven.
"""
        message = call_claude(
            messages=[{"role": "user", "content": prompt}],
            max_tokens=1200
        )
        analysis = message.content[0].text
        send_telegram(f"""
📈 *XAUUSD Backtest Report — 2 Years (real entry/stop/target simulation)*
_{datetime.utcnow().strftime('%d %b %Y')}_

*Data:* {total_candles} candles | {total_signals} resolved signals | {inconclusive_count} inconclusive (excluded)
*Overall Win Rate:* {overall_wr}%
*Fixed Risk:Reward:* 1:{RISK_REWARD_TARGET:.0f}
*Expectancy:* {expectancy_r}R per trade

*By Signal Type:*
{type_summary}

*By Session:*
{session_summary}

*Best Hours:* {best_hours_str}
*Worst Hours:* {worst_hours_str}

{analysis}
""")
    except Exception as e:
        error_msg = f"⚠️ Backtest error: {str(e)}"
        print(error_msg)
        send_telegram(error_msg)

# ============================================================
# DASHBOARD
# ============================================================
@app.route('/dashboard', methods=['GET'])
def dashboard():
    variant = request.args.get('variant', 'A')
    if variant not in VARIANTS:
        return f"variant must be one of {VARIANTS}", 400
    session_name, session_desc, is_killzone = get_session()
    zone, zone_pct, zone_advice = get_premium_discount((KEY_LEVELS['dealing_range_high'] + KEY_LEVELS['dealing_range_low']) / 2)
    dxy_direction, dxy_desc, dxy_implication = get_dxy_bias()
    news_risk, news_msg = check_news_risk()
    zone_color = "#ff4444" if zone == "PREMIUM" else "#44ff88"
    dxy_color = "#ff4444" if dxy_direction == "BULLISH" else "#44ff88" if dxy_direction == "BEARISH" else "#ffaa00"
    alerts_html = ""
    for a in reversed(recent_alerts[-10:]):
        alert_type = a.get('type', '')
        color = "#ff4444" if "BEARISH" in alert_type else "#44ff88"
        alerts_html += f'<div class="alert-row"><span style="color:{color}">●</span><span class="alert-time">{a.get("time", "")}</span><span class="alert-type">{alert_type}</span><span class="alert-tf">{a.get("timeframe", "")} | {a.get("price", "")}</span></div>'
    if not alerts_html:
        alerts_html = "<div class='no-data'>No alerts this session yet</div>"
    trades_html = ""
    for trade_id, trade in active_trades[variant].items():
        direction = trade.get('direction', '')
        color = "#44ff88" if direction == "LONG" else "#ff4444"
        trades_html += f'<div class="trade-row"><span style="color:{color}">{"▲" if direction == "LONG" else "▼"} {direction}</span><span>Entry: {trade.get("entry", 0):.2f}</span><span>SL: {trade.get("stop", 0):.2f}</span><span>TP: {trade.get("target", 0):.2f}</span><span class="trade-open">OPEN</span></div>'
    if not trades_html:
        trades_html = "<div class='no-data'>No active paper trades</div>"
    levels_html = "".join([f'<div class="level-row"><span class="level-label">{k.replace("_", " ").title()}</span><span class="level-value">{v}</span></div>' for k, v in KEY_LEVELS.items()])
    account = PROP_FIRM_RULES["account_size"]
    daily_used_pct = (abs(min(daily_pnl[variant], 0)) / account) * 100
    total_used_pct = (abs(min(total_pnl[variant], 0)) / account) * 100
    daily_status_color = "#ff4444" if daily_used_pct >= 80 else "#ffaa00" if daily_used_pct >= 50 else "#44ff88"
    total_status_color = "#ff4444" if total_used_pct >= 80 else "#ffaa00" if total_used_pct >= 50 else "#44ff88"
    variant_tabs = "".join([f'<a href="/dashboard?variant={v}" style="color:{"#ffd700" if v == variant else "#888"};text-decoration:none;padding:4px 12px;border:1px solid {"#ffd700" if v == variant else "#333"};border-radius:6px;margin-right:8px;">{v}</a>' for v in VARIANTS])
    return f"""<!DOCTYPE html>
<html>
<head>
    <title>Gold Bot Dashboard [{variant}]</title>
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <meta http-equiv="refresh" content="30">
    <style>
        * {{ box-sizing: border-box; margin: 0; padding: 0; }}
        body {{ background: #0a0a1a; color: #eee; font-family: 'Courier New', monospace; padding: 15px; max-width: 900px; margin: 0 auto; }}
        .header {{ text-align: center; padding: 20px 0 15px; border-bottom: 1px solid #333; margin-bottom: 20px; }}
        .header h1 {{ color: #ffd700; font-size: 24px; letter-spacing: 3px; }}
        .header .subtitle {{ color: #888; font-size: 12px; margin-top: 5px; }}
        .status-bar {{ display: flex; justify-content: space-between; align-items: center; background: #111130; border: 1px solid #ffd700; border-radius: 8px; padding: 12px 20px; margin-bottom: 20px; flex-wrap: wrap; gap: 10px; }}
        .status-item {{ display: flex; flex-direction: column; align-items: center; }}
        .status-label {{ color: #888; font-size: 10px; text-transform: uppercase; letter-spacing: 1px; }}
        .status-value {{ color: #ffd700; font-size: 14px; font-weight: bold; margin-top: 3px; }}
        .grid {{ display: grid; grid-template-columns: 1fr 1fr; gap: 15px; margin-bottom: 15px; }}
        @media (max-width: 600px) {{ .grid {{ grid-template-columns: 1fr; }} }}
        .card {{ background: #111130; border: 1px solid #333; border-radius: 8px; padding: 15px; }}
        .card h3 {{ color: #ffd700; font-size: 11px; text-transform: uppercase; letter-spacing: 2px; margin-bottom: 12px; padding-bottom: 8px; border-bottom: 1px solid #333; }}
        .full-width {{ grid-column: 1 / -1; }}
        .level-row {{ display: flex; justify-content: space-between; padding: 5px 0; border-bottom: 1px solid #1a1a3a; font-size: 13px; }}
        .level-label {{ color: #aaa; }}
        .level-value {{ color: #ffd700; font-weight: bold; }}
        .alert-row {{ display: flex; gap: 10px; padding: 6px 0; border-bottom: 1px solid #1a1a3a; font-size: 12px; align-items: center; flex-wrap: wrap; }}
        .alert-time {{ color: #888; min-width: 70px; }}
        .alert-type {{ color: #fff; flex: 1; }}
        .alert-tf {{ color: #888; font-size: 11px; }}
        .trade-row {{ display: flex; gap: 15px; padding: 8px 0; border-bottom: 1px solid #1a1a3a; font-size: 12px; align-items: center; flex-wrap: wrap; }}
        .trade-open {{ color: #ffaa00; font-weight: bold; margin-left: auto; }}
        .prop-row {{ display: flex; justify-content: space-between; align-items: center; padding: 8px 0; border-bottom: 1px solid #1a1a3a; font-size: 13px; }}
        .prop-label {{ color: #aaa; }}
        .progress-bar {{ background: #222; border-radius: 4px; height: 6px; margin-top: 4px; overflow: hidden; }}
        .progress-fill {{ height: 100%; border-radius: 4px; }}
        .no-data {{ color: #555; font-size: 12px; padding: 10px 0; text-align: center; }}
        .badge {{ display: inline-block; padding: 3px 8px; border-radius: 4px; font-size: 11px; font-weight: bold; }}
        .news-badge {{ background: #ff4444; color: #fff; }}
        .safe-badge {{ background: #1a4a2a; color: #44ff88; }}
        .footer {{ text-align: center; color: #555; font-size: 11px; margin-top: 20px; padding-top: 15px; border-top: 1px solid #333; }}
    </style>
</head>
<body>
    <div class="header">
        <h1>🥇 GOLD BOT [{variant}]</h1>
        <div class="subtitle">Auto-refreshes every 30 seconds | {datetime.utcnow().strftime('%d %b %Y %H:%M UTC')}</div>
        <div style="margin-top:10px;">{variant_tabs}</div>
    </div>
    <div class="status-bar">
        <div class="status-item"><span class="status-label">System</span><span class="status-value">🟢 LIVE</span></div>
        <div class="status-item"><span class="status-label">Session</span><span class="status-value">{session_name}</span></div>
        <div class="status-item"><span class="status-label">Killzone</span><span class="status-value">{'🎯 ACTIVE' if is_killzone else '⭕ INACTIVE'}</span></div>
        <div class="status-item"><span class="status-label">Zone</span><span class="status-value" style="color:{zone_color}">{zone} {zone_pct}%</span></div>
        <div class="status-item"><span class="status-label">DXY</span><span class="status-value" style="color:{dxy_color}">{dxy_direction}</span></div>
        <div class="status-item"><span class="status-label">Alerts Today</span><span class="status-value">{len(recent_alerts)}</span></div>
    </div>
    <div style="margin-bottom:15px;">{'<span class="badge news-badge">⚠️ ' + news_msg + '</span>' if news_risk else '<span class="badge safe-badge">✅ No major news risk</span>'}</div>
    <div class="grid">
        <div class="card"><h3>📊 Key Levels</h3>{levels_html}</div>
        <div class="card">
            <h3>🏦 Prop Firm Status [{variant}]</h3>
            <div class="prop-row"><span class="prop-label">Account Size</span><span style="color:#ffd700">${account:,.2f}</span></div>
            <div class="prop-row"><span class="prop-label">Balance</span><span style="color:#44ff88">${current_balance[variant]:,.2f}</span></div>
            <div class="prop-row"><span class="prop-label">Today P&L</span><span style="color:{'#44ff88' if daily_pnl[variant] >= 0 else '#ff4444'}">${daily_pnl[variant]:,.2f}</span></div>
            <div class="prop-row"><span class="prop-label">Total P&L</span><span style="color:{'#44ff88' if total_pnl[variant] >= 0 else '#ff4444'}">${total_pnl[variant]:,.2f}</span></div>
            <div style="margin-top:10px;">
                <div style="display:flex;justify-content:space-between;font-size:11px;color:#aaa;"><span>Daily Loss Used</span><span style="color:{daily_status_color}">{daily_used_pct:.1f}% of {PROP_FIRM_RULES['max_daily_loss_pct']}%</span></div>
                <div class="progress-bar"><div class="progress-fill" style="width:{min(daily_used_pct, 100)}%;background:{daily_status_color}"></div></div>
            </div>
            <div style="margin-top:8px;">
                <div style="display:flex;justify-content:space-between;font-size:11px;color:#aaa;"><span>Total Drawdown Used</span><span style="color:{total_status_color}">{total_used_pct:.1f}% of {PROP_FIRM_RULES['max_total_drawdown_pct']}%</span></div>
                <div class="progress-bar"><div class="progress-fill" style="width:{min(total_used_pct, 100)}%;background:{total_status_color}"></div></div>
            </div>
            <div class="prop-row" style="margin-top:10px;"><span class="prop-label">Trading Days</span><span style="color:#ffd700">{trading_days[variant]}/{PROP_FIRM_RULES['min_trading_days']}</span></div>
            <div class="prop-row"><span class="prop-label">Drawdown Protection</span><span style="color:{'#ff4444' if drawdown_protection[variant] else '#44ff88'}">{'ACTIVE' if drawdown_protection[variant] else 'OFF'}</span></div>
        </div>
        <div class="card full-width"><h3>📡 Today's Alerts ({len(recent_alerts)} this session, shared across all variants)</h3>{alerts_html}</div>
        <div class="card full-width"><h3>📈 Active Paper Trades [{variant}] ({len(active_trades[variant])} open)</h3>{trades_html}</div>
    </div>
    <div class="footer">Gold Bot v2.0 | Railway | Auto-refreshes every 30s | Last updated: {datetime.utcnow().strftime('%H:%M:%S UTC')}</div>
</body>
</html>"""

# ============================================================
# COUNTERFACTUAL REPORT — "trades you didn't take"
# Compares real trade performance against shadow-tracked rejected
# alerts, broken down by why each one was rejected. Only shadow
# trades where Claude gave real, extractable levels are included —
# an explicit "No trade" response has nothing to test and is
# correctly excluded rather than force-fit with fabricated numbers.
# ============================================================
@app.route('/counterfactual-report', methods=['GET'])
def counterfactual_report_endpoint():
    thread = threading.Thread(target=run_counterfactual_report)
    thread.start()
    return jsonify({"status": "counterfactual report started"})


def run_counterfactual_report():
    """
    The actual A/B/C comparison -- computes each variant's own taken-
    vs-rejected performance independently (same real, extractable-
    levels-only methodology as before), then shows all three side by
    side. This is the direct answer to the whole project's question:
    which filter set actually performed best.
    """
    try:
        try:
            with open(data_path('shadow_trades.json'), 'r') as f:
                all_shadow = json.load(f)
            if not isinstance(all_shadow, dict):
                all_shadow = {v: [] for v in VARIANTS}
        except FileNotFoundError:
            all_shadow = {v: [] for v in VARIANTS}

        try:
            with open(data_path('paper_trades.json'), 'r') as f:
                all_real = json.load(f)
            if not isinstance(all_real, dict):
                all_real = {v: [] for v in VARIANTS}
        except FileNotFoundError:
            all_real = {v: [] for v in VARIANTS}

        total_closed_shadow = sum(len([t for t in all_shadow.get(v, []) if t.get('result') in ('WIN', 'LOSS')]) for v in VARIANTS)
        if total_closed_shadow < 5:
            send_telegram(f"⚠️ Counterfactual report skipped — only {total_closed_shadow} resolved shadow trades across all variants so far. Need at least 5.")
            return

        variant_sections = []
        for v in VARIANTS:
            shadow = all_shadow.get(v, [])
            real_trades = all_real.get(v, [])

            closed_shadow = [t for t in shadow if t.get('result') in ('WIN', 'LOSS')]
            open_shadow_count = len([t for t in shadow if t.get('result') == 'OPEN'])
            real_closed = [t for t in real_trades if t.get('result') in ('WIN', 'LOSS')]
            real_wr = round(len([t for t in real_closed if t['result'] == 'WIN']) / len(real_closed) * 100, 1) if real_closed else None
            real_avg_r = round(sum(t.get('r_multiple', 0) for t in real_closed) / len(real_closed), 2) if real_closed else None

            if closed_shadow:
                shadow_wins = len([t for t in closed_shadow if t['result'] == 'WIN'])
                shadow_wr = round(shadow_wins / len(closed_shadow) * 100, 1)
                shadow_avg_r = round(sum(t.get('r_multiple', 0) for t in closed_shadow) / len(closed_shadow), 2)
            else:
                shadow_wr = shadow_avg_r = None

            by_reason = {}
            for t in closed_shadow:
                reason = t.get('rejection_reason', 'UNKNOWN')
                if reason not in by_reason:
                    by_reason[reason] = {"wins": 0, "losses": 0, "total_r": 0.0}
                if t['result'] == 'WIN':
                    by_reason[reason]['wins'] += 1
                else:
                    by_reason[reason]['losses'] += 1
                by_reason[reason]['total_r'] += t.get('r_multiple', 0)
            reason_summary = "\n".join([
                f"  - {reason}: {v2['wins']}W/{v2['losses']}L ({round(v2['wins']/(v2['wins']+v2['losses'])*100)}% win rate) | Avg R: {round(v2['total_r']/(v2['wins']+v2['losses']), 2)}"
                for reason, v2 in by_reason.items()
            ]) or "  (no rejected signals yet)"

            variant_sections.append(f"""
*[{v}]* Taken: {len(real_closed)} resolved | WR: {f"{real_wr}%" if real_wr is not None else "n/a"} | Avg R: {real_avg_r if real_avg_r is not None else "n/a"}
Rejected: {len(closed_shadow)} resolved ({open_shadow_count} still tracking) | WR: {f"{shadow_wr}%" if shadow_wr is not None else "n/a"} | Avg R: {shadow_avg_r if shadow_avg_r is not None else "n/a"}
{reason_summary}""")

        report = f"""
🔮 *Counterfactual Report — A/B/C Comparison*
_{datetime.utcnow().strftime('%d %b %Y')}_
{"".join(variant_sections)}

_Only alerts where Claude gave a real, extractable stop and target are tracked as "rejected" — an explicit "No trade" response has nothing to test and is correctly excluded, not force-fit with fabricated levels. Small samples per bucket limit how much confidence to place in any one row — read this as an early signal, not a verdict._
"""
        send_telegram(report)
    except Exception as e:
        error_msg = f"⚠️ Counterfactual report error: {str(e)}"
        print(error_msg)
        send_telegram(error_msg)


# ============================================================
# DAILY HEARTBEAT
# Sent once a day so silence in Telegram is never ambiguous between
# "market's quiet" and "the bot is down". This is a plain function
# (not a Flask route) so the scheduler can call it directly without
# the app-context issue that affected the other scheduled jobs.
# ============================================================
def send_heartbeat():
    try:
        ensure_daily_reset()
        sections = []
        for v in VARIANTS:
            open_trades = sum(1 for t in active_trades[v].values() if t.get('result') == 'OPEN')
            sections.append(
                f"*[{v}]* Active: {open_trades} | Balance: ${current_balance[v]:,.2f} | "
                f"Total P&L: ${total_pnl[v]:,.2f} | Days: {trading_days[v]}/{PROP_FIRM_RULES['min_trading_days']} | "
                f"Drawdown: {'ACTIVE ⚠️' if drawdown_protection[v] else 'OFF ✅'}"
            )
        msg = f"""
💓 *Daily Heartbeat — system running normally*
{datetime.now(timezone.utc).strftime('%d %b %Y — %H:%M UTC')}

Alerts today: {daily_alert_count}
{chr(10).join(sections)}
"""
        send_telegram(msg)
    except Exception as e:
        print(f"Heartbeat error: {e}")

@app.route('/heartbeat', methods=['GET'])
def heartbeat_endpoint():
    try:
        send_heartbeat()
        return jsonify({"status": "heartbeat sent"})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# HEALTH CHECK
# ============================================================
@app.route('/health', methods=['GET'])
def health():
    return jsonify({
        "status": "✅ running",
        "alerts_this_session": daily_alert_count,
        "active_trades": {v: len(active_trades[v]) for v in VARIANTS},
        "paper_trades_logged": {v: len(paper_trades[v]) for v in VARIANTS},
        "drawdown_protection": drawdown_protection,
        "time_utc": datetime.utcnow().strftime('%H:%M:%S UTC')
    })

# ============================================================
# TEST ENDPOINT
# ============================================================
@app.route('/test', methods=['GET'])
def test():
    try:
        fake_alert = {
            "type": "BEARISH_FVG_SWEEP",
            "price": "4088.50",
            "high": "4095.20",
            "low": "4082.10",
            "timeframe": "15m"
        }
        session_name, session_desc, is_killzone = get_session()
        dxy_direction, dxy_desc, dxy_implication = get_dxy_bias()
        zone, zone_pct, zone_advice = get_premium_discount(fake_alert['price'])
        news_risk, news_msg = check_news_risk()
        drawdown_active, drawdown_msg = check_drawdown_protection("A")
        analysis = analyse_with_claude(
            fake_alert, "No prior alerts — this is a test",
            session_name, session_desc, is_killzone,
            zone, zone_pct, zone_advice,
            news_risk, news_msg, drawdown_active,
            dxy_direction, dxy_desc
        )
        send_telegram(f"""
🧪 *TEST ALERT — system working correctly* ✅
📍 Price: 4088.50
📊 Zone: {zone} ({zone_pct}%)
⏰ {datetime.utcnow().strftime('%H:%M UTC')} | {session_name}
💵 DXY: {dxy_desc}

{analysis}
""")
        return jsonify({"status": "✅ test complete — check your Telegram", "session": session_name, "dxy": dxy_direction})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# START SERVER
# ============================================================
if __name__ == '__main__':
    load_state()

    def run_in_context(func):
        """
        APScheduler calls these functions directly as plain Python
        functions, not as real HTTP requests. Several of them are
        Flask routes that call jsonify(), which requires an active
        Flask application context — without it they crash with
        'RuntimeError: Working outside of application context.'
        This wrapper pushes that context manually before each
        scheduled run, and catches/logs any other exception so one
        bad run can't silently kill future runs of the same job.
        """
        def wrapper():
            try:
                with app.app_context():
                    func()
            except Exception as e:
                print(f"Scheduled job error in {func.__name__}: {e}")
        wrapper.__name__ = f"wrapped_{func.__name__}"
        return wrapper

    scheduler = BackgroundScheduler()
    scheduler.add_job(func=run_in_context(morning_briefing), trigger='cron', hour=7, minute=0)
    scheduler.add_job(func=send_heartbeat, trigger='cron', hour=8, minute=0, id='heartbeat')
    scheduler.add_job(func=ensure_daily_reset, trigger='cron', hour=0, minute=1, id='daily_pnl_reset')
    scheduler.add_job(func=run_in_context(weekly_bias_report), trigger='cron', day_of_week='sun', hour=20, minute=0)
    scheduler.add_job(func=run_in_context(monday_gap_analysis), trigger='cron', day_of_week='mon', hour=6, minute=55)
    scheduler.add_job(func=run_in_context(auto_update_levels), trigger='cron', day_of_week='sun', hour=21, minute=0)
    scheduler.add_job(func=run_scheduled_self_review, trigger='cron', day_of_week='sun', hour=19, minute=0, id='self_review')
    scheduler.add_job(func=run_counterfactual_report, trigger='cron', day_of_week='sun', hour=19, minute=30, id='counterfactual_report')
    scheduler.add_job(func=run_in_context(check_entries), trigger='interval', minutes=5, id='entry_monitor')
    scheduler.add_job(func=run_in_context(monitor_trades_endpoint), trigger='interval', minutes=2, id='trade_monitor')
    scheduler.add_job(func=check_bridge_watchdog, trigger='interval', minutes=2, id='bridge_watchdog')
    scheduler.add_job(func=run_in_context(cot_report), trigger='cron', day_of_week='fri', hour=16, minute=0, id='cot_report')
    scheduler.add_job(func=run_in_context(update_intraday), trigger='interval', minutes=30, id='intraday_updater')
    scheduler.add_job(func=lambda: save_state(), trigger='interval', minutes=10, id='state_saver')
    scheduler.start()
    atexit.register(lambda: scheduler.shutdown())
    print("🚀 Gold Alert System starting...")
    print("📡 Waiting for TradingView alerts...")
    print("🔗 Test at: http://localhost:5000/test")
    print("❤️ Health check: http://localhost:5000/health")
    port = int(os.environ.get('PORT', 5000))
    app.run(host='0.0.0.0', port=port, debug=False)