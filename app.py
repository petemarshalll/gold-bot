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
from datetime import datetime, timezone, timedelta
from dotenv import load_dotenv
from apscheduler.schedulers.background import BackgroundScheduler
import atexit
import yfinance as yf
import pandas as pd

load_dotenv()

app = Flask(__name__)

claude_client = anthropic.Anthropic(api_key=os.getenv("ANTHROPIC_API_KEY"))
TELEGRAM_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID")

# ============================================================
# MEMORY
# ============================================================
recent_alerts = []
paper_trades = []
active_trades = {}
daily_losses = 0
consecutive_losses = 0
drawdown_protection = False
scheduler = None

# ============================================================
# PROP FIRM RULES
# ============================================================
PROP_FIRM_RULES = {
    "account_size": 10000,
    "max_daily_loss_pct": 4.0,
    "max_total_drawdown_pct": 8.0,
    "min_trading_days": 4,
    "max_loss_per_trade_pct": 1.0,
}

current_balance = 10000
daily_pnl = 0
total_pnl = 0
trading_days = 0

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
        midpoint = (high + low) / 2
        percentage = ((price - low) / (high - low)) * 100
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

        # Calculate candle spread as proxy for market spread
        candle_range = high - low
        spread_pct = (candle_range / price) * 100

        # Normal gold spread on 15m candle
        # Under 0.1% = tight, good conditions
        # 0.1-0.2% = normal
        # Over 0.3% = wide, be cautious
        # Over 0.5% = very wide, avoid

        if spread_pct > 0.5:
            return True, f"⚠️ VERY WIDE spread detected ({spread_pct:.2f}%) — high slippage risk, avoid entry"
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
# DRAWDOWN PROTECTION
# ============================================================
def check_drawdown_protection():
    global consecutive_losses, drawdown_protection
    if consecutive_losses >= 3:
        drawdown_protection = True
        return True, f"⚠️ DRAWDOWN PROTECTION ACTIVE — {consecutive_losses} consecutive losses."
    drawdown_protection = False
    return False, "Normal trading mode"

# ============================================================
# DXY CORRELATION
# ============================================================
def get_dxy_bias():
    try:
        dxy = yf.download('DX-Y.NYB', period='5d', interval='1h', progress=False)
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

def get_dxy_confluence(alert_type, dxy_implication):
    is_bearish = "BEARISH" in alert_type
    is_bullish = "BULLISH" in alert_type
    if is_bearish and dxy_implication == "BEARISH":
        return "✅ STRONG CONFLUENCE — DXY rising confirms bearish gold bias", 2
    elif is_bullish and dxy_implication == "BULLISH":
        return "✅ STRONG CONFLUENCE — DXY falling confirms bullish gold bias", 2
    elif dxy_implication == "NEUTRAL":
        return "⚠️ NEUTRAL — DXY flat, no additional confluence", 0
    else:
        return "❌ CONFLICT — DXY opposes this gold signal, reduce confidence", -1

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
            response = requests.post(url, json=payload)
            print(f"Telegram sent: {response.status_code}")
            if response.status_code == 400:
                payload["parse_mode"] = "None"
                requests.post(url, json=payload)
        except Exception as e:
            print(f"Telegram error: {e}")

# ============================================================
# LOG TO CSV
# ============================================================
def log_to_csv(alert_type, price, confidence, analysis):
    try:
        with open('trade_log.csv', 'a', newline='') as f:
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
def log_paper_trade(alert_type, price, direction, entry, stop, target, confidence, alert_time):
    trade_id = f"{alert_type}_{alert_time.replace(':', '').replace(' ', '_')}"
    trade = {
        "id": trade_id,
        "time": alert_time,
        "type": alert_type,
        "price": price,
        "direction": direction,
        "entry": float(entry),
        "stop": float(stop),
        "target": float(target),
        "confidence": confidence,
        "result": "OPEN"
    }
    paper_trades.append(trade)
    active_trades[trade_id] = trade
    try:
        with open('paper_trades.json', 'w') as f:
            json.dump(paper_trades, f, indent=2)
    except Exception as e:
        print(f"Paper trade log error: {e}")
    return trade_id

# ============================================================
# MONITOR ACTIVE TRADES — SL/TP based
# ============================================================
def monitor_active_trades(current_price):
    current_price = float(current_price)
    trades_to_close = []
    for trade_id, trade in active_trades.items():
        if trade['result'] != 'OPEN':
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
            points = abs(target - entry)
            trade['result'] = 'WIN'
            send_telegram(f"""
✅ *TRADE CLOSED — TARGET HIT*
Alert: {trade['type']} | {trade['time']}
Direction: {direction}
Entry: {entry}
Target: {target} ← hit at {current_price}
Result: WIN ✅ +{points:.2f} points
""")
            trades_to_close.append(trade_id)
        elif hit_sl:
            points = abs(stop - entry)
            trade['result'] = 'LOSS'
            send_telegram(f"""
❌ *TRADE CLOSED — STOP HIT*
Alert: {trade['type']} | {trade['time']}
Direction: {direction}
Entry: {entry}
Stop: {stop} ← hit at {current_price}
Result: LOSS ❌ -{points:.2f} points
""")
            trades_to_close.append(trade_id)
    for trade_id in trades_to_close:
        del active_trades[trade_id]
    try:
        with open('paper_trades.json', 'w') as f:
            json.dump(paper_trades, f, indent=2)
    except Exception as e:
        print(f"Paper trade update error: {e}")

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
{"⚠️ DRAWDOWN PROTECTION ACTIVE — only flag if genuinely HIGH confidence" if drawdown_active else "Normal mode — standard confidence thresholds apply"}

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
Specific price zone.

**STOP LOSS**
Specific level and one sentence reason.

**TARGET**
Primary target level. Secondary if applicable.

**RISK:REWARD**
Entry / Stop / Target / RR — one line only.

**CONFIDENCE LEVEL**
LOW / MEDIUM / HIGH — one sentence max.

**AVOID IF**
2 bullet points maximum.

Keep total response under 250 words. Be extremely concise.
"""

    try:
        message = claude_client.messages.create(
            model="claude-sonnet-4-6",
            max_tokens=300,
            messages=[{"role": "user", "content": prompt}]
        )
        return message.content[0].text
    except Exception as e:
        return f"Claude analysis error: {str(e)}"

# ============================================================
# WEBHOOK
# ============================================================
@app.route('/webhook', methods=['POST'])
def webhook():
    global recent_alerts
    try:
        data = request.json
        print(f"Alert received: {data}")

        session_name, session_desc, is_killzone = get_session()
        zone, zone_pct, zone_advice = get_premium_discount(data.get('price', 0))
        news_risk, news_msg = check_news_risk()
        drawdown_active, drawdown_msg = check_drawdown_protection()
        dxy_direction, dxy_desc, dxy_implication = get_dxy_bias()
        dxy_confluence_msg, dxy_score = get_dxy_confluence(data.get('type', ''), dxy_implication)
        spread_risk, spread_msg = check_spread(
            data.get('high', 0),
            data.get('low', 0),
            data.get('price', 0)
        )

        recent_alerts.append({
            "type": data.get('type', 'Unknown'),
            "price": data.get('price', 'Unknown'),
            "timeframe": data.get('timeframe', '15m'),
            "time": datetime.utcnow().strftime('%H:%M UTC')
        })
        if len(recent_alerts) > 10:
            recent_alerts.pop(0)

        context = "\n".join([
            f"- {a['time']}: {a['type']} at {a['price']} ({a['timeframe']})"
            for a in recent_alerts[:-1]
        ])

        analysis = analyse_with_claude(
            data, context, session_name, session_desc,
            is_killzone, zone, zone_pct, zone_advice,
            news_risk, news_msg, drawdown_active,
            dxy_direction, dxy_desc
        )

        confidence = "MEDIUM"
        if "HIGH" in analysis.upper() and "CONFIDENCE" in analysis.upper():
            confidence = "HIGH"
        elif "LOW" in analysis.upper() and "CONFIDENCE" in analysis.upper():
            confidence = "LOW"

        if drawdown_active and confidence == "LOW":
            log_to_csv(data.get('type'), data.get('price'), "SKIPPED-DRAWDOWN", "Skipped due to drawdown protection")
            return jsonify({"status": "skipped", "reason": "drawdown protection active"})

        if news_risk and confidence != "HIGH":
            send_telegram(f"⚠️ *Alert suppressed — news risk active*\n{news_msg}\nAlert type: {data.get('type')} at {data.get('price')}")
            return jsonify({"status": "suppressed", "reason": "news risk"})

        alert_type = data.get('type', '')
        emoji = "🔴" if "BEARISH" in alert_type else "🟢" if "BULLISH" in alert_type else "🟡"
        killzone_badge = "🎯 KILLZONE" if is_killzone else ""

        telegram_message = f"""
{emoji} *XAUUSD — {alert_type}* {killzone_badge}
📍 Price: {data.get('price', 'N/A')}
📊 Zone: {zone} ({zone_pct}%)
⏰ {datetime.utcnow().strftime('%H:%M UTC')} | {session_name}
⚠️ News: {news_msg}
💵 DXY: {dxy_confluence_msg}
📊 Spread: {spread_msg}

{analysis}

_Timeframe: {data.get('timeframe', '15m')} | Log this trade in your journal_
"""

        send_telegram(telegram_message)
        log_to_csv(alert_type, data.get('price'), confidence, analysis)

        direction = "SHORT" if "SHORT" in analysis.upper() or "BEARISH" in alert_type else "LONG"
        entry_price = float(data.get('price', 0))
        stop_price = entry_price * 1.005 if direction == "SHORT" else entry_price * 0.995
        target_price = entry_price * 0.99 if direction == "SHORT" else entry_price * 1.01

        sl_patterns = [r'Stop(?:\s+Loss)?[:\s]+(\d+\.?\d*)', r'SL[:\s]+(\d+\.?\d*)']
        for pattern in sl_patterns:
            match = re.search(pattern, analysis, re.IGNORECASE)
            if match:
                extracted = float(match.group(1))
                if 3000 < extracted < 5500:
                    stop_price = extracted
                    break

        tp_patterns = [r'Target(?:\s+1)?[:\s]+(\d+\.?\d*)', r'TP[:\s]+(\d+\.?\d*)']
        for pattern in tp_patterns:
            match = re.search(pattern, analysis, re.IGNORECASE)
            if match:
                extracted = float(match.group(1))
                if 3000 < extracted < 5500:
                    target_price = extracted
                    break

        if confidence in ["HIGH", "MEDIUM"]:
            alert_time = datetime.utcnow().strftime('%H:%M UTC')
            log_paper_trade(alert_type, data.get('price'), direction, entry_price, stop_price, target_price, confidence, alert_time)

        monitor_active_trades(data.get('price', 0))

        return jsonify({"status": "ok"})

    except Exception as e:
        error_msg = f"⚠️ SYSTEM ERROR: {str(e)}"
        print(error_msg)
        send_telegram(error_msg)
        return jsonify({"status": "error", "message": str(e)}), 500

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
        message = claude_client.messages.create(
            model="claude-sonnet-4-6",
            max_tokens=400,
            messages=[{"role": "user", "content": prompt}]
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
        levels_text = "\n".join([f"- {k.replace('_', ' ').title()}: {v}" for k, v in KEY_LEVELS.items()])
        prompt = f"""
You are an expert XAUUSD analyst. Weekly bias report for an SMC trader.

Date: {datetime.utcnow().strftime('%A %d %B %Y')}
Key levels: {levels_text}
DXY: {dxy_desc}

Cover in under 350 words:
**WEEKLY BIAS** — bullish/bearish/neutral and why
**KEY LEVELS** — most important 3 levels this week
**SESSION FOCUS** — London or NY and why
**BEST SETUP** — specific setup type to look for
**AVOID** — what not to trade
**SUMMARY** — one sentence
"""
        message = claude_client.messages.create(
            model="claude-sonnet-4-6",
            max_tokens=400,
            messages=[{"role": "user", "content": prompt}]
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
        message = claude_client.messages.create(
            model="claude-sonnet-4-6",
            max_tokens=400,
            messages=[{"role": "user", "content": prompt}]
        )
        send_telegram(f"🌅 *XAUUSD Monday Gap Analysis — {datetime.utcnow().strftime('%d %b %Y')}*\n\n{message.content[0].text}")
        return jsonify({"status": "monday gap sent"})
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
        daily_used_pct = (abs(min(daily_pnl, 0)) / account) * 100
        total_used_pct = (abs(min(total_pnl, 0)) / account) * 100
        daily_remaining = daily_loss_limit - abs(min(daily_pnl, 0))
        total_remaining = total_drawdown_limit - abs(min(total_pnl, 0))
        daily_status = "🔴 DANGER" if daily_used_pct >= 80 else "🟡 CAUTION" if daily_used_pct >= 50 else "🟢 SAFE"
        total_status = "🔴 DANGER" if total_used_pct >= 80 else "🟡 CAUTION" if total_used_pct >= 50 else "🟢 SAFE"
        message = f"""
📊 *Prop Firm Status Report*

*Account Size:* ${account:,.2f}
*Current Balance:* ${current_balance:,.2f}
*Today's P&L:* ${daily_pnl:,.2f}
*Total P&L:* ${total_pnl:,.2f}
*Trading Days:* {trading_days}/{PROP_FIRM_RULES['min_trading_days']} minimum

*Daily Loss Limit:* {daily_status}
Used: {daily_used_pct:.1f}% | Remaining: ${daily_remaining:,.2f}

*Total Drawdown:* {total_status}
Used: {total_used_pct:.1f}% | Remaining: ${total_remaining:,.2f}

*Max Risk Per Trade:* {PROP_FIRM_RULES['max_loss_per_trade_pct']}% (${account * PROP_FIRM_RULES['max_loss_per_trade_pct'] / 100:,.2f})
"""
        send_telegram(message)
        return jsonify({"status": "ok", "daily_status": daily_status, "total_status": total_status})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# UPDATE P&L
# ============================================================
@app.route('/update-pnl', methods=['POST'])
def update_pnl():
    global daily_pnl, total_pnl, current_balance, trading_days
    try:
        data = request.json
        trade_pnl = float(data.get('pnl', 0))
        daily_pnl += trade_pnl
        total_pnl += trade_pnl
        current_balance += trade_pnl
        account = PROP_FIRM_RULES["account_size"]
        daily_loss_limit = account * (PROP_FIRM_RULES["max_daily_loss_pct"] / 100)
        total_drawdown_limit = account * (PROP_FIRM_RULES["max_total_drawdown_pct"] / 100)
        warnings = []
        if abs(min(daily_pnl, 0)) >= daily_loss_limit * 0.8:
            warnings.append(f"⚠️ DAILY LOSS WARNING — at {(abs(min(daily_pnl,0))/account)*100:.1f}% of limit")
        if abs(min(daily_pnl, 0)) >= daily_loss_limit:
            warnings.append(f"🚨 DAILY LOSS LIMIT HIT — STOP TRADING TODAY")
        if abs(min(total_pnl, 0)) >= total_drawdown_limit:
            warnings.append(f"🚨 TOTAL DRAWDOWN LIMIT HIT — ACCOUNT AT RISK")
        if warnings:
            send_telegram("\n".join(warnings))
        return jsonify({"status": "updated", "daily_pnl": daily_pnl, "total_pnl": total_pnl})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# AUTO LEVEL DETECTION
# ============================================================
@app.route('/auto-levels', methods=['GET'])
def auto_update_levels():
    global KEY_LEVELS
    try:
        gold = yf.download('GC=F', period='30d', interval='1d', progress=False)
        if gold.empty:
            send_telegram("⚠️ Auto level update failed — no data returned")
            return jsonify({"status": "error", "message": "no data"})
        gold.columns = [col[0] for col in gold.columns]
        weekly = gold.tail(5)
        today = gold.tail(1)
        recent = gold.tail(10)
        full_range = gold.tail(20)
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
# UPDATE KEY LEVELS MANUALLY
# ============================================================
@app.route('/update-levels', methods=['POST'])
def update_levels():
    global KEY_LEVELS
    try:
        new_levels = request.json
        KEY_LEVELS.update(new_levels)
        send_telegram(f"📊 *Key Levels Updated*\n" + "\n".join([f"- {k}: {v}" for k, v in KEY_LEVELS.items()]))
        return jsonify({"status": "levels updated", "levels": KEY_LEVELS})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# DASHBOARD
# ============================================================
@app.route('/dashboard', methods=['GET'])
def dashboard():
    session_name, session_desc, is_killzone = get_session()
    zone, zone_pct, zone_advice = get_premium_discount(
        (KEY_LEVELS['dealing_range_high'] + KEY_LEVELS['dealing_range_low']) / 2
    )
    dxy_direction, dxy_desc, dxy_implication = get_dxy_bias()
    news_risk, news_msg = check_news_risk()

    zone_color = "#ff4444" if zone == "PREMIUM" else "#44ff88"
    dxy_color = "#ff4444" if dxy_direction == "BULLISH" else "#44ff88" if dxy_direction == "BEARISH" else "#ffaa00"
    killzone_badge = "🎯 KILLZONE ACTIVE" if is_killzone else ""
    news_badge = f"⚠️ {news_msg}" if news_risk else "✅ No major news risk"

    alerts_html = ""
    for a in reversed(recent_alerts[-10:]):
        alert_type = a.get('type', '')
        color = "#ff4444" if "BEARISH" in alert_type else "#44ff88"
        alerts_html += f"""
        <div class="alert-row">
            <span style="color:{color}">●</span>
            <span class="alert-time">{a.get('time', '')}</span>
            <span class="alert-type">{alert_type}</span>
            <span class="alert-tf">{a.get('timeframe', '')} | {a.get('price', '')}</span>
        </div>
        """
    if not alerts_html:
        alerts_html = "<div class='no-data'>No alerts this session yet</div>"

    trades_html = ""
    for trade_id, trade in active_trades.items():
        direction = trade.get('direction', '')
        color = "#44ff88" if direction == "LONG" else "#ff4444"
        trades_html += f"""
        <div class="trade-row">
            <span style="color:{color}">{'▲' if direction == 'LONG' else '▼'} {direction}</span>
            <span>Entry: {trade.get('entry', 0):.2f}</span>
            <span>SL: {trade.get('stop', 0):.2f}</span>
            <span>TP: {trade.get('target', 0):.2f}</span>
            <span class="trade-open">OPEN</span>
        </div>
        """
    if not trades_html:
        trades_html = "<div class='no-data'>No active paper trades</div>"

    levels_html = ""
    for k, v in KEY_LEVELS.items():
        label = k.replace('_', ' ').title()
        levels_html += f"""
        <div class="level-row">
            <span class="level-label">{label}</span>
            <span class="level-value">{v}</span>
        </div>
        """

    account = PROP_FIRM_RULES["account_size"]
    daily_loss_limit = account * (PROP_FIRM_RULES["max_daily_loss_pct"] / 100)
    total_drawdown_limit = account * (PROP_FIRM_RULES["max_total_drawdown_pct"] / 100)
    daily_used_pct = (abs(min(daily_pnl, 0)) / account) * 100
    total_used_pct = (abs(min(total_pnl, 0)) / account) * 100
    daily_status_color = "#ff4444" if daily_used_pct >= 80 else "#ffaa00" if daily_used_pct >= 50 else "#44ff88"
    total_status_color = "#ff4444" if total_used_pct >= 80 else "#ffaa00" if total_used_pct >= 50 else "#44ff88"

    html = f"""
<!DOCTYPE html>
<html>
<head>
    <title>Gold Bot Dashboard</title>
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <meta http-equiv="refresh" content="30">
    <style>
        * {{ box-sizing: border-box; margin: 0; padding: 0; }}
        body {{
            background: #0a0a1a;
            color: #eee;
            font-family: 'Courier New', monospace;
            padding: 15px;
            max-width: 900px;
            margin: 0 auto;
        }}
        .header {{
            text-align: center;
            padding: 20px 0 15px;
            border-bottom: 1px solid #333;
            margin-bottom: 20px;
        }}
        .header h1 {{
            color: #ffd700;
            font-size: 24px;
            letter-spacing: 3px;
        }}
        .header .subtitle {{
            color: #888;
            font-size: 12px;
            margin-top: 5px;
        }}
        .status-bar {{
            display: flex;
            justify-content: space-between;
            align-items: center;
            background: #111130;
            border: 1px solid #ffd700;
            border-radius: 8px;
            padding: 12px 20px;
            margin-bottom: 20px;
            flex-wrap: wrap;
            gap: 10px;
        }}
        .status-item {{
            display: flex;
            flex-direction: column;
            align-items: center;
        }}
        .status-label {{
            color: #888;
            font-size: 10px;
            text-transform: uppercase;
            letter-spacing: 1px;
        }}
        .status-value {{
            color: #ffd700;
            font-size: 14px;
            font-weight: bold;
            margin-top: 3px;
        }}
        .grid {{
            display: grid;
            grid-template-columns: 1fr 1fr;
            gap: 15px;
            margin-bottom: 15px;
        }}
        @media (max-width: 600px) {{
            .grid {{ grid-template-columns: 1fr; }}
        }}
        .card {{
            background: #111130;
            border: 1px solid #333;
            border-radius: 8px;
            padding: 15px;
        }}
        .card h3 {{
            color: #ffd700;
            font-size: 11px;
            text-transform: uppercase;
            letter-spacing: 2px;
            margin-bottom: 12px;
            padding-bottom: 8px;
            border-bottom: 1px solid #333;
        }}
        .full-width {{
            grid-column: 1 / -1;
        }}
        .level-row {{
            display: flex;
            justify-content: space-between;
            padding: 5px 0;
            border-bottom: 1px solid #1a1a3a;
            font-size: 13px;
        }}
        .level-label {{ color: #aaa; }}
        .level-value {{ color: #ffd700; font-weight: bold; }}
        .alert-row {{
            display: flex;
            gap: 10px;
            padding: 6px 0;
            border-bottom: 1px solid #1a1a3a;
            font-size: 12px;
            align-items: center;
            flex-wrap: wrap;
        }}
        .alert-time {{ color: #888; min-width: 70px; }}
        .alert-type {{ color: #fff; flex: 1; }}
        .alert-tf {{ color: #888; font-size: 11px; }}
        .trade-row {{
            display: flex;
            gap: 15px;
            padding: 8px 0;
            border-bottom: 1px solid #1a1a3a;
            font-size: 12px;
            align-items: center;
            flex-wrap: wrap;
        }}
        .trade-open {{
            color: #ffaa00;
            font-weight: bold;
            margin-left: auto;
        }}
        .prop-row {{
            display: flex;
            justify-content: space-between;
            align-items: center;
            padding: 8px 0;
            border-bottom: 1px solid #1a1a3a;
            font-size: 13px;
        }}
        .prop-label {{ color: #aaa; }}
        .progress-bar {{
            background: #222;
            border-radius: 4px;
            height: 6px;
            margin-top: 4px;
            overflow: hidden;
        }}
        .progress-fill {{
            height: 100%;
            border-radius: 4px;
            transition: width 0.3s;
        }}
        .no-data {{
            color: #555;
            font-size: 12px;
            padding: 10px 0;
            text-align: center;
        }}
        .badge {{
            display: inline-block;
            padding: 3px 8px;
            border-radius: 4px;
            font-size: 11px;
            font-weight: bold;
        }}
        .killzone-badge {{
            background: #ffd700;
            color: #000;
        }}
        .news-badge {{
            background: #ff4444;
            color: #fff;
        }}
        .safe-badge {{
            background: #1a4a2a;
            color: #44ff88;
        }}
        .footer {{
            text-align: center;
            color: #555;
            font-size: 11px;
            margin-top: 20px;
            padding-top: 15px;
            border-top: 1px solid #333;
        }}
    </style>
</head>
<body>
    <div class="header">
        <h1>🥇 GOLD BOT</h1>
        <div class="subtitle">Auto-refreshes every 30 seconds | {datetime.utcnow().strftime('%d %b %Y %H:%M UTC')}</div>
    </div>

    <div class="status-bar">
        <div class="status-item">
            <span class="status-label">System</span>
            <span class="status-value">🟢 LIVE</span>
        </div>
        <div class="status-item">
            <span class="status-label">Session</span>
            <span class="status-value">{session_name}</span>
        </div>
        <div class="status-item">
            <span class="status-label">Killzone</span>
            <span class="status-value">{'🎯 ACTIVE' if is_killzone else '⭕ INACTIVE'}</span>
        </div>
        <div class="status-item">
            <span class="status-label">Zone</span>
            <span class="status-value" style="color:{zone_color}">{zone} {zone_pct}%</span>
        </div>
        <div class="status-item">
            <span class="status-label">DXY</span>
            <span class="status-value" style="color:{dxy_color}">{dxy_direction}</span>
        </div>
        <div class="status-item">
            <span class="status-label">Alerts Today</span>
            <span class="status-value">{len(recent_alerts)}</span>
        </div>
    </div>

    <div style="margin-bottom:15px;">
        {'<span class="badge news-badge">⚠️ ' + news_msg + '</span>' if news_risk else '<span class="badge safe-badge">✅ No major news risk</span>'}
    </div>

    <div class="grid">
        <div class="card">
            <h3>📊 Key Levels</h3>
            {levels_html}
        </div>

        <div class="card">
            <h3>🏦 Prop Firm Status</h3>
            <div class="prop-row">
                <span class="prop-label">Account Size</span>
                <span style="color:#ffd700">${account:,.2f}</span>
            </div>
            <div class="prop-row">
                <span class="prop-label">Balance</span>
                <span style="color:#44ff88">${current_balance:,.2f}</span>
            </div>
            <div class="prop-row">
                <span class="prop-label">Today P&L</span>
                <span style="color:{'#44ff88' if daily_pnl >= 0 else '#ff4444'}">${daily_pnl:,.2f}</span>
            </div>
            <div class="prop-row">
                <span class="prop-label">Total P&L</span>
                <span style="color:{'#44ff88' if total_pnl >= 0 else '#ff4444'}">${total_pnl:,.2f}</span>
            </div>
            <div style="margin-top:10px;">
                <div style="display:flex;justify-content:space-between;font-size:11px;color:#aaa;">
                    <span>Daily Loss Used</span>
                    <span style="color:{daily_status_color}">{daily_used_pct:.1f}% of {PROP_FIRM_RULES['max_daily_loss_pct']}%</span>
                </div>
                <div class="progress-bar">
                    <div class="progress-fill" style="width:{min(daily_used_pct, 100)}%;background:{daily_status_color}"></div>
                </div>
            </div>
            <div style="margin-top:8px;">
                <div style="display:flex;justify-content:space-between;font-size:11px;color:#aaa;">
                    <span>Total Drawdown Used</span>
                    <span style="color:{total_status_color}">{total_used_pct:.1f}% of {PROP_FIRM_RULES['max_total_drawdown_pct']}%</span>
                </div>
                <div class="progress-bar">
                    <div class="progress-fill" style="width:{min(total_used_pct, 100)}%;background:{total_status_color}"></div>
                </div>
            </div>
            <div class="prop-row" style="margin-top:10px;">
                <span class="prop-label">Trading Days</span>
                <span style="color:#ffd700">{trading_days}/{PROP_FIRM_RULES['min_trading_days']}</span>
            </div>
            <div class="prop-row">
                <span class="prop-label">Drawdown Protection</span>
                <span style="color:{'#ff4444' if drawdown_protection else '#44ff88'}">{'ACTIVE' if drawdown_protection else 'OFF'}</span>
            </div>
        </div>

        <div class="card full-width">
            <h3>📡 Today's Alerts ({len(recent_alerts)} this session)</h3>
            {alerts_html}
        </div>

        <div class="card full-width">
            <h3>📈 Active Paper Trades ({len(active_trades)} open)</h3>
            {trades_html}
        </div>
    </div>

    <div class="footer">
        Gold Bot v2.0 | Railway | Auto-refreshes every 30s | Last updated: {datetime.utcnow().strftime('%H:%M:%S UTC')}
    </div>
</body>
</html>
"""
    return html

# ============================================================
# SELF LEARNING — Claude analyses its own performance
# ============================================================
@app.route('/self-review', methods=['GET'])
def self_review():
    try:
        # Load trade log
        trades = []
        try:
            with open('trade_log.csv', 'r') as f:
                reader = csv.reader(f)
                for row in reader:
                    if len(row) >= 4:
                        trades.append({
                            "time": row[0],
                            "type": row[1],
                            "price": row[2],
                            "confidence": row[3],
                            "analysis": row[4] if len(row) > 4 else ""
                        })
        except FileNotFoundError:
            trades = []

        # Load paper trades
        paper = []
        try:
            with open('paper_trades.json', 'r') as f:
                paper = json.load(f)
        except FileNotFoundError:
            paper = []

        if len(trades) < 5:
            send_telegram("⚠️ Self review skipped — not enough trade data yet. Need at least 5 alerts logged.")
            return jsonify({"status": "insufficient data"})

        # Build performance summary
        wins = [t for t in paper if t.get('result') == 'WIN']
        losses = [t for t in paper if t.get('result') == 'LOSS']
        open_trades = [t for t in paper if t.get('result') == 'OPEN']

        win_rate = len(wins) / (len(wins) + len(losses)) * 100 if (wins or losses) else 0

        # Analyse by type
        type_performance = {}
        for trade in paper:
            t_type = trade.get('type', 'UNKNOWN')
            if t_type not in type_performance:
                type_performance[t_type] = {"wins": 0, "losses": 0}
            if trade.get('result') == 'WIN':
                type_performance[t_type]['wins'] += 1
            elif trade.get('result') == 'LOSS':
                type_performance[t_type]['losses'] += 1

        # Analyse by confidence
        high_conf = [t for t in paper if t.get('confidence') == 'HIGH']
        med_conf = [t for t in paper if t.get('confidence') == 'MEDIUM']
        high_wins = len([t for t in high_conf if t.get('result') == 'WIN'])
        med_wins = len([t for t in med_conf if t.get('result') == 'WIN'])

        # Build performance text for Claude
        type_summary = "\n".join([
            f"- {k}: {v['wins']}W / {v['losses']}L ({round(v['wins']/(v['wins']+v['losses'])*100) if v['wins']+v['losses'] > 0 else 0}% win rate)"
            for k, v in type_performance.items()
        ])

        trades_summary = "\n".join([
            f"- {t['time']}: {t['type']} | Conf: {t['confidence']} | Result: {t['result']}"
            for t in paper[-20:]
        ])

        prompt = f"""
You are a trading system analyst reviewing the performance of an automated XAUUSD alert system.

## PERFORMANCE DATA

Total Alerts Logged: {len(trades)}
Closed Paper Trades: {len(wins) + len(losses)}
Wins: {len(wins)}
Losses: {len(losses)}
Win Rate: {win_rate:.1f}%
Open Trades: {len(open_trades)}

HIGH Confidence trades: {len(high_conf)} total | {high_wins} wins
MEDIUM Confidence trades: {len(med_conf)} total | {med_wins} wins

## PERFORMANCE BY SETUP TYPE
{type_summary if type_summary else "No completed trades yet"}

## RECENT TRADE LOG
{trades_summary if trades_summary else "No trades logged yet"}

## YOUR TASK

Analyse this performance data and provide:

**WHAT IS WORKING**
Which setup types, sessions or conditions are producing the best results?

**WHAT IS NOT WORKING**
Which setup types or conditions are consistently losing?

**KEY PATTERN IDENTIFIED**
The single most important pattern you can see in this data.

**RECOMMENDED RULE CHANGES**
Specific changes to make to improve performance:
- Should any setup types be filtered out entirely?
- Should confidence thresholds be adjusted?
- Are certain sessions consistently underperforming?

**UPDATED TRADING RULES**
Write 3-5 specific rules for the system to follow next week based on this data.
Example format: "Rule 1: Do not flag Asian session standalone FVGs as above MEDIUM confidence"

**NEXT WEEK FOCUS**
One specific thing to prioritise next week.

Be direct and data driven. Base everything on the actual numbers above.
"""

        message = claude_client.messages.create(
            model="claude-sonnet-4-6",
            max_tokens=400,
            messages=[{"role": "user", "content": prompt}]
        )

        review = message.content[0].text

        # Save the updated rules to a file
        try:
            with open('learned_rules.txt', 'w') as f:
                f.write(f"Last updated: {datetime.utcnow().strftime('%Y-%m-%d %H:%M UTC')}\n\n")
                f.write(review)
        except Exception as e:
            print(f"Rules save error: {e}")

        telegram_message = f"""
🧠 *Gold Bot Self-Review Report*
_{datetime.utcnow().strftime('%d %b %Y — %H:%M UTC')}_

📊 Stats: {len(trades)} alerts | {len(wins)}W {len(losses)}L | {win_rate:.1f}% win rate

{review}
"""
        send_telegram(telegram_message)

        return jsonify({
            "status": "self review complete",
            "win_rate": win_rate,
            "total_trades": len(trades)
        })

    except Exception as e:
        error_msg = f"⚠️ Self review error: {str(e)}"
        send_telegram(error_msg)
        return jsonify({"status": "error", "message": str(e)}), 500


# ============================================================
# LOAD LEARNED RULES INTO ANALYSIS
# ============================================================
def get_learned_rules():
    try:
        with open('learned_rules.txt', 'r') as f:
            return f.read()
    except FileNotFoundError:
        return "No learned rules yet — system will develop rules after first self-review."

# ============================================================
# SMART ENTRY TIMER — alerts when price hits entry zone
# ============================================================
@app.route('/check-entries', methods=['GET'])
def check_entries():
    try:
        if not active_trades:
            return jsonify({"status": "no active trades to monitor"})

        # Get current gold price
        gold = yf.download('GC=F', period='1d', interval='5m', progress=False)
        if gold.empty:
            return jsonify({"status": "no price data"})

        gold.columns = [col[0] for col in gold.columns]
        current_price = round(float(gold['Close'].iloc[-1]), 2)

        alerts_sent = 0
        for trade_id, trade in active_trades.items():
            if trade.get('result') != 'OPEN':
                continue

            entry = trade.get('entry', 0)
            stop = trade.get('stop', 0)
            target = trade.get('target', 0)
            direction = trade.get('direction', '')

            # Define entry zone as within 0.3% of entry price
            entry_zone_high = entry * 1.003
            entry_zone_low = entry * 0.997

            in_entry_zone = entry_zone_low <= current_price <= entry_zone_high

            if in_entry_zone:
                risk = abs(entry - stop)
                reward = abs(target - entry)
                rr = round(reward / risk, 1) if risk > 0 else 0

                message = f"""
⏰ *ENTRY ZONE ALERT*
_{trade['type']} | {trade['time']}_

Price is NOW in your entry zone!

📍 Current Price: {current_price}
🎯 Entry Zone: {round(entry_zone_low, 2)} — {round(entry_zone_high, 2)}
{'▲ LONG' if direction == 'LONG' else '▼ SHORT'}

Stop Loss: {stop}
Target: {target}
R:R = 1:{rr}

_Act now or wait for next candle close confirmation_
"""
                send_telegram(message)
                alerts_sent += 1

        return jsonify({
            "status": "checked",
            "current_price": current_price,
            "active_trades": len(active_trades),
            "entry_alerts_sent": alerts_sent
        })

    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# HEALTH CHECK
# ============================================================
@app.route('/health', methods=['GET'])
def health():
    return jsonify({
        "status": "✅ running",
        "alerts_this_session": len(recent_alerts),
        "active_trades": len(active_trades),
        "paper_trades_logged": len(paper_trades),
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
        drawdown_active, drawdown_msg = check_drawdown_protection()
        analysis = analyse_with_claude(
            fake_alert, "No prior alerts — this is a test",
            session_name, session_desc, is_killzone,
            zone, zone_pct, zone_advice,
            news_risk, news_msg, drawdown_active,
            dxy_direction, dxy_desc
        )
        telegram_message = f"""
🧪 *TEST ALERT — XAUUSD System Check*
📍 Price: 4088.50
📊 Zone: {zone} ({zone_pct}%)
⏰ {datetime.utcnow().strftime('%H:%M UTC')} | {session_name}
💵 DXY: {dxy_desc}

{analysis}

_This was a test alert — system is working correctly_ ✅
"""
        send_telegram(telegram_message)
        return jsonify({"status": "✅ test complete — check your Telegram", "session": session_name, "dxy": dxy_direction})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# START SERVER
# ============================================================
if __name__ == '__main__':
    scheduler = BackgroundScheduler()
    scheduler.add_job(func=lambda: morning_briefing(), trigger='cron', hour=7, minute=0)
    scheduler.add_job(func=lambda: weekly_bias_report(), trigger='cron', day_of_week='sun', hour=20, minute=0)
    scheduler.add_job(func=lambda: monday_gap_analysis(), trigger='cron', day_of_week='mon', hour=6, minute=55)
    scheduler.add_job(func=lambda: auto_update_levels(), trigger='cron', day_of_week='sun', hour=21, minute=0)
    scheduler.add_job(func=lambda: self_review(), trigger='cron', day_of_week='sun', hour=19, minute=0)
    scheduler.add_job(
        func=lambda: check_entries(),
        trigger='interval',
        minutes=5,
        id='entry_monitor'
    )
    scheduler.start()
    atexit.register(lambda: scheduler.shutdown())
    print("🚀 Gold Alert System starting...")
    print("📡 Waiting for TradingView alerts...")
    print("🔗 Test at: http://localhost:5000/test")
    print("❤️ Health check: http://localhost:5000/health")
    port = int(os.environ.get('PORT', 5000))
    app.run(host='0.0.0.0', port=port, debug=False)