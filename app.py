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
from datetime import datetime, timezone
from dotenv import load_dotenv
from apscheduler.schedulers.background import BackgroundScheduler
import atexit
import yfinance as yf
import pandas as pd

# Load secret keys from .env file
load_dotenv()

# Start the server
app = Flask(__name__)

# Connect to Claude
claude_client = anthropic.Anthropic(api_key=os.getenv("ANTHROPIC_API_KEY"))

# Telegram details
TELEGRAM_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID")

# ============================================================
# MEMORY — stores recent alerts so Claude has context
# ============================================================
recent_alerts = []
paper_trades = []
daily_losses = 0
consecutive_losses = 0
drawdown_protection = False
scheduler = None

# ============================================================
# PROP FIRM RULES — update these when you join a firm
# ============================================================
PROP_FIRM_RULES = {
    "account_size": 10000,
    "max_daily_loss_pct": 4.0,
    "max_total_drawdown_pct": 8.0,
    "min_trading_days": 4,
    "max_loss_per_trade_pct": 1.0,
}

# Track current performance
current_balance = 10000
daily_pnl = 0
total_pnl = 0
trading_days = 0

# ============================================================
# KEY LEVELS — update these every Sunday
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
# PREMIUM / DISCOUNT ZONE CALCULATOR
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
# ECONOMIC CALENDAR — checks for high impact news
# ============================================================
def check_news_risk():
    hour = datetime.now(timezone.utc).hour
    minute = datetime.now(timezone.utc).minute
    weekday = datetime.now(timezone.utc).weekday()

    high_risk_times = [
        (13, 30),  # US market open / NFP / CPI typical time
        (15, 0),   # Fed speeches common time
        (12, 0),   # Noon announcements
    ]

    for risk_hour, risk_minute in high_risk_times:
        time_diff = abs((hour * 60 + minute) - (risk_hour * 60 + risk_minute))
        if time_diff <= 30:
            return True, f"High impact news window — within 30 mins of {risk_hour}:{risk_minute:02d} UTC"

    if weekday == 4 and 13 <= hour <= 14:
        return True, "NFP Friday risk window — avoid new trades"

    return False, "No major news risk detected"

# ============================================================
# DRAWDOWN PROTECTION CHECK
# ============================================================
def check_drawdown_protection():
    global consecutive_losses, drawdown_protection
    if consecutive_losses >= 3:
        drawdown_protection = True
        return True, f"⚠️ DRAWDOWN PROTECTION ACTIVE — {consecutive_losses} consecutive losses. Only HIGH confidence signals will be sent."
    drawdown_protection = False
    return False, "Normal trading mode"

# ============================================================
# SEND TELEGRAM MESSAGE
# ============================================================
def send_telegram(message):
    # Telegram max length is 4096 characters
    # Trim cleanly if too long
    if len(message) > 4000:
        # Find the last complete sentence before the limit
        trimmed = message[:4000]
        last_period = trimmed.rfind('.')
        if last_period > 3500:
            message = trimmed[:last_period + 1] + "\n\n_✅ Analysis complete_"
        else:
            message = trimmed + "\n\n_✅ Analysis complete_"

    url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
    payload = {
        "chat_id": TELEGRAM_CHAT_ID,
        "text": message,
        "parse_mode": "Markdown"
    }
    try:
        response = requests.post(url, json=payload)
        print(f"Telegram sent: {response.status_code}")
        # If markdown parsing fails try plain text
        if response.status_code == 400:
            payload["parse_mode"] = "None"
            response = requests.post(url, json=payload)
            print(f"Telegram plain text sent: {response.status_code}")
    except Exception as e:
        print(f"Telegram error: {e}")

# ============================================================
# LOG TRADE TO CSV
# ============================================================
def log_to_csv(alert_type, price, confidence, analysis):
    try:
        with open('trade_log.csv', 'a', newline='') as f:
            writer = csv.writer(f)
            writer.writerow([
                datetime.utcnow().strftime('%Y-%m-%d %H:%M'),
                alert_type,
                price,
                confidence,
                analysis[:150]
            ])
    except Exception as e:
        print(f"CSV log error: {e}")

# ============================================================
# PAPER TRADE TRACKER
# ============================================================
def log_paper_trade(alert_type, price, direction, entry, stop, target, confidence):
    trade = {
        "time": datetime.utcnow().strftime('%Y-%m-%d %H:%M'),
        "type": alert_type,
        "price": price,
        "direction": direction,
        "entry": entry,
        "stop": stop,
        "target": target,
        "confidence": confidence,
        "result": "OPEN"
    }
    paper_trades.append(trade)

    try:
        with open('paper_trades.json', 'w') as f:
            json.dump(paper_trades, f, indent=2)
    except Exception as e:
        print(f"Paper trade log error: {e}")

# ============================================================
# MAIN CLAUDE ANALYSIS
# ============================================================
def analyse_with_claude(alert_data, recent_context, session_name, session_desc, is_killzone, zone, zone_pct, zone_advice, news_risk, news_msg, drawdown_active):

    levels_text = "\n".join([f"- {k.replace('_', ' ').title()}: {v}" for k, v in KEY_LEVELS.items()])

    killzone_text = "✅ YES — weight this signal higher" if is_killzone else "❌ NO — standard session, normal weighting"

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

## RECENT ALERT HISTORY
{recent_context if recent_context else "No prior alerts this session"}

## DRAWDOWN STATUS
{"⚠️ DRAWDOWN PROTECTION ACTIVE — only flag if genuinely HIGH confidence" if drawdown_active else "Normal mode — standard confidence thresholds apply"}

## YOUR ANALYSIS — use exactly these headers:

**SETUP VALIDITY**
Is this a genuine SMC setup or noise? Explain why in 2-3 sentences.

**CONFLUENCE SCORE**
Rate out of 10 and list what confluences are present:
- Killzone alignment (2 points)
- Premium/Discount alignment (2 points)  
- Key level proximity (2 points)
- Timeframe alignment (2 points)
- Clean structure (2 points)

**TRADE DIRECTION**
Long or Short? Why does structure support this?

**ENTRY ZONE**
Specific price zone to look for entry.

**STOP LOSS**
Where does structure say you are wrong? Specific level.

**TARGET**
Logical draw on liquidity or target zone. Specific level.

**RISK:REWARD**
Calculate the RR ratio based on entry, stop and target above.

**CONFIDENCE LEVEL**
Rate as LOW / MEDIUM / HIGH and explain why in one sentence.

**AVOID IF**
List any specific reasons to skip this trade entirely.

Be direct and concise. Use the headers exactly as shown.

CRITICAL FORMATTING RULES:
- Maximum 2 sentences per section
- Stop Loss: one sentence only
- Target: two sentences maximum  
- Always end with CONFIDENCE LEVEL and AVOID IF sections
- Total response must be under 500 words
"""

    try:
        message = claude_client.messages.create(
            model="claude-sonnet-4-6",
            max_tokens=550,
            messages=[{"role": "user", "content": prompt}]
        )
        return message.content[0].text
    except Exception as e:
        return f"Claude analysis error: {str(e)}"

# ============================================================
# WEBHOOK — receives TradingView alerts
# ============================================================
@app.route('/webhook', methods=['POST'])
def webhook():
    global recent_alerts

    try:
        data = request.json
        print(f"Alert received: {data}")

        # Get all context
        session_name, session_desc, is_killzone = get_session()
        zone, zone_pct, zone_advice = get_premium_discount(data.get('price', 0))
        news_risk, news_msg = check_news_risk()
        drawdown_active, drawdown_msg = check_drawdown_protection()

        # Add to recent history
        recent_alerts.append({
            "type": data.get('type', 'Unknown'),
            "price": data.get('price', 'Unknown'),
            "timeframe": data.get('timeframe', '15m'),
            "time": datetime.utcnow().strftime('%H:%M UTC')
        })
        if len(recent_alerts) > 10:
            recent_alerts.pop(0)

        # Build context string
        context = "\n".join([
            f"- {a['time']}: {a['type']} at {a['price']} ({a['timeframe']})"
            for a in recent_alerts[:-1]
        ])

        # Get Claude's analysis
        analysis = analyse_with_claude(
            data, context, session_name, session_desc,
            is_killzone, zone, zone_pct, zone_advice,
            news_risk, news_msg, drawdown_active
        )

        # Extract predicted direction from analysis
        predicted_direction = "NEUTRAL"
        if "LONG" in analysis.upper() and "DIRECTION" in analysis.upper():
            predicted_direction = "LONG"
        elif "SHORT" in analysis.upper() and "DIRECTION" in analysis.upper():
            predicted_direction = "SHORT"

        # Schedule outcome check in 4 hours
        from datetime import timedelta
        check_time = datetime.now(timezone.utc) + timedelta(hours=4)
        entry_price = float(data.get('price', 0))
        alert_time_str = datetime.now(timezone.utc).strftime('%H:%M UTC')
        
        if scheduler:
            job_id = f"outcome_{datetime.now(timezone.utc).timestamp()}"
            scheduler.add_job(
                func=lambda a=data.get('type', 'Unknown'), b=entry_price, c=predicted_direction, d=alert_time_str: check_trade_outcome(a, b, c, d),
                trigger='date',
                run_date=check_time,
                id=job_id
            )

        # Extract confidence from analysis
        confidence = "MEDIUM"
        if "HIGH" in analysis.upper() and "CONFIDENCE" in analysis.upper():
            confidence = "HIGH"
        elif "LOW" in analysis.upper() and "CONFIDENCE" in analysis.upper():
            confidence = "LOW"

        # Skip low confidence signals during drawdown
        if drawdown_active and confidence == "LOW":
            log_to_csv(data.get('type'), data.get('price'), "SKIPPED-DRAWDOWN", "Skipped due to drawdown protection")
            return jsonify({"status": "skipped", "reason": "drawdown protection active"})

        # Skip if news risk and not high confidence
        if news_risk and confidence != "HIGH":
            send_telegram(f"⚠️ *Alert suppressed — news risk active*\n{news_msg}\nAlert type: {data.get('type')} at {data.get('price')}")
            return jsonify({"status": "suppressed", "reason": "news risk"})

        # Format emoji
        alert_type = data.get('type', '')
        if "BEARISH" in alert_type:
            emoji = "🔴"
        elif "BULLISH" in alert_type:
            emoji = "🟢"
        else:
            emoji = "🟡"

        # Killzone badge
        killzone_badge = "🎯 KILLZONE" if is_killzone else ""

        # Build Telegram message
        telegram_message = f"""
{emoji} *XAUUSD — {alert_type}* {killzone_badge}
📍 Price: {data.get('price', 'N/A')}
📊 Zone: {zone} ({zone_pct}%)
⏰ {datetime.utcnow().strftime('%H:%M UTC')} | {session_name}
⚠️ News Risk: {news_msg}

{analysis}

_Confidence: {confidence} | Log this trade in your journal_
"""

        send_telegram(telegram_message)
        log_to_csv(alert_type, data.get('price'), confidence, analysis)

        return jsonify({"status": "ok"})

    except Exception as e:
        error_msg = f"⚠️ SYSTEM ERROR: {str(e)}"
        print(error_msg)
        send_telegram(error_msg)
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# MORNING BRIEFING — call this every day at 7am
# ============================================================
@app.route('/morning-briefing', methods=['GET'])
def morning_briefing():
    try:
        levels_text = "\n".join([f"- {k.replace('_', ' ').title()}: {v}" for k, v in KEY_LEVELS.items()])

        prompt = f"""
You are an expert XAUUSD analyst. Provide a concise morning briefing for a gold trader.

Today is {datetime.utcnow().strftime('%A %d %B %Y')}

Key levels this week:
{levels_text}

Recent alerts this session:
{str(recent_alerts[-5:]) if recent_alerts else "No alerts yet today"}

Cover these points concisely:
1. Key levels to watch today
2. Recommended session focus (London vs NY)
3. Bias direction based on key levels (bullish/bearish/neutral)
4. What setups to look for
5. What to avoid today
6. One sentence summary

Keep it punchy and practical. This trader uses SMC — FVGs, sweeps, order blocks.
"""

        message = claude_client.messages.create(
            model="claude-sonnet-4-6",
            max_tokens=500,
            messages=[{"role": "user", "content": prompt}]
        )

        briefing = message.content[0].text
        telegram_message = f"☀️ *XAUUSD Morning Briefing — {datetime.utcnow().strftime('%d %b %Y')}*\n\n{briefing}"
        send_telegram(telegram_message)

        return jsonify({"status": "briefing sent"})

    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500
# ============================================================
# WEEKLY BIAS REPORT — fires every Sunday 8pm
# ============================================================
@app.route('/weekly-bias', methods=['GET'])
def weekly_bias_report():
    try:
        levels_text = "\n".join([f"- {k.replace('_', ' ').title()}: {v}" for k, v in KEY_LEVELS.items()])

        prompt = f"""
You are an expert XAUUSD analyst preparing a weekly trading bias report.

Today is {datetime.utcnow().strftime('%A %d %B %Y')}

Key levels this week:
{levels_text}

Provide a structured weekly bias report covering:

**WEEKLY BIAS**
Overall directional bias for the coming week — bullish, bearish or neutral and why.

**KEY LEVELS TO RESPECT**
The most important levels to watch this week and why they matter.

**SESSIONS TO FOCUS ON**
Which sessions are likely to produce the best setups this week.

**SETUPS TO LOOK FOR**
Specific setup types that align with the weekly bias.

**SETUPS TO AVOID**
What NOT to trade this week.

**RISK EVENTS**
Key news events or market conditions to be aware of.

**ONE SENTENCE SUMMARY**
The week in one clear sentence.

Keep it punchy, practical and SMC focused.
"""

        message = claude_client.messages.create(
            model="claude-sonnet-4-6",
            max_tokens=600,
            messages=[{"role": "user", "content": prompt}]
        )

        report = message.content[0].text
        telegram_message = f"📊 *XAUUSD Weekly Bias Report — Week of {datetime.utcnow().strftime('%d %b %Y')}*\n\n{report}"
        send_telegram(telegram_message)

        return jsonify({"status": "weekly bias report sent"})

    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500


# ============================================================
# MONDAY GAP ANALYSIS — fires every Monday 6:55am
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

Give a concise Monday gap analysis covering:
**GAP STRATEGY** - what to look for at Monday open
**FIRST SETUP** - ideal first trade conditions this Monday
**ASIAN SESSION** - likely direction before London
**AVOID** - traps smart money typically sets Monday open

Maximum 3 sentences per section. Be direct and actionable.
"""

        message = claude_client.messages.create(
            model="claude-sonnet-4-6",
            max_tokens=300,
            messages=[{"role": "user", "content": prompt}]
        )

        analysis = message.content[0].text
        telegram_message = f"🌅 *XAUUSD Monday Gap Analysis — {datetime.utcnow().strftime('%d %b %Y')}*\n\n{analysis}"
        send_telegram(telegram_message)

        return jsonify({"status": "monday gap analysis sent"})

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

        if daily_used_pct >= 80:
            daily_status = "🔴 DANGER"
        elif daily_used_pct >= 50:
            daily_status = "🟡 CAUTION"
        else:
            daily_status = "🟢 SAFE"

        if total_used_pct >= 80:
            total_status = "🔴 DANGER"
        elif total_used_pct >= 50:
            total_status = "🟡 CAUTION"
        else:
            total_status = "🟢 SAFE"

        message = f"""
📊 *Prop Firm Status Report*

*Account Size:* ${account:,.2f}
*Current Balance:* ${current_balance:,.2f}
*Today's P&L:* ${daily_pnl:,.2f}
*Total P&L:* ${total_pnl:,.2f}
*Trading Days:* {trading_days}/{PROP_FIRM_RULES['min_trading_days']} minimum

*Daily Loss Limit:* {daily_status}
Used: {daily_used_pct:.1f}% | Remaining: ${daily_remaining:,.2f}
Limit: {PROP_FIRM_RULES['max_daily_loss_pct']}% (${daily_loss_limit:,.2f})

*Total Drawdown:* {total_status}
Used: {total_used_pct:.1f}% | Remaining: ${total_remaining:,.2f}
Limit: {PROP_FIRM_RULES['max_total_drawdown_pct']}% (${total_drawdown_limit:,.2f})

*Max Risk Per Trade:* {PROP_FIRM_RULES['max_loss_per_trade_pct']}% (${account * PROP_FIRM_RULES['max_loss_per_trade_pct'] / 100:,.2f})
"""
        send_telegram(message)
        return jsonify({
            "status": "ok",
            "daily_used_pct": daily_used_pct,
            "total_used_pct": total_used_pct,
            "daily_status": daily_status,
            "total_status": total_status
        })

    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500


# ============================================================
# UPDATE P&L — call this after each trade
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
            warnings.append(f"⚠️ DAILY LOSS WARNING — at {(abs(min(daily_pnl,0))/account)*100:.1f}% of {PROP_FIRM_RULES['max_daily_loss_pct']}% limit")
        if abs(min(total_pnl, 0)) >= total_drawdown_limit * 0.8:
            warnings.append(f"⚠️ TOTAL DRAWDOWN WARNING — at {(abs(min(total_pnl,0))/account)*100:.1f}% of {PROP_FIRM_RULES['max_total_drawdown_pct']}% limit")
        if abs(min(daily_pnl, 0)) >= daily_loss_limit:
            warnings.append(f"🚨 DAILY LOSS LIMIT HIT — STOP TRADING TODAY")
        if abs(min(total_pnl, 0)) >= total_drawdown_limit:
            warnings.append(f"🚨 TOTAL DRAWDOWN LIMIT HIT — ACCOUNT AT RISK")

        if warnings:
            send_telegram("\n".join(warnings))

        return jsonify({
            "status": "updated",
            "daily_pnl": daily_pnl,
            "total_pnl": total_pnl,
            "current_balance": current_balance,
            "warnings": warnings
        })

    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# AUTO LEVEL DETECTION — runs every Sunday 9pm automatically
# ============================================================
@app.route('/auto-levels', methods=['GET'])
def auto_update_levels():
    global KEY_LEVELS
    try:
    # Pull data
        gold = yf.download('GC=F', period='30d', interval='1d', progress=False)

        if gold.empty:
            send_telegram("⚠️ Auto level update failed — no data returned")
            return jsonify({"status": "error", "message": "no data"})

        # Flatten MultiIndex FIRST before doing anything else
        gold.columns = [col[0] for col in gold.columns]

        # NOW create subsets after flattening
        weekly = gold.tail(5)
        today = gold.tail(1)
        recent = gold.tail(10)
        full_range = gold.tail(20)

        # Extract levels
        weekly_high = round(float(weekly['High'].max()), 2)
        weekly_low = round(float(weekly['Low'].min()), 2)
        daily_high = round(float(today['High'].iloc[-1]), 2)
        daily_low = round(float(today['Low'].iloc[-1]), 2)
        major_resistance = round(float(recent['High'].max()), 2)
        major_support = round(float(recent['Low'].min()), 2)
        dealing_range_high = round(float(full_range['High'].max()), 2)
        dealing_range_low = round(float(full_range['Low'].min()), 2)

        # Update the global KEY_LEVELS automatically
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

        # Send confirmation to Telegram
        levels_text = "\n".join([
            f"- {k.replace('_', ' ').title()}: {v}" 
            for k, v in KEY_LEVELS.items()
        ])

        telegram_message = f"""
🤖 *Auto Level Update Complete*
_{datetime.utcnow().strftime('%d %b %Y — %H:%M UTC')}_

Levels have been automatically calculated from live market data and updated for the coming week:

{levels_text}

_Claude will use these levels in all analysis until next Sunday_ ✅
"""
        send_telegram(telegram_message)

        return jsonify({
            "status": "levels auto updated",
            "levels": KEY_LEVELS
        })

    except Exception as e:
        error_msg = f"⚠️ Auto level update error: {str(e)}"
        send_telegram(error_msg)
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# TRADE OUTCOME TRACKER
# ============================================================
def check_trade_outcome(alert_type, entry_price, predicted_direction, alert_time):
    try:
        # Pull current gold price
        gold = yf.download('GC=F', period='1d', interval='5m', progress=False)
        
        if gold.empty:
            return
            
        # Flatten columns
        gold.columns = [col[0] for col in gold.columns]
        
        # Get current price
        current_price = round(float(gold['Close'].iloc[-1]), 2)
        
        # Calculate move
        price_move = round(current_price - entry_price, 2)
        points_moved = abs(price_move)
        
        # Determine if prediction was correct
        if predicted_direction == "LONG":
            correct = price_move > 0
            direction_emoji = "🟢" if correct else "🔴"
        elif predicted_direction == "SHORT":
            correct = price_move < 0
            direction_emoji = "🟢" if correct else "🔴"
        else:
            correct = None
            direction_emoji = "🟡"
        
        result = "WIN ✅" if correct else "LOSS ❌" if correct is not None else "NEUTRAL"
        
        # Build outcome message
        message = f"""
📊 *Trade Outcome Update*
_{alert_time} alert — 4 hour check_

Alert: {alert_type}
Entry Price: {entry_price}
Current Price: {current_price}
Move: {'+' if price_move > 0 else ''}{price_move} points
Predicted: {predicted_direction}
Result: {direction_emoji} {result}

_Log this result in your journal_
"""
        send_telegram(message)
        
        # Log to CSV
        with open('outcomes.csv', 'a', newline='') as f:
            writer = csv.writer(f)
            writer.writerow([
                alert_time,
                alert_type,
                entry_price,
                current_price,
                price_move,
                predicted_direction,
                result
            ])
            
    except Exception as e:
        print(f"Outcome tracker error: {e}")

# ============================================================
# HEALTH CHECK
# ============================================================
@app.route('/health', methods=['GET'])
def health():
    return jsonify({
        "status": "✅ running",
        "alerts_this_session": len(recent_alerts),
        "paper_trades_logged": len(paper_trades),
        "drawdown_protection": drawdown_protection,
        "consecutive_losses": consecutive_losses,
        "time_utc": datetime.utcnow().strftime('%H:%M:%S UTC')
    })

# ============================================================
# TEST ENDPOINT — sends a fake alert to test everything
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
        zone, zone_pct, zone_advice = get_premium_discount(fake_alert['price'])
        news_risk, news_msg = check_news_risk()
        drawdown_active, drawdown_msg = check_drawdown_protection()

        analysis = analyse_with_claude(
            fake_alert, "No prior alerts — this is a test",
            session_name, session_desc, is_killzone,
            zone, zone_pct, zone_advice,
            news_risk, news_msg, drawdown_active
        )

        telegram_message = f"""
🧪 *TEST ALERT — XAUUSD System Check*
📍 Price: 2341.50
⏰ {datetime.utcnow().strftime('%H:%M UTC')} | {session_name}

{analysis}

_This was a test alert — system is working correctly_ ✅
"""
        send_telegram(telegram_message)

        return jsonify({
            "status": "✅ test complete — check your Telegram",
            "session": session_name,
            "zone": zone
        })

    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# ============================================================
# UPDATE KEY LEVELS — call this every Sunday
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
# START THE SERVER
# ============================================================
if __name__ == '__main__':
    # Start the scheduler
    scheduler = BackgroundScheduler()
    
    # Morning briefing every day at 7am UTC
    scheduler.add_job(
        func=lambda: morning_briefing(),
        trigger='cron',
        hour=7,
        minute=0
    )

    # Auto update key levels every Sunday at 9pm UTC
    scheduler.add_job(
        func=lambda: auto_update_levels(),
        trigger='cron',
        day_of_week='sun',
        hour=21,
        minute=0
    )
    
    # Weekly bias report every Sunday at 8pm UTC
    scheduler.add_job(
        func=lambda: weekly_bias_report(),
        trigger='cron',
        day_of_week='sun',
        hour=20,
        minute=0
    )

    # Monday gap analysis every Monday at 6:55am UTC
    scheduler.add_job(
        func=lambda: monday_gap_analysis(),
        trigger='cron',
        day_of_week='mon',
        hour=6,
        minute=55
    )

    scheduler.start()
    atexit.register(lambda: scheduler.shutdown())

    print("🚀 Gold Alert System starting...")
    print("📡 Waiting for TradingView alerts...")
    print("🔗 Test at: http://localhost:5000/test")
    print("❤️ Health check: http://localhost:5000/health")
    print("⏰ Scheduler running — morning briefing at 7am UTC daily")
    
    port = int(os.environ.get('PORT', 5000))
    app.run(host='0.0.0.0', port=port, debug=False)