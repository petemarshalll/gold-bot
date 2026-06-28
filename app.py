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
    url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
    payload = {
        "chat_id": TELEGRAM_CHAT_ID,
        "text": message,
        "parse_mode": "Markdown"
    }
    try:
        response = requests.post(url, json=payload)
        print(f"Telegram sent: {response.status_code}")
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
"""

    try:
        message = claude_client.messages.create(
            model="claude-sonnet-4-6",
            max_tokens=800,
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
            max_tokens=400,
            messages=[{"role": "user", "content": prompt}]
        )

        analysis = message.content[0].text
        telegram_message = f"🌅 *XAUUSD Monday Gap Analysis — {datetime.utcnow().strftime('%d %b %Y')}*\n\n{analysis}"
        send_telegram(telegram_message)

        return jsonify({"status": "monday gap analysis sent"})

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
            "price": "2341.50",
            "high": "2344.20",
            "low": "2338.10",
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