# Gold research harness

Offline, cost-aware backtesting for finding and validating a trading edge on
XAUUSD using real MT5 data. Nothing here touches the live bot.

## Setup (laptop or VPS, Python 3.10+)

```
cd gold-bot/research
pip install -r requirements.txt
python -m pytest tests -q        # 9 tests should pass
```

## Workflow

1. **Export data** on the VPS from B's terminal (real broker feed):
   `python export_mt5_history.py` with `MCP_PORT`, `MCP_API_KEY`, `SYMBOL=XAUUSD.m` set.
   Produces `data/XAUUSD.m_M5.csv` (and M1 if the broker has it). Copy the M5 CSV to wherever you run research.

2. **Smoke test** the harness on random data if the export isn't done yet:
   `python make_synthetic.py --years 2` then
   `python run.py open_range --data data/SYNTH_M5.csv`.
   Random data must show a negative avg R. If it doesn't, the engine has a bug, stop and fix it.

3. **Run a hypothesis** on real data:
   `python run.py open_range --data data/XAUUSD.m_M5.csv`
   `python run.py open_range --data data/XAUUSD.m_M5.csv --set open_utc=13.5`
   `python run.py asian_reversion --data data/XAUUSD.m_M5.csv`
   `python run.py asian_reversion --data data/XAUUSD.m_M5.csv --vol-filter`

4. **Read the output in this order**
   - WALK-FORWARD `OOS TOTAL` and `positive test windows`. This is the only number for go/no-go.
   - `by session`, `by direction`, `by regime`: does the edge live in one corner? Then the rule needs a filter, not more params.
   - ROBUSTNESS: does avg R hold within roughly +/-30% when each param moves 20%? If one param is a cliff, it's curve-fit.
   - FULL HISTORY fixed-params: the optimistic in-sample view. Never decide from this alone.

5. **Set costs to what you see live.** Defaults in `engine.CostModel` are conservative guesses.
   Update `spread_by_session`, `commission_per_lot_rt` and `stop_slippage` from B's real fills
   (`get_trading_history_positions` gives commission; compare fill vs intended entry for slippage).

## Go / no-go for a hypothesis

Keep it only if all of these hold on walk-forward OOS:
- n >= 200 OOS trades (or >= 100 with t-stat > 2.5)
- avg R >= +0.20 after costs
- profit factor >= 1.3
- at least 2/3 of test windows positive
- robustness: no single 20% param change flips avg R negative
- positive in both `trend` and `range` months, or a clear reason for a regime switch

Most hypotheses will fail this. That is the process working.

## Adding a hypothesis

Create `strategies/<name>.py` with a class subclassing `strategies.base.Strategy`:
- `defaults`: dict of params
- `param_grid()`: a SMALL grid (2-3 values for 2-3 params, under ~30 combos) for walk-forward
- `generate(df)`: return `Signal`s using only bars up to `signal.time`
Register it in `run.py` `STRATEGIES`.

Rules for `generate`: decide on a closed bar, never peek at later bars; use `resample`/`atr` from
`engine`; prefer stop or limit orders with a `ttl_bars`; set `exit_at` for session-bound ideas.

## Hypothesis backlog (in test order)

1. London open-range breakout (`open_range`, default) and NY (`--set open_utc=13.5`)
2. Asian-range false-break reversion (`asian_reversion`)
3. Either of the above with the volatility-regime filter (`--vol-filter`)
4. Post-news momentum: continuation 15-60 min after 08:30/13:30 US releases (needs a news calendar CSV)
5. DXY / real-yield divergence filter on any of the above (needs a DXY M5 export from the same terminal)
6. Port the existing FVG + sweep detector from `app.py` and run it through walk-forward with costs, so the current v1.3 rules get the same treatment as everything else
7. Day-of-week / month-end seasonality as filters, never as standalone entries

## Files

- `engine.py`: data loading, `CostModel`, `simulate`, `metrics`, `walk_forward`, `robustness`, `regime_split`
- `strategies/base.py`: `Strategy` base, `VolRegimeFilter`
- `strategies/open_range.py`, `strategies/asian_reversion.py`: hypotheses 1 and 2
- `run.py`: CLI report; writes trade lists to `results/`
- `export_mt5_history.py`: MT5 -> CSV via the MCP server
- `make_synthetic.py`: random-walk data for engine sanity checks
- `tests/test_engine.py`: fill, cost and R-maths tests
