"""Strategy base class and the volatility-regime filter wrapper."""
from __future__ import annotations

import pandas as pd

from engine import Signal, atr, resample


class Strategy:
    name = "base"
    defaults: dict = {}

    def __init__(self, **params):
        self.params = {**self.defaults, **params}

    def with_params(self, params: dict) -> "Strategy":
        return self.__class__(**{**self.params, **params})

    def param_grid(self) -> dict:
        return {}

    def generate(self, df: pd.DataFrame) -> list[Signal]:
        raise NotImplementedError

    def describe(self) -> str:
        return f"{self.name} {self.params}"


class VolRegimeFilter(Strategy):
    """
    Wraps any strategy and only passes signals when H1 ATR sits inside a
    rolling percentile band. Tests the hypothesis 'this edge only works
    in normal volatility' without touching the inner strategy.
    """
    name = "vol_filter"
    defaults = {"atr_n": 14, "lookback_bars": 500, "p_low": 0.2, "p_high": 0.9}

    def __init__(self, inner: Strategy, **params):
        super().__init__(**params)
        self.inner = inner
        self.name = f"vol_filter({inner.name})"

    def with_params(self, params: dict) -> "VolRegimeFilter":
        mine = {k: v for k, v in params.items() if k in self.defaults}
        theirs = {k: v for k, v in params.items() if k not in self.defaults}
        return VolRegimeFilter(self.inner.with_params(theirs), **{**self.params, **mine})

    def param_grid(self) -> dict:
        return {**self.inner.param_grid(), "p_low": [0.1, 0.3], "p_high": [0.8, 0.95]}

    def generate(self, df: pd.DataFrame) -> list[Signal]:
        p = self.params
        h1 = resample(df, "1h")
        a = atr(h1, p["atr_n"])
        rank = a.rolling(p["lookback_bars"]).rank(pct=True)
        ok = rank.between(p["p_low"], p["p_high"])
        out = []
        for s in self.inner.generate(df):
            h = s.time.floor("1h")
            pos = ok.index.get_indexer([h], method="ffill")[0]
            if pos >= 0 and bool(ok.iloc[pos]):
                out.append(s)
        return out
