"""Generic predictive orbit emulator, driven by a fitted spec.

Where ``predictor.py`` hard-codes Antihydra's proven rules, this class
bootstraps from a finite raw prefix, fits the machine's exact record rules
(same rational elimination as ``finder.py``), enriches each rule with its
successor state and expansion side (fail-closed: both must be constant per
rule group), and then predicts records arbitrarily far forward with zero
raw simulation: blocks, exact raw-step index, control state, and absolute
head position (each frontier record extends its side by exactly one cell,
so heads are the running expansion counts).

Bounded empirical structure validated differentially — never a proof.
"""

from __future__ import annotations

from fractions import Fraction

from qgkit.bb6.dragon.finder import _solve_affine, CAP


def _full_rank(inputs, free=None):
    """Full rank of the affine design matrix over the *free* coordinates
    (those not pinned to an exact value by the rule's signature) plus bias.
    Pinned coordinates cannot vary for any state matching the key, so rank
    deficiency there is harmless by construction."""
    n = len(inputs[0])
    if free is None:
        free = list(range(n))
    rows = [[Fraction(inp[i]) for i in free] + [Fraction(1)]
            for inp in inputs]
    n = len(free)
    rank, r0 = 0, 0
    for c in range(n + 1):
        pr = next((r for r in range(r0, len(rows)) if rows[r][c] != 0), None)
        if pr is None:
            continue
        rows[r0], rows[pr] = rows[pr], rows[r0]
        rows[r0] = [v / rows[r0][c] for v in rows[r0]]
        for r in range(len(rows)):
            if r != r0 and rows[r][c] != 0:
                rows[r] = [v - rows[r][c] * w
                           for v, w in zip(rows[r], rows[r0])]
        rank += 1
        r0 += 1
    return rank == n + 1
from qgkit.bb6.vcollatz.classify import simulate_records


class MissingRule(Exception):
    pass


class GenericOrbitPredictor:
    def __init__(self, code: str, fit_steps: int = 120_000,
                 cap: int = 2_000):
        self.code = code
        halted, _, recs = simulate_records(code, steps=fit_steps, cap=cap)
        if halted:
            raise ValueError("machine halted in fit budget")
        recs = [r for r in recs if r["blocks"]]
        # the orbit lives on the dominant frontier side; the other side's
        # expansions are mid-rule snapshots that follow no record grammar
        n_r = sum(1 for r in recs if r["side"] == "R")
        self.side = "R" if n_r * 2 >= len(recs) else "L"
        recs = [r for r in recs if r["side"] == self.side]
        self._recs = recs
        # adaptive seed: skip the startup transient until the suffix fits
        last_err = None
        for seed in (1, 2, 4, 8, 16, 32, 64, 128):
            try:
                self.rules = self._fit_suffix(recs[seed:])
                self.seed_index = seed
                break
            except ValueError as e:
                last_err = e
        else:
            raise ValueError(f"no stable suffix: {last_err}")

    @staticmethod
    def _fit_group(samples, free=None):
        """Fit one rule group; None if arity/state inconsistent or inexact."""
        n_out = len(samples[0][1])
        if any(len(x[1]) != n_out for x in samples):
            return None
        states = {x[3] for x in samples}
        if len(states) != 1:
            return None
        maps = [_solve_affine([(b1, b2[t]) for b1, b2, _, _, _ in samples])
                for t in range(n_out)]
        cost = _solve_affine([(b1, d) for b1, _, d, _, _ in samples])
        if cost is None or any(m is None for m in maps):
            return None
        return {"maps": maps, "cost": cost, "state": states.pop(),
                "determined": _full_rank([x[0] for x in samples], free),
                "lookup": {x[0]: (x[1], x[2]) for x in samples}}

    @classmethod
    def _fit_suffix(cls, recs):
        fine, coarse, pooled = {}, {}, {}
        for r1, r2 in zip(recs, recs[1:]):
            sample = (tuple(r1["blocks"]), tuple(r2["blocks"]),
                      r2["step"] - r1["step"], r2["state"], r2["side"])
            fk = (r1["state"], len(r1["blocks"]),
                  tuple((min(x, CAP), x & 1) for x in r1["blocks"]))
            ck = (r1["state"], len(r1["blocks"]),
                  tuple(min(x, CAP) for x in r1["blocks"]))
            pk = (r1["state"], len(r1["blocks"]))
            fine.setdefault(fk, []).append(sample)
            coarse.setdefault(ck, []).append(sample)
            pooled.setdefault(pk, []).append(sample)
        rules = {
            "fine": {k: r for k, v in fine.items()
                     if (r := cls._fit_group(
                         v, [i for i, (c, _) in enumerate(k[2])
                             if c == CAP])) is not None},
            "coarse": {k: r for k, v in coarse.items()
                       if (r := cls._fit_group(
                           v, [i for i, c in enumerate(k[2])
                               if c == CAP])) is not None},
            "pooled": {k: r for k, v in pooled.items()
                       if (r := cls._fit_group(v)) is not None}}
        if not rules["fine"]:
            raise ValueError("no fittable rule group")
        return rules

    @staticmethod
    def _apply(coeffs, blocks):
        n = len(blocks)
        v = sum(c * Fraction(x) for c, x in zip(coeffs[:n], blocks)) + coeffs[n]
        if v.denominator != 1 or v < 0:
            raise MissingRule("non-integral prediction")
        return int(v)

    def predict(self, n_records: int):
        """Predict records forward from the seed via the spec alone.
        Yields dicts with record index, blocks, raw step, state, head."""
        seed = self._recs[self.seed_index]
        blocks, step = tuple(seed["blocks"]), seed["step"]
        state = seed["state"]
        # this side's frontier advances one cell per record of this side
        n = self.seed_index + 1
        sign = 1 if self.side == "R" else -1
        for i in range(n_records):
            yield {"i": self.seed_index + i, "blocks": blocks, "step": step,
                   "state": state, "head": sign * n}
            fk = (state, len(blocks),
                  tuple((min(x, CAP), x & 1) for x in blocks))
            ck = (state, len(blocks), tuple(min(x, CAP) for x in blocks))
            fine = self.rules["fine"].get(fk)
            coarse = self.rules["coarse"].get(ck)
            if fine is not None and fine["determined"]:
                rule = fine
                step = step + self._apply(rule["cost"], blocks)
                blocks = tuple(self._apply(m, blocks) for m in rule["maps"])
            elif coarse is not None and coarse["determined"]:
                rule = coarse
                step = step + self._apply(rule["cost"], blocks)
                blocks = tuple(self._apply(m, blocks) for m in rule["maps"])
            elif ((pr := self.rules["pooled"].get((state, len(blocks))))
                  is not None and pr["determined"]):
                rule = pr
                step = step + self._apply(rule["cost"], blocks)
                blocks = tuple(self._apply(m, blocks) for m in rule["maps"])
            elif fine is not None and blocks in fine["lookup"]:
                rule = fine
                out, d = fine["lookup"][blocks]
                step, blocks = step + d, out
            else:
                raise MissingRule(f"no usable rule at record "
                                  f"{self.seed_index + i} ({fk})")
            state = rule["state"]
            n += 1
