"""Orbit finder: discover a machine's record-orbit rules automatically.

Where ``predictor.py`` hard-codes Antihydra's three proven rules, the
finder *derives* an orbit spec for any collapse-like machine: simulate its
frontier records, group consecutive record transitions by shape, fit exact
affine maps (block vectors and step costs) by rational elimination, and
verify fail-closed — a fitted spec is returned only if it replays every
observed transition exactly.  The output is precisely what an
``OrbitPredictor`` (and, downstream, a flying-dragon localization proof)
needs for that machine: rules, exact costs, guards.

Bounded empirical structure: a spec is evidence about observed records,
never a proof.  The Lean layer is where specs graduate to theorems.
"""

from __future__ import annotations

from fractions import Fraction

from qgkit.bb6.vcollatz.classify import simulate_records

CAP = 3  # guard signature cap: coordinates < CAP are guard-relevant


def _solve_affine(samples):
    """Exact least-constraint affine fit: outputs[t] = A·inputs + b over Q.
    samples: list of (inputs tuple, output int). Returns coeff tuple
    (a_1..a_n, b) or None."""
    n = len(samples[0][0])
    rows = [[Fraction(x) for x in inp] + [Fraction(1), Fraction(out)]
            for inp, out in samples]
    cols = n + 1
    # Gaussian elimination on the first `cols` independent rows
    mat, piv = [r[:] for r in rows], []
    r0 = 0
    for c in range(cols):
        pr = next((r for r in range(r0, len(mat)) if mat[r][c] != 0), None)
        if pr is None:
            continue
        mat[r0], mat[pr] = mat[pr], mat[r0]
        mat[r0] = [v / mat[r0][c] for v in mat[r0]]
        for r in range(len(mat)):
            if r != r0 and mat[r][c] != 0:
                mat[r] = [v - mat[r][c] * w for v, w in zip(mat[r], mat[r0])]
        piv.append(c)
        r0 += 1
    sol = [Fraction(0)] * cols
    for i, c in enumerate(piv):
        sol[c] = mat[i][cols]
    # verify on ALL samples (fail-closed)
    for inp, out in samples:
        val = sum(s * Fraction(x) for s, x in zip(sol[:n], inp)) + sol[n]
        if val != out:
            return None
    return tuple(sol)


class OrbitFinder:
    """Fit an exact record-orbit spec for one machine."""

    def __init__(self, code: str, steps: int = 200_000, cap: int = 2_000):
        self.code = code
        halted, self.stop_step, recs = simulate_records(
            code, steps=steps, cap=cap)
        self.halted = halted
        self.pairs = [
            (tuple(r1["blocks"]), tuple(r2["blocks"]),
             r2["step"] - r1["step"])
            for r1, r2 in zip(recs, recs[1:])
            if r1["blocks"] and r2["blocks"] and r1["side"] == r2["side"]]

    @staticmethod
    def _key(bin_, bout):
        return (len(bin_), len(bout),
                tuple(min(x, CAP) for x in bin_))

    def fit(self) -> dict | None:
        """Group, fit, verify. Returns the spec or None (fail-closed)."""
        groups: dict = {}
        for bin_, bout, dstep in self.pairs:
            groups.setdefault(self._key(bin_, bout), []).append(
                (bin_, bout, dstep))
        rules = {}
        for key, samples in groups.items():
            n_out = key[1]
            maps = []
            for t in range(n_out):
                fit = _solve_affine([(b_in, b_out[t])
                                     for b_in, b_out, _ in samples])
                if fit is None:
                    return None
                maps.append(fit)
            cost = _solve_affine([(b_in, d) for b_in, _, d in samples])
            if cost is None:
                return None
            rules[key] = {"maps": maps, "cost": cost,
                          "support": len(samples)}
        # final fail-closed replay of every observed transition
        for bin_, bout, dstep in self.pairs:
            rule = rules[self._key(bin_, bout)]
            n = len(bin_)
            for t, m in enumerate(rule["maps"]):
                val = sum(c * Fraction(x) for c, x in zip(m[:n], bin_)) + m[n]
                if val != bout[t]:
                    return None
            cval = (sum(c * Fraction(x)
                        for c, x in zip(rule["cost"][:n], bin_))
                    + rule["cost"][n])
            if cval != dstep:
                return None
        return {"code": self.code, "n_transitions": len(self.pairs),
                "n_rules": len(rules), "rules": rules}
