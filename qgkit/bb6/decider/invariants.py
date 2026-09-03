"""Sound invariant searchers over affine branch systems.

The mathematical core of the certificate-emitting decider. A machine
law is modeled as a finite set of branches, each an affine map on an
integer tuple with an optional guard; the searchers return only
invariants VERIFIED symbolically in exact rational arithmetic.
Nothing here trusts simulation; callers stress results against raw
runs separately, and nothing becomes a decision until the law itself
is kernel-checked.
"""

from __future__ import annotations
from dataclasses import dataclass, field
from fractions import Fraction
from itertools import product


@dataclass(frozen=True)
class Branch:
    """x -> A x + b, applicable when guard(x) holds.

    guard_mod: optional (m, allowed_residue_vectors) restricting
    applicability by residues; None means the branch may fire from
    any state (the sound default when guards are unknown)."""
    matrix: tuple          # rows of Fractions/ints
    offset: tuple
    name: str = ""
    guard_mod: tuple | None = None

    def apply(self, x):
        return tuple(
            sum(Fraction(a) * Fraction(v) for a, v in zip(row, x))
            + Fraction(c)
            for row, c in zip(self.matrix, (x and self.offset) or
                              self.offset))

    def applies_residue(self, r, m):
        if self.guard_mod is None:
            return True
        gm, allowed = self.guard_mod
        if m % gm != 0:
            return True          # cannot refute at this modulus: sound
        return tuple(v % gm for v in r) in allowed

    def integral_on(self, m):
        """True if the branch maps integer vectors to integer vectors
        for every residue class mod m it can fire from (fractional
        coefficients may still be integral under residue guards)."""
        for r in product(range(m), repeat=len(self.offset)):
            if not self.applies_residue(r, m):
                continue
            y = self.apply(r)
            if any(v.denominator != 1 for v in y):
                return False
        return True


@dataclass
class AffineSystem:
    branches: list
    dim: int
    seed: tuple
    fatal_residues: dict = field(default_factory=dict)
    # fatal_residues: {m: set(residue vectors)} - states whose residue
    # lies in the set are (or may lead to) fatal; an invariant must
    # avoid them.


def congruence_search(sys_: AffineSystem, moduli=range(2, 65)):
    """Find (m, S): S a set of residue vectors mod m, closed under
    every applicable branch, containing the seed residue, disjoint
    from fatal residues at m (when provided). Returns list of hits
    (m, frozenset S). Sound: closure is checked over every residue in
    S under every branch that can fire there; branches with
    non-integral images at some residue in S disqualify the modulus
    (the abstraction cannot follow them)."""
    hits = []
    for m in moduli:
        fatal = sys_.fatal_residues.get(m, set())
        # grow S from the seed by closure; reject if it meets fatal
        seed_r = tuple(v % m for v in sys_.seed)
        if seed_r in fatal:
            continue
        ok = True
        S = {seed_r}
        frontier = [seed_r]
        while frontier and ok:
            r = frontier.pop()
            for br in sys_.branches:
                if not br.applies_residue(r, m):
                    continue
                y = br.apply(r)
                if any(v.denominator != 1 for v in y):
                    ok = False
                    break
                yr = tuple(int(v) % m for v in y)
                if yr in fatal:
                    ok = False
                    break
                if yr not in S:
                    S.add(yr)
                    frontier.append(yr)
            if len(S) == m ** sys_.dim:
                ok = False       # full space: vacuous, excludes nothing
        if ok and fatal:
            hits.append((m, frozenset(S)))
    return hits


def monotone_search(sys_: AffineSystem, coeff_range=range(-3, 4),
                    fatal_upper=None):
    """Find integer functionals f(x) = c . x with, for every branch,
    f(Ax + b) - f(x) >= 1 identically (checked symbolically: the
    linear part of the difference must be the zero functional or
    dominated appropriately; this searcher only accepts differences
    that are CONSTANT in x and >= 1, the unconditionally sound case).
    With fatal_upper = (c0): if every fatal state satisfies
    f(x) <= c0 and f increases by >= 1 per step from a seed with
    f(seed) > c0, the fatal set is never reached. Returns list of
    (coeffs, min_increment)."""
    hits = []
    n = sys_.dim
    for coeffs in product(coeff_range, repeat=n):
        if all(c == 0 for c in coeffs):
            continue
        incs = []
        good = True
        for br in sys_.branches:
            # f(Ax+b) - f(x): linear part must vanish identically
            lin = [sum(Fraction(coeffs[i]) * Fraction(br.matrix[i][j])
                       for i in range(n)) - Fraction(coeffs[j])
                   for j in range(n)]
            if any(v != 0 for v in lin):
                good = False
                break
            const = sum(Fraction(c) * Fraction(b)
                        for c, b in zip(coeffs, br.offset))
            if const < 1:
                good = False
                break
            incs.append(const)
        if good and incs:
            hits.append((coeffs, min(incs)))
    return hits


def stress(sys_: AffineSystem, invariant_m_S, steps=100000):
    """Iterate the system from its seed and confirm the congruence
    invariant holds on every visited state (guards permitting).
    Returns (ok, first_violation)."""
    m, S = invariant_m_S
    x = sys_.seed
    for k in range(steps):
        r = tuple(int(v) % m for v in x)
        if r not in S:
            return False, (k, x)
        fired = False
        for br in sys_.branches:
            if br.applies_residue(r, m):
                y = br.apply(x)
                if all(v.denominator == 1 for v in y):
                    x = tuple(int(v) for v in y)
                    fired = True
                    break
        if not fired:
            return True, None      # no branch: end of modeled orbit
    return True, None
