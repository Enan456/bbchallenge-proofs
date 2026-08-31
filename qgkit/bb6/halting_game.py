"""The halting game: a classical two-prover encoding of the certified
dossier-2/3 verification, modeled on the MIP* = RE mechanism.

Claim under verification: "the machine halts within K renewals."

Two isolated provers each commit to a claimed history
H = (s_0, ..., s_K) of renewal states s_i = (a_i, b_i), plus a halt
index k*.  The verifier:

  1. seed check     : s_0 equals the certified anchor;
  2. law checks     : r indices j sampled uniformly; each check asks
                      prover A for (s_j, s_{j+1}) and prover B for
                      s_{j+1}, and verifies both cross-consistency
                      and R(s_j) = s_{j+1} via the closed-form
                      renewal map (O(1) per check: this is the
                      compression step, standing on the certified
                      episode theorems rather than on replay);
  3. terminal check : s_{k*} must lie in the fatal set, which the
                      certified lethality result converts into an
                      actual halt within about fifty raw steps.

Completeness: if the machine halts within K renewals, honest provers
present the true history and win with probability 1.

Soundness mechanism: R is deterministic and s_0 is fixed, so the only
law-consistent history is the true orbit; the true orbit's minimum
distance above the fatal window over the tested horizon is 4, so the
terminal check fails on it.  A winning strategy therefore needs at
least one seam (an index j with R(s_j) != s_{j+1}), and each sampled
law check catches a single seam with probability 1/K, giving value
at most (1 - 1/K)^r.
"""

from __future__ import annotations
import random

SEED = (6, 13)


def R(a, b):
    if b % 2 == 0:
        return a + 6, b - 3
    alpha, beta = (6, a - 1) if a % 2 == 1 else (9, a - 2)
    if b < beta:
        return alpha + 3 * (b - 3), beta - (b - 3)
    return alpha + 3 * beta + 3, b - beta - 4


def fatal(a, b):
    if b <= 2:
        return True
    if b % 2 == 0:
        return b == 4
    beta = (a - 1) if a % 2 == 1 else (a - 2)
    return b > beta and b - beta in (1, 3, 5)


def true_orbit(K):
    orb = [SEED]
    a, b = SEED
    for _ in range(K):
        a, b = R(a, b)
        orb.append((a, b))
    return orb


class HonestProver:
    """Presents the true orbit.  Cannot name a fatal index."""

    def __init__(self, orbit):
        self.orbit = orbit

    def snapshot(self, j):
        return self.orbit[j]

    def halt_index(self):
        for i, (a, b) in enumerate(self.orbit):
            if fatal(a, b):
                return i
        return None


class SeamForger(HonestProver):
    """Follows the true orbit to a chosen seam m, then splices a
    fabricated fatal state at m+1.  Exactly one law violation."""

    def __init__(self, orbit, m):
        super().__init__(orbit)
        self.m = m
        a, _ = orbit[m + 1]
        beta = (a - 1) if a % 2 == 1 else (a - 2)
        self.forged = (a, beta + 1)          # diagonal offset 1: fatal

    def snapshot(self, j):
        if j == self.m + 1:
            return self.forged
        return self.orbit[j]

    def halt_index(self):
        return self.m + 1


def play(prover_a, prover_b, K, r, rng):
    """One round of the game.  Returns (accept, reason)."""
    if prover_a.snapshot(0) != SEED or prover_b.snapshot(0) != SEED:
        return False, 'seed'
    k = prover_a.halt_index()
    if k is None or k != prover_b.halt_index():
        return False, 'no-halt-claim'
    sk = prover_a.snapshot(k)
    if sk != prover_b.snapshot(k) or not fatal(*sk):
        return False, 'terminal'
    for _ in range(r):
        j = rng.randrange(K)
        sj = prover_a.snapshot(j)
        sj1_a = prover_a.snapshot(j + 1)
        sj1_b = prover_b.snapshot(j + 1)
        if sj1_a != sj1_b:
            return False, 'cross'
        if R(*sj) != sj1_a:
            return False, f'law@{j}'
    return True, 'accept'


if __name__ == '__main__':
    K = 100_000
    rng = random.Random(7)
    orbit = true_orbit(K)
    n_fatal = sum(1 for s in orbit if fatal(*s))
    print(f"true orbit: K={K}, fatal states on it: {n_fatal}")

    honest = HonestProver(orbit)
    acc, why = play(honest, honest, K, 64, rng)
    print(f"honest provers, forever-running machine: accept={acc} "
          f"({why})  [no false acceptance possible: no fatal index]")

    print(f"{'r':>9} {'accept rate':>12} {'(1-1/K)^r':>12}  trials")
    for r, trials in ((64, 4000), (1024, 2000), (16384, 400),
                      (262144, 40), (1048576, 12)):
        n_acc = 0
        for t in range(trials):
            forger = SeamForger(orbit, rng.randrange(K - 1))
            a1, _ = play(forger, forger, K, r, rng)
            n_acc += a1
        pred = (1 - 1 / K) ** r
        print(f"{r:>9} {n_acc / trials:>12.4f} {pred:>12.4f}  "
              f"{trials}", flush=True)
