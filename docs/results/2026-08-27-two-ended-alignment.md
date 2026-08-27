# Two-ended emulation for dossier-3: MIP*-inspired alignment

**Date:** 2026-08-27 · **Script:** `docs/results/two_ended2.py`

## 1. The MIP* = RE read-through, and what we borrow

[MIP\* = RE](https://arxiv.org/abs/2001.04383) (Ji–Natarajan–Vidick–
Wright–Yuen) proves that a classical polynomial-time verifier
interacting with two entangled provers can verify any recursively
enumerable statement — the halting problem included. Its mechanisms
([overview](https://scottaaronson.blog/?p=4512),
[CACM](https://cacm.acm.org/research/mip-re/)):

- **History-state alignment**: the verifier forces two isolated provers
  to hold consistent snapshots of a claimed computation history,
  cross-checked at sampled points.
- **Gap-preserving recursive compression**: a game about a long
  computation is compressed into a smaller game about a verifier that
  itself checks a compressed game — verification cost decouples from
  runtime.
- Zero-gap variants reach Π₂⁰
  ([Mousavi–Nezhadi–Yuen](https://arxiv.org/abs/2002.10490)), the
  level where non-halting claims live.

**Our classical, certified analogue.** Prover A = forward emulation
from the anchor (the certified orbit). Prover B = backward emulation
from the halting event (the halt cone). Verifier = an in-between
solver checking whether any alignment exists: the machine halts iff
forward(t) meets the backward cone at some t. Our compression is the
episode/orbit certification — one theorem per unbounded episode.

## 2. Machine B1: the raw halt cone of dossier-3

Dossier-3 halts only in state C reading 0. Backward BFS over
predecessor *constraint patterns* (partial configurations) gives the
exact family counts by depth:

```
1, 1, 1, 1, 1, 3, 3, 5, 3, 3, 5, 7, 7, 13, 11, 13, 17, 23, 29, 43,
46, 60, 75, 107, 134
```

**Alignment result (raw level):** every one of the 134 depth-24
families requires at least three 0s within a six-cell window — a
pattern no certified spawn-entry shape (`holeTape`: isolated holes in
a 1-field) can satisfy. The backward cone and the forward shapes are
provably incompatible 24 raw steps from death. This is a finite,
checkable statement and a natural candidate for a Lean lemma.

## 3. Machine B2: the abstract cone is a Fibonacci tree

At the renewal level, dying-within-k is exactly a union of integer
line families (symbolic preimages of the fatal set under the verified
map R, computed with parity/divisibility reparametrizations). Counts
by depth:

```
9, 19, 31, 50, 81, 131, 212, 343, 555, 898, 1453, 2351, 3804
```

From depth 2 onward these satisfy **L(k) = L(k−1) + L(k−2) exactly** —
the backward death tree is a Fibonacci tree, branching at the golden
ratio φ ≈ 1.618. This matches the forward factor complexity
(~1.6ⁿ) measured independently: *the same constant governs both ends*,
and its combinatorial source is visible — a terminate step flips the
parity of b, so T can never follow T, which is precisely the
no-two-consecutive constraint that generates Fibonacci counting.

Consequences: the dying set now has an exact generating description
(φᵏ line families of dimension 1), which makes the finite-horizon part
of the almost-all-seeds argument fully structural: density of dying-
by-k in a box of side X is ≤ C·φᵏ/X, while forward sizes along
surviving orbits grow like e^{0.134k} per renewal — the two growth
rates from the two ends are the entire Borel–Cantelli mechanism.

## 4. The verifier: alignment run

20,000 forward dossier-3 renewal states (from its first C-entry,
normalized (a,b) = (6,49)) were tested for exact membership against
all 9,937 cone families of depths 0–12. **Zero alignments.** Every
tested forward state is therefore more than 12 renewals from death —
a certified-empirical *time margin*, complementing the value margin
(distance ≥ 4 above the diagonal) measured earlier.

## 5. Plan forward

1. Deepen B2 (dedup + normal forms) toward depth ~30; the Fibonacci
   law predicts ~1.3M families — prune by feasibility.
2. Prove the Fibonacci recurrence for L(k) (combinatorial lemma on
   branch words without TT).
3. Lean-certify the raw-cone incompatibility lemma (depth-24, finite
   case analysis — our generators can emit it).
4. Alignment as a standing monitor: every future forward extension of
   the orbit is checked against the cone automatically.

## Honest scope

Raw-cone incompatibility is machine-checked arithmetic in Python, not
yet Lean. The Fibonacci law is observed exactly for depths 2–12 and
explained mechanistically; it is not yet a theorem. Alignment horizons
are what we ran: 20,000 forward states × depth-12 cone.
