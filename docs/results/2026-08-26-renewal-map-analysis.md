# The renewal map: closed form, invariant search, rigidity tests

**Date:** 2026-08-26 · **Scripts:** session scratchpad
`renewal_analysis3.py` (verified against `metaStep`, itself validated
against 10⁹ raw steps)

## Task 1 — the closed form (DERIVED AND VERIFIED)

Taking C-entries (states `(a, b)` with `c = 3`) as the renewal section,
the exact renewal-to-renewal map is:

- **T** (`b` even, terminate round): `(a, b) → (a + 6, b − 3)`
- **deep** (`b` odd): set `(α, β) = (6, a−1)` if `a` odd, `(9, a−2)` if
  `a` even; then
  - if `b < β` (loop exits through `c`):
    `(a, b) → (α + 3(b−3), β − (b−3))`
  - if `b > β` (loop exits through `b`, fuse):
    `(a, b) → (α + 3β + 3, b − β − 4)`

Note `b` odd and `β` even always, so `b ≠ β`: the map is total off the
fatal set. Verified exactly against 30 ground-truth transitions of the
certified abstract orbit and by reproducing the orbit itself.

**The fatal set is the diagonal.** Death occurs exactly at:
`b ≤ 2`; or `b = 4` before a terminate; or a deep-fuse with
`b − β ∈ {1, 3, 5}` — i.e., **the two counters arriving almost equal**
(a window of width 5 around the diagonal). The conjecture
`SafeMetaOrbit` is: the orbit of `(6, 13)` under `R` never enters the
diagonal window.

## Task 2 — congruence-invariant search (NEGATIVE, informative)

Sound residue-abstraction BFS over `(a, b) mod M` for
`M ∈ {8, 16, 24, 48, 96, 192, 384}`:

| M | reachable | fatal-compatible |
|---|---|---|
| 8 | 64/64 | 32 |
| 24 | 192/576 | 32 |
| 96 | 3072/9216 | 128 |
| 384 | 49152/147456 | 512 |

A genuine **mod-3 conservation law exists** (reachable set is exactly
1/3 of residue pairs at moduli divisible by 3), but fatal-compatible
residues are reachable at every modulus tested. **No congruence-lattice
inductive invariant up to mod 384 excludes the fatal window.** An
unconditional proof cannot be a residue argument at this scale.

## Task 3 — rigidity tests (NEGATIVE, informative)

- **Factor complexity** of the branch-symbol sequence over 100,000
  renewals: `p(n) = 5, 10, 16, 26, 42, 68, 110, 178, 287, 463, 745,
  1196, 1892, 2945` for `n = 1..14` — growing like `≈ 1.6ⁿ`.
  A rotation/interval-exchange (Sturmian) coding would give
  `p(n) = n + 1`. **The renewal dynamics is not conjugate to a rigid
  system**; the continued-fraction/Diophantine route fails as stated.
- **Log-growth per renewal**: mean 0.134, standard deviation 0.138 —
  noise comparable to drift, the signature of a multiplicative
  pseudorandom walk (Collatz-like), not of a linearizable system.
- **Near miss**: over 100,000 renewals the orbit's minimum margin above
  the fatal window is **4**. The orbit is not bounded away from death;
  it grazes the diagonal and survives. Any proof must control
  arbitrarily close approaches — there is no structural buffer.

## Verdict

The reduction is as sharp as it can be made, and the two mechanical
routes to an unconditional proof are now *closed with evidence*, not
just suspicion:

1. No small congruence invariant (task 2).
2. No rotation rigidity (task 3).

What remains is exactly the hard core: a pointwise avoidance statement
for a pseudorandom multiplicative integer map — the same epistemic
position as Collatz, with three mitigations: the map is explicit and
total, the fatal set is a finite union of lines near the diagonal, and
a mod-3 conservation law plus the certified reduction give any future
attempt a rigid, machine-checked foundation. Realistic near-term
products: a Tao-style almost-all-seeds theorem for `R` (publishable,
does not decide our seed), certified astronomical runtime lower bounds
for the machines, and the modular-surface reformulation (fatal window
as horoball avoidance) as a bridge to the badly-approximable-numbers
community.

## Honest scope

Negative results are at the tested scales (mod ≤ 384; 10⁵ renewals for
complexity; 10⁸ episodes for orbit survival). They close routes at
these scales; they are not impossibility theorems.
