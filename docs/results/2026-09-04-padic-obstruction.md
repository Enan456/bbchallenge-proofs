# Non-Archimedean obstruction search for the renewal map: none exists

**Date:** 2026-09-04 · **Script:** `qgkit/bb6/padic_obstruction.py`
· **Builds on:** `docs/results/2026-08-26-renewal-map-analysis.md`
(no congruence invariant to mod 384) and `docs/results/renewal_analysis3.py`
(the exact renewal map `R`, `fatal`, and the residue BFS reused here).

## Question

Prior work established that no congruence invariant modulo `M ≤ 384`
separates the orbit of `(6, 13)` under `R` from the fatal set. This note
asks the sharper, genuinely non-Archimedean question:

> Does **any** p-adic invariant — a residue-class system at a prime power
> `2^k`, `3^m`, or a mixed `2^k·3^m`, or a p-adic **valuation/ball**
> constraint on the orbit — exclude the fatal set?

The two structurally relevant primes are **2** (the parity branch `b`
even/odd) and **3** (the Collatz multiplier: every deep branch multiplies
by 3). These are the only primes the map manufactures, so a
non-Archimedean certificate, if one exists, must live at 2, 3, or their
product.

**Verdict (measurement): NO.** The fatal set stays reachable at every
modulus tested, up to `2^12 = 4096` (2-adic), `3^7 = 2187` (3-adic), and
`2^5·3^5 = 7776` (mixed). No p-adic valuation confines the orbit or the
fatal gap to a separating ball. This **extends and strengthens** the prior
impossibility: there is no finite non-Archimedean certificate.

## Method and its soundness

A non-Archimedean (modular) invariant excluding the fatal set is a union
`S` of residue classes mod `M` such that (1) the seed's class lies in `S`,
(2) `S` is closed under the abstract transition taking **both** exit
branches — a purely modular predicate cannot see the magnitude comparison
`b < β` vs `b > β`, so it must be closed under both — and (3) `S` is
disjoint from every **fatal-compatible** class `F_M` (a class containing
some fatal integer point, via existential lift). The minimal such `S` is
exactly the BFS-reachable set `R_M`. Therefore:

- `R_M ∩ F_M = ∅` ⟹ an invariant **exists** at `M`.
- `R_M ∩ F_M ≠ ∅` ⟹ **no** modular invariant of any kind exists at `M`
  (every valid `S` contains the minimal `R_M`, which already meets `F_M`).

This is sound for the **negative** claim. The BFS uses a flat `bytearray`
seen-set (1 byte per class, state encoded `u·M + v`), which is what lets it
reach `M²` up to ~6·10⁷ classes. Note: because `R` contains **no halving**,
every branch is affine mod `M`; the abstraction is exact apart from the
magnitude-driven branch choice, which BFS over-approximates by taking both.

*Discrepancy note (honesty):* the fatal-compatible counts here exceed those
in the 2026-08-26 table (e.g. mod 384: 894 vs 512) because this script uses
a **broader** fatal-compatible definition — it also marks classes
witnessing `b ≤ 2` and `b = 4` (`T→1`), not only the diagonal window. A
larger `F_M` only strengthens a negative conclusion.

## Part 1 — extended residue BFS (measurement)

**Pure 2-adic, `M = 2^k`, k = 3..12:** reachable set is **FULL** at every
`k` (fraction 1.0000). The 2-adic abstraction carries **zero information**:
every residue pair is reachable, so it trivially cannot exclude the fatal
set. Fatal-compatible count grows as `≈ 7·2^k` (50, 106, 218, …, 28666 at
`M = 4096`).

**Pure 3-adic, `M = 3^m`, m = 2..7:** reachable fraction converges to
`≈ 0.192` (14/81, 128/729, …, 917833/4782969). This is the **mod-3
conservation law** deepening at higher 3-powers — the only genuine
non-Archimedean constraint the map has. It never zeroes the fatal set:
fatal-compatible = 10, 37, 124, 373, 1102, **3324** at `M = 2187`.

**Mixed `M = 2^k·3^m` (highest `2^5·3^5 = 7776`):** reachable fraction
depends only on the 3-power and is **below** the product of the pure
fractions — 2 and 3 structure are *not* independent (parity of `a` couples
to the mod-3 class through the offset `β = a − {1,2}`):

| 3-power in `M` | reachable fraction | example (`M`, fatal-compat) |
|---|---|---|
| `3^1` | 0.3333 | 384 → 894 |
| `3^3` | 0.0885 | 3456 → 2111 |
| `3^4` | 0.0558 | 5184 → 2015 |
| `3^5` | 0.0358 | 7776 → 1935 |

Fatal-compatible is **nonzero at every one of the 32 moduli tested.** No
`INVARIANT` tag was ever emitted.

## Part 2 — p-adic valuations along the true integer orbit (measurement)

Run of 200,000 renewals (52,255 deep-fuse events, orbit ~38,701 bits).

**The fatal window has no p-adic structure to exploit.** The fatal
condition in a deep-fuse is on the gap `g = b − β`. Since `b` is odd and `β`
is even, **`g` is always odd**, so `v₂(g) = 0` for the entire fatal window
`{1,3,5}` *and* for every safe gap `7, 9, 11, 13, …` alike — all sit in the
single 2-adic sphere `|g|₂ = 1`. **No 2-adic ball separates the fatal window
from the safe odd gaps.** 3-adically it is no better: `{1,3,5}` has
valuations `[0,1,0]` and units `[1,1,2]`, exactly matching the spread of the
safe gaps `7,9,11,13` (`v₃ = [0,2,0,0]`, units `[1,1,2,1]`) — both the fatal
and safe gaps populate every 3-adic ball. **No p-adic ball on the gap
excludes `{1,3,5}`.**

**The orbit is not p-adically confined.** Along the run, `v₂(b)` and
`v₃(b)` spread across all values with the geometric profile of an
equidistributing sequence (`v₂(b)`: 126128 zeros, 36692 ones, 18598 twos, …
≈ halving; `v₃(b)`: 133443, 44312, 14971, … ≈ thirding). The orbit visits
every p-adic ball; it is trapped in none. There is no valuation constraint
the orbit provably respects that also avoids the fatal condition.

## Part 3 — concrete witness: the real orbit enters fatal-compatible classes

Beyond the over-approximating BFS, the **true** integer orbit itself visits
fatal-compatible residue classes at every modulus (surviving each as an
integer, since a class-match is not an integer-match):

| M | 384 | 768 | 1536 | 2592 | 5184 | 7776 |
|---|---|---|---|---|---|---|
| distinct fatal-compatible classes visited | 327 | 295 | 179 | 109 | 64 | 43 |

So it is not merely that the abstraction *could* reach the fatal set — the
actual orbit *does* enter fatal-compatible classes, and survives, at every
scale. No modular predicate can fence the orbit out of the fatal set,
because the orbit is demonstrably on both sides of any such fence.

## Verdict

**No non-Archimedean invariant excludes the fatal set** (measurement, at
the tested scales). Specifically:

1. **2-adic:** the reachable set is *full* at every `2^k ≤ 4096` — the
   2-adic abstraction is vacuous. The fatal window `{1,3,5}` is 2-adically
   indistinguishable from all safe odd gaps.
2. **3-adic:** the mod-3 conservation law (reachable fraction → 0.192 at
   `3^m`, → 1/3 at div-by-3 mixed) is real and deepens with the 3-power,
   but the fatal set is reachable through it at every `3^m ≤ 2187`. No
   3-adic ball separates the gap window.
3. **Mixed `2^k·3^m`:** additional joint 2–3 structure shrinks reachability
   to as low as 0.0358, yet fatal-compatible stays nonzero up to
   `2^5·3^5 = 7776`, and the *real* orbit visits fatal-compatible classes at
   all of them.

This is a **negative result, and it is the expected and valuable one.** It
**extends** the 2026-08-26 impossibility from "no congruence invariant to
mod 384" to "no non-Archimedean certificate — congruence or p-adic
valuation — at any prime-power scale up to `2^12`, `3^7`, `2^5·3^5`."
Together with the earlier failures of congruence and rotation-rigidity, the
mechanical / non-Archimedean routes to an unconditional proof are now closed
with computational evidence. What remains is the Archimedean hard core: a
pointwise avoidance statement for a pseudorandom multiplicative integer map,
the same epistemic position as Collatz.

## Honest scope

These are measurements at the tested scales: residue BFS to `M = 7776`
(and pure `2^12`, `3^7`); 2·10⁵ renewals for the valuation and
witness analysis. They close the non-Archimedean route at these scales;
they are **not** an impossibility theorem for all moduli. The result found
no unexpected separating structure — only the already-known mod-3
conservation law, which does not touch the fatal window. No positive
invariant was manufactured; none exists in the range searched.
