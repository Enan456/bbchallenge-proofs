# Offset equidistribution at the diagonal: empirical evidence for the almost-all lemma

**Date:** 2026-09-04. Direct measurement of the one lemma the
"almost-all seeds never die" theorem was reduced to in
`2026-09-04-modular-dictionary-probe.md`. Runs the exact verified
renewal map `R` (`renewal_analysis3.py`). Script:
`qgkit/bb6/offset_equidist.py`. **This is empirical evidence, not a
proof** — see the Honesty box.

## The lemma under test

> As the trajectory crosses the diagonal (`b` passing `beta`), the
> offset `o = b - beta` equidistributes finely enough that the fraction
> of crossings landing in the width-3 fatal window `{1,3,5}` is summable
> along almost every orbit.

An **above-diagonal event** (potential fatal crossing) is a renewal with
`b` odd and `b > beta` — exactly the `F`-branch. At every such event
`o = b - beta` is a **positive odd** integer (both `a`-parities give
`beta` even, `b` odd). The orbit dies iff `o in {1,3,5}`.

## Ensemble

505 reproducible seeds, no randomness: 300 from the deterministic family
`(6+4k, 13+8k)`, plus 205 "large" seeds obtained by iterating `R` 40
steps from that family. Each orbit run up to 3000 renewals. Totals:
**395,330 above-diagonal events**, 556,933 `C`, 556,759 `T`; 503/505
orbits survived the full 3000 renewals, 2 died by diagonal, 0 by axis.

---

## (1) Offset mod-M uniformity over admissible (odd) residues

`o` is always odd, so the admissible residues mod even `M` are the odd
ones. Deviation reported plainly as `max |frac − 1/k|` (k = #admissible
residues) alongside chi-square/dof.

| M | #resid k | N | chi2/dof | max\|frac−1/k\| | 1/k |
|---|---|---|---|---|---|
| 2 | 1 | 395,328 | — | 0.0000 | 1.0000 |
| 4 | 2 | 395,328 | 0.018 | 0.0001 | 0.5000 |
| 6 | 3 | 395,328 | 7.006 | 0.0026 | 0.3333 |
| 8 | 4 | 395,328 | 1.801 | 0.0011 | 0.2500 |
| 16 | 8 | 395,328 | 1.386 | 0.0011 | 0.1250 |
| 384 | 192 | 395,328 | 1.718 | 0.0004 | 0.0052 |

Residue fractions mod 6: `{1: 0.3359, 3: 0.3311, 5: 0.3330}`; mod 8:
`{1: 0.2491, 3: 0.2511, 5: 0.2508, 7: 0.2490}`.

**Reading.** The offset phase is uniform over admissible residues to
**better than 0.3% in every modulus tested**, down to width-1/192 bins
at M=384. The only statistically resolved wrinkle (N is ~4·10^5, so tiny
biases show) is a **+0.8% relative excess at residue 1 mod 6**
(chi2/dof 7.0). That is a residue-class bias, not a small-integer bias,
and does not touch the safety margin — which is governed by the density
of *small* offsets, measured next.

## (2) Fatal-window scale and hit fraction

Survivor offsets (395,328 of them): min **7**, median ~6·10^90 (the
median grows with the orbit — offsets scale geometrically), max ~10^170.
The 12 smallest offsets ever seen across the whole ensemble:
`[7, 9, 9, 13, 13, 13, 17, 17, 19, 19, 21, 21]` — survivors sit just
outside the deleted `{1,3,5}` window and the low tail is flat, not piled
up. Occupancy of successive width-3 odd windows:

| window | survivor fraction |
|---|---|
| {1,3,5} (FATAL) | 0.00000 (survivors never here) |
| {7,9,11} | 0.0000101 |
| {13,15,17} | 0.0000106 |
| {19,21,23} | 0.0000156 |
| {25,27,29} | 0.0000106 |
| {31,33,35} | 0.0000131 |

Flat near zero. Per-odd-integer density there is `rho ≈ 2.53·10^-6`, so
the model per-crossing fatal probability is `3·rho ≈ 7.6·10^-6`. The
**measured** per-crossing diagonal-death fraction is `2 / 395,330 =
5.06·10^-6` — consistent to within small-count (Poisson) noise (≈3
deaths expected, 2 seen).

**Scaling with size.** `o/beta` has median **1.72** (mean 23.5, heavy
right tail); `o/b` median **0.63**. So the offset scale tracks `beta ≈ a`.
Binning crossings by `bitlen(a)` (see script output) confirms mean
`o/beta` is **stationary at ≈ 10–30 across all bit-lengths 7…600** — the
offset keeps the same *relative* spread as the numbers grow by 180
orders of magnitude. If `o` were `Uniform(0, 1.72·beta]` the hit rate
would be `6/(1.72·beta) ≈ 3.49/beta`, i.e. `C ≈ 3.5`; the direct
density estimate gives the equivalent `3·rho·beta`-form. This is the
same **≈ C/size hazard** family as the known per-renewal `~1.74/size`
(same order; the factor-2 gap is the `o/b`≈0.63 range correction).
The essential point for the lemma is that the per-crossing hazard
**decays like 1/size while `size` grows geometrically**.

## (3) Summability

Per-orbit sum of the model fatal-probabilities `Σ 3/(beta/2)` over its
crossings: min 0.000, median **0.017**, mean 0.049, p99 0.585, max 1.88
— finite for every orbit, small for the typical one. The tail (average
over orbits of hazard summed from crossing index `k` onward) collapses
**geometrically**:

| from crossing k | avg remaining hazard |
|---|---|
| 0 | 4.86·10^-2 |
| 1 | 3.08·10^-2 |
| 2 | 2.47·10^-2 |
| 5 | 9.51·10^-3 |
| 10 | 9.62·10^-4 |
| 20 | 3.50·10^-5 |
| 40 | 2.36·10^-9 |
| 80 | 7.76·10^-17 |

Each factor-of-2 in crossing index drops the tail by roughly two orders
of magnitude — because `beta` grows geometrically, `Σ 1/beta_i`
converges fast. **Summability holds decisively** in the sample.

## (4) Horocycle-drive check — mechanism CORRECTED

The prior probe conjectured the phase is randomized by the parabolic
generator `T` *sweeping* the offset (`b -> b-3` repeatedly). **The
measurement refutes that literal mechanism:** `T` requires `b` even and
sends `b -> b-3` (odd), so `T` **can never occur twice in a row** — the
T-run-length distribution is `{1: 556759}`, exclusively singletons.
There is no multi-step parabolic sweep. Consecutive above-diagonal
events are separated by a median of **3** renewals (mean 3.82, max 41),
a short interleaving of single `T`, `C`, and `F` moves.

So the equidistribution in (1) is **not** horocycle-sweep-driven; it is
produced by the **mixing of the three-generator semigroup** as a whole
(consistent with the short-range memory / block-entropy 0.423 measured
in `2026-09-04-invariant-measure-ergodic.md`). The *outcome* the lemma
needs — a uniform offset phase — holds; the *proposed mechanism* does
not, and any proof attempt must lean on semigroup mixing, not on a
parabolic sweep.

## (5) Certified seed (6,13): generic, hence undecidable by this route

Over 3000 renewals `(6,13)` produced 781 above-diagonal events. Its
smallest offsets: `[9, 13, 35, 59, 67, 157, 265, 593, 947, 2557]` —
**min offset 9**, reproducing the prior probe's "≥9 over 2043 renewals"
margin. Its offset phase matches the ensemble: mod-6 split
`{1: 0.319, 3: 0.328, 5: 0.353}` vs ensemble `{1: 0.336, 3: 0.331,
5: 0.333}`.

`(6,13)` is **generic**: its offset distribution is statistically
indistinguishable from the ensemble. That is precisely why this argument
**cannot** decide it. Equidistribution is an almost-all statement; it is
silent on whether this one trajectory's phases forever avoid `{1,3,5}`.
The `min = 9` margin is a property of one generic orbit's realized
phases, not a theorem. **The Collatz-hard wall for the specific machine
is untouched.**

---

## Verdict

Empirically, **the offset-equidistribution lemma holds**, and strongly:

- offset phase uniform over admissible residues to <0.3% up to M=384;
- density of small offsets flat, giving per-crossing hazard
  `≈ 7.6·10^-6` matching the observed death fraction `5.06·10^-6`;
- per-crossing hazard `≈ C/size` (C ≈ 3.5, same family as `1.74/size`)
  with `size` growing geometrically;
- per-orbit hazard sum finite (median 0.017) with a geometric tail;
- the one caveat: a real but tiny (+0.8%) residue-1-mod-6 phase bias,
  and a **corrected mechanism** — no parabolic sweep exists (T never
  repeats); equidistribution comes from full semigroup mixing.

## Honesty box

- This is **empirical evidence** that the equidistribution lemma holds
  (and a measurement of *how well* — sub-0.3% phase uniformity,
  geometrically summable hazard). It is **not a proof**. A proof would
  need to establish the offset phase equidistribution and the
  small-offset density bound rigorously for the three-generator
  `GL(2, Z[1/3])` semigroup, unconditionally.
- The finding bears **only** on the **almost-all-seeds** theorem. It
  says **nothing** about the unconditional non-halting of any specific
  machine. The certified seed `(6,13)` is measured to be **generic**,
  which is exactly the reason this route **cannot** decide it — the
  same Collatz-hard wall as every prior finding.
- One prior conjecture is **refuted**: the parabolic generator `T` does
  not sweep the offset (it cannot occur twice consecutively). The
  equidistribution outcome survives; its mechanism is semigroup mixing,
  not a horocycle sweep.
- No Lean file, no other results doc, and no certificate is upgraded by
  this measurement.
```
Reproduce:  python3 qgkit/bb6/offset_equidist.py   (~2s, deterministic)
```
