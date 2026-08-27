# Almost all seeds survive: the density-zero theorem for R, empirically

**Date:** 2026-08-26 · companion to
`2026-08-26-renewal-map-analysis.md`

## Statement (empirical, quantified)

For the verified renewal map `R`, let `D` be the set of seeds
`(a, b) ∈ ℤ₊²` whose orbit ever enters the fatal set. Then:

- **Exact enumeration** of every seed in `[X, 2X)²` for
  `X = 16 … 256`: the dying fraction is `≈ 12/X`
  (density × X = 8.1, 9.7, 10.7, 11.7, 12.3 — a slowly-varying
  constant, possibly with a log factor).
- **Sampled sweep** to `X = 2¹⁶` agrees: `p_die × 2ʲ ≈ 10–13`
  throughout, with zero observed deaths for `j ≥ 14` at 400
  samples/box.

So `D` has natural density zero, with the quantitative rate
Borel–Cantelli predicts. *Almost all seeds survive; our machines'
seeds are typical survivors, not exceptions.*

## The mechanism, verified in three parts

1. **Early-game only.** In exact enumeration, `die ≤ 50` equals
   `die ≤ 500` at every box size: every death happens in the first
   fifty renewals. Once the counters are large, orbits never die
   (within all tested horizons).
2. **Uniform hazard at the diagonal.** Across 30,000 random seeds,
   fatal fuse-offsets {1,3,5} occur at the same per-value rate
   (37 total) as their non-fatal odd neighbors 7–15 (≈ 15–18 per
   value) — the offset distribution near the diagonal is consistent
   with uniform, fatal values included.
3. **Exponential escape.** Sizes grow by a factor `e^0.134` per
   renewal on average, so the per-renewal hazard `≈ 6/size` sums
   geometrically along any surviving orbit: total remaining hazard
   from size `s` is `≈ 50/s`. Death is an early-game phenomenon;
   survival compounds.

## A methodological confession worth keeping

Our first hazard measurement reported **zero** fatal-window hits in
208,173 fuse events (equidistribution predicted ~738), which briefly
looked like a hidden invariant making the diagonal unreachable — a
proof of `SafeMetaOrbit` in one move. It was **survivorship bias**:
offsets were logged only on steps actually taken, and a fatal offset
is a death, checked *before* the step — so fatal offsets could never
appear in the log. Wald's bomber armor, reproduced faithfully in our
own pipeline. The corrected instrumentation (count offsets at entry,
deaths included) restores perfect consistency with uniform hazard.
Backward analysis confirms it: every fatal offset has feasible
predecessors; there is no local obstruction.

## What a rigorous version needs

The finite-horizon part is exact lattice counting over a finite union
of lines (mechanical; even formalizable). The infinite tail needs a
hazard bound along orbits — worst-case additive growth (`size + 3`
per step) gives only a divergent `Σ 1/(X+3k)`, so the tail requires
the *typical* multiplicative growth, i.e. an invariant-measure or
martingale argument in the style of Tao's Collatz result. That is a
real but well-scoped project: the map is explicit, total, piecewise
affine, with verified uniform hazard — considerably more structure
than Collatz offers.

## Honest scope

Empirical horizons: exact to `X = 256`, sampled to `X = 2¹⁶`,
per-orbit horizons 500–20,000 renewals with a size-cap justification
(residual hazard `< 3·10⁻¹²`). "Almost all" here is a measured
density statement plus a verified mechanism, not yet a theorem.
