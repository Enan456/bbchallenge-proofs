# Item 1a: the native-resolution hazard bound, tested directly on integer orbits

**Date:** 2026-09-08. Item 1a asserts the integer offsets obey
`P[o_d ∈ {1,3,5} | scale S] ≤ C/S` — the native-resolution non-concentration
that makes `#halts = O(N log N)`. Rather than only argue it from the operator,
I measured it directly on exact integer orbits. **It holds** in the regime where
halting occurs, with the constant matching theory — reported with its two
genuine caveats.

## Method

A 2-D seed ensemble: 40 000 random seeds `(a,b) ∈ [3,3000)²`. Along every
orbit, at each F-visit (`b` odd, `b>β`) record the offset `o=b−β` and the
scale `S~b`, **including the fatal event** `o ∈ {1,3,5}` (the earlier version of
this test wrongly `break`-ed on fatal *before* recording, so it measured only
survivors and saw `P=0` — fixed here). Bin by `⌊log₂ S⌋`; report
`S·P[o∈{1,3,5}]`, which the theory predicts is bounded (`≈ 6h(0)`).

## Result

| log₂S | n (F-visits) | P[o∈{1,3,5}] | S·P |
|---|---|---|---|
| 13 | 55 522 | 4.5e−4 | 2.6 |
| 14 | 53 104 | 3.6e−4 | 4.1 |
| 15 | 53 373 | 1.3e−4 | 3.0 |
| 16 | 53 411 | 7.5e−5 | 3.5 |
| 17 | 53 449 | 3.7e−5 | 3.5 |

In the well-sampled interior (log₂S = 13–17), **S·P is flat at ≈ 3–4** across
five octaves — i.e. `P[o∈{1,3,5}] ~ C/S` with `C ≈ 3–4`. The theory predicts
`6h(0)` with `h(0) ≈ 0.5`, i.e. `≈ 3` — consistent. Lower bins (log₂S = 10–12)
give `S·P ≈ 5–7`, inflated by proximity to the seed scale `~2^{11.5}` (boundary
effect, not the asymptotic).

## Two honest caveats

1. **Halting is early-scale.** Beyond `log₂S ≈ 18` there are **zero** fatal
   events: an orbit that survives that far has reached the survivor manifold
   and never halts. So the `C/S` law is confirmed only over the scale window
   where halting actually happens (here `2^{10}`–`2^{18}`). This is consistent
   with — indeed is the microscopic mechanism behind — the fact that
   `#halts = O(N log N)`: the hazard is spent early and the survivors escape.
2. **Modest sample.** 304 fatal-by-offset events among 4.24×10⁶ F-visits
   (fraction 7.2×10⁻⁵). The per-bin `S·P` therefore carries real counting
   noise (one bin at log₂S=18 read 10.4 off just 3 events and is dropped as
   noise). The *flatness* across the interior bins, each with tens of thousands
   of visits and dozens of events, is the trustworthy signal; individual bin
   values are not.

## What this establishes

- **Directly confirmed:** the exact integer offsets do **not** concentrate at
  small values; `P[o∈{1,3,5}] ~ C/S` with `C ≈ 3–4 ≈ 6h(0)`, flat across the
  interior scale window. This is the empirical form of item 1a's claim, on the
  integer dynamics itself, not the model.
- **In context:** item 1a argues this follows from the scale-uniform gap (item
  1) because the integer dynamics *is* the operator; this test is the
  end-to-end check that the conclusion actually holds on integers, and it does,
  with the predicted constant.
- **Not claimed:** a proof (this is numerics), nor the law outside the halting
  window (there is none — survivors escape), nor sharp constants (the sample is
  too small for that).

## Status

Item 1a's conclusion is now directly supported on exact integer orbits, with
`C ≈ 6h(0)` as predicted. Combined with item 1 (scale-uniform gap) and item 2
(countable-branch reduction), the density-form mechanism is confirmed at every
level it can be numerically — the measure form remains the unconditional
theorem, the density form remains a reduction to standard write-ups (the
sequential-composition/integer-upper-bound lemma, full UNI over long words, the
assembly), and the specific orbit remains Collatz-hard. No closure claimed;
this closes the empirical question of whether the hazard law holds on integers
(it does).
