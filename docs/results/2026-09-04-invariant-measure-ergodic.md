# The offset process of R: invariant measure, mixing, and a hitting-probability probe

**Date:** 2026-09-04 · **Script:** `qgkit/bb6/offset_measure.py`
(exact integer map R, verified against
`docs/results/2026-08-26-renewal-map-analysis.md`)

These are rigorous numerics on the exact renewal map R at large
horizons. They characterize the ergodic object an invariant-measure
proof would use. None of it is a proof. Every quantitative claim below
carries its horizon.

## The object

At each renewal `(a, b)` the offset is `u = b - beta`, where
`beta = a-1` if `a` odd and `a-2` if `a` even, defined whenever `b` is
odd. Since `b` is odd and `beta` is even, `u` is always odd, verified
over 20.6 million fuse events and confirmed structurally. Branch T is
`b` even, branch C is `b < beta` (`u < 0`), branch F is the fuse
`b > beta` (`u > 0`). Death occurs when a fuse lands with
`u in {1, 3, 5}` (or `b <= 2`, or `b = 4`). The fatal band is thus the
three smallest positive odd offsets.

## 1. The offset invariant measure and the fatal-band measure

**The raw offset has no stationary distribution: it is transient.** The
fuse offset `u` scales with orbit size. Over the (6,13) orbit to 200,000
renewals the largest fuse offset had thousands of decimal digits, and
the offset grows with `beta` without bound. There is no invariant
probability measure for `u` on the integers.

**The scale-free object is `u / beta`.** Measured over 20,000 to 40,000
first-fuse events at fixed scale `beta ~ 2^40`, the normalized offset
`u / beta` has a limiting law that is heavy-tailed: median 0.57, mean
about 14, 95th percentile about 28, maximum about 26,000. Its density
near 0 is positive and finite, which is what fixes the hazard scale
below.

**The low-end offset law is flat, and the fatal band carries exactly
its uniform share.** Over an ensemble of 50,000 to 200,000 independent
orbits, offsets recorded at entry (before the fatal check, so fatal
offsets are included and there is no survivorship bias), the histogram
of small odd offsets `u = 1, 3, 5, ..., 41` is flat within Poisson
noise. In one run of 200,000 orbits the counts for `u = 1, 3, 5` were
708, 792, 768 against neighbors 7 to 41 all in the range 670 to 820,
and the number of `u in {1,3,5}` events equaled the number of diagonal
deaths exactly (2268), a direct consistency check that the measurement
is unbiased. The fatal band carries the local-uniform measure of three
odd values, no more and no less. There is no local obstruction
concentrating or excluding it.

**The fatal-band measure decays as `6 / size`.** With `beta` controlled
at the seed scale (first-fuse-only sampling, 30,000 events per scale),
the per-slot probability `P(u = specific odd value) = c / beta` has
`c = 1.90, 2.39, 1.96, 2.55` at scales `beta ~ 2^8, 2^12, 2^16, 2^20`,
stable near 2. Hence the fatal-band hazard per fuse is
`P(u in {1,3,5}) ~ 3 * 2 / beta = 6 / beta ~ 6 / size`. This confirms
the "hazard about 6/size" statement of
`docs/results/2026-08-26-almost-all-seeds.md` from the offset law
directly. The fatal band does not carry a stable positive measure; its
measure tends to 0 as orbits grow.

**The branch-symbol chain is stationary.** Over 200,000 renewals of the
(6,13) orbit the symbol frequencies are T 0.370, C 0.185, dC 0.185,
F 0.130, dF 0.131. The a-parity split (d versus D) is about 50/50. This
chain, unlike the raw offset, has a genuine stationary distribution.

## 2. Mixing verdict: YES, with finite memory

The branch-symbol sequence mixes. Evidence at horizon 120,000 to
200,000 renewals:

- **Entropy rate is finite and the process is near finite-order.** The
  conditional block entropy `h_n = H_n - H_{n-1}` drops to a plateau at
  about 0.423 nats per symbol from block length 3 onward
  (`h_1 = 1.52, h_2 = 0.68, h_3 = 0.425, h_4 = 0.425, ...`), the
  signature of an approximately order-2 Markov chain. The Kullback
  divergence of the empirical 3-gram law from an order-1 Markov
  prediction is 0.256 nats, so the chain is not order-1, but the
  entropy plateau places its effective memory at about order 2.
- **Autocorrelation decays fast.** The log-growth increments
  `d log(size)` have autocorrelation `-0.35` at lag 1, decaying below
  0.03 by lag 5 or 6. The normalized fuse offsets `log(u / beta)` have
  autocorrelation within 0.011 of 0 at every lag 1 through 8, that is,
  consecutive fuse offsets are essentially independent draws.
- **Factor complexity is `~1.6^n`, not Sturmian.** Measured
  `p(n) = 5, 10, 16, 26, 42, 68, 110, 178, 288, 466, 753, 1214, 1938,
  3066` for `n = 1..14`, ratio near 1.6, cross-checking the earlier
  measurement. The entropy rate 0.423 nats sits just below the
  topological value `log 1.6 = 0.470`, so the invariant measure has
  positive entropy and is not the measure of maximal entropy. The
  source of the golden-ratio complexity is the no-TT constraint: a
  terminate flips the parity of `b`, so T cannot follow T, the
  no-two-consecutive rule that generates Fibonacci counting.

The process has short-range memory and no detectable long-range
structure. A finitely-mixing symbol process with independent-across-fuse
offsets is exactly the setting in which a quantitative Borel-Cantelli
argument becomes reachable. The caveat is that mixing is measured here,
not proven; establishing that the symbol law is a genuine mixing Gibbs
or finite-order Markov measure is itself the hard content.

## 3. Martingale probe: a real drift, but no barrier

**`size = a + b` strictly increases from every non-fatal state.** The
per-branch increment is exactly: T gives `+3`; C gives `b - 1` (a odd)
or `b + 1` (a even), at least 2 since `b >= 3` off the fatal set; F
gives `a + 3` (a odd) or `a + 4` (a even), at least 9. Confirmed over
2 to 3 million random states: the size never fails to increase, minimum
increment 2. So `1 / size` is a pathwise supermartingale, and this fact
is provable. But the growth guaranteed this way is only additive
(`Delta size >= 2`), which gives a divergent hazard sum
`sum 6 / (size_0 + 2k)`. Additive monotonicity alone is not enough.

**The multiplicative drift is present and gives the summable bound.**
On the (6,13) orbit over 300,000 renewals, with `G = size' / size`, the
estimates `E[G^{-theta}]` are `0.968, 0.937, 0.883, 0.835, 0.793` at
`theta = 0.25, 0.5, 1.0, 1.5, 2.0`, all below 1, and the size never
shrinks (`d log size` in `[0.000, 0.423]`, mean 0.134). So `size^{-theta}`
carries the supermartingale drift needed. Combined with the hazard
`6 / size` this gives a summable series: the expected number of fatal
events from size `s` onward is at most
`6 / (1 - e^{-0.134}) / s ~ 48 / s`, reproducing the `~50/s` of the
almost-all-seeds analysis, and hence a hitting bound
`P(ever fatal) <~ 48 / size_0` under a random-seed model.

**No barrier supermartingale exists.** A hitting bound by optional
stopping across a barrier requires a nonneg supermartingale that is
large on the fatal set, which in turn requires the fatal set to be
approached gradually. It is not. Consecutive fuse offsets are
independent (autocorrelation of `log(u / beta)` within 0.011 of 0 at all
tested lags), and each fuse draws a fresh offset with finite density
near 0, so the fatal set is hit in one shot, not crossed. Exponential
offset tilts `exp(-theta u)` therefore have no useful supermartingale
drift and no size-independent barrier. The bound above is a first-moment
Borel-Cantelli bound, not an optional-stopping barrier bound.

**Honest status of the bound.** The `48 / size_0` bound is rigorous only
under a genuinely random model, either random seed (the almost-all-seeds
setting) or the offset modeled as an equidistributed random sequence.
The specific dossier-2/3 orbit is deterministic, so its
probability of ever being fatal is 0 or 1 and no martingale can bound
it. The two ingredients of the bound, the hazard `<= C / size` (offset
equidistribution) and the geometric size drift, are exactly the two
statements that remain unproven. This experiment shows they hold
numerically and fit together; it does not establish either.

## 4. The specific dossier-2/3 orbit is generic

The (6,13) orbit over 2,000,000 renewals is alive, at 386,709 bits, with
522,633 fuse events and a smallest fuse offset of `u = 9`, that is a
margin of 4 above the fatal band, the same margin reported at 100,000
renewals and unchanged across the twentyfold horizon extension. That
`u = 9` occurred exactly once in 2,000,000 renewals; the orbit reached
`u <= 11` once, `u <= 15` twice, `u <= 51` three times, `u <= 101` five
times, and `u <= 1001` nine times, and never produced `u = 7`. Close
approaches are rare and thin out consistently with the decaying hazard
`sum 6 / size`: the counts of approaches within a window grow only
logarithmically in the window while the size grows exponentially. The
dossier-3 C-entry seed (6,49) over 1,000,000 renewals is likewise alive
at 193,313 bits with a smallest offset `u = 11` (margin 6). Both orbits
graze the band and survive with no structural buffer, exactly as the
near-miss analysis found.

The orbit is statistically generic. Both (6,13) and dossier-3's C-entry
seed (6,49) match random large seeds (drawn near `10^5` to `10^6`) on
every measured invariant: stationary symbol law (T 0.369, C and dC
0.184, F and dF 0.131), entropy rate 0.423 nats, and mean log-growth
0.134 per renewal, all agreeing to three decimals across four orbits at
horizon 120,000, and the mean log-growth holds at 0.13402 for (6,13) to
2,000,000 renewals and 0.13399 for (6,49) to 1,000,000. The specific orbit shows no special structure that
would place it outside a typical-orbit measure argument, and none that
would let a measure argument single it out either.

## Verdict

- **Fatal-band measure:** the raw offset is transient with no stationary
  law; the fatal band `{1,3,5}` carries the local-uniform measure of
  three odd values, a per-fuse hazard of `6 / size` that decays to 0.
  There is no stable positive fatal-band measure and no local
  obstruction (horizons: 20.6M fuse events for the flat law, scales
  `2^8` to `2^20` for the `6/size` scaling).
- **Mixing:** yes. Finite short-range memory (effective order about 2 in
  the symbols, independent across fuse offsets), entropy rate 0.423 nats
  below the topological `log 1.6`, autocorrelations decaying to noise
  within about 5 lags (horizon 200,000 renewals).
- **Supermartingale:** `1 / size` is a genuine (pathwise) supermartingale
  from the strict size-monotonicity lemma, and `size^{-theta}` has
  multiplicative drift `E[G^{-theta}] < 1` for all tested theta; together
  with hazard `6 / size` these give `P(ever fatal) <~ 48 / size_0` under
  a random-seed model. No barrier supermartingale exists: the fatal set
  is hit in one shot from independent draws, not approached, so optional
  stopping across a barrier does not apply.
- **Is an invariant-measure proof within reach?** For almost-all-seeds,
  the mechanism is complete and consistent at these horizons: uniform
  hazard `6 / size`, geometric size drift, a summable first-moment
  bound. Turning it into a theorem requires proving offset
  equidistribution (hazard `<= C / size`) and the geometric drift as
  statements about the invariant measure, and proving the measure mixes.
  These are real, well-scoped analytic tasks with the map fully explicit,
  but they are not done here. For the specific (6,13) orbit an
  invariant-measure argument cannot decide it: the orbit is deterministic
  and generic, so a measure argument gives it the typical survival
  probability but no pointwise verdict. The honest position is unchanged
  from the almost-all-seeds analysis: the object a proof would use is
  characterized precisely, and the specific-orbit question remains a
  pointwise avoidance statement no measure argument reaches.

## Honest scope

Ensemble horizons: 50,000 to 200,000 orbits at horizon 300 to 400 for
the offset law and deaths; 30,000 first-fuse events per scale for the
`6/size` fit; specific-orbit horizons to 2,000,000 renewals for (6,13)
and 1,000,000 for (6,49).
Mixing statistics are single-orbit samples of the process at horizon
120,000 to 200,000. All "measure" and "mixing" statements are measured
properties at these horizons, not established properties of a proven
invariant measure.
