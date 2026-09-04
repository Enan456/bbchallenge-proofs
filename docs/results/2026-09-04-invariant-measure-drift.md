# Invariant-measure program on R: drift search and tail-hazard scaffold

**Date:** 2026-09-04 · **Script:** `qgkit/bb6/lyapunov_search.py`
(reusable) · companion to `2026-08-26-renewal-map-analysis.md` and
`2026-08-26-almost-all-seeds.md`

## Status banner

Everything below is a NUMERICAL SCAFFOLD. It builds the quantitative
objects a Tao-style proof would consume (a drift function, a per-renewal
hazard bound, a convergent tail sum) and measures them at stated
horizons. It does NOT constitute a proof of anything, neither the
almost-all-seeds density statement nor the survival of the specific
`(6, 13)` orbit. Section 3 states exactly what is still missing.

The map is the verified renewal map R (T, C, F branches) with fatal set
`b <= 2`, `b = 4`, and deep-fuse offset `b - beta in {1, 3, 5}`. Its
definition is reproduced at the top of the script.

## 0. Growth rate (re-verified, horizon 200,000 renewals)

The true orbit of `(6, 13)` was run 200,000 renewals under exact bigint
arithmetic (final size 38,700 bits, no death). Per-renewal log-growth of
the size `s = a + b`:

- mean `r = 0.13411`, standard deviation `0.13845`, range `[0, 0.4229]`.

The mean matches the earlier report of 0.134 to five figures. The
standard deviation is comparable to the mean, the signature of a
multiplicative pseudorandom walk rather than a linearizable system.

## 1. Foster-Lyapunov drift search

### 1.1 Framing correction

The textbook Foster-Lyapunov drift condition (`E[V(next) - V] <= -eps`
outside a compact set) certifies POSITIVE RECURRENCE, that is, the chain
returns to a compact core. That is the wrong target here, and the search
for such a `V` is expected to fail, for a structural reason worth stating
plainly: the size drifts to infinity (Section 0), so R is TRANSIENT, and
no nonnegative `V` growing with size can have uniformly negative drift.
The correct object is a Lyapunov function for TRANSIENCE, a bounded
nonnegative supermartingale outside a compact set (Foster's transience
criterion). That is what the search below actually finds.

A second point, equally important and equally honest: transience alone
does NOT avoid the fatal set. The diagonal window `b - beta in {1, 3, 5}`
is present at EVERY size scale, not only near the origin. Escaping to
infinity does not escape the diagonal. So the drift function is
necessary background structure, not the mechanism of survival. The
mechanism is the tail-hazard sum of Section 2.

### 1.2 Metrics measured

Because sizes reach tens of thousands of bits, raw differences of
candidate functions overflow floating point. The script instead computes
overflow-safe drift metrics through exact ratios `rho = s'/s` (Python
true division of bigints returns a correct float):

- `log_rho = log(s'/s)` is the one-step drift of `V = log(size)`.
- `s * D(1/s) = 1/rho - 1` is `size` times the drift of `V = 1/size`.
- `D(u/s)` is the drift of the normalized fuse offset `u/(a+b)`.

### 1.3 Results

Along the true orbit, stratified by size band (bits), 200,000 renewals:

| band | `log_rho` (drift of log s) | `s * D(1/s)` (drift of 1/s, scaled) |
|---|---|---|
| 16 bit | +0.1256 | -0.1114 |
| 64 bit | +0.1560 | -0.1354 |
| 256 bit | +0.1132 | -0.0992 |
| 1024 bit | +0.1663 | -0.1445 |
| 4096 bit | +0.1463 | -0.1258 |
| 16384 bit | +0.1015 | -0.0908 |

Over a visited-state ensemble (states harvested by running R from random
seeds and binned by size band `[s, 2s)`, 3,000 states per band):

| band | `log_rho` | `s * D(1/s)` |
|---|---|---|
| `[1e3, 2e3)` | +0.1448 | -0.1267 |
| `[1e4, 2e4)` | +0.1368 | -0.1196 |
| `[1e5, 2e5)` | +0.1349 | -0.1179 |
| `[1e6, 2e6)` | +0.1343 | -0.1175 |

### 1.4 Best drift function found

`V(a, b) = 1 / (a + b)`.

It is nonnegative, bounded above (by `1/s_min`), tends to 0 at infinity,
and its measured one-step drift is uniformly NEGATIVE across every band
tested, on the orbit and on the ensemble:

- `E[V(next) - V] = (s * D(1/s)) / s` is approximately `-0.12 / s`.

The scaled drift `s * D(1/s)` sits at about `-0.118` to `-0.127` across
seven size decades. This matches the closed-form prediction from the
growth rate: if `s' = s * rho` with `E[log rho] = r`, then to first order
`E[1/rho - 1] ~ e^{-r} - 1 = e^{-0.134} - 1 = -0.1254`. Measurement and
prediction agree.

Interpretation. `V = 1/(a+b)` is a bounded supermartingale outside any
compact size core, so it is a valid Foster TRANSIENCE certificate for R
under the sampled measure: the process escapes to infinity, it does not
return to a compact set. This is the clean, exactly reported drift
result. Its drift is NOT bounded below by a fixed `epsilon`; it decays
like `1/s`. That decay is precisely why R is transient rather than
positive recurrent, and it is the honest reason no classical
positive-recurrence Lyapunov function exists. The complementary function
`V = log(size)` has uniform positive drift `+0.134`, the same fact read
the other way.

No candidate delivered a positive-recurrence drift (`-eps` outside a
compact set), and none was expected to. The offset-based candidates
(`u`, `u^2`, `u/s`) carry near-zero drift and do not separate the fatal
region.

## 2. Tail hazard h(s)

### 2.1 Definition and exact measurement

`h(s)` is defined as the fraction of alive states `(a, b)` with
`a >= 5`, `b >= 3`, `a + b in [s, 2s)`, whose NEXT renewal `R(a, b)`
lands in the fatal set. This is the per-renewal one-step hazard under the
uniform (almost-all-seeds) measure on a size band. Full enumeration of
every lattice state in the band:

| s | alive states | die next | h(s) | C = h(s) * s |
|---|---|---|---|---|
| 64 | 5,504 | 167 | 3.034e-2 | 1.942 |
| 128 | 23,296 | 332 | 1.425e-2 | 1.824 |
| 256 | 95,744 | 667 | 6.966e-3 | 1.783 |
| 512 | 388,096 | 1,330 | 3.427e-3 | 1.755 |
| 1,024 | 1,562,624 | 2,663 | 1.704e-3 | 1.745 |
| 2,048 | 6,270,976 | 5,324 | 8.490e-4 | 1.739 |
| 4,096 | 25,124,864 | 10,651 | 4.239e-4 | 1.736 |

`C = h(s) * s` is monotone decreasing and converges to about 1.73. The
supremum over the exact range `s >= 64` is `C_emp = 1.942` (attained at
the smallest band). So the empirical, exactly enumerated bound is

    h(s) <= C_emp / s  with  C_emp = 1.94   for  64 <= s <= 4096.

Sampled confirmation beyond exact reach (uniform states in the band):
`s = 1e4` gives `C = 1.830 +/- 0.078` (549 deaths in 3e6 samples);
`s = 1e5` gives `C = 1.625 +/- 0.116` (195 deaths in 1.2e7 samples).
Both are consistent with the asymptote near 1.73.

### 2.2 Reconciliation with the earlier "~6/size" estimate

The almost-all-seeds note estimated a per-renewal hazard near `6/size`
and a residual near `50/s`. The refined figure is `C ~ 1.74`, smaller.
The "6" is correctly read as the offset-model numerator: on a deep-fuse
the fatal offsets are the three odd values `{1, 3, 5}` spaced by 2, which
gives a per-fuse numerator of `2 * 3 = 6` when the offset is treated as
ranging uniformly over odds. The one-step hazard over ALL states is that
per-fuse numerator times the fraction of states that are fuses. The exact
scan gives `fuse_frac -> 0.250`, so the fuse contribution alone is about
`0.25 * (something near 6) / s`. But fuses are not the dominant death
mode. The death-mode breakdown at `s = 1024` (2,663 fatal transitions):

- T-step (`b` even) landing on the diagonal: 1,536 (58%);
- F-step (deep fuse) landing on the diagonal: 615 (23%);
- C-step landing on `b = 4`: 512 (19%).

So the largest one-step hazard channel is a terminate step whose image
`(a + 6, b - 3)` falls in the diagonal window, not the fuse itself. The
single constant `C ~ 1.74` already aggregates all three channels. This
refines, and slightly lowers, the earlier rough figure.

### 2.3 Tail sum along the true orbit

Model the hazard as `h(s_k) <= C / s_k` with `C = 1.94`, and use the
measured sizes `s_k` along the 200,000-renewal orbit. The tail from
renewal `K` is `sum_{k >= K} C / s_k`. Because `s_k` grows geometrically
with rate `r = 0.134`, it is bounded by `(C / s_K) / (1 - e^{-r})` with
`1 / (1 - e^{-r}) = 7.97`.

| from renewal K | exact sum C/s_k | geometric bound |
|---|---|---|
| 0 | 5.72e-1 | 8.14e-1 |
| 10 | 1.23e-1 | 1.35e-1 |
| 50 | 4.36e-4 | 4.72e-4 |
| 100 | 4.63e-7 | 4.66e-7 |
| 1000 | 9.82e-60 | 9.11e-60 |

The tail converges geometrically. Under the model, the total expected
number of fatal events summed over the whole orbit is order 1 (0.57),
concentrated in the first handful of renewals: this is the quantitative
form of "death is an early-game phenomenon". From renewal 100 onward the
entire remaining hazard is below `5e-7`, and from renewal 1000 it is
below `1e-59`. This is the Borel-Cantelli backbone: IF the per-renewal
fatal probability is `<= C/s_k` and IF the sizes grow multiplicatively,
the surviving-orbit death probability is finite and tiny.

### 2.4 What the true orbit's offset actually does

The Borel-Cantelli model above uses the uniform-measure hazard `C/s`. The
specific orbit need not follow it. Direct measurement of the orbit's fuse
offsets over 300,000 renewals (78,448 fuses) shows the normalized offset
`u/y = (b - beta)/b` is NOT uniform: its deciles are

    [4646, 5270, 5672, 6250, 6916, 7752, 8507, 9760, 11155, 12520]

increasing toward large offsets, mean `u/y = 0.590`. The orbit puts LESS
mass near the fatal window (small `u`) than uniform would, which is
favorable, but the density near `u = 0` is positive and bounded away from
both 0 and infinity. That is exactly the regime that yields a hazard of
order `1/s` with a positive constant: the fatal window `{1, 3, 5}` is a
fixed 3-point target under a distribution with bounded density on a range
of width of order `s`.

## 3. The gap to rigor

The numerics supply values. A proof needs the following lemmas, none of
which the numerics establish. Each is listed with what the experiments
make plausible and its difficulty.

**L1. Genuine multiplicative growth (lower bound, not mean).** Needed:
`s_k >= s_0 * lambda^k` for some `lambda > 1` for all `k`, or a
supermartingale controlling `log s_k` from below along the orbit. The
experiments give the MEAN drift `+0.134` with comparable variance, and
the minimum single-step log-growth observed is 0 (never negative in
200,000 renewals). Plausible that growth never reverses on average, but a
worst-case per-step lower bound is false (T-steps with `b` near `a` grow
little), so the real statement is a large-deviation or martingale bound
on the partial sums of `log rho`. Difficulty: moderate for an
almost-all-seeds statement (a positive Lyapunov exponent for the
skew-product), genuinely hard for the specific orbit, which is a single
non-random trajectory with no ensemble to average over.

**L2. Uniform hazard bound `h(s) <= C/s` for ALL s.** Needed: the exact
lattice-counting bound of Section 2.1, proven for every `s`, not just
`s <= 4096`. This is the most tractable lemma. The count of fatal-image
states in a band is a lattice-point count over a finite union of affine
lines (the three death channels), and the leading term is linear in `s`
while the band holds order `s^2` states, giving `C/s`. Difficulty: low
to moderate. This is mechanical, essentially a piecewise-affine
lattice-point computation, and is plausibly formalizable. It is the one
lemma the experiments most nearly promote to a theorem.

**L3. Equidistribution / bounded density of the orbit's offset.** Needed:
along the specific orbit, `P(u_k in {1, 3, 5}) <= C/s_k`, equivalently
the offset process has density bounded near 0 uniformly in `k`. The
experiments show the orbit's offset density near 0 is positive and
bounded (Section 2.4), and that the branch-symbol sequence has positive
entropy (factor complexity `~1.6^n`, from the earlier note), consistent
with mixing. But this is the crux and it is unproven. It is the exact
analogue of the equidistribution input in Tao's Collatz argument.
Difficulty: hard. For the almost-all-seeds measure it is an
equidistribution statement about an explicit piecewise-affine skew
product, plausibly reachable with transfer-operator or thermodynamic
methods. For the single orbit it is Collatz-hard: it asserts a specific
non-random integer sequence is equidistributed, which no current method
delivers.

**L4. Summability into a survival bound (Borel-Cantelli closure).**
Needed: turn `sum_k h(s_k) < infinity` into `P(orbit ever fatal) < 1`, or
for the specific orbit into an actual avoidance certificate. For an
ensemble this is the first Borel-Cantelli lemma and is immediate once L1
to L3 hold; it yields the almost-all-seeds theorem. For the SINGLE orbit
Borel-Cantelli says nothing: a probability-zero event can still occur for
one fixed trajectory, and the orbit either hits the window or it does
not, deterministically. Difficulty: trivial for almost-all, and a
category error for the specific orbit. This is the wall.

### 3.1 Two theorems, two distances

- Almost-all-seeds theorem for R (density-zero fatal set with rate
  `O(1/X)`). Reachable. It needs L1, L2, L3 in their ensemble form plus
  L4. L2 is nearly mechanical, L1 is a positive-Lyapunov-exponent
  statement, L3 is the substantive equidistribution input. This is the
  Tao-Collatz-shaped project the earlier notes named, and the scaffold
  here supplies its constants: `r = 0.134`, `C = 1.94`, geometric tail
  factor `7.97`.

- Specific-orbit theorem (SafeMetaOrbit, the actual bbchallenge goal).
  Not reachable by this route. L3 and L4 both degenerate for a single
  deterministic trajectory. The hazard sum being finite is strong
  heuristic evidence (residual below `1e-59` from renewal 1000) but is
  not a proof, for the same reason the analogous Collatz heuristic is not
  a proof.

## Verdict

The best drift function is `V = 1/(a + b)`, a bounded supermartingale
whose scaled one-step drift is `-0.12` uniformly across size decades 16
bit to 16384 bit on the orbit and `1e3` to `1e6` on the ensemble. Its
sign is negative, certifying transience, not positive recurrence, which
is the correct and only available drift structure for this map. The
per-renewal tail hazard is `h(s) <= C/s` with exactly enumerated
`C_emp = 1.94` for `64 <= s <= 4096` and asymptote near 1.73, refining
the earlier `~6/size` down to `~1.74/size`. Under the measured growth
rate the tail sum converges geometrically with factor `7.97`, residual
hazard below `5e-7` from renewal 100 and below `1e-59` from renewal 1000.

The tail PROVABLY converges under the two stated assumptions
(multiplicative growth and `h(s) <= C/s`); it does not converge from the
numerics alone, because neither assumption is a theorem. Distance to a
rigorous almost-all-seeds theorem: one hard equidistribution lemma (L3)
plus two mechanical ones (L1 ensemble, L2). Distance to a rigorous
specific-orbit theorem: unbounded, because Borel-Cantelli and
equidistribution both lose their meaning for a single deterministic
trajectory. This is the honest frontier. The scaffold is complete and
the constants are pinned; the missing object is a proof that the offset
process equidistributes, which is exactly the Collatz-hard core the
reduction was always going to leave behind.

## Honest scope

Growth rate: 200,000 renewals. Drift: 200,000 renewals on the orbit,
3,000 states per band on the ensemble, size decades 16 bit to 16384 bit.
Exact hazard: full enumeration to `s = 4096` (25 million states in the
top band). Sampled hazard: 3e6 and 1.2e7 samples at `s = 1e4, 1e5`.
Offset distribution: 300,000 renewals, 78,448 fuses. All results are
measurements at these horizons. None is an impossibility theorem and none
is a proof of survival or of density zero.
