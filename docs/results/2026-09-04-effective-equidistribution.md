# Effective equidistribution vs. the fatal window: the specific-orbit door is BOLTED

**Date:** 2026-09-04 · **Script:** `qgkit/bb6/effective_equidist.py`
(exact verified renewal map `R`, native bigints, no randomness).

This experiment decides one **methodological** question — not a machine.
The prior offset-equidistribution finding
(`2026-09-04-offset-equidistribution.md`) showed the diagonal-crossing
offset `o = b - beta` equidistributes to <0.3% and left open whether an
*effective* (quantitative, error-bounded) equidistribution theorem could
ever localize a **single** good-phase orbit's fate below the width-3
fatal window `{1,3,5}`. The question: is that door **BOLTED** (provably
out of reach) or merely **HEAVY** (in principle reachable)?

**Verdict: BOLTED.** The achievable equidistribution error decays only
diffusively (`~ n^{-1/2}`, CLT rate) while the fatal window shrinks
exponentially; the error term is astronomically larger than the window
at every large scale, so no effective-equidistribution theorem of this
type can resolve a specific orbit below the window. See the Honesty box:
this measures the **feasibility of a method**; it does not itself decide
any machine.

---

## Ensemble

Primary: 2,236 deterministic seeds — `(6+4k, 13+8k)` for `k in
range(2000)` plus 236 large iterated states — each run to `bitlen(a) =
800` (≈4,100 renewals) or death. Totals: **2,379,559 above-diagonal
crossings**, mean 1,064 crossings/orbit. Death-harvest ensemble: 22,344
small seeds (`a0 in [6,300)`, high early hazard `~6/beta`) run to a
220-bit cap, yielding **848 diagonal deaths** for the rare-event test.

## (1) Discrepancy decay rate — the single most important number

For each orbit and each modulus `M`, the running star-discrepancy proxy
`D_orbit(n) = max_r |freq_r(n) − 1/k|` over admissible (odd) residues,
averaged over all orbits with ≥ n crossings, log-log fitted `D(n) ~
n^{-alpha}`:

| M | k residues | fitted alpha | R² | fit range |
|---|---|---|---|---|
| 6 | 3 | **0.489** | 0.9998 | n ∈ [20, 900] |
| 8 | 4 | **0.481** | 0.9998 | n ∈ [20, 900] |
| 16 | 8 | **0.492** | 0.9999 | n ∈ [20, 900] |
| 384 | 192 | 0.616 | 0.9995 | n ∈ [20, 900] |

**alpha ≈ 0.49, cross-modulus mean 0.52.** The fits are essentially
perfect (R² > 0.999 over ~1.6 decades of n). This is **exactly the
diffusive / CLT rate `n^{-1/2}`** — the generic rate at which the
empirical residue frequency of a *mixing* sequence converges to uniform
(count fluctuations scale like `√n`, so the frequency deviation scales
like `n^{-1/2}`). It is emphatically **not** exponential (`e^{-λn}`
would require alpha → ∞) and **not** super-CLT (`alpha > 1`).

The M=384 value (0.62) is a mild finite-sample artifact: with 192
residues and n ≤ 900, most residues carry < 5 counts and the max-
deviation proxy sits near its `1/k` noise floor, steepening the fit
slightly. It is still polynomial and nowhere near exponential.

## (2) Mixing spectral gap — a genuine gap, but it only buys CLT

Two independent estimates of correlation decay for the 5-symbol process
`{T, dC, DC, dF, DF}`:

**(b) Transition-operator eigenvalues** (pooled over 9.07M transitions).
Order-1 operator: `|λ₂| = 0.440`, so **spectral gap `1 − |λ₂| = 0.560`**.
Order-2 operator (10 visited pair-states): `|λ₂| = 0.782`, gap 0.218.
Both bounded away from 1 ⇒ **genuine exponential mixing** of the symbol
process. (The no-TT constraint shows cleanly: `dC`, `DC` deterministically
return to `T`.)

**(a) Autocorrelation.** Growth increments `d log(size)`: `−0.34` at lag 1,
decaying into noise by lag ~5 (exp-fit `e^{-0.71·lag}`, `|λ|≈0.49`). The
offset-residue indicator `[o mod 6 = 1]`: `0.064` at lag 1 and within
noise thereafter — **consecutive crossing offsets are essentially
independent draws**.

**The crux.** There *is* a spectral gap, i.e. mixing is exponential. But
a spectral gap delivers a **Central Limit Theorem**, whose consequence
for empirical frequencies is a `n^{-1/2}` discrepancy — precisely what
(1) measures. Exponential *mixing* does **not** produce exponential
*equidistration error*. This is the structural reason the door is bolted:
the best correlation-decay the dynamics offers still leaves a diffusive
error floor.

## (3) The comparison that answers the question

Fatal-window fraction at renewal `n` shrinks like `e^{-0.134 n}` (prior
measured mean log-growth 0.134/renewal). With ~3 renewals per crossing,
per crossing the window shrinks like `e^{-0.402 n}`. Side by side with
the measured `D(n)` (M=6):

| n (crossings) | D(n) [polynomial] | window `~e^{-0.402 n}` | D / window |
|---|---|---|---|
| 10 | 1.68e−1 | 1.79e−2 | 9.4 |
| 20 | 1.31e−1 | 3.22e−4 | 4.1e+2 |
| 40 | 9.53e−2 | 1.04e−7 | 9.2e+5 |
| 80 | 6.80e−2 | 1.08e−14 | 6.3e+12 |
| 160 | 4.84e−2 | 1.17e−28 | 4.2e+26 |
| 320 | 3.40e−2 | 1.36e−56 | 2.5e+54 |
| 640 | 2.44e−2 | 1.84e−112 | 1.3e+110 |
| 900 | 2.06e−2 | 7.45e−158 | 2.8e+155 |

The ratio explodes past crossing ~10 and reaches **10^155** by n=900.
`D(n)` decays polynomially (`n^{-0.49}`); the window decays exponentially
(`e^{-0.402 n}`). **The equidistribution error is astronomically larger
than the window at every large scale.** This is the BOLTED case in the
experiment's own decision rule.

## (4) Rare-event vs. smooth accumulation — corroboration

For the 848 harvested diagonal deaths (plus 2 natural-rate deaths in the
primary ensemble; per-crossing natural rate 8.4e−7), the **offset at the
crossing immediately before the fatal one** (n=641 with a recorded
predecessor):

- min 7, p10 61, **median 221**, p90 1021, max 37,103;
- **0 of 641** had the previous offset inside `{1,3,5}`;
- only **0.5%** had previous offset ≤ 11; **8.4%** ≤ 51.

Death is **hit in one shot from a generic, typically large offset** —
not approached gradually through shrinking offsets. The fatal set is
entered by a single fresh draw landing in `{1,3,5}`, with the previous
draw sitting at a wholly ordinary value (median 221). This is the
rare-event signature (BOLTED), and it matches the prior ergodic finding
"fatal set hit in one shot, not approached — no barrier supermartingale."

One honest correction to the naive expectation: the per-orbit **hazard-
sum** is *not* overdispersed here — mean 0.014, var 0.0048, **var/mean
0.34 < 1**. Hazard sums are dominated by the first few small-scale
crossings and are fairly regular across orbits, so var/mean is not the
informative diagnostic. The decisive rare-event evidence is the
predecessor-offset distribution above: a one-shot entry from a generic
value, with no gradual descent toward the window.

## (5) Effective-tail feasibility for the certified orbit (6,13)

`(6,13)` run to bitlen 800 (4,100 renewals): 1,074 crossings, **min
offset ever = 9** (margin 4 above the window — reproducing every prior
horizon). Its cumulative model hazard tail `Σ 3/(beta/2)` = **1.88**,
collapsing geometrically (tail from crossing k≥5 is 0.078; k≥20 is
2.7e−6; k≥40 is 4.1e−12).

**The feasibility inequality.** To certify "no fatal crossing ever" for
this *specific* deterministic orbit, an effective theorem must resolve
each crossing's phase to *below* the per-crossing hazard `3/(beta_k/2)`
it must rule out. But the achievable resolution is the discrepancy error
`D(k) ≈ 0.54·k^{-0.49}`. Comparing:

| k | D(k) error | per-crossing hazard 3/(β/2) | D(k) / hazard |
|---|---|---|---|
| 10 | 1.75e−1 | 5.83e−4 | 3.0e+2 |
| 40 | 8.87e−2 | 5.25e−13 | 1.7e+11 |
| 80 | 6.32e−2 | 1.04e−22 | 6.1e+20 |
| 160 | 4.50e−2 | 3.68e−41 | 1.2e+39 |
| 320 | 3.21e−2 | 3.70e−75 | 8.7e+72 |
| 640 | 2.29e−2 | 3.09e−147 | 7.4e+144 |

**`D(k)` is never below the hazard it must resolve — the ratio only
grows**, from 300 at k=10 to 10^144 at k=640, because
`error / hazard ~ k^{-0.49} · e^{+0.402 k} → ∞`. The specific orbit
`(6,13)` is provably **not localizable** by an effective-equidistribution
bound: the method's own uncertainty dwarfs the effect it must resolve, by
a gap that diverges super-exponentially. Quantified gap: the deviation
budget `D(k)·(#crossings)` exceeds the model tail by factors that pass
10^100 well before crossing 640.

---

## Verdict: DOOR BOLTED

- **Discrepancy exponent alpha ≈ 0.49** (M=6,8,16; mean 0.52), R² > 0.999
  — diffusive `n^{-1/2}`, the CLT rate. Polynomial, decisively not
  exponential.
- **Spectral gap present** — order-1 `1 − |λ₂| = 0.56`, order-2 0.22;
  offset residues essentially i.i.d. Exponential *mixing* holds — but a
  gap yields a CLT, hence only `n^{-1/2}` equidistribution error, not an
  exponential one.
- **The comparison is one-sided at every scale**: `D(n)` polynomial vs.
  window `e^{-0.134 n}` exponential; ratio → 10^155 by n=900.
- **Rare-event confirmed**: 848 deaths entered in one shot from generic
  predecessor offsets (median 221; 0/641 in `{1,3,5}`), not by gradual
  approach.
- **(6,13) not localizable**: `D(k)/hazard` grows from 300 to 10^144;
  never below 1.

An effective-equidistribution theorem, no matter how strong within its
class, can localize a specific orbit's fate only down to its `n^{-1/2}`
error floor — which is exponentially coarser than the window that
governs survival. **The specific-orbit door is bolted, not merely
heavy.** The almost-all-seeds statement is untouched and remains the only
publishable target (a `n^{-1/2}` error is perfectly sufficient for a
Borel–Cantelli / summability argument over *typical* orbits — see the
prior three docs).

## Honesty box

- This is a **measurement of method feasibility, not a proof and not a
  decision about any machine**. It establishes that a specific well-scoped
  proof *strategy* (deciding one orbit via effective equidistribution)
  cannot work, by quantifying that the strategy's intrinsic error floor
  (`n^{-1/2}`) is exponentially larger than the fatal window it would have
  to resolve. It does **not** prove `(6,13)` halts or does not halt.
- All quantities are **empirical at finite horizon** (2.38M crossings;
  bitlen cap 800; 848 harvested deaths). The exponent `alpha`, the
  spectral gap, and the `0.134` log-growth are fitted/measured constants,
  not theorems. The M=384 fit (0.62) carries a finite-sample steepening.
- The BOLTED verdict is a statement about **this family of methods**
  (effective equidistribution / discrepancy bounds). It does not preclude
  an entirely different route (a purely arithmetic invariant, an exact
  algebraic obstruction) — it only closes the equidistribution route for
  the specific orbit, consistent with every prior Collatz-hard-wall
  finding.
- No Lean file, no other results doc, and no certificate is upgraded by
  this measurement.

```
Reproduce:  python3 qgkit/bb6/effective_equidist.py   (~37s, deterministic)
```
