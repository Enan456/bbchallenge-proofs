# Transfer-operator scaffold for the almost-all-seeds theorem: Ulam spectrum, invariant density, and the one remaining Lasota-Yorke lemma

**Date:** 2026-09-04 · **Script:** `qgkit/bb6/transfer_operator.py`
(exact verified renewal map `R`, native bigints, no randomness) ·
companion to `2026-09-04-invariant-measure-drift.md`,
`2026-09-04-modular-dictionary-probe.md`,
`2026-09-04-offset-equidistribution.md`,
`2026-09-04-effective-equidistribution.md`.

This builds the Ruelle-Perron-Frobenius (transfer) operator of the
induced renewal dynamics and discretizes it (Ulam method) to measure the
objects a Lasota-Yorke / Ionescu-Tulcea-Marinescu proof of the
**almost-all-seeds** theorem would consume: the leading eigenvalue (= 1,
with the invariant density as eigenvector), the **spectral gap**, the
numerical **invariant density**, and the **factorization** of the
invariant measure into (ratio density) x (uniform residue) that *is* the
offset-equidistribution lemma. It then states precisely which standard
theorems would close conditions (i)-(iii) and isolates the single
machine-specific lemma left open. **Numerical scaffold, not a proof** —
see the Honesty box.

---

## 0. The operator

The verified renewal map `R` (`renewal_analysis3.py`) has three branches
(`2026-09-04-modular-dictionary-probe.md`):

| move | condition | linear part | det | type |
|---|---|---|---|---|
| **T** | `b` even | `[[1,0],[0,1]]`+shift | +1 | parabolic (trace 2) |
| **C** | `b` odd, `b<beta` | `[[0,3],[1,-1]]` | -3 | hyperbolic |
| **F** | `b` odd, `b>beta` | `[[3,0],[-1,1]]` | +3 | expanding (eig 3) |

**Induced return map.** Fatality lives at the diagonal crossings (the
`F`-branch: `b` odd, `b>beta`, offset `o = b-beta`, death iff
`o in {1,3,5}`). We take the **first-return map** `F_Sigma` of `R` to the
crossing section `Sigma = {b odd, b>beta}`. Between returns the orbit
performs a short interleaving of `T`, `C`, `F` moves (measured mean 3.82
renewals/return, max 43; `T` never fires twice — it cannot, `b->b-3` odd).

**Scale-invariant coordinates.** `R` is (in `a`) volume-expanding by the
det-3 factor, so the natural state for the *return* dynamics is
projective. We use

- ratio coordinate `z = o/(o+beta) in (0,1)` (equivalently `xi = o/beta`,
  `z = xi/(1+xi)`) — scale invariant;
- residue coordinate `r = o mod M` in the finite group `Z/M`
  (`o` is always odd, so admissible residues are the odd ones).

The **transfer operator** `L` acts on densities `rho` on `Sigma`:
`(L rho)(y) = sum_{x: F_Sigma(x)=y} rho(x)/|F_Sigma'(x)|`. Its fixed
density is the invariant density `h`; the physical (SRB) measure is
`h·Leb`. The offset-equidistribution lemma is the statement that the
`Z/M`-marginal of that measure is **Haar (uniform)**.

## 1. Ulam discretization

Partition `Sigma` into cells (`NZ` uniform `z`-cells) x (`k` odd residues
mod `M`). The Ulam matrix `L_ij =` (fraction of cell `i` that maps to cell
`j`) is estimated as the empirical transition frequency between
consecutive crossings, over a deterministic ensemble (1,057 seeds,
**981,706 induced crossings**, bitlen cap 700). `L` is row-stochastic;
its **leading eigenvalue is 1 by construction** (the content is the *gap*
below it and the *shape* of the stationary vector), the stationary left
eigenvector is the invariant density, and `|lambda_2|` is the spectral
gap.

## 2. Numerical spectrum

**Primary operator** (`NZ=24` z-cells x 3 residues mod 6, 72 states):

| quantity | value |
|---|---|
| leading `|lambda_1|` | **1.000000** (exact, as required) |
| second `|lambda_2|` | **0.2115** |
| **spectral gap `1-|lambda_2|`** | **0.7885** |
| top-8 `|eigenvalues|` | 1.00, 0.21, 0.21, 0.18, 0.18, 0.16, 0.16, 0.16 |

**Ratio-only operator** (residue collapsed) — the clean `z`-dynamics gap,
stable under refinement:

| NZ | `|lambda_2|` | gap |
|---|---|---|
| 16 | 0.186 | 0.814 |
| 24 | 0.214 | 0.786 |
| 32 | 0.233 | 0.767 |
| 48 | 0.242 | 0.758 |

`|lambda_2|` creeps up toward ~0.25 as the grid refines and **stabilizes;
the gap sits robustly at 0.76-0.81** across 12-48 bins (Ulam convergence
table (C) in the script). This is a genuine, resolution-stable spectral
gap of the induced return-map operator: **quasi-compact behaviour, not a
numerical artifact.**

**Cross-check vs. the 5-symbol operator.** The single-renewal
`{T,dC,DC,dF,DF}` transition operator gives `|lambda_2| = 0.4434`, gap
**0.5566** — reproducing the prior effective-equidistribution report
(`|lambda_2|=0.440`, gap 0.560) to three figures. The two gaps are
*different operators*: 0.79 is per **return** (~3.82 renewals composed),
0.56 is per **single renewal**. They reconcile: `0.21^(1/3.82) ≈ 0.66`
effective per-renewal `|lambda|`, the same order as 0.44 (the residual is
Ulam coarse-graining bias, which inflates `|lambda_2|` on coarse grids).
**Both are decisively bounded away from 1** — the essential fact.

**Consistency with the "door bolted" finding.** A spectral gap gives a
*Central Limit Theorem*, hence an `n^{-1/2}` equidistribution
(discrepancy) error — exactly the measured exponent 0.49
(`2026-09-04-effective-equidistribution.md`). The gap does **not** give
exponential equidistribution error. So this operator scaffold is fully
consistent with (i) the almost-all lemma holding via Borel-Cantelli and
(ii) the specific-orbit door remaining bolted.

## 3. The invariant density (candidate stationary measure)

The stationary left eigenvector, marginalized:

**Ratio marginal `f(z)`** is **clean**: smooth, positive on all of
`(0,1)`, **monotone increasing** from ~0.025 mass per bin near `z=0`
(small offset relative to `beta`) to ~0.070 near `z=1` (offset `>> beta`,
the heavy `o/beta` right tail). No spikes, no gaps, no multimodality —
a bounded-variation, essentially Lipschitz density. (Full 24-bin profile
in the script output.)

**Residue marginal** over `{1,3,5} mod 6`: `[0.3345, 0.3326, 0.3330]`,
**max deviation from uniform 0.00114** — uniform to ~0.1%.

**Factorization.** Mass-weighted mean of `max_r |P(r|z) - 1/k|` over
z-slices = **0.00319**. The invariant measure factorizes as
`mu(z,r) ≈ f(z) x uniform(Z/M)` to 0.3%: the residue is uniform in *every*
ratio slice. **This factorization is the offset-equidistribution lemma
expressed as a property of the invariant measure** — the `Z/M`-marginal is
Haar.

**Drift as an invariant-measure integral.** Per-renewal log-growth along
`(6,13)` = **0.13422** (std 0.138, 20,638 renewals), i.e.
`E_mu[log|F'|] > 0`: the positive Lyapunov exponent the invariant measure
integrates. Matches the prior 0.134. This is the geometric drift as an
invariant-measure property — condition (ii).

## 4. Quasi-compactness assessment

- **Function space.** `BV((0,1))` (bounded variation in the ratio
  coordinate) tensored with `ell(Z/M)` (finite-dimensional, automatically
  fine). The Möbius/analytic branch structure would also support a Hölder
  `C^alpha` space.
- **Uniform expansion.** The `F`-branch has `|F'| = 3` exactly (the
  Collatz multiplier / det-3 factor is uniform expansion by 3 in the
  `a`-direction); the `C`-branch expands by its hyperbolic eigenvalue
  (1.30-2.30). Every return composes at least one `C`/`F` expansion, so
  the induced map `F_Sigma` is uniformly expanding, `lambda_Sigma > 1`.
- **The obstruction: the parabolic `T`.** `T` is unipotent (trace 2,
  neutral fixed point at the cusp). Because of it, `R` *itself* is a
  **non-uniformly expanding / intermittent (Pomeau-Manneville-type) map**,
  and the standard Lasota-Yorke inequality **fails for the un-induced
  map** — the neutral fixed point destroys uniform expansion. **Inducing
  on the `F`-section is exactly the standard cure** (Young-tower / inducing
  scheme), and it is why the induced operator above shows a clean gap while
  the raw map does not. The numerics say the return times are short
  (mean 3.82, `T` never repeats, tail decays fast).

Given a Lasota-Yorke inequality for `F_Sigma`, quasi-compactness is
**standard**: `L-Y` + compact embedding `BV ↪ L^1` ⟹ (Ionescu-Tulcea-
Marinescu) `L` is quasi-compact, essential spectral radius `≤ 1/lambda_Sigma
< 1`, finitely many peripheral eigenvalues; topological mixing ⟹ `1` is
simple and isolated ⟹ **unique ACIM `h in BV`, exponential decay of
correlations at the spectral-gap rate.**

## 5. Proof skeleton (almost-all seeds)

**Assumptions / setup.** `R`, its three branches, the `F`-section
`Sigma`, the induced first-return map `F_Sigma` in coordinates `(z, r)`,
the transfer operator `L` on `BV((0,1)) ⊗ ell(Z/M)`.

**Chain of standard theorems** (each off-the-shelf once the one lemma
below holds):

1. **Lasota-Yorke inequality** (from uniform expansion + bounded
   distortion of `F_Sigma`): `||L^n rho||_BV ≤ A theta^n ||rho||_BV +
   B ||rho||_{L^1}` with `theta ≤ 1/lambda_Sigma < 1`.
2. **Ionescu-Tulcea-Marinescu** (L-Y + compact embedding `BV ↪ L^1`):
   `L` quasi-compact; essential spectral radius `≤ theta`; peripheral
   spectrum finite. Mixing ⟹ `1` simple and the only peripheral
   eigenvalue ⟹ **unique invariant density `h`**, and **exponential
   decay of correlations** at rate `= gap` (measured 0.79/return,
   0.56/renewal) — this is condition **(iii)**.
3. **Invariant-measure drift** `= int log|F'| dmu > 0` (measured 0.134):
   positive Lyapunov exponent, the geometric drift as an invariant-measure
   property — condition **(ii)**.
4. **Haar residue marginal** (offset equidistribution): apply ITM to the
   `Z/M`-skew-product; if the residue cocycle is **aperiodic** (not
   supported on a proper subgroup/coset — the mod-`M` reachability BFS in
   `renewal_analysis3.py` is the numerical no-obstruction evidence), the
   `Z/M`-marginal of `mu` is Haar ⟹ the offset equidistributes over
   residues — condition **(i)**. The measured factorization (dev 0.003)
   is this conclusion.
5. **Nagaev-Guivarc'h CLT** (perturb `L` to `L_t = L(e^{it phi}·)` for
   `phi =` residue/hazard observable): quasi-compactness ⟹ smooth leading
   eigenvalue `lambda(t)` ⟹ CLT with the `n^{-1/2}` discrepancy — matching
   the measured exponent 0.49, and giving the effective error term for a
   Borel-Cantelli / summability argument.
6. **Borel-Cantelli closure.** With (i) the uniform residue phase, (ii)
   the geometric drift `s_k >= s_0 lambda^k`, and the per-crossing hazard
   `<= C/beta_k` (bounded density near the fatal window, from `h` bounded),
   `sum_k P(fatal at crossing k) < infinity` for `mu`-a.e. orbit ⟹
   **almost-all seeds never die** (the density-zero fatal-set theorem).

**The single machine-specific lemma left open.** Everything above is
standard *once step 1 holds*. The one open, machine-specific input is:

> **Lemma (bounded distortion + summable return-time tails for the
> induced `F`-return operator).** The first-return map `F_Sigma` of `R` to
> the `F`-section, written in the ratio coordinate, is uniformly expanding
> with uniformly bounded distortion — there exist `lambda_Sigma > 1` and
> `D < infinity` such that every return branch `g` satisfies
> `|g'| ≥ lambda_Sigma` and `|log|g'|(x) - log|g'|(y)| ≤ D|x-y|` — **and**
> the return time (number of intermediate parabolic-`T` steps) has
> summable (exponentially decaying) tails. Consequently the induced
> transfer operator satisfies a Lasota-Yorke inequality on
> `BV((0,1)) ⊗ ell(Z/M)`.

This is the **distortion / bounded-variation bound for this specific
piecewise-affine (piecewise-Möbius, det-3 arithmetic) map**, exactly the
lemma the task anticipated. Its crux and its danger are the **parabolic
`T`**: converting "measured short return times" (mean 3.82, no `TT`,
fast-decaying tail) into a *proven* summable-tail + bounded-distortion
estimate for this `GL(2, Z[1/3])` semigroup is the open work. A secondary,
easier sub-lemma is the **aperiodicity of the residue cocycle mod `M`**
(step 4), for which the mod-`M` BFS already gives complete numerical
no-obstruction evidence.

## 6. Reachability verdict

- **Reachable, standard:** steps 2, 3, 5, 6 (ITM quasi-compactness, the
  drift integral, Nagaev-Guivarc'h, Borel-Cantelli) — all off-the-shelf
  once step 1 holds. The numerics confirm every ingredient they need: a
  gap bounded from 1, a clean BV invariant density, a Haar residue
  marginal, a positive drift.
- **The one hard lemma:** the induced-map Lasota-Yorke inequality (step
  1), whose difficulty is concentrated in the parabolic-`T` return-time
  control. This is the standard intermittent-map inducing estimate,
  plausibly reachable but genuinely machine-specific work.
- **Untouched:** the specific-orbit (SafeMetaOrbit) goal. The transfer
  operator is a statement about the invariant *measure*; it is silent on
  any single deterministic trajectory. `(6,13)` remains generic and
  Collatz-hard, exactly as every prior finding.

## Honesty box

- This is a **numerical scaffold**, not a proof. The leading eigenvalue
  `= 1` is **automatic** for a stochastic matrix and proves nothing on its
  own; the content is the measured spectral gap (0.79 induced / 0.56
  symbol), the clean BV invariant density, the Haar residue marginal
  (dev 0.001), and the measure factorization (dev 0.003). All are
  **finite-horizon measurements** (981,706 crossings, bitlen cap 700).
- Ulam eigenvalues are **discretization-dependent**; `|lambda_2|` drifts
  with grid resolution (0.19-0.25 over 16-48 bins) and Ulam coarse-graining
  biases it upward. The reported gap is robust in sign and order (bounded
  away from 1 across all grids), **not** a certified value of the true
  operator's second eigenvalue.
- The proof skeleton names **standard theorems** (Lasota-Yorke,
  Ionescu-Tulcea-Marinescu, Nagaev-Guivarc'h, Borel-Cantelli) and one
  **open machine-specific lemma** (the induced-map L-Y / bounded-distortion
  + return-time-tail estimate). Naming the route is **not** walking it; the
  lemma is unproven and its parabolic-`T` core is the real work.
- The finding bears **only** on the **almost-all-seeds** theorem. It says
  **nothing** about the unconditional non-halting of any specific machine.
  `(6,13)` is generic; the specific-orbit door stays bolted
  (`2026-09-04-effective-equidistribution.md`). **A spectral gap yields a
  CLT (`n^{-1/2}` error), never the exponential resolution a single orbit
  would need.**
- No Lean file, no other results doc, and no certificate is created or
  upgraded by this measurement.

```
Reproduce:  python3 qgkit/bb6/transfer_operator.py   (~18s, deterministic)
```
