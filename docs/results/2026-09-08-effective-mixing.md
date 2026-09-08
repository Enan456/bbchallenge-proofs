# Effective mixing rate of the offset over the induced return map G: the residue is a finite affine cocycle, and its marginal equidistributes exponentially-in-d (poly-in-N)

**Date:** 2026-09-08 · **Script:** `qgkit/bb6/effective_mixing.py`
(exact verified renewal map `R`, native bigints, no randomness) ·
companion to `2026-09-04-effective-equidistribution.md`,
`2026-09-04-offset-equidistribution.md`,
`2026-09-04-transfer-operator.md`.

This experiment quantifies the **effective mixing / equidistribution
rate** of the diagonal-crossing offset `o_d = b_d − beta_d` over the
**induced first-return map `G`** of `R` to the crossing section
`Sigma = {b odd, b > beta}` (the `F`-branch). It answers, as
measurements, the four inputs the "Method B" route (effective
equidistribution → natural density, needed because the halting set is not
Jordan-measurable) would consume. **Everything below is measurement at a
finite horizon, not a proof.** See the Honesty box.

Ensemble: **1,978 deterministic seeds** (family `(6+4k, 13+8k)` plus
iterated reseeds), each run to `bitlen(a) = 340` or death, giving
**873,557 induced crossings** (mean 442/orbit). Cocycle modulus
`L = 2·384·5 = 3840` (divisible by 2 and by every tested `M`).

---

## (1) Cocycle structure of `o_d`: residue is a finite affine cocycle; the integer offset is projective, not a Birkhoff sum

**The exact form.** Every renewal move is an **affine map** on the state
`(a,b)`:  `(a,b) ↦ Lin·(a,b) + shift`, with `Lin ∈ {I, Clin, Flin}`,
`Clin = [[0,3],[1,−1]]` (det −3), `Flin = [[3,0],[−1,1]]` (det +3),
`T = I` + shift `(+6,−3)`. Since the linear parts are integer matrices
and the shifts are integers, **reduction mod `L` is exact**: the reduced
state `(a mod L, b mod L)` evolves by an affine cocycle, and

> `o_d mod M = (b_d − beta_d) mod M` is a **deterministic factor** of the
> reduced state (using `a mod 2` for the parity that sets `beta = a−1` or
> `a−2`), for every `M | L`.

**Verified exactly:** predicting `o_d mod M` from `(a,b) mod L` through
the affine cocycle `R_mod` and comparing to the bigint truth over all
`873,557` crossings × 8 moduli `{2,3,4,5,6,8,16,384}` gives
**0 mismatches**. So the offset-residue process is a genuine `Z/M`-valued
cocycle over `G`, driven by the branch-symbol sequence — the object whose
character `e(t·o/M)` a twisted transfer operator would weight.

**The integer offset itself is NOT a Birkhoff sum.** `log o_d` grows
**linearly** in the crossing index `d`: per-orbit slope median
**0.5108** (mean 0.5111), and the mean increment
`E[log o_{d+1} − log o_d] = 0.5097` nats/crossing. (Cross-check: at 3.80
renewals/crossing this is 0.134 nats/renewal — exactly the prior measured
per-renewal log-growth `0.134`.) The offset is a **projective /
multiplicative** observable of a volume-expanding (det-3) map; it carries
no bounded per-step additive summand. Only two objects are stationary
observables of `G`: the **residue** `o_d mod M` (finite cocycle) and the
**scale-invariant** `z = o/(o+beta) ∈ (0,1)`.

**`G` symbolically.** The return word (branch symbols between consecutive
`F`-crossings) has mean length **3.80** and only odd lengths occur
(`1: .365, 3: .305, 5: .134, 7: .087`, …) — the alternation
`F · (C·T)^m`. Dominant words: `dF`, `DF` (.184/.181, a bare crossing),
then `dF.dC.T`, `DF.DC.T` (.153/.152), etc. This is the Euclidean-
algorithm / Gauss-type return structure.

## (2) Correlation decay over `G` (Dolgopyat rate)

Normalized autocorrelation `ρ(n) = C(n)/C(0)`,
`C(n) = ⟨f, \bar f∘G^n⟩ − |⟨f⟩|²`, pooled over orbits (noise floor
`≈ 1/√(#pairs) ≈ 0.0011`). Induced spectral gap from the prior Ulam
transfer operator: `|λ₂| = 0.21` per return (`⇒` rate `−ln|λ₂| = 1.56`).

| observable | ρ(1) | ρ(2) | ρ(3) | fitted \|λ\| | rate | R² |
|---|---|---|---|---|---|---|
| `z = o/(o+beta)` | −0.0668 | −0.0150 | 0.0033 | 0.47 | 0.75 | 0.95 |
| `e(o/6)` (cos+isin) | 0.0396 | 0.0310 | 0.0388 | ~1 | ~0 | — |
| `e(o/8)` | −0.0041 | 0.0834 | −0.0012 | n/a | n/a | — |
| `e(o/16)` | −0.0014 | −0.0163 | −0.0003 | n/a | n/a | — |
| `e(o/384)` | −0.0003 | 0.0014 | 0.0010 | 0.76 | 0.28 | — |
| `[o mod 6 = 1]` | 0.1294 | 0.0681 | 0.0323 | **0.137** | **1.99** | 0.888 |

**Reading.** The **character** observables `e(t·o/M)` decorrelate within a
**single return** — every `|ρ(1)|` sits at or barely above the 0.0011
floor, so their fitted "rates" are noise and are reported only for
honesty. The two observables that carry resolvable signal both agree with
a large gap: the scale-invariant `z` has `|ρ(1)| ≈ 0.07` and is gone by
lag 2; the residue indicator `[o mod 6 = 1]` decays cleanly at rate
**1.99** (`|λ| ≈ 0.14`, R² 0.89). All measurements are **consistent with
correlations dropping ≥ 5× per return** — i.e. an induced spectral gap of
the measured order (`|λ₂| ≈ 0.17–0.21`), and no slower mode. This is the
Dolgopyat-type exponential mixing the effective route would rely on; the
residue phase is, to measurement precision, **decorrelated after one
crossing** (strengthening the prior "offsets ≈ i.i.d." finding).

## (3) Effective equidistribution rate of `o_d mod M → uniform`

Per-crossing relaxation rate = `|λ₂|` of the **pooled residue transition
operator** `P_M[r,s] = Pr(o_{d+1}=s | o_d=r)` (restricted to the
admissible odd residues; `o` is always odd). Exponential-in-`d` gives
`TV ~ |λ₂|^d`. Since size grows geometrically
(`E[Δlog size] = 0.510`/crossing), a size `N` is reached in
`~ ln N / 0.510` crossings, so the residue bias at scale `N` is
`TV ~ N^{−α}` with `α = −ln|λ₂| / 0.510` — **polynomial in N**, which is
exactly the natural-density input.

| M | k | \|λ₂(P_M)\| | rate `−ln\|λ₂\|` | **α(N)** | d→1e−3 | d→1e−6 |
|---|---|---|---|---|---|---|
| 3 | 3 | 0.2025 | 1.597 | **3.13** | 4.1 | 8.4 |
| 4 | 2 | 0.1673 | 1.788 | **3.51** | 3.5 | 7.3 |
| 5 | 5 | 0.0188 | 3.974 | **7.80** | 1.7 | 3.4 |
| 6 | 3 | 0.2025 | 1.597 | **3.13** | 4.1 | 8.4 |
| 8 | 4 | 0.1673 | 1.788 | **3.51** | 3.7 | 7.6 |
| 16 | 8 | 0.1673 | 1.788 | **3.51** | 3.8 | 7.7 |
| 384 | 192 | 0.2028 | 1.596 | **3.13** | 4.3 | 8.7 |

(M=2 trivial: `o` is always `≡ 1`.)

**Prime factorization of the mixing rate.** The rates cluster by prime:
`|λ₂|(mod 2^k) ≈ 0.167`, `|λ₂|(mod 3) ≈ 0.203`, `|λ₂|(mod 5) ≈ 0.019`.
`M=6 ≡ M=3` because `o` is deterministic mod 2; `M=4,8,16` share the
2-adic rate; `M=384 = 2^7·3` inherits the **slowest** prime (mod 3). So
the binding equidistribution exponent is the **mod-3 one: α ≈ 3.13**, and
`TV(o_d mod M) ≲ C·N^{−3.1}` for every tested `M` — a strong polynomial
rate.

**Direct TV check (M=6, worst-case start).** `TV(P_6^d row, uniform)`:

```
 d :  0       1       2       3       4       5      6+
TV :  0.6667  0.1678  0.0244  0.0067  0.0019  0.0011  (floor ~0.001)
```

Fitted `TV(d) ~ exp(−1.26 d)` (`|λ| ≈ 0.28`, the early-transient value
sitting just above the asymptotic `|λ₂| = 0.20`). The marginal reaches
`10^{−3}` of uniform in **~4 crossings** and saturates the sampling floor
by ~5.

**Annealed marginal across the ensemble (M=6)** at crossing index `d`:
`TV ≈ 0.005–0.017` for all `d` (uniform-sample floor `≈ 0.013`). The
seed-varied marginal is **already at uniform within sampling from d=0** —
the equilibration is faster than a finite ensemble can resolve, which is
the expected fingerprint of exponential-in-`d` relaxation.

**This does not contradict the "door bolted" result.** Two distinct
convergences must not be conflated:
- the **annealed marginal** `law(o_d mod M)` here converges
  **exponentially in d ⇒ polynomially in N** (`α ≈ 3.1`) — the
  natural-density / almost-all input, which is **favorable**;
- the **empirical frequency along one orbit** converges only at the
  **CLT rate `n^{−1/2}`** (`2026-09-04-effective-equidistribution.md`) —
  which is what blocks localizing a **single** orbit below the
  exponentially-shrinking fatal window.

Method B needs the former (marginal, for natural density); single-orbit
decision needs the latter (bolted). Both prior findings stand.

## (4) Modular-surface framework: honest assessment

**The linear parts are det ±3 — this is `GL(2, Z[1/3])`, not `SL(2,Z)`.**
`det Clin = −3`, `det Flin = +3`, `T = I`. The semigroup is
**volume-expanding (non-unimodular)**, confirmed by the measured
geometric growth `0.51` nats/crossing. Consequences for the
effective-equidistribution literature:

- **Sarnak–Ubis (horocycle equidistribution at the cusp), Strömbergsson
  (effective equidistribution of long closed horocycles), effective
  Ratner / Einsiedler–Margulis–Venkatesh** all concern **unipotent flows
  on `SL(2,ℝ)/Γ` with `Γ` a lattice (unimodular)**. Our object is an
  **expanding** self-map, not a measure-preserving unipotent flow on a
  finite-volume homogeneous space, so these theorems **do not apply
  directly**. There is no genuine `SL(2,ℤ)\H` unipotent orbit here to
  which one could hand the offset. *(These are real papers; I am confident
  about the unimodularity hypothesis they require and about the det-±3
  arithmetic here. I am NOT certain of each paper's exact hypotheses and
  am flagging that rather than asserting a precise theorem match.)*

- **The applicable engine is Dolgopyat / twisted transfer operators**, not
  homogeneous dynamics. `R` is a piecewise-Möbius **expanding Markov
  (Gauss-type)** map (branch endpoints `ρ_{k+1} = 1/(3ρ_k+1)`,
  accumulation `ρ* = (√13−1)/6`, expansion `λ = 6/(7−√13) = 1.768`). Its
  natural extension is a section of a geodesic flow on a Hecke/congruence
  modular quotient (classical Series-type continued-fraction ↔ geodesic
  correspondence; the "3" is the congruence datum). Effective
  equidistribution for **such** maps comes from the **spectral gap of the
  weighted/twisted transfer operator** `L_{s,t}` (Ruelle–Pollicott
  resonances), which the correlation decay in (2) and the residue
  operator `|λ₂|` in (3) both measure directly.

- **So: does the literature "plausibly supply the rate"?** Honest answer:
  **not through the modular-surface (horocycle/Ratner) route** — the
  non-unimodularity blocks it — **but the analogous transfer-operator
  (Dolgopyat) route does supply an exponential ⇒ poly-in-N rate, and every
  measurement here is consistent with it** (`α ≈ 3.1`). The remaining gap
  is not conceptual but a **theorem gap**: converting the measured `|λ₂|`
  into a rigorous rate needs a Dolgopyat non-concentration / Diophantine
  (uniform-non-integrability) estimate for **this specific** three-
  generator `GL(2, Z[1/3])` semigroup — the **same** machine-specific
  Lasota–Yorke/Dolgopyat lemma the transfer-operator scaffold already
  isolated as the one open input for the almost-all theorem
  (`2026-09-04-transfer-operator.md`). The effective-rate INPUT that
  Method B wants is therefore **available in the correct (transfer-
  operator) framework and measured favorable**; it is **not** available as
  an off-the-shelf modular-surface citation.

---

## Verdict (all measurement)

- **Cocycle structure exact:** `o_d mod M` is a `Z/M`-factor of the affine
  cocycle on `(Z/L)²` — **0 mismatches / 873,557 crossings × 8 moduli**.
  The integer offset is projective (log grows 0.51/crossing), **not** a
  Birkhoff sum.
- **Correlation decay:** characters `e(t·o/M)` decorrelate within **one
  return** (`|ρ(1)|` at the 0.001 floor); resolvable observables (`z`,
  `[o mod 6=1]`) decay at rate `≈ 1–2`, i.e. `|λ| ≈ 0.14–0.47`,
  consistent with the induced gap `|λ₂| ≈ 0.17–0.21`.
- **Equidistribution rate:** per-crossing residue relaxation
  `|λ₂(P_M)| ≈ 0.17–0.20` (slowest prime mod 3), rate `≈ 1.6`, giving
  **`TV(o_d mod M) ~ N^{−3.1}`** — exponential-in-d ⇒ **polynomial-in-N**,
  the natural-density input. Marginal reaches `10^{−6}` of uniform in
  ~8 crossings.
- **Framework:** the rate is supplied by the **Dolgopyat / twisted-
  transfer-operator** engine, **not** by horocycle/Ratner effective
  equidistribution (non-unimodular, det ±3). The one missing piece is the
  machine-specific Dolgopyat/Lasota–Yorke estimate — the pre-existing open
  lemma, not a new obstruction.

## Honesty box

- **This is a measurement, not a proof, and decides no machine.** The
  cocycle verification (item 1) is exact and reproducible; the rates
  (items 2–3) are **fitted/empirical constants at finite horizon**
  (873,557 crossings, bitlen cap 340), not theorems. `|λ₂|`, `α`, and the
  0.51 growth are measured, not proven.
- **Two convergences are kept distinct on purpose.** The favorable
  **exponential-in-d / poly-in-N** rate here is the **annealed marginal**
  (almost-all / natural-density input). It does **not** upgrade
  single-orbit decidability: the empirical-frequency floor along one orbit
  is still the CLT `n^{−1/2}` of `2026-09-04-effective-equidistribution.md`
  ("door bolted"). Nothing here reopens that door.
- **The framework assessment (item 4) is reasoned, with uncertainty
  flagged.** The det-±3 non-unimodularity is exact arithmetic; the claim
  that Sarnak–Ubis / Strömbergsson / effective-Ratner require
  unimodularity and hence do not apply directly is my reasoning about
  their scope — I did not verify each paper's precise hypotheses and do
  not assert a specific theorem match. The positive claim ("Dolgopyat /
  twisted transfer operator supplies the correct engine") rests on the
  measured spectral gap and standard transfer-operator theory, still
  conditional on the open machine-specific non-concentration lemma.
- No Lean file, no `.tex`, no other results doc, and no certificate is
  changed by this measurement.

```
Reproduce:  python3 qgkit/bb6/effective_mixing.py   (~27s, deterministic)
```
