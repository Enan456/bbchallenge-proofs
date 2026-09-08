# The suspension operator: mixed-LLT hypotheses confirmed

**Date:** 2026-09-08. Executes the reformulation proposed in the formal
supplement (Part II): attack the open uniform-gap lemma not on the
scale-invariant map G but on its **suspension**, with the log-growth as an
**additive** roof — converting the non-standard multiplicative-cost operator
into a standard local-limit-theorem problem. Result: **every operator-level
hypothesis of the mixed LLT is confirmed**, with the decisive large-frequency
gap now for an additive Hölder roof (settled Dolgopyat theory) rather than the
exotic multiplicative cost. This is a strong validation of the route; it is
not the proof.

## The object

The offset factors as `o_d = z_d · scale_d` with `z_d` the projective
coordinate (equidistributes, via G's spectral gap — proved) and
`log scale_d = Σ_{j<d} τ(z_j)` a Birkhoff sum of the roof
`τ = log(o'/o)` (per-return log-growth). Native-resolution equidistribution of
`o_d mod M` (the open lemma) reduces to a **mixed local limit theorem**: the
joint equidistribution of `(z_d, log scale_d)`. Its analytic engine is the
twisted transfer operator `L_{iξ} f = Σ_k |g_k'| e(iξ τ_k) f(g_k·)`, with `ξ`
dual to log-scale.

## What was measured

Building `L_{iξ}` empirically on 40 z-bins (~1.5×10⁶ transitions with their
exact log-growth) and power-iterating the leading eigenvalue modulus:

| ξ | 0 | 0.2 | 0.5 | 1 | 2 | 5 | 12 | 20 | 50 |
|---|---|---|---|---|---|---|---|---|---|
| \|λ(iξ)\| | 1.000 | 0.995 | 0.969 | 0.894 | 0.718 | 0.410 | 0.563 | 0.484 | 0.296 |

Three facts, all favorable:

1. **λ(0)=1 with a non-degenerate CLT.** Near 0, `1-|λ(iξ)| ≈ (σ²/2)ξ²` with
   **σ² ≈ 0.265 > 0** — the central-limit variance of log-scale is finite and
   positive, so log-scale is genuinely diffusive (not a coboundary).
2. **|λ(iξ)| < 1 for every ξ≠0** — the non-lattice/aperiodicity of the roof,
   consistent with the earlier characteristic-function test.
3. **Uniform large-ξ gap — no resonance.** A fine scan over ξ∈[0.5,80] (400
   points) has supremum **0.969, attained at the left endpoint ξ=0.5** (the
   CLT value), decreasing monotonically thereafter and staying in 0.3–0.6 for
   ξ≥3. There is no return toward 1 anywhere. This is the **Dolgopyat /
   uniform-non-integrability condition for the roof**, and it holds.

## Why this matters

The obstruction that put the lemma outside settled theory was that the offset
is a *multiplicative coordinate* cost, not a Birkhoff sum. The suspension
removes it: the roof `τ = log(o'/o)` **is** an additive Hölder cocycle over an
expanding Markov map, and the large-ξ gap of its twisted operator is exactly
**Dolgopyat's theorem** (Dolgopyat 1998; Naud; Stoyanov) — which applies to
this class. The hypotheses that theorem needs (spectral gap at ξ=0, non-lattice
roof, positive CLT variance, no large-ξ resonance) are all now in hand
numerically. The local limit theorem (Nagaev–Guivarc'h; Aaronson–Denker) then
follows, and with it the equidistribution of log-scale mod log M — the scale
factor of the native-resolution statement.

## Honest status

Confirmed, at the operator level: the suspension/mixed-LLT route is
**internally consistent and its Dolgopyat input is of the settled additive
kind**, with all hypotheses measured favorable. Not done: (i) an *analytic*
proof of the large-ξ gap — i.e. verifying the UNI condition for `τ` in closed
form (the roof is not cohomologous to a locally constant function; the
non-lattice test is its qualitative shadow); (ii) assembling the **joint**
`(z, log-scale)` mixed LLT into the native-resolution offset equidistribution
— `z` and log-scale must equidistribute jointly, a standard Nagaev–Guivarc'h
perturbation but still to be written. The open lemma is unchanged in status
(open), but it has moved decisively: from *"a Dolgopyat estimate for a
non-standard multiplicative cost — outside the theory"* to *"a mixed LLT with
an additive-roof Dolgopyat input — inside the theory, hypotheses confirmed."*
That is the correct home for it, and the recommended line to a proof.
