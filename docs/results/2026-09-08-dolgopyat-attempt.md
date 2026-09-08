# Dolgopyat uniform-gap attempt: setup and ingredients confirmed, hard core not closed

**Date:** 2026-09-08. Attempt at the one remaining lemma
(`2026-09-08-methodA-consolidation.md`): a uniform-in-character spectral gap
for the twisted transfer operator $\mathcal L_{s,t}$, which would close the
density form. Honest outcome: the operator is set up, aperiodicity and a
strong fixed-$M$ frequency-band gap are confirmed, **but the binding regime
--- native resolution $M\sim\text{scale}$ --- is not established, and it is
exactly the hard analytic content. The gap is supported, not proved.**

## What was set up and confirmed

The continuous-frequency operator, realised on $(z\text{-bin},\,o\bmod M)$,
was scanned over a fine character grid ($M$ up to $240$). Over the character
band $\xi=t/M$ bounded away from the resonances $\{0,\tfrac12\}$:
\[
\sup_{\xi\in[0.03,0.47]\cup[0.53,0.97]}|\lambda(\xi)|\approx 0.085,
\]
**stable as $M$ grows** ($30\to240$), with no resonance (no $\xi$ where
$|\lambda|\to1$). The profile is flat and small; the parity character
$\xi=\tfrac12$ is the only non-decaying one (structural, harmless). This is a
genuine uniform gap --- but for the **fixed-$M$** regime, where the offset
$o\gg M$ and $o\bmod M$ decorrelates almost instantly.

## Why that is not enough --- the binding regime

To detect the fatal set $\{1,3,5\}$ exactly one must resolve the offset to
$O(1)$, i.e.\ work at modulus $M\sim\text{scale}$, where $o$ and $M$ are
comparable and the coarse-residue mixing above does not apply. A direct test
--- the integer distribution of $o\le21$ conditioned on scale $S$ --- is
**inconclusive by rarity**: at $S\sim10^6$ the event $o\le21$ has probability
$\sim21/S\sim10^{-5}$, so a $2.7\times10^4$-crossing band sees essentially
zero. The regime that carries the density form's difficulty is precisely the
one too rare to sample, and the required statement --- that the fixed-$M$ gap
**transfers** to native resolution $M\sim\text{scale}$ --- is the actual
content of the Dolgopyat/Baladi--Vall\'ee theorem, not a corollary of the
fixed-$M$ numerics.

## Honest status of the Dolgopyat route

The hypotheses of the relevant theorem are in hand: quasi-compactness
(summable variation, proved); aperiodicity ($|\lambda(t)|<1$, confirmed two
ways incl.\ rigorous non-coboundary witnesses); a strong fixed-$M$ gap (this
note). What is **not** done is the theorem itself for our operator --- and our
setting is non-standard: the cocycle is affine (not a Birkhoff sum), the
semigroup is non-unimodular ($\det\pm3$, $GL(2,\Z[1/3])$), and the cost is a
coordinate, not an additive functional. Baladi--Vall\'ee's uniform gap is
proved for the classical Euclidean/Gauss cost; adapting it to this affine,
non-unimodular offset cocycle is real analytic work (a Dolgopyat
oscillatory-cancellation / non-local-integrability estimate at native
resolution), which this attempt does not carry out.

**Verdict.** The Dolgopyat uniform gap is **supported** (ingredients all
confirmed, no resonance in the accessible regime) but **not proved** in the
binding regime. The density form remains conditional on exactly this analytic
lemma. No closure is claimed. The honest lesson: the fixed-$M$ mixing is easy
and confirmed; the native-resolution transfer is the genuine difficulty, and
it sits at the same place --- small offset at large scale --- that every route
in this campaign has converged on.
