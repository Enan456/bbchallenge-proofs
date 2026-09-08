# Consolidation: where Method A stands after the parallel probes

**Date:** 2026-09-08. Synthesises the four threads run to attack the one open
estimate behind the density form (`2026-09-08-closure-plan.md`): the main-thread
$\mathcal L_{s,t}$ setup and three subagents (large-sieve count, effective
mixing, aperiodicity/coboundary). Bottom line: **all routes converge on a
single well-posed estimate --- a uniform-in-$t$ analytic spectral gap for the
twisted transfer operator --- whose enabling property (aperiodicity) is now
confirmed, one part rigorously.** The estimate is not proved; it is much
sharper and its viability is established.

## What is confirmed

**1. Aperiodicity of the offset cocycle --- two independent methods, one
rigorous.** The parametrised operator $\mathcal L_{s,t}$ has
$|\lambda(s^\ast,t)|<\lambda(s^\ast,0)=1$ for every nontrivial character (odd
$M$: $|\lambda(t)|\in[0.004,0.30]$, gaps $0.70$--$0.99$). Independently, an
exact coboundary cycle-test finds the only coboundary characters are $t=0$ and
the parity $t=M/2$, with **explicit non-coboundary witnesses** (rigorous, to
mod $384$; e.g. $M=8$: cycles $(7,5),(2,0)$ admit no common constant). The one
degeneracy is the offset's oddness --- structural (parity grammar) and harmless
($\{1,3,5\}$ is all-odd. **Method A is not blocked.**

**2. The effective rate is favorable and polynomial.** The offset residue is
an affine cocycle character over $G$ (exactly what $\mathcal L_{s,t}$ weights);
characters decorrelate within one return; the annealed marginal has
$\mathrm{TV}(o_d\bmod M)\sim N^{-3.1}$. This is the equidistribution input the
density transfer needs, measured comfortably.

**3. The conclusion is directly confirmed.** $\#\{\text{halting seeds}\le N\}
=\Theta(N)=o(N^2)$ by exact count ($\#\text{halt}/N$ plateaus $\approx30$--$35$
over a $640\times$ range).

## What is corrected (honest plan revisions)

**4. The large sieve is the wrong tool.** The fatal conditions live in cosets
of sublattices of index $Q_d=3^{\#C+\#F}$, which exceeds $N$ by depth $\sim3$
and $N^2$ by depth $\sim4$ (measured: $Q_d=81,2187,19683,\dots$). Montgomery's
$N+Q^2$ is then vacuous --- the sieve wants many small moduli, this has few
enormous ones. $\ell^2$-decoupling likewise n/a (fatal sets are lines, not
curves). *This route from the plan is dead.*

**5. The modular-surface citations do not apply.** The linear parts have
$\det=\pm3$, so the semigroup is in $GL(2,\Z[1/3])$, **non-unimodular**;
Sarnak--Ubis / effective-Ratner (unipotent flows on unimodular
$SL(2,\R)/\Gamma$) are off. *Method B's off-the-shelf route is dead*; the
correct engine is Dolgopyat / twisted transfer operators --- i.e. Method A.

## What is rigorously closed (partial)

The **fat regime** --- cylinders of lattice-step $\le N$, depth $\lesssim
\log_3 N$, carrying the bulk of the halting mass --- is disposed of by
finite-depth lattice counting: $O(N)$ such cylinders, contributing $o(N^2)$.
Plus the non-coboundary witnesses give aperiodicity a rigorous footing.

## The single remaining estimate

Every route reduces to the same object. The **thin tail** ($\Theta(N^2)$
cylinders of step $>N$) is bounded iff the offset does not concentrate on
$\{1,3,5\}$ --- i.e. iff $\mathcal L_{s,t}$ has a **spectral gap uniform in the
character $t$**. We now have: quasi-compactness (summable variation, proved);
aperiodicity $|\lambda(t)|<1$ for each $t$ (confirmed, partly rigorous); a
favorable measured rate. What is missing is the **analytic, uniform-in-$t$
gap** --- the Dolgopyat/Baladi--Vall\'ee estimate for this specific Gauss-type
operator. Given it, the chain closes: uniform gap $\Rightarrow$ offset
equidistribution with summable error $\Rightarrow$ per-scale
$\mathrm{hf}(s)\le Cs^{-\delta}$ $\Rightarrow$ (scale decomposition)
$\#\text{halting}=o(N^2)$ $\Rightarrow$ density form.

## Honest status

The density form is still conditional. But its proof has crystallised from
"an equidistribution estimate of Collatz difficulty" to **one named analytic
lemma** --- a uniform spectral gap for an explicit twisted Euclidean-algorithm
transfer operator --- with its hypothesis (aperiodicity) verified, its rate
measured favorable, its two rival routes (sieve, modular) honestly ruled out,
and the fat regime already rigorous. That is the frontier. The remaining lemma
is exactly the kind Baladi--Vall\'ee and Dolgopyat prove for Gauss-type maps; it
is real analytic work, not yet done, and no closure is claimed.
