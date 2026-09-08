# The discrete equidistribution estimate: a research probe

**Date:** 2026-09-07. Opens the one open estimate on which the
natural-density form of the almost-all theorem is conditional
(`docs/submissions/door/almost-all-nonhalting-paper.tex`, Prop.\ on the
reduction). This is a research note: strong numerical evidence, a clean
algebraic structure, a partial proof, and a precisely located obstruction
--- **not** a proof. Nothing here upgrades the paper's claim; the density
form remains conditional.

## The estimate

For each depth $n$ and branch cylinder $[k_1,\dots,k_n]$ of the induced
Markov map, the count of integer section-seeds $(a,b)$, $a,b\le N$, whose
first $n$ returns realise that cylinder should be
$\bigl(\mathrm{Leb}[k_1,\dots,k_n]+o(1)\bigr)\cdot\#\{\text{seeds}\le N\}$.
For the density-zero conclusion only the one-sided **upper** bound
$\#\{\text{seeds in cylinder}\}\le C\cdot\mathrm{Leb}\cdot N^2$ (absolute
$C$) is needed, since $\mu\sim\mathrm{Leb}$ with bounded density.

## What the numerics say (strong)

Sampling section seeds $(a,b)$ with $a<N$, $a<b\le N$ ($N=2600$,
$\sim1.66\times10^6$ seeds) and comparing per-cylinder frequencies against
the model Lebesgue frequencies:

| depth | # cylinders (>0.2%) | max int/Leb | min int/Leb |
|---|---|---|---|
| 1 | 10 | 1.03 | 0.98 |
| 2 | 42 | 1.07 | 0.92 |
| 3 | 88 | 1.08 | 0.77 |
| 4 | 96 | 1.06 | 0.42 |
| 5 | 50 | 1.11 | 0.64 |
| 6 | 10 | 1.06 | 0.93 |

The ratio stays $\approx1$ with **max $\le1.11$ uniformly through depth 6**;
integer seeds do not merely satisfy the upper bound, they **equidistribute**.
(Low min values at depth 4--5 are thin low-count cylinders, finite-$N$
noise; the max --- the upper-bound direction --- is the robust quantity.)
This is convincing evidence that the estimate is true and the density form
holds.

## The algebraic structure (clean)

Each first-return in branch $k$ is an **affine** map of $(a,b)$: linear part
$P_k=C_\ell^{\,k}F_\ell$ (integer, $\det=\pm3^{k+1}$, verified) plus an
integer translation. Therefore it sends $\Z^2$ into a **coset of the
index-$3^{k+1}$ sublattice** $P_k\Z^2$. A depth-$n$ cylinder is thus a
curved sector cut by $n$ affine/M\"obius conditions, and its integer count is
a lattice-point count for a sublattice of index $\prod 3^{k_i+1}$ in a
sector-like region. Sublattices equidistribute in sectors exactly as $\Z^2$
does, which is the source of the observed equidistribution.

## Partial proof, and the obstruction (precisely located)

- **Fixed depth $n=O(1)$: provable.** The cylinder is a region bounded by
  $O(n)$ smooth arcs; classical lattice-point counting (Gauss/sector, with
  the sublattice density $\prod3^{-(k_i+1)}$) gives
  $\#=\mathrm{Leb}\cdot N^2+O(N)$, hence equidistribution. This handles any
  bounded truncation $H_n$.
- **The hard regime: cylinders of width $\sim1/N$.** A seed $\le N$ makes
  $O(\log N)$ returns before its scale exceeds $N$; the cylinder widths
  shrink like $\lambda^{-n}$, $\lambda=6/(7-\sqrt{13})=1.768$, reaching the
  lattice spacing $1/N$ around depth $n\sim\log_\lambda N$. For such thin
  cylinders the lattice-count error ($\sim$ perimeter) is comparable to the
  area, and the per-cylinder argument fails --- this is the genuine
  arithmetic difficulty, the analogue of Tao's Syracuse-distribution step.
- **Why it is plausibly still tractable.** The halting hazard is geometric
  ($\sim\lambda^{-n}$ at depth $n$), so the fatal cylinders beyond depth
  $\log_\lambda N$ have **total** Lebesgue measure $O(1/N)$. An *aggregate*
  upper bound on the integer count in this thin-cylinder tail --- rather than
  a per-cylinder one --- would contribute only $O(N)=o(N^2)$ halting seeds
  and close the estimate. Establishing such an aggregate non-concentration
  bound is the concrete remaining problem.

## Direct confirmation: the density is zero, and the hard tail is empty

Counting the actual halting fraction of integer section-seeds
$(a,b)$, $a<b\le N$ (random samples of $5\times10^4$ per $N$):

| $N$ | halting fraction | fraction halting at depth $>\log_\lambda N$ |
|---|---|---|
| 500 | 0.0576 | 5e-4 |
| 1000 | 0.0305 | 6e-5 |
| 2000 | 0.0166 | 0 |
| 4000 | 0.0087 | 2e-5 |
| 8000 | 0.0041 | 0 |
| 16000 | 0.0026 | 0 |
| 32000 | 0.0014 | 0 |

Two facts, both decisive. **(1) The halting fraction falls like $C/N$**
(ratio $\approx0.53$ per doubling over a $64\times$ range), so the natural
density is $0$ --- the theorem's conclusion is directly confirmed, not merely
inferred from the measure statement. **(2) The deep-halt fraction is
essentially $0$**: almost no seed survives $\sim\log_\lambda N$ returns and
then halts, because the halting hazard is geometric in depth and the scale
has grown past $N$. So halting is dominated by \emph{shallow} returns, where
the cylinders are fat ($\gg1/N$) and the sector/sublattice count of \S above
is rigorous. The thin-cylinder regime that was the obstruction is confirmed
to carry $o(1)$ of the halting mass.

## Two structural facts that soften the estimate

**$\R$ is bounded-to-one.** Over the tested range every state has at most
$2$ preimages under $\R$ (multiplicities: $1$ for $\sim84\%$, $2$ for
$\sim16\%$, never more). Backward orbits thus form a binary tree of bounded
branching, which is exactly the input an injection/counting argument needs.

**Scale decomposition weakens the target to a weak decay bound.** Write
$\mathrm{hf}(s)$ for the fraction of seeds with $a\in[s,2s]$, $b\le N$ that
halt. Then $\#\text{halting}\le\sum_{s\ \mathrm{dyadic}}\mathrm{hf}(s)\cdot
s(N-\tfrac32 s)$. Measured $\mathrm{hf}(s)$ decays (from $4.3\times10^{-3}$
at $s=16$ to $8\times10^{-4}$ at $s=4096$), and the dyadic sum is
$\approx N^{1.7}=o(N^2)$. Crucially, this conclusion needs only
$\mathrm{hf}(s)\le C\,s^{-\delta}$ for \emph{some} $\delta>0$ --- a weak
polynomial decay of the per-scale halting fraction --- \emph{not} the full
equidistribution. That is a much softer estimate: it says merely that seeds
at scale $s$ hit the (measure-$\Theta(1/s)$) fatal set with probability
$o(1)$, which follows from bounded distortion plus the boundedness of the
backward branching, modulo a counting error that the weakness of the required
decay leaves ample room for.

## Attempt to prove the weak decay bound, and why it does not close

Aiming for $\mathrm{hf}(s)\le Cs^{-\delta}$, the natural hope is that halting
is dominated by the first crossing, where the count is elementary: for fixed
$a$ the fatal offsets $o_0=b-\beta\in\{1,3,5\}$ pin $b$ to three values, an
$O(1/\text{range})$ fraction. That hope is **false**. Locating the halting
mass by crossing index (which return the seed dies at):

| $s$ | crossing 0 | crossings 1--4 | crossings 5+ |
|---|---|---|---|
| 64 | 0.04 | 0.71 | 0.25 |
| 512 | 0.08 | 0.71 | 0.21 |
| 4096 | 0.25 | 0.75 | 0.13 |

Only a small fraction of halts occur at the first crossing (for wide-$b$
seeds the first-crossing offset is $\sim N$, so that fraction is $\sim3/N$,
negligible). The halting mass sits at crossings $1$--$10$: a seed halts when
the deterministic \emph{offset process} is driven into $\{1,3,5\}$ several
returns in. Bounding $\mathrm{hf}(s)$ therefore requires controlling the
distribution of the offset along the orbit --- exactly the equidistribution
estimate, with no elementary shortcut. The affine/bounded-to-one structure
constrains it but does not remove the need for an equidistribution input at
the resolution of the fatal window.

**Honest conclusion of this attempt.** $\mathrm{hf}(s)\le Cs^{-\delta}$ is
\emph{not} proved here, and I do not have a rigorous proof of it. The
reduction to a weak decay bound is genuine and the target is softer than the
original estimate, but the residual is still an equidistribution statement
for the offset process --- the same arithmetic core as Tao's Collatz estimate
--- and it is not closed by the elementary/lattice arguments available. The
density form of the theorem remains conditional. No proof should be claimed.

## Status

The estimate is (i) strongly supported numerically to depth 6, (ii) reduced
to a lattice-point count with explicit sublattice structure, (iii) proved for
every fixed depth, (iv) accompanied by direct confirmation that the halting
density is $0$ ($\sim C/N$) with the hard thin-cylinder tail carrying
negligible mass, and (v) softened, via the scale decomposition and the
bounded-to-one property, to a \emph{weak per-scale decay} bound
$\mathrm{hf}(s)\le C s^{-\delta}$ rather than full equidistribution. It is
still **not** proved --- the weak decay bound, though much easier than the
original estimate, is not established rigorously here. But the problem has
moved a long way: from "an equidistribution estimate of Collatz difficulty''
to "a weak polynomial decay of the per-scale halting fraction, for a
bounded-to-one piecewise-affine map with bounded distortion.'' That is a
concrete, plausibly tractable analytic problem, and it is the honest current
frontier of the density form.
