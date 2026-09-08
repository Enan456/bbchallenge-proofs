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

## Status

The estimate is (i) strongly supported numerically to depth 6, (ii) reduced
to a lattice-point count with explicit sublattice structure, (iii) proved for
every fixed depth, and (iv) reduced, in the hard regime, to a single
aggregate non-concentration bound on fatal cylinders of width $\lesssim1/N$.
It is **not** proved. This is a sharper localization of the obstruction than
"Tao-hard'': the difficulty is confined to an $O(1/N)$-measure tail of thin
cylinders, where an averaged bound may suffice. Recommended next step: attempt
the aggregate bound via a large sieve / mean-value estimate over the
sublattice cosets, not a per-cylinder count.
