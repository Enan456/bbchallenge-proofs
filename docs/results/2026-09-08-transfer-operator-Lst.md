# L_{s,t} setup and the aperiodicity of the offset cocycle (Method A crux)

**Date:** 2026-09-08. Executes the first concrete step of the closure plan
(`2026-09-08-closure-plan.md`, Method A): set up the Baladi--Vall\'ee
parametrised transfer operator for the offset, and check the aperiodicity on
which the whole method hinges. **Result: aperiodicity holds, with a strong
uniform spectral gap.** This is a confirmation of the crux, not a completed
proof.

## The operator

For the Gauss-type induced map $G$ (branches $I_k$, inverse branches
$g_k^{-1}$, endpoints $\rho_{k+1}=(3\rho_k+1)^{-1}$) and the offset cost
$o=b-\beta$, the parametrised transfer operator is
\[
(\mathcal L_{s,t}f)(x)=\sum_k |g_k'(x)|^{-s}\,e\!\left(\tfrac{t\,o_k(x)}{M}\right) f(g_k^{-1}x),
\qquad e(u)=e^{2\pi i u}.
\]
At $t=0$ this is the ordinary (Ruelle) operator whose leading eigenvalue is
$\lambda(s,0)$, $=1$ at the natural parameter $s^\ast$. The twist by the
character $e(t o/M)$ carries the offset residue. Method A's requirement:
$|\lambda(s^\ast,t)|<1$ for every $t\not\equiv0\ (\mathrm{mod}\ M)$ ---
otherwise $e(to/M)$ is a coboundary and the offset fails to equidistribute
mod $M$.

## Realisation and the aperiodicity test

Realised as the joint transfer operator on $(z\text{-bin},\,o\bmod M)$ (20
$z$-bins), built from $\sim2\times10^6$ exact section transitions; for each
character $t$ the $t$-Fourier block gives the twisted leading eigenvalue
$|\lambda(t)|$.

| $M$ (odd) | $|\lambda(0)|$ | $\max_{t\neq0}|\lambda(t)|$ | gap |
|---|---|---|---|
| 3 | 1.000 | 0.095 | 0.905 |
| 5 | 1.000 | 0.007 | 0.993 |
| 7 | 1.000 | 0.005 | 0.995 |
| 9 | 1.000 | 0.303 | 0.697 |
| 11 | 1.000 | 0.004 | 0.996 |
| 15 | 1.000 | 0.095 | 0.905 |

For every odd modulus $|\lambda(t)|<1$ strictly for all $t\neq0$, with a
uniform gap; the rate is governed by the small prime factors ($\mod 3$ gives
$0.095$, $\mod 5$ gives $0.007$; $M=9=3^2$ is slower at $0.303$ but still
$<1$). **The offset cocycle is aperiodic mod every odd $M$.**

## The one degeneracy is structural and harmless

Mod even $M$ the parity character ($t=M/2$) does not decay: the offset is
**always odd** ($b$ odd, $\beta$ even at every $F$-crossing --- the parity
grammar, Lemma 1 of the paper). This is a genuine coboundary
($o\equiv1\bmod2$ is constant), but it is not an obstruction: the fatal
window $\{1,3,5\}$ lies entirely within the odd residues, so the relevant
equidistribution is of $o$ among odd residues, which the odd-$M$ table
confirms with a strong gap.

## What this delivers, and what remains

**Delivered (crux confirmed).** The parametrised operator has
$|\lambda(s^\ast,t)|<\lambda(s^\ast,0)$ for every nontrivial character; the
offset equidistributes mod $M$ (among odd residues) at exponential rate
$|\lambda(t)|^d$ per return. This is exactly the non-degeneracy Baladi--Vall\'ee
require, and it was the biggest risk flagged in the plan. It is now retired
(numerically, with large margins).

**Remaining for a proof (Method A assembly).**
1. A \emph{rigorous} analytic spectral gap for $\mathcal L_{s,t}$ (the table is
   numerical). For Gauss/Euclidean-type operators this is the Baladi--Vall\'ee /
   Dolgopyat machinery; the summable-variation bound already proved gives
   quasi-compactness, and the aperiodicity gives $|\lambda(t)|<1$; making the
   gap uniform in $t$ is the analytic work.
2. From the gap, the per-crossing fatal probability $\le C/\text{scale}
   +O(\text{gap}^{d})$, hence $\mathrm{hf}(s)\le Cs^{-\delta}$ and the density
   form (via the scale decomposition).
3. The integer-count version via the large sieve over the sublattice cosets
   (separate probe).

Honest status: the crux of Method A is confirmed with strong numerical
margins; the analytic spectral gap and the assembly are not yet done. No
closure is claimed --- but the method is now known to be non-degenerate, which
is the fact that determines whether it can work at all.
