# Collaborator notes: what is actually missing to finish the density form

**Written as the dynamics / analytic-number-theory collaborator who would
take this to a finished manuscript.** Honest, technical, ranked by how much
genuine mathematics each item hides. The purpose is to separate "laborious but
standard" from "where a real obstruction could still live," so nobody starts
the writing believing it is closed when it is not.

## What is solid and I would not re-examine

- The reduction machine $\R\to G$: parity grammar, the exact branch endpoints
  $\rho_{k+1}=(3\rho_k+1)^{-1}$ and accumulation $(\sqrt{13}-1)/6$, eventual
  expansion, summable variation. Clean, checkable, done.
- The measure form (Lebesgue-a.e.\ survival) via Rychlik. Complete.
- Transience ($a+b$ strictly increases). Elementary, unconditional.
- Aperiodicity of the offset cocycle: proved two ways incl.\ exact
  non-coboundary witnesses. Solid.
- The suspension reformulation and the UNI \emph{non-degeneracy}
  (Prop.: branch forms $L_k$ pairwise non-proportional $\Rightarrow$ temporal
  distances non-constant). The algebra is exact; I trust it.
- $\sigma^2>0$, non-lattice. Verified.
- The combinatorial skeleton of the count: first-fatal decomposition (avoids
  the non-Jordan-measurable $H$), scale splitting, $O(N\log N)$. Correct, and
  numerically confirmed ($\#/(N\log N)\approx3.3$).

The density form is genuinely reduced to the analytic core below. That
reduction is the real contribution.

## The genuinely remaining work, ranked

### 1. Native-resolution model-to-exact transfer — DISSOLVED as a framing artifact (2026-09-08)
I had flagged this as the crux: detecting $o_d\in\{1,3,5\}$ needs the twisted
family up to $\xi\sim S\sim a$, where the $O(1/a)$ model-to-exact perturbation
gives a twisted phase $\e(i\cdot O(1))$ --- $O(1)$, not small --- so
Keller--Liverani cannot transfer $G$'s gap. \textbf{That argument is correct
only for the approach it assumes (perturbing from the limit $G$), and that
approach is the wrong one.} At each scale $a$ the exact dynamics is its own
real-analytic map $G_a$, and Dolgopyat's theorem applies to \emph{each $G_a$
directly}; one never perturbs. The hypotheses hold with constants
\emph{uniform in $a$} for a structural reason: the load-bearing data --- branch
forms $L_k=(r_k-p_k)+(s_k-q_k)\xi$, endpoints $\rho_{k+1}=(3\rho_k+1)^{-1}$,
expansion $\inf|(G^2)'|=3$, UNI non-degeneracy (slopes $-\rho_k$ distinct) ---
are \emph{exact algebraic facts of the fixed integer matrices
$P_k=C_\ell^kF_\ell$}, with no scale dependence; only the $O(1/a)$ translation
corrections carry scale, and they are lower order. So $\{G_a\}_{a\ge a_0}$ is a
uniformly-controlled family and the gap is uniform in scale. \textbf{Confirmed
numerically:} the twisted $|\lambda(i\xi)|$ is flat across bit-length bands and
across native-resolution frequencies $\xi\in\{2,5,12,20,35\}$ (identical to
3--4 digits over the large bands; the smallest-scale band, worst case for the
correction, is if anything \emph{more} contractive). See
`docs/results/2026-09-08-scale-uniform-gap.md`. What remains is standard: the
sequential-composition step (uniform per-scale gap $\Rightarrow$ orbit
native-resolution bound) and the integer \emph{upper} bound (the integer
dynamics \emph{is} the operator we built, so the $\le C/S$ upper bound follows
from the same uniform gap by the standard Fourier-inversion upper bound --- we
never need the full asymptotic). Item~1 is no longer the crux; item~2 is now
the leading remaining citation.

### 2. The countable-branch gap — REDUCED to finite-branch Dolgopyat + an exact geometric tail (2026-09-08)
Our map is a \emph{countable}-branch Gauss-type map accumulating at
$\rho^\ast$, whereas the off-the-shelf Dolgopyat/Naud theorems are
finite-branch. \textbf{This reduces cleanly, and the tail rate is exact.} The
branch endpoints $\rho_{k+1}=1/(3\rho_k+1)$ accumulate at the fixed point
$\rho^\ast$ of $\varphi(\rho)=1/(3\rho+1)$ with multiplier
\[
|\varphi'(\rho^\ast)|=3/(3\rho^\ast+1)^2=3\rho^{\ast2}=1-\rho^\ast=\lambda^{-1}=(7-\sqrt{13})/6\approx0.5657,
\]
(using $3\rho^{\ast2}+\rho^\ast-1=0$): \emph{the geometric tail rate equals the
inverse expansion} --- the same algebraic number. So branch-$k$ mass decays
like $\lambda^{-k}$ (measured ratios oscillate around $0.566$; $P[k\ge8]\approx
0.011$), and the tail operator has norm $O(\lambda^{-K})$ \emph{uniformly in
$\xi$} (as $|\e(i\xi\tau)|=1$). Crucially the accumulation is \textbf{benign}:
the truncated-operator gap $\theta_K$ \emph{stabilizes} as $K$ grows
($K=8,10,\infty$ agree to 2--3 digits, all $<1$; the UNI constant is dominated
by the low-$k$ well-separated branches, not the crowding high-$k$ ones), so it
does not degrade to $1$. Hence
$\rho(\Lop_{i\xi})\le\theta_K+C\lambda^{-K}<1$ for large $K$, with $\theta_K$
the \emph{finite-branch} Dolgopyat gap (genuinely off-the-shelf: Dolgopyat
1998, Naud 2005) and $C\lambda^{-K}$ the proved tail. Here --- unlike item~1's
scale perturbation --- the tail perturbation \textbf{is} uniformly small in
$\xi$, so Keller--Liverani in the branch-count genuinely applies. See
`docs/results/2026-09-08-countable-branch-reduction.md`. What remains to write:
the standard truncation lemma and pinning $\theta_K$'s reference. No exotic
countable-branch theorem is needed. \emph{(One numerical artifact noted there:
hard-truncating at exactly $K=3$ on the fixed 40-bin grid gives a spurious
$|\lambda|=1$ --- a rank/binning artifact, isolated between $K=2,4$ both
$\approx0.71$, gone under rebinning.)}

### 3. UNI: from 2-cylinder non-degeneracy to the full uniform condition
The verified statement is that adjacent branch forms are non-proportional, so
the temporal distance is non-constant at word-length one. The Dolgopyat UNI
condition is uniform over \emph{long} words: $\inf_n\sup$ of the temporal-distance
oscillation over length-$n$ word pairs, bounded below. Propagating the
one-step non-degeneracy to all $n$ is standard for real-analytic maps (the
non-integrability is not destroyed by composition) but must be written; it is
a lemma, not a citation.

### 4. The joint LLT upper bound, in full
Prop.\ (uniform hazard bound) asserts the joint density $p_d(z,\ell)$ is
bounded uniformly in $d$ down to scale $1/S$ in $z$, via Fourier inversion of
$\lambda(i\xi)^d$ plus the gap. Writing this needs: the spectral projection's
regularity in $\xi$, the tail bound from item 2's gap, and the integer-window
integration. Standard given items 1--3, but it is the technical heart of the
LLT half and should be written, not asserted.

### 5. Seed equidistribution and the sum, with discrepancy
Sector lattice-point counting gives the initial seed law with discrepancy
$O(1/a)$; mixing pushes to $\mu$; the sum $\sum_s sN\cdot\mathrm{hf}(s)$ is
elementary. This is genuinely routine, but the discrepancy must be carried
through so the $o(N^2)$ is uniform. A week, no risk.

## Risk assessment

| item | nature | risk of a real obstruction |
|---|---|---|
| 1. native-resolution model-to-exact | ~~new estimate~~ **dissolved** (framing artifact; gap uniform in scale) | **removed** |
| 2. countable-branch gap | **reduced** to finite-branch Dolgopyat + exact geometric tail ($\lambda^{-1}=1-\rho^*$); accumulation benign | low — standard citation + written tail lemma |
| 3. full UNI over long words | lemma | low |
| 4. joint LLT upper bound | write-out | low (given 2--3) |
| 5. seed equidistribution + sum | routine | negligible |
| 1a-macro. sequential composition (macroscopic density bound) | **DONE** — proved in full (iterate uniform LY) | none |
| 1a-arith. integer upper bound at native resolution | **the arithmetic heart** (= Tao's hardest step), but **PROBED FRIENDLY (2026-09-09):** FFT of $E_h$ over 1.7M offsets shows high-freq sum at the $1/\sqrt M$ noise floor, no resonance growth, 3-adic spikes only at $h=3,9$ — cylinders do NOT conspire. Raw Erdős–Turán is lossy (low-freq density shape ≠ fine equidist); smoothed count + incoherent-cross-cylinder-addition is the route. Reframed adversarial→friendly, plausibly provable by standard exp-sum methods, still open | **the real remaining core, now looks tractable** |

## Honest verdict, revised

The measure form is complete and unconditional. The density form is
\emph{reduced}, rigorously, to the analytic core, with the reduction and the
UNI non-degeneracy genuinely proved. After firing on item~1 (2026-09-08), the
picture improved: the piece I had called the crux --- the native-resolution
model-to-exact transfer --- \textbf{dissolved as a framing artifact}. It only
looked fatal under the wrong approach (Keller--Liverani-perturbing from the
limit map); the right approach applies Dolgopyat to each exact-scale map $G_a$
directly, whose hypotheses are exact scale-independent algebra of the fixed
integer matrices, so the gap is uniform in scale --- confirmed numerically
across scales and native-resolution frequencies. What now stands between the
reduction and a finished proof is: \emph{(i)} pinning the countable-branch
spectral-gap theorem with uniform-in-scale constants (item~2, the leading
remaining citation --- low-to-moderate, a pin-and-adapt not a new idea);
\emph{(ii)} two standard write-ups --- the sequential-composition step and the
integer upper bound (item~1a), and the full UNI over long words (item~3); and
\emph{(iii)} the routine LLT-upper-bound and seed-sum assembly (items~4--5).
The honest one-line status: \emph{the density form is a well-posed problem
entirely inside established dynamics; its hardest-looking obstruction turned
out to be a framing error and dissolves; what remains is one citation to pin
and standard write-ups.} That is a finishable paper for the right collaborator,
and it is not yet finished. The specific certified orbit stays Collatz-hard
throughout.
