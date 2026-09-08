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

### 1. Native-resolution model-to-exact transfer — the one that can bite
**This was mislabeled "routine" in the drafts; it is the crux.** All the
operator analysis (gap, UNI, LLT) is proved for the \emph{analytic} model
$G$; the object we must control is the \emph{exact integer} map, which is the
model plus fixed translations, an $O(1/a)$ coordinate perturbation. For the
measure theorem this is standard (Keller--Liverani). For the density form it
is not, and here is precisely why:

- detecting $o_d\in\{1,3,5\}$ is a native-resolution statement, requiring the
  twisted family $\Lop_{i\xi}$ up to frequency $\xi\sim M\sim S\sim a$;
- the perturbation phase is $\e(i\xi\,\delta)$ with $\delta=O(1/a)$, so at
  $\xi\sim a$ the perturbation is $\e(i\cdot O(1))$ --- **$O(1)$, not small.**

So Keller--Liverani stability, which needs the perturbation small in the
relevant norm \emph{uniformly in $\xi$}, does **not** transfer the gap to the
exact map at the frequencies the density statement needs. Two honest ways out,
both real work:
  - **(a) Work the operator theory on the exact integer dynamics directly**
    (the numerics already do this), and re-derive the Dolgopyat gap there. The
    obstacle: Dolgopyat/Naud need analyticity or a clean $C^{1+\alpha}$
    structure; the exact map is a lattice object, not literally analytic, so
    one needs a symbolic/anisotropic-norm formulation adapted to it. Plausible,
    not automatic.
  - **(b) Bound the model-to-exact offset discrepancy at native resolution.**
    Show the exact offset equals the model offset up to a correction whose
    distribution is itself equidistributed, so the fatal event transfers with a
    controlled error. This is a genuine estimate, not bookkeeping.
This item is where I would spend the first month, and where a referee would
push hardest. It is not believed fatal --- Tao's Collatz proof resolves the
analogous integer-vs-model tension --- but it is the real remaining
mathematics.

### 2. The precise Dolgopyat citation is not off-the-shelf
We invoke "Dolgopyat 1998 / Naud 2005 / Stoyanov 2011," but our map is a
\emph{countable}-branch Gauss-type map with an accumulation point $\rho^\ast$.
Dolgopyat's original theorem is for finitely many branches / Axiom A flows;
Naud's is for specific analytic families (Gauss map, Schottky). The countable
branches plus the accumulation point are a real technical wrinkle: one must
either cite the infinite-branch extension (Aaronson--Denker--Urba\'nski;
Melbourne--Terhesiu for the operator-renewal side) or verify the tail estimate
that lets the finite-branch machinery apply. The summable-variation control we
have is the right input, but the exact theorem to cite (or adapt) must be
pinned; I would not hand-wave "settled theory" here in the manuscript.

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
| 1. native-resolution model-to-exact | new estimate | **moderate** — the one to settle first |
| 2. precise gap citation (countable + accumulation) | pin/adapt a theorem | low--moderate |
| 3. full UNI over long words | lemma | low |
| 4. joint LLT upper bound | write-out | low (given 1--3) |
| 5. seed equidistribution + sum | routine | negligible |

## Honest verdict, revised

The measure form is complete and unconditional. The density form is **not**
"complete modulo one citation" as an earlier draft claimed --- that
overstated it. It is: \emph{reduced}, rigorously, to the analytic core, with
the reduction and the UNI non-degeneracy genuinely proved; and it rests on
(i) an analytic spectral-gap theorem that must be pinned for the
countable-branch/accumulation setting, and, more seriously, (ii) a
native-resolution model-to-exact transfer that is a real estimate, not
bookkeeping. Items 3--5 are standard write-ups. The honest one-line status:
\emph{the density form is a well-posed problem entirely inside established
dynamics, with one genuine estimate (item 1) still to be proved and one
citation (item 2) still to be pinned; the rest is writing.} That is a
finishable paper for the right collaborator, and it is not finished. The
specific certified orbit stays Collatz-hard throughout.
