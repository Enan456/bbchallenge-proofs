# A plan to close the density form: two methods, and what to borrow from modern analysis

**Date:** 2026-09-08. The measure form of the almost-all theorem is proved
(`docs/submissions/door/almost-all-nonhalting-paper.tex`). The density form
is conditional on one estimate; the honest state after direct attack
(`2026-09-07-discrete-equidistribution-probe.md`) is that halting mass sits
at crossings 1--10, so the estimate is genuinely an **equidistribution of the
offset process at the resolution of the fatal window $\{1,3,5\}$** --- no
elementary shortcut. This note plans its closure along the two methods
already identified, and surveys the leading analysis worth importing, with an
honest read on what transfers.

## The precise target

Let the induced first-return map $G$ on the section carry the integer offset
$o_d=b_d-\beta_d$. The density form follows from either of:

- **(T) Offset equidistribution.** Along $\mu$-typical orbits, and for
  integer seeds up to $N$, the offset $o_d$ equidistributes mod the small
  moduli that resolve $\{1,3,5\}$, with a summable error; equivalently the
  per-scale halting fraction $\mathrm{hf}(s)\le Cs^{-\delta}$.
- **(C) Aggregate lattice count.** $\#\{(a,b)\le N:\text{some }o_d\in\{1,3,5\}\}
  =o(N^2)$, via counting integer points on the union of fatal lines
  $L_{\text{cyl}}(a,b)\in\{1,3,5\}$ across cylinders.

The map is our advantage: $G$ is a **Gauss-type (Euclidean-algorithm)
transfer map** --- countable full-branch, piecewise-M\"obius, endpoints
$\rho_{k+1}=(3\rho_k+1)^{-1}$, expansion $\lambda=6/(7-\sqrt{13})$, and each
return is **affine with integer matrix** $P_k$ ($\det=\pm3^{k+1}$),
bounded-to-one. This is far more structured than Collatz, and it is exactly
the setting where distributional theorems for arithmetic dynamics exist.

## Method A --- Arithmetic: parametrised transfer operators + sieve/decoupling

The single most on-target tool is **Baladi--Vall\'ee**, *Euclidean algorithms
are Gaussian* (J. Number Theory 110 (2005), 331--386) and the Dolgopyat--Baladi--Vall\'ee
line: attach to the Gauss-type map a **transfer operator with a parameter**,
$\mathcal L_{s,t}\,f(x)=\sum_k |g_k'(x)|^{s}\,e^{2\pi i t\,c_k(x)}\,f(g_k x)$,
where $c_k$ is the arithmetic cost (here the offset / the linear form $L$).
Analytic perturbation of the leading eigenvalue $\lambda(s,t)$ in $t$ gives
the characteristic function of the offset, hence its distribution, with an
**effective error from the spectral gap** we already exhibit (Lemma on
summable variation). This is precisely how they proved the Gaussian law for
Euclidean-algorithm costs; the offset $\bmod$ the fatal window is such a cost.

Concrete steps.
1. Write the fatal event $o_d\in\{1,3,5\}$ as a finite character sum
   $\frac1M\sum_{|t|<M}\hat{\mathbf 1}(t)\,e(t\,o_d/M)$ over small $M$.
2. Express $\mathbb E[e(t\,o_d/M)]$ via $\mathcal L_{s,t}^{\,d}$; the leading
   eigenvalue $\lambda(s,t)$ has $|\lambda(s,t)|<\lambda(s,0)$ for $t\not\equiv0$
   (aperiodicity of the offset cocycle mod $M$ --- checkable via the mod-$M$
   BFS already run; the offset is not cohomologous to a constant).
3. Sum over $d$: geometric decay in $d$ from the gap gives per-crossing fatal
   probability $\le C/\text{scale}+O(\text{gap}^d)$, then $\mathrm{hf}(s)\le
   Cs^{-\delta}$.
4. **Integer version** (the count (C)): the number of $(a,b)\le N$ on the
   fatal lines is bounded by the **large sieve** (Montgomery) over the moduli
   $M$ and the sublattice cosets $P_k\Z^2$; where the lines cluster on short
   arcs, **$\ell^2$ decoupling** (Bourgain--Demeter, *Ann. Math.* 182 (2015))
   controls the lattice points on the associated curve. Both are the modern
   sharp tools for "integer points in thin dynamically-defined sets".

Risk: step 2's aperiodicity is the crux; if the offset cocycle is degenerate
mod some $M$ the method needs a twist. Numerics (mod-384 BFS, offset
equidistribution to $<0.3\%$) say it is non-degenerate.

## Method B --- Dynamical: effective equidistribution on the modular surface

We established (`2026-09-04-modular-dictionary-probe.md`) that the offset
process is an $SL(2,\Z)$-type action; the induced map is Gauss-like, whose
natural extension is the geodesic flow on the modular surface. The tool is
**effective equidistribution / rapid mixing**:

- **Dolgopyat**, *On decay of correlations in Anosov flows* (Ann. Math. 147
  (1998)), and Baladi--Vall\'ee's spectral gap for the Gauss map, give
  exponential decay of correlations with explicit rate --- the quantitative
  input the measure proof used only qualitatively.
- **Effective horocycle/geodesic equidistribution** (Sarnak; Str\"ombergsson;
  Sarnak--Ubis, *horocycle flow at prime times*) transfers the offset
  distribution to arithmetic progressions of seeds with a polynomial error,
  which is what the density transfer needs to replace the failed
  Koksma--Hlawka step (the halting set is not Jordan-measurable, so one needs
  the *rate*, not just the limit).

Concrete steps: identify the offset as a Birkhoff sum over the geodesic;
apply the effective ergodic theorem with the Dolgopyat rate; discretise to
integer seeds via the sublattice structure. Method B and Method A are two
faces of the same transfer operator; A is cleaner for the arithmetic count,
B for the conceptual measure-to-density passage.

## What to borrow from recent Navier--Stokes analysis --- honestly

The user asked specifically for leading PDE/analysis, especially recent
Navier--Stokes. Here is a candid triage; two items genuinely transfer, one is
a conceptual mirror, one does not apply.

**(i) Quantitative propagation / Carleman machinery --- TRANSFERS as method.**
Tao, *Quantitative bounds for critically bounded solutions to Navier--Stokes*
(Ann. Math. 2021, arXiv:1908.04958) turns qualitative Escauriaza--Seregin--\v
Sver\'ak regularity into explicit bounds using **Carleman estimates** for
backward uniqueness and unique continuation, plus a **pigeonhole across dyadic
scales** ("epochs of regularity"). Our problem has the same shape: a quantity
(the offset distribution) evolving under a nonlinear map, which we must show
cannot *concentrate* on a small set (the fatal window). The dyadic-scale
pigeonhole is exactly our scale decomposition $\mathrm{hf}(s)$; the Carleman
philosophy --- a weighted energy that forbids a solution from vanishing
(here: from concentrating) faster than a fixed rate --- is a real template for
proving the offset cannot pile onto $\{1,3,5\}$. This is the most transferable
NS idea, at the level of strategy (weighted-energy / frequency-localised
monotonicity), not a plug-in theorem.

**(ii) Frequency-localised energy / bilinear estimates --- TRANSFERS as
technique.** The modern NS well-posedness toolkit (Koch--Tataru $BMO^{-1}$;
Kenig--Koch--Tataru bilinear/paraproduct estimates) is about controlling
interactions across frequencies. Our transfer operator with parameter is a
frequency ($t$) localisation; the aperiodicity/non-degeneracy of the offset
cocycle is a bilinear non-resonance condition. The techniques for proving
such non-resonance (stationary phase, $TT^\ast$) are directly usable in
Method A step 2.

**(iii) Embedded computation / supercriticality --- CONCEPTUAL MIRROR, not a
tool.** Tao, *Finite time blowup for an averaged 3D Navier--Stokes equation*
(J. AMS 2016, arXiv:1402.0290), forces blowup by embedding a self-replicating
"fluid machine" --- the exact theme of Busy Beaver: computation inside a
dynamical system. This illuminates *why* our specific-orbit problem is
Collatz-hard (a machine can be embedded, so single orbits are undecidable),
but it constructs halting; it offers no upper-bound technique for
*almost-all* non-halting. Keep it as orientation, not method.

**(iv) Convex integration --- DOES NOT APPLY.** De Lellis--Sz\'ekelyhidi /
Buckmaster--Vicol convex integration builds wild, non-unique, pathological
solutions. It is a construction of counterexamples --- the wrong direction for
an equidistribution upper bound. Note it only to set it aside.

## Sequencing, and honest risk

1. **First: Method A via Baladi--Vall\'ee** (highest hit-probability). Our map
   *is* a Euclidean-algorithm transfer map; they proved exactly this class of
   distributional theorem. Task: verify offset-cocycle aperiodicity mod small
   $M$ (largely done numerically), then run the parametrised-operator
   argument. If it closes, it closes both (T) and, with the large sieve, (C).
2. **In parallel: the large-sieve count (C)** directly, which may give the
   crude $o(N^2)$ upper bound even without full equidistribution --- enough for
   density zero.
3. **Method B** as the conceptual backbone and the route for the
   measure-to-density passage (the non-Jordan-measurable halting set needs the
   effective *rate*, supplied by Dolgopyat).
4. **NS import**: use the Carleman/weighted-energy strategy (i) and the
   non-resonance techniques (ii) as the method for the one hard lemma
   (offset non-concentration), should the clean transfer-operator route stall.

**Honest risk.** None of these is a guaranteed close; each is a real theorem's
worth of work. But the target is now specific and well-matched: it is a
distributional theorem for a Euclidean-type transfer map, for which
Baladi--Vall\'ee is essentially a template, backed by an effective spectral
gap we already have. That is a materially better position than "a Collatz-hard
equidistribution", and the recommended first move --- the parametrised
transfer operator --- is concrete. No claim of closure is made here; this is
the route, not the result.
