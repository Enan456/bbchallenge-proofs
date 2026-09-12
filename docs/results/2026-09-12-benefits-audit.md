# Audit: new benefits re-uncovered across the work

**Date:** 2026-09-12. A sweep of the recent arc (scale-uniform gap, countable-branch
reduction, Lemma-B coherence probe, coherence determinants, the validated
grammar extractor, the verified citations) for places where an insight proved
for one purpose turns out to unlock or strengthen something else. Rated honestly:
**[real]** = concrete, usable now; **[likely]** = strong but needs a step to
cash in; **[speculative]** = plausible, unverified. Non-benefits flagged too.

## [real] The grammar lemma is mechanizable — 18 -> ~122 conditional closures
The per-machine parity-grammar lemma was hand-proved. The Phase-1 extractor
(`grammar_extract.py`) now recovers it automatically on dossier-2/3 — alphabet,
adjacency, TT-forbidden, the `b%2` forcing invariant — with a Lean obligation.
**Benefit:** the first and most-repeated step of every conditional closure is no
longer bespoke. If the extractor generalizes across the cohort (Phase 6), the
bottleneck on scaling 18 certified closures toward the ~122 shifts from "prove a
grammar by hand" to "verify an emitted obligation." This is the single biggest
throughput lever uncovered.

## [real] Two levels of "invariant" were being conflated — and only one is blocked
The decider pilot found **zero** invariants (invariant-free to mod 384) — but
that is about the *halting/offset* dynamics. The grammar extractor finds a clean
`b%2` **forcing invariant** for the *symbolic* dynamics. **Benefit:** these are
different levels, and separating them is clarifying and usable: the symbolic
layer is highly structured (gives grammar, non-intermittency, fuel bounds for
free), and only the arithmetic offset layer is invariant-free. Earlier framing
risked "invariant-free" sounding like "no structure at all," which understates
what is provable. The honest statement is sharper: *structured symbolically,
invariant-free arithmetically.*

## [real] One determinant computation serves three ends
`det(f_i,f_j) != 0` for all offset-form pairs (depth 1 and 2), all carrying a
3-power factor with a small `r_k` cofactor. This simultaneously: (a) gives the
cross-cylinder **incoherence** for Lemma B (no proportional forms => sqrt, not
linear, accumulation); (b) **explains** why halting is invariant-free — the
coupling is 3-adic, and a modular invariant would need to see the whole 3-adic
tower; (c) confirms the **Tao analogy is exact** (his characteristic function
lives on Z/3^n). **Benefit:** a three-line computation unifies the Lemma-B
route, the invariant-free wall, and the Collatz-template positioning — these
were three separate stories and are now one structural fact.

## [likely] The scale-uniform gap argument is class-general, not dossier-2-only
Item 1 dissolved because the Dolgopyat/Naud hypotheses are *exact algebra of the
fixed branch matrices*, hence scale-independent. Nothing in that argument is
special to dossier-2: any renewal-class machine whose branch forms come from
fixed integer matrices with pairwise-distinct slopes inherits the same
scale-uniform gap. **Benefit (to cash in):** the measure-form / density route
may extend across the whole renewal sub-class (dossiers 2, 3, and their
relatives), not just the flagship — turning a single almost-all theorem into a
class theorem. Needs: check the branch-form non-proportionality per machine
(the extractor's `det` tagging already computes the inputs).

## [likely] The fuel axis of the open-set audit can be upgraded empirical -> proven
`audit_openset.py` currently *measures* the record gap to 20M steps. The grammar
-> non-intermittency -> fuel chain makes that quadratic bound a *theorem* for any
grammar-extractable machine. **Benefit:** the "fuel sound" verdict stops being
"held up to 2e7" and becomes certified, which is what a bbchallenge-grade
non-halting certificate needs. Needs: Phases 2-3 wired to the extractor output.

## [real] Naud Def 2.1 is a reusable class lemma, not a one-off citation
The gap citation is now a *named theorem whose hypothesis we instantiate* (NLI =
non-proportional branch roofs). **Benefit:** every renewal-class machine that
passes the extractor's non-proportionality check gets the spectral gap from Naud
by the same one-line instantiation — the analytic input is now boilerplate, not
a per-machine research problem.

## [real] The classifier produces the density-argument inputs for free
Phase 5's classification computes the per-symbol `det` and the log-growth `Lambda`
— which are exactly the scale-growth inputs the almost-all/density argument
consumes. **Benefit:** the aggregate route and the per-machine decider share a
data product; no separate pipeline is needed to feed the statistical attack.

## [speculative] The fail-closed completeness check is a reusable bug-catcher
The orbit-boundary contamination bug was caught by `prove_complete` refusing,
not by a test. **Benefit (if it holds up):** the forcing-invariant closure test
is a general soundness tripwire — any extraction artifact that injects a phantom
transition breaks closure and is refused. Worth watching whether it catches
other artifact classes (sampling truncation, mis-tagged symbols) as the cohort
scales.

## Non-benefits, to keep the ledger honest
- The **unconditional closure wall is unchanged.** None of the above crosses it;
  the arithmetic offset question stays Collatz-hard. Benefits are all on the
  *conditional closure / classification / aggregate* side.
- **Lemma B is not proved.** The coherence probe and determinant structure make
  it look friendly and provable-by-standard-methods, but "uniform in the
  ~lambda^d cylinders and in scale" is still unwritten.
- The **grammar extractor is validated on one machine** (the known answer).
  Generalization to the ~122 is asserted by design, not yet demonstrated.

## One-line summary
The recurring dividend this session is that **the symbolic/dynamical layer is
far more structured and mechanizable than the arithmetic layer is hard** — the
grammar extractor, the scale-uniform gap, the Naud instantiation, and the
classifier inputs all exploit that gap between "structured symbolically" and
"Collatz-hard arithmetically," and together they point at scaling conditional
closure across the cohort rather than fighting the unconditional wall.
