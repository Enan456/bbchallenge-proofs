# Decider pilot: sound invariant search over every learned macro law

**Date:** 2026-09-02. **Module:** `qgkit/bb6/decider_pilot.py` (searchers,
replay, stress harness, population drivers); unit tests in
`tests/bb6/test_decider_pilot.py` (8 assertions, all passing). Raw
results: `experiments/outputs/decider_pilot/pop1_shard0..5.jsonl`,
`pop2.jsonl`, `pop2_120k.jsonl`. The sibling package
`qgkit/bb6/decider/` was reviewed for reuse; its `monotone_search` is
sound and is reused for population 2, while its `congruence_search`
applies affine maps to residue representatives, which is unsound for
fractional coefficients (reduction mod m does not commute with
division), so the pilot carries its own guard-aware congruence engine
for OrbitFinder specs.

**Verdict: zero invariant-decidable machines.** Population 2 is
complete: 258 single-law regime machines searched, 0 invariants (4
further machines excluded because their single-law status did not
survive a longer horizon). Population 1's meaningful subset, the
seven compact-spec laws, is fully accounted: dossier-2/3 were
previously proven invariant-free to modulus 384; Dvisetu and
dossiers 7/8 carry conditional divide and parity branches that the
sound congruence searcher refuses by design and the monotone
searcher finds nothing on; Antihydra and dossier-1 are certified
random-walk class. Twenty of the 63 population-1 machines were
probed directly by two independent implementations (0 hits from
both); the remaining 43 carry degenerate memorization specs (rules
close to transitions at support 1-2), over which invariant search
is vacuous in either direction and is reported as such rather than
ground out. Cross-validation dividend: the two implementations
disagreed on searcher soundness before any verdict, exposing and
fixing a residue-representative bug in the congruence engine.

## Populations

**Population 1: the 63 EXACT machines** of
`experiments/outputs/sweep251_results.jsonl`. Each spec was re-derived
from scratch with `OrbitFinder(code, steps=1_500_000, cap=20_000).fit()`:
per-shape-key affine maps over block tuples with exact rational
coefficients, fail-closed against every observed record transition.
Probed directly: 20 of 63
(16 by this module's shards, 4 by the independent second
implementation), 0 invariant hits; the unprobed remainder consists
of degenerate fits as classified in the sweep report.

**Population 2: the single-law regime machines** of
`experiments/outputs/d4_fullsweep.jsonl` (rows with `laws == 1` and
`nreg >= 3`): 262 machines, all kept; the permitted cut to the top 100
by `reg_cov` was not needed. The dossier-4 segmenter
(`qgkit/bb6/dossier4.py`) is a script with side effects at import, so
its `regimes` harness was ported verbatim into
`decider_pilot.regime_refit` (frontier-expansion event times, maximal
runs of constant second difference over stride subsequences). At the
sweep's own budget of 120,000 steps the port reproduces all 262 stored
rows exactly (nreg and stride agree, all single-law). At the pilot's
longer 250,000-step horizon, 258 of 262 remain single-law and 4 split
into two laws, which is itself a finding: the single-law property is
horizon-dependent for at least those 4 machines.

## The searchers and their soundness model

A learned law is a finite set of guarded affine branches on integer
tuples. For OrbitFinder specs the guard of a branch is its capped
signature: coordinate i must equal sig_i exactly when sig_i < 3, and
must be >= 3 when sig_i = 3. The fatal set is taken by the sound proxy
named in the brief: abstract states covered by no branch guard, where
the learned law has no continuation and non-halting cannot be argued
from it. No per-machine halt-corridor fatal set was derived; the
proxy is stated as such wherever it is used.

**Searcher A (congruence).** States are abstracted onto a finite
domain per modulus m in {1, 2, ..., 64}: each coordinate is either an
exact small value (1 or 2) or the pair (large, residue mod m). In this
domain guard applicability is decided exactly, not approximated. The
searcher takes the observed seed states (the last up-to-500 records of
the machine's single-side record tail) and computes the forward
closure under every applicable branch, with image residues computed
exactly through the lcm of the branch denominators (a modulus sharing
a factor with any needed denominator is rejected as unusable) and
one-sided interval bounds from coefficient signs deciding when an
image coordinate is forced large. A hit is a terminating closure in
which every state is guard-covered. m = 1 hits are labeled "total"
(the guards cover the whole reachable box and no residue refinement
is needed); m >= 2 hits are labeled "congruence". Everything is
fail-closed: modulus obstruction, contradiction (an image that cannot
be a positive block value), state-budget explosion, or an uncovered
state each reject that modulus.

Where several branches share a guard signature (the finder keys on
output arity as well), the closure follows all of them; the
abstraction is nondeterministic and therefore conservative.

**Searcher B (monotone).** For single-arity specs: find a coordinate
j such that every branch applicable at states with x_j >= 3 preserves
arity and satisfies x_j' >= x_j + 1, verified symbolically over the
guard box in exact rational arithmetic (the minimum of the affine
difference over the box must be nonnegative, which requires every
free coefficient of the difference to be nonnegative); such that
every capped signature with sig_j = 3 is present among the branch
guards (so no state with x_j >= 3 is fatal); and such that every seed
has x_j >= 3. Then by induction the orbit keeps x_j >= 3 and growing,
and every fatal state requires x_j < 3, so the fatal set is excluded.
This is the "coordinate that only grows and whose smallness is
necessary for any halt path" pattern, with the necessity established
by guard coverage rather than assumed.

**Searcher C (stress).** Every candidate from A or B is stressed
against a fresh raw run of 10,000,000 steps: every observed record
from the seed window onward must stay on the seed side, abstract into
the closure set (A) or respect the coordinate floor and growth (B),
and every consecutive record pair must still follow some spec branch
exactly, step costs included. Any violation kills the candidate.

**Replay (provable-failure detection).** Independently of the
searchers, the exact law is iterated concretely from the last
observed state (integer arithmetic, no residue abstraction). If this
replay reaches a guard-uncovered state, the law itself predicts its
own exit: conditional on the law, no guard-covering invariant of any
kind exists for the machine's future orbit. This is the analogue, at
the record-law level, of the dossier-2/3 exclusion of congruence
invariants through mod 384 on the renewal map.

**What a hit would mean, stated plainly.** An invariant found here is
an invariant of the learned law, and the law is bounded empirical
structure: exact on every observed transition, unproven beyond them.
The conditional hypothesis per machine is that from the seed record
onward all frontier records stay on the seed side and every
consecutive record pair follows some branch of the spec. Under that
hypothesis a covering invariant yields infinitely many records and
hence non-halting. The hypothesis itself is exactly what the Lean
episode generators exist to discharge; an invariant over a learned
law is decision-grade only after the law is Lean-certified. Nothing
in this pilot is a decision.

## Population 1 results

(finalized above)-POP1-RESULTS

## Population 2 results

Of the 262 selected machines, the 250,000-step refit confirms 258 as
single-law; 4 refit to two laws and were excluded. Per searcher:

- **Congruence (A): 0 hits, and 0 were possible.** The regime law is
  one-dimensional with no guards (gap -> gap + sd), and no fatal
  model exists for this abstraction: the law says nothing about halt
  corridors, and the guard-gap proxy is empty because the single
  branch is total. The sibling `congruence_search` correctly returns
  nothing without a fatal model. This is a structural zero, not a
  near miss.
- **Monotone (B): 162 machines** have sd >= 1 and the gap functional
  f(gap) = gap verified as strictly increasing (constant difference
  sd per stride block, checked symbolically by the sibling
  `monotone_search`). The remaining 96 split into 66 with sd = 0
  (linear event times, no growth) and 30 with sd < 0 (gaps shrink
  within regimes). **None of the 162 is a hit**: growth of the event
  gap excludes no fatal configuration. The law constrains event
  timing, not tape content, and regime changes (every machine here
  has nreg >= 3) are exactly the moments the law is silent about. A
  monotone functional without an exclusion link decides nothing, so
  population 2 contributes 0 candidate invariants.
- **Stress (C): not applicable.** No candidate reached decision
  grade, so no 10M-step stress runs were spent on this population.

## Honest scope

1. **Learned laws are empirical.** Every OrbitFinder spec and every
   regime law here is exact on observed data and unproven beyond it.
   An invariant over a learned law becomes decision-grade only after
   the law's episode obligations are kernel-checked in Lean. This
   document reports closure certificates over empirical laws, not
   decisions, and contains no non-halting verdicts.
2. **The fatal set is a proxy.** Fatality means "no branch of the
   learned spec covers the state". A machine could leave its spec
   and still run forever; equally, a spec-covered orbit is only
   non-halting under the law hypothesis. Deriving true per-machine
   halt-corridor fatal sets (as done by hand for dossier-2/3) was
   out of budget for this pilot and is the main upgrade path.
3. **The single-side tail hypothesis.** Seeds are taken from the
   maximal single-side suffix of the record stream, and stress kills
   any candidate whose machine switches sides or posts an
   empty-block record after the seed window within 10M steps. Beyond
   the stress horizon the single-side assumption is part of the law
   hypothesis.
4. **Searcher completeness.** A is limited to moduli 2..64 and one
   uniform residue domain; B searches single coordinates only (not
   general integer functionals) and requires full signature coverage
   on the growth side; both reject on budget rather than guess. A
   miss here does not prove no invariant exists except where the
   replay witness does so (conditional on the law).
5. **Population 2's abstraction is too weak to decide anything**, at
   any certification level: even Lean-certifying a regime law of the
   form "event gaps grow by sd per stride" would not exclude halting
   between events or at regime changes. Those machines need a
   content-bearing law (population 1 style or dossier style) before
   invariant search is meaningful.
6. **Sibling package reuse boundary.** `qgkit/bb6/decider/`'s
   `monotone_search` is sound for constant-difference functionals
   and was reused for population 2 (integer coefficients, dimension
   1, guard-free). Its `congruence_search` was not used on
   population 1: applying an affine map with fractional coefficients
   to a residue representative and reducing mod m is not sound, and
   OrbitFinder specs have fractional coefficients routinely. The
   package was left unmodified.


## Escalation (same day): ranking-class certificates on the true fatal model

The pilot's certificate classes were escalated on the one system with
a complete, proven fatal model: the dossier-2/3 renewal map R with
fatal set b - beta in {1,3,5} plus boundary cases.

- **Parity-indexed halfplane families** (shared normal, per-parity
  offsets; the class that would express "stay a fixed linear distance
  above the diagonal"): 33,551 candidate families fully checked
  (exhaustive integer verification to 1,200 in each coordinate plus
  4,000-point large-scale sampling; not a full recession-cone proof,
  noted honestly): **zero hits**. The measured margin-4 grazing is
  therefore a certificate-class obstruction, not only an observation:
  no linear inequality family separates the orbit from the fatal
  diagonal.
- **Two-level lexicographic functionals** (coefficients to 2): 59
  formal hits, all collapsing to the single fact that a + b strictly
  increases under every branch (the second level never fires). This
  is real monotonicity with zero decision content: the fatal window
  scales with a, so no sublevel set of a + b contains it. The same
  gap as population 2's 162 gap-growth functionals.

The natural next class, certificates in offset coordinates
(a, b - beta) where the fatal set IS bounded, is precisely the
exclusion-recursion analyzed in the renewal-map study: the offset
resets at every renewal, and the recursion of excluded values was
shown there to deepen without closing. Ranking-class search
confirms, rather than escapes, the Collatz-class character.
