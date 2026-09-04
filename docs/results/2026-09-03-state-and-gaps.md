# State of the program and the gap map

> **Editorial note (main-loop verification).** The band counts in
> Section 3 depend on the exact structured/unstructured threshold,
> which is not pinned across the program's tooling. An independent
> recount with the definition `laws == 1 and nreg >= 3` gives 262
> single-law and 793 unstructured, versus this document's 289 and
> 748 under a looser threshold. The two disagreeing counts are
> themselves the finding: fixing a single band definition is a
> prerequisite for the audit harness of gap 1. What is not in doubt:
> 18 closed, 39 multi-law, 0 halts, 0 alignments.


**Date:** 2026-09-03. **Role of this document:** a skeptical
consolidation of what is proven, what is measured but unproven, where
the coverage boundary actually sits, and what an external reviewer
would attack first. Sources are cited inline; every count below was
recomputed from the named data files for this document, not copied
from earlier prose.

---

## 1. What is proven

### 1.1 The eighteen conditional closures

Eighteen machines of the 1,094-machine BB(6) holdout cohort
(`experiments/outputs/BB6_holdouts_1094.txt`) carry theorems of the
form

    Safe_X  ->  not RawHalts blankStart

checked by the Lean 4 kernel at axioms {propext, Quot.sound} with no
`sorry`, all in one green build
(`busy-beaver-core/BusyBeaverCore/*.lean`; synthesis in
`docs/submissions/closure-report.tex` and
`docs/submissions/closures-doc/closures-deep-dive.tex`). Each file is
self-contained down to Lean core: raw machine semantics, a
halt-localization corridor lemma, probe-safety segment machinery,
episode theorems, a concrete startup anchor, an executable abstract
orbit, and a transport theorem. The eighteen are Antihydra,
dossiers 1, 2, 3 (mirror pair), Dvisetu (dossier-6), rank-1
(dossier-5), and dossiers 7 through 18.

Stated as a class rather than a list: the closures span both
state-space classes the census distinguishes and all three rungs of
the grain ladder.

- **Fixed-dimension machines** (bounded tuple state spaces):
  Antihydra (hydra triple), dossier-1 (chain), dossier-2/3 (five
  integers), Dvisetu (one hole, two counters). Closed at gait grain:
  episodes are the machine's natural behaviours with exact step
  counts (crawl 10, drift (32b-41)/3, and so on), proven by
  induction.
- **Array-class machines** (word state spaces of growing dimension):
  rank-1 at cell grain (the first growing-dimension closure, zero
  folded assumptions), and dossiers 7 through 18 at single-raw-step
  grain, where the certified engine simulates every branch of the
  record law exactly, including residue cases whose first empirical
  occurrence is projected near 3x10^12 raw steps (dossier-8's g >= 2
  grand renewal; `docs/results/2026-08-31-dossier7-dossier8-laws.md`).

What "closed" means, precisely: *if* the machine's explicit orbit
conjecture holds (`SafeMetaOrbit`, `SafeWordOrbit`,
`SafeCheckpointOrbit`, and so on, one per machine), the machine never
halts from the blank tape. The reduction direction is complete and,
where tested, sharp: states violating the conjecture provably halt
within tens of raw steps (dossier-2 danger-band corners in 6 to 12
steps at K = 200,000 game episodes,
`docs/results/2026-08-30-halting-game.md`; Antihydra's realizable
dying family in exactly (3c^2+44c+125)/4 steps for odd c, verified
c = 1..79, `docs/results/2026-08-31-antihydra-parity.md`).

Exactly one closure carries a folded assumption: Dvisetu's
`SafeCheckpointOrbit` conjoins `DivideFaithful`
(`DvisetuRawTM.lean:1544,1562`), the assumption that the recursive
divide renewal realizes its abstract outputs on the tape. The other
seventeen fold nothing; their only fail-closed exits are the genuine
halt patterns and fuel.

### 1.2 The unconditional negatives

These are the program's only unconditional contributions, and they
are negative results at stated scales, not impossibility theorems.

- **No congruence-lattice invariant to modulus 384** excludes the
  dossier-2/3 fatal window (sound residue-abstraction BFS over
  (a,b) mod M, M up to 384; a genuine mod-3 conservation law exists
  but fatal-compatible residues stay reachable at every tested
  modulus). `docs/results/2026-08-26-renewal-map-analysis.md`.
- **No rotation rigidity**: branch-symbol factor complexity grows
  like 1.6^n over 10^5 renewals against n+1 for any Sturmian coding;
  the continued-fraction route fails as stated. Same file.
- **Zero invariant-decidable machines** across every learned law in
  the cohort (`docs/results/2026-09-02-decider-pilot.md`): 258
  stable single-law regime machines searched by a sound congruence
  engine (moduli 2..64) and a sound monotone engine, 0 hits; 20 of
  the 63 EXACT-spec machines probed directly by two independent
  implementations, 0 hits; the remaining 43 EXACT specs are
  degenerate memorization fits over which invariant search is
  vacuous. The 162 monotone functionals found in population 2 carry
  zero decision content (they constrain event timing, not tape
  content).
- **Ranking-class certificates refuted on the true fatal model**:
  33,551 parity-indexed halfplane families exhaustively checked to
  1,200 in each coordinate plus large-scale sampling, zero hits; 59
  lexicographic hits all collapse to a+b monotonicity, whose
  sublevel sets cannot contain the scaling fatal window. Not a full
  recession-cone proof, and stated as such. Same file, escalation
  section.
- **Census-level negatives**: 0 halts and 0 forward-backward cone
  alignments across all 1,094 holdouts at the stated horizons
  (120k-step sampling, depth-18 cones;
  `experiments/outputs/d4_fullsweep.jsonl`, fields `halted`,
  `aligns`).

### 1.3 What remains open

Every one of the eighteen conjectures. Zero machines are decided
unconditionally by this program; the documents claim zero non-halting
verdicts, and that claim is correct. The honest summary of section 1
is: eighteen machine-checked reductions, each restating one machine's
halting problem as one explicit orbit-avoidance question, plus
evidence-graded refutations of the certificate classes that would
have made any of those questions easy.

---

## 2. Empirical findings that are not theorems

Each item below is load-bearing in the program's narrative and none
of it is proven. Listed with current evidential status and what a
proof would require.

**The branching-constant series {phi, 2-adic, 1}.** Dossier-3's
abstract death cone satisfies L(k) = L(k-1) + L(k-2) exactly for
depths 2 through 12 (9, 19, 31, 50, ... 3,804 families;
`docs/results/2026-08-27-two-ended-alignment.md`), with an identified
mechanism (a terminate step flips the parity of b, so T never follows
T). The rank-1 machine's preimage multiplicity is
prod_i 2^max(0, t_i - 2) in train lengths
(`closures-deep-dive.tex`). Antihydra's abstract cone is linear with
constant exactly 1: counts observed to depth 400 (L(400) = 202), no
integer linear recurrence of order up to 12 fits, validation box
[0,13)^3 exhaustive (`docs/results/2026-08-31-antihydra-parity.md`).
Status: three exact observations at bounded depth plus mechanisms. A
proof of the Fibonacci case is a finite combinatorial lemma on branch
words without TT and is probably days of work; the Antihydra case
needs the subcritical-branching-with-immigration argument made
rigorous (backward a-drift as an absorbing constraint), which is
harder; a general theorem tying the constant to episode-alternation
rules does not yet have even a candidate statement.

**Phi changes organs: hazard versus cone.** Antihydra's death is
gambler's ruin with steps -1/+2, ruin root of r^3 - 2r + 1, equal to
1/phi = 0.618; the measured a-marginal death fraction decays at ratio
0.63 to 0.84 through a = 11 against the model's 0.618, then cuts off
deterministically (zero deaths for a >= 14 in the tested window,
(m, c) <= 48). Dossier-3 carries phi in its cone instead. Status: a
heuristic i.i.d. model plus measurements that agree until they
deterministically exceed it. A proof requires equidistribution of the
deterministic parity sequence, which is itself Collatz-hard; the
cutoff observation is unexplained and is evidence the model is not
the mechanism.

**Almost-all-seeds density.** For the dossier-2/3 renewal map R:
dying-seed fraction approximately 12/X, exact enumeration of every
seed in [X, 2X)^2 for X = 16..256, sampled to X = 2^16; deaths are
early-game only (die-by-50 equals die-by-500 at every box size);
hazard at the diagonal uniform across 30,000 seeds; sizes grow by
e^0.134 per renewal (`docs/results/2026-08-26-almost-all-seeds.md`).
For Antihydra: all deaths in a bounded counter slab, shifted boxes
death-free from [16,32)^3 exactly (36,864 seeds), latest observed
death at volley 32 among 10^5 random seeds
(`2026-08-31-antihydra-parity.md`). Status: measured density plus a
verified finite mechanism. The finite-horizon part is mechanical
lattice counting and could be formalized; the tail requires an
invariant-measure or martingale argument (worst-case additive growth
gives a divergent hazard sum, so typical multiplicative growth is
essential). This is the section-4 frontier item.

**Closed-form lethality times.** Antihydra (3c^2+44c+125)/4 for odd
c, verified c = 1..79 and spot-checked at 9, 21, 99, 999; even
c >= 4 escapes the broken grammar and does not halt within 2x10^7
raw steps (tested c = 4..10), which is an open gap between abstract
death and raw halting, not a lemma. Dossier-2 corner states halt in
6 to 12 steps. Status: the odd-c formula is a finite-plus-induction
statement and is the cheapest promotion to a theorem available in
the whole program; the even-c behaviour is unresolved and slightly
embarrassing for the "abstract death = lethality" narrative, since
it shows abstract death is loss of certification, not death.

**The raw-cone incompatibility margins.** No record configuration of
Antihydra is within 30 raw steps of the halt (42,295 depth-30
families checked, 7 needing exact enumeration over a, m, c < 40);
dossier-3's analogue at depth 24 (134 families, all demanding three
0s in a six-cell window no holeTape can satisfy). Status:
machine-checked arithmetic in python, explicitly not Lean; finite
case analyses that the existing generators could emit as lemmas.

**The recurring closure pattern.** Two parametric boundary families
plus a derived floor law plus a derived kind law, observed in four
independent machines (rank-1, dossier-9, the dip-aware pair;
`docs/results/2026-08-31-candidate-parametrics.md`,
`2026-08-31-campaign-consolidation.md`). Status: a pattern with four
instances and no statement of the class it is a theorem about.

A general caution applies to all of section 2: the empirical laws
underlying the gait-grain closures are exact on their observed
transitions (2,746 for Dvisetu at 2x10^7 steps, 5,251 for dossier-7,
3,879 for dossier-8) and are extrapolation beyond them. The raw-step
engines close that gap for d7-d18 by simulating unobserved branches,
but for the gait-grain five the unobserved branches are covered by
proof only where an episode theorem quantifies over them, and by
assumption where folded (Dvisetu's divide, five harvested events to
n = 18,648, recursion depths d = 0, 1, 2 only).

---

## 3. Coverage gaps, ranked by leverage

### 3.0 The ledger, recomputed

All counts recomputed from `experiments/outputs/d4_fullsweep.jsonl`
(1,094 rows) and `experiments/outputs/sweep251_results.jsonl`
(237 rows) for this document.

| band | count | definition (census fields) |
|---|---|---|
| closed | 18 | kernel-checked conditional closures |
| open single-law | 289 | `laws == 1`, not closed (307 total single-law; all 18 closed machines are in this band) |
| open multi-law | 39 | `laws >= 2` (36 with 2 laws, 1 with 3, 2 with 6) |
| unstructured | 748 | `nreg == 0`, equivalently `laws == 0` |
| total open | 1,076 | |

Coverage is 18 of 1,094, or 1.6 percent. Every closed machine sits
in the single-law band: the program has never closed a machine the
regime census called multi-law or unstructured. Note the widely
quoted "733 unstructured" undercounts; the census file says 748.

Within the open single-law band, the 10x finder sweep
(`sweep251_results.jsonl`, 237 machines attempted, all single-law)
produced 63 EXACT orbit specs. Seven of the 63 are closed machines
blindly re-discovered. Of the remaining 56: 13 were probed by the
decider pilot with re-derived compact specs (0 invariants), and 43
carry degenerate memorization specs, rules approximately equal to
transitions at support 1 to 2 (`2026-09-02-decider-pilot.md`; the
campaign ledger's "56 degenerate" conflates these two subsets and
should not be quoted). Horizon warning attached to the whole band:
4 of 262 machines lost their single-law status between 120k and 250k
steps, so band membership is a budgeted claim.

### 3.1 Gap 1: the open single-law band (289 machines), highest leverage

The dossier-9 lesson (`Dossier9RawTM.lean` header,
`closures-deep-dive.tex` grain-ladder section) is that the raw-step
engine needs no law tables: its inputs are a corridor lemma, a
record-event definition, and a fuel budget; the tranche then closed
nine machines in one campaign, including machines (the two-sided
five, the arch-variants) whose laws were never extracted. Nothing in
principle restricts the engine to the exact-spec cohort. What
actually blocks pointing it at the 289, enumerated concretely:

1. **Per-machine halt anatomy.** Deriving the corridor is mechanical
   backward analysis of a 12-entry table, and every tranche machine
   was a halt-is-the-probe case (one-cell predicate; d16 needed two
   doors). But the probe predicate must satisfy two conditions:
   halting implies it fires, and it empirically never fires. A sound
   corridor predicate that fires benignly mid-run makes the
   conjecture false without the machine halting, wasting the
   closure. This needs a probe-safety audit (mirror run, every raw
   step) before any Lean is written, exactly as the tranche did at
   2x10^7 steps per machine.
2. **Record-event and sidedness audit.** The engine's word state is
   one growing side plus a bounded far side (dossier-9's left extent
   bounded at -10) or the blank-default far-end surgery proven to
   absorb the two-sided five. The census records `nreg` and `stride`
   but not sidedness; a per-machine growth-direction and far-side
   boundedness probe (the `d78_laws.py` pattern) is a missing
   instrument and is cheap.
3. **Fuel bounds.** The uniform budget is quadratic in word length
   (`wfuel = 64(len+64)^2`), and the tranche's measured margins were
   1,900x to 7,877x. A machine with superquadratic sweeps would
   exhaust fuel; the fix is a larger polynomial (fail-closed either
   way), but the audit must happen per machine, since fuel
   exhaustion falsifies the conjecture silently.
4. **Mirror and differential-test templating.** Each closed machine
   has a hand-built python mirror and test file
   (`tests/bb6/test_d*_theorems.py`). At 289 machines this is the
   throughput ceiling.
5. **Lean generation.** The tranche files are near-clones
   (d15 is d14 with the table swapped, about 1,000 to 1,100 lines
   each), yet `busy-beaver-core/generators/` contains only the
   dossier-2/3 gait-grain generators. No raw-step-engine generator
   exists. This is the single most valuable tool the program has not
   built.

Effort estimate: generator plus audit harness, one to two weeks;
after that the cadence the tranche demonstrated (nine machines in
roughly two days, mirrors pre-validated) suggests the band is
throughput-limited, not idea-limited. The honest unknown is the
audit pass rate: machines failing sidedness or probe-benignity fall
out, and no measurement of that rate exists yet. Running audits
first (gap 2) converts this unknown into a number before the tooling
bet is placed. Priority targets inside the band: the 13
probed compact-spec machines, then the 43 degenerate-fit EXACTs
(degenerate specs are an extraction failure, not evidence of
unsuitability for an engine that ignores specs), then the remainder
by audit verdict.

### 3.2 Gap 2: the audit instrument itself

A sidedness / probe-benignity / fuel-growth audit over all 1,076
open machines at 2x10^7 steps each is two to three days of
implementation plus compute, reuses existing mirror machinery, and
produces the real denominator for gap 1. It also directly probes the
748 unstructured machines, because the raw-step engine does not
require regime structure. Highest information per unit effort of
anything on this list.

### 3.3 Gap 3: the multi-law band (39 machines)

Dossier-12's mirror spans a 13M-step regime shift
(`closures-deep-dive.tex`, tranche entry), so the engine tolerates
regime changes. The marginal blocker is validation horizon: a
machine whose law switches at 10^7-step scale needs mirrors run
well past the switch. Effort: same pipeline as gap 1, longer runs.
Small band, moderate value, mostly worth doing as a byproduct.

### 3.4 Gap 4: the unstructured 748, the true dark matter

Two distinct readings of `nreg == 0`, and the program has not
separated them: (a) the machine genuinely lacks affine regime
structure at any horizon; (b) the instrument failed at 120,000 steps
with frontier-expansion events and constant-second-difference laws
as the only vocabulary. The precedent is bad for reading (a): the
census's "only four fixed-dimension machines" claim fell to a 10x
budget increase (`2026-08-31-new-fixed-dimension-machines.md`), and
the 1M-step shape gates misclassified dossiers 7 and 8. What the
cohort needs is a second-generation census: longer horizons (10^7
steps), both-sided and interior event definitions, non-affine law
families (quadratic event times, multiplicative gaps), and the
natural-alphabet search motivated by the wrong-alphabet lesson
(period-2 runs and unary ladders made machines look array-class when
they were bounded counters in the right alphabet;
`2026-08-31-campaign-consolidation.md`, finding 4). Effort: about a
week for the census, unknown for what it finds. Separately, gap 2's
audit may show some of the 748 are closable without any structure
being found, which would be coverage without understanding; see
section 5.2 for why that trade should be made consciously.

### 3.5 Gap 5: promotions from empirical to theorem

Cheap, finite, and currently python-only: the Fibonacci recurrence
for dossier-3's cone (combinatorial lemma), the depth-24/depth-30
raw-cone incompatibility lemmas (finite case analyses the generators
can emit), and Antihydra's odd-c lethality formula (induction). Days
each. These do not expand coverage but harden the sharpness story
the closures lean on, and they are the items an external referee can
check without trusting any horizon.

---

## 4. The mathematical frontier

**The invariant-measure program.** The only identified route past
the Collatz wall for any of the eighteen conjectures. The target is
a Tao-style almost-all-seeds theorem for the dossier-2/3 renewal map
R: explicit, total, piecewise affine, with a verified closed form,
verified uniform hazard at the diagonal, a mod-3 conservation law,
and a fatal set that is a finite union of lines
(`2026-08-26-renewal-map-analysis.md`). That is materially more
structure than Collatz offers, and the finite-horizon half of the
argument is already mechanical. Two sober caveats: an almost-all
theorem does not decide the seed (6, 13), and the orbit's measured
minimum margin above the fatal window is 4 over 10^5 renewals, so
any pointwise statement must control arbitrarily close approaches.
The exclusion-recursion analysis shows offset-coordinate
certificates deepen without closing, which is why measure, not
certificates, is the route. Effort: months, genuinely mathematical,
publishable independently of BB(6).

**The branching-constant theorem.** The series {phi, 2-adic, 1} is
three exact computations, each traceable to an alternation
constraint of the episode calculus. A theorem of the form "the
abstract cone's growth is determined by the episode-alternation
graph" would upgrade lambda_back from a ranking heuristic (measured
for all 1,094 at depth 16 to 18, unimodal at 1.3 to 1.4, certified
machines in the low tail; `2026-08-27-dossier4-sweep.md`) into a
meaningful invariant, and would be the first cross-machine theorem
of the program. Start with the Fibonacci case, which is finite.

**Cross-machine structure worth chasing.** The recurring closure
anatomy (two parametric boundary families, floor law, kind law) now
has four instances; if it is a theorem about some class of one-sided
record machines, extraction for the whole single-law band collapses
to fitting two families. The alphabet-artifact lesson points the
same direction: "array-class" was repeatedly a symptom of reading
the tape in the wrong alphabet, so an automated natural-alphabet
search (period detection over run-length encodings) is the concrete
instrument this conjecture suggests. The phi seat-change (cone for
dossier-3, hazard for Antihydra) hints that one generating mechanism
underlies both, but no statement exists; it is currently numerology
with a mechanism sketch on each end.

---

## 5. Fragilities and honest risks

**5.1 Everything decisive is conditional.** Zero of 1,094 machines
are decided. The eighteen theorems are reductions; each conjecture
is exactly the hard part, and section 1.2's negatives are evidence
the hard part is genuinely hard, not evidence it will yield. The
first external challenge will be "you proved the direction that was
never in doubt," and the honest response is the sharpness results
plus the negative results, both of which have finite horizons.

**5.2 Raw-step-grain closures have thin conjectural content.** For
dossiers 7 through 18 the abstract orbit is a fail-closed simulator
on a one-sided word encoding, and `Safe` says that simulator never
returns `none`. The genuine content over "the machine never halts"
is: halt localization, the one-sided compression with a blank far
side, and the fuel bound. But `Safe` is strictly stronger than
non-halting (fuel exhaustion or an unanticipated far-side excursion
falsifies it without a halt), and the conjecture is about an orbit
the file computes but does not explain (`closures-deep-dive.tex`
concedes this). A reviewer will ask what separates such a closure
from a verified simulator plus an assumption, and the answer is:
less than for the gait-grain closures. Scaling gap 1 multiplies
exactly this thinnest kind of closure; the program should decide
explicitly that coverage at this grain is worth having, and say so
in its papers rather than letting the eighteen read as uniform in
depth.

**5.3 DivideFaithful is a different kind of assumption.** The other
seventeen conjectures are statements about integer or word orbits;
Dvisetu's includes an assumption about the machine's own tape
behaviour, resting on five harvested divide events to n = 18,648
(recursion depths 0, 1, 2). It is the single folded assumption in
the program and the first closure a referee should attack. The known
fix, re-closing Dvisetu at raw-step grain, would eliminate it and
should be treated as debt, not as an option.

**5.4 The thinnest empirical horizons, named.** Dvisetu's mod-9
sub-rule: two events. Dossier-7/8 startup rules: one observation
each. Dossier-8's g >= 2 grand renewal: never observed, first
occurrence projected near 3x10^12 steps (covered by simulation in
Lean, uncovered by any measurement). Antihydra's even-c dying
states: unresolved beyond 2x10^7 raw steps, an open gap between
abstract death and raw halting. Almost-all-seeds: exact only to
X = 256. Fibonacci cone law: depth 12. Antihydra cone linearity:
depth 400. Danger-band lethality for dossier-7/8 inside excursions:
explicitly not settled (`2026-08-31-dossier7-dossier8-laws.md`, halt
anatomy section).

**5.5 The instruments have a record of being wrong at budget.** The
census claim "the certified four are the only fixed-dimension
machines" was falsified by a 10x sweep within four days. The 1M-step
shape gates misclassified dossiers 7 and 8 in both directions.
Single-law status is horizon-dependent for at least 4 machines. Two
PASS verdicts were refuted outright (commit 3714080). The
survivorship-bias incident (fatal offsets invisible because logging
happened after the death check,
`2026-08-26-almost-all-seeds.md`) was caught internally but shows
the pipeline can manufacture exactly the artifact that would fake a
breakthrough. Every classification in section 3 should be read with
these precedents attached.

**5.6 External verification has not happened.** Palomar entries are
pinned and locally checker-green (19 entries at commit f8c07a3) but
registration awaits the author's browser session; the forum post is
drafted, not posted; no non-author has run the build. Until one
does, "kernel-checked" means "kernel-checked on the author's
machine." Relatedly, the trusted base includes the transcription of
each machine table into Lean; the python mirrors check their parsed
tables against the Lean `instr` tables entry by entry
(`2026-08-31-antihydra-parity.md`, section 0), but that check runs
in the untrusted layer. A transcription error would yield a correct
theorem about the wrong machine, and only external reproduction
against the community's machine list closes that loop. The
provenance of `BB6_holdouts_1094.txt` as the community's current
holdout set should be re-pinned in the same step, since every
denominator in this document depends on it.

**5.7 Internal bookkeeping inconsistencies.** The campaign ledger
says 56 of 63 EXACT specs are degenerate; the decider pilot says 43
degenerate plus 20 probed. The consolidation quotes 307 single-law
machines where the pilot's population definition yields 262; both
are right under their own filters (`laws == 1` versus
`laws == 1 and nreg >= 3`), but the documents cite the numbers
interchangeably. The commonly quoted 733 for the unstructured cohort
is 748 in the data file. None of these change any conclusion; all of
them are the kind of thing a hostile reviewer finds first.

---

## Summary of the next order of work

1. Build the audit harness (sidedness, probe benignity, fuel growth)
   and run it over all 1,076 open machines. Two to three days plus
   compute. Output: the true closable denominator.
2. Build the raw-step-engine generator (Lean file plus mirror plus
   differential tests from a machine table and audit verdict). One
   to two weeks. Then batch-close the open single-law band, starting
   with the 13 probed compact-spec machines and the 43
   degenerate-fit EXACTs.
3. Re-census the 748 unstructured with longer horizons, richer event
   and law vocabularies, and the natural-alphabet search. About a
   week.
4. Promote the finite empirical facts to Lean (Fibonacci recurrence,
   cone-incompatibility lemmas, odd-c lethality; re-close Dvisetu at
   raw-step grain to retire DivideFaithful). Days each.
5. Open the invariant-measure program on the dossier-2/3 renewal
   map. Months; the only route to any unconditional conjecture, and
   independently publishable.

And in parallel, at near-zero cost: the Palomar browser session, the
forum post, and one external `lake build`.
