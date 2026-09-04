# Forward plan: addressing the state-and-gaps review

Derived from `2026-09-03-state-and-gaps.md`. Organized so that the
cheap, denominator-setting, and de-risking work comes before the
expensive tooling bets. Each item lists effort, what it unblocks, and
its dependency. Effort is calendar-scale for one focused worker plus
agents; "session" means an evening.

## Phase 0: pin the ground (prerequisite, ~1 day)

**0.1 One band definition.** The review found the census bands drift
with the threshold (262 vs 289 single-law). Fix one definition
(`laws == 1 and nreg >= 3`, computed from `d4_fullsweep.jsonl`),
write it into a single `qgkit/bb6/census_bands.py` that every later
doc and harness imports, and recompute every band count once.
Unblocks: honest denominators for everything below.

**0.2 External verification, the near-zero-cost items.** These need
the author's browser, not engineering: the Palomar session (19
entries pinned at `f8c07a3`, intake proven 0/0), the bbchallenge
forum post (drafted), and asking one non-author to run `lake build`.
Effort: under an hour of the author's time. Unblocks: fragility 4
(the only fragility that no amount of our own work can close).

## Phase 1: find the true closable denominator (2-3 days)

**1.1 The audit harness** (review gap 1). A script over all 1,076
open machines that, per machine, decides three yes/no questions the
raw-step engine actually depends on, without closing anything:
- *sidedness*: does the tape grow one side, both, or neither, and
  which extreme has the fewest arrival states (the record side);
- *probe benignity*: is the undefined transition a halt-is-probe
  case (one-cell safety) or does it need a neighbour guard;
- *fuel growth*: measure max record-gap vs word length over 20M
  steps; is it sub-quadratic (standard fuel suffices)?

Output: a table classifying every open machine as engine-ready,
engine-ready-with-work (which work), or out-of-scope (needs a new
record notion). This is the number that tells us whether the next
bet closes 40 machines or 400. Fail-closed: a machine that halts in
the 20M audit is reported, not hidden.

## Phase 2: the batch-closer (1-2 weeks, then fast)

**2.1 The raw-step Lean generator** (review gap 2). The
`generators/` directory only has gait-grain d2/d3 tooling; the nine
tranche closures were hand-built per machine by agents. Generalize
that into a generator that takes a machine table plus the audit's
sidedness/probe/fuel verdict and emits: the `DossierNRawTM.lean`
closure, the python mirror, the differential test, and the Palomar
challenge/solution/comparator quadruple. The tranche proved the
template is uniform (~1,010-1,067 lines, first-try green); the
generator makes it push-button.

**2.2 Batch close the engine-ready band.** Run the generator over
every machine the audit marks engine-ready, starting with the 13
probed compact-spec EXACTs and the 43 degenerate-fit EXACTs (already
known to have exact orbit structure), then the rest of the
single-law band. Demonstrated cadence: ~9 machines / 2 days. Each
batch: generate, `lake build`, verify axioms, add to Palomar,
re-run `check_palomar.py`. Unblocks: coverage from 1.6% toward
whatever the audit's denominator allows.

## Phase 3: de-risk the closures we already have (days each)

**3.1 Retire DivideFaithful** (fragility 2). Re-close Dvisetu at
raw-step grain with the generator from 2.1; that eliminates the
program's only folded assumption and makes all closures
assumption-free.

**3.2 Strengthen the thinnest conjectures** (fragility 1). The
raw-step-grain `Safe` is "the simulator never dies," stronger than
non-halting only via fuel. Add, per raw-step closure, a short lemma
that the fuel bound is never the reason for a `none` (i.e. `none`
implies the halt pattern, not exhaustion), closing the gap between
`Safe` and true non-halting. The audit's fuel data (1.1) supplies
the bound; this is mechanical once stated.

## Phase 4: cheap theorem promotions (days each, parallelizable)

Move empirical findings to theorems (review gap 4, section 2):
- **4.1** the Fibonacci recurrence `L(k)=L(k-1)+L(k-2)` for
  dossier-3's cone (combinatorial lemma on branch words with no
  consecutive terminate);
- **4.2** the depth-24/30 raw-cone incompatibility lemmas (finite
  case analysis; the generators can emit them);
- **4.3** the odd-c lethality formula `(3c^2+44c+125)/4` for
  Antihydra as a certified lemma, and the even-c gap characterized
  (the open piece between abstract death and raw halting);
- **4.4** the closure pattern (two parametric families + floor + kind
  law) stated as a class proposition once a fifth instance confirms
  it.

## Phase 5: the mathematical frontier (months)

**5.1 The invariant-measure program on R** (review gap 5, the only
route to any unconditional result). The renewal map is explicit,
total, piecewise affine, with verified uniform hazard; the obstacle
is that margin-4 grazing means a pointwise-avoidance proof must
control arbitrarily close approaches to the diagonal. Entry points:
the Fibonacci case of the branching-constant theorem (4.1) as a
warm-up, then a martingale/invariant-measure argument for the tail
hazard in the style of Tao's Collatz result. Independently
publishable; the natural home for outside collaborators.

**5.2 Second-generation census** (review gap 3) of the unstructured
cohort (~750-790 machines): longer horizons, non-affine law fitting,
both-sided record events, and the automated natural-alphabet search
motivated by the alphabet-artifact lesson (several "array-class"
machines were fixed-dimension in the right alphabet). This is where
the dark matter either yields structure or is shown genuinely
horizonless.

## Sequencing

```
0.1 band pin ─┬─> 1.1 audit ──> 2.1 generator ──> 2.2 batch close
0.2 external ─┘                        │
                              3.1 retire DivideFaithful
                              3.2 fuel lemmas
4.x theorem promotions  (parallel, independent)
5.x frontier            (parallel, long-horizon)
```

Phase 0 and 1 are the whole near-term decision: they cost under a
week and tell us whether coverage can grow by an order of magnitude
or is capped near the current band. Everything expensive (the
generator, the frontier) is gated on that answer. The external items
(0.2) should go out immediately and in parallel; they are the only
work that converts what already exists rather than building more.

## What "done" would mean, honestly

Best realistic case: coverage grows from 18 to the engine-ready
denominator (phase 2), every closure is assumption-free (phase 3),
several findings become theorems (phase 4), and one conjecture
(Antihydra or dossier-2/3) gets a genuine unconditional attack under
way (phase 5). The wall does not move: the conjectures stay
conjectures, and the honest headline remains "0 machines decided
unconditionally, N reduced to explicit arithmetic." The plan
maximizes N and the rigor of the reductions; it does not pretend to
cross the Collatz wall, because the program's own negatives show
that finite certificates cannot.
