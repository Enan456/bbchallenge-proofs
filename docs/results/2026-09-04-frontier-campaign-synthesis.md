# Frontier campaign: six-front synthesis

**Date:** 2026-09-04. Consolidates the six parallel fronts of the
frontier campaign (`2026-09-04-frontier-campaign-plan.md`). Each front
was run by an independent agent, its load-bearing numbers re-verified by
the parent, and pushed separately. This is the joined picture.

## Results by front

| # | front | headline | verified | bears on |
|---|---|---|---|---|
| 1 | coverage calibration | 47/49 = **95.9% clean**, 0 halts, 0 fails; extrap **~658 clean closure candidates** of ~686 untouched engine-ready | parent's own 30-machine run: 27 PASS, 0 halts | the COUNT |
| 2 | conjecture reduction | 115 conjectures collapse to **<=89 independent roots** (upper bound); families D69-80 (12), D82-93 (11); 5 branching constants track renewal arity | script reproduces 89 deterministically | the SHAPE |
| 3 | transfer operator | spectral gap 0.21 (induced) / 0.44 (per-renewal); clean BV invariant density factorizing as density x Haar; almost-all reduces to **one named Lasota-Yorke lemma** | residue uniformity 0.0014, drift 0.134, density monotone | the THEOREM |
| 4 | dark-matter alphabet | **~27% (floor ~218/793) secretly fixed-dim** via an untested head-sweep stride at k=1; ~575 genuine dark matter; 0 halts | parent 15-machine subset: 2 fixed-dim incl. stride-4, 0 halts | the DARK MATTER |
| 5 | p-adic obstruction | **NEGATIVE** -- no non-Archimedean invariant excludes the fatal set (tested 2^12, 3^7, 7776); strengthens the mod-384 impossibility | 654 deep-fuse gaps all odd, fatal set nonempty | the WALL |
| 6 | Antihydra even-c | odd-c halt formula (3c^2+44c+125)/4 **derived in closed form**; does NOT extend -- even c is resurrection, its fate an instance of SafeOrbitA | script self-checks pass, formula integral | the MAP |

## What the campaign changes

**The count is ~10x larger than realized, and it is execution, not
research.** Front 1 shows ~658 of the untouched engine-ready holdouts
are clean closure candidates under the existing generator (0 halts, 0
fails in the sample), plus Front 4 adds a floor of ~218 dark-matter
machines that are secretly fixed-dimensional once the right head-sweep
stride is used. Realizing them is a compute task (batch generate +
`lake build`) plus one Lean lemma (A2 split-door corridor), not new
mathematics. Every one stays conditional — unconditionality untouched.

**The cohort is far less diverse than 115.** Front 2 caps the
independent problems at 89 and the true number is lower (syntactic
clustering cannot see proven abstract reductions like d2/d3). Two
families alone account for 23 machines as one map with a movable fatal
probe, and only five distinct branching constants exist across the whole
corpus. The program is solving fewer root conjectures than the machine
count suggests.

**The one reachable theorem is now precisely scoped.** Front 3 reduces
the almost-all-seeds theorem to a single standard-shaped lemma: a
Lasota-Yorke bounded-distortion + summable-return-tail estimate for the
induced F-return operator. The parabolic generator T is the
Pomeau-Manneville intermittency obstruction, cured by inducing on the F
section (numerically: mean return 3.82, fast tail). Given that lemma the
rest is off-the-shelf (ITM -> mixing, Nagaev-Guivarc'h -> CLT,
Borel-Cantelli -> almost-all). This is the natural home for outside
collaboration.

**The wall is confirmed from one more independent angle.** Front 5's
clean p-adic negative joins the five prior finite-method impossibilities,
the invariant-measure genericity, the closed horoball route, and the
effective-equidistribution "door bolted" verdict. No non-Archimedean
invariant exists. The specific-orbit unconditional result stays
Collatz-hard.

**Antihydra's even-c mystery is resolved at the map level.** Front 6
derives the odd-c lethality quadratic exactly and shows even c is a
separate resurrection regime whose fate reduces to SafeOrbitA itself —
characterizing the abstract map without touching the conjecture.

## The strategic picture

The campaign cleanly separates three lanes:

1. **Execution (grow the count):** batch-realize the ~658 candidates;
   build the A2 split-door lemma to unlock the ~48 SKIPs; run a
   stride-aware re-census to convert the ~218 dark-matter leads. All
   conditional, all mechanical.
2. **The theorem (the reachable prize):** prove Front 3's one Lasota-Yorke
   lemma -> the almost-all-seeds theorem. Real, publishable analysis.
3. **The wall (settled):** unconditional non-halting of a specific
   machine is Collatz-hard and now blocked from finite, p-adic,
   geometric, and effective-analytic directions. Not a to-do; a proven
   boundary.

Nothing in the campaign fabricated a result or relabeled a conditional
closure as unconditional. Two negatives (Fronts 5, and the effective
route) are reported as cleanly as the positives.
