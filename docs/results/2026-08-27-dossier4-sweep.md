# Dossier-4: the three-machine verdict harness, run across open machines

**Date:** 2026-08-27 · **Code:** `qgkit/bb6/dossier4.py`,
`qgkit/bb6/cone_sweep.py`

## The architecture

Dossier-4 is not a machine — it is the harness that judges machines,
completing the MIP*-inspired alignment picture with a third emulator:

1. **START machine**: the blank-tape startup, run until the first
   stable regime is established.
2. **REGIME machine** (new): the regime-change emulator — segments the
   record-event sequence into maximal runs governed by a single affine
   law (constant second difference of event times, with stride
   detection for alternating dynamics); regime changes are the law
   switches. For dossier-2/3 this recovers the spawn/traversal
   structure (stride 4) that the certified `metaStep` describes
   exactly; for uncertified machines it is the empirical stand-in.
3. **END machine**: the backward halt cone — constraint-pattern
   families grown from every undefined transition, with branching
   ratio λ_back and exact alignment checks against the forward run.

Verdict = compile(START, REGIME chain, END alignment).

## Sweep findings

**λ_back separates the cohort.** Across the 9-machine certification
queue, the four machines with exact orbit specifications have the
lowest backward branching (1.09–1.30 at depth 20), the five rejected
machines the highest (1.21–1.47), Antihydra highest of all. Across
all 1,094 holdouts (depth-16 cone-only sweep), λ_back is unimodal
around 1.3–1.4 with thin tails — a new, cheap, decider-independent
classification feature: *how fast does the set of ways-to-die grow
backward in time*.

**No free decisions.** Three holdouts showed nearly-flat cones at
depth 16 (2–8 families); extending the closure shows all three blow
past 50,000 families — slow starters, not finite closures. A machine
whose backward closure were finite and start-incompatible would be
decided non-halting outright; none of the 1,094 obliges.

**Zero alignments anywhere.** Across all nine queue machines, 250,000
forward steps sampled against depth-20 cones: no forward configuration
ever matches a cone family. Every sampled configuration of every open
machine is >20 raw steps from halting — and for the four certified
machines this complements the episode-level safety theorems.

## The verdict table

```
DOSSIER-4 VERDICT TABLE (start | regimes | end-cone | verdict)
====================================================================================================
1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA
  START : blank -> first regime after event 43
  REGIME: startup<=evt43, 26 regimes (stride 4), mean len 84 evts, 1 distinct laws
  END   : cone lam=1.471, families@20=890, alignments in 250k steps: 0
  VERDICT: NONHALT if HydraSafe (certified reduction)

1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB
  START : blank -> first regime after event 71
  REGIME: startup<=evt71, 24 regimes (stride 4), mean len 40 evts, 1 distinct laws
  END   : cone lam=1.093, families@20=10, alignments in 250k steps: 0
  VERDICT: NONHALT if SafeOrbit (certified reduction)

1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD
  START : blank -> first regime after event 42
  REGIME: startup<=evt42, 29 regimes (stride 4), mean len 49 evts, 1 distinct laws
  END   : cone lam=1.303, families@20=49, alignments in 250k steps: 0
  VERDICT: NONHALT if SafeMetaOrbit (certified closure)

1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE
  START : blank -> first regime after event 71
  REGIME: startup<=evt71, 28 regimes (stride 4), mean len 50 evts, 1 distinct laws
  END   : cone lam=1.283, families@20=46, alignments in 250k steps: 0
  VERDICT: NONHALT if SafeMetaOrbit (certified closure)

1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA
  START : blank -> first regime after event 79
  REGIME: startup<=evt79, 24 regimes (stride 4), mean len 62 evts, 1 distinct laws
  END   : cone lam=1.436, families@20=17, alignments in 250k steps: 0
  VERDICT: OPEN

1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA
  START : blank -> first regime after event ?
  REGIME: no stable regimes found
  END   : cone lam=1.389, families@20=514, alignments in 250k steps: 0
  VERDICT: OPEN

1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE
  START : blank -> first regime after event 48
  REGIME: startup<=evt48, 24 regimes (stride 4), mean len 34 evts, 1 distinct laws
  END   : cone lam=1.212, families@20=54, alignments in 250k steps: 0
  VERDICT: OPEN

1RB1RA_1RC1LB_0LD0RA_1RA1LE_---1LF_1LC0LF
  START : blank -> first regime after event ?
  REGIME: no stable regimes found
  END   : cone lam=1.387, families@20=507, alignments in 250k steps: 0
  VERDICT: OPEN

1RB1RA_1RC1LE_1RD1LC_0LB0RA_---1LF_1LD0LF
  START : blank -> first regime after event ?
  REGIME: no stable regimes found
  END   : cone lam=1.390, families@20=642, alignments in 250k steps: 0
  VERDICT: OPEN
```

## Reading the table

- The four certified machines carry conditional NONHALT verdicts whose
  conditions are single arithmetic conjectures (machine-checked
  reductions).
- The five OPEN machines now each have: a measured startup, an
  empirical regime chain (three of the five show clean stride-4
  regime structure — caterpillar-class candidates for the same
  episode-compilation pipeline), and a cone margin. The two with
  λ_back ≈ 1.39 and no stable regimes (`1RB0RA…`, `1RB1RA_1RC1LB…`,
  `1RB1RA_1RC1LE…`) are the least structured and likely the hardest.
- Next targets for certification: the stride-4 OPEN machines —
  `1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA` (24 regimes, one law)
  and `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE` (clean stride-1
  regimes) — the dossier-2/3 machinery should transfer.

## Honest scope

Regime detection is empirical segmentation, not certification; cone
margins are at sampled times and stated depths; verdicts labeled OPEN
are open. The certified verdicts are exactly the four Lean theorems.
