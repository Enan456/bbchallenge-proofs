# Dossier-4 against the full set, and the certification gate run to its boundary

**Date:** 2026-08-27 · **Data:** `experiments/outputs/d4_fullsweep.jsonl`
(1,094 rows) · **Code:** `qgkit/bb6/dossier4.py`, probes in session
scratchpad

## The full-set run

The complete three-machine harness (START / REGIME / END + verdict)
ran on all 1,094 BB(6) holdouts. Headlines:

- **0 halts, 0 alignments.** No machine halted within the horizons; no
  forward configuration of any machine ever matched its backward halt
  cone (depth 18, sampled at 120k steps). Every holdout is, at every
  sampled instant, ≥ 18 raw steps from halting.
- **346 / 1,094 machines have detectable regime structure**; 307 of
  those are governed by a single affine law — the structured third of
  the cohort.
- λ_back (backward cone branching) is unimodal at 1.3–1.4 across the
  cohort; the certified machines sit in the low tail.

## The certification cascade

Ranked by regime cleanliness (single law, many regimes, low λ_back):

| gate | pass |
|---|---|
| top-ranked candidates | 25 |
| fail-closed exact orbit spec (OrbitFinder, 150k steps) | **11** |
| bounded-hole shape family (holeTape-class) | **0** |
| bounded RLE dimension (block-vector class) | **0** |

The regime ranking works — 11/25 EXACT versus the old queue's 4/9.
But every one of the 11 fails both shape gates: hole counts grow
linearly, and even the run-length encoding of the tape grows in
*length* (dimension 20 → 80 across entries, gaining ~2 blocks per
regime). Their exact orbit specs are correspondingly fragmented
(403–854 rules at support 1–2): the affine law is real but lives on a
state space whose dimension itself grows.

## What this means

**The current certification technology is complete on its class.**
The pipeline certifies machines whose spawn-entry tapes form a
fixed-dimension family (Antihydra's block triple, dossier-1's shape,
dossier-2/3's five-integer holeTape). The dossier-4 sweep now shows
those four are — up to this ranking's reach — the *only* such machines
in the cohort: everything else structured is **array-class**, with
tape shapes that are unboundedly growing vectors of blocks.

The next frontier is therefore a shape language over *lists*:
`Realizes` predicates parameterized by a vector of run lengths of
growing dimension, episode theorems quantified over array shapes, and
an abstract orbit on sequences rather than tuples — the certified
counterpart of the v-Collatz vector representation already in
`qgkit/bb6/vcollatz` (whose reversible vector maps were built for
exactly this class). That is a genuine next project, not an evening's
compilation.

## Verdict compilation (final)

- 4 machines: NONHALT conditional, machine-checked (the certified
  reductions/closures).
- 1,090 machines: OPEN, each now annotated with startup, regime chain,
  λ_back, and cone margin — with 307 single-law machines as the
  structured frontier and 11 of the top 25 holding exact-but-
  fragmented orbit specs awaiting array-class certification.

## Honest scope

Ranking reach: gates were run on the top 25 by the stated criteria;
machines outside the shortlist were not probed for specs or shapes.
"Only such machines" is relative to this ranking and these budgets.
Probe horizons: 1M steps (shape), 150k (finder), 120k (alignment).
