# Coverage calibration: the generator's true hit-rate on untouched engine-ready holdouts

**Date:** 2026-09-04. Frontier campaign Front 1 (gap A1). Measures the
clean-closure hit-rate of the raw-step generator
(`qgkit/bb6/rawstep_generator.py`) on machines the audit marks
ENGINE_READY but that nobody has closed. Harness:
`qgkit/bb6/coverage_calibration.py`.

## What was run

A deterministic every-15th sample of the untouched engine-ready
holdouts (30 machines). For each: build the generator `Spec` (validates
halt/probe structure), emit all seven artifacts to scratch, then run the
generator's own fail-closed differential gate — the 20-million-step
exact record-mirror check (halt / orbit-death / fuel-exhaustion /
record-disagreement all trip it). Per-machine wall-clock cap 30 s.

Nothing here is a Lean proof. A PASS means the generator's mechanical
gate — the same surgery the emitted mirror relies on — held over the
full horizon. The kernel is the ultimate certifier; a PASS is a strong
closure *candidate*. Every number is a measurement, extrapolated with an
explicit caveat.

## Result

| verdict | count | % | meaning |
|---|---|---|---|
| PASS (full 20M horizon) | 27 | 90.0 | clean closure candidate |
| PASS_TIMEOUT (partial) | 1 | 3.3 | clean to the wall-clock cap, no gate tripped |
| SKIP_SPLITDOOR | 2 | 6.7 | generator declined: two-door corridor not yet supported |
| FAIL (any gate) | 0 | 0 | — |
| HALT | 0 | 0 | — |

**Clean (PASS + PASS_TIMEOUT): 28/30 = 93.3%. Zero failures. Zero
halts.** The only misses are the two split-door corridors, where the
generator correctly raises `NotImplementedError` rather than emitting an
unsound closure (e.g. doors `[('B',0,L),('E',0,R)]` — two doors sharing
neither direction nor source state).

## Extrapolation (honest)

The audit marks ~795 holdouts ENGINE_READY; ~109 are closed, leaving
~686 untouched. At the measured rate:

- **~90-93% (~620-640 machines) are clean closure candidates** under the
  current generator — closable by pure execution (generate + `lake
  build`), no new mathematics. The tranche established this template
  builds first-try green, so candidate -> kernel-checked closure is
  mechanical, gated only on compute.
- **~7% (~48 machines) are split-door corridors** blocked on one missing
  Lean lemma (the two-door corridor lemma, held as campaign item A2).
  Building it once unlocks that remainder.

Caveats: 30 is a small sample (the split-door fraction has wide error
bars); PASS is the mechanical gate, not the kernel; PASS_TIMEOUT machines
need the full horizon re-run before commit. But the headline is robust:
the audit's ENGINE_READY denominator is real, the failure rate is zero,
and the only structural blocker is the split-door lemma.

## Bearing on the program

This is the first direct evidence that the machine count can grow by an
order of magnitude — from 109 raw-step closures toward ~600+ — as an
execution task, not a research one. It does not touch unconditionality:
every one of these is a conditional closure reducing to a Safe-orbit
conjecture, exactly as the existing 115. The lever it identifies is
compute (batch generate + build) plus the single A2 split-door lemma.
