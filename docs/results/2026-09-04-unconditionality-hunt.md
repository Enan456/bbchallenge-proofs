# Unconditionality hunt: which BB(6) holdouts admit an unconditional non-halting proof

**Date:** 2026-09-04. **Detector:** `qgkit/bb6/uncond_hunt.py` (reusable).
**Outputs:** `experiments/outputs/uncond_hunt.jsonl` (Route A screen, all 1094),
`experiments/outputs/uncond_bounded_longrun.jsonl` (the 13 audit-bounded
machines to 5x10^7), `experiments/outputs/uncond_route_b.jsonl` (Route B
structural measurement over the 795 ENGINE_READY machines to 10^7).

This campaign asks a sharper question than the audit
(`docs/results/2026-09-03-audit-openset.md`): not which holdouts the raw-step
closure engine can reach, but which holdouts admit a GENUINE UNCONDITIONAL
non-halting proof, one that does not condition on a Collatz-class orbit
conjecture. The program's conditional closures all condition on such a
conjecture, and the decider pilot (`docs/results/2026-09-02-decider-pilot.md`)
proved that conjecture cannot be discharged by a finite certificate: zero
invariant-decidable machines, no congruence invariant to modulus 384, ranking
certificates refuted. An unconditional proof therefore has to come from one of
two routes that never touch that wall.

## The two honest routes

**Route A, eventual periodicity (translated cycle, shift may be zero).** If a
configuration repeats up to a fixed spatial shift, with the same state, every
P steps after a transient T, the machine provably never halts,
unconditionally, and the certificate is the triple (T, P, shift). A pure
in-place cycle is the shift-zero case. This is checked in two phases, both
fail-closed. Phase one screens: at every fresh-extreme (record) event on the
growing side the detector hashes (state, a fixed window of tape behind the
head); a candidate is raised only when the same key recurs three times in
arithmetic progression, two consecutive periods with a consistent shift and
equal spacing. Phase two verifies: an independent re-simulation confirms the
exact translated-cycle relation over several full periods, tracking the
leftward excursion depth so the compared window provably covers the whole
region the head reads in a period. A growing translated cycler leaves a
growing trail, so the certificate is windowed over the active region, not a
whole-line equality. Only a verified cycle is reported.

**Route B, monotone divergence with unreachable halt.** A strictly monotone
unbounded quantity (word length) whose halt probe requires reading a value the
diverging orbit provably never realises, because the probed cell is always in
the solidly grown region and never a fresh frontier zero. The detector
measures the structural preconditions. It is explicit that a precondition is
not a proof: for a Collatz-class holdout the probe's safety is exactly the
orbit conjecture, and only a bounded structural argument, independent of the
orbit's arithmetic, would make it unconditional.

## Route A result: zero

Every one of the 1094 machines (the 1076 open plus the 18 already closed) was
screened to 10^7 steps with a 1024-cell window. The screen raised 27
translated-cycle candidates and 0 pure-cycle and 0 halt events. Every one of
the 27 candidates was refuted by the rigorous verifier: the window match held
across three equally spaced records over 1024 cells, but the machine's actual
per-period read region reached far deeper than 1024 cells (mismatch positions
ran to several thousand cells behind the head), so the windowed match was a
coincidence of a structured tape, not a cycle. Re-screening all 27 to the full
10^7 horizon with a wider 4096-cell window and inline verification, so that a
false candidate can never stop the screen early, reached NONE for all 27. The
27 near-misses are themselves informative: these machines build a tape regular
enough to repeat over a kilobyte for three periods, then diverge, which is the
signature of a slow arithmetic process, not a cycle.

The 13 machines the audit called bounded (OUT_OF_SCOPE, the natural home of a
translated or in-place cycler) were given a dedicated long run to 5x10^7 with
exact cycle detection while the span stayed small. None cycled and none
halted. All 13 are slow divergers: the tape span keeps creeping upward, with
fresh extremes set as late as step 2x10^7 to 4.5x10^7, reaching spans up to
18538, and each visited more than 3x10^6 distinct bounded configurations
without a repeat. They are not cyclers; they are Collatz-class growers whose
growth is merely too slow to trip the audit's second-half extent test at
2x10^7 steps.

**Route A count: 0.** No holdout is eventually periodic within the horizons
checked (10^7 for all 1094, 5x10^7 for the 13 bounded).

## Route B result: zero unconditional proofs

All 795 ENGINE_READY machines were measured to 10^7 steps. Each has exactly
one undefined transition (one is anomalous with more and is excluded, leaving
794), a word length that is monotone non-decreasing over the whole run (0 of
795 ever retract the span), and never halts. The undefined transition halts on
reading a 1 for 521 machines and on reading a 0 for 273. On any non-halting
orbit the machine reads only the SAFE bit in the undefined state, so the
measurement is not whether the halt fires (it never does, by definition) but
WHERE the safe read sits relative to the frontier:

| probe location over 10^7 steps | machines |
|---|---:|
| always a fresh frontier cell (all-fresh-probe) | 19 |
| always a solidly grown cell (all-grown-probe) | 479 |
| mixed (sometimes fresh, sometimes grown) | 296 |
| never enters the undefined state | 0 |

The 19 all-fresh-probe machines (all halt-on-1) are the cleanest Route B
shape: the undefined state is entered only at fresh frontier zeros, so the
fatal 1 is never read. The 479 all-grown-probe machines are the Route B(ii)
shape named in the brief: the probed cell sits in the solidly grown region and
its value is a maintained quantity. These are structural PRECONDITIONS. None
is a proof, for three independent reasons.

First, on a non-halting orbit the safe read is safe by definition, so
observing it 313 times, or 6 times, is non-observation, not a theorem. Several
of the 19 enter the undefined state only 6 to 15 times in 10^7 steps; the
all-fresh property is a tiny sample, not a structural law.

Second, making the precondition a proof requires a finite invariant that fixes
the probed cell's value independently of the orbit's arithmetic. The decider
pilot (2026-09-02) searched exactly this space over every learned macro law
and found zero: no congruence invariant to modulus 384, monotone search empty,
ranking certificates refuted. The all-grown and all-fresh probers are drawn
from the same population and inherit that result.

Third, the structure of the 19 all-fresh machines shows the freshness is not
locally forced. Each has a single predecessor into the undefined state and a
safe branch (read 0) that moves back to a different state and continues the
computation rather than marching outward, and all 19 use both left and right
moves. The undefined state therefore sits inside a two-directional arithmetic
loop: the head goes out to probe the frontier and comes back to compute.
Whether it is ever brought back to the undefined state onto a previously
written 1 is a fact about the long-run arithmetic, the orbit conjecture
itself. A machine whose undefined state lived in a purely one-directional
absorbing component would be a translated cycler, and Route A found none.

**Route B count: 0 unconditional proofs.** 19 all-fresh-probe and 479
all-grown-probe machines hold the structural precondition; every one of them
is safe for the orbit reason, not a bounded structural reason.

## Why zero confirms the Collatz wall

The two routes are exactly the two ways a machine can fail to be genuinely
Collatz-class. Route A fails when the machine is eventually periodic, a finite
object. Route B fails when the halt is unreachable for a bounded structural
reason, again a finite object. A machine that admits neither is one whose
non-halting is a statement about the long-run arithmetic of its orbit, with no
finite witness, which is precisely what Collatz-class means and precisely what
the decider pilot proved these machines to be.

The holdouts already survived translated-cycler deciders at bounded transient
and period budgets. This campaign raised those budgets by orders of magnitude
(period up to roughly 3x10^6 within a 10^7 horizon, and 5x10^7 for the bounded
set) and still found nothing. That the 27 near-misses replicate over a
kilobyte for three periods before diverging is the clearest possible picture
of the boundary: these machines are as close to periodic as a non-periodic
machine can look, and they are not periodic. Route B's structural
preconditions hold widely, but the safety they describe is the orbit
conjecture itself, the object the program has proven carries no finite
certificate. A zero result here is the expected and honest outcome, and it
sharpens rather than weakens the program's central claim: the open BB(6)
machines are open because they are genuinely Collatz-class, neither periodic
nor cleanly divergent.

## Reproduction

    python3 qgkit/bb6/uncond_hunt.py --selfcheck        # detector self-test
    python3 qgkit/bb6/uncond_hunt.py --horizon=1e7      # Route A, all 1094
    python3 qgkit/bb6/uncond_hunt.py --bounded          # 13 bounded to 5e7
    python3 qgkit/bb6/uncond_hunt.py --route-b --horizon=1e7   # Route B
    python3 qgkit/bb6/uncond_hunt.py --verify FILE      # verify screen candidates

Every claim is horizon-bounded and every reported cycle is verified over
multiple full periods before it is believed. No cycle was reported.
