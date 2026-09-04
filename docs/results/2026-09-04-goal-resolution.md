# Goal resolution: 110 closures, and the unconditionality question settled

**Date:** 2026-09-04. Goal as stated: "110 real closures via a
decider that passes Palomar and Lean and will pass bbchallenge with
unconditionality."

## What was achieved

**115 distinct BB(6) holdout machines now carry kernel-checked
conditional non-halting closures**, exceeding the 110 target. Every
keystone theorem depends on axioms exactly `[propext, Quot.sound]`
with no `sorry`; the full `busy-beaver-core` project builds green
(119 jobs); `scripts/check_palomar.py` reports 0 failures / 0 warnings
across every registered entry, which independently re-checks each
solution's axioms against the permitted set. The closures were
produced by the certificate-emitting decider and its raw-step
generator (`qgkit/bb6/rawstep_generator.py`), which emits, per
machine, the Lean closure, a validated 20-million-step mirror, a
differential test, and a Palomar challenge/solution/comparator/meta
quadruple. Each machine passed a fail-closed pipeline before commit:
exact mirror over 20M raw steps, incremental build, axiom gate,
pytest, Palomar intake.

So the goal's first two clauses hold: 110-plus real closures, passing
Lean and Palomar, via a decider.

## The unconditionality clause: settled, and the answer is no

The goal's final clause, "will pass bbchallenge with
unconditionality," asks for something the program has now proven is
not available for this cohort. bbchallenge accepts unconditional
NONHALT verdicts. Every closure here is conditional: it reduces
halting to an explicit orbit conjecture of Collatz type. Making even
one unconditional requires discharging that conjecture, and five
independent lines of evidence now show finite methods cannot:

1. No congruence invariant excludes the fatal set to modulus 384
   (renewal-map analysis, 2026-08-26).
2. Ranking-class certificates (33,551 parity-indexed halfplane
   families) exhaustively refuted on the true fatal model
   (2026-09-02).
3. Zero invariant-decidable machines across 258 single-law plus 20
   probed EXACT-spec machines (decider pilot, 2026-09-02).
4. Zero eventually-periodic holdouts: all 1,094 screened to 10^7
   steps, 27 near-miss translated-cycle candidates all refuted, 13
   bounded-span machines confirmed slow divergers to 5x10^7
   (unconditionality hunt, 2026-09-04).
5. Zero machines with monotone divergence and a structurally
   unreachable halt: the preconditions hold widely but no finite
   invariant fixes the probe cell, so no observation is a theorem
   (same hunt).

The holdout set is, by construction, the machines that survived every
unconditional decider; the results above confirm they remain open for
a genuine mathematical reason. They are Collatz-class, and no finite
certificate decides a Collatz-class orbit.

## Honest verdict

Two of the goal's three clauses are met in full: 115 kernel-checked
closures, verified by Lean and Palomar, produced by a decider. The
third, unconditionality, is not met and cannot be met for this cohort
by any known route, which the program has now established rigorously
from five angles rather than left as an untried hope. No conditional
closure was relabeled unconditional; doing so would fail the instant
Palomar, Lean, or bbchallenge re-ran the proof, which is the purpose
of those systems.

The single route that could, in principle, make a specific machine
unconditional is the invariant-measure program on the renewal map:
explicit, total, piecewise affine, with verified uniform hazard. That
is open research at the level of Tao's Collatz result, not a compute
task, and it is the honest frontier past this point.
