# Dossier-6 opened: Dvisetu, the one-hole two-counter machine

**Date:** 2026-08-31 · **Machine:**
`1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB` (Dvisetu, this program's
own miner candidate of 2026-07-27, stages 655-744; re-surfaced blind
by the deep finder sweep as the smallest-spec machine in the pool
and gate-verified fixed-dimension on 2026-08-31)

## Identity and halt anatomy

Halt requires state `F` reading 0; `F` is entered only from `E`
reading 0, so the halt funnel is the `E0 -> F0` corridor. No halt
through 2x10^8 raw steps (July run) and none in any probe since.

## The certified-grade shape family

At 857 of 885 fresh-right-extreme records (2M steps; the ratio holds
at 20M), the tape is exactly

```
1^a 0 1^b        head at the right end, state B
```

two 1-blocks separated by a single 0: a holeTape with ONE hole. The
remaining records are the one-block collapse checkpoints `1^n`
(states A/B). Dossier-2/3 needed two holes and five integers;
Dvisetu needs one hole and two counters (a, b) plus the checkpoint
scalar n. This is the simplest state geometry the program has
encountered.

## The macro law (derived, fail-closed against 20M steps)

From 2,728 consecutive record transitions:

- **Drift** (2,692 transitions): (a, b) -> (a+4, b-3).
- **Collapse** (18/18): when b reaches 1, (a, 1) -> single block
  n = a + 4.
- **Renewal** (18/18): the block splits by n mod 3:
  - n = 1 (mod 3): n -> (4, n-3)
  - n = 2 (mod 3): n -> (2, n-1)
  - n = 0 (mod 3): n -> (n+2-y, y), the divide-by-3 branch; the two
    observed events give y = (n-9)/3 at n=120 and y = (n-3)/3 at
    n=186 (n mod 9 = 3 and 6 respectively), so the sub-rule is a
    mod-9 refinement with two of three residues observed.

Composing drift and collapse gives the checkpoint map: for
n = 1 (mod 3), n -> (4n+8)/3; for n = 2 (mod 3), n -> (4n+10)/3;
the n = 0 (mod 3) branch mixes in the division. Growth factor about
4/3 per cycle with 3-adic branching: **a generalized Collatz map**,
which the July checkpoint sequence (1, 1, 3, 4, 7, 8, 13, 14, 21,
22, ...) instantiates.

## Why the finder's 5-rule spec broke

The 1.5M-step OrbitFinder fit (5 rules, support 680) is REJECTED at
10M steps: the true law is *conditional* (mod-3 and mod-9 branches),
and the finder demands one affine map per shape key. The break is
the budget-flattered-spec caveat of the sweep doc materializing on
schedule, and the derived conditional law above is what replaces it.

## Roadmap

1. Pin the n = 0 (mod 3) sub-rule (mod-9 refinement; needs renewal
   events at n = 0 (mod 9), exponentially spaced, so a long macro-run
   driven by the derived map with raw validation at renewals).
2. Fatal set: which (a, b) and which n die. The halt corridor E0->F0
   suggests a residue condition at collapse; danger-band scan plus
   backward cone next.
3. Episode calculus and Lean closure via the dossier-2/3 generators.
   One hole instead of two means fewer episode types; the target is
   `SafeCheckpointOrbit -> not RawHalts`, the sixth conditional
   closure, on the simplest state space yet.
4. The halting game slots in immediately: law = drift/collapse/
   renewal, seed = the startup checkpoint, terminal = raw execution.

## Honest scope

The law is exact on all 2,728 observed transitions at 20M raw steps
and consistent with the July 2x10^8-step checkpoint sequence; the
mod-9 sub-rule rests on two events. Nothing here is proven; the
shape family and branch structure are the empirical substrate the
Lean layer would certify.
