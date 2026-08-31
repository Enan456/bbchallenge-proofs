# The halting game: the certified verification, encoded as a two-prover game

**Date:** 2026-08-30 · **Code:** `qgkit/bb6/halting_game.py`

## Construction

The MIP* = RE mechanism, classically instantiated: two isolated
provers commit to a claimed computation history; the verifier
cross-checks snapshots at sampled points; compression makes each
check cheap. Here the history is the renewal-level orbit of
dossier-2/3 and the compression is the certified reduction.

Game G(K, r), claim "the machine halts within K renewals":

1. **Seed check.** Both provers' s_0 must equal the certified anchor
   (6, 13).
2. **Law checks.** r indices j are sampled uniformly; prover A
   supplies (s_j, s_{j+1}), prover B independently supplies s_{j+1};
   the verifier requires cross-consistency and R(s_j) = s_{j+1},
   where R is the closed-form renewal map. Each check is O(1)
   integer arithmetic; the certified episode theorems are what
   entitle the verifier to check the law instead of replaying raw
   steps.
3. **Terminal check.** The claimed halt index k* must satisfy
   fatal(s_{k*}); the certified lethality result converts membership
   in the fatal set into an actual halt within about fifty raw
   steps.

Completeness: a genuinely halting machine gives honest provers a
probability-1 win. Soundness: R is deterministic with fixed seed, so
the only law-consistent history is the true orbit; over the tested
horizon its minimum distance above the fatal window is 4, so the
terminal check fails on it, and any winning strategy needs a seam,
caught per sample with probability 1/K.

## Measured play (K = 100,000)

- The true orbit contains **zero** fatal states, so honest provers
  cannot even name a halt index: no false acceptance is possible on
  the real history.
- Single-seam forgers (true orbit spliced to a fabricated fatal
  state at a random position):

| r (law checks) | accept rate (trials) | bound (1-1/K)^r |
|---|---|---|
| 64 | 0.9980 (4000) | 0.9994 |
| 1,024 | 0.9830 (2000) | 0.9898 |
| 16,384 | 0.7450 (400) | 0.8489 |
| 262,144 | 0.0000 (40) | 0.0727 |
| 1,048,576 | 0.0000 (12) | 0.0000 |

Observed rates sit at or below the single-seam bound (a splice
breaks the law on both of its sides, so the effective catch rate is
about 2/K). At r = 2^20 the analytic failure bound is
(1-1/K)^r < 3·10^-5 and no forgery survived.

## The same game at the certified five-integer layer (dossier-2)

`qgkit/bb6/halting_game23.py` upgrades the renewal-level game to the
full certified abstraction: the law check is one metaStep evaluation
(the exact mirror of the Lean-certified map), and the terminal check
materializes the claimed five-integer state through the certified
holeTape realization and runs the raw machine. Forged terminals are
danger-band corner states (collapsed inter-hole gap, renewal-adjacent
offsets); the lethality result is observed live: every constructed
corner state halts in 6 to 12 raw steps. Measured at K = 200,000
episodes: zero raw-halting states on the sampled true orbit; forgery
acceptance 1.000 at r=64, 0.963 at r=4096, 0.475 at r=65,536, and 0
in all trials at r=2^19 and 2^21. A robustness finding en route:
20,000 random small hole-perturbations of mid-orbit states produced
zero halting configurations; only constructed corner states die, the
same narrow-band geometry the word machine showed under single-cell
mutation.

## The same game over the dossier-5 word calculus

`qgkit/bb6/halting_game5.py` plays G on the rank-1 array-class
machine with word configurations as states, one calc.step evaluation
as the law check (fail-closed: an Unexplained context rejects), and
raw execution of the materialized word as the terminal check. The
forged terminals come from the machine's own backward halt cone:
depth-24 constraint patterns with control state B (618 families),
stamped around the head of a true orbit word, halt by construction
when fully in range. Prover B of a forgery is literally the end
machine.

Measured (word orbit iterated 346 segments past raw validation to
its fail-closed frontier, widths 9,899 to 11,855 cells):

- zero fatal words on the true orbit (raw-verified sample);
  honest provers cannot name a halt index;
- fully stamped cone forgeries pass the terminal check (they
  genuinely halt) and are then caught by law sampling:
  accept 0.980 at r=4, 0.813 at r=32, 0.242 at r=256, 0 in all
  trials at r=2048 and r=8192, tracking the two-sided seam rate
  (1-2/K)^r at K=346.

The game generalizes across state-space classes unchanged: the same
verifier code plays over five-integer states and over words of
growing dimension, because all it needs is a certified law, a seed,
and a checkable fatal predicate.

## Reading

The verifier's work is r constant-cost arithmetic checks on
five-integer states whose raw-tape realizations, at depth 10^5
renewals, are astronomically long. Verification cost decouples from
runtime; that is the middle rung of the paper's spectrum, played as
an actual game. The dossier-5 word calculus supports the same game
on word states (its reseed differentials are precisely the law
check, demonstrated exact on both arrival kinds); the terminal
predicate there is the fatal-motif set mapped in the step-2 work.

## Honest scope

The game is classical; no entanglement is used or needed, because
the histories here are deterministic and the seed is fixed. Its
soundness constant inherits the empirical margin-4 statement over
the tested horizon; the unconditional version of soundness is
exactly the SafeMetaOrbit conjecture.
