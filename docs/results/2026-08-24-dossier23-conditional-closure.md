# Dossier-2 and dossier-3: conditional closure via the interaction calculus

**Date:** 2026-08-24
**Machines:**
- dossier-2 `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD`
- dossier-3 `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE` (exact mirror dynamics)

**Lean:** `busy-beaver-core/BusyBeaverCore/Dossier2RawTM.lean`, `Dossier3RawTM.lean`
(all theorems at `[propext, Quot.sound]`; gate: `scripts/check_lean.sh`)
**Tests:** `tests/bb6/test_dossier23_theorems.py` (differential validation of
every theorem layer against raw emulation)

## Headline

Both machines are **reduced, machine-checked end to end, to a single
arithmetic conjecture on five integers each**:

```
dossier2_nonhalting_of_safeMetaOrbit : SafeMetaOrbit → ¬ RawHalts blankStart
dossier3_nonhalting_of_safeMetaOrbit : SafeMetaOrbit → ¬ RawHalts blankStart
```

`SafeMetaOrbit` says the *abstract orbit* — a deterministic, guard-dispatched
affine map `metaStep` on shapes `(three?, l, h1, h2, r)` — never leaves its
guarded region. Everything else is a theorem: the machine's startup
(235 / 2044 concrete steps, including one degenerate episode each), and every
raw step it will ever take afterwards, is accounted for by seven certified
episode theorems.

## The interaction calculus (what the machines actually do)

The tape between spawn entries is always `holeTape`: a solid field of 1s with
two mobile holes. Each episode is one spawn-entry-to-spawn-entry trajectory:

| episode | shape map | steps |
|---|---|---|
| spawn | dig fresh carried hole at `r−2`, field +1 | 7 |
| spawn-variant | fill the edge hole, re-dig one left | 7 |
| traverse-generic | crawl, cross upper hole (+4), terminate lower (+6) | `10k₁+13+10k₂+13+1+2m` |
| fuse (`b=1`) | three business fills, fused hole at `h1+9`, hole-exit | `10k₁+19+1+2m` |
| carried-terminate | terminate without crossing, hole-exit | `10k₁+13+1+2m` |
| deep-odd / deep-even | cross the lone hole, run to the left edge, extend field by 1 / 3 | crawl + edge + sweep |

Underneath: `cat_run` (the n-fold caterpillar), `sweep_mixed` (the D↔F return
gait that needs 1s only on D-cells — why holes cross at F-parity for free),
and eight fixed-window atoms (cross, terminate, fuse, two edge businesses, two
march fragments, spawn-variant). Every danger-state read-of-0 in the entire
eternal run happens inside a business chain with a proven 1 on the probe side.

## Validation

- The calculus matched **1,000,000,000 raw steps per machine** episode-for-
  episode, fail-closed (one flagged startup degenerate each, covered by the
  concrete anchor runs).
- The Lean `metaStep`'s python mirror reproduces every raw spawn-entry
  snapshot (position, full shape) for 10⁶ raw steps from the anchors — now a
  permanent pytest.
- The abstract orbits stay alive for ≥ 10⁸ abstract episodes (widths grow to
  ~10⁸ cells; the equivalent raw-step horizon is ~10¹⁵).

## Why the remaining conjecture is genuinely hard (and sharp)

The corner states excluded by the guards are **provably lethal**: constructing
`F3` with `c = 6` or a carried-terminate with `r−h1 = 5` and running the raw
machine produces a probe violation (halt) within ~50 steps. So `SafeMetaOrbit`
is not an artifact of our proof method — avoiding those bands *is* the halting
question.

The renewal-to-renewal map is a subtractive Euclid/Collatz hybrid: generic
loops conserve `γ = c − b` while `a` grows by 6 per loop; deep renewals swap
`(a, b)` and reset `a` to 6/9; fuses rotate `(a, 2, c) → (a+9, c−6, 1)`. The
danger bands (`γ ∈ {1,3,5}` at renewal, `b_C ≤ 2` at carried entries) are
finite, explicit, and — empirically — never approached. Proving that is a
number-theoretic question about a deterministic integer dynamical system, of
the same epistemic class as the Antihydra conjecture but *deterministic* and,
we believe, considerably more structured.

## Honest scope

- No unconditional non-halting claim is made for either machine.
- The conditional theorems are axiom-clean (`propext, Quot.sound` only) and
  the axiom gate covers every theorem cited here.
- The startup anchors are fully concrete certified runs; nothing about the
  startup is conjectural.
- The conjectures' empirical horizon is bounded by what we ran, not by what
  is true.
