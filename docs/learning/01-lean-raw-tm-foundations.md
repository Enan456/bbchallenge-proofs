# Set 1 — The traditional busy-beaver formal layer (raw TM semantics in Lean)

**Files today:** the first ~430 lines of both
`lean/BBChallenge/Dossier1RawTM.lean` and `lean/BBChallenge/AntihydraRawTM.lean`
(currently duplicated per machine; consolidation into a shared
`BBChallenge/RawTM.lean` kernel is planned).

## What this layer is

This is our Lean rendition of the *traditional* busy-beaver formalization —
the same mathematical object the bbchallenge community's canonical work is
built on. BB(5) = 47,176,870 was settled (July 2024) with a proof
machine-checked in **Rocq** (formerly Coq), the "Coq-BB5" development, and
Rocq remains the community's reference formal system for accepted busy-beaver
results. We did not port that Rocq code line-by-line; we re-built the same
semantic foundation natively in **core Lean 4** (no mathlib, axioms only
`propext` and `Quot.sound`), so that everything downstream rests on a
definition an auditor can read in one sitting.

## The model, definition by definition

A machine is six states `A–F` over a two-symbol alphabet, encoded exactly as
in the bbchallenge standard-text format (e.g. Antihydra is
`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`):

- `instr : State → Bool → Option Instr` — the transition table transcribed by
  hand from the standard code. `none` is the single undefined transition
  (`F0` on both our machines); reaching it is the *only* way to halt. This
  hand transcription is the one trust-critical step of the whole layer, which
  is why Plan 1 adds a mechanical parser cross-check.
- `Config = ⟨state, head : Int, tape : Int → Bool⟩` — a two-way-infinite tape
  as a total function, with `writeAt` (pointwise functional override) as the
  only tape mutation. Four small lemmas (`writeAt_same`, `writeAt_other`,
  `writeAt_self`, `writeAt_overwrite`) are the complete tape algebra.
- `step : Config → Option Config` — one raw TM step in the option monad;
  `stepN : Nat → Config → Option Config` iterates it, absorbing halts.
- `RawHalts c := ∃ n, stepN n c = none` and
  `Reaches c d := ∃ n, stepN n c = some d` — halting and reachability, with
  `blankStart` the all-zero start configuration in state `A`.

## What is proven at this level (per machine, identically structured)

1. **Halt characterization.** `step_eq_none_iff`: the machine halts in one
   step *iff* it is in state `F` reading `0`. Pure case analysis over the
   table — nothing clever, and that is the point.
2. **Entry analysis.** `into_F_only_from_E0` (Antihydra) /
   `into_F_only_from_C0` (dossier-1): state `F` is only ever entered from one
   specific transition. So any halt is preceded by a specific local tape
   pattern.
3. **Halt localization.** `halt_requires_e_probe_00` /
   `halt_requires_c_probe_00`: any halting run from a non-`F` start passes
   through a reachable "probe" configuration — the danger state reading a `0`
   whose neighbour (left for Antihydra, right for dossier-1) is also `0`.
   Proved via two generic run lemmas (`stepN_none_last`, `stepN_some_pred`)
   that walk a finite halting run back to its last successful configuration.
4. **The safety contract.** `EProbeSafe` / `CProbeSafe`: "every `0` the danger
   state ever reads has a `1` on the critical side." The theorems
   `nonhalting_of_*_probe_safe` show this invariant implies the machine never
   halts. This is the *interface* between Set 1 and Set 2: everything above
   is elementary and machine-checked; discharging the invariant is where the
   real dynamics live.

## Why this design

- **Auditability over generality.** A bbchallenge reviewer should be able to
  diff `instr` against the machine code and read `step` in a minute. The
  whole trust base is ~150 lines plus core Lean.
- **Rocq parity by construction, not by translation.** Our `step` is
  semantically the standard TM step used in Coq-BB5 and in bbchallenge's
  deciders (partial transition function, undefined = halt, two-way infinite
  binary tape). Parity is a claim to *validate* (Plan 1), not an assumption:
  the validation plan pins the correspondence with a Lean-side parser check
  of the standard-format code and differential execution traces against the
  independent Python simulator in `qgkit/`.
- **`Int`-indexed functional tapes** rather than zipper/list tapes (which the
  Rocq tradition often uses): functional tapes make the segment algebra of
  Set 2 (frame lemmas, block predicates) purely pointwise, at the cost of the
  `writeAt`-tower verbosity we are addressing separately.

## Consolidation target

Both machine files clone this layer verbatim (modulo the table and the probe
direction). The planned split makes it one generic module —
section-parameterized over the transition table, with the probe machinery
generic over `(danger state, probe offset)` — so machine number three starts
from zero duplicated lines, and "Set 1" becomes a single reviewable file.
