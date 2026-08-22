/-!
# Challenge: boundary-only checking is sound and complete for the Antihydra orbit

The abstract orbit of the BB(6) machine *Antihydra*
(`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`) is the sequence of triples
`(a, m, c)` from `(2, 7, 2)` under one exact rule per record transition: the
counter-frozen *hydra* rule for `m ≥ 3`, the counter-paying *drop* at
`m = 2`, and the counter-feeding *merge* at `m = 1`.  The community's
Antihydra conjecture is equivalent to this orbit never reaching `none`
(machine-checked elsewhere; not claimed here).

This challenge concerns the *incision structure* of that orbit:

1. `astep_dies_iff` — the orbit can die **only** on the explicit boundary
   set: `m = 0`, or a drop (`m = 2`) with counter `a ≤ 1`.
2. `boundary_checking_complete` — the *event process* (`eorbit`), which
   samples the orbit only at those boundary states and skips every
   intervening hydra volley in closed form (`volley`), dies **iff** the full
   orbit dies.  Verifying orbit safety only at incision events is therefore
   both sound and complete — an exponential certified acceleration, since
   consecutive events are separated by volleys whose raw-machine cost grows
   without bound.

This file is self-contained over Lean core; proofs are in the accompanying
solution module.
-/

namespace IncisionChallenge

/-- One abstract orbit step on `(a, m, c)`: hydra (`m ≥ 3`, counter
frozen), drop (`m = 2`, counter pays 1, dies if it cannot), merge (`m = 1`,
counter gains 2); `m = 0` is dead. -/
def astep : Nat × Nat × Nat → Option (Nat × Nat × Nat)
  | (a, m, c) =>
      if 3 ≤ m then some (a, m - 2, c + 3)
      else if m = 2 then (if 2 ≤ a then some (a - 1, c + 3, 2) else none)
      else if m = 1 then some (a + 2, c + 2, 2)
      else none

/-- The abstract orbit from the post-startup record `(2, 7, 2)`. -/
def aorbit : Nat → Option (Nat × Nat × Nat)
  | 0 => some (2, 7, 2)
  | k + 1 =>
      match aorbit k with
      | none => none
      | some s => astep s

/-- Collapse a maximal run of hydra steps in closed form: from `(a, m, c)`
deterministically to the boundary state
`(a, 2 - m % 2, c + 3⌊(m-1)/2⌋)`, the counter untouched. -/
def volley : Nat × Nat × Nat → Nat × Nat × Nat
  | (a, m, c) =>
      if m ≤ 2 then (a, m, c) else (a, 2 - m % 2, c + 3 * ((m - 1) / 2))

/-- One incision event: the boundary rule, then the whole following
volley. -/
def estep (s : Nat × Nat × Nat) : Option (Nat × Nat × Nat) :=
  match astep s with
  | none => none
  | some t => some (volley t)

/-- The event orbit: the abstract orbit sampled at its incision events. -/
def eorbit : Nat → Option (Nat × Nat × Nat)
  | 0 => some (volley (2, 7, 2))
  | k + 1 =>
      match eorbit k with
      | none => none
      | some s => estep s

/-- The orbit dies exactly on the explicit boundary death set. -/
theorem astep_dies_iff (a m c : Nat) :
    astep (a, m, c) = none ↔ (m = 0 ∨ (m = 2 ∧ a ≤ 1)) := sorry

/-- **Boundary-only checking is sound and complete**: the event process
never dies iff the full abstract orbit never dies. -/
theorem boundary_checking_complete :
    (∀ k, eorbit k ≠ none) ↔ (∀ k, aorbit k ≠ none) := sorry

end IncisionChallenge
