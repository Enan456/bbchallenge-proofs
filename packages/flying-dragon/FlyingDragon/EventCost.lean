import Bridge.Incision

/-!
# Certified event costs (flying-dragon, tier-1 extension)

The stage756 atlas *measures* the raw-step cost of each incision event; this
module makes those quantities theorems. The per-rule costs come from the
proven trajectories in busy-beaver-core (`hydra_step` = `2c+11`,
`drop_step` = `2c+15`, `merge_chain` = `2a+2c+22`); a volley of `j` hydra
steps starting from a fresh `c = 2` block therefore costs
`Σ_{i<j} (2·(2+3i) + 11)`, and we prove the closed form `3j² + 15j` —
the formula the Python atlas uses (as `3j² + 12j + 3j`).

Also the death margin, as a certified quantity on boundary states.
Core-only; axioms `[propext, Quot.sound]`.
-/

namespace QIG.FlyingDragon

open QIG.AntihydraRawTM

/-- Cost of the `i`-th hydra step of a volley that starts on a fresh
`c = 2` block: the c-block has grown to `2 + 3i`, and `hydra_step` costs
`2c + 11`. -/
def hydraStepCost (i : Nat) : Nat := 2 * (2 + 3 * i) + 11

/-- Total cost of a `j`-step volley from a fresh block. -/
def volleyCost : Nat → Nat
  | 0 => 0
  | j + 1 => volleyCost j + hydraStepCost j

/-- **Closed form**: a `j`-step volley costs exactly `3j² + 12j` plus the
`3j` from the growing writes — total `3j² + 15j`. -/
theorem volleyCost_closed (j : Nat) : volleyCost j = 3 * j * j + 12 * j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      show volleyCost j + hydraStepCost j = 3 * (j + 1) * (j + 1) + 12 * (j + 1)
      rw [ih]
      unfold hydraStepCost
      rw [Nat.mul_assoc 3 (j + 1) (j + 1),
          show (j + 1) * (j + 1) = j * j + 2 * j + 1 from by
            rw [Nat.succ_mul, Nat.mul_succ]; omega,
          Nat.mul_assoc 3 j j]
      omega

/-- The boundary rule's own raw cost, from the proven step counts. -/
def ruleCost (s : AState) : Nat :=
  if s.m = 1 then 2 * s.a + 2 * s.c + 22        -- merge_chain
  else if s.m = 2 then 2 * s.c + 15             -- drop_step
  else 0

/-- One incision event's certified total cost: the boundary rule plus the
whole following volley.  The rule lands on block value `M` (`c+2` after a
merge, `c+3` after a drop) with a fresh `c = 2`, and the volley then fires
`(M-1)/2` hydra steps (landing on 1 for odd `M`, 2 for even). -/
def eventCost (s : AState) : Nat :=
  ruleCost s + volleyCost (((if s.m = 1 then s.c + 2 else s.c + 3) - 1) / 2)

/-- The closed form of a whole event's cost — what the Python atlas
computes, now a theorem. -/
theorem eventCost_closed (s : AState) :
    eventCost s
      = ruleCost s
        + (3 * (((if s.m = 1 then s.c + 2 else s.c + 3) - 1) / 2)
             * (((if s.m = 1 then s.c + 2 else s.c + 3) - 1) / 2)
           + 12 * (((if s.m = 1 then s.c + 2 else s.c + 3) - 1) / 2)) := by
  unfold eventCost
  rw [volleyCost_closed]

/-- The death margin at a boundary state: how many counter units above the
death condition a drop finds. `0` is the last surviving drop. -/
def margin (s : AState) : Nat := s.a - 2

/-- A drop that survives (`astep` alive at `m = 2`) has its margin
well-defined as `a − 2` with `a ≥ 2` — dying and `margin` bottoming out
coincide. -/
theorem drop_alive_iff_margin (a c : Nat) :
    astep ⟨a, 2, c⟩ ≠ none ↔ 2 ≤ a := by
  constructor
  · intro h
    by_cases ha : 2 ≤ a
    · exact ha
    · exact absurd (astep_drop_dead c (by omega)) h
  · intro ha h
    rw [astep_drop_alive c ha] at h
    simp at h

end QIG.FlyingDragon

#print axioms QIG.FlyingDragon.volleyCost_closed
#print axioms QIG.FlyingDragon.eventCost_closed
#print axioms QIG.FlyingDragon.drop_alive_iff_margin
