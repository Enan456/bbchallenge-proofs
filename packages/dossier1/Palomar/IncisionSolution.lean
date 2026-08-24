import Bridge.Incision

/-!
# Solution: boundary-only checking is sound and complete

Re-declares the definitions and theorems of `Palomar.IncisionChallenge`
verbatim and proves them by transporting `Bridge.Incision`'s certified
results (`QIG.AntihydraRawTM.astep_eq_none_iff`,
`eventSafe_iff_safeOrbitA`) across the challenge's triple-based
formulation.
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

/-! ## Transport to the certified development -/

/-! ## Transport: why re-declaring works

The challenge defines its own copies of every type, so its theorems cannot
simply cite ours.  The maps below are componentwise identities up to
renaming; each commutation lemma is a finite case split or structural
induction; the certified theorems then cross the bridge intact. -/

def tMap (s : Nat × Nat × Nat) : QIG.AntihydraRawTM.AState :=
  ⟨s.1, s.2.1, s.2.2⟩

theorem astep_map (s : Nat × Nat × Nat) :
    QIG.AntihydraRawTM.astep (tMap s) = Option.map tMap (astep s) := by
  obtain ⟨a, m, c⟩ := s
  by_cases h3 : 3 ≤ m
  · simp [astep, QIG.AntihydraRawTM.astep, tMap, h3]
  · by_cases h2 : m = 2
    · by_cases ha : 2 ≤ a <;>
        simp [astep, QIG.AntihydraRawTM.astep, tMap, h3, h2, ha]
    · by_cases h1 : m = 1 <;>
        simp [astep, QIG.AntihydraRawTM.astep, tMap, h3, h2, h1]

theorem volley_map (s : Nat × Nat × Nat) :
    QIG.AntihydraRawTM.volley (tMap s) = tMap (volley s) := by
  obtain ⟨a, m, c⟩ := s
  by_cases h : m ≤ 2 <;>
    simp [volley, QIG.AntihydraRawTM.volley, tMap, h]

theorem estep_map (s : Nat × Nat × Nat) :
    QIG.AntihydraRawTM.estep (tMap s) = Option.map tMap (estep s) := by
  rw [show QIG.AntihydraRawTM.estep (tMap s)
        = (match QIG.AntihydraRawTM.astep (tMap s) with
           | none => none
           | some t => some (QIG.AntihydraRawTM.volley t))
      from rfl]
  rw [show estep s
        = (match astep s with
           | none => none
           | some t => some (volley t))
      from rfl]
  rw [astep_map]
  cases hs : astep s with
  | none => rfl
  | some t =>
      show some (QIG.AntihydraRawTM.volley (tMap t)) = some (tMap (volley t))
      rw [volley_map]

theorem aorbit_map : ∀ k,
    QIG.AntihydraRawTM.aorbit k = Option.map tMap (aorbit k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show QIG.AntihydraRawTM.aorbit (k + 1)
            = (match QIG.AntihydraRawTM.aorbit k with
               | none => none
               | some s => QIG.AntihydraRawTM.astep s)
          from rfl]
      rw [show aorbit (k + 1)
            = (match aorbit k with
               | none => none
               | some s => astep s)
          from rfl]
      rw [ih]
      cases hk : aorbit k with
      | none => rfl
      | some s =>
          show QIG.AntihydraRawTM.astep (tMap s) = Option.map tMap (astep s)
          exact astep_map s

theorem eorbit_map : ∀ k,
    QIG.AntihydraRawTM.eorbit k = Option.map tMap (eorbit k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show QIG.AntihydraRawTM.eorbit (k + 1)
            = (match QIG.AntihydraRawTM.eorbit k with
               | none => none
               | some s => QIG.AntihydraRawTM.estep s)
          from rfl]
      rw [show eorbit (k + 1)
            = (match eorbit k with
               | none => none
               | some s => estep s)
          from rfl]
      rw [ih]
      cases hk : eorbit k with
      | none => rfl
      | some s =>
          show QIG.AntihydraRawTM.estep (tMap s) = Option.map tMap (estep s)
          exact estep_map s

/-- A mapped orbit is `none`-free iff the original is. -/
theorem safety_iff {α β : Type} (f : α → β) (o1 : Nat → Option β)
    (o2 : Nat → Option α) (h : ∀ k, o1 k = Option.map f (o2 k)) :
    (∀ k, o1 k ≠ none) ↔ (∀ k, o2 k ≠ none) := by
  constructor
  · intro hs k hk
    have := hs k
    rw [h k, hk] at this
    exact this rfl
  · intro hs k
    rw [h k]
    cases hk : o2 k with
    | none => exact absurd hk (hs k)
    | some _ => simp

/-- The orbit dies exactly on the explicit boundary death set. -/
theorem astep_dies_iff (a m c : Nat) :
    astep (a, m, c) = none ↔ (m = 0 ∨ (m = 2 ∧ a ≤ 1)) := by
  have hmap := astep_map (a, m, c)
  rw [show tMap (a, m, c) = (⟨a, m, c⟩ : QIG.AntihydraRawTM.AState) from rfl]
    at hmap
  have hq := QIG.AntihydraRawTM.astep_eq_none_iff ⟨a, m, c⟩
  constructor
  · intro h
    rw [h] at hmap
    exact hq.mp hmap
  · intro h
    have hnone := hq.mpr h
    rw [hnone] at hmap
    cases hs : astep (a, m, c) with
    | none => rfl
    | some t => rw [hs] at hmap; simp at hmap

/-- **Boundary-only checking is sound and complete**: the event process
never dies iff the full abstract orbit never dies. -/
theorem boundary_checking_complete :
    (∀ k, eorbit k ≠ none) ↔ (∀ k, aorbit k ≠ none) := by
  have h1 := safety_iff tMap QIG.AntihydraRawTM.eorbit eorbit eorbit_map
  have h2 := safety_iff tMap QIG.AntihydraRawTM.aorbit aorbit aorbit_map
  rw [← h1, ← h2]
  exact QIG.AntihydraRawTM.eventSafe_iff_safeOrbitA

end IncisionChallenge
