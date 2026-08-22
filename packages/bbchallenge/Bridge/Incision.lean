import BBChallenge.AntihydraRawTM

/-!
# Incision layer for Antihydra (plan 3, tasks 1–2)

Boundary decomposition of the abstract step, the closed-form volley
(certified event-skipping), and the event-process equivalence: checking the
orbit **only at incision events** (boundary states, where the counter can
move or the orbit can die) is sound *and* complete for `SafeOrbitA`.

Everything here is core-only and stays at the `[propext, Quot.sound]` axiom
bar of the main development.
-/

namespace QIG.AntihydraRawTM

/-! ## The death set and the boundary -/

/-- The death set: exactly the abstract states where `astep` dies.  These are
the halt opportunities — `m = 0` (no middle block) or a drop (`m = 2`) with
the counter too small to pay. -/
def Dead (s : AState) : Prop := s.m = 0 ∨ (s.m = 2 ∧ s.a ≤ 1)

/-- The incision boundary: everything counter-changing (drop, merge) and
every death happens at `m ≤ 2`; above it only the counter-frozen hydra rule
fires. -/
def Boundary (s : AState) : Prop := s.m ≤ 2

instance (s : AState) : Decidable (Dead s) := by unfold Dead; exact inferInstance
instance (s : AState) : Decidable (Boundary s) := by unfold Boundary; exact inferInstance

/-- `astep` dies exactly on the death set. -/
theorem astep_eq_none_iff (s : AState) : astep s = none ↔ Dead s := by
  obtain ⟨a, m, c⟩ := s
  by_cases h3 : 3 ≤ m
  · -- simp leaves `¬(m = 0) ∧ ¬(m = 2 ∧ a ≤ 1)`; split it so omega only
    -- sees atomic-ish goals (compound positive goals cost Classical.choice)
    simp [astep, Dead, h3]
    constructor <;> omega
  · by_cases h2 : m = 2
    · by_cases ha : 2 ≤ a
      · simp [astep, Dead, h2, ha]
        omega
      · simp [astep, Dead, h2, ha]
        try omega
    · by_cases h1 : m = 1
      · simp [astep, Dead, h1, h2]
        try omega
      · -- here `m = 0`: simp uses h2/h1 to kill the right disjunct, leaving
        -- the atomic goal `m = 0` (omega must never see a positive ∨-goal,
        -- which would pull in `Classical.choice`)
        simp [astep, Dead, h3, h2, h1]
        omega

/-- Above the boundary only the hydra rule fires, in closed form. -/
theorem astep_interior {a m c : Nat} (h3 : 3 ≤ m) :
    astep ⟨a, m, c⟩ = some ⟨a, m - 2, c + 3⟩ := by
  simp [astep, h3]

theorem astep_merge (a c : Nat) : astep ⟨a, 1, c⟩ = some ⟨a + 2, c + 2, 2⟩ := by
  simp [astep]

theorem astep_drop_alive {a : Nat} (c : Nat) (ha : 2 ≤ a) :
    astep ⟨a, 2, c⟩ = some ⟨a - 1, c + 3, 2⟩ := by
  simp [astep, ha]

theorem astep_drop_dead {a : Nat} (c : Nat) (ha : a ≤ 1) :
    astep ⟨a, 2, c⟩ = none := by
  simp [astep, show ¬ 2 ≤ a by omega]

/-- The conjecture is exactly death-set avoidance along the orbit. -/
theorem safeOrbitA_iff_avoids_death :
    SafeOrbitA ↔ ∀ n s, aorbit n = some s → ¬ Dead s := by
  constructor
  · intro h n s hs hd
    have hnone := h (n + 1)
    rw [aorbit_succ hs, (astep_eq_none_iff s).mpr hd] at hnone
    exact hnone rfl
  · intro h n
    induction n with
    | zero => intro hc; simp [aorbit] at hc
    | succ n ih =>
        cases horb : aorbit n with
        | none => exact absurd horb ih
        | some s =>
            rw [aorbit_succ horb]
            intro hc
            exact h n s horb ((astep_eq_none_iff s).mp hc)

/-! ## The volley: certified event-skipping -/

/-- Collapse a whole run of hydra steps in closed form: from `(a, m, c)` the
orbit deterministically reaches the boundary state
`(a, 2 - m % 2, c + 3⌊(m-1)/2⌋)` without the counter moving. -/
def volley (s : AState) : AState :=
  if s.m ≤ 2 then s else ⟨s.a, 2 - s.m % 2, s.c + 3 * ((s.m - 1) / 2)⟩

theorem volley_boundary {s : AState} (h : s.m ≤ 2) : volley s = s := by
  simp [volley, h]

theorem volley_boundary_mem (s : AState) : Boundary (volley s) := by
  obtain ⟨a, m, c⟩ := s
  by_cases h : m ≤ 2 <;> simp [volley, Boundary, h] <;> omega

theorem volley_unfold {a m c : Nat} (h : ¬ m ≤ 2) :
    volley ⟨a, m, c⟩ = ⟨a, 2 - m % 2, c + 3 * ((m - 1) / 2)⟩ := by
  simp [volley, h]

/-- The closed form really is the hydra recursion.  (Component equalities go
to `omega` one at a time via `congr` — compound goals would make `omega`
reach for `Classical.choice`.) -/
theorem volley_interior {a m c : Nat} (h3 : 3 ≤ m) :
    volley ⟨a, m, c⟩ = volley ⟨a, m - 2, c + 3⟩ := by
  rw [volley_unfold (show ¬ m ≤ 2 by omega)]
  by_cases h : m - 2 ≤ 2
  · rw [volley_boundary (s := ⟨a, m - 2, c + 3⟩) h]
    congr 1
    · omega
    · omega
  · rw [volley_unfold h]
    congr 1
    · omega
    · omega

/-- Iterated abstract step (from an arbitrary state). -/
def aiter : Nat → AState → Option AState
  | 0, s => some s
  | k + 1, s =>
      match astep s with
      | none => none
      | some t => aiter k t

theorem aiter_one (s : AState) : aiter 1 s = astep s := by
  cases h : astep s <;> simp [aiter, h]

theorem aiter_add (j k : Nat) (s : AState) :
    aiter (j + k) s = match aiter j s with
      | none => none
      | some t => aiter k t := by
  induction j generalizing s with
  | zero => rw [Nat.zero_add]; rfl
  | succ j ih =>
      rw [show j + 1 + k = (j + k) + 1 by omega]
      show (match astep s with | none => none | some t => aiter (j + k) t) =
        match (match astep s with | none => none | some t => aiter j t) with
        | none => none
        | some t => aiter k t
      cases hstep : astep s with
      | none => rfl
      | some t => exact ih t

theorem aorbit_eq_aiter (n : Nat) : aorbit n = aiter n ⟨2, 7, 2⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show (match aorbit n with | none => none | some s => astep s) =
        aiter (n + 1) ⟨2, 7, 2⟩
      rw [aiter_add n 1, ← ih]
      cases aorbit n with
      | none => rfl
      | some s => exact (aiter_one s).symm

theorem aorbit_add_aiter (n j : Nat) {t : AState} (h : aorbit n = some t) :
    aorbit (n + j) = aiter j t := by
  rw [aorbit_eq_aiter, aiter_add n j, ← aorbit_eq_aiter, h]

/-- The volley is reachable along the abstract orbit (and, since interior
steps never die, reachable without dying). -/
theorem aiter_volley_fuel :
    ∀ (k : Nat) (s : AState), s.m ≤ 2 * k + 2 →
      ∃ j, aiter j s = some (volley s) := by
  intro k
  induction k with
  | zero =>
      intro s hm
      exact ⟨0, by rw [volley_boundary hm]; rfl⟩
  | succ k ih =>
      intro s hm
      obtain ⟨a, m, c⟩ := s
      simp only at hm
      by_cases h3 : 3 ≤ m
      · obtain ⟨j, hj⟩ := ih ⟨a, m - 2, c + 3⟩ (show m - 2 ≤ 2 * k + 2 by omega)
        refine ⟨1 + j, ?_⟩
        rw [aiter_add 1 j, aiter_one, astep_interior h3, volley_interior h3]
        exact hj
      · exact ⟨0, by rw [volley_boundary (show m ≤ 2 by omega)]; rfl⟩

theorem aiter_volley (s : AState) : ∃ j, aiter j s = some (volley s) :=
  aiter_volley_fuel s.m s (by omega)

/-! ## The event process -/

/-- One incision event: apply the boundary rule, then skip the whole
following hydra volley.  This is the accelerated dynamics: one `estep`
per counter movement. -/
def estep (s : AState) : Option AState :=
  match astep s with
  | none => none
  | some t => some (volley t)

/-- The event orbit: the abstract orbit sampled at its incision events,
starting from the first boundary state after the startup record. -/
def eorbit : Nat → Option AState
  | 0 => some (volley ⟨2, 7, 2⟩)
  | k + 1 =>
      match eorbit k with
      | none => none
      | some s => estep s

/-- Safety of the boundary-event process alone. -/
def EventSafe : Prop := ∀ k, eorbit k ≠ none

theorem eorbit_succ {k : Nat} {s : AState} (h : eorbit k = some s) :
    eorbit (k + 1) = estep s := by
  show (match eorbit k with | none => none | some s => estep s) = estep s
  rw [h]

/-! ## The equivalence: boundary-only checking is sound and complete -/

/-- **Soundness of boundary-only checking**: if the event process never dies,
the full abstract orbit never dies.  (Every full-orbit state lies on the
volley path of an event state, and volleys never die.) -/
theorem safeOrbitA_of_eventSafe (h : EventSafe) : SafeOrbitA := by
  have main : ∀ n, ∃ t, aorbit n = some t ∧ ∃ k, eorbit k = some (volley t) := by
    intro n
    induction n with
    | zero => exact ⟨⟨2, 7, 2⟩, rfl, 0, rfl⟩
    | succ n ih =>
        obtain ⟨t, ht, k, hk⟩ := ih
        by_cases h3 : 3 ≤ t.m
        · obtain ⟨a, m, c⟩ := t
          simp only at h3
          refine ⟨⟨a, m - 2, c + 3⟩, ?_, k, ?_⟩
          · rw [aorbit_succ ht, astep_interior h3]
          · rw [← volley_interior h3]; exact hk
        · have hvt : volley t = t := volley_boundary (by omega)
          rw [hvt] at hk
          have hne : eorbit (k + 1) ≠ none := h (k + 1)
          rw [eorbit_succ hk] at hne
          cases hstep : astep t with
          | none => exact absurd (by simp [estep, hstep]) hne
          | some u =>
              refine ⟨u, ?_, k + 1, ?_⟩
              · rw [aorbit_succ ht, hstep]
              · rw [eorbit_succ hk]; simp [estep, hstep]
  intro n
  obtain ⟨t, ht, _⟩ := main n
  rw [ht]
  simp

/-- **Completeness of boundary-only checking**: if the full orbit never dies,
neither does the event process (event states are orbit states). -/
theorem eventSafe_of_safeOrbitA (h : SafeOrbitA) : EventSafe := by
  have main : ∀ k, ∃ t n, eorbit k = some t ∧ aorbit n = some t := by
    intro k
    induction k with
    | zero =>
        obtain ⟨j, hj⟩ := aiter_volley ⟨2, 7, 2⟩
        refine ⟨volley ⟨2, 7, 2⟩, j, rfl, ?_⟩
        rw [aorbit_eq_aiter]
        exact hj
    | succ k ih =>
        obtain ⟨t, n, hek, han⟩ := ih
        have hne : aorbit (n + 1) ≠ none := h (n + 1)
        rw [aorbit_succ han] at hne
        cases hstep : astep t with
        | none => exact absurd hstep hne
        | some u =>
            obtain ⟨j, hj⟩ := aiter_volley u
            have hn1 : aorbit (n + 1) = some u := by
              rw [aorbit_succ han, hstep]
            refine ⟨volley u, n + 1 + j, ?_, ?_⟩
            · rw [eorbit_succ hek]; simp [estep, hstep]
            · rw [aorbit_add_aiter (n + 1) j hn1]; exact hj
  intro k
  obtain ⟨t, n, hek, _⟩ := main k
  rw [hek]
  simp

/-- **The incision theorem.**  Checking only at boundary events is exactly
as strong as checking the whole orbit. -/
theorem eventSafe_iff_safeOrbitA : EventSafe ↔ SafeOrbitA :=
  ⟨safeOrbitA_of_eventSafe, eventSafe_of_safeOrbitA⟩

/-- Chained with the Set 2 reduction: boundary-event safety alone implies
Antihydra never halts from the blank tape. -/
theorem eventSafe_nonhalting (h : EventSafe) : ¬ RawHalts blankStart :=
  safeOrbitA_nonhalting (safeOrbitA_of_eventSafe h)

end QIG.AntihydraRawTM

#print axioms QIG.AntihydraRawTM.astep_eq_none_iff
#print axioms QIG.AntihydraRawTM.eventSafe_iff_safeOrbitA
#print axioms QIG.AntihydraRawTM.eventSafe_nonhalting
