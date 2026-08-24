import Bridge.Incision

/-!
# The Forge, layer 2: generic orbits and margin localization

The abstract-orbit machinery proven once, for any state type: iterated
partial dynamics, and the **margin contract** — supply any `margin`
function that (a) falls by at most one per step and (b) is zero wherever
the dynamics die, and you get certified skip windows
(`margin_halt_localized`) and the projected-death bound, generically.

`AntihydraDemo` instantiates the contract with `margin = a − 1` on the
incision event process and re-derives the machine-specific
`halt_localized` from the generic theorem — the template every new
machine's margin candidate follows.

Core-only; axioms `[propext, Quot.sound]`.
-/

namespace QIG.Forge

section Orbit

variable {A : Type} (f : A → Option A) (seed : A)

/-- Iterated partial dynamics from a seed. -/
def orbit : Nat → Option A
  | 0 => some seed
  | k + 1 =>
      match orbit k with
      | none => none
      | some s => f s

def OrbitSafe : Prop := ∀ k, orbit f seed k ≠ none

theorem orbit_succ {k : Nat} {s : A} (h : orbit f seed k = some s) :
    orbit f seed (k + 1) = f s := by
  show (match orbit f seed k with
        | none => none
        | some s => f s) = f s
  rw [h]

variable (margin : A → Nat)

/-- The margin contract: one step loses at most one margin unit, and the
dynamics die only at margin zero. -/
def MarginRules : Prop :=
  (∀ s t, f s = some t → margin s ≤ margin t + 1) ∧
  (∀ s, f s = none → margin s = 0)

theorem margin_lower_bound (hm : MarginRules f margin) :
    ∀ (j k : Nat) (s : A), orbit f seed k = some s → j + 1 ≤ margin s →
      ∃ t, orbit f seed (k + j) = some t ∧ margin s ≤ margin t + j := by
  intro j
  induction j with
  | zero =>
      intro k s h _
      exact ⟨s, by rw [Nat.add_zero]; exact h, by omega⟩
  | succ j ih =>
      intro k s h hj
      obtain ⟨t, ht, hbound⟩ := ih k s h (by omega)
      cases hf : f t with
      | none =>
          have h0 := hm.2 t hf
          exact absurd hj (by omega)
      | some u =>
          have hstep := hm.1 t u hf
          refine ⟨u, ?_, by omega⟩
          rw [show k + (j + 1) = (k + j) + 1 by omega,
              orbit_succ f seed ht, hf]

/-- **Generic skip windows**: from any live state, the orbit provably
survives the next `margin s − 1` steps — no death checks needed inside
the window. -/
theorem margin_halt_localized (hm : MarginRules f margin) (k j : Nat)
    (s : A) (h : orbit f seed k = some s) (hj : j < margin s) :
    orbit f seed (k + j) ≠ none := by
  obtain ⟨t, ht, _⟩ := margin_lower_bound f seed margin hm j k s h (by omega)
  rw [ht]
  simp

/-- Any death lies at least `margin s` steps past any live state. -/
theorem margin_death_bound (hm : MarginRules f margin) (k n : Nat) (s : A)
    (h : orbit f seed k = some s) (hdead : orbit f seed n = none)
    (hkn : k ≤ n) : k + margin s ≤ n := by
  by_cases hlt : n - k < margin s
  · exact absurd
      (by rw [show k + (n - k) = n by omega]; exact hdead)
      (margin_halt_localized f seed margin hm k (n - k) s h hlt)
  · omega

end Orbit

/-!
## Demo instantiation: Antihydra's event process

`margin = a − 1` (zero at both death modes) satisfies the contract; the
machine-specific skip windows fall out of the generic theorem.
-/

namespace AntihydraDemo

open QIG.AntihydraRawTM

def margin (s : AState) : Nat := if s.m = 0 then 0 else s.a - 1

/-- Constructor-form counter preservation (local so forge need not import
flying-dragon; the mk-form keeps `omega` sighted). -/
theorem volley_a' (x y z : Nat) : (volley ⟨x, y, z⟩).a = x := by
  by_cases h : y ≤ 2
  · rw [volley_boundary (show (⟨x, y, z⟩ : AState).m ≤ 2 from h)]
  · rw [volley_unfold h]

theorem volley_m_pos {s : AState} (h : 1 ≤ s.m) : 1 ≤ (volley s).m := by
  obtain ⟨a, m, c⟩ := s
  simp only at h
  by_cases hb : m ≤ 2
  · rw [volley_boundary hb]
    exact h
  · rw [volley_unfold hb]
    show 1 ≤ 2 - m % 2
    omega

theorem margin_rules : MarginRules estep margin := by
  constructor
  · intro s t hst
    obtain ⟨a, m, c⟩ := s
    rw [show estep ⟨a, m, c⟩
          = (match astep ⟨a, m, c⟩ with
             | none => none
             | some u => some (volley u))
        from rfl] at hst
    by_cases h3 : 3 ≤ m
    · rw [astep_interior h3] at hst
      have ht : t = volley ⟨a, m - 2, c + 3⟩ := (Option.some.inj hst).symm
      have hm1 : 1 ≤ (volley ⟨a, m - 2, c + 3⟩).m :=
        volley_m_pos (show 1 ≤ (⟨a, m - 2, c + 3⟩ : AState).m from by
          show 1 ≤ m - 2; omega)
      have hL : margin ⟨a, m, c⟩ = a - 1 := by
        show (if (⟨a, m, c⟩ : AState).m = 0 then 0
              else (⟨a, m, c⟩ : AState).a - 1) = a - 1
        rw [if_neg (show ¬ (⟨a, m, c⟩ : AState).m = 0 from by
          show ¬ m = 0; omega)]
      have hR : margin t = a - 1 := by
        rw [ht]
        show (if (volley ⟨a, m - 2, c + 3⟩).m = 0 then 0
              else (volley ⟨a, m - 2, c + 3⟩).a - 1) = a - 1
        rw [if_neg (by omega), volley_a']
      rw [hL, hR]
      omega
    · by_cases h1 : m = 1
      · subst h1
        rw [astep_merge a c] at hst
        have ht : t = volley ⟨a + 2, c + 2, 2⟩ := (Option.some.inj hst).symm
        have hm1 : 1 ≤ (volley ⟨a + 2, c + 2, 2⟩).m :=
          volley_m_pos (show 1 ≤ (⟨a + 2, c + 2, 2⟩ : AState).m from by
            show 1 ≤ c + 2; omega)
        have hL : margin ⟨a, 1, c⟩ = a - 1 := by
          show (if (⟨a, 1, c⟩ : AState).m = 0 then 0
                else (⟨a, 1, c⟩ : AState).a - 1) = a - 1
          rw [if_neg (show ¬ (⟨a, 1, c⟩ : AState).m = 0 from by
            show ¬ (1 : Nat) = 0; omega)]
        have hR : margin t = a + 2 - 1 := by
          rw [ht]
          show (if (volley ⟨a + 2, c + 2, 2⟩).m = 0 then 0
                else (volley ⟨a + 2, c + 2, 2⟩).a - 1) = a + 2 - 1
          rw [if_neg (by omega), volley_a']
        rw [hL, hR]
        omega
      · by_cases h2 : m = 2
        · subst h2
          by_cases ha : 2 ≤ a
          · rw [astep_drop_alive c ha] at hst
            have ht : t = volley ⟨a - 1, c + 3, 2⟩ :=
              (Option.some.inj hst).symm
            have hm1 : 1 ≤ (volley ⟨a - 1, c + 3, 2⟩).m :=
              volley_m_pos (show 1 ≤ (⟨a - 1, c + 3, 2⟩ : AState).m from by
                show 1 ≤ c + 3; omega)
            have hL : margin ⟨a, 2, c⟩ = a - 1 := by
              show (if (⟨a, 2, c⟩ : AState).m = 0 then 0
                    else (⟨a, 2, c⟩ : AState).a - 1) = a - 1
              rw [if_neg (show ¬ (⟨a, 2, c⟩ : AState).m = 0 from by
                show ¬ (2 : Nat) = 0; omega)]
            have hR : margin t = a - 1 - 1 := by
              rw [ht]
              show (if (volley ⟨a - 1, c + 3, 2⟩).m = 0 then 0
                    else (volley ⟨a - 1, c + 3, 2⟩).a - 1) = a - 1 - 1
              rw [if_neg (by omega), volley_a']
            rw [hL, hR]
            omega
          · rw [astep_drop_dead c (by omega)] at hst
            exact absurd hst (by simp)
        · have hdead : astep ⟨a, m, c⟩ = none :=
            (astep_eq_none_iff ⟨a, m, c⟩).mpr (Or.inl (show m = 0 by omega))
          rw [hdead] at hst
          exact absurd hst (by simp)
  · intro s h
    obtain ⟨a, m, c⟩ := s
    rw [show estep ⟨a, m, c⟩
          = (match astep ⟨a, m, c⟩ with
             | none => none
             | some u => some (volley u))
        from rfl] at h
    cases hat : astep ⟨a, m, c⟩ with
    | some u => rw [hat] at h; exact absurd h (by simp)
    | none =>
        have hd := (astep_eq_none_iff ⟨a, m, c⟩).mp hat
        show (if (⟨a, m, c⟩ : AState).m = 0 then 0
              else (⟨a, m, c⟩ : AState).a - 1) = 0
        rcases hd with h0 | ⟨h2, ha⟩
        · rw [if_pos h0]
        · have h2' : m = 2 := h2
          have ha' : a ≤ 1 := ha
          rw [if_neg (show ¬ (⟨a, m, c⟩ : AState).m = 0 from by
            show ¬ m = 0; omega)]
          show a - 1 = 0
          omega

/-- The Forge orbit over `estep` is the incision event orbit. -/
theorem orbit_eq_eorbit :
    ∀ k, orbit estep (volley ⟨2, 7, 2⟩) k = eorbit k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [orbit, eorbit]
      rw [ih]
      cases eorbit k <;> rfl

/-- **Antihydra's skip windows, re-derived generically**: the statement of
`FlyingDragon.halt_localized`, as an instance of the Forge margin
theorem. -/
theorem halt_localized (k j : Nat) (s : AState) (h : eorbit k = some s)
    (hm0 : s.m ≠ 0) (hj : j < s.a - 1) : eorbit (k + j) ≠ none := by
  rw [← orbit_eq_eorbit]
  refine margin_halt_localized estep (volley ⟨2, 7, 2⟩) margin margin_rules
    k j s ?_ ?_
  · rw [orbit_eq_eorbit]
    exact h
  · show j < if s.m = 0 then 0 else s.a - 1
    rw [if_neg hm0]
    exact hj

end AntihydraDemo

end QIG.Forge

#print axioms QIG.Forge.margin_halt_localized
#print axioms QIG.Forge.margin_death_bound
#print axioms QIG.Forge.AntihydraDemo.halt_localized
