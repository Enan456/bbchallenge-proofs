import Bridge.Incision

/-!
# Heads accounting along the event orbit (flying-dragon)

The atlas *measures* the heads counter drifting at +0.5/event; this module
proves the exact bookkeeping behind that curve: along the certified event
orbit, the counter equals its start (2) plus two per merge minus one per
drop —

`heads_accounting : eorbit k = some s → s.a + dropCount k = 2 + 2 * mergeCount k`

(stated additively so Nat subtraction never appears).  Corollary of the
proof structure: every event a live orbit executes is a merge or a drop —
hydra volleys never touch the counter, which is the whole reason the event
orbit is the right sampling of the dynamics.

Core-only; axioms `[propext, Quot.sound]`.
-/

namespace QIG.FlyingDragon

open QIG.AntihydraRawTM

/-- Number of merge events (`m = 1` boundary states) among the first `k`
executed events. -/
def mergeCount : Nat → Nat
  | 0 => 0
  | k + 1 =>
      mergeCount k +
        (match eorbit k with
         | some s => if s.m = 1 then 1 else 0
         | none => 0)

/-- Number of drop events (`m = 2` boundary states) among the first `k`
executed events. -/
def dropCount : Nat → Nat
  | 0 => 0
  | k + 1 =>
      dropCount k +
        (match eorbit k with
         | some s => if s.m = 2 then 1 else 0
         | none => 0)

/-- The volley never touches the counter. -/
theorem volley_a (s : AState) : (volley s).a = s.a := by
  obtain ⟨a, m, c⟩ := s
  by_cases h : m ≤ 2 <;> simp [volley, h]

/-- Every event-orbit state is a boundary state (`m ≤ 2`). -/
theorem eorbit_boundary : ∀ {k : Nat} {s : AState},
    eorbit k = some s → s.m ≤ 2 := by
  intro k s h
  cases k with
  | zero =>
      have hs : volley ⟨2, 7, 2⟩ = s := Option.some.inj h
      rw [← hs]
      exact volley_boundary_mem ⟨2, 7, 2⟩
  | succ k =>
      rw [show eorbit (k + 1)
            = (match eorbit k with
               | none => none
               | some t => estep t)
          from rfl] at h
      cases het : eorbit k with
      | none => rw [het] at h; exact absurd h (by simp)
      | some t =>
          rw [het] at h
          change estep t = some s at h
          rw [show estep t
                = (match astep t with
                   | none => none
                   | some u => some (volley u))
              from rfl] at h
          cases hat : astep t with
          | none => rw [hat] at h; exact absurd h (by simp)
          | some u =>
              rw [hat] at h
              have hs : volley u = s := Option.some.inj h
              rw [← hs]
              exact volley_boundary_mem u

/-- **Heads accounting.**  Along the event orbit, the counter carries its
complete history: start 2, +2 per merge, −1 per drop.

Informally: a conservation law.  The measured +0.5/event drift is not a
statistic about the counter — it *is* the merge/drop ratio, because
nothing else ever touches the counter (volleys are counter-frozen).
Stated additively (`a + drops = 2 + 2·merges`) so ℕ-subtraction never
muddies the ledger. -/
theorem heads_accounting :
    ∀ (k : Nat) (s : AState), eorbit k = some s →
      s.a + dropCount k = 2 + 2 * mergeCount k := by
  intro k
  induction k with
  | zero =>
      intro s h
      have hs : volley ⟨2, 7, 2⟩ = s := Option.some.inj h
      rw [← hs]
      rfl
  | succ k ih =>
      intro s' h
      rw [show eorbit (k + 1)
            = (match eorbit k with
               | none => none
               | some t => estep t)
          from rfl] at h
      cases het : eorbit k with
      | none => rw [het] at h; exact absurd h (by simp)
      | some t =>
          rw [het] at h
          have hb : t.m ≤ 2 := eorbit_boundary het
          have iht := ih t het
          have hmc : mergeCount (k + 1)
              = mergeCount k + (if t.m = 1 then 1 else 0) := by
            show mergeCount k +
                (match eorbit k with
                 | some s => if s.m = 1 then 1 else 0
                 | none => 0) = _
            rw [het]
          have hdc : dropCount (k + 1)
              = dropCount k + (if t.m = 2 then 1 else 0) := by
            show dropCount k +
                (match eorbit k with
                 | some s => if s.m = 2 then 1 else 0
                 | none => 0) = _
            rw [het]
          obtain ⟨a, m, c⟩ := t
          simp only at hb iht hmc hdc
          change estep ⟨a, m, c⟩ = some s' at h
          rw [show estep ⟨a, m, c⟩
                = (match astep ⟨a, m, c⟩ with
                   | none => none
                   | some u => some (volley u))
              from rfl] at h
          by_cases hm1 : m = 1
          · subst hm1
            rw [astep_merge a c] at h
            have hs' : volley ⟨a + 2, c + 2, 2⟩ = s' := Option.some.inj h
            rw [← hs', volley_a]
            show a + 2 + dropCount (k + 1) = 2 + 2 * mergeCount (k + 1)
            simp at hmc hdc
            omega
          · by_cases hm2 : m = 2
            · subst hm2
              by_cases ha : 2 ≤ a
              · rw [astep_drop_alive c ha] at h
                have hs' : volley ⟨a - 1, c + 3, 2⟩ = s' := Option.some.inj h
                rw [← hs', volley_a]
                show a - 1 + dropCount (k + 1) = 2 + 2 * mergeCount (k + 1)
                simp at hmc hdc
                omega
              · rw [astep_drop_dead c (by omega)] at h
                exact absurd h (by simp)
            · -- m ≤ 2, m ≠ 1, m ≠ 2 ⇒ m = 0 ⇒ dead ⇒ contradiction
              have hdead : astep ⟨a, m, c⟩ = none :=
                (astep_eq_none_iff ⟨a, m, c⟩).mpr (Or.inl (show m = 0 by omega))
              rw [hdead] at h
              exact absurd h (by simp)

/-- Every executed event is a merge or a drop — event counts partition. -/
theorem event_is_merge_or_drop {k : Nat} {s : AState}
    (h : eorbit k = some s) (halive : eorbit (k + 1) ≠ none) :
    s.m = 1 ∨ s.m = 2 := by
  have hb : s.m ≤ 2 := eorbit_boundary h
  by_cases h1 : s.m = 1
  · exact Or.inl h1
  · by_cases h2 : s.m = 2
    · exact Or.inr h2
    · exfalso
      apply halive
      rw [eorbit_succ h]
      rw [show estep s
            = (match astep s with
               | none => none
               | some u => some (volley u))
          from rfl,
          (astep_eq_none_iff s).mpr (Or.inl (by omega))]

end QIG.FlyingDragon

#print axioms QIG.FlyingDragon.heads_accounting
#print axioms QIG.FlyingDragon.event_is_merge_or_drop
