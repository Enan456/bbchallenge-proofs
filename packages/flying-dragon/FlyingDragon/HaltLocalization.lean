import Bridge.Incision
import FlyingDragon.HeadsAccounting

/-!
# Projected-halt localization on the event orbit (flying-dragon)

The incision layer already reduced checking to boundary events; this module
localizes further: death needs a drop with counter ≤ 1, and the counter
falls by at most 1 per event, so from any event state the orbit provably
cannot die for the next `a − 1` events —

`halt_localized  : eorbit k = some s → j < s.a → eorbit (k + j) ≠ none`
`projected_death_bound : … → eorbit n = none → k + s.a ≤ n`

This is the certified skip window: a checker may advance `s.a − 1` events
with **zero death checks**, re-reading the counter only at the window's
edge.  Since the counter drifts upward (+0.5/event measured, and each
skipped event is itself an exponential raw-step volley), the windows grow
as the orbit runs — localized checking in exactly the sense the macro
emulation localized raw halting to probes.

Honest scope: this localizes death of the *abstract orbit*.  The machine
connection remains the proven one-directional reduction (orbit safety ⇒
machine never halts); no timing claim about raw machine halting is made.
Core-only; axioms `[propext, Quot.sound]`.
-/

namespace QIG.FlyingDragon

open QIG.AntihydraRawTM

/-- Structural invariant of event states: the boundary block is 1 or 2 and
the companion block is nonempty. -/
theorem eorbit_inv : ∀ (k : Nat) (s : AState), eorbit k = some s →
    (s.m = 1 ∨ s.m = 2) ∧ 1 ≤ s.c := by
  intro k
  induction k with
  | zero =>
      intro s h
      have hs : volley ⟨2, 7, 2⟩ = s := Option.some.inj h
      rw [← hs]
      exact ⟨Or.inl rfl, by decide⟩
  | succ k ih =>
      intro s h
      rw [show eorbit (k + 1)
            = (match eorbit k with
               | none => none
               | some t => estep t)
          from rfl] at h
      cases het : eorbit k with
      | none => rw [het] at h; exact absurd h (by simp)
      | some t =>
          rw [het] at h
          obtain ⟨hm, hc⟩ := ih t het
          obtain ⟨a, m, c⟩ := t
          simp only at hm hc
          change estep ⟨a, m, c⟩ = some s at h
          rw [show estep ⟨a, m, c⟩
                = (match astep ⟨a, m, c⟩ with
                   | none => none
                   | some u => some (volley u))
              from rfl] at h
          rcases hm with rfl | rfl
          · rw [astep_merge a c] at h
            have hs : volley ⟨a + 2, c + 2, 2⟩ = s := Option.some.inj h
            rw [← hs, volley_unfold (show ¬ c + 2 ≤ 2 by omega)]
            refine ⟨?_, show (1 : Nat) ≤ 2 + 3 * ((c + 2 - 1) / 2) by omega⟩
            show 2 - (c + 2) % 2 = 1 ∨ 2 - (c + 2) % 2 = 2
            by_cases hp : (c + 2) % 2 = 0
            · exact Or.inr (by omega)
            · exact Or.inl (by omega)
          · by_cases ha : 2 ≤ a
            · rw [astep_drop_alive c ha] at h
              have hs : volley ⟨a - 1, c + 3, 2⟩ = s := Option.some.inj h
              rw [← hs, volley_unfold (show ¬ c + 3 ≤ 2 by omega)]
              refine ⟨?_, show (1 : Nat) ≤ 2 + 3 * ((c + 3 - 1) / 2) by omega⟩
              show 2 - (c + 3) % 2 = 1 ∨ 2 - (c + 3) % 2 = 2
              by_cases hp : (c + 3) % 2 = 0
              · exact Or.inr (by omega)
              · exact Or.inl (by omega)
            · rw [astep_drop_dead c (by omega)] at h
              exact absurd h (by simp)

/-- Informally: *the counter is a fuse that burns one notch per drop and
never faster* — merges lengthen it, drops shorten it by exactly one, and
nothing else touches it.  So `j` events after reading the fuse at length
`a`, at least `a − j` remains, and in particular the orbit is still alive.
(This is the concrete ancestor of the forge's generic `MarginRules`
argument.) -/
theorem counter_lower_bound :
    ∀ (j k : Nat) (s : AState), eorbit k = some s → j + 1 ≤ s.a →
      ∃ t, eorbit (k + j) = some t ∧ s.a ≤ t.a + j := by
  intro j
  induction j with
  | zero =>
      intro k s h _
      exact ⟨s, by rw [Nat.add_zero]; exact h, by omega⟩
  | succ j ih =>
      intro k s h hj
      obtain ⟨t, ht, hbound⟩ := ih k s h (by omega)
      obtain ⟨hm, hc⟩ := eorbit_inv (k + j) t ht
      have hnext : eorbit (k + j + 1) = estep t := eorbit_succ ht
      obtain ⟨a, m, c⟩ := t
      simp only at hm hc hbound
      rw [show estep ⟨a, m, c⟩
            = (match astep ⟨a, m, c⟩ with
               | none => none
               | some u => some (volley u))
          from rfl] at hnext
      rcases hm with rfl | rfl
      · rw [astep_merge a c] at hnext
        refine ⟨volley ⟨a + 2, c + 2, 2⟩,
                by rw [show k + (j + 1) = k + j + 1 by omega]; exact hnext,
                ?_⟩
        rw [volley_a]
        show s.a ≤ a + 2 + (j + 1)
        omega
      · have ha : 2 ≤ a := by omega
        rw [astep_drop_alive c ha] at hnext
        refine ⟨volley ⟨a - 1, c + 3, 2⟩,
                by rw [show k + (j + 1) = k + j + 1 by omega]; exact hnext,
                ?_⟩
        rw [volley_a]
        show s.a ≤ a - 1 + (j + 1)
        omega

/-- **Projected-halt localization.**  From an event state with counter `a`,
the orbit cannot die within the next `a − 1` events — a certified skip
window needing zero death checks.

Informally: death requires the fuse to burn to nothing, and the fuse burns
at most one notch per event — so read it once and leap.  At event 20,000
the fuse is 9,919 notches long; the leaps grow as the orbit runs. -/
theorem halt_localized (k j : Nat) (s : AState) (h : eorbit k = some s)
    (hj : j < s.a) : eorbit (k + j) ≠ none := by
  obtain ⟨t, ht, _⟩ := counter_lower_bound j k s h (by omega)
  rw [ht]
  simp

/-- Equivalent bound form: any orbit death lies at least `s.a` events past
any live event state — the earliest *candidate* death index is computable
from the current counter alone. -/
theorem projected_death_bound (k n : Nat) (s : AState)
    (h : eorbit k = some s) (hdead : eorbit n = none) (hkn : k ≤ n) :
    k + s.a ≤ n := by
  by_cases hlt : n - k < s.a
  · exact absurd (by rw [show k + (n - k) = n by omega]; exact hdead)
      (halt_localized k (n - k) s h hlt)
  · omega

end QIG.FlyingDragon

#print axioms QIG.FlyingDragon.eorbit_inv
#print axioms QIG.FlyingDragon.halt_localized
#print axioms QIG.FlyingDragon.projected_death_bound
