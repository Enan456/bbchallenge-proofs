import Bridge.Incision

/-!
# The bridge to the standard Antihydra conjecture (plan 2, task 1)

The community states the Antihydra conjecture about the 1-D hydra recurrence
`b ↦ b + ⌊b/2⌋` (BusyBeaverWiki: initial value 8, heads counter `+2` on even
values, `−1` on odd values, halting when the counter dies).  Our machine
reduction `safeOrbitA_nonhalting` is stated about the `(a, m, c)` triple
orbit.  This file closes the gap with a machine-checked conjugacy:

* the incision **event process** of `Bridge.Incision` is step-for-step
  related (`RelHA`) to the 1-D hydra system via `b = m + 2·(c−2)/3 + 5`,
  with the machine's counter `a` equal to the hydra heads counter;
* deaths coincide exactly, so `HydraSafe ↔ SafeOrbitA`;
* therefore `HydraSafe → ¬ RawHalts blankStart`.

**Honest scope.**  Our hydra system starts at `b = 12 = H(8)` with heads
`= 2` (the 62-step startup absorbs the wiki's first term `8`), and it dies
at an odd value when the heads counter is `≤ 1`, where the wiki convention
dies at counter `= 0` (wiki counter `−1`).  The delta is one boundary case:
the tape grammar `Realizes` needs a non-empty counter block, so our
abstract orbit stops tracking the machine one drop earlier than the wiki's
process stops.  `HydraSafe` (die at `heads ≤ 1`) is thus (possibly strictly)
stronger than the wiki conjecture (die at `heads = 0`); closing that last
case is listed as follow-up work in the submission plan.
-/

namespace QIG.AntihydraRawTM

/-- The hydra function `H(b) = b + ⌊b/2⌋ = ⌊3b/2⌋`. -/
def hydraNext (b : Nat) : Nat := b + b / 2

/-- 1-D hydra state: current value and the heads counter. -/
structure HydraState where
  b : Nat
  heads : Nat
deriving Repr, DecidableEq

/-- One step of the community recurrence: `+2` heads on even values, `−1`
on odd values; an odd value with `heads ≤ 1` is the death our tape grammar
can no longer track. -/
def hydraStep (s : HydraState) : Option HydraState :=
  if s.b % 2 = 0 then some ⟨hydraNext s.b, s.heads + 2⟩
  else if 2 ≤ s.heads then some ⟨hydraNext s.b, s.heads - 1⟩
  else none

/-- The hydra orbit from `b = 12 = H(8)`, heads `= 2` (the values the wiki
process holds after its first term). -/
def hydraOrbit : Nat → Option HydraState
  | 0 => some ⟨12, 2⟩
  | k + 1 =>
      match hydraOrbit k with
      | none => none
      | some s => hydraStep s

/-- **The (strengthened) Antihydra conjecture**, in 1-D form. -/
def HydraSafe : Prop := ∀ k, hydraOrbit k ≠ none

theorem hydraOrbit_succ {k : Nat} {s : HydraState} (h : hydraOrbit k = some s) :
    hydraOrbit (k + 1) = hydraStep s := by
  show (match hydraOrbit k with | none => none | some s => hydraStep s) = hydraStep s
  rw [h]

/-! ## Closed forms of the event step at the boundary -/

theorem estep_merge (a c : Nat) (hc : 1 ≤ c) :
    estep ⟨a, 1, c⟩
      = some ⟨a + 2, 2 - (c + 2) % 2, 2 + 3 * ((c + 2 - 1) / 2)⟩ := by
  simp [estep, astep_merge, volley, show ¬ (c + 2 ≤ 2) by omega]

theorem estep_drop {a : Nat} (c : Nat) (ha : 2 ≤ a) :
    estep ⟨a, 2, c⟩
      = some ⟨a - 1, 2 - (c + 3) % 2, 2 + 3 * ((c + 3 - 1) / 2)⟩ := by
  simp [estep, astep_drop_alive c ha, volley, show ¬ (c + 3 ≤ 2) by omega]

theorem estep_drop_dead {a : Nat} (c : Nat) (ha : a ≤ 1) :
    estep ⟨a, 2, c⟩ = none := by
  simp [estep, astep_drop_dead c ha]

/-! ## The conjugacy -/

/-- The simulation relation between boundary states of the event process and
1-D hydra states: the hydra value is the *pre-volley* block length plus 5
(`b = m + 2·(c−2)/3 + 5`), and the hydra heads counter is the machine's
counter block `a`.  Boundary states always satisfy `c ≡ 2 (mod 3)`. -/
def RelHA (s : AState) (h : HydraState) : Prop :=
  (s.m = 1 ∨ s.m = 2) ∧ s.c % 3 = 2 ∧
    h.b = s.m + 2 * ((s.c - 2) / 3) + 5 ∧ h.heads = s.a

/-- `2 - x % 2` is `1` or `2` — proved by explicit case split so that `omega`
only ever faces atomic goals (a positive ∨-goal via omega would pull in
`Classical.choice`). -/
theorem two_sub_mod_two (x : Nat) : 2 - x % 2 = 1 ∨ 2 - x % 2 = 2 := by
  by_cases h : x % 2 = 0
  · exact Or.inr (by omega)
  · exact Or.inl (by omega)

/-- One event step preserves the relation, and deaths coincide exactly. -/
theorem relHA_step {s : AState} {h : HydraState} (hr : RelHA s h) :
    (estep s = none ∧ hydraStep h = none) ∨
    (∃ s' h', estep s = some s' ∧ hydraStep h = some h' ∧ RelHA s' h') := by
  obtain ⟨a, m, c⟩ := s
  obtain ⟨b, heads⟩ := h
  obtain ⟨hm, hc3, hb, hha⟩ := hr
  simp only at hm hc3 hb hha
  subst hb
  rw [hha]
  rcases hm with rfl | rfl
  · -- merge event: m = 1, hydra value even, heads += 2
    right
    refine ⟨⟨a + 2, 2 - (c + 2) % 2, 2 + 3 * ((c + 2 - 1) / 2)⟩,
            ⟨hydraNext (1 + 2 * ((c - 2) / 3) + 5), a + 2⟩,
            estep_merge a c (by omega), ?_, ?_⟩
    · simp [hydraStep, show (1 + 2 * ((c - 2) / 3) + 5) % 2 = 0 by omega]
    · refine ⟨two_sub_mod_two (c + 2), ?_, ?_, ?_⟩
      · show (2 + 3 * ((c + 2 - 1) / 2)) % 3 = 2
        omega
      · show hydraNext (1 + 2 * ((c - 2) / 3) + 5)
            = (2 - (c + 2) % 2) + 2 * (((2 + 3 * ((c + 2 - 1) / 2)) - 2) / 3) + 5
        simp only [hydraNext]
        omega
      · rfl
  · -- drop event: m = 2, hydra value odd, heads −= 1 (dies at heads ≤ 1)
    by_cases ha2 : 2 ≤ a
    · right
      refine ⟨⟨a - 1, 2 - (c + 3) % 2, 2 + 3 * ((c + 3 - 1) / 2)⟩,
              ⟨hydraNext (2 + 2 * ((c - 2) / 3) + 5), a - 1⟩,
              estep_drop c ha2, ?_, ?_⟩
      · simp [hydraStep, show ¬ ((2 + 2 * ((c - 2) / 3) + 5) % 2 = 0) by omega,
              ha2]
      · refine ⟨two_sub_mod_two (c + 3), ?_, ?_, ?_⟩
        · show (2 + 3 * ((c + 3 - 1) / 2)) % 3 = 2
          omega
        · show hydraNext (2 + 2 * ((c - 2) / 3) + 5)
              = (2 - (c + 3) % 2) + 2 * (((2 + 3 * ((c + 3 - 1) / 2)) - 2) / 3) + 5
          simp only [hydraNext]
          omega
        · rfl
    · left
      refine ⟨estep_drop_dead c (by omega), ?_⟩
      simp [hydraStep, show ¬ ((2 + 2 * ((c - 2) / 3) + 5) % 2 = 0) by omega,
            show ¬ 2 ≤ a by omega]

/-- The two orbits run in lock-step: related states, or both dead. -/
theorem orbit_rel (k : Nat) :
    (∃ s h, eorbit k = some s ∧ hydraOrbit k = some h ∧ RelHA s h) ∨
    (eorbit k = none ∧ hydraOrbit k = none) := by
  induction k with
  | zero =>
      left
      refine ⟨volley ⟨2, 7, 2⟩, ⟨12, 2⟩, rfl, rfl, ?_⟩
      have hv : volley ⟨2, 7, 2⟩ = ⟨2, 1, 11⟩ := rfl
      rw [hv]
      exact ⟨Or.inl rfl, rfl, rfl, rfl⟩
  | succ k ih =>
      rcases ih with ⟨s, h, hes, hhs, hr⟩ | ⟨hen, hhn⟩
      · rcases relHA_step hr with ⟨he0, hh0⟩ | ⟨s', h', hes', hhs', hr'⟩
        · right
          refine ⟨?_, ?_⟩
          · rw [eorbit_succ hes]; exact he0
          · rw [hydraOrbit_succ hhs]; exact hh0
        · left
          refine ⟨s', h', ?_, ?_, hr'⟩
          · rw [eorbit_succ hes]; exact hes'
          · rw [hydraOrbit_succ hhs]; exact hhs'
      · right
        refine ⟨?_, ?_⟩
        · show (match eorbit k with | none => none | some s => estep s) = none
          rw [hen]
        · show (match hydraOrbit k with | none => none | some s => hydraStep s)
              = none
          rw [hhn]

/-- The 1-D hydra system and the event process die together. -/
theorem hydraSafe_iff_eventSafe : HydraSafe ↔ EventSafe := by
  constructor
  · intro hh k
    rcases orbit_rel k with ⟨s, h, hes, _, _⟩ | ⟨_, hhn⟩
    · rw [hes]; simp
    · exact absurd hhn (hh k)
  · intro he k
    rcases orbit_rel k with ⟨s, h, _, hhs, _⟩ | ⟨hen, _⟩
    · rw [hhs]; simp
    · exact absurd hen (he k)

/-- **THE BRIDGE.**  The 1-D form is exactly our orbit conjecture. -/
theorem hydraSafe_iff_safeOrbitA : HydraSafe ↔ SafeOrbitA :=
  hydraSafe_iff_eventSafe.trans eventSafe_iff_safeOrbitA

/-- **Main corollary.**  If the 1-D hydra process (`b ↦ b + ⌊b/2⌋` from 12,
heads `+2` on even / `−1` on odd, never facing an odd value with heads
`≤ 1`) runs forever, Antihydra never halts from the blank tape. -/
theorem hydraSafe_nonhalting (h : HydraSafe) : ¬ RawHalts blankStart :=
  safeOrbitA_nonhalting (hydraSafe_iff_safeOrbitA.mp h)

end QIG.AntihydraRawTM

#print axioms QIG.AntihydraRawTM.relHA_step
#print axioms QIG.AntihydraRawTM.hydraSafe_iff_safeOrbitA
#print axioms QIG.AntihydraRawTM.hydraSafe_nonhalting
