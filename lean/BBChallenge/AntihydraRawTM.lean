import Lean.Elab.Tactic.Omega

/-!
# Antihydra raw Turing-machine semantics and halt localization

Bare-Lean model of the concrete BB(6) machine

`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`  (Antihydra).

Checked statements (no sorry, no extra axioms):

* `step_eq_none_iff` — the machine halts in one step exactly at the unique
  undefined transition `F0`.
* `into_F_only_from_E0` — state `F` is entered only via `E` reading `0`
  (the transition `E0 = 1LF`: write `1`, move left).
* `halt_requires_e_probe_00` — any raw halt from a non-`F` start passes
  through a reachable configuration in state `E` reading `0` whose left
  neighbour is also `0`.
* `nonhalting_of_e_probe_safe` / `blank_nonhalting_of_e_probe_safe` — the
  E-probe-safety invariant ("every 0 that state E reads has a 1 to its
  left") implies the machine never halts.

`EProbeSafe blankStart` is exactly the invariant discharged empirically by
stage753 (13/13 (rule, window) obligations `DISCHARGED_UNIFORM`; 14,109
entry events over 10^8 steps, zero unsafe landings).  Proving it from the
13 macro obligations is the remaining raw-to-macro contract, in the style
of `Dossier1RawTM` / `DvisetuRawTM`'s layered endgame.
-/

namespace QIG.AntihydraRawTM

inductive State where
  | A | B | C | D | E | F
deriving Repr, DecidableEq

inductive Dir where
  | L | R
deriving Repr, DecidableEq

structure Instr where
  next : State
  write : Bool
  dir : Dir
deriving Repr, DecidableEq

/-- The Antihydra transition table.  `none` is the undefined halt
transition. -/
def instr : State → Bool → Option Instr
  | State.A, false => some ⟨State.B, true, Dir.R⟩
  | State.A, true => some ⟨State.A, true, Dir.R⟩
  | State.B, false => some ⟨State.C, false, Dir.L⟩
  | State.B, true => some ⟨State.E, true, Dir.L⟩
  | State.C, false => some ⟨State.D, true, Dir.L⟩
  | State.C, true => some ⟨State.C, true, Dir.L⟩
  | State.D, false => some ⟨State.A, true, Dir.L⟩
  | State.D, true => some ⟨State.B, false, Dir.L⟩
  | State.E, false => some ⟨State.F, true, Dir.L⟩
  | State.E, true => some ⟨State.E, true, Dir.R⟩
  | State.F, false => none
  | State.F, true => some ⟨State.A, false, Dir.R⟩

def move : Int → Dir → Int
  | h, Dir.L => h - 1
  | h, Dir.R => h + 1

def writeAt (tape : Int → Bool) (pos : Int) (value : Bool) : Int → Bool :=
  fun x => if x = pos then value else tape x

theorem writeAt_same (tape : Int → Bool) (pos : Int) (value : Bool) :
    writeAt tape pos value pos = value := by
  simp [writeAt]

theorem writeAt_other (tape : Int → Bool) (pos x : Int) (value : Bool)
    (h : x ≠ pos) :
    writeAt tape pos value x = tape x := by
  simp [writeAt, h]

structure Config where
  state : State
  head : Int
  tape : Int → Bool

/-- One raw TM step.  `none` means the undefined `F0` halt was reached. -/
def step (c : Config) : Option Config := do
  let ins ← instr c.state (c.tape c.head)
  some {
    state := ins.next
    head := move c.head ins.dir
    tape := writeAt c.tape c.head ins.write
  }

/-- Iterate `step`, returning `none` after any halt. -/
def stepN : Nat → Config → Option Config
  | 0, c => some c
  | n + 1, c => do
      let c' ← step c
      stepN n c'

/-- The raw machine halts in one step exactly at the unique undefined
transition `F0`. -/
theorem step_eq_none_iff (c : Config) :
    step c = none ↔ c.state = State.F ∧ c.tape c.head = false := by
  cases hs : c.state <;> cases ht : c.tape c.head <;>
    simp [step, instr, hs, ht]

def RawHalts (c : Config) : Prop := ∃ n : Nat, stepN n c = none

def Reaches (c d : Config) : Prop := ∃ n : Nat, stepN n c = some d

def blankTape : Int → Bool := fun _ => false

def blankStart : Config where
  state := State.A
  head := 0
  tape := blankTape

/-- State `F` is entered only by `E` reading `0` (the transition
`E0 = 1LF`): the predecessor is in state `E` on a `0`, and the successor
sits one cell to the left with a `1` written at the probed cell. -/
theorem into_F_only_from_E0 {c c' : Config} (h : step c = some c')
    (hF : c'.state = State.F) :
    c.state = State.E ∧ c.tape c.head = false ∧
      c'.head = c.head - 1 ∧ c'.tape = writeAt c.tape c.head true := by
  cases hs : c.state <;> cases ht : c.tape c.head <;>
    simp [step, instr, hs, ht] at h
  all_goals
    first
      | exact ⟨rfl, rfl, by rw [← h]; simp [move], by rw [← h]⟩
      | (rw [← h] at hF; simp at hF)

/-- Any finite run ending in a halt contains a strictly earlier configuration
whose single step halts. -/
theorem stepN_none_last :
    ∀ (n : Nat) (c : Config), stepN n c = none →
      ∃ k : Nat, k < n ∧ ∃ d : Config, stepN k c = some d ∧ step d = none := by
  intro n
  induction n with
  | zero =>
      intro c h
      simp [stepN] at h
  | succ n ih =>
      intro c h
      cases hstep : step c with
      | none =>
          exact ⟨0, by omega, c, by simp [stepN], hstep⟩
      | some c1 =>
          have h1 : stepN n c1 = none := by
            simpa [stepN, hstep] using h
          obtain ⟨k, hk, d, hd, hstop⟩ := ih c1 h1
          exact ⟨k + 1, by omega, d, by simpa [stepN, hstep] using hd, hstop⟩

/-- A successful `k+1`-step run has an immediate predecessor of its endpoint. -/
theorem stepN_some_pred :
    ∀ (k : Nat) (c d : Config), stepN (k + 1) c = some d →
      ∃ e : Config, stepN k c = some e ∧ step e = some d := by
  intro k
  induction k with
  | zero =>
      intro c d h
      cases hstep : step c with
      | none => simp [stepN, hstep] at h
      | some c1 =>
          have : c1 = d := by simpa [stepN, hstep] using h
          exact ⟨c, by simp [stepN], by rw [hstep, this]⟩
  | succ k ih =>
      intro c d h
      cases hstep : step c with
      | none => simp [stepN, hstep] at h
      | some c1 =>
          have h1 : stepN (k + 1) c1 = some d := by
            simpa [stepN, hstep] using h
          obtain ⟨e, he, hlast⟩ := ih c1 d h1
          exact ⟨e, by simpa [stepN, hstep] using he, hlast⟩

/-- Halt localization: from any non-`F` start, a raw halt forces a reachable
configuration where `E` reads a `0` whose left neighbour is also `0`. -/
theorem halt_requires_e_probe_00 {c : Config} (hne : c.state ≠ State.F)
    (hh : RawHalts c) :
    ∃ d : Config, Reaches c d ∧ d.state = State.E ∧
      d.tape d.head = false ∧ d.tape (d.head - 1) = false := by
  obtain ⟨n, hn⟩ := hh
  obtain ⟨k, _, d0, hd0, hstop⟩ := stepN_none_last n c hn
  have hF := (step_eq_none_iff d0).mp hstop
  cases k with
  | zero =>
      have hcd : c = d0 := by simpa [stepN] using hd0
      exact absurd (hcd ▸ hF.1) hne
  | succ k' =>
      obtain ⟨e, he, hstepe⟩ := stepN_some_pred k' c d0 hd0
      obtain ⟨hE, h0, hhead, htape⟩ := into_F_only_from_E0 hstepe hF.1
      refine ⟨e, ⟨k', he⟩, hE, h0, ?_⟩
      have hread : d0.tape d0.head = false := hF.2
      rw [htape, hhead] at hread
      rwa [writeAt_other e.tape e.head (e.head - 1) true (by omega)] at hread

/-- The E-probe-safety invariant: every `0` that state `E` reads in any
reachable configuration has a `1` immediately to its left.  This is exactly
the invariant discharged empirically by stage753. -/
def EProbeSafe (c : Config) : Prop :=
  ∀ d : Config, Reaches c d → d.state = State.E → d.tape d.head = false →
    d.tape (d.head - 1) = true

/-- E-probe safety implies the machine never halts. -/
theorem nonhalting_of_e_probe_safe {c : Config} (hne : c.state ≠ State.F)
    (hsafe : EProbeSafe c) : ¬ RawHalts c := by
  intro hh
  obtain ⟨d, hreach, hE, h0, h00⟩ := halt_requires_e_probe_00 hne hh
  have h1 := hsafe d hreach hE h0
  rw [h1] at h00
  exact Bool.noConfusion h00

/-- Specialization to the blank start: the remaining raw-to-macro contract is
exactly `EProbeSafe blankStart`. -/
theorem blank_nonhalting_of_e_probe_safe
    (hsafe : EProbeSafe blankStart) : ¬ RawHalts blankStart := by
  have hne : blankStart.state ≠ State.F := by
    simp [blankStart]
  exact nonhalting_of_e_probe_safe hne hsafe

/-!
## Sweep lemmas — the atoms of the raw-to-macro rule lemmas

Antihydra's three self-looping transitions (`A1 = 1RA`, `C1 = 1LC`,
`E1 = 1RE`) each rewrite `1` over `1`, so the tape is literally unchanged
and a head crossing a block of `n` ones is a clean induction.  Every
stage753 macro-rule micro-trajectory decomposes into these sweeps plus a
bounded number of boundary steps.
-/

theorem writeAt_self (tape : Int → Bool) (pos : Int) {value : Bool}
    (h : tape pos = value) : writeAt tape pos value = tape := by
  funext x
  by_cases hx : x = pos
  · subst hx; simp [writeAt, h]
  · simp [writeAt, hx]

theorem step_A_on_one {c : Config} (hs : c.state = State.A)
    (ht : c.tape c.head = true) :
    step c = some ⟨State.A, c.head + 1, c.tape⟩ := by
  have hw := writeAt_self c.tape c.head ht
  simp [step, instr, hs, ht, move, hw]

theorem step_C_on_one {c : Config} (hs : c.state = State.C)
    (ht : c.tape c.head = true) :
    step c = some ⟨State.C, c.head - 1, c.tape⟩ := by
  have hw := writeAt_self c.tape c.head ht
  simp [step, instr, hs, ht, move, hw]

theorem step_E_on_one {c : Config} (hs : c.state = State.E)
    (ht : c.tape c.head = true) :
    step c = some ⟨State.E, c.head + 1, c.tape⟩ := by
  have hw := writeAt_self c.tape c.head ht
  simp [step, instr, hs, ht, move, hw]

/-- State `E` sweeps right across `n` ones without touching the tape. -/
theorem sweep_E :
    ∀ (n : Nat) (c : Config), c.state = State.E →
      (∀ i : Nat, i < n → c.tape (c.head + i) = true) →
      stepN n c = some ⟨State.E, c.head + n, c.tape⟩ := by
  intro n
  induction n with
  | zero =>
      intro c hs _
      obtain ⟨s, h, t⟩ := c
      simp_all [stepN]
  | succ n ih =>
      intro c hs hones
      have h0 : c.tape c.head = true := by
        simpa using hones 0 (Nat.succ_pos n)
      have hstep := step_E_on_one hs h0
      have hnext : stepN n ⟨State.E, c.head + 1, c.tape⟩ =
          some ⟨State.E, c.head + 1 + (n : Int), c.tape⟩ :=
        ih ⟨State.E, c.head + 1, c.tape⟩ rfl
          (fun i hi => by
            have h := hones (i + 1) (by omega)
            have heq : c.head + 1 + (i : Int) = c.head + ((i + 1 : Nat) : Int) := by
              omega
            rw [heq]; exact h)
      have harith : c.head + 1 + (n : Int) = c.head + ((n + 1 : Nat) : Int) := by
        omega
      rw [show stepN (n + 1) c = (step c).bind (stepN n) from rfl, hstep]
      rw [show ((some ⟨State.E, c.head + 1, c.tape⟩ : Option Config).bind (stepN n))
            = stepN n ⟨State.E, c.head + 1, c.tape⟩ from rfl]
      rw [hnext, harith]

/-- State `A` sweeps right across `n` ones without touching the tape. -/
theorem sweep_A :
    ∀ (n : Nat) (c : Config), c.state = State.A →
      (∀ i : Nat, i < n → c.tape (c.head + i) = true) →
      stepN n c = some ⟨State.A, c.head + n, c.tape⟩ := by
  intro n
  induction n with
  | zero =>
      intro c hs _
      obtain ⟨s, h, t⟩ := c
      simp_all [stepN]
  | succ n ih =>
      intro c hs hones
      have h0 : c.tape c.head = true := by
        simpa using hones 0 (Nat.succ_pos n)
      have hstep := step_A_on_one hs h0
      have hnext : stepN n ⟨State.A, c.head + 1, c.tape⟩ =
          some ⟨State.A, c.head + 1 + (n : Int), c.tape⟩ :=
        ih ⟨State.A, c.head + 1, c.tape⟩ rfl
          (fun i hi => by
            have h := hones (i + 1) (by omega)
            have heq : c.head + 1 + (i : Int) = c.head + ((i + 1 : Nat) : Int) := by
              omega
            rw [heq]; exact h)
      have harith : c.head + 1 + (n : Int) = c.head + ((n + 1 : Nat) : Int) := by
        omega
      rw [show stepN (n + 1) c = (step c).bind (stepN n) from rfl, hstep]
      rw [show ((some ⟨State.A, c.head + 1, c.tape⟩ : Option Config).bind (stepN n))
            = stepN n ⟨State.A, c.head + 1, c.tape⟩ from rfl]
      rw [hnext, harith]

/-- State `C` sweeps left across `n` ones without touching the tape. -/
theorem sweep_C :
    ∀ (n : Nat) (c : Config), c.state = State.C →
      (∀ i : Nat, i < n → c.tape (c.head - i) = true) →
      stepN n c = some ⟨State.C, c.head - n, c.tape⟩ := by
  intro n
  induction n with
  | zero =>
      intro c hs _
      obtain ⟨s, h, t⟩ := c
      simp_all [stepN]
  | succ n ih =>
      intro c hs hones
      have h0 : c.tape c.head = true := by
        simpa using hones 0 (Nat.succ_pos n)
      have hstep := step_C_on_one hs h0
      have hnext : stepN n ⟨State.C, c.head - 1, c.tape⟩ =
          some ⟨State.C, c.head - 1 - (n : Int), c.tape⟩ :=
        ih ⟨State.C, c.head - 1, c.tape⟩ rfl
          (fun i hi => by
            have h := hones (i + 1) (by omega)
            have heq : c.head - 1 - (i : Int) = c.head - ((i + 1 : Nat) : Int) := by
              omega
            rw [heq]; exact h)
      have harith : c.head - 1 - (n : Int) = c.head - ((n + 1 : Nat) : Int) := by
        omega
      rw [show stepN (n + 1) c = (step c).bind (stepN n) from rfl, hstep]
      rw [show ((some ⟨State.C, c.head - 1, c.tape⟩ : Option Config).bind (stepN n))
            = stepN n ⟨State.C, c.head - 1, c.tape⟩ from rfl]
      rw [hnext, harith]

end QIG.AntihydraRawTM

#print axioms QIG.AntihydraRawTM.halt_requires_e_probe_00
#print axioms QIG.AntihydraRawTM.blank_nonhalting_of_e_probe_safe
#print axioms QIG.AntihydraRawTM.sweep_E
#print axioms QIG.AntihydraRawTM.sweep_C
