import Lean.Elab.Tactic.Omega

/-!
# Dossier-3 raw semantics and halt localization

Bare-Lean model of the BB(6) holdout
`1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE` (stage757: exact orbit spec).

* halt in one step exactly at the undefined `C0`;
* state `C` is entered only via `B0` (write 1, move left);
* any raw halt passes through a reachable `B`-probe of a `00` pattern
  (the probed 0's LEFT neighbour is also 0);
* `BProbeSafe blankStart → ¬ RawHalts blankStart` — the contract the
  machine's (future) certified orbit must discharge.
-/

namespace QIG.Dossier3RawTM

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

/-- The dossier-3 transition table.  `none` at `C0` is the halt. -/
def instr : State → Bool → Option Instr
  | State.A, false => some ⟨State.B, true, Dir.R⟩
  | State.A, true => some ⟨State.B, true, Dir.R⟩
  | State.B, false => some ⟨State.C, true, Dir.L⟩
  | State.B, true => some ⟨State.E, false, Dir.R⟩
  | State.C, false => none
  | State.C, true => some ⟨State.D, true, Dir.L⟩
  | State.D, false => some ⟨State.A, false, Dir.R⟩
  | State.D, true => some ⟨State.B, true, Dir.L⟩
  | State.E, false => some ⟨State.A, true, Dir.R⟩
  | State.E, true => some ⟨State.F, true, Dir.L⟩
  | State.F, false => some ⟨State.E, false, Dir.L⟩
  | State.F, true => some ⟨State.E, true, Dir.L⟩

def move : Int → Dir → Int
  | h, Dir.L => h - 1
  | h, Dir.R => h + 1

def writeAt (tape : Int → Bool) (pos : Int) (value : Bool) : Int → Bool :=
  fun x => if x = pos then value else tape x

theorem writeAt_other (tape : Int → Bool) (pos x : Int) (value : Bool)
    (h : x ≠ pos) : writeAt tape pos value x = tape x := by
  simp [writeAt, h]

structure Config where
  state : State
  head : Int
  tape : Int → Bool

def step (c : Config) : Option Config := do
  let ins ← instr c.state (c.tape c.head)
  some {
    state := ins.next
    head := move c.head ins.dir
    tape := writeAt c.tape c.head ins.write
  }

def stepN : Nat → Config → Option Config
  | 0, c => some c
  | n + 1, c => do
      let c' ← step c
      stepN n c'

theorem step_eq_none_iff (c : Config) :
    step c = none ↔ c.state = State.C ∧ c.tape c.head = false := by
  cases hs : c.state <;> cases ht : c.tape c.head <;>
    simp [step, instr, hs, ht]

/-- Informally: halting is the existence of a finite step count after
which the iterated dynamics return `none` — the one global property this
file localizes into a two-cell tape pattern. -/
def RawHalts (c : Config) : Prop := ∃ n : Nat, stepN n c = none

def Reaches (c d : Config) : Prop := ∃ n : Nat, stepN n c = some d

def blankTape : Int → Bool := fun _ => false

def blankStart : Config where
  state := State.A
  head := 0
  tape := blankTape

/-- State `C` is entered only by `B` reading `0` (`B0 = 1LC`). -/
theorem into_C_only_from_B0 {c c' : Config} (h : step c = some c')
    (hE : c'.state = State.C) :
    c.state = State.B ∧ c.tape c.head = false ∧
      c'.head = c.head - 1 ∧ c'.tape = writeAt c.tape c.head true := by
  cases hs : c.state <;> cases ht : c.tape c.head <;>
    simp [step, instr, hs, ht] at h
  all_goals
    first
      | exact ⟨rfl, rfl, by rw [← h]; simp [move], by rw [← h]⟩
      | (rw [← h] at hE; simp at hE)

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

/-- Halt localization: any raw halt from a non-`C` start forces a reachable
`B` reading a `0` whose LEFT neighbour is also `0`. -/
theorem halt_requires_b_probe_00 {c : Config} (hne : c.state ≠ State.C)
    (hh : RawHalts c) :
    ∃ d : Config, Reaches c d ∧ d.state = State.B ∧
      d.tape d.head = false ∧ d.tape (d.head - 1) = false := by
  obtain ⟨n, hn⟩ := hh
  obtain ⟨k, _, d0, hd0, hstop⟩ := stepN_none_last n c hn
  have hE := (step_eq_none_iff d0).mp hstop
  cases k with
  | zero =>
      have hcd : c = d0 := by simpa [stepN] using hd0
      exact absurd (hcd ▸ hE.1) hne
  | succ k' =>
      obtain ⟨e, he, hstepe⟩ := stepN_some_pred k' c d0 hd0
      obtain ⟨hB, h0, hhead, htape⟩ := into_C_only_from_B0 hstepe hE.1
      refine ⟨e, ⟨k', he⟩, hB, h0, ?_⟩
      have hread : d0.tape d0.head = false := hE.2
      rw [htape, hhead] at hread
      rwa [writeAt_other e.tape e.head (e.head - 1) true (by omega)] at hread

/-- The B-probe-safety contract: every `0` that `B` reads has a `1` to its
left. -/
def BProbeSafe (c : Config) : Prop :=
  ∀ d : Config, Reaches c d → d.state = State.B → d.tape d.head = false →
    d.tape (d.head - 1) = true

theorem nonhalting_of_b_probe_safe {c : Config} (hne : c.state ≠ State.C)
    (hsafe : BProbeSafe c) : ¬ RawHalts c := by
  intro hh
  obtain ⟨d, hreach, hB, h0, h00⟩ := halt_requires_b_probe_00 hne hh
  have h1 := hsafe d hreach hB h0
  rw [h1] at h00
  exact Bool.noConfusion h00

theorem blank_nonhalting_of_b_probe_safe
    (hsafe : BProbeSafe blankStart) : ¬ RawHalts blankStart := by
  have hne : blankStart.state ≠ State.C := by
    simp [blankStart]
  exact nonhalting_of_b_probe_safe hne hsafe

end QIG.Dossier3RawTM

#print axioms QIG.Dossier3RawTM.halt_requires_b_probe_00
#print axioms QIG.Dossier3RawTM.blank_nonhalting_of_b_probe_safe
