import BusyBeaverCore.AntihydraRawTM

/-!
# Zipper-tape bisimulation (plan 1, task 4)

The Rocq (Coq-BB5) tradition models the tape as a head-centred zipper —
`left list × current cell × right list`, blanks beyond the lists — while
busy-beaver-core uses a total function `Int → Bool` with an absolute head.
This module proves the two semantics are step-for-step equivalent for the
Antihydra table: a `Matches` relation ties a zipper configuration to a
functional one, one machine step preserves it (`step_bisim`), `n` steps
preserve it (`stepN_bisim`), halting transfers (`halts_bisim`), and the
blank starts match — so

`zipper_halts_iff : ZHalts zBlank ↔ RawHalts blankStart`.

This upgrades Rocq parity from a correspondence document to a theorem:
any argument about the zipper machine is an argument about ours.
Core-only; axioms `[propext, Quot.sound]`.
-/

namespace QIG.AntihydraRawTM

/-- A Rocq-style zipper configuration: the tape as
`…left₁ left₀ [cur] right₀ right₁…`, blanks beyond the lists. -/
structure ZConfig where
  state : State
  left : List Bool
  cur : Bool
  right : List Bool

/-- One zipper step: consult the table on `cur`, write, then shift the
zipper in the head's direction (the vacated cell is pushed onto one side,
the next cell popped — blank if its list is exhausted). -/
def zstep (z : ZConfig) : Option ZConfig :=
  match instr z.state z.cur with
  | none => none
  | some ins =>
      match ins.dir with
      | .R => some ⟨ins.next, ins.write :: z.left,
                    z.right.getD 0 false, z.right.tail⟩
      | .L => some ⟨ins.next, z.left.tail,
                    z.left.getD 0 false, ins.write :: z.right⟩

def zstepN : Nat → ZConfig → Option ZConfig
  | 0, z => some z
  | n + 1, z =>
      match zstep z with
      | none => none
      | some z' => zstepN n z'

def ZHalts (z : ZConfig) : Prop := ∃ n, zstepN n z = none

/-- The blank zipper start. -/
def zBlank : ZConfig := ⟨State.A, [], false, []⟩

/-- A zipper configuration matches a functional one when every cell agrees:
the current cell, and both half-tapes read off by offset (out-of-list
offsets are blank, which `List.getD … false` encodes). -/
def Matches (z : ZConfig) (c : Config) : Prop :=
  z.state = c.state ∧
  c.tape c.head = z.cur ∧
  (∀ i : Nat, c.tape (c.head - 1 - i) = z.left.getD i false) ∧
  (∀ i : Nat, c.tape (c.head + 1 + i) = z.right.getD i false)

theorem tail_getD (l : List Bool) (i : Nat) :
    l.tail.getD i false = l.getD (i + 1) false := by
  cases l <;> rfl

/-- One step preserves `Matches`; halts coincide. -/
theorem step_bisim {z : ZConfig} {c : Config} (h : Matches z c) :
    (zstep z = none ∧ step c = none) ∨
    (∃ z' c', zstep z = some z' ∧ step c = some c' ∧ Matches z' c') := by
  obtain ⟨hs, hcur, hleft, hright⟩ := h
  have hinsc : instr c.state (c.tape c.head) = instr z.state z.cur := by
    rw [hcur, hs]
  cases hins : instr z.state z.cur with
  | none =>
      left
      refine ⟨?_, ?_⟩
      · simp [zstep, hins]
      · simp [step, hinsc, hins]
  | some ins =>
      right
      have hstepc : step c
          = some ⟨ins.next, move c.head ins.dir,
                  writeAt c.tape c.head ins.write⟩ := by
        simp [step, hinsc, hins]
      cases hdir : ins.dir with
      | R =>
          refine ⟨⟨ins.next, ins.write :: z.left,
                   z.right.getD 0 false, z.right.tail⟩,
                  ⟨ins.next, c.head + 1, writeAt c.tape c.head ins.write⟩,
                  ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [zstep, hins, hdir]
          · rw [hstepc, hdir]
            rfl
          · rfl
          · -- current cell: one step right reads the first right cell
            show writeAt c.tape c.head ins.write (c.head + 1)
                = z.right.getD 0 false
            rw [writeAt_other _ _ _ _ (by omega)]
            have := hright 0
            rwa [show c.head + 1 + ((0 : Nat) : Int) = c.head + 1 by omega]
              at this
          · -- left list gains the written cell
            intro i
            cases i with
            | zero =>
                show writeAt c.tape c.head ins.write (c.head + 1 - 1 - 0)
                    = ins.write
                rw [show c.head + 1 - 1 - (0 : Int) = c.head by omega]
                exact writeAt_same _ _ _
            | succ i =>
                show writeAt c.tape c.head ins.write (c.head + 1 - 1 - (i + 1 : Nat))
                    = z.left.getD i false
                rw [writeAt_other _ _ _ _ (by omega),
                    show c.head + 1 - 1 - ((i + 1 : Nat) : Int)
                      = c.head - 1 - i by omega]
                exact hleft i
          · -- right list loses its first cell
            intro i
            show writeAt c.tape c.head ins.write (c.head + 1 + 1 + i)
                = z.right.tail.getD i false
            rw [writeAt_other _ _ _ _ (by omega), tail_getD,
                show c.head + 1 + 1 + (i : Int)
                  = c.head + 1 + ((i + 1 : Nat) : Int) by omega]
            exact hright (i + 1)
      | L =>
          refine ⟨⟨ins.next, z.left.tail,
                   z.left.getD 0 false, ins.write :: z.right⟩,
                  ⟨ins.next, c.head - 1, writeAt c.tape c.head ins.write⟩,
                  ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [zstep, hins, hdir]
          · rw [hstepc, hdir]
            rfl
          · rfl
          · show writeAt c.tape c.head ins.write (c.head - 1)
                = z.left.getD 0 false
            rw [writeAt_other _ _ _ _ (by omega)]
            have := hleft 0
            rwa [show c.head - 1 - ((0 : Nat) : Int) = c.head - 1 by omega]
              at this
          · intro i
            show writeAt c.tape c.head ins.write (c.head - 1 - 1 - i)
                = z.left.tail.getD i false
            rw [writeAt_other _ _ _ _ (by omega), tail_getD,
                show c.head - 1 - 1 - (i : Int)
                  = c.head - 1 - ((i + 1 : Nat) : Int) by omega]
            exact hleft (i + 1)
          · intro i
            cases i with
            | zero =>
                show writeAt c.tape c.head ins.write (c.head - 1 + 1 + 0)
                    = ins.write
                rw [show c.head - 1 + 1 + (0 : Int) = c.head by omega]
                exact writeAt_same _ _ _
            | succ i =>
                show writeAt c.tape c.head ins.write (c.head - 1 + 1 + (i + 1 : Nat))
                    = z.right.getD i false
                rw [writeAt_other _ _ _ _ (by omega),
                    show c.head - 1 + 1 + ((i + 1 : Nat) : Int)
                      = c.head + 1 + (i : Int) by omega]
                exact hright i

/-- `n` steps preserve `Matches`; the two runs live and die together. -/
theorem stepN_bisim : ∀ (n : Nat) {z : ZConfig} {c : Config}, Matches z c →
    (zstepN n z = none ∧ stepN n c = none) ∨
    (∃ z' c', zstepN n z = some z' ∧ stepN n c = some c' ∧ Matches z' c') := by
  intro n
  induction n with
  | zero => intro z c h; exact Or.inr ⟨z, c, rfl, rfl, h⟩
  | succ n ih =>
      intro z c h
      rcases step_bisim h with ⟨hz, hc⟩ | ⟨z1, c1, hz, hc, h1⟩
      · left
        exact ⟨by simp [zstepN, hz], by simp [stepN, hc]⟩
      · have hzn : zstepN (n + 1) z = zstepN n z1 := by
          simp [zstepN, hz]
        have hcn : stepN (n + 1) c = stepN n c1 := by
          simp [stepN, hc]
        rcases ih h1 with ⟨hz1, hc1⟩ | ⟨z2, c2, hz2, hc2, h2⟩
        · exact Or.inl ⟨by rw [hzn]; exact hz1, by rw [hcn]; exact hc1⟩
        · exact Or.inr ⟨z2, c2, by rw [hzn]; exact hz2,
                        by rw [hcn]; exact hc2, h2⟩

/-- Halting transfers across the bisimulation. -/
theorem halts_bisim {z : ZConfig} {c : Config} (h : Matches z c) :
    ZHalts z ↔ RawHalts c := by
  constructor
  · intro ⟨n, hn⟩
    rcases stepN_bisim n h with ⟨_, hc⟩ | ⟨z', _, hz', _, _⟩
    · exact ⟨n, hc⟩
    · rw [hz'] at hn; exact absurd hn (by simp)
  · intro ⟨n, hn⟩
    rcases stepN_bisim n h with ⟨hz, _⟩ | ⟨_, c', _, hc', _⟩
    · exact ⟨n, hz⟩
    · rw [hc'] at hn; exact absurd hn (by simp)

/-- The blank starts match cell-for-cell. -/
theorem zBlank_matches : Matches zBlank blankStart :=
  ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-- **Rocq parity as a theorem**: the zipper machine halts from blank iff
the functional machine does. -/
theorem zipper_halts_iff : ZHalts zBlank ↔ RawHalts blankStart :=
  halts_bisim zBlank_matches

end QIG.AntihydraRawTM

#print axioms QIG.AntihydraRawTM.step_bisim
#print axioms QIG.AntihydraRawTM.zipper_halts_iff
