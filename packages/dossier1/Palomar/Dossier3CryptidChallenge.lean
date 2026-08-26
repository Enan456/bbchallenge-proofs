/-!
# Challenge: dossier-3 does not halt, conditional on its orbit conjecture

**Machine.**  Dossier-3 is the 6-state 2-symbol Turing machine
`1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE` (bbchallenge standard text format), one of the BB(6)
holdouts.  This file defines its semantics from scratch and states:

**Theorem** (`dossier3_nonhalting`).  If the five-integer abstract
orbit (`SafeMetaOrbit`) never leaves its guarded region, the machine
never halts from the all-zero tape.

The abstract orbit is a deterministic guard-dispatched affine map on
shapes `(three?, l, h1, h2, r)`; the accompanying solution transports a
certified development in which every raw step of the machine — a
2044-step concrete startup and an eternity of seven certified episode
types — is accounted for by kernel-checked theorems.  Nothing here
decides the machine: the conjecture itself remains open, and its
excluded parameter bands are provably lethal, so it is exactly the
machine's halting problem.

This challenge file is self-contained over Lean core; the proof lives
in the accompanying solution module.
-/

namespace Dossier3CryptidChallenge

/-- Machine control states. -/
inductive St
  | A | B | C | D | E | F

/-- Head movement directions. -/
inductive Dir
  | L | R

/-- One machine instruction: successor state, symbol written, head
direction. -/
structure Instr where
  next : St
  write : Bool
  dir : Dir

/-- The transition table of `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE`.  `none` marks the unique undefined
transition: reaching it is the only way the machine can halt. -/
def instr : St → Bool → Option Instr
  | .A, false => some ⟨.B, true, .R⟩
  | .A, true => some ⟨.B, true, .R⟩
  | .B, false => some ⟨.C, true, .L⟩
  | .B, true => some ⟨.E, false, .R⟩
  | .C, false => none
  | .C, true => some ⟨.D, true, .L⟩
  | .D, false => some ⟨.A, false, .R⟩
  | .D, true => some ⟨.B, true, .L⟩
  | .E, false => some ⟨.A, true, .R⟩
  | .E, true => some ⟨.F, true, .L⟩
  | .F, false => some ⟨.E, false, .L⟩
  | .F, true => some ⟨.E, true, .L⟩

/-- A machine configuration: control state, head position, and the two-way
infinite binary tape as a total function. -/
structure Config where
  state : St
  head : Int
  tape : Int → Bool

/-- One raw machine step; `none` means the undefined transition was reached
(the machine halts). -/
def step (c : Config) : Option Config :=
  match instr c.state (c.tape c.head) with
  | none => none
  | some i =>
      some ⟨i.next,
        (match i.dir with | .L => c.head - 1 | .R => c.head + 1),
        fun x => if x = c.head then i.write else c.tape x⟩

/-- `n`-fold iteration of `step`. -/
def stepN : Nat → Config → Option Config
  | 0, c => some c
  | n + 1, c =>
      match step c with
      | none => none
      | some c' => stepN n c'

/-- The start configuration: state `A`, head at the origin, all-zero
tape. -/
def blankStart : Config := ⟨.A, 0, fun _ => false⟩

/-- The machine halts (from the blank start) iff some finite iterate
reaches the undefined transition. -/
def Halts : Prop := ∃ n, stepN n blankStart = none

/-- Abstract spawn-entry state: `three` marks the 3-hole tape family;
`l` and `r` are the field boundaries, `h1` and `h2` the mobile holes. -/
structure MetaState where
  three : Bool
  l : Int
  h1 : Int
  h2 : Int
  r : Int

/-- One abstract step: the guard-dispatched affine shape map.  `none`
is the fail-closed boundary of the certified region. -/
def metaStep : MetaState → Option MetaState
  | ⟨true, l, h1, h2, r⟩ =>
      if h1 ≤ l ∧ h2 ≤ h1 - 4 ∧ r ≤ h2 - 6 ∧
          (h2 - r) % 2 = 0 ∧ (h1 - h2) % 2 = 0 then
        some ⟨false, l, h1 - 6, h2 - 4, r - 1⟩
      else if h1 ≤ l ∧ h2 = h1 - 2 ∧ r ≤ h2 - 7 ∧ (h2 - r) % 2 = 0 then
        some ⟨false, l, h1 - 9, r - 1, r - 2⟩
      else none
  | ⟨false, l, h1, h2, r⟩ =>
      if h2 = r + 1 then
        if h1 ≤ l ∧ r + 4 ≤ h1 then
          some ⟨false, l, h1, r + 2, r - 1⟩
        else none
      else if h2 = r + 3 then
        if (h1 - r) % 2 = 1 then
          if h1 ≤ l ∧ r ≤ h1 - 7 then
            some ⟨false, l, h1 - 6, r - 1, r - 2⟩
          else none
        else if (l - h1) % 2 = 1 then
          if h1 ≤ l - 3 ∧ r ≤ h1 - 6 then
            some ⟨false, l + 1, l - 5, h1 - 4, r - 1⟩
          else none
        else
          if h1 ≤ l - 5 ∧ r ≤ h1 - 6 then
            some ⟨false, l + 3, l - 6, h1 - 4, r - 1⟩
          else none
      else
        if h1 ≤ l ∧ h2 ≤ h1 - 1 ∧ r + 4 ≤ h2 then
          some ⟨true, l, h1, h2, r - 1⟩
        else none

/-- The startup's landing state, reached from the blank tape after
2044 certified machine steps. -/
def s0 : MetaState := ⟨false, 17, 11, -39, -40⟩

/-- The abstract orbit from the anchor. -/
def metaOrbit : Nat → Option MetaState
  | 0 => some s0
  | n + 1 =>
      match metaOrbit n with
      | none => none
      | some s => metaStep s

/-- **The safety conjecture**: the five-integer abstract orbit never
falls off the guarded region.  Validated to 10^8 abstract episodes;
the excluded parameter bands provably force the halting transition. -/
def SafeMetaOrbit : Prop := ∀ k, metaOrbit k ≠ none

/-- **Main result** (proved in the solution module).  Under the orbit
conjecture, dossier-3 never halts from the all-zero tape. -/
theorem dossier3_nonhalting (hsafe : SafeMetaOrbit) : ¬ Halts := sorry

end Dossier3CryptidChallenge
