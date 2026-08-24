/-!
# Challenge: Antihydra does not halt, conditional on the hydra conjecture

**Machine.**  Antihydra is the 6-state 2-symbol Turing machine
`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA` (bbchallenge standard text
format), a famous BB(6) "cryptid".  This file defines its semantics from
scratch — a two-way infinite binary tape, a partial transition table whose
unique undefined transition (state `F` reading `0`) is the only way to halt —
and states the result:

**Theorem** (`antihydra_nonhalting`).  If the 1-D *hydra process* never dies
(`HydraSafe`), then Antihydra never halts from the all-zero tape.

**The hydra process** iterates `b ↦ b + ⌊b/2⌋` starting from `b = 12`,
keeping a heads counter starting at `2` that gains 2 on even values and loses
1 on odd values; the process *dies* if an odd value is reached while the
counter is `≤ 1`.  `HydraSafe` says it never dies.  This is a (slightly
strengthened) form of the community's Antihydra conjecture: the standard
statement starts the hydra value at 8 (our start `12 = H(8)`, counter `2`,
is the state after one standard step) and halts the machine at counter `−1`,
i.e. dies at an odd value with counter `= 0`; the strengthening from `= 0`
to `≤ 1` is one boundary case, inherited from the tape grammar of the
underlying formalisation, and is documented in the submission metadata.

This challenge file is self-contained over Lean core; the proof lives in the
accompanying solution module.
-/

namespace AntihydraChallenge

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

/-- The Antihydra transition table
`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`.  `none` at `(F, false)` is the
unique undefined transition: reaching it is the only way the machine can
halt. -/
def instr : St → Bool → Option Instr
  | .A, false => some ⟨.B, true, .R⟩
  | .A, true => some ⟨.A, true, .R⟩
  | .B, false => some ⟨.C, false, .L⟩
  | .B, true => some ⟨.E, true, .L⟩
  | .C, false => some ⟨.D, true, .L⟩
  | .C, true => some ⟨.C, true, .L⟩
  | .D, false => some ⟨.A, true, .L⟩
  | .D, true => some ⟨.B, false, .L⟩
  | .E, false => some ⟨.F, true, .L⟩
  | .E, true => some ⟨.E, true, .R⟩
  | .F, false => none
  | .F, true => some ⟨.A, false, .R⟩

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

/-- `n`-fold iteration of `step`; `none` once the machine has halted. -/
def stepN : Nat → Config → Option Config
  | 0, c => some c
  | n + 1, c =>
      match step c with
      | none => none
      | some c' => stepN n c'

/-- The start configuration: state `A`, head at the origin, all-zero tape. -/
def blankStart : Config := ⟨.A, 0, fun _ => false⟩

/-- The machine halts (from the blank start) iff some finite iterate reaches
the undefined transition. -/
def Halts : Prop := ∃ n, stepN n blankStart = none

/-- The hydra function `H(b) = b + ⌊b/2⌋ = ⌊3b/2⌋`. -/
def hydraNext (b : Nat) : Nat := b + b / 2

/-- The hydra process: pairs `(value, heads counter)` starting from
`(12, 2)`.  Even values feed the counter `+2`; odd values cost `−1`; an odd
value with counter `≤ 1` kills the process (`none`). -/
def hydraOrbit : Nat → Option (Nat × Nat)
  | 0 => some (12, 2)
  | k + 1 =>
      match hydraOrbit k with
      | none => none
      | some (b, h) =>
          if b % 2 = 0 then some (hydraNext b, h + 2)
          else if 2 ≤ h then some (hydraNext b, h - 1)
          else none

/-- **The (strengthened) Antihydra conjecture**: the hydra process never
dies. -/
def HydraSafe : Prop := ∀ k, hydraOrbit k ≠ none

/-- **Main result.**  Under the hydra conjecture, Antihydra never halts from
the all-zero tape.

Informally: everything above this line is the complete formal meaning of
the claim — a reader who checks these 100 lines has checked the statement;
the proof lives in the solution module and is compared by Comparator. -/
theorem antihydra_nonhalting (hsafe : HydraSafe) : ¬ Halts := sorry

end AntihydraChallenge
