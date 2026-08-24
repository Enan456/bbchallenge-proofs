/-!
# Challenge: a BB(6) machine does not halt, conditional on its orbit conjecture

**Machine.**  The 6-state 2-symbol Turing machine
`1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB` (bbchallenge standard text
format), an unsolved BB(6) holdout.  This file defines its semantics from
scratch — two-way infinite binary tape, partial transition table whose
unique undefined transition (state `F` reading `0`) is the only way to
halt — and states:

**Theorem** (`dossier1_nonhalting`).  If the machine's abstract chain orbit
never dies (`SafeOrbit`), the machine never halts from the all-zero tape.

**The abstract orbit** tracks the machine's record dynamics as a stack of
chain levels `L : List Nat` with an active pair `(b, c)` (or a single `top`
value between chain phases).  One abstract step decrements `b` by 2 while
feeding `c` (the workhorse rules), spawns a new level when `b = 2` (needing
`c ≥ 4`), and collapses the last level into its parent when `b = 1`.
`SafeOrbit` — the sole hypothesis — says this orbit never reaches `none`:
whenever `b` reaches 2 the companion satisfies `c ≥ 4`, and collapses always
find a level.  Every dynamical fact about the machine itself (that these
rules exactly simulate it) is proven, not assumed.

This challenge file is self-contained over Lean core; the proof lives in the
accompanying solution module.
-/

namespace Dossier1Challenge

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

/-- The transition table `1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB`.
`none` at `(F, false)` is the unique undefined transition: reaching it is
the only way the machine can halt. -/
def instr : St → Bool → Option Instr
  | .A, false => some ⟨.B, true, .R⟩
  | .A, true => some ⟨.E, false, .L⟩
  | .B, false => some ⟨.B, true, .L⟩
  | .B, true => some ⟨.C, true, .R⟩
  | .C, false => some ⟨.F, false, .R⟩
  | .C, true => some ⟨.D, false, .R⟩
  | .D, false => some ⟨.E, true, .R⟩
  | .D, true => some ⟨.A, false, .L⟩
  | .E, false => some ⟨.A, true, .L⟩
  | .E, true => some ⟨.E, true, .R⟩
  | .F, false => none
  | .F, true => some ⟨.B, false, .R⟩

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

/-- Abstract orbit states: a bare `top` value between chain phases, or a
stack of chain levels `L` with the active pair `(b, c)`. -/
inductive AState
  | top (n : Nat)
  | lvl (L : List Nat) (b : Nat) (c : Nat)

/-- Increase the last level by 2. -/
def lastInc2 : List Nat → List Nat
  | [] => []
  | [a] => [a + 2]
  | a :: rest => a :: lastInc2 rest

/-- Split a list at its last element. -/
def unsnoc : List Nat → Option (List Nat × Nat)
  | [] => none
  | [a] => some ([], a)
  | x :: y :: rest =>
      match unsnoc (y :: rest) with
      | none => none
      | some (L', a) => some (x :: L', a)

/-- The state a level-death produces: a `top` record when no levels
remain. -/
def collapseTarget : List Nat → Nat → AState
  | [], n => AState.top n
  | x :: xs, n => AState.lvl (x :: xs) n 1

/-- One abstract step.  `none` marks exactly the value patterns whose
absence from the orbit is the conjecture. -/
def astep : AState → Option AState
  | AState.top n =>
      if 4 ≤ n then some (AState.lvl [2] (n - 2) 2) else none
  | AState.lvl L b c =>
      match unsnoc L with
      | none => none
      | some (L₀, a) =>
          if 3 ≤ b then some (AState.lvl (lastInc2 L) (b - 2) (c + 1))
          else if b = 2 then
            (if 4 ≤ c then some (AState.lvl (lastInc2 L ++ [1]) (c - 2) 1)
             else none)
          else if b = 1 then some (collapseTarget L₀ (a + c + 4))
          else none

/-- The abstract orbit from the startup handoff. -/
def aorbit : Nat → Option AState
  | 0 => some (AState.top 5)
  | k + 1 =>
      match aorbit k with
      | none => none
      | some s => astep s

/-- **The orbit conjecture** — the sole unproven ingredient: the abstract
orbit never dies. -/
def SafeOrbit : Prop := ∀ k, aorbit k ≠ none

/-- **Main result.**  Under the orbit conjecture, the machine never halts
from the all-zero tape.

Informally: this file *is* the claim — machine, orbit, and hypothesis in
150 auditable lines; the proof arrives by transport in the solution
module. -/
theorem dossier1_nonhalting (hsafe : SafeOrbit) : ¬ Halts := sorry

end Dossier1Challenge
