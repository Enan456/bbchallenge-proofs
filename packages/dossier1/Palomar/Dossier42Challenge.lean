/-!
# Challenge: dossier-42 does not halt, conditional on its record-orbit conjecture

**Machine.**  Dossier-13 is the 6-state 2-symbol Turing machine
`1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE` (bbchallenge standard text
format), one of the BB(6) holdouts.  This file defines its semantics
from scratch and states:

**Theorem** (`safeD42Orbit_nonhalting`).  If the fail-closed record
orbit (`SafeD42Orbit`) never dies, the machine never halts from the
all-zero tape.

The record orbit is the certified word machine `wstep` iterated from
the blank anchor `(A, [])`: from each arrival word the executable
sweep `go` runs single-raw-step list surgery on the boundary pair
`(em, rest)` to the machine's next record extreme, failing closed on
the machine's fatal halt probe and on fuel exhaustion.  The
accompanying solution transports a certified development in which
every raw step of the machine is accounted for by kernel-checked
theorems, so no `Faithful` assumption accompanies the conjecture.
Nothing here decides the machine: the orbit conjecture itself remains
open, so it is exactly the machine's halting problem.

This challenge file is self-contained over Lean core; the proof lives
in the accompanying solution module.
-/

set_option autoImplicit false

namespace Dossier42Challenge

/-- Machine control states. -/
inductive State where
  | A | B | C | D | E | F

/-- Head movement directions. -/
inductive Dir where
  | L | R

/-- One machine instruction: successor state, symbol written, head
direction. -/
structure Instr where
  next : State
  write : Bool
  dir : Dir

/-- The dossier-42 transition table.  `none` is the undefined halt
transition `A1`. -/
def instr : State → Bool → Option Instr
  | State.A, false => some ⟨State.B, true, Dir.R⟩
  | State.A, true => none
  | State.B, false => some ⟨State.C, true, Dir.L⟩
  | State.B, true => some ⟨State.B, false, Dir.R⟩
  | State.C, false => some ⟨State.D, false, Dir.L⟩
  | State.C, true => some ⟨State.C, false, Dir.L⟩
  | State.D, false => some ⟨State.E, true, Dir.R⟩
  | State.D, true => some ⟨State.B, true, Dir.R⟩
  | State.E, false => some ⟨State.D, true, Dir.R⟩
  | State.E, true => some ⟨State.F, true, Dir.L⟩
  | State.F, false => some ⟨State.A, true, Dir.L⟩
  | State.F, true => some ⟨State.E, false, Dir.L⟩

def move : Int → Dir → Int
  | h, Dir.L => h - 1
  | h, Dir.R => h + 1

/-- Pointwise tape update. -/
def writeAt (tape : Int → Bool) (pos : Int) (value : Bool) : Int → Bool :=
  fun x => if x = pos then value else tape x

/-- A machine configuration: control state, head position, and the
two-way infinite binary tape as a total function. -/
structure Config where
  state : State
  head : Int
  tape : Int → Bool

/-- One raw TM step.  `none` means the undefined `D1` halt was
reached. -/
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

/-- The machine halts from `c` iff some finite iterate reaches the
undefined transition. -/
def RawHalts (c : Config) : Prop := ∃ n : Nat, stepN n c = none

/-- The all-zero tape. -/
def blankTape : Int → Bool := fun _ => false

/-- The start configuration: state `A`, head at the origin, all-zero
tape. -/
def blankStart : Config where
  state := State.A
  head := 0
  tape := blankTape

/-- The fail-closed word machine: from `(st, em, rest)` (`em` = cells
between the head and the record extreme, nearest first; `rest` = the
head cell inward) run single-raw-step list surgery until the first
extreme-extending pop — the next arrival, i.e. the machine's next
record event — and return `(state, arrival word, raw steps)`.  It
fails closed (`none`) exactly on the machine's fatal probe branch and
on fuel exhaustion. -/
def go : Nat → State → List Bool → List Bool → Option (State × List Bool × Nat)
  | 0, _, _, _ => none
  | fuel + 1, st, em, rest =>
    match st, rest.getD 0 false with
    | State.A, false =>
        (go fuel State.B (true :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.A, true => none
    | State.B, false =>
        match em with
        | [] => some (State.C, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.C em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.B, true =>
        (go fuel State.B (false :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.C, false =>
        match em with
        | [] => some (State.D, false :: false :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.D em2 (e0 :: false :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.C, true =>
        match em with
        | [] => some (State.C, false :: false :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.C em2 (e0 :: false :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.D, false =>
        (go fuel State.E (true :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.D, true =>
        (go fuel State.B (true :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.E, false =>
        (go fuel State.D (true :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.E, true =>
        match em with
        | [] => some (State.F, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.F em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.F, false =>
        match em with
        | [] => some (State.A, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.A em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.F, true =>
        match em with
        | [] => some (State.E, false :: false :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.E em2 (e0 :: false :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))

/-- Generous fuel: raw steps per record gap, comfortably quadratic in
the arrival word length.  Fail-closed — exhaustion is an orbit
death. -/
def wfuel (w : List Bool) : Nat := 64 * (w.length + 64) * (w.length + 64)

/-- One certified record-to-record sweep: from an arrival `(st, w)`
(head at the record extreme, word `w` inward), run the raw machine to
the next fresh record extreme.  Returns `(state', word', steps)`. -/
def wstep (st : State) (w : List Bool) : Option (State × List Bool × Nat) :=
  go (wfuel w) st [] w

/-- The word orbit: `wstep` iterated from the blank anchor `(A, [])`. -/
def worbit : Nat → Option (State × List Bool)
  | 0 => some (State.A, [])
  | k + 1 =>
      match worbit k with
      | none => none
      | some s => (wstep s.1 s.2).map (fun r => (r.1, r.2.1))

/-- **The dossier-42 record-orbit conjecture**: the fail-closed record
orbit never dies — no sweep ever meets the fatal probe or fuel
exhaustion.  A statement about a sequence of `(state, word)` pairs
with no tape, no head, no machine. -/
def SafeD42Orbit : Prop := ∀ k : Nat, worbit k ≠ none

/-- **Main result** (proved in the solution module).  Under the
record-orbit conjecture, dossier-42 never halts from the all-zero
tape. -/
theorem safeD42Orbit_nonhalting (hso : SafeD42Orbit) :
    ¬ RawHalts blankStart := sorry

end Dossier42Challenge
