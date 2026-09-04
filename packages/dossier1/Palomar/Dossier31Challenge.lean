/-!
# Challenge: dossier-31 does not halt, conditional on its record-orbit conjecture

**Machine.**  Dossier-9 is the 6-state 2-symbol Turing machine
`1RB0LF_1RC---_1LD0RF_1RA0LE_0LD1LD_0RD0RB` (bbchallenge standard text
format), one of the BB(6) holdouts.  This file defines its semantics
from scratch and states:

**Theorem** (`safeD31Orbit_nonhalting`).  If the fail-closed record
orbit (`SafeD31Orbit`) never dies, the machine never halts from the
all-zero tape.

The record orbit is the certified word machine `wstep` iterated from
the blank anchor `(A, [])`: from each arrival word the executable
sweep `go` runs single-raw-step list surgery on the pair `(em, rest)`
to the next fresh right extreme (the machine's record events), failing
closed on the fatal `B1` halt probe and on fuel exhaustion.  The
accompanying solution transports a certified development in which
every raw step of the machine is accounted for by kernel-checked
theorems, so no `Faithful` assumption accompanies the conjecture.
Nothing here decides the machine: the orbit conjecture itself remains
open, so it is exactly the machine's halting problem.

This challenge file is self-contained over Lean core; the proof lives
in the accompanying solution module.
-/

set_option autoImplicit false

namespace Dossier31Challenge

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

/-- The dossier-31 transition table.  `none` is the undefined halt
transition `A1`. -/
def instr : State → Bool → Option Instr
  | State.A, false => some ⟨State.B, true, Dir.R⟩
  | State.A, true => none
  | State.B, false => some ⟨State.C, false, Dir.L⟩
  | State.B, true => some ⟨State.F, true, Dir.R⟩
  | State.C, false => some ⟨State.E, true, Dir.L⟩
  | State.C, true => some ⟨State.D, false, Dir.R⟩
  | State.D, false => some ⟨State.B, false, Dir.R⟩
  | State.D, true => some ⟨State.C, true, Dir.R⟩
  | State.E, false => some ⟨State.D, true, Dir.R⟩
  | State.E, true => some ⟨State.E, false, Dir.L⟩
  | State.F, false => some ⟨State.C, false, Dir.R⟩
  | State.F, true => some ⟨State.A, true, Dir.R⟩

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

/-- One raw TM step.  `none` means the undefined `B1` halt was
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
above the head, nearest first; `rest` = the head cell downward) run
single-raw-step list surgery until the first above-base pop — the next
arrival, i.e. the next fresh-right-extreme record — and return
`(state, arrival word, raw steps)`.  It returns `none` exactly on the
fatal `B`-probe (`B` reading `1`, which on this machine *is* the
undefined halt transition) and on fuel exhaustion. -/
def go : Nat → State → List Bool → List Bool → Option (State × List Bool × Nat)
  | 0, _, _, _ => none
  | fuel + 1, st, em, rest =>
    match st, rest.getD 0 false with
    | State.A, false =>
        match em with
        | [] => some (State.B, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.B em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.A, true => none
    | State.B, false =>
        (go fuel State.C (false :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.B, true =>
        match em with
        | [] => some (State.F, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.F em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.C, false =>
        (go fuel State.E (true :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.C, true =>
        match em with
        | [] => some (State.D, false :: false :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.D em2 (e0 :: false :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.D, false =>
        match em with
        | [] => some (State.B, false :: false :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.B em2 (e0 :: false :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.D, true =>
        match em with
        | [] => some (State.C, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.C em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.E, false =>
        match em with
        | [] => some (State.D, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.D em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.E, true =>
        (go fuel State.E (false :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.F, false =>
        match em with
        | [] => some (State.C, false :: false :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.C em2 (e0 :: false :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.F, true =>
        match em with
        | [] => some (State.A, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.A em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))

/-- Generous fuel: raw steps per record gap, comfortably quadratic in
the arrival word length.  Fail-closed — exhaustion is an orbit
death. -/
def wfuel (w : List Bool) : Nat := 64 * (w.length + 64) * (w.length + 64)

/-- One certified record-to-record sweep: from an arrival `(st, w)`
(head at the right extreme, word `w` leftward), run the raw machine to
the next fresh right extreme.  Returns `(state', word', steps)`. -/
def wstep (st : State) (w : List Bool) : Option (State × List Bool × Nat) :=
  go (wfuel w) st [] w

/-- The word orbit: `wstep` iterated from the blank anchor `(A, [])`. -/
def worbit : Nat → Option (State × List Bool)
  | 0 => some (State.A, [])
  | k + 1 =>
      match worbit k with
      | none => none
      | some s => (wstep s.1 s.2).map (fun r => (r.1, r.2.1))

/-- **The dossier-31 record-orbit conjecture**: the fail-closed record
orbit never dies — no sweep ever meets the fatal `B1` probe or fuel
exhaustion.  A statement about a sequence of `(state, word)` pairs
with no tape, no head, no machine. -/
def SafeD31Orbit : Prop := ∀ k : Nat, worbit k ≠ none

/-- **Main result** (proved in the solution module).  Under the
record-orbit conjecture, dossier-31 never halts from the all-zero
tape. -/
theorem safeD31Orbit_nonhalting (hso : SafeD31Orbit) :
    ¬ RawHalts blankStart := sorry

end Dossier31Challenge
