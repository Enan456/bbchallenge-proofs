/-!
# Challenge: the Dvisetu machine does not halt, conditional on its checkpoint conjecture

**Machine.**  Dvisetu (dossier-6, the divide-renewal machine) is the
6-state 2-symbol Turing machine
`1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB` (bbchallenge standard text
format), one of the BB(6) holdouts.  This file defines its semantics
from scratch and states:

**Theorem** (`safeDvisetuOrbit_nonhalting`).  Under the Dvisetu
checkpoint conjecture (`SafeCheckpointOrbit`), the machine never halts
from the all-zero tape.

The conjecture has two components: (i) the abstract checkpoint orbit
(`corbit`, a fail-closed integer dynamical system dispatching drift,
collapse, micro and renewal episodes, including an iterated-division
renewal) never dies, and (ii) the divide renewals realize their
abstract outputs on the tape (`DivideFaithful`) — the one episode of
the timed abstract map whose choreography is not certified in the
accompanying development; every other episode is played on the tape by
kernel-checked theorems.  Nothing here decides the machine: the
checkpoint conjecture itself remains open, so it is exactly the
machine's halting problem.

This challenge file is self-contained over Lean core; the proof lives
in the accompanying solution module.
-/

set_option autoImplicit false

namespace DvisetuChallenge

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

/-- The Dvisetu transition table.  `none` is the undefined halt
transition `F0`: reaching it is the only way the machine can halt. -/
def instr : State → Bool → Option Instr
  | State.A, false => some ⟨State.B, true, Dir.R⟩
  | State.A, true => some ⟨State.B, false, Dir.R⟩
  | State.B, false => some ⟨State.B, true, Dir.L⟩
  | State.B, true => some ⟨State.C, false, Dir.L⟩
  | State.C, false => some ⟨State.D, true, Dir.R⟩
  | State.C, true => some ⟨State.C, true, Dir.L⟩
  | State.D, false => some ⟨State.E, true, Dir.R⟩
  | State.D, true => some ⟨State.A, false, Dir.R⟩
  | State.E, false => some ⟨State.F, false, Dir.R⟩
  | State.E, true => some ⟨State.A, true, Dir.R⟩
  | State.F, false => none
  | State.F, true => some ⟨State.B, true, Dir.L⟩

/-- Head movement on the two-way infinite tape. -/
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

/-- One raw TM step.  `none` means the undefined `F0` halt was
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

/-- Conditional E-probe safety over the first `N` steps of a run: every
`0` probed by state `E` has a `1` immediately to its right (the halt
corridor `E0 → F0` never opens). -/
def ESafeSeg (c : Config) (N : Nat) : Prop :=
  ∀ k d, k < N → stepN k c = some d → d.state = State.E →
    d.tape d.head = false → d.tape (d.head + 1) = true

/-- Abstract checkpoint states: a two-block record `1^a 0 1^b`, or a
one-block checkpoint `1^m` in state `A` or `1^n` in state `B`. -/
inductive CState where
  | twoBlock (a b : Nat)
  | oneA (m : Nat)
  | oneB (n : Nat)

/-- Iterated division for the divide renewal: divide by 3 while the
value is `0 (mod 9)`, returning the terminal value and the division
count.  Fuel-driven. -/
def divCount : Nat → Nat → Nat × Nat
  | 0, m => (m, 0)
  | fuel + 1, m =>
      if m % 9 = 0 then
        let p := divCount fuel (m / 3)
        (p.1, p.2 + 1)
      else (m, 0)

/-- The divide renewal branch: `n ≡ 0 (mod 3)` splits into
`(n + 2 + d - y, y)` with `y` read off the terminal value of the
division cascade.  Guarded fail-closed. -/
def divideStep (n : Nat) : Option CState :=
  let m := (divCount n n).1
  let d := (divCount n n).2
  let y := if m % 9 = 3 then (m - 9) / 3 else (m - 3) / 3
  if 1 ≤ y ∧ y + 1 ≤ n + 2 + d then
    some (CState.twoBlock (n + 2 + d - y) y)
  else none

/-- The abstract checkpoint transition.  `none` marks exactly the value
patterns whose absence from the orbit is the checkpoint conjecture. -/
def cstep : CState → Option CState
  | CState.twoBlock a b =>
      if b = 1 then some (CState.oneA (a + 3))
      else if b % 3 = 1 then some (CState.twoBlock (a + 4) (b - 3))
      else none
  | CState.oneA m => some (CState.oneB (m + 1))
  | CState.oneB n =>
      if n % 3 = 1 then
        if 4 ≤ n then some (CState.twoBlock 4 (n - 3)) else none
      else if n % 3 = 2 then some (CState.twoBlock 2 (n - 1))
      else divideStep n

/-- The checkpoint orbit from the startup anchor `oneA 3` (the tape
`1^3` reached six raw steps from blank). -/
def corbit : Nat → Option CState
  | 0 => some (CState.oneA 3)
  | k + 1 => match corbit k with
      | none => none
      | some s => cstep s

/-- A configuration realizing an abstract checkpoint state: the tape
grammar pinning every cell from at most two integers and an anchor.
Two-block records anchor at the gap `g`; one-block checkpoints at the
left end `L`.  The head always sits on the fresh right frontier. -/
def Realizes : CState → Config → Prop
  | CState.twoBlock a b, cfg =>
      1 ≤ a ∧ 1 ≤ b ∧ cfg.state = State.B ∧
      ∃ g : Int,
        (∀ x : Int, x < g - a → cfg.tape x = false) ∧
        (∀ i : Nat, i < a → cfg.tape (g - a + i) = true) ∧
        cfg.tape g = false ∧
        (∀ i : Nat, i < b → cfg.tape (g + 1 + i) = true) ∧
        (∀ x : Int, g + b + 1 ≤ x → cfg.tape x = false) ∧
        cfg.head = g + b + 1
  | CState.oneA m, cfg =>
      1 ≤ m ∧ cfg.state = State.A ∧
      ∃ L : Int,
        (∀ x : Int, x < L → cfg.tape x = false) ∧
        (∀ i : Nat, i < m → cfg.tape (L + i) = true) ∧
        (∀ x : Int, L + m ≤ x → cfg.tape x = false) ∧
        cfg.head = L + m
  | CState.oneB n, cfg =>
      1 ≤ n ∧ cfg.state = State.B ∧
      ∃ L : Int,
        (∀ x : Int, x < L → cfg.tape x = false) ∧
        (∀ i : Nat, i < n → cfg.tape (L + i) = true) ∧
        (∀ x : Int, L + n ≤ x → cfg.tape x = false) ∧
        cfg.head = L + n

/-- The divide-episode assumption: whenever a one-block checkpoint
`1^n` with `n ≡ 0 (mod 3)` is realized on the tape and the abstract
divide branch produces an output, the raw machine reaches a
configuration realizing that output through a probe-safe segment. -/
def DivideFaithful : Prop :=
  ∀ (n : Nat) (s : CState) (cfg : Config), n % 3 = 0 →
    divideStep n = some s → Realizes (CState.oneB n) cfg →
    ∃ (N : Nat) (cfg' : Config), 0 < N ∧ stepN N cfg = some cfg' ∧
      Realizes s cfg' ∧ ESafeSeg cfg N

/-- **The Dvisetu checkpoint conjecture**: (i) the abstract checkpoint
orbit never dies — no renewal at `n = 1`, no divide with an undersized
terminal value, no two-block record off the `b ≡ 1 (mod 3)` lattice —
and (ii) the divide renewals realize their abstract outputs on the
tape (`DivideFaithful`). -/
def SafeCheckpointOrbit : Prop :=
  (∀ k : Nat, corbit k ≠ none) ∧ DivideFaithful

/-- **Main result** (proved in the solution module).  Under the
checkpoint conjecture, Dvisetu never halts from the all-zero tape. -/
theorem safeDvisetuOrbit_nonhalting (hso : SafeCheckpointOrbit) :
    ¬ RawHalts blankStart := sorry

end DvisetuChallenge
