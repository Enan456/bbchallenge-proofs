import BusyBeaverCore.Rank1RawTM

/-!
# Solution: the rank-1 array-class machine does not halt, conditional on its word-orbit conjecture

Re-declares the definitions and theorem of the challenge verbatim and
supplies the proof by transporting the certified development
(`BusyBeaverCore.Rank1RawTM`: `QIG.Rank1RawTM.safeWordOrbit_nonhalting`)
across the challenge's own definitions.  The challenge definitions are
syntactically identical to the certified module's; the word-level
engine involves no machine state at all, so its transport lemmas are
plain equalities, and the raw-machine transport is the usual renaming
of the finite state type.
-/

set_option autoImplicit false

namespace Rank1Challenge

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

/-- The rank-1 transition table.  `none` is the undefined halt
transition `E1`: reaching it is the only way the machine can halt. -/
def instr : State → Bool → Option Instr
  | State.A, false => some ⟨State.B, true, Dir.R⟩
  | State.A, true => some ⟨State.D, true, Dir.R⟩
  | State.B, false => some ⟨State.C, true, Dir.L⟩
  | State.B, true => some ⟨State.C, false, Dir.L⟩
  | State.C, false => some ⟨State.D, false, Dir.R⟩
  | State.C, true => some ⟨State.B, false, Dir.L⟩
  | State.D, false => some ⟨State.F, true, Dir.R⟩
  | State.D, true => some ⟨State.E, false, Dir.L⟩
  | State.E, false => some ⟨State.D, false, Dir.R⟩
  | State.E, true => none
  | State.F, false => some ⟨State.A, false, Dir.R⟩
  | State.F, true => some ⟨State.C, true, Dir.R⟩

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

/-- One raw TM step.  `none` means the undefined `E1` halt was
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

/-- The parametric descent executed as list surgery on the stack `em`:
the four cases are the immediate turn, the two blank-region
terminations below the base (extending the left extreme by 1 or 2),
and the two-cell recursion.  Returns
`(raw steps, head offset delta, new stack, new rest)`. -/
def descendExec : List Bool → Bool → List Bool → Nat × Nat × List Bool × List Bool
  | [], r, rest => (2, 1, [false], (!r) :: rest)
  | [true], r, rest => (4, 2, [false], true :: false :: (!r) :: rest)
  | false :: em2, r, rest => (2, 0, false :: em2, (!r) :: rest)
  | true :: b :: em2, r, rest =>
      ((descendExec em2 b (false :: (!r) :: rest)).1 + 2,
       (descendExec em2 b (false :: (!r) :: rest)).2)

/-- Descent scan: `some i` = the descent from a `B`-turn over this
stack turns at stack index `2i` (depth `2i+1`); `none` = it runs off
the bottom (extends the left extreme: a full arrival). -/
def dScan : List Bool → Option Nat
  | [] => none
  | false :: _ => some 0
  | true :: [] => none
  | true :: _ :: t => (dScan t).map (· + 1)

/-- A `B`-turn is the *next arrival* iff its descent is deep
(`2i+1 ≥ 8`, i.e. `i ≥ 4`) or extreme-extending. -/
def stopDeep (em : List Bool) : Bool :=
  match dScan em with
  | none => true
  | some i => decide (4 ≤ i)

/-- The fail-closed pass: from state `D` at the boundary of `em`
(below, nearest first) and `rest` (head cell first), run the sweep to
the next arrival.  Returns `(word, head offset, steps)`.  It fails
closed (`none`) exactly on the fatal `D`-probe, on a malformed or
`C`-state arrival, and on fuel exhaustion. -/
def passGo : Nat → List Bool → List Bool → Option (List Bool × Nat × Nat)
  | 0, _, _ => none
  | fuel + 1, em, rest =>
    match rest.getD 0 false, em.getD 0 false, rest.getD 1 false, rest.getD 2 false with
    | true, true, _, _ => none
    | true, false, _, _ =>
        (passGo fuel em (false :: rest.drop 1)).map
          (fun r => (r.1, r.2.1, 2 + r.2.2))
    | false, _, false, true =>
        (passGo fuel (true :: false :: true :: em) (rest.drop 3)).map
          (fun r => (r.1, r.2.1, 3 + r.2.2))
    | false, _, true, false =>
        (passGo fuel (false :: true :: true :: em) (rest.drop 3)).map
          (fun r => (r.1, r.2.1, 3 + r.2.2))
    | false, _, false, false =>
        if stopDeep (true :: false :: true :: em) then
          if (rest.drop 3).getD 0 false then none
          else some ((true :: false :: true :: em).reverse ++ rest.drop 3,
            em.length + 3, 3)
        else
          (passGo fuel
            (descendExec (true :: false :: true :: em)
              ((rest.drop 3).getD 0 false) ((rest.drop 3).drop 1)).2.2.1
            (descendExec (true :: false :: true :: em)
              ((rest.drop 3).getD 0 false) ((rest.drop 3).drop 1)).2.2.2).map
            (fun r => (r.1, r.2.1,
              3 + (descendExec (true :: false :: true :: em)
                ((rest.drop 3).getD 0 false) ((rest.drop 3).drop 1)).1 + r.2.2))
    | false, _, true, true =>
        if stopDeep (true :: em) then none
        else
          (passGo fuel
            (descendExec (true :: em) true (false :: rest.drop 3)).2.2.1
            (descendExec (true :: em) true (false :: rest.drop 3)).2.2.2).map
            (fun r => (r.1, r.2.1,
              3 + (descendExec (true :: em) true (false :: rest.drop 3)).1 + r.2.2))

/-- Generous fuel: recursion depth is bounded by the raw step count of
one sweep, comfortably quadratic in the word length.  Fail-closed —
exhaustion is an orbit death. -/
def passFuel (w : List Bool) : Nat := 64 * (w.length + 64) * (w.length + 64)

/-- One certified sweep: from an arrival `(w, poff)` (state `B`
reading `0`), execute the shoot (the initial descent, full or mini as
the word dictates) and the pass.  Returns `(w', poff', steps)`. -/
def wstep (w : List Bool) (poff : Nat) : Option (List Bool × Nat × Nat) :=
  if poff ≤ w.length ∧ w.getD poff false = false then
    (passGo (passFuel w)
      (descendExec ((w.take poff).reverse) false (w.drop (poff + 1))).2.2.1
      (descendExec ((w.take poff).reverse) false (w.drop (poff + 1))).2.2.2).map
      (fun r => (r.1, r.2.1,
        (descendExec ((w.take poff).reverse) false (w.drop (poff + 1))).1 + r.2.2))
  else none

/-- The word orbit: `wstep` iterated from the anchor `([1], 1)` — the
arrival reached one raw step from the blank start. -/
def worbit : Nat → Option (List Bool × Nat)
  | 0 => some ([true], 1)
  | k + 1 =>
      match worbit k with
      | none => none
      | some s => (wstep s.1 s.2).map (fun r => (r.1, r.2.1))

/-- **The rank-1 word-orbit conjecture**: the fail-closed word orbit
never dies — no sweep ever meets a fatal `D`-probe, a malformed
arrival, a `C`-state arrival, or fuel exhaustion.  A statement about a
sequence of words with no tape, no head, no machine. -/
def SafeWordOrbit : Prop := ∀ k : Nat, worbit k ≠ none

/-! ## Transport to the certified development -/

/-- State renaming, challenge → certified. -/
def stMap : State → QIG.Rank1RawTM.State
  | State.A => QIG.Rank1RawTM.State.A
  | State.B => QIG.Rank1RawTM.State.B
  | State.C => QIG.Rank1RawTM.State.C
  | State.D => QIG.Rank1RawTM.State.D
  | State.E => QIG.Rank1RawTM.State.E
  | State.F => QIG.Rank1RawTM.State.F

/-- Configuration transport. -/
def cMap (c : Config) : QIG.Rank1RawTM.Config :=
  ⟨stMap c.state, c.head, c.tape⟩

theorem writeAt_eq (t : Int → Bool) (p : Int) (v : Bool) :
    QIG.Rank1RawTM.writeAt t p v = writeAt t p v := rfl

theorem step_map (c : Config) :
    QIG.Rank1RawTM.step (cMap c) = Option.map cMap (step c) := by
  obtain ⟨s, h, t⟩ := c
  cases s <;> cases ht : t h <;>
    simp [step, QIG.Rank1RawTM.step, instr, QIG.Rank1RawTM.instr,
      move, QIG.Rank1RawTM.move, writeAt_eq, cMap, stMap, ht]

theorem stepN_map : ∀ (n : Nat) (c : Config),
    QIG.Rank1RawTM.stepN n (cMap c) = Option.map cMap (stepN n c) := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
      intro c
      rw [show QIG.Rank1RawTM.stepN (n + 1) (cMap c)
            = (QIG.Rank1RawTM.step (cMap c)).bind (QIG.Rank1RawTM.stepN n)
          from rfl,
          show stepN (n + 1) c = (step c).bind (stepN n) from rfl,
          step_map]
      cases hs : step c with
      | none => rfl
      | some c' => exact ih c'

theorem halts_iff :
    RawHalts blankStart
      ↔ QIG.Rank1RawTM.RawHalts QIG.Rank1RawTM.blankStart := by
  have hbs : cMap blankStart = QIG.Rank1RawTM.blankStart := rfl
  constructor
  · intro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← hbs, stepN_map n blankStart, hn]
    rfl
  · intro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hmap := stepN_map n blankStart
    rw [hbs, hn] at hmap
    cases h : stepN n blankStart with
    | none => rfl
    | some c => rw [h] at hmap; simp at hmap

/-! The word-level engine mentions no machine state, so the transport
lemmas below are plain equalities between the challenge's executable
functions and the certified module's. -/

theorem descendExec_eq : ∀ (em : List Bool) (r : Bool) (rest : List Bool),
    descendExec em r rest = QIG.Rank1RawTM.descendExec em r rest := by
  intro em r rest
  induction em, r, rest using descendExec.induct <;>
    simp [descendExec, QIG.Rank1RawTM.descendExec, *]

theorem dScan_eq : ∀ l : List Bool, dScan l = QIG.Rank1RawTM.dScan l := by
  intro l
  induction l using dScan.induct <;>
    simp [dScan, QIG.Rank1RawTM.dScan, *]

theorem stopDeep_eq (em : List Bool) :
    stopDeep em = QIG.Rank1RawTM.stopDeep em := by
  unfold stopDeep QIG.Rank1RawTM.stopDeep
  rw [dScan_eq]
  cases QIG.Rank1RawTM.dScan em <;> rfl

theorem passFuel_eq (w : List Bool) :
    passFuel w = QIG.Rank1RawTM.passFuel w := rfl

theorem passGo_eq : ∀ (fuel : Nat) (em rest : List Bool),
    passGo fuel em rest = QIG.Rank1RawTM.passGo fuel em rest := by
  intro fuel
  induction fuel with
  | zero => intro em rest; rfl
  | succ fuel ih =>
      intro em rest
      rw [passGo.eq_def, QIG.Rank1RawTM.passGo.eq_def]
      cases hr0 : rest.getD 0 false <;> cases he : em.getD 0 false <;>
        cases hr1 : rest.getD 1 false <;> cases hr2 : rest.getD 2 false <;>
        simp only [hr0, he, hr1, hr2, ih, descendExec_eq, stopDeep_eq]

theorem wstep_eq (w : List Bool) (poff : Nat) :
    wstep w poff = QIG.Rank1RawTM.wstep w poff := by
  simp only [wstep, QIG.Rank1RawTM.wstep, passFuel_eq, descendExec_eq,
    passGo_eq]

theorem worbit_eq : ∀ k : Nat, worbit k = QIG.Rank1RawTM.worbit k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show worbit (k + 1)
            = (match worbit k with
               | none => none
               | some s => (wstep s.1 s.2).map (fun r => (r.1, r.2.1)))
          from rfl,
          show QIG.Rank1RawTM.worbit (k + 1)
            = (match QIG.Rank1RawTM.worbit k with
               | none => none
               | some s => (QIG.Rank1RawTM.wstep s.1 s.2).map
                   (fun r => (r.1, r.2.1)))
          from rfl,
          ← ih]
      cases worbit k with
      | none => rfl
      | some s =>
          show (wstep s.1 s.2).map (fun r => (r.1, r.2.1))
            = (QIG.Rank1RawTM.wstep s.1 s.2).map (fun r => (r.1, r.2.1))
          rw [wstep_eq]

theorem safe_transport (hso : SafeWordOrbit) :
    QIG.Rank1RawTM.SafeWordOrbit := by
  intro k
  rw [← worbit_eq k]
  exact hso k

/-- **Main result.**  Under the word-orbit conjecture, the rank-1
machine never halts from the all-zero tape. -/
theorem safeWordOrbit_nonhalting (hso : SafeWordOrbit) :
    ¬ RawHalts blankStart :=
  fun hH =>
    QIG.Rank1RawTM.safeWordOrbit_nonhalting (safe_transport hso)
      (halts_iff.mp hH)

end Rank1Challenge
