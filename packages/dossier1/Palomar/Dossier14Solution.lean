import BusyBeaverCore.Dossier14RawTM

/-!
# Solution: dossier-14 does not halt, conditional on its record-orbit conjecture

Re-declares the definitions and theorem of the challenge verbatim and
supplies the proof by transporting the certified development
(`BusyBeaverCore.Dossier14RawTM`: `QIG.Dossier14RawTM.safeD14Orbit_nonhalting`)
across the challenge's own definitions.  The challenge definitions are
syntactically identical to the certified module's, so the transport
maps are componentwise identities up to renaming of the finite state
type.
-/

set_option autoImplicit false

namespace Dossier14Challenge

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

/-- The dossier-14 transition table.  `none` is the undefined halt
transition `B1`: reaching it is the only way the machine can halt. -/
def instr : State → Bool → Option Instr
  | State.A, false => some ⟨State.B, true, Dir.R⟩
  | State.A, true => some ⟨State.C, true, Dir.L⟩
  | State.B, false => some ⟨State.C, true, Dir.R⟩
  | State.B, true => none
  | State.C, false => some ⟨State.D, true, Dir.L⟩
  | State.C, true => some ⟨State.C, true, Dir.L⟩
  | State.D, false => some ⟨State.E, true, Dir.R⟩
  | State.D, true => some ⟨State.C, false, Dir.L⟩
  | State.E, false => some ⟨State.F, true, Dir.R⟩
  | State.E, true => some ⟨State.E, false, Dir.R⟩
  | State.F, false => some ⟨State.A, true, Dir.R⟩
  | State.F, true => some ⟨State.D, false, Dir.R⟩

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
    | State.A, true =>
        match em with
        | [] => some (State.C, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.C em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.B, false =>
        (go fuel State.C (true :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.B, true => none
    | State.C, false =>
        match em with
        | [] => some (State.D, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.D em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.C, true =>
        match em with
        | [] => some (State.C, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.C em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.D, false =>
        (go fuel State.E (true :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.D, true =>
        match em with
        | [] => some (State.C, false :: false :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.C em2 (e0 :: false :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.E, false =>
        (go fuel State.F (true :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.E, true =>
        (go fuel State.E (false :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.F, false =>
        (go fuel State.A (true :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.F, true =>
        (go fuel State.D (false :: em) (rest.drop 1)).map
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

/-- **The dossier-14 record-orbit conjecture**: the fail-closed record
orbit never dies — no sweep ever meets the fatal probe or fuel
exhaustion.  A statement about a sequence of `(state, word)` pairs
with no tape, no head, no machine. -/
def SafeD14Orbit : Prop := ∀ k : Nat, worbit k ≠ none

/-! ## Transport to the certified development

The maps below are componentwise identities up to the renaming of the
finite state type; every transport lemma is a small induction. -/

/-- State renaming, challenge → certified. -/
def stMap : State → QIG.Dossier14RawTM.State
  | State.A => QIG.Dossier14RawTM.State.A
  | State.B => QIG.Dossier14RawTM.State.B
  | State.C => QIG.Dossier14RawTM.State.C
  | State.D => QIG.Dossier14RawTM.State.D
  | State.E => QIG.Dossier14RawTM.State.E
  | State.F => QIG.Dossier14RawTM.State.F

/-- State renaming, certified → challenge. -/
def stInv : QIG.Dossier14RawTM.State → State
  | QIG.Dossier14RawTM.State.A => State.A
  | QIG.Dossier14RawTM.State.B => State.B
  | QIG.Dossier14RawTM.State.C => State.C
  | QIG.Dossier14RawTM.State.D => State.D
  | QIG.Dossier14RawTM.State.E => State.E
  | QIG.Dossier14RawTM.State.F => State.F

theorem stInv_stMap : ∀ s : State, stInv (stMap s) = s := by
  intro s; cases s <;> rfl

/-- Configuration transport. -/
def cMap (c : Config) : QIG.Dossier14RawTM.Config :=
  ⟨stMap c.state, c.head, c.tape⟩

theorem writeAt_eq (t : Int → Bool) (p : Int) (v : Bool) :
    QIG.Dossier14RawTM.writeAt t p v = writeAt t p v := rfl

theorem step_map (c : Config) :
    QIG.Dossier14RawTM.step (cMap c) = Option.map cMap (step c) := by
  obtain ⟨s, h, t⟩ := c
  cases s <;> cases ht : t h <;>
    simp [step, QIG.Dossier14RawTM.step, instr, QIG.Dossier14RawTM.instr,
      move, QIG.Dossier14RawTM.move, writeAt_eq, cMap, stMap, ht]

theorem stepN_map : ∀ (n : Nat) (c : Config),
    QIG.Dossier14RawTM.stepN n (cMap c) = Option.map cMap (stepN n c) := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
      intro c
      rw [show QIG.Dossier14RawTM.stepN (n + 1) (cMap c)
            = (QIG.Dossier14RawTM.step (cMap c)).bind (QIG.Dossier14RawTM.stepN n)
          from rfl,
          show stepN (n + 1) c = (step c).bind (stepN n) from rfl,
          step_map]
      cases hs : step c with
      | none => rfl
      | some c' => exact ih c'

theorem halts_iff :
    RawHalts blankStart
      ↔ QIG.Dossier14RawTM.RawHalts QIG.Dossier14RawTM.blankStart := by
  have hbs : cMap blankStart = QIG.Dossier14RawTM.blankStart := rfl
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

/-- Sweep-result transport. -/
def rMap (r : State × List Bool × Nat) :
    QIG.Dossier14RawTM.State × List Bool × Nat :=
  (stMap r.1, r.2.1, r.2.2)

/-- The per-step cost bump commutes with the state renaming. -/
theorem add1_rMap :
    ((fun r => (r.1, r.2.1, 1 + r.2.2)) ∘ rMap)
      = (rMap ∘ fun (r : State × List Bool × Nat) => (r.1, r.2.1, 1 + r.2.2)) := by
  funext r; rfl

theorem go_map : ∀ (fuel : Nat) (q : QIG.Dossier14RawTM.State)
    (em rest : List Bool),
    QIG.Dossier14RawTM.go fuel q em rest
      = Option.map rMap (go fuel (stInv q) em rest) := by
  intro fuel
  induction fuel with
  | zero => intro q em rest; cases q <;> rfl
  | succ fuel ih =>
      intro q em rest
      cases rest with
      | nil =>
          cases q <;>
            (cases em with
             | nil =>
                 simp [go, QIG.Dossier14RawTM.go, stInv, stMap, ih, rMap,
                   Option.map_map, add1_rMap]
             | cons e0 em2 =>
                 cases e0 <;>
                   simp [go, QIG.Dossier14RawTM.go, stInv, stMap, ih, rMap,
                     Option.map_map, add1_rMap])
      | cons b rest =>
          cases b <;> cases q <;>
            (cases em with
             | nil =>
                 simp [go, QIG.Dossier14RawTM.go, stInv, stMap, ih, rMap,
                   Option.map_map, add1_rMap]
             | cons e0 em2 =>
                 cases e0 <;>
                   simp [go, QIG.Dossier14RawTM.go, stInv, stMap, ih, rMap,
                     Option.map_map, add1_rMap])

theorem wstep_map (st : State) (w : List Bool) :
    QIG.Dossier14RawTM.wstep (stMap st) w = Option.map rMap (wstep st w) := by
  have h := go_map (wfuel w) (stMap st) [] w
  rw [stInv_stMap] at h
  exact h

/-- Orbit-state transport. -/
def pMap (s : State × List Bool) : QIG.Dossier14RawTM.State × List Bool :=
  (stMap s.1, s.2)

theorem worbit_map : ∀ k : Nat,
    QIG.Dossier14RawTM.worbit k = Option.map pMap (worbit k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show QIG.Dossier14RawTM.worbit (k + 1)
            = (match QIG.Dossier14RawTM.worbit k with
               | none => none
               | some s => (QIG.Dossier14RawTM.wstep s.1 s.2).map
                   (fun r => (r.1, r.2.1)))
          from rfl,
          show worbit (k + 1)
            = (match worbit k with
               | none => none
               | some s => (wstep s.1 s.2).map (fun r => (r.1, r.2.1)))
          from rfl,
          ih]
      cases hk : worbit k with
      | none => rfl
      | some s =>
          show (QIG.Dossier14RawTM.wstep (stMap s.1) s.2).map
              (fun r => (r.1, r.2.1))
            = Option.map pMap ((wstep s.1 s.2).map (fun r => (r.1, r.2.1)))
          rw [wstep_map]
          cases wstep s.1 s.2 <;> rfl

theorem safe_transport (hso : SafeD14Orbit) :
    QIG.Dossier14RawTM.SafeD14Orbit := by
  intro k
  rw [worbit_map k]
  cases hk : worbit k with
  | none => exact absurd hk (hso k)
  | some s => simp

/-- **Main result.**  Under the record-orbit conjecture, dossier-14
never halts from the all-zero tape. -/
theorem safeD14Orbit_nonhalting (hso : SafeD14Orbit) :
    ¬ RawHalts blankStart :=
  fun hH =>
    QIG.Dossier14RawTM.safeD14Orbit_nonhalting (safe_transport hso)
      (halts_iff.mp hH)

end Dossier14Challenge
