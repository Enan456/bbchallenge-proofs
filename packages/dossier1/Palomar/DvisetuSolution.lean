import BusyBeaverCore.DvisetuRawTM

/-!
# Solution: the Dvisetu machine does not halt, conditional on its checkpoint conjecture

Re-declares the definitions and theorem of the challenge verbatim and
supplies the proof by transporting the certified development
(`BusyBeaverCore.DvisetuRawTM`: `QIG.DvisetuRawTM.safeDvisetuOrbit_nonhalting`)
across the challenge's own definitions.  The challenge definitions are
syntactically identical to the certified module's, so the transport
maps are componentwise identities up to renaming of the finite state
and checkpoint-state types; the `DivideFaithful` component transports
contravariantly through the configuration renaming.
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

/-! ## Transport to the certified development -/

/-- State renaming, challenge → certified. -/
def stMap : State → QIG.DvisetuRawTM.State
  | State.A => QIG.DvisetuRawTM.State.A
  | State.B => QIG.DvisetuRawTM.State.B
  | State.C => QIG.DvisetuRawTM.State.C
  | State.D => QIG.DvisetuRawTM.State.D
  | State.E => QIG.DvisetuRawTM.State.E
  | State.F => QIG.DvisetuRawTM.State.F

/-- State renaming, certified → challenge. -/
def stInv : QIG.DvisetuRawTM.State → State
  | QIG.DvisetuRawTM.State.A => State.A
  | QIG.DvisetuRawTM.State.B => State.B
  | QIG.DvisetuRawTM.State.C => State.C
  | QIG.DvisetuRawTM.State.D => State.D
  | QIG.DvisetuRawTM.State.E => State.E
  | QIG.DvisetuRawTM.State.F => State.F

theorem stMap_stInv : ∀ q : QIG.DvisetuRawTM.State, stMap (stInv q) = q := by
  intro q; cases q <;> rfl

theorem stMap_eq_A : ∀ s : State,
    stMap s = QIG.DvisetuRawTM.State.A ↔ s = State.A := by
  intro s; cases s <;> simp [stMap]

theorem stMap_eq_B : ∀ s : State,
    stMap s = QIG.DvisetuRawTM.State.B ↔ s = State.B := by
  intro s; cases s <;> simp [stMap]

theorem stMap_eq_E : ∀ s : State,
    stMap s = QIG.DvisetuRawTM.State.E ↔ s = State.E := by
  intro s; cases s <;> simp [stMap]

/-- Configuration transport, challenge → certified. -/
def cMap (c : Config) : QIG.DvisetuRawTM.Config :=
  ⟨stMap c.state, c.head, c.tape⟩

/-- Configuration transport, certified → challenge. -/
def cInv (c : QIG.DvisetuRawTM.Config) : Config :=
  ⟨stInv c.state, c.head, c.tape⟩

theorem cMap_cInv : ∀ c : QIG.DvisetuRawTM.Config, cMap (cInv c) = c := by
  intro c; cases c; simp [cMap, cInv, stMap_stInv]

theorem writeAt_eq (t : Int → Bool) (p : Int) (v : Bool) :
    QIG.DvisetuRawTM.writeAt t p v = writeAt t p v := rfl

theorem step_map (c : Config) :
    QIG.DvisetuRawTM.step (cMap c) = Option.map cMap (step c) := by
  obtain ⟨s, h, t⟩ := c
  cases s <;> cases ht : t h <;>
    simp [step, QIG.DvisetuRawTM.step, instr, QIG.DvisetuRawTM.instr,
      move, QIG.DvisetuRawTM.move, writeAt_eq, cMap, stMap, ht]

theorem stepN_map : ∀ (n : Nat) (c : Config),
    QIG.DvisetuRawTM.stepN n (cMap c) = Option.map cMap (stepN n c) := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
      intro c
      rw [show QIG.DvisetuRawTM.stepN (n + 1) (cMap c)
            = (QIG.DvisetuRawTM.step (cMap c)).bind (QIG.DvisetuRawTM.stepN n)
          from rfl,
          show stepN (n + 1) c = (step c).bind (stepN n) from rfl,
          step_map]
      cases hs : step c with
      | none => rfl
      | some c' => exact ih c'

theorem halts_iff :
    RawHalts blankStart
      ↔ QIG.DvisetuRawTM.RawHalts QIG.DvisetuRawTM.blankStart := by
  have hbs : cMap blankStart = QIG.DvisetuRawTM.blankStart := rfl
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

/-- Checkpoint-state renaming, challenge → certified. -/
def csMap : CState → QIG.DvisetuRawTM.CState
  | CState.twoBlock a b => QIG.DvisetuRawTM.CState.twoBlock a b
  | CState.oneA m => QIG.DvisetuRawTM.CState.oneA m
  | CState.oneB n => QIG.DvisetuRawTM.CState.oneB n

theorem divCount_eq : ∀ (fuel m : Nat),
    divCount fuel m = QIG.DvisetuRawTM.divCount fuel m := by
  intro fuel
  induction fuel with
  | zero => intro m; rfl
  | succ fuel ih =>
      intro m
      simp [divCount, QIG.DvisetuRawTM.divCount, ih]

theorem divideStep_map (n : Nat) :
    QIG.DvisetuRawTM.divideStep n = Option.map csMap (divideStep n) := by
  simp only [divideStep, QIG.DvisetuRawTM.divideStep, divCount_eq]
  split <;> rename_i h <;> simp [h, csMap]

theorem cstep_map : ∀ s : CState,
    QIG.DvisetuRawTM.cstep (csMap s) = Option.map csMap (cstep s) := by
  intro s
  cases s with
  | twoBlock a b =>
      by_cases h1 : b = 1 <;> by_cases h3 : b % 3 = 1 <;>
        simp [cstep, QIG.DvisetuRawTM.cstep, csMap, h1, h3]
  | oneA m => rfl
  | oneB n =>
      by_cases h1 : n % 3 = 1 <;> by_cases h2 : n % 3 = 2 <;>
        by_cases h4 : 4 ≤ n <;>
        simp [cstep, QIG.DvisetuRawTM.cstep, csMap, h1, h2, h4,
          divideStep_map]

theorem corbit_map : ∀ k : Nat,
    QIG.DvisetuRawTM.corbit k = Option.map csMap (corbit k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show QIG.DvisetuRawTM.corbit (k + 1)
            = (match QIG.DvisetuRawTM.corbit k with
               | none => none
               | some s => QIG.DvisetuRawTM.cstep s)
          from rfl,
          show corbit (k + 1)
            = (match corbit k with
               | none => none
               | some s => cstep s)
          from rfl,
          ih]
      cases corbit k with
      | none => rfl
      | some s => exact cstep_map s

theorem realizes_map : ∀ (s : CState) (cfg : Config),
    QIG.DvisetuRawTM.Realizes (csMap s) (cMap cfg) ↔ Realizes s cfg := by
  intro s cfg
  cases s <;>
    simp [Realizes, QIG.DvisetuRawTM.Realizes, csMap, cMap,
      stMap_eq_A, stMap_eq_B]

theorem esafe_map {c : Config} {N : Nat} (h : ESafeSeg c N) :
    QIG.DvisetuRawTM.ESafeSeg (cMap c) N := by
  intro k d hk hkd hE h0
  rw [stepN_map] at hkd
  cases hs : stepN k c with
  | none => rw [hs] at hkd; exact absurd hkd (by simp)
  | some d0 =>
      rw [hs] at hkd
      have hd : cMap d0 = d := by simpa using hkd
      subst hd
      have hst : d0.state = State.E := (stMap_eq_E d0.state).mp hE
      exact h k d0 hk hs hst h0

theorem safe_transport (hso : SafeCheckpointOrbit) :
    QIG.DvisetuRawTM.SafeCheckpointOrbit := by
  obtain ⟨horb, hdf⟩ := hso
  refine ⟨?_, ?_⟩
  · intro k
    rw [corbit_map k]
    cases hk : corbit k with
    | none => exact absurd hk (horb k)
    | some s => simp
  · intro n s cfg hn hds hreal
    have hds' : Option.map csMap (divideStep n) = some s := by
      rw [← divideStep_map]; exact hds
    cases hd0 : divideStep n with
    | none => rw [hd0] at hds'; exact absurd hds' (by simp)
    | some s0 =>
        rw [hd0] at hds'
        have hcs : csMap s0 = s := by simpa using hds'
        have hreal0 : Realizes (CState.oneB n) (cInv cfg) := by
          have hiff := realizes_map (CState.oneB n) (cInv cfg)
          rw [show csMap (CState.oneB n)
                = QIG.DvisetuRawTM.CState.oneB n from rfl,
              cMap_cInv] at hiff
          exact hiff.mp hreal
        obtain ⟨N, cfg', hN, hstep, hreal', hseg⟩ :=
          hdf n s0 (cInv cfg) hn hd0 hreal0
        refine ⟨N, cMap cfg', hN, ?_, ?_, ?_⟩
        · rw [← cMap_cInv cfg, stepN_map, hstep]
          rfl
        · rw [← hcs]
          exact (realizes_map s0 cfg').mpr hreal'
        · have hE := esafe_map hseg
          rw [cMap_cInv] at hE
          exact hE

/-- **Main result.**  Under the checkpoint conjecture, Dvisetu never
halts from the all-zero tape. -/
theorem safeDvisetuOrbit_nonhalting (hso : SafeCheckpointOrbit) :
    ¬ RawHalts blankStart :=
  fun hH =>
    QIG.DvisetuRawTM.safeDvisetuOrbit_nonhalting (safe_transport hso)
      (halts_iff.mp hH)

end DvisetuChallenge
