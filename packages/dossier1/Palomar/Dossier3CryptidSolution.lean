import BusyBeaverCore.Dossier3RawTM

/-!
# Solution: dossier-3 does not halt, conditional on its orbit conjecture

Re-declares the definitions and theorem of the challenge verbatim and
supplies the proof by transporting the certified development
(`BusyBeaverCore.Dossier3RawTM`: `QIG.Dossier3RawTM.dossier3_nonhalting_of_safeMetaOrbit`)
across the challenge's own definitions.  The transport maps are
componentwise identities up to renaming of the finite inductive types.
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

/-! ## Transport to the certified development -/

def stMap : St → QIG.Dossier3RawTM.State
  | .A => .A | .B => .B | .C => .C | .D => .D | .E => .E | .F => .F

def cMap (c : Config) : QIG.Dossier3RawTM.Config :=
  ⟨stMap c.state, c.head, c.tape⟩

theorem writeAt_lambda (t : Int → Bool) (p : Int) (v : Bool) :
    QIG.Dossier3RawTM.writeAt t p v = fun x => if x = p then v else t x := rfl

theorem step_map (c : Config) :
    QIG.Dossier3RawTM.step (cMap c) = Option.map cMap (step c) := by
  obtain ⟨s, h, t⟩ := c
  cases s <;> cases ht : t h <;>
    simp [step, QIG.Dossier3RawTM.step, instr, QIG.Dossier3RawTM.instr,
      QIG.Dossier3RawTM.move, writeAt_lambda, cMap, stMap, ht]

theorem stepN_map : ∀ (n : Nat) (c : Config),
    QIG.Dossier3RawTM.stepN n (cMap c) = Option.map cMap (stepN n c) := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
      intro c
      rw [show QIG.Dossier3RawTM.stepN (n + 1) (cMap c)
            = (QIG.Dossier3RawTM.step (cMap c)).bind (QIG.Dossier3RawTM.stepN n)
          from rfl]
      rw [show stepN (n + 1) c
            = (match step c with
               | none => none
               | some c' => stepN n c')
          from rfl]
      rw [step_map]
      cases hs : step c with
      | none => rfl
      | some c' => exact ih c'

theorem halts_iff :
    Halts ↔ QIG.Dossier3RawTM.RawHalts QIG.Dossier3RawTM.blankStart := by
  have hbs : cMap blankStart = QIG.Dossier3RawTM.blankStart := rfl
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

def mMap (s : MetaState) : QIG.Dossier3RawTM.MetaState :=
  ⟨s.three, s.l, s.h1, s.h2, s.r⟩

theorem metaStep_map (s : MetaState) :
    QIG.Dossier3RawTM.metaStep (mMap s) = Option.map mMap (metaStep s) := by
  obtain ⟨t, l, h1, h2, r⟩ := s
  cases t <;>
    simp only [metaStep, QIG.Dossier3RawTM.metaStep, mMap] <;>
    (repeat' split) <;> rfl

theorem metaOrbit_map : ∀ k,
    QIG.Dossier3RawTM.metaOrbit k = Option.map mMap (metaOrbit k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show QIG.Dossier3RawTM.metaOrbit (k + 1)
            = (match QIG.Dossier3RawTM.metaOrbit k with
               | none => none
               | some s => QIG.Dossier3RawTM.metaStep s)
          from rfl,
          show metaOrbit (k + 1)
            = (match metaOrbit k with
               | none => none
               | some s => metaStep s)
          from rfl,
          ih]
      cases hk : metaOrbit k with
      | none => rfl
      | some s =>
          show QIG.Dossier3RawTM.metaStep (mMap s) = Option.map mMap (metaStep s)
          exact metaStep_map s

theorem safe_transport (hsafe : SafeMetaOrbit) :
    QIG.Dossier3RawTM.SafeMetaOrbit := by
  intro k
  rw [metaOrbit_map k]
  cases hk : metaOrbit k with
  | none => exact absurd hk (hsafe k)
  | some s => simp

/-- **Main result.**  Under the orbit conjecture, dossier-3 never
halts from the all-zero tape. -/
theorem dossier3_nonhalting (hsafe : SafeMetaOrbit) : ¬ Halts :=
  fun hH =>
    QIG.Dossier3RawTM.dossier3_nonhalting_of_safeMetaOrbit (safe_transport hsafe)
      (halts_iff.mp hH)

end Dossier3CryptidChallenge
