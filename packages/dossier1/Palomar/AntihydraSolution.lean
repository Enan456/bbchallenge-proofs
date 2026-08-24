import Bridge.Conjecture

/-!
# Solution: Antihydra does not halt, conditional on the hydra conjecture

Re-declares the definitions and theorem of `Palomar.AntihydraChallenge`
verbatim and supplies the proof, by transporting the certified development
(`Bridge.Conjecture`: `QIG.AntihydraRawTM.hydraSafe_nonhalting`) across the
challenge's own definitions.  The transport maps are componentwise identities
up to renaming of the finite inductive types, and every commutation lemma is
a finite case analysis or a structural induction.
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

/-! ## Transport to the certified development -/

/-! ## Transport: why re-declaring works

The challenge defines its own copies of every type, so its theorem cannot
simply cite ours — the types differ.  The maps below are componentwise
identities up to renaming; each commutation lemma is a finite case split;
and the main theorem is our certified result pulled across the bridge.
This is the standard pattern for making a small auditable statement file
inherit a large development's theorem. -/

def stMap : St → QIG.AntihydraRawTM.State
  | .A => .A | .B => .B | .C => .C | .D => .D | .E => .E | .F => .F

def cMap (c : Config) : QIG.AntihydraRawTM.Config :=
  ⟨stMap c.state, c.head, c.tape⟩

/-- `writeAt` is definitionally the pointwise-override lambda used by the
challenge's `step`; stating it as a rewrite lets `simp` normalize both sides
of the step commutation identically. -/
theorem writeAt_lambda (t : Int → Bool) (p : Int) (v : Bool) :
    QIG.AntihydraRawTM.writeAt t p v = fun x => if x = p then v else t x := rfl

theorem step_map (c : Config) :
    QIG.AntihydraRawTM.step (cMap c) = Option.map cMap (step c) := by
  obtain ⟨s, h, t⟩ := c
  cases s <;> cases ht : t h <;>
    simp [step, QIG.AntihydraRawTM.step, instr, QIG.AntihydraRawTM.instr,
      QIG.AntihydraRawTM.move, writeAt_lambda, cMap, stMap, ht]

theorem stepN_map : ∀ (n : Nat) (c : Config),
    QIG.AntihydraRawTM.stepN n (cMap c) = Option.map cMap (stepN n c) := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
      intro c
      rw [show QIG.AntihydraRawTM.stepN (n + 1) (cMap c)
            = (QIG.AntihydraRawTM.step (cMap c)).bind (QIG.AntihydraRawTM.stepN n)
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
    Halts ↔ QIG.AntihydraRawTM.RawHalts QIG.AntihydraRawTM.blankStart := by
  have hbs : cMap blankStart = QIG.AntihydraRawTM.blankStart := rfl
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

def hMap (p : Nat × Nat) : QIG.AntihydraRawTM.HydraState := ⟨p.1, p.2⟩

theorem hydraOrbit_map : ∀ k,
    QIG.AntihydraRawTM.hydraOrbit k = Option.map hMap (hydraOrbit k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show QIG.AntihydraRawTM.hydraOrbit (k + 1)
            = (match QIG.AntihydraRawTM.hydraOrbit k with
               | none => none
               | some s => QIG.AntihydraRawTM.hydraStep s)
          from rfl]
      rw [ih]
      cases hk : hydraOrbit k with
      | none => simp [hydraOrbit, hk]
      | some p =>
          obtain ⟨b, h⟩ := p
          simp only [hydraOrbit, hk, Option.map]
          by_cases hb : b % 2 = 0
          · simp [QIG.AntihydraRawTM.hydraStep, QIG.AntihydraRawTM.hydraNext,
                  hydraNext, hMap, hb]
          · by_cases hh : 2 ≤ h
            · simp [QIG.AntihydraRawTM.hydraStep, QIG.AntihydraRawTM.hydraNext,
                    hydraNext, hMap, hb, hh]
            · simp [QIG.AntihydraRawTM.hydraStep, hMap, hb, hh]

theorem hydraSafe_transport (hsafe : HydraSafe) :
    QIG.AntihydraRawTM.HydraSafe := by
  intro k
  rw [hydraOrbit_map k]
  cases hk : hydraOrbit k with
  | none => exact absurd hk (hsafe k)
  | some p => simp

/-- **Main result.**  Under the hydra conjecture, Antihydra never halts from
the all-zero tape. -/
theorem antihydra_nonhalting (hsafe : HydraSafe) : ¬ Halts := fun hH =>
  QIG.AntihydraRawTM.hydraSafe_nonhalting (hydraSafe_transport hsafe)
    (halts_iff.mp hH)

end AntihydraChallenge
