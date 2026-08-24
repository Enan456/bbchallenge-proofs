import BusyBeaverCore.Dossier1RawTM

/-!
# Solution: dossier-1 does not halt, conditional on its orbit conjecture

Re-declares the definitions and theorem of `Palomar.Dossier1Challenge`
verbatim and proves them by transporting the certified development
(`QIG.Dossier1RawTM.safeOrbit_nonhalting`) across the challenge's own
definitions.  The transport maps are componentwise identities up to
renaming of the finite inductive types; the list helpers (`lastInc2`,
`unsnoc`) are proved equal to the development's by structural induction.
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

/-! ## Transport: the raw machine -/

/-! ## Transport: why re-declaring works

The challenge defines its own copies of every type, so its theorems cannot
simply cite ours.  The maps below are componentwise identities up to
renaming; each commutation lemma is a finite case split or structural
induction; the certified theorems then cross the bridge intact. -/

def stMap : St → QIG.Dossier1RawTM.State
  | .A => .A | .B => .B | .C => .C | .D => .D | .E => .E | .F => .F

def cMap (c : Config) : QIG.Dossier1RawTM.Config :=
  ⟨stMap c.state, c.head, c.tape⟩

theorem writeAt_lambda (t : Int → Bool) (p : Int) (v : Bool) :
    QIG.Dossier1RawTM.writeAt t p v = fun x => if x = p then v else t x := rfl

theorem step_map (c : Config) :
    QIG.Dossier1RawTM.step (cMap c) = Option.map cMap (step c) := by
  obtain ⟨s, h, t⟩ := c
  cases s <;> cases ht : t h <;>
    simp [step, QIG.Dossier1RawTM.step, instr, QIG.Dossier1RawTM.instr,
      QIG.Dossier1RawTM.move, writeAt_lambda, cMap, stMap, ht]

theorem stepN_map : ∀ (n : Nat) (c : Config),
    QIG.Dossier1RawTM.stepN n (cMap c) = Option.map cMap (stepN n c) := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
      intro c
      rw [show QIG.Dossier1RawTM.stepN (n + 1) (cMap c)
            = (QIG.Dossier1RawTM.step (cMap c)).bind (QIG.Dossier1RawTM.stepN n)
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
    Halts ↔ QIG.Dossier1RawTM.RawHalts QIG.Dossier1RawTM.blankStart := by
  have hbs : cMap blankStart = QIG.Dossier1RawTM.blankStart := rfl
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

/-! ## Transport: the abstract orbit -/

theorem lastInc2_eq : ∀ L : List Nat,
    lastInc2 L = QIG.Dossier1RawTM.lastInc2 L := by
  intro L
  induction L with
  | nil => rfl
  | cons x rest ih =>
      cases rest with
      | nil => rfl
      | cons y ys =>
          show x :: lastInc2 (y :: ys)
              = x :: QIG.Dossier1RawTM.lastInc2 (y :: ys)
          rw [ih]

theorem unsnoc_eq : ∀ L : List Nat,
    unsnoc L = QIG.Dossier1RawTM.unsnoc L := by
  intro L
  induction L with
  | nil => rfl
  | cons x rest ih =>
      cases rest with
      | nil => rfl
      | cons y ys =>
          show (match unsnoc (y :: ys) with
                | none => none
                | some (L', a) => some (x :: L', a))
              = (match QIG.Dossier1RawTM.unsnoc (y :: ys) with
                 | none => none
                 | some (L', a) => some (x :: L', a))
          rw [ih]

def aMap : AState → QIG.Dossier1RawTM.AState
  | .top n => .top n
  | .lvl L b c => .lvl L b c

theorem collapseTarget_map (L : List Nat) (n : Nat) :
    aMap (collapseTarget L n) = QIG.Dossier1RawTM.collapseTarget L n := by
  cases L <;> rfl

theorem astep_map (s : AState) :
    QIG.Dossier1RawTM.astep (aMap s) = Option.map aMap (astep s) := by
  cases s with
  | top n =>
      by_cases h4 : 4 ≤ n <;>
        simp [astep, QIG.Dossier1RawTM.astep, aMap, h4]
  | lvl L b c =>
      rw [show astep (AState.lvl L b c)
            = (match unsnoc L with
               | none => none
               | some (L₀, a) =>
                   if 3 ≤ b then
                     some (AState.lvl (lastInc2 L) (b - 2) (c + 1))
                   else if b = 2 then
                     (if 4 ≤ c then
                        some (AState.lvl (lastInc2 L ++ [1]) (c - 2) 1)
                      else none)
                   else if b = 1 then some (collapseTarget L₀ (a + c + 4))
                   else none)
          from rfl]
      rw [show QIG.Dossier1RawTM.astep (aMap (AState.lvl L b c))
            = (match QIG.Dossier1RawTM.unsnoc L with
               | none => none
               | some (L₀, a) =>
                   if 3 ≤ b then
                     some (QIG.Dossier1RawTM.AState.lvl
                       (QIG.Dossier1RawTM.lastInc2 L) (b - 2) (c + 1))
                   else if b = 2 then
                     (if 4 ≤ c then
                        some (QIG.Dossier1RawTM.AState.lvl
                          (QIG.Dossier1RawTM.lastInc2 L ++ [1]) (c - 2) 1)
                      else none)
                   else if b = 1 then
                     some (QIG.Dossier1RawTM.collapseTarget L₀ (a + c + 4))
                   else none)
          from rfl]
      rw [unsnoc_eq]
      cases hu : QIG.Dossier1RawTM.unsnoc L with
      | none => rfl
      | some pr =>
          obtain ⟨L₀, a⟩ := pr
          by_cases h3 : 3 ≤ b
          · simp [h3, aMap, lastInc2_eq]
          · by_cases h2 : b = 2
            · by_cases h4 : 4 ≤ c <;> simp [h3, h2, h4, aMap, lastInc2_eq]
            · by_cases h1 : b = 1
              · simp [h3, h2, h1, collapseTarget_map]
              · simp [h3, h2, h1]

theorem aorbit_map : ∀ k,
    QIG.Dossier1RawTM.aorbit k = Option.map aMap (aorbit k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show QIG.Dossier1RawTM.aorbit (k + 1)
            = (match QIG.Dossier1RawTM.aorbit k with
               | none => none
               | some s => QIG.Dossier1RawTM.astep s)
          from rfl]
      rw [show aorbit (k + 1)
            = (match aorbit k with
               | none => none
               | some s => astep s)
          from rfl]
      rw [ih]
      cases hk : aorbit k with
      | none => rfl
      | some s =>
          show QIG.Dossier1RawTM.astep (aMap s) = Option.map aMap (astep s)
          exact astep_map s

theorem safeOrbit_transport (hsafe : SafeOrbit) :
    QIG.Dossier1RawTM.SafeOrbit := by
  intro k
  rw [aorbit_map k]
  cases hk : aorbit k with
  | none => exact absurd hk (hsafe k)
  | some s => simp

/-- **Main result.**  Under the orbit conjecture, the machine never halts
from the all-zero tape. -/
theorem dossier1_nonhalting (hsafe : SafeOrbit) : ¬ Halts := fun hH =>
  QIG.Dossier1RawTM.safeOrbit_nonhalting (safeOrbit_transport hsafe)
    (halts_iff.mp hH)

end Dossier1Challenge
