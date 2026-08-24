import Lean.Elab.Tactic.Omega

/-!
# The Forge, layer 1: generic raw TM semantics and halt localization

Everything the four bespoke `*RawTM` developments proved separately about
raw semantics and halt localization, proven **once**, parameterized by the
transition table.  A new machine instantiates this file with its table plus
two finite-case-analysis facts (`HaltIff`, `EntryOnly`) and immediately
receives: halt characterization, halt localization to a two-cell probe
pattern, and the probe-safety contract `ProbeSafe → ¬ RawHalts`.

Also the *disproof* arm: `halts_certificate` — a concrete halting trace,
checkable by kernel computation, is a proof of halting.

Core-only; axioms `[propext, Quot.sound]`.
-/

namespace QIG.Forge

inductive St where
  | A | B | C | D | E | F
deriving Repr, DecidableEq

inductive Dir where
  | L | R
deriving Repr, DecidableEq

structure Instr where
  next : St
  write : Bool
  dir : Dir
deriving Repr, DecidableEq

def move : Int → Dir → Int
  | h, Dir.L => h - 1
  | h, Dir.R => h + 1

def probeOff : Dir → Int
  | Dir.L => -1
  | Dir.R => 1

theorem move_probeOff (h : Int) (d : Dir) : move h d = h + probeOff d := by
  cases d <;> simp [move, probeOff] <;> omega

def writeAt (tape : Int → Bool) (pos : Int) (value : Bool) : Int → Bool :=
  fun x => if x = pos then value else tape x

theorem writeAt_other (tape : Int → Bool) (pos x : Int) (value : Bool)
    (h : x ≠ pos) : writeAt tape pos value x = tape x := by
  simp [writeAt, h]

structure Config where
  state : St
  head : Int
  tape : Int → Bool

def blankStart : Config := ⟨St.A, 0, fun _ => false⟩

section Machine

variable (tbl : St → Bool → Option Instr)

def step (c : Config) : Option Config :=
  match tbl c.state (c.tape c.head) with
  | none => none
  | some i => some ⟨i.next, move c.head i.dir, writeAt c.tape c.head i.write⟩

def stepN : Nat → Config → Option Config
  | 0, c => some c
  | n + 1, c =>
      match step tbl c with
      | none => none
      | some c' => stepN n c'

def RawHalts (c : Config) : Prop := ∃ n : Nat, stepN tbl n c = none

def Reaches (c d : Config) : Prop := ∃ n : Nat, stepN tbl n c = some d

/-- **The disproof arm.**  Informally: to show a machine halts, you need
nothing clever — exhibit the number of steps and let the kernel replay the
run.  For a concrete machine and a concrete `n`, the hypothesis `h` is
established by `rfl`/`decide`, i.e. by pure computation inside the trusted
kernel; the "proof" is one constructor application, which is why this
theorem needs no axioms at all.  Together with
`nonhalting_of_probe_safe` below, both possible verdicts about a machine
have a landing pad in the forge. -/
theorem halts_certificate {c : Config} (n : Nat)
    (h : stepN tbl n c = none) : RawHalts tbl c := ⟨n, h⟩

/-- The halt shape of a machine: which state halts, which state feeds it,
in which direction the feeding move goes. -/
structure HaltSpec where
  haltSt : St
  probeSt : St
  dir : Dir
  wr : Bool

variable (spec : HaltSpec)

/-- Instantiation fact 1: the table is undefined exactly at
`(haltSt, 0)`. -/
def HaltIff : Prop :=
  ∀ s b, tbl s b = none ↔ (s = spec.haltSt ∧ b = false)

/-- Instantiation fact 2: the halt state is entered only from
`(probeSt, 0)`, writing `wr` and moving in `dir`.

Informally: together with `HaltIff`, this is *all* a machine must certify
about itself to enter the forge — two sentences a 12-way case split checks
mechanically.  Everything else is generic. -/
def EntryOnly : Prop :=
  ∀ s b i, tbl s b = some i → i.next = spec.haltSt →
    s = spec.probeSt ∧ b = false ∧ i.write = spec.wr ∧ i.dir = spec.dir

/-- Informally: *the machine can die in one step exactly when it stands on
the one undefined cell of its program* — in state `haltSt` reading `0`.
Everything else in the development funnels halting through this single
door.  The proof is nothing but a case split on what the table returns,
with the instantiation fact `hh` translating "the table returned `none`"
into "we are at the halt cell". -/
theorem step_eq_none_iff (hh : HaltIff tbl spec) (c : Config) :
    step tbl c = none ↔ c.state = spec.haltSt ∧ c.tape c.head = false := by
  cases hi : tbl c.state (c.tape c.head) with
  | none =>
      simp [step, hi]
      exact (hh _ _).mp hi
  | some i =>
      have hs : step tbl c
          = some ⟨i.next, move c.head i.dir, writeAt c.tape c.head i.write⟩ := by
        simp [step, hi]
      constructor
      · intro hnone
        rw [hs] at hnone
        simp at hnone
      · rintro ⟨h1, h2⟩
        have hnone := (hh _ _).mpr ⟨h1, h2⟩
        rw [hi] at hnone
        simp at hnone

/-- Informally: *you cannot wander into the halting state; there is exactly
one turnstile*.  If a step lands in `haltSt`, the previous configuration
was in `probeSt` reading a `0`, the head moved one cell in the fixed
direction `dir`, and the tape changed only at the departed cell.  This is
what lets us reason about the last two steps of any halting run: the
final configuration is forced, so the penultimate one is too. -/
theorem into_halt_only_from_probe (he : EntryOnly tbl spec) {c c' : Config}
    (h : step tbl c = some c') (hst : c'.state = spec.haltSt) :
    c.state = spec.probeSt ∧ c.tape c.head = false ∧
      c'.head = c.head + probeOff spec.dir ∧
      c'.tape = writeAt c.tape c.head spec.wr := by
  cases hi : tbl c.state (c.tape c.head) with
  | none => simp [step, hi] at h
  | some i =>
      simp [step, hi] at h
      rw [← h] at hst
      obtain ⟨hs, hb, hw, hd⟩ := he _ _ _ hi hst
      refine ⟨hs, hb, ?_, ?_⟩
      · rw [← h]
        show move c.head i.dir = c.head + probeOff spec.dir
        rw [hd, move_probeOff]
      · rw [← h]
        show writeAt c.tape c.head i.write = writeAt c.tape c.head spec.wr
        rw [hw]

theorem stepN_none_last :
    ∀ (n : Nat) (c : Config), stepN tbl n c = none →
      ∃ k : Nat, k < n ∧ ∃ d : Config,
        stepN tbl k c = some d ∧ step tbl d = none := by
  intro n
  induction n with
  | zero =>
      intro c h
      simp [stepN] at h
  | succ n ih =>
      intro c h
      cases hstep : step tbl c with
      | none =>
          exact ⟨0, by omega, c, by simp [stepN], hstep⟩
      | some c1 =>
          have h1 : stepN tbl n c1 = none := by
            simpa [stepN, hstep] using h
          obtain ⟨k, hk, d, hd, hstop⟩ := ih c1 h1
          exact ⟨k + 1, by omega, d, by simpa [stepN, hstep] using hd, hstop⟩

theorem stepN_some_pred :
    ∀ (k : Nat) (c d : Config), stepN tbl (k + 1) c = some d →
      ∃ e : Config, stepN tbl k c = some e ∧ step tbl e = some d := by
  intro k
  induction k with
  | zero =>
      intro c d h
      cases hstep : step tbl c with
      | none => simp [stepN, hstep] at h
      | some c1 =>
          have : c1 = d := by simpa [stepN, hstep] using h
          exact ⟨c, by simp [stepN], by rw [hstep, this]⟩
  | succ k ih =>
      intro c d h
      cases hstep : step tbl c with
      | none => simp [stepN, hstep] at h
      | some c1 =>
          have h1 : stepN tbl (k + 1) c1 = some d := by
            simpa [stepN, hstep] using h
          obtain ⟨e, he, hlast⟩ := ih c1 d h1
          exact ⟨e, by simpa [stepN, hstep] using he, hlast⟩

/-- **Generic halt localization.**  Informally: *a halting run must, at
some earlier moment, stand in the probe state on a `0` whose `dir`-side
neighbour is also `0`* — a two-cell window on an infinite tape.

Why: rewind the halting run to its last living configuration (it dies by
`step_eq_none_iff`, so it is the halt state reading `0`); its predecessor
entered through the turnstile (`into_halt_only_from_probe`), so it was the
probe state reading `0`; and the fatal `0` the halt state dies on sits one
cell over in direction `dir` — a cell the turnstile step *did not write*
(`writeAt_other`), so it was already `0` at probe time.  Halting, an
unbounded global property, has become the reachability of one local
pattern.  This is the same move the macro emulation makes empirically;
here it is a theorem. -/
theorem halt_requires_probe (hh : HaltIff tbl spec) (he : EntryOnly tbl spec)
    {c : Config} (hne : c.state ≠ spec.haltSt) (hraw : RawHalts tbl c) :
    ∃ d : Config, Reaches tbl c d ∧ d.state = spec.probeSt ∧
      d.tape d.head = false ∧
      d.tape (d.head + probeOff spec.dir) = false := by
  obtain ⟨n, hn⟩ := hraw
  obtain ⟨k, _, d0, hd0, hstop⟩ := stepN_none_last tbl n c hn
  have hE := (step_eq_none_iff tbl spec hh d0).mp hstop
  cases k with
  | zero =>
      have hcd : c = d0 := by simpa [stepN] using hd0
      exact absurd (hcd ▸ hE.1) hne
  | succ k' =>
      obtain ⟨e, he', hstepe⟩ := stepN_some_pred tbl k' c d0 hd0
      obtain ⟨hP, h0, hhead, htape⟩ :=
        into_halt_only_from_probe tbl spec he hstepe hE.1
      refine ⟨e, ⟨k', he'⟩, hP, h0, ?_⟩
      have hread : d0.tape d0.head = false := hE.2
      rw [htape, hhead] at hread
      rwa [writeAt_other e.tape e.head (e.head + probeOff spec.dir) spec.wr
        (by cases hd : spec.dir <;> simp [probeOff, hd] <;> omega)] at hread

/-- The generic probe-safety contract.

Informally: the sentry condition, machine-independent — a `1` always
guards the `dir`-side of whatever the probe state reads.  Discharging it
is what the orbit layers of any particular machine are for. -/
def ProbeSafe (c : Config) : Prop :=
  ∀ d : Config, Reaches tbl c d → d.state = spec.probeSt →
    d.tape d.head = false → d.tape (d.head + probeOff spec.dir) = true

/-- **The proof arm.**  Informally: *if every `0` the probe state ever
reads has a `1` standing guard on its `dir` side, the machine can never
halt* — because a halt would produce the guarded pattern with a `0` where
the guard must be.  Discharging this `ProbeSafe` invariant is the entire
remaining content of a non-halting proof; the orbit layers exist to supply
it. -/
theorem nonhalting_of_probe_safe (hh : HaltIff tbl spec)
    (he : EntryOnly tbl spec) {c : Config} (hne : c.state ≠ spec.haltSt)
    (hsafe : ProbeSafe tbl spec c) : ¬ RawHalts tbl c := by
  intro hraw
  obtain ⟨d, hreach, hP, h0, h00⟩ :=
    halt_requires_probe tbl spec hh he hne hraw
  have h1 := hsafe d hreach hP h0
  rw [h1] at h00
  exact Bool.noConfusion h00

theorem blank_nonhalting_of_probe_safe (hh : HaltIff tbl spec)
    (he : EntryOnly tbl spec) (hA : spec.haltSt ≠ St.A)
    (hsafe : ProbeSafe tbl spec blankStart) :
    ¬ RawHalts tbl blankStart :=
  nonhalting_of_probe_safe tbl spec hh he
    (fun h => hA (by rw [← h]; rfl)) hsafe

end Machine

end QIG.Forge

#print axioms QIG.Forge.halt_requires_probe
#print axioms QIG.Forge.nonhalting_of_probe_safe
#print axioms QIG.Forge.halts_certificate
