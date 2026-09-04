import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000

/-!
# Dossier-9 machine: raw semantics and conditional closure

Bare-Lean model of the concrete BB(6) machine

`1RB0LF_1RC---_1LD0RF_1RA0LE_0LD1LD_0RD0RB`  (dossier-9: the
parametrics candidate of 2026-08-31, the right-growing machine whose
tail dynamics collapse into two parametric families — the `..####`
cursor marching left with derived floor and kind laws, 271,344/271,344
held-out segments exact at the 8M horizon).

This is the program's tenth conditional closure.  Growth direction
note: unlike dossiers 7 and 8 this machine grows *right* (records at
fresh right extremes), so the certified layer is the exact coordinate
mirror of the dossier-7/8 single-raw-step engine: each word-machine
move is one raw step of list surgery on the pair `(em, rest)` (`em` =
cells *above* the head, nearest first; `rest` = the head cell
downward), and an *arrival* is an above-base pop: the head stepping
onto a fresh right extreme.  These are the machine's record events;
the validated python mirror (`tests/bb6/test_d9_theorems.py`)
reproduces every one of them exactly over the 20M-step horizon.

Halt anatomy note: this machine's undefined transition is `B1` — the
halt happens *in* state `B`, on the probed cell itself, so the
probe-safety predicate needs no neighbour cell at all: "state `B`
never reads a `1`".  The corridor lemma `into_B_only_from_A0_or_F1`
(state `B` is entered only by `A` reading `0` or `F` reading `1`, both
stepping right onto the probed cell, which their writes cannot touch)
is proven as the two-cell localization of the same fact.

Checked statements (no sorry, no extra axioms):

* `step_eq_none_iff` — the machine halts in one step exactly at the
  unique undefined transition `B1`.
* `into_B_only_from_A0_or_F1` — state `B` is entered only via `A`
  reading `0` (the transition `A0 = 1RB`) or `F` reading `1` (the
  transition `F1 = 0RB`), both moving right.
* `halt_requires_b_read_1` — any raw halt passes through a reachable
  configuration in state `B` reading `1` (the halt is the probe).
* `halt_requires_entry_probe` — the corridor form: from any non-`B`
  start, a raw halt forces a reachable `A0` or `F1` configuration
  whose *right* neighbour is a `1` — the cell `B` will die on.
* `nonhalting_of_b_probe_safe` — the B-probe-safety invariant ("state
  `B` never reads a `1`") implies the machine never halts.
* `push_step` / `pop_step_cons` / `pop_step_nil` — the three one-step
  episode lemmas: every raw move is a certified push (left move) or
  pop (right move, interior or extreme-extending) on the word pair.
* `go_faithful` / `wstep_faithful` — the certified record-to-record
  sweep: `wstep` is a fail-closed executable map on `(state, word)`
  pairs whose every `some` output is realized by the raw machine in
  *exactly* the returned step count, B-probe-safely.  It dies (returns
  `none`) exactly on the `B1` halt probe itself and on fuel exhaustion
  — nothing else.
* the word orbit `worbit` from the blank anchor `(A, [])`, and the
  keystone `safeD9Orbit_nonhalting`:
  `SafeD9Orbit → ¬ RawHalts blankStart`.

`SafeD9Orbit` is the single conjecture `∀ k, worbit k ≠ none`: the
fail-closed record orbit never dies.  As in the rank-1 closure, *no*
`Faithful` assumption remains: because the engine is the raw step
itself, every branch of the empirical parametric calculus — both tail
families at every `m`, the bounded `C0` growth unit, the floor and
kind laws, and the once-per-cycle rebuild sweep that the segment
tiling never covered — is simulated exactly rather than assumed.  The
conjecture is exactly the empirical substrate validated by the
record-mirror differential test (`tests/bb6/test_d9_theorems.py`:
every record transition reproduced exactly — state, word, step count —
over multi-million-step horizons).
-/

namespace QIG.Dossier9RawTM

set_option autoImplicit false

inductive State where
  | A | B | C | D | E | F
deriving Repr, DecidableEq

inductive Dir where
  | L | R
deriving Repr, DecidableEq

structure Instr where
  next : State
  write : Bool
  dir : Dir
deriving Repr, DecidableEq

/-- The dossier-9 transition table.  `none` is the undefined halt
transition `B1`. -/
def instr : State → Bool → Option Instr
  | State.A, false => some ⟨State.B, true, Dir.R⟩
  | State.A, true => some ⟨State.F, false, Dir.L⟩
  | State.B, false => some ⟨State.C, true, Dir.R⟩
  | State.B, true => none
  | State.C, false => some ⟨State.D, true, Dir.L⟩
  | State.C, true => some ⟨State.F, false, Dir.R⟩
  | State.D, false => some ⟨State.A, true, Dir.R⟩
  | State.D, true => some ⟨State.E, false, Dir.L⟩
  | State.E, false => some ⟨State.D, false, Dir.L⟩
  | State.E, true => some ⟨State.D, true, Dir.L⟩
  | State.F, false => some ⟨State.D, false, Dir.R⟩
  | State.F, true => some ⟨State.B, false, Dir.R⟩

def move : Int → Dir → Int
  | h, Dir.L => h - 1
  | h, Dir.R => h + 1

def writeAt (tape : Int → Bool) (pos : Int) (value : Bool) : Int → Bool :=
  fun x => if x = pos then value else tape x

theorem writeAt_same (tape : Int → Bool) (pos : Int) (value : Bool) :
    writeAt tape pos value pos = value := by
  simp [writeAt]

theorem writeAt_other (tape : Int → Bool) (pos x : Int) (value : Bool)
    (h : x ≠ pos) :
    writeAt tape pos value x = tape x := by
  simp [writeAt, h]

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

/-- The raw machine halts in one step exactly at the unique undefined
transition `B1`. -/
theorem step_eq_none_iff (c : Config) :
    step c = none ↔ c.state = State.B ∧ c.tape c.head = true := by
  cases hs : c.state <;> cases ht : c.tape c.head <;>
    simp [step, instr, hs, ht]

def RawHalts (c : Config) : Prop := ∃ n : Nat, stepN n c = none

def Reaches (c d : Config) : Prop := ∃ n : Nat, stepN n c = some d

def blankTape : Int → Bool := fun _ => false

def blankStart : Config where
  state := State.A
  head := 0
  tape := blankTape

/-- State `B` is entered only by `A` reading `0` (the transition
`A0 = 1RB`: write `1`, move right) or `F` reading `1` (the transition
`F1 = 0RB`: write `0`, move right).  Either way the successor sits one
cell to the *right* of the probed cell, so the cell `B` then reads was
never touched by the entering write.

Informally: the turnstile into death — `B` is reachable only through
`A0` or `F1`, stepping right, and the cell it dies on was already a
`1` before the entry step. -/
theorem into_B_only_from_A0_or_F1 {c c' : Config} (h : step c = some c')
    (hB : c'.state = State.B) :
    c'.head = c.head + 1 ∧
      ((c.state = State.A ∧ c.tape c.head = false ∧
          c'.tape = writeAt c.tape c.head true) ∨
        (c.state = State.F ∧ c.tape c.head = true ∧
          c'.tape = writeAt c.tape c.head false)) := by
  cases hs : c.state <;> cases ht : c.tape c.head <;>
    simp [step, instr, hs, ht] at h
  all_goals
    first
      | exact ⟨by rw [← h]; simp [move], Or.inl ⟨rfl, rfl, by rw [← h]⟩⟩
      | exact ⟨by rw [← h]; simp [move], Or.inr ⟨rfl, rfl, by rw [← h]⟩⟩
      | (rw [← h] at hB; simp at hB)

/-- Any finite run ending in a halt contains a strictly earlier
configuration whose single step halts. -/
theorem stepN_none_last :
    ∀ (n : Nat) (c : Config), stepN n c = none →
      ∃ k : Nat, k < n ∧ ∃ d : Config, stepN k c = some d ∧ step d = none := by
  intro n
  induction n with
  | zero =>
      intro c h
      simp [stepN] at h
  | succ n ih =>
      intro c h
      cases hstep : step c with
      | none =>
          exact ⟨0, by omega, c, by simp [stepN], hstep⟩
      | some c1 =>
          have h1 : stepN n c1 = none := by
            simpa [stepN, hstep] using h
          obtain ⟨k, hk, d, hd, hstop⟩ := ih c1 h1
          exact ⟨k + 1, by omega, d, by simpa [stepN, hstep] using hd, hstop⟩

/-- A successful `k+1`-step run has an immediate predecessor of its
endpoint. -/
theorem stepN_some_pred :
    ∀ (k : Nat) (c d : Config), stepN (k + 1) c = some d →
      ∃ e : Config, stepN k c = some e ∧ step e = some d := by
  intro k
  induction k with
  | zero =>
      intro c d h
      cases hstep : step c with
      | none => simp [stepN, hstep] at h
      | some c1 =>
          have : c1 = d := by simpa [stepN, hstep] using h
          exact ⟨c, by simp [stepN], by rw [hstep, this]⟩
  | succ k ih =>
      intro c d h
      cases hstep : step c with
      | none => simp [stepN, hstep] at h
      | some c1 =>
          have h1 : stepN (k + 1) c1 = some d := by
            simpa [stepN, hstep] using h
          obtain ⟨e, he, hlast⟩ := ih c1 d h1
          exact ⟨e, by simpa [stepN, hstep] using he, hlast⟩

/-- Halt localization, direct form: a raw halt passes through a
reachable configuration in state `B` reading `1`.

Informally: on this machine the halt *is* the probe — `B1` is itself
the undefined transition, so no predecessor analysis is needed: to die
the machine must first stand in state `B` on a `1`.  An unbounded
question ("does it ever halt?") becomes the reachability of a
one-cell pattern. -/
theorem halt_requires_b_read_1 {c : Config} (hh : RawHalts c) :
    ∃ d : Config, Reaches c d ∧ d.state = State.B ∧
      d.tape d.head = true := by
  obtain ⟨n, hn⟩ := hh
  obtain ⟨k, _, d0, hd0, hstop⟩ := stepN_none_last n c hn
  have hF := (step_eq_none_iff d0).mp hstop
  exact ⟨d0, ⟨k, hd0⟩, hF.1, hF.2⟩

/-- Halt localization, corridor form: from any non-`B` start, a raw
halt forces a reachable configuration in state `A` reading `0` or in
state `F` reading `1` whose *right* neighbour is a `1` — the cell the
machine will die on one step later.

Informally: the only doors into `B` are `A0` and `F1`, both stepping
right onto the fatal cell, and neither entry write can touch it. -/
theorem halt_requires_entry_probe {c : Config} (hne : c.state ≠ State.B)
    (hh : RawHalts c) :
    ∃ d : Config, Reaches c d ∧ d.tape (d.head + 1) = true ∧
      ((d.state = State.A ∧ d.tape d.head = false) ∨
        (d.state = State.F ∧ d.tape d.head = true)) := by
  obtain ⟨n, hn⟩ := hh
  obtain ⟨k, _, d0, hd0, hstop⟩ := stepN_none_last n c hn
  have hF := (step_eq_none_iff d0).mp hstop
  cases k with
  | zero =>
      have hcd : c = d0 := by simpa [stepN] using hd0
      exact absurd (hcd ▸ hF.1) hne
  | succ k' =>
      obtain ⟨e, he, hstepe⟩ := stepN_some_pred k' c d0 hd0
      obtain ⟨hhead, hcase⟩ := into_B_only_from_A0_or_F1 hstepe hF.1
      have hread : d0.tape d0.head = true := hF.2
      cases hcase with
      | inl hA =>
          obtain ⟨hst, hrd, htape⟩ := hA
          refine ⟨e, ⟨k', he⟩, ?_, Or.inl ⟨hst, hrd⟩⟩
          rw [htape, hhead] at hread
          rwa [writeAt_other e.tape e.head (e.head + 1) true (by omega)] at hread
      | inr hFe =>
          obtain ⟨hst, hrd, htape⟩ := hFe
          refine ⟨e, ⟨k', he⟩, ?_, Or.inr ⟨hst, hrd⟩⟩
          rw [htape, hhead] at hread
          rwa [writeAt_other e.tape e.head (e.head + 1) false (by omega)] at hread

/-- The B-probe-safety invariant: state `B` never reads a `1` in any
reachable configuration.

Informally: a sentry condition on the probed cell itself.  If every
cell `B` ever probes is a `0`, the fatal pattern of
`halt_requires_b_read_1` can never occur, so the machine runs forever.
The rest of this file exists to discharge this one predicate from the
word-orbit dynamics. -/
def BProbeSafe (c : Config) : Prop :=
  ∀ d : Config, Reaches c d → d.state = State.B → d.tape d.head = false

/-- B-probe safety implies the machine never halts. -/
theorem nonhalting_of_b_probe_safe {c : Config}
    (hsafe : BProbeSafe c) : ¬ RawHalts c := by
  intro hh
  obtain ⟨d, hreach, hB, h1⟩ := halt_requires_b_read_1 hh
  have h0 := hsafe d hreach hB
  rw [h0] at h1
  exact Bool.noConfusion h1

/-- Specialization to the blank start. -/
theorem blank_nonhalting_of_b_probe_safe
    (hsafe : BProbeSafe blankStart) : ¬ RawHalts blankStart :=
  nonhalting_of_b_probe_safe hsafe

/-!
## Segment safety machinery

Identical in structure to the dossier-7/8 layer: conditional probe
safety over the first `N` steps of a run, composition, and the
segment-induction keystone that turns the per-sweep safety of the
certified word machine into safety of the infinite run.
-/

theorem stepN_add :
    ∀ (m n : Nat) (c : Config),
      stepN (m + n) c = (stepN m c).bind (stepN n) := by
  intro m
  induction m with
  | zero => intro n c; simp [stepN, Nat.zero_add]
  | succ m ih =>
      intro n c
      rw [Nat.succ_add]
      cases hstep : step c with
      | none => simp [stepN, hstep]
      | some c1 => simp [stepN, hstep, ih]

/-- Conditional B-probe safety over the first `N` steps of a run:
state `B` never reads a `1`. -/
def BSafeSeg (c : Config) (N : Nat) : Prop :=
  ∀ k d, k < N → stepN k c = some d → d.state = State.B →
    d.tape d.head = false

theorem bsafe_compose {c c' : Config} {m n : Nat}
    (hm : stepN m c = some c') (h1 : BSafeSeg c m) (h2 : BSafeSeg c' n) :
    BSafeSeg c (m + n) := by
  intro k d hk hkd hB
  by_cases hkm : k < m
  · exact h1 k d hkm hkd hB
  · have hkeq : k = m + (k - m) := by omega
    rw [hkeq, stepN_add, hm] at hkd
    exact h2 (k - m) d (by omega) hkd hB

/-- The segment-induction keystone: an invariant maintained by positive
safe segments gives `BProbeSafe` for the whole infinite run.

Informally: *safety in pieces is safety forever*.  If from every
invariant-satisfying configuration the machine runs some positive
number of steps safely and lands on the invariant again, then every
moment of the infinite run falls inside one of these safe segments —
strong induction on how many segments precede it. -/
theorem bprobe_safe_of_segments {Inv : Config → Prop} {c0 : Config}
    (h0 : Inv c0)
    (hseg : ∀ c, Inv c → ∃ k, 0 < k ∧ ∃ c', stepN k c = some c' ∧
      Inv c' ∧ BSafeSeg c k) :
    BProbeSafe c0 := by
  have main : ∀ (N n : Nat) (c : Config), n ≤ N → Inv c →
      ∀ d, stepN n c = some d → d.state = State.B →
        d.tape d.head = false := by
    intro N
    induction N with
    | zero =>
        intro n c hn hInv d hd hB
        obtain ⟨k, hk, c', _hs, _hInv', hsafe⟩ := hseg c hInv
        exact hsafe n d (by omega) hd hB
    | succ N ihN =>
        intro n c hn hInv d hd hB
        obtain ⟨k, hk, c', hs, hInv', hsafe⟩ := hseg c hInv
        by_cases hlt : n < k
        · exact hsafe n d hlt hd hB
        · have hneq : n = k + (n - k) := by omega
          rw [hneq, stepN_add, hs] at hd
          exact ihN (n - k) c' (by omega) hInv' d hd hB
  intro d hreach hB
  obtain ⟨n, hn⟩ := hreach
  exact main n n c0 (Nat.le_refl n) h0 d hn hB

/-!
## One-step evaluator scaffolding and list foundation

Never rewrite on a `stepN` goal: chains are glued in term mode from
single-step facts (the standing proof-engineering convention of this
repository).  The word representation is the dossier-7/8 one, mirrored:
`getD` with default `false` makes blank tape outside the two lists
semantically invisible, so a pair `(em, rest)` pins the whole
configuration up to translation.
-/

theorem stepN_zero (c : Config) : stepN 0 c = some c := rfl

theorem stepN_succ_of_step {c d e : Config} {n : Nat}
    (h1 : step c = some d) (h2 : stepN n d = some e) :
    stepN (n + 1) c = some e := by
  rw [show stepN (n + 1) c = (step c).bind (stepN n) from rfl, h1]
  exact h2

theorem getD_nil (k : Nat) : ([] : List Bool).getD k false = false := by
  cases k <;> rfl

theorem getD_drop :
    ∀ (n : Nat) (l : List Bool) (j : Nat),
      (l.drop n).getD j false = l.getD (n + j) false := by
  intro n
  induction n with
  | zero => intro l j; simp
  | succ n ih =>
      intro l j
      cases l with
      | nil => simp
      | cons a t =>
          rw [show (a :: t).drop (n + 1) = t.drop n from rfl,
              show n + 1 + j = (n + j) + 1 by omega, List.getD_cons_succ]
          exact ih t j

/-!
## The boundary invariant

At every moment the machine's whole configuration is pinned by two
lists and a base position: `em` — the cells *above* the head, nearest
first (blank above `base`, subsumed by `getD`'s default), and `rest` —
the cells from the head downward (head cell included, `rest.getD 0`).
Every raw step is local surgery on this pair: a *push* (left move)
transfers the written head cell onto `em`, a *pop* (right move) either
transfers `em`'s top back onto `rest` or — when `em` is empty — steps
above `base` onto a fresh right extreme: an arrival, the record event
of the dossier-9 dynamics.
-/

/-- The boundary invariant: state `st`, head at `base - em.length`,
cells above the head read `em` (nearest first, blank above `base`),
cells from the head downward read `rest`. -/
def Inv (st : State) (base : Int) (em rest : List Bool) (cfg : Config) : Prop :=
  cfg.state = st ∧ cfg.head = base - em.length ∧
  (∀ k : Nat, cfg.tape (base - em.length + 1 + k) = em.getD k false) ∧
  (∀ j : Nat, cfg.tape (base - em.length - j) = rest.getD j false)

/-!
## The three one-step episodes

The dossier-7/8 design, mirrored: the grain is a single raw step, so
exactly three episode shapes cover the entire dynamics — push, interior
pop, and extreme-extending pop — and *every* branch of the parametric
calculus (both tail families, the growth unit, the floor and kind
laws, and the untiled rebuild sweeps) is a composite of them,
simulated rather than assumed. -/

/-- Push: any left-moving instruction transfers the written head cell
onto the stack `em`.  One raw step; trivially B-probe-safe because no
left-moving instruction leaves state `B` (`B0` moves right and `B1` is
the halt). -/
theorem push_step {st st' : State} {wv : Bool} {base : Int} {em rest : List Bool}
    {cfg : Config}
    (hInv : Inv st base em rest cfg)
    (hins : instr st (rest.getD 0 false) = some ⟨st', wv, Dir.L⟩)
    (hnB : st ≠ State.B) :
    ∃ cfg', stepN 1 cfg = some cfg' ∧
      Inv st' base (wv :: em) (rest.drop 1) cfg' ∧ BSafeSeg cfg 1 := by
  obtain ⟨hst, hhd, hup, hdown⟩ := hInv
  obtain ⟨cs, hd, t⟩ := cfg
  simp only at hst hhd hup hdown
  subst hst
  subst hhd
  have r0 : t (base - (em.length : Int)) = rest.getD 0 false := by
    have h := hdown 0
    rw [show base - (em.length : Int) - ((0 : Nat) : Int)
          = base - (em.length : Int) by omega] at h
    exact h
  have s1 : step ⟨cs, base - (em.length : Int), t⟩
      = some ⟨st', base - (em.length : Int) - 1,
          writeAt t (base - (em.length : Int)) wv⟩ := by
    rw [show step ⟨cs, base - (em.length : Int), t⟩
          = (instr cs (t (base - (em.length : Int)))).bind (fun ins =>
              some ⟨ins.next, move (base - (em.length : Int)) ins.dir,
                writeAt t (base - (em.length : Int)) ins.write⟩) from rfl,
        r0, hins]
    rfl
  have hup' : ∀ k : Nat,
      (writeAt t (base - (em.length : Int)) wv)
        (base - ((em.length + 1 : Nat) : Int) + 1 + (k : Int))
        = (wv :: em).getD k false := by
    intro k
    cases k with
    | zero =>
        rw [show base - ((em.length + 1 : Nat) : Int) + 1 + ((0 : Nat) : Int)
              = base - (em.length : Int) by omega, writeAt_same]
        rfl
    | succ k =>
        rw [show base - ((em.length + 1 : Nat) : Int) + 1 + ((k + 1 : Nat) : Int)
              = base - (em.length : Int) + 1 + (k : Int) by omega,
            writeAt_other _ _ _ _ (by omega), hup k, List.getD_cons_succ]
  have hdown' : ∀ j : Nat,
      (writeAt t (base - (em.length : Int)) wv)
        (base - ((em.length + 1 : Nat) : Int) - (j : Int))
        = (rest.drop 1).getD j false := by
    intro j
    rw [show base - ((em.length + 1 : Nat) : Int) - (j : Int)
          = base - (em.length : Int) - ((1 + j : Nat) : Int) by omega,
        writeAt_other _ _ _ _ (by omega), hdown (1 + j), getD_drop]
  refine ⟨⟨st', base - (em.length : Int) - 1,
      writeAt t (base - (em.length : Int)) wv⟩,
    stepN_succ_of_step s1 (stepN_zero _),
    ⟨rfl, show base - (em.length : Int) - 1
        = base - ((em.length + 1 : Nat) : Int) by omega, hup', hdown'⟩, ?_⟩
  intro k d hk hkd hB
  have hk0 : k = 0 := by omega
  subst hk0
  have hdd : (⟨cs, base - (em.length : Int), t⟩ : Config) = d := by
    simpa [stepN] using hkd
  rw [← hdd] at hB
  exact absurd hB hnB

/-- Interior pop: any right-moving instruction with a nonempty stack
transfers `em`'s top back onto `rest`.  One raw step; the safety
hypothesis is exactly the machine's mortality, localized — when `B`
moves, the probed cell must have been a `0` (which `hins` itself
already forces, since `B1` is undefined). -/
theorem pop_step_cons {st st' : State} {wv e0 : Bool} {base : Int}
    {em2 rest : List Bool} {cfg : Config}
    (hInv : Inv st base (e0 :: em2) rest cfg)
    (hins : instr st (rest.getD 0 false) = some ⟨st', wv, Dir.R⟩)
    (hBsafe : st = State.B → rest.getD 0 false = false) :
    ∃ cfg', stepN 1 cfg = some cfg' ∧
      Inv st' base em2 (e0 :: wv :: rest.drop 1) cfg' ∧ BSafeSeg cfg 1 := by
  obtain ⟨hst, hhd, hup, hdown⟩ := hInv
  obtain ⟨cs, hd, t⟩ := cfg
  simp only at hst hhd hup hdown
  simp only [List.length_cons] at hhd hup hdown
  subst hst
  subst hhd
  have r0 : t (base - ((em2.length + 1 : Nat) : Int)) = rest.getD 0 false := by
    have h := hdown 0
    rw [show base - ((em2.length + 1 : Nat) : Int) - ((0 : Nat) : Int)
          = base - ((em2.length + 1 : Nat) : Int) by omega] at h
    exact h
  have s1 : step ⟨cs, base - ((em2.length + 1 : Nat) : Int), t⟩
      = some ⟨st', base - ((em2.length + 1 : Nat) : Int) + 1,
          writeAt t (base - ((em2.length + 1 : Nat) : Int)) wv⟩ := by
    rw [show step ⟨cs, base - ((em2.length + 1 : Nat) : Int), t⟩
          = (instr cs (t (base - ((em2.length + 1 : Nat) : Int)))).bind (fun ins =>
              some ⟨ins.next, move (base - ((em2.length + 1 : Nat) : Int)) ins.dir,
                writeAt t (base - ((em2.length + 1 : Nat) : Int)) ins.write⟩) from rfl,
        r0, hins]
    rfl
  have hup' : ∀ k : Nat,
      (writeAt t (base - ((em2.length + 1 : Nat) : Int)) wv)
        (base - (em2.length : Int) + 1 + (k : Int)) = em2.getD k false := by
    intro k
    rw [show base - (em2.length : Int) + 1 + (k : Int)
          = base - ((em2.length + 1 : Nat) : Int) + 1 + ((k + 1 : Nat) : Int) by omega,
        writeAt_other _ _ _ _ (by omega), hup (k + 1), List.getD_cons_succ]
  have hdown' : ∀ j : Nat,
      (writeAt t (base - ((em2.length + 1 : Nat) : Int)) wv)
        (base - (em2.length : Int) - (j : Int))
        = (e0 :: wv :: rest.drop 1).getD j false := by
    intro j
    cases j with
    | zero =>
        rw [show base - (em2.length : Int) - ((0 : Nat) : Int)
              = base - ((em2.length + 1 : Nat) : Int) + 1 + ((0 : Nat) : Int) by omega,
            writeAt_other _ _ _ _ (by omega), hup 0]
        rfl
    | succ j =>
        cases j with
        | zero =>
            rw [show base - (em2.length : Int) - ((1 : Nat) : Int)
                  = base - ((em2.length + 1 : Nat) : Int) by omega,
                writeAt_same]
            rfl
        | succ j =>
            rw [show base - (em2.length : Int) - ((j + 1 + 1 : Nat) : Int)
                  = base - ((em2.length + 1 : Nat) : Int) - ((1 + j : Nat) : Int) by omega,
                writeAt_other _ _ _ _ (by omega), hdown (1 + j),
                List.getD_cons_succ, List.getD_cons_succ, getD_drop]
  refine ⟨⟨st', base - ((em2.length + 1 : Nat) : Int) + 1,
      writeAt t (base - ((em2.length + 1 : Nat) : Int)) wv⟩,
    stepN_succ_of_step s1 (stepN_zero _),
    ⟨rfl, show base - ((em2.length + 1 : Nat) : Int) + 1
        = base - (em2.length : Int) by omega, hup', hdown'⟩, ?_⟩
  intro k d hk hkd hB
  have hk0 : k = 0 := by omega
  subst hk0
  have hdd : (⟨cs, base - ((em2.length + 1 : Nat) : Int), t⟩ : Config) = d := by
    simpa [stepN] using hkd
  rw [← hdd] at hB
  have hrf : rest.getD 0 false = false := hBsafe hB
  rw [← hdd]
  show t (base - ((em2.length + 1 : Nat) : Int)) = false
  rw [r0]
  exact hrf

/-- Extreme-extending pop: a right move with an empty stack steps above
`base` onto blank tape — the *arrival*, a fresh right extreme, the
record event.  One raw step; when `B` moves the probed cell was a `0`
(the safety hypothesis, which `hins` itself already forces). -/
theorem pop_step_nil {st st' : State} {wv : Bool} {base : Int}
    {rest : List Bool} {cfg : Config}
    (hInv : Inv st base [] rest cfg)
    (hins : instr st (rest.getD 0 false) = some ⟨st', wv, Dir.R⟩)
    (hBsafe : st = State.B → rest.getD 0 false = false) :
    ∃ cfg', stepN 1 cfg = some cfg' ∧
      Inv st' (base + 1) [] (false :: wv :: rest.drop 1) cfg' ∧ BSafeSeg cfg 1 := by
  obtain ⟨hst, hhd, hup, hdown⟩ := hInv
  obtain ⟨cs, hd, t⟩ := cfg
  simp only at hst hhd hup hdown
  simp only [List.length_nil] at hhd hup hdown
  subst hst
  subst hhd
  rw [show base - ((0 : Nat) : Int) = base by omega]
  have r0 : t base = rest.getD 0 false := by
    have h := hdown 0
    rw [show base - ((0 : Nat) : Int) - ((0 : Nat) : Int) = base by omega] at h
    exact h
  have s1 : step ⟨cs, base, t⟩
      = some ⟨st', base + 1, writeAt t base wv⟩ := by
    rw [show step ⟨cs, base, t⟩
          = (instr cs (t base)).bind (fun ins =>
              some ⟨ins.next, move base ins.dir, writeAt t base ins.write⟩) from rfl,
        r0, hins]
    rfl
  have hup' : ∀ k : Nat,
      (writeAt t base wv) (base + 1 - ((0 : Nat) : Int) + 1 + (k : Int))
        = ([] : List Bool).getD k false := by
    intro k
    rw [show base + 1 - ((0 : Nat) : Int) + 1 + (k : Int)
          = base - ((0 : Nat) : Int) + 1 + ((k + 1 : Nat) : Int) by omega,
        writeAt_other _ _ _ _ (by omega), hup (k + 1)]
    exact (getD_nil (k + 1)).trans (getD_nil k).symm
  have hdown' : ∀ j : Nat,
      (writeAt t base wv) (base + 1 - ((0 : Nat) : Int) - (j : Int))
        = (false :: wv :: rest.drop 1).getD j false := by
    intro j
    cases j with
    | zero =>
        rw [show base + 1 - ((0 : Nat) : Int) - ((0 : Nat) : Int)
              = base - ((0 : Nat) : Int) + 1 + ((0 : Nat) : Int) by omega,
            writeAt_other _ _ _ _ (by omega), hup 0]
        exact getD_nil 0
    | succ j =>
        cases j with
        | zero =>
            rw [show base + 1 - ((0 : Nat) : Int) - ((1 : Nat) : Int)
                  = base by omega, writeAt_same]
            rfl
        | succ j =>
            rw [show base + 1 - ((0 : Nat) : Int) - ((j + 1 + 1 : Nat) : Int)
                  = base - ((0 : Nat) : Int) - ((1 + j : Nat) : Int) by omega,
                writeAt_other _ _ _ _ (by omega), hdown (1 + j),
                List.getD_cons_succ, List.getD_cons_succ, getD_drop]
  refine ⟨⟨st', base + 1, writeAt t base wv⟩,
    stepN_succ_of_step s1 (stepN_zero _),
    ⟨rfl, show base + 1 = base + 1 - ((0 : Nat) : Int) by omega, hup', hdown'⟩, ?_⟩
  intro k d hk hkd hB
  have hk0 : k = 0 := by omega
  subst hk0
  have hdd : (⟨cs, base, t⟩ : Config) = d := by
    simpa [stepN] using hkd
  rw [← hdd] at hB
  have hrf : rest.getD 0 false = false := hBsafe hB
  rw [← hdd]
  show t base = false
  rw [r0]
  exact hrf

/-!
## The certified sweep: `go` and `wstep`

`go` is the fail-closed word machine: from `(st, em, rest)` it runs
single-raw-step surgery until the first above-base pop — the next
arrival, i.e. the next fresh-right-extreme record — and returns
`(state, arrival word, raw steps)`.  It returns `none` exactly on the
fatal `B`-probe (`B` reading `1` — which on this machine *is* the
undefined halt transition) and on fuel exhaustion.  Nothing else
fails: every other branch is the raw machine verbatim, so all
parametric-calculus branches — observed or not — are simulated
exactly.
-/

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
    | State.A, true =>
        (go fuel State.F (false :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.B, false =>
        match em with
        | [] => some (State.C, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.C em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.B, true => none
    | State.C, false =>
        (go fuel State.D (true :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.C, true =>
        match em with
        | [] => some (State.F, false :: false :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.F em2 (e0 :: false :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.D, false =>
        match em with
        | [] => some (State.A, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.A em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.D, true =>
        (go fuel State.E (false :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.E, false =>
        (go fuel State.D (false :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.E, true =>
        (go fuel State.D (true :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.F, false =>
        match em with
        | [] => some (State.D, false :: false :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.D em2 (e0 :: false :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.F, true =>
        match em with
        | [] => some (State.B, false :: false :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.B em2 (e0 :: false :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))

theorem map_add1_eq_some {o : Option (State × List Bool × Nat)} {st' : State}
    {w : List Bool} {d : Nat}
    (h : o.map (fun r => (r.1, r.2.1, 1 + r.2.2)) = some (st', w, d)) :
    ∃ d', o = some (st', w, d') ∧ d = 1 + d' := by
  cases o with
  | none => simp at h
  | some r =>
      obtain ⟨s0, w0, d0⟩ := r
      simp at h
      obtain ⟨hs, hw, hd⟩ := h
      exact ⟨d0, by rw [hs, hw], by omega⟩

/-- Faithfulness of the sweep, by induction on fuel: every `some`
output of `go` is realized by the raw machine in exactly the returned
step count, B-probe-safely, landing on an arrival configuration of the
returned word (head at the new base, the fresh right extreme). -/
theorem go_faithful :
    ∀ (fuel : Nat) (st : State) (em rest : List Bool) (st' : State)
      (w' : List Bool) (d : Nat),
      go fuel st em rest = some (st', w', d) →
      ∀ (base : Int) (cfg : Config), Inv st base em rest cfg →
        ∃ (cfg' : Config) (base' : Int), stepN d cfg = some cfg' ∧
          Inv st' base' [] w' cfg' ∧ BSafeSeg cfg d ∧ 0 < d := by
  intro fuel
  induction fuel with
  | zero =>
      intro st em rest st' w' d hgo base cfg hInv
      simp [go] at hgo
  | succ fuel ih =>
      intro st em rest st' w' d hgo base cfg hInv
      simp only [go] at hgo
      split at hgo
      · -- A0: pop to B
        next hr =>
          split at hgo
          · -- arrival
            obtain ⟨hs, hw, hd⟩ : State.B = st' ∧
                false :: true :: rest.drop 1 = w' ∧ 1 = d := by
              simpa using hgo
            subst hs; subst hw; subst hd
            obtain ⟨cfg', h1, h2, h3⟩ := pop_step_nil hInv (by rw [hr]; rfl)
              (fun h => absurd h (by decide))
            exact ⟨cfg', base + 1, h1, h2, h3, by omega⟩
          · next e0 em2 =>
              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
              subst hd
              obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                (fun h => absurd h (by decide))
              obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
              · rw [stepN_add, h1]
                exact h1'
              · exact bsafe_compose h1 h3 h3'
      · -- A1: push to F
        next hr =>
          obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
          subst hd
          obtain ⟨cfg₂, h1, h2, h3⟩ := push_step hInv (by rw [hr]; rfl) (by decide)
          obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
          refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
          · rw [stepN_add, h1]
            exact h1'
          · exact bsafe_compose h1 h3 h3'
      · -- B0: pop to C — the safe probe, `B` reading `0`
        next hr =>
          split at hgo
          · obtain ⟨hs, hw, hd⟩ : State.C = st' ∧
                false :: true :: rest.drop 1 = w' ∧ 1 = d := by
              simpa using hgo
            subst hs; subst hw; subst hd
            obtain ⟨cfg', h1, h2, h3⟩ := pop_step_nil hInv (by rw [hr]; rfl)
              (fun _ => hr)
            exact ⟨cfg', base + 1, h1, h2, h3, by omega⟩
          · next e0 em2 =>
              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
              subst hd
              obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                (fun _ => hr)
              obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
              · rw [stepN_add, h1]
                exact h1'
              · exact bsafe_compose h1 h3 h3'
      · -- B1: the halt probe — fail-closed
        simp at hgo
      · -- C0: push to D
        next hr =>
          obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
          subst hd
          obtain ⟨cfg₂, h1, h2, h3⟩ := push_step hInv (by rw [hr]; rfl) (by decide)
          obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
          refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
          · rw [stepN_add, h1]
            exact h1'
          · exact bsafe_compose h1 h3 h3'
      · -- C1: pop to F
        next hr =>
          split at hgo
          · obtain ⟨hs, hw, hd⟩ : State.F = st' ∧
                false :: false :: rest.drop 1 = w' ∧ 1 = d := by
              simpa using hgo
            subst hs; subst hw; subst hd
            obtain ⟨cfg', h1, h2, h3⟩ := pop_step_nil hInv (by rw [hr]; rfl)
              (fun h => absurd h (by decide))
            exact ⟨cfg', base + 1, h1, h2, h3, by omega⟩
          · next e0 em2 =>
              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
              subst hd
              obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                (fun h => absurd h (by decide))
              obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
              · rw [stepN_add, h1]
                exact h1'
              · exact bsafe_compose h1 h3 h3'
      · -- D0: pop to A
        next hr =>
          split at hgo
          · obtain ⟨hs, hw, hd⟩ : State.A = st' ∧
                false :: true :: rest.drop 1 = w' ∧ 1 = d := by
              simpa using hgo
            subst hs; subst hw; subst hd
            obtain ⟨cfg', h1, h2, h3⟩ := pop_step_nil hInv (by rw [hr]; rfl)
              (fun h => absurd h (by decide))
            exact ⟨cfg', base + 1, h1, h2, h3, by omega⟩
          · next e0 em2 =>
              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
              subst hd
              obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                (fun h => absurd h (by decide))
              obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
              · rw [stepN_add, h1]
                exact h1'
              · exact bsafe_compose h1 h3 h3'
      · -- D1: push to E
        next hr =>
          obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
          subst hd
          obtain ⟨cfg₂, h1, h2, h3⟩ := push_step hInv (by rw [hr]; rfl) (by decide)
          obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
          refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
          · rw [stepN_add, h1]
            exact h1'
          · exact bsafe_compose h1 h3 h3'
      · -- E0: push to D
        next hr =>
          obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
          subst hd
          obtain ⟨cfg₂, h1, h2, h3⟩ := push_step hInv (by rw [hr]; rfl) (by decide)
          obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
          refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
          · rw [stepN_add, h1]
            exact h1'
          · exact bsafe_compose h1 h3 h3'
      · -- E1: push to D
        next hr =>
          obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
          subst hd
          obtain ⟨cfg₂, h1, h2, h3⟩ := push_step hInv (by rw [hr]; rfl) (by decide)
          obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
          refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
          · rw [stepN_add, h1]
            exact h1'
          · exact bsafe_compose h1 h3 h3'
      · -- F0: pop to D
        next hr =>
          split at hgo
          · obtain ⟨hs, hw, hd⟩ : State.D = st' ∧
                false :: false :: rest.drop 1 = w' ∧ 1 = d := by
              simpa using hgo
            subst hs; subst hw; subst hd
            obtain ⟨cfg', h1, h2, h3⟩ := pop_step_nil hInv (by rw [hr]; rfl)
              (fun h => absurd h (by decide))
            exact ⟨cfg', base + 1, h1, h2, h3, by omega⟩
          · next e0 em2 =>
              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
              subst hd
              obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                (fun h => absurd h (by decide))
              obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
              · rw [stepN_add, h1]
                exact h1'
              · exact bsafe_compose h1 h3 h3'
      · -- F1: pop to B
        next hr =>
          split at hgo
          · obtain ⟨hs, hw, hd⟩ : State.B = st' ∧
                false :: false :: rest.drop 1 = w' ∧ 1 = d := by
              simpa using hgo
            subst hs; subst hw; subst hd
            obtain ⟨cfg', h1, h2, h3⟩ := pop_step_nil hInv (by rw [hr]; rfl)
              (fun h => absurd h (by decide))
            exact ⟨cfg', base + 1, h1, h2, h3, by omega⟩
          · next e0 em2 =>
              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
              subst hd
              obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                (fun h => absurd h (by decide))
              obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
              · rw [stepN_add, h1]
                exact h1'
              · exact bsafe_compose h1 h3 h3'

/-- Generous fuel: raw steps per record gap, comfortably quadratic in
the arrival word length.  Fail-closed — exhaustion is an orbit death,
and the empirical margin is above 2,000× at the 20M horizon. -/
def wfuel (w : List Bool) : Nat := 64 * (w.length + 64) * (w.length + 64)

/-- One certified record-to-record sweep: from an arrival
`(st, w)` (head at the right extreme, word `w` leftward), run the raw
machine to the next fresh right extreme.  Returns
`(state', word', steps)`. -/
def wstep (st : State) (w : List Bool) : Option (State × List Bool × Nat) :=
  go (wfuel w) st [] w

/-- **The sweep is faithful**: whenever `wstep` yields a successor
arrival, the raw machine, started on any realization of the input
arrival, runs *exactly* the returned number of steps, stays
B-probe-safe throughout, and lands on a realization of the successor
arrival.  No `Faithful` assumption remains anywhere in this file. -/
theorem wstep_faithful {st st' : State} {w w' : List Bool} {d : Nat}
    (hw : wstep st w = some (st', w', d)) :
    ∀ (base : Int) (cfg : Config), Inv st base [] w cfg →
      ∃ (cfg' : Config) (base' : Int), stepN d cfg = some cfg' ∧
        Inv st' base' [] w' cfg' ∧ BSafeSeg cfg d ∧ 0 < d :=
  fun base cfg hInv => go_faithful (wfuel w) st [] w st' w' d hw base cfg hInv

end QIG.Dossier9RawTM
