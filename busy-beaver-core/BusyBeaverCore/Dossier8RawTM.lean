import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000

/-!
# Dossier-8 machine: raw semantics and conditional closure

Bare-Lean model of the concrete BB(6) machine

`1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE`  (dossier-8: the second of
the two ladder machines of 2026-08-31, the left-growing unary-counter
odometer with record family `1^a 0 1 0 1^b 0 (1 0)^k (1^4 0)^g 1^2` —
opposite ladder parity to dossier-7, plus the grand-epoch counter `g`).

This is the program's ninth conditional closure.  Growth direction
note: like dossier-7 this machine grows *left* (records at fresh left
extremes).  No mirrored semantics are needed: the certified layer
works at the single-raw-step grain, one grain finer than the rank-1
micro-episodes, where direction is subsumed entirely — each
word-machine move is one raw step of list surgery on the pair
`(em, rest)` (`em` = cells below the head, nearest first; `rest` = the
head cell upward), and an *arrival* is a below-base pop: the head
stepping onto a fresh left extreme, exactly the record events of the
validated dossier-8 law (`qgkit/bb6/d78_laws.py`, 3,879/3,879 record
transitions exact at 20M raw steps).

Checked statements (no sorry, no extra axioms):

* `step_eq_none_iff` — the machine halts in one step exactly at the
  unique undefined transition `F0`.
* `into_F_only_from_C0` — state `F` is entered only via `C` reading `0`
  (the transition `C0 = 1LF`: write `1`, move left).
* `halt_requires_c_probe_00` — any raw halt from a non-`F` start passes
  through a reachable configuration in state `C` reading `0` whose
  *left* neighbour is also `0`.
* `nonhalting_of_c_probe_safe` — the C-probe-safety invariant ("every
  `0` that state `C` reads has a `1` to its left") implies the machine
  never halts.
* `push_step` / `pop_step_cons` / `pop_step_nil` — the three one-step
  episode lemmas: every raw move is a certified push (right move) or
  pop (left move, interior or extreme-extending) on the word pair.
* `go_faithful` / `wstep_faithful` — the certified record-to-record
  sweep: `wstep` is a fail-closed executable map on `(state, word)`
  pairs whose every `some` output is realized by the raw machine in
  *exactly* the returned step count, C-probe-safely.  It dies (returns
  `none`) exactly on a fatal `C`-probe (a `0` read by `C` with no `1`
  guard on its left, the frontier case included), on the `F0` halt
  itself, and on fuel exhaustion — nothing else.
* the word orbit `worbit` from the blank anchor `(A, [])`, and the
  keystone `safeD8Orbit_nonhalting`:
  `SafeD8Orbit → ¬ RawHalts blankStart`.

`SafeD8Orbit` is the single conjecture `∀ k, worbit k ≠ none`: the
fail-closed record orbit never dies.  As in the rank-1 closure, *no*
`Faithful` assumption remains: because the engine is the raw step
itself, every branch of the empirical record law — drift, merge, the
minor renewals with their A-checkpoints, the epoch-incrementing grand
renewal and the grand funnel, and even the residues never exercised at
the 20M horizon (the odd-bottom ladder exhaustion `(4,B,4^g,2)`, the
`B`-odd grand renewal, every `g ≥ 2` grand renewal — the first such
event projects near `3 × 10^12` raw steps) — is simulated exactly
rather than assumed.  The conjecture is exactly the empirical
substrate validated by the record-mirror differential test
(`tests/bb6/test_d8_theorems.py`: every record transition reproduced
exactly — state, word, step count — over multi-million-step horizons,
with fuel margin above 1,700×).
-/

namespace QIG.Dossier8RawTM

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

/-- The dossier-8 transition table.  `none` is the undefined halt
transition `F0`. -/
def instr : State → Bool → Option Instr
  | State.A, false => some ⟨State.B, true, Dir.R⟩
  | State.A, true => some ⟨State.C, false, Dir.L⟩
  | State.B, false => some ⟨State.C, true, Dir.L⟩
  | State.B, true => some ⟨State.D, false, Dir.R⟩
  | State.C, false => some ⟨State.F, true, Dir.L⟩
  | State.C, true => some ⟨State.A, true, Dir.L⟩
  | State.D, false => some ⟨State.B, true, Dir.L⟩
  | State.D, true => some ⟨State.E, true, Dir.R⟩
  | State.E, false => some ⟨State.B, true, Dir.R⟩
  | State.E, true => some ⟨State.E, true, Dir.L⟩
  | State.F, false => none
  | State.F, true => some ⟨State.E, false, Dir.L⟩

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

/-- The raw machine halts in one step exactly at the unique undefined
transition `F0`. -/
theorem step_eq_none_iff (c : Config) :
    step c = none ↔ c.state = State.F ∧ c.tape c.head = false := by
  cases hs : c.state <;> cases ht : c.tape c.head <;>
    simp [step, instr, hs, ht]

def RawHalts (c : Config) : Prop := ∃ n : Nat, stepN n c = none

def Reaches (c d : Config) : Prop := ∃ n : Nat, stepN n c = some d

def blankTape : Int → Bool := fun _ => false

def blankStart : Config where
  state := State.A
  head := 0
  tape := blankTape

/-- State `F` is entered only by `C` reading `0` (the transition
`C0 = 1LF`): the predecessor is in state `C` on a `0`, and the
successor sits one cell to the left with the probed cell rewritten
to `1`.

Informally: the turnstile into death — `F` is reachable only through
`C` reading a `0`, stepping left over it.  So the final two
configurations of any halting run are completely determined. -/
theorem into_F_only_from_C0 {c c' : Config} (h : step c = some c')
    (hF : c'.state = State.F) :
    c.state = State.C ∧ c.tape c.head = false ∧
      c'.head = c.head - 1 ∧ c'.tape = writeAt c.tape c.head true := by
  cases hs : c.state <;> cases ht : c.tape c.head <;>
    simp [step, instr, hs, ht] at h
  all_goals
    first
      | exact ⟨rfl, rfl, by rw [← h]; simp [move], by rw [← h]⟩
      | (rw [← h] at hF; simp at hF)

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

/-- Halt localization: from any non-`F` start, a raw halt forces a
reachable configuration where `C` reads a `0` whose left neighbour is
also `0`.

Informally: *to die, the machine must first stand in state `C` on a
`0` with another `0` immediately to its left* — because the only door
into the halting state `F` is the transition `C0`, which writes a `1`
over the probed cell and steps left, so the cell `F` then dies on was
already `0` when `C` probed.  An unbounded question ("does it ever
halt?") becomes the reachability of a two-cell pattern. -/
theorem halt_requires_c_probe_00 {c : Config} (hne : c.state ≠ State.F)
    (hh : RawHalts c) :
    ∃ d : Config, Reaches c d ∧ d.state = State.C ∧
      d.tape d.head = false ∧ d.tape (d.head - 1) = false := by
  obtain ⟨n, hn⟩ := hh
  obtain ⟨k, _, d0, hd0, hstop⟩ := stepN_none_last n c hn
  have hF := (step_eq_none_iff d0).mp hstop
  cases k with
  | zero =>
      have hcd : c = d0 := by simpa [stepN] using hd0
      exact absurd (hcd ▸ hF.1) hne
  | succ k' =>
      obtain ⟨e, he, hstepe⟩ := stepN_some_pred k' c d0 hd0
      obtain ⟨hC, h0, hhead, htape⟩ := into_F_only_from_C0 hstepe hF.1
      refine ⟨e, ⟨k', he⟩, hC, h0, ?_⟩
      have hread : d0.tape d0.head = false := hF.2
      rw [htape, hhead] at hread
      rwa [writeAt_other e.tape e.head (e.head - 1) true (by omega)] at hread

/-- The C-probe-safety invariant: every `0` that state `C` reads in any
reachable configuration has a `1` immediately to its left.

Informally: a sentry condition.  If a `1` always guards the left flank
of whatever `C` probes, the fatal pattern of `halt_requires_c_probe_00`
can never occur, so the machine runs forever.  The rest of this file
exists to discharge this one predicate from the word-orbit dynamics. -/
def CProbeSafe (c : Config) : Prop :=
  ∀ d : Config, Reaches c d → d.state = State.C → d.tape d.head = false →
    d.tape (d.head - 1) = true

/-- C-probe safety implies the machine never halts. -/
theorem nonhalting_of_c_probe_safe {c : Config} (hne : c.state ≠ State.F)
    (hsafe : CProbeSafe c) : ¬ RawHalts c := by
  intro hh
  obtain ⟨d, hreach, hC, h0, h00⟩ := halt_requires_c_probe_00 hne hh
  have h1 := hsafe d hreach hC h0
  rw [h1] at h00
  exact Bool.noConfusion h00

/-- Specialization to the blank start. -/
theorem blank_nonhalting_of_c_probe_safe
    (hsafe : CProbeSafe blankStart) : ¬ RawHalts blankStart := by
  have hne : blankStart.state ≠ State.F := by
    simp [blankStart]
  exact nonhalting_of_c_probe_safe hne hsafe

/-!
## Segment safety machinery

Identical in structure to the rank-1 layer: conditional probe safety
over the first `N` steps of a run, composition, and the
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

/-- Conditional C-probe safety over the first `N` steps of a run:
every `0` probed by state `C` has a `1` immediately to its left. -/
def CSafeSeg (c : Config) (N : Nat) : Prop :=
  ∀ k d, k < N → stepN k c = some d → d.state = State.C →
    d.tape d.head = false → d.tape (d.head - 1) = true

theorem csafe_compose {c c' : Config} {m n : Nat}
    (hm : stepN m c = some c') (h1 : CSafeSeg c m) (h2 : CSafeSeg c' n) :
    CSafeSeg c (m + n) := by
  intro k d hk hkd hC hread
  by_cases hkm : k < m
  · exact h1 k d hkm hkd hC hread
  · have hkeq : k = m + (k - m) := by omega
    rw [hkeq, stepN_add, hm] at hkd
    exact h2 (k - m) d (by omega) hkd hC hread

/-- The segment-induction keystone: an invariant maintained by positive
safe segments gives `CProbeSafe` for the whole infinite run.

Informally: *safety in pieces is safety forever*.  If from every
invariant-satisfying configuration the machine runs some positive
number of steps safely and lands on the invariant again, then every
moment of the infinite run falls inside one of these safe segments —
strong induction on how many segments precede it. -/
theorem cprobe_safe_of_segments {Inv : Config → Prop} {c0 : Config}
    (h0 : Inv c0)
    (hseg : ∀ c, Inv c → ∃ k, 0 < k ∧ ∃ c', stepN k c = some c' ∧
      Inv c' ∧ CSafeSeg c k) :
    CProbeSafe c0 := by
  have main : ∀ (N n : Nat) (c : Config), n ≤ N → Inv c →
      ∀ d, stepN n c = some d → d.state = State.C →
        d.tape d.head = false → d.tape (d.head - 1) = true := by
    intro N
    induction N with
    | zero =>
        intro n c hn hInv d hd hC hread
        obtain ⟨k, hk, c', _hs, _hInv', hsafe⟩ := hseg c hInv
        exact hsafe n d (by omega) hd hC hread
    | succ N ihN =>
        intro n c hn hInv d hd hC hread
        obtain ⟨k, hk, c', hs, hInv', hsafe⟩ := hseg c hInv
        by_cases hlt : n < k
        · exact hsafe n d hlt hd hC hread
        · have hneq : n = k + (n - k) := by omega
          rw [hneq, stepN_add, hs] at hd
          exact ihN (n - k) c' (by omega) hInv' d hd hC hread
  intro d hreach hC hread
  obtain ⟨n, hn⟩ := hreach
  exact main n n c0 (Nat.le_refl n) h0 d hn hC hread

/-!
## One-step evaluator scaffolding and list foundation

Never rewrite on a `stepN` goal: chains are glued in term mode from
single-step facts (the standing proof-engineering convention of this
repository).  The word representation is the rank-1 one: `getD` with
default `false` makes blank tape outside the two lists semantically
invisible, so a pair `(em, rest)` pins the whole configuration up to
translation.
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
lists and a base position: `em` — the cells *below* the head, nearest
first (blank below `base`, subsumed by `getD`'s default), and `rest` —
the cells from the head upward (head cell included, `rest.getD 0`).
Every raw step is local surgery on this pair: a *push* (right move)
transfers the written head cell onto `em`, a *pop* (left move) either
transfers `em`'s top back onto `rest` or — when `em` is empty — steps
below `base` onto a fresh left extreme: an arrival, the record event
of the dossier-8 law.
-/

/-- The boundary invariant: state `st`, head at `base + em.length`,
cells below the head read `em` (nearest first, blank below `base`),
cells from the head upward read `rest`. -/
def Inv (st : State) (base : Int) (em rest : List Bool) (cfg : Config) : Prop :=
  cfg.state = st ∧ cfg.head = base + em.length ∧
  (∀ k : Nat, cfg.tape (base + em.length - 1 - k) = em.getD k false) ∧
  (∀ j : Nat, cfg.tape (base + em.length + j) = rest.getD j false)

/-!
## The three one-step episodes

The rank-1 lesson, taken to its limit: going one grain finer than the
learned record law subsumes boundary complexity.  Here the grain is a
single raw step, so exactly three episode shapes cover the entire
dynamics — push, interior pop, and extreme-extending pop — and *every*
branch of the record law (drift, merge, minors, checkpoints, both
grand parities, and the residues unobserved at 20M) is a composite of
them, simulated rather than assumed. -/

/-- Push: any right-moving instruction transfers the written head cell
onto the stack `em`.  One raw step; trivially C-probe-safe because no
right-moving instruction leaves state `C` (`C0` and `C1` both move
left). -/
theorem push_step {st st' : State} {wv : Bool} {base : Int} {em rest : List Bool}
    {cfg : Config}
    (hInv : Inv st base em rest cfg)
    (hins : instr st (rest.getD 0 false) = some ⟨st', wv, Dir.R⟩)
    (hnC : st ≠ State.C) :
    ∃ cfg', stepN 1 cfg = some cfg' ∧
      Inv st' base (wv :: em) (rest.drop 1) cfg' ∧ CSafeSeg cfg 1 := by
  obtain ⟨hst, hhd, hdown, hup⟩ := hInv
  obtain ⟨cs, hd, t⟩ := cfg
  simp only at hst hhd hdown hup
  subst hst
  subst hhd
  have r0 : t (base + (em.length : Int)) = rest.getD 0 false := by
    have h := hup 0
    rw [show base + (em.length : Int) + ((0 : Nat) : Int)
          = base + (em.length : Int) by omega] at h
    exact h
  have s1 : step ⟨cs, base + (em.length : Int), t⟩
      = some ⟨st', base + (em.length : Int) + 1,
          writeAt t (base + (em.length : Int)) wv⟩ := by
    rw [show step ⟨cs, base + (em.length : Int), t⟩
          = (instr cs (t (base + (em.length : Int)))).bind (fun ins =>
              some ⟨ins.next, move (base + (em.length : Int)) ins.dir,
                writeAt t (base + (em.length : Int)) ins.write⟩) from rfl,
        r0, hins]
    rfl
  have hdown' : ∀ k : Nat,
      (writeAt t (base + (em.length : Int)) wv)
        (base + ((em.length + 1 : Nat) : Int) - 1 - (k : Int))
        = (wv :: em).getD k false := by
    intro k
    cases k with
    | zero =>
        rw [show base + ((em.length + 1 : Nat) : Int) - 1 - ((0 : Nat) : Int)
              = base + (em.length : Int) by omega, writeAt_same]
        rfl
    | succ k =>
        rw [show base + ((em.length + 1 : Nat) : Int) - 1 - ((k + 1 : Nat) : Int)
              = base + (em.length : Int) - 1 - (k : Int) by omega,
            writeAt_other _ _ _ _ (by omega), hdown k, List.getD_cons_succ]
  have hup' : ∀ j : Nat,
      (writeAt t (base + (em.length : Int)) wv)
        (base + ((em.length + 1 : Nat) : Int) + (j : Int))
        = (rest.drop 1).getD j false := by
    intro j
    rw [show base + ((em.length + 1 : Nat) : Int) + (j : Int)
          = base + (em.length : Int) + ((1 + j : Nat) : Int) by omega,
        writeAt_other _ _ _ _ (by omega), hup (1 + j), getD_drop]
  refine ⟨⟨st', base + (em.length : Int) + 1,
      writeAt t (base + (em.length : Int)) wv⟩,
    stepN_succ_of_step s1 (stepN_zero _),
    ⟨rfl, show base + (em.length : Int) + 1
        = base + ((em.length + 1 : Nat) : Int) by omega, hdown', hup'⟩, ?_⟩
  intro k d hk hkd hC hread
  have hk0 : k = 0 := by omega
  subst hk0
  have hdd : (⟨cs, base + (em.length : Int), t⟩ : Config) = d := by
    simpa [stepN] using hkd
  rw [← hdd] at hC
  exact absurd hC hnC

/-- Interior pop: any left-moving instruction with a nonempty stack
transfers `em`'s top back onto `rest`.  One raw step; the safety
hypothesis is exactly the machine's mortality, localized — when `C`
pops a `0`, the guard cell `e0` must be `1`. -/
theorem pop_step_cons {st st' : State} {wv e0 : Bool} {base : Int}
    {em2 rest : List Bool} {cfg : Config}
    (hInv : Inv st base (e0 :: em2) rest cfg)
    (hins : instr st (rest.getD 0 false) = some ⟨st', wv, Dir.L⟩)
    (hCsafe : st = State.C → rest.getD 0 false = false → e0 = true) :
    ∃ cfg', stepN 1 cfg = some cfg' ∧
      Inv st' base em2 (e0 :: wv :: rest.drop 1) cfg' ∧ CSafeSeg cfg 1 := by
  obtain ⟨hst, hhd, hdown, hup⟩ := hInv
  obtain ⟨cs, hd, t⟩ := cfg
  simp only at hst hhd hdown hup
  simp only [List.length_cons] at hhd hdown hup
  subst hst
  subst hhd
  have r0 : t (base + ((em2.length + 1 : Nat) : Int)) = rest.getD 0 false := by
    have h := hup 0
    rw [show base + ((em2.length + 1 : Nat) : Int) + ((0 : Nat) : Int)
          = base + ((em2.length + 1 : Nat) : Int) by omega] at h
    exact h
  have s1 : step ⟨cs, base + ((em2.length + 1 : Nat) : Int), t⟩
      = some ⟨st', base + ((em2.length + 1 : Nat) : Int) - 1,
          writeAt t (base + ((em2.length + 1 : Nat) : Int)) wv⟩ := by
    rw [show step ⟨cs, base + ((em2.length + 1 : Nat) : Int), t⟩
          = (instr cs (t (base + ((em2.length + 1 : Nat) : Int)))).bind (fun ins =>
              some ⟨ins.next, move (base + ((em2.length + 1 : Nat) : Int)) ins.dir,
                writeAt t (base + ((em2.length + 1 : Nat) : Int)) ins.write⟩) from rfl,
        r0, hins]
    rfl
  have hdown' : ∀ k : Nat,
      (writeAt t (base + ((em2.length + 1 : Nat) : Int)) wv)
        (base + (em2.length : Int) - 1 - (k : Int)) = em2.getD k false := by
    intro k
    rw [show base + (em2.length : Int) - 1 - (k : Int)
          = base + ((em2.length + 1 : Nat) : Int) - 1 - ((k + 1 : Nat) : Int) by omega,
        writeAt_other _ _ _ _ (by omega), hdown (k + 1), List.getD_cons_succ]
  have hup' : ∀ j : Nat,
      (writeAt t (base + ((em2.length + 1 : Nat) : Int)) wv)
        (base + (em2.length : Int) + (j : Int))
        = (e0 :: wv :: rest.drop 1).getD j false := by
    intro j
    cases j with
    | zero =>
        rw [show base + (em2.length : Int) + ((0 : Nat) : Int)
              = base + ((em2.length + 1 : Nat) : Int) - 1 - ((0 : Nat) : Int) by omega,
            writeAt_other _ _ _ _ (by omega), hdown 0]
        rfl
    | succ j =>
        cases j with
        | zero =>
            rw [show base + (em2.length : Int) + ((1 : Nat) : Int)
                  = base + ((em2.length + 1 : Nat) : Int) by omega,
                writeAt_same]
            rfl
        | succ j =>
            rw [show base + (em2.length : Int) + ((j + 1 + 1 : Nat) : Int)
                  = base + ((em2.length + 1 : Nat) : Int) + ((1 + j : Nat) : Int) by omega,
                writeAt_other _ _ _ _ (by omega), hup (1 + j),
                List.getD_cons_succ, List.getD_cons_succ, getD_drop]
  refine ⟨⟨st', base + ((em2.length + 1 : Nat) : Int) - 1,
      writeAt t (base + ((em2.length + 1 : Nat) : Int)) wv⟩,
    stepN_succ_of_step s1 (stepN_zero _),
    ⟨rfl, show base + ((em2.length + 1 : Nat) : Int) - 1
        = base + (em2.length : Int) by omega, hdown', hup'⟩, ?_⟩
  intro k d hk hkd hC hread
  have hk0 : k = 0 := by omega
  subst hk0
  have hdd : (⟨cs, base + ((em2.length + 1 : Nat) : Int), t⟩ : Config) = d := by
    simpa [stepN] using hkd
  rw [← hdd] at hC hread
  have hrf : rest.getD 0 false = false := by rw [← r0]; exact hread
  have he0 : e0 = true := hCsafe hC hrf
  rw [← hdd]
  show t (base + ((em2.length + 1 : Nat) : Int) - 1) = true
  have h := hdown 0
  rw [show base + ((em2.length + 1 : Nat) : Int) - 1 - ((0 : Nat) : Int)
        = base + ((em2.length + 1 : Nat) : Int) - 1 by omega] at h
  rw [h, List.getD_cons_zero]
  exact he0

/-- Extreme-extending pop: a left move with an empty stack steps below
`base` onto blank tape — the *arrival*, a fresh left extreme, the
record event.  One raw step; `C` never arrives here reading `0` (that
is the guarded fatal frontier probe). -/
theorem pop_step_nil {st st' : State} {wv : Bool} {base : Int}
    {rest : List Bool} {cfg : Config}
    (hInv : Inv st base [] rest cfg)
    (hins : instr st (rest.getD 0 false) = some ⟨st', wv, Dir.L⟩)
    (hCr : st = State.C → rest.getD 0 false = true) :
    ∃ cfg', stepN 1 cfg = some cfg' ∧
      Inv st' (base - 1) [] (false :: wv :: rest.drop 1) cfg' ∧ CSafeSeg cfg 1 := by
  obtain ⟨hst, hhd, hdown, hup⟩ := hInv
  obtain ⟨cs, hd, t⟩ := cfg
  simp only at hst hhd hdown hup
  simp only [List.length_nil] at hhd hdown hup
  subst hst
  subst hhd
  rw [show base + ((0 : Nat) : Int) = base by omega]
  have r0 : t base = rest.getD 0 false := by
    have h := hup 0
    rw [show base + ((0 : Nat) : Int) + ((0 : Nat) : Int) = base by omega] at h
    exact h
  have s1 : step ⟨cs, base, t⟩
      = some ⟨st', base - 1, writeAt t base wv⟩ := by
    rw [show step ⟨cs, base, t⟩
          = (instr cs (t base)).bind (fun ins =>
              some ⟨ins.next, move base ins.dir, writeAt t base ins.write⟩) from rfl,
        r0, hins]
    rfl
  have hdown' : ∀ k : Nat,
      (writeAt t base wv) (base - 1 + ((0 : Nat) : Int) - 1 - (k : Int))
        = ([] : List Bool).getD k false := by
    intro k
    rw [show base - 1 + ((0 : Nat) : Int) - 1 - (k : Int)
          = base + ((0 : Nat) : Int) - 1 - ((k + 1 : Nat) : Int) by omega,
        writeAt_other _ _ _ _ (by omega), hdown (k + 1)]
    exact (getD_nil (k + 1)).trans (getD_nil k).symm
  have hup' : ∀ j : Nat,
      (writeAt t base wv) (base - 1 + ((0 : Nat) : Int) + (j : Int))
        = (false :: wv :: rest.drop 1).getD j false := by
    intro j
    cases j with
    | zero =>
        rw [show base - 1 + ((0 : Nat) : Int) + ((0 : Nat) : Int)
              = base + ((0 : Nat) : Int) - 1 - ((0 : Nat) : Int) by omega,
            writeAt_other _ _ _ _ (by omega), hdown 0]
        exact getD_nil 0
    | succ j =>
        cases j with
        | zero =>
            rw [show base - 1 + ((0 : Nat) : Int) + ((1 : Nat) : Int)
                  = base by omega, writeAt_same]
            rfl
        | succ j =>
            rw [show base - 1 + ((0 : Nat) : Int) + ((j + 1 + 1 : Nat) : Int)
                  = base + ((0 : Nat) : Int) + ((1 + j : Nat) : Int) by omega,
                writeAt_other _ _ _ _ (by omega), hup (1 + j),
                List.getD_cons_succ, List.getD_cons_succ, getD_drop]
  refine ⟨⟨st', base - 1, writeAt t base wv⟩,
    stepN_succ_of_step s1 (stepN_zero _),
    ⟨rfl, show base - 1 = base - 1 + ((0 : Nat) : Int) by omega, hdown', hup'⟩, ?_⟩
  intro k d hk hkd hC hread
  have hk0 : k = 0 := by omega
  subst hk0
  have hdd : (⟨cs, base, t⟩ : Config) = d := by
    simpa [stepN] using hkd
  rw [← hdd] at hC hread
  have hrf : rest.getD 0 false = false := by rw [← r0]; exact hread
  have hrt := hCr hC
  rw [hrt] at hrf
  exact Bool.noConfusion hrf

/-!
## The certified sweep: `go` and `wstep`

`go` is the fail-closed word machine: from `(st, em, rest)` it runs
single-raw-step surgery until the first below-base pop — the next
arrival, i.e. the next record of the dossier-8 law — and returns
`(state, arrival word, raw steps)`.  It returns `none` exactly on a
fatal `C`-probe (`C` reading `0` with no `1` guard below, the frontier
case `em = []` included), on the `F0` halt itself, and on fuel
exhaustion.  Nothing else fails: every other branch is the raw machine
verbatim, so all record-law branches — observed or not — are simulated
exactly.
-/

def go : Nat → State → List Bool → List Bool → Option (State × List Bool × Nat)
  | 0, _, _, _ => none
  | fuel + 1, st, em, rest =>
    match st, rest.getD 0 false with
    | State.A, false =>
        (go fuel State.B (true :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.A, true =>
        match em with
        | [] => some (State.C, false :: false :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.C em2 (e0 :: false :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.B, false =>
        match em with
        | [] => some (State.C, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.C em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.B, true =>
        (go fuel State.D (false :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.C, false =>
        match em with
        | [] => none
        | e0 :: em2 =>
            if e0 then
              (go fuel State.F em2 (e0 :: true :: rest.drop 1)).map
                (fun r => (r.1, r.2.1, 1 + r.2.2))
            else none
    | State.C, true =>
        match em with
        | [] => some (State.A, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.A em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.D, false =>
        match em with
        | [] => some (State.B, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.B em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.D, true =>
        (go fuel State.E (true :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.E, false =>
        (go fuel State.B (true :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.E, true =>
        match em with
        | [] => some (State.E, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.E em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.F, false => none
    | State.F, true =>
        match em with
        | [] => some (State.E, false :: false :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.E em2 (e0 :: false :: rest.drop 1)).map
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
step count, C-probe-safely, landing on an arrival configuration of the
returned word (head at the new base, the fresh left extreme). -/
theorem go_faithful :
    ∀ (fuel : Nat) (st : State) (em rest : List Bool) (st' : State)
      (w' : List Bool) (d : Nat),
      go fuel st em rest = some (st', w', d) →
      ∀ (base : Int) (cfg : Config), Inv st base em rest cfg →
        ∃ (cfg' : Config) (base' : Int), stepN d cfg = some cfg' ∧
          Inv st' base' [] w' cfg' ∧ CSafeSeg cfg d ∧ 0 < d := by
  intro fuel
  induction fuel with
  | zero =>
      intro st em rest st' w' d hgo base cfg hInv
      simp [go] at hgo
  | succ fuel ih =>
      intro st em rest st' w' d hgo base cfg hInv
      simp only [go] at hgo
      split at hgo
      · -- A0: push to B
        next hr =>
          obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
          subst hd
          obtain ⟨cfg₂, h1, h2, h3⟩ := push_step hInv (by rw [hr]; rfl) (by decide)
          obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
          refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
          · rw [stepN_add, h1]
            exact h1'
          · exact csafe_compose h1 h3 h3'
      · -- A1: pop to C
        next hr =>
          split at hgo
          · -- arrival
            obtain ⟨hs, hw, hd⟩ : State.C = st' ∧
                false :: false :: rest.drop 1 = w' ∧ 1 = d := by
              simpa using hgo
            subst hs; subst hw; subst hd
            obtain ⟨cfg', h1, h2, h3⟩ := pop_step_nil hInv (by rw [hr]; rfl) (fun _ => hr)
            exact ⟨cfg', base - 1, h1, h2, h3, by omega⟩
          · next e0 em2 =>
              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
              subst hd
              obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                (fun h _ => absurd h (by decide))
              obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
              · rw [stepN_add, h1]
                exact h1'
              · exact csafe_compose h1 h3 h3'
      · -- B0: pop to C
        next hr =>
          split at hgo
          · obtain ⟨hs, hw, hd⟩ : State.C = st' ∧
                false :: true :: rest.drop 1 = w' ∧ 1 = d := by
              simpa using hgo
            subst hs; subst hw; subst hd
            obtain ⟨cfg', h1, h2, h3⟩ := pop_step_nil hInv (by rw [hr]; rfl)
              (fun h => absurd h (by decide))
            exact ⟨cfg', base - 1, h1, h2, h3, by omega⟩
          · next e0 em2 =>
              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
              subst hd
              obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                (fun h _ => absurd h (by decide))
              obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
              · rw [stepN_add, h1]
                exact h1'
              · exact csafe_compose h1 h3 h3'
      · -- B1: push to D
        next hr =>
          obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
          subst hd
          obtain ⟨cfg₂, h1, h2, h3⟩ := push_step hInv (by rw [hr]; rfl) (by decide)
          obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
          refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
          · rw [stepN_add, h1]
            exact h1'
          · exact csafe_compose h1 h3 h3'
      · -- C0: the guarded probe — pop to F when the guard is a 1
        next hr =>
          split at hgo
          · simp at hgo
          · next e0 em2 =>
              split at hgo
              · next he0 =>
                  obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
                  subst hd
                  obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                    (fun _ _ => he0)
                  obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
                  refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
                  · rw [stepN_add, h1]
                    exact h1'
                  · exact csafe_compose h1 h3 h3'
              · simp at hgo
      · -- C1: pop to A
        next hr =>
          split at hgo
          · obtain ⟨hs, hw, hd⟩ : State.A = st' ∧
                false :: true :: rest.drop 1 = w' ∧ 1 = d := by
              simpa using hgo
            subst hs; subst hw; subst hd
            obtain ⟨cfg', h1, h2, h3⟩ := pop_step_nil hInv (by rw [hr]; rfl) (fun _ => hr)
            exact ⟨cfg', base - 1, h1, h2, h3, by omega⟩
          · next e0 em2 =>
              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
              subst hd
              obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                (fun _ hf => by rw [hr] at hf; exact Bool.noConfusion hf)
              obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
              · rw [stepN_add, h1]
                exact h1'
              · exact csafe_compose h1 h3 h3'
      · -- D0: pop to B
        next hr =>
          split at hgo
          · obtain ⟨hs, hw, hd⟩ : State.B = st' ∧
                false :: true :: rest.drop 1 = w' ∧ 1 = d := by
              simpa using hgo
            subst hs; subst hw; subst hd
            obtain ⟨cfg', h1, h2, h3⟩ := pop_step_nil hInv (by rw [hr]; rfl)
              (fun h => absurd h (by decide))
            exact ⟨cfg', base - 1, h1, h2, h3, by omega⟩
          · next e0 em2 =>
              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
              subst hd
              obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                (fun h _ => absurd h (by decide))
              obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
              · rw [stepN_add, h1]
                exact h1'
              · exact csafe_compose h1 h3 h3'
      · -- D1: push to E
        next hr =>
          obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
          subst hd
          obtain ⟨cfg₂, h1, h2, h3⟩ := push_step hInv (by rw [hr]; rfl) (by decide)
          obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
          refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
          · rw [stepN_add, h1]
            exact h1'
          · exact csafe_compose h1 h3 h3'
      · -- E0: push to B
        next hr =>
          obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
          subst hd
          obtain ⟨cfg₂, h1, h2, h3⟩ := push_step hInv (by rw [hr]; rfl) (by decide)
          obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
          refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
          · rw [stepN_add, h1]
            exact h1'
          · exact csafe_compose h1 h3 h3'
      · -- E1: pop to E
        next hr =>
          split at hgo
          · obtain ⟨hs, hw, hd⟩ : State.E = st' ∧
                false :: true :: rest.drop 1 = w' ∧ 1 = d := by
              simpa using hgo
            subst hs; subst hw; subst hd
            obtain ⟨cfg', h1, h2, h3⟩ := pop_step_nil hInv (by rw [hr]; rfl) (fun _ => hr)
            exact ⟨cfg', base - 1, h1, h2, h3, by omega⟩
          · next e0 em2 =>
              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
              subst hd
              obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                (fun h _ => absurd h (by decide))
              obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
              · rw [stepN_add, h1]
                exact h1'
              · exact csafe_compose h1 h3 h3'
      · -- F0: the halt — fail-closed
        simp at hgo
      · -- F1: pop to E
        next hr =>
          split at hgo
          · obtain ⟨hs, hw, hd⟩ : State.E = st' ∧
                false :: false :: rest.drop 1 = w' ∧ 1 = d := by
              simpa using hgo
            subst hs; subst hw; subst hd
            obtain ⟨cfg', h1, h2, h3⟩ := pop_step_nil hInv (by rw [hr]; rfl)
              (fun h => absurd h (by decide))
            exact ⟨cfg', base - 1, h1, h2, h3, by omega⟩
          · next e0 em2 =>
              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
              subst hd
              obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                (fun h _ => absurd h (by decide))
              obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
              · rw [stepN_add, h1]
                exact h1'
              · exact csafe_compose h1 h3 h3'

/-- Generous fuel: raw steps per record gap, comfortably quadratic in
the arrival word length.  Fail-closed — exhaustion is an orbit death,
and the empirical margin is above 2,000× at the 20M horizon. -/
def wfuel (w : List Bool) : Nat := 64 * (w.length + 64) * (w.length + 64)

/-- One certified record-to-record sweep: from an arrival
`(st, w)` (head at the left extreme, word `w` rightward), run the raw
machine to the next fresh left extreme.  Returns
`(state', word', steps)`. -/
def wstep (st : State) (w : List Bool) : Option (State × List Bool × Nat) :=
  go (wfuel w) st [] w

/-- **The sweep is faithful**: whenever `wstep` yields a successor
arrival, the raw machine, started on any realization of the input
arrival, runs *exactly* the returned number of steps, stays
C-probe-safe throughout, and lands on a realization of the successor
arrival.  No `Faithful` assumption remains anywhere in this file. -/
theorem wstep_faithful {st st' : State} {w w' : List Bool} {d : Nat}
    (hw : wstep st w = some (st', w', d)) :
    ∀ (base : Int) (cfg : Config), Inv st base [] w cfg →
      ∃ (cfg' : Config) (base' : Int), stepN d cfg = some cfg' ∧
        Inv st' base' [] w' cfg' ∧ CSafeSeg cfg d ∧ 0 < d :=
  fun base cfg hInv => go_faithful (wfuel w) st [] w st' w' d hw base cfg hInv

/-!
## The word orbit and the keystone

The blank start itself realizes the virtual arrival `(A, [])` (head at
its own left extreme over the empty word), so the orbit needs no raw
startup prefix at all: `worbit 1` computes to the first true record
`(A, [0,1,1])` at `t = 3`, matching the python extractor.  The word
orbit is `wstep` iterated; `SafeD8Orbit` — the whole conjecture — is
the single clause that it never dies.
-/

/-- The word orbit: `wstep` iterated from the blank anchor `(A, [])`. -/
def worbit : Nat → Option (State × List Bool)
  | 0 => some (State.A, [])
  | k + 1 =>
      match worbit k with
      | none => none
      | some s => (wstep s.1 s.2).map (fun r => (r.1, r.2.1))

/-- **The dossier-8 record-orbit conjecture**, in the exact form the
machine needs: the fail-closed record orbit never dies — no sweep ever
meets a fatal `C`-probe, the `F0` halt, or fuel exhaustion.  A
statement about a sequence of `(state, word)` pairs with no tape, no
head, no machine; every clause of the sweep dynamics behind it is
proven, so no `Faithful` component accompanies it. -/
def SafeD8Orbit : Prop := ∀ k : Nat, worbit k ≠ none

/-- The raw-side orbit invariant: the configuration realizes some live
state of the word orbit. -/
def OrbitInv (cfg : Config) : Prop :=
  ∃ (k : Nat) (st : State) (w : List Bool) (base : Int),
    worbit k = some (st, w) ∧ Inv st base [] w cfg

/-- The blank start realizes the anchor `(A, [])`. -/
theorem blank_realizes : Inv State.A 0 [] [] blankStart := by
  refine ⟨rfl, by simp [blankStart], ?_, ?_⟩
  · intro k
    exact (getD_nil k).symm
  · intro j
    exact (getD_nil j).symm

theorem orbitInv_start : OrbitInv blankStart :=
  ⟨0, State.A, [], 0, rfl, blank_realizes⟩

theorem worbit_succ {k : Nat} {s : State × List Bool}
    (horb : worbit k = some s) :
    worbit (k + 1) = (wstep s.1 s.2).map (fun r => (r.1, r.2.1)) := by
  rw [show worbit (k + 1) = (match worbit k with
      | none => none
      | some s => (wstep s.1 s.2).map (fun r => (r.1, r.2.1))) from rfl, horb]

/-- Segment step: from any configuration realizing a live orbit state,
the next sweep runs probe-safely to a configuration realizing the next
orbit state. -/
theorem orbit_segment (hso : SafeD8Orbit) (cfg : Config)
    (hinv : OrbitInv cfg) :
    ∃ n : Nat, 0 < n ∧ ∃ cfg' : Config, stepN n cfg = some cfg' ∧
      OrbitInv cfg' ∧ CSafeSeg cfg n := by
  obtain ⟨k, st, w, base, horb, hreal⟩ := hinv
  have hlive := hso (k + 1)
  rw [worbit_succ horb] at hlive
  cases hws : wstep st w with
  | none => exact absurd (by simp [hws]) hlive
  | some r =>
      obtain ⟨st2, w2, d⟩ := r
      obtain ⟨cfg', base', h1, h2, h3, h4⟩ := wstep_faithful hws base cfg hreal
      refine ⟨d, h4, cfg', h1, ?_, h3⟩
      exact ⟨k + 1, st2, w2, base',
        by rw [worbit_succ horb, hws]; rfl, h2⟩

/-- **The conditional closure**: the dossier-8 record-orbit conjecture
implies the machine never halts from blank.

Informally: the blank start realizes the empty arrival; from every
realized orbit word the certified sweep runs probe-safely to the next
record; segment induction turns the faithful sweep into
`CProbeSafe blankStart`; and the halt corridor `C0 → F0` is closed
forever.  The ninth closure — the second ladder machine, closing the
2026-08-31 pair at the same single-raw-step grain as dossier-7. -/
theorem safeD8Orbit_nonhalting (hso : SafeD8Orbit) :
    ¬ RawHalts blankStart := by
  apply blank_nonhalting_of_c_probe_safe
  exact cprobe_safe_of_segments orbitInv_start
    (fun c hinv => orbit_segment hso c hinv)

#print axioms safeD8Orbit_nonhalting

end QIG.Dossier8RawTM
