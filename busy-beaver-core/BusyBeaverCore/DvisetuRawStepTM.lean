import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000

/-!
# Dvisetu machine: raw-step semantics and assumption-free closure

Bare-Lean model of the concrete BB(6) machine

`1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB`  (Dvisetu, dossier-6: the
one-hole two-counter machine).

This file is the **assumption-free companion** to `DvisetuRawTM.lean`.
That file closes Dvisetu at *gait grain*: its keystone
`safeDvisetuOrbit_nonhalting` conditions on `SafeCheckpointOrbit`, which
carries a `DivideFaithful` clause — the recursive `n ≡ 0 (mod 3)` divide
renewal is *assumed* to realize its abstract output on the tape, because
at gait grain its recursive divide-by-3 was too costly to certify
directly.

Here Dvisetu is re-closed at **raw-step grain** (the dossier-9/14
engine).  Each word-machine move is a single raw step of list surgery on
the pair `(em, rest)` (`em` = cells *above* the head — to the right, the
growth direction — nearest first; `rest` = the head cell downward), and
an *arrival* is an above-base pop: the head stepping onto a fresh right
extreme.  The recursive divide renewal is then just a long run of
ordinary raw steps that the fail-closed sweep handles like every other
branch, so **no faithfulness assumption is needed**: the keystone
`safeDvisetuRawStep_nonhalting` conditions on the orbit-liveness clause
alone (`∀ k, worbit k ≠ none`), with no `DivideFaithful`.

Halt anatomy: Dvisetu grows *right* and halts via the undefined
transition `F0` — state `F` reading a `0`.  `F` is entered only from `E`
reading `0` (the transition `E0 = 0RF`, moving right), so the halt is the
`E0 → F0` corridor.  On this machine the halt *is* the probe: `F0` is
itself the undefined transition, so — the exact mirror of dossier-9's
`B1` — the probe-safety predicate needs no neighbour cell: "state `F`
never reads a `0`".  `F` pushes (its only defined move `F1 = 1LB` is a
left move) and never pops, so `F` is the coordinate mirror of dossier-9's
`B` (which pops and never pushes): `pop` episodes carry `st ≠ F` and
`push` episodes carry the fatal-cell safety hypothesis.

Checked statements (no sorry, no extra axioms):

* `step_eq_none_iff` — the machine halts in one step exactly at the
  unique undefined transition `F0`.
* `into_F_only_from_E0` — state `F` is entered only via `E` reading `0`.
* `halt_requires_f_read_0` — any raw halt passes through a reachable
  configuration in state `F` reading `0` (the halt is the probe).
* `halt_requires_entry_probe` — the corridor form: from any non-`F`
  start, a raw halt forces a reachable `E0` configuration whose *right*
  neighbour is a `0` — the cell `F` will die on.
* `nonhalting_of_f_probe_safe` — the F-probe-safety invariant ("state
  `F` never reads a `0`") implies the machine never halts.
* `push_step` / `pop_step_cons` / `pop_step_nil` — the three one-step
  episode lemmas.
* `go_faithful` / `wstep_faithful` — the certified record-to-record
  sweep: `wstep` is a fail-closed executable map on `(state, word)`
  pairs whose every `some` output is realized by the raw machine in
  *exactly* the returned step count, F-probe-safely.  It dies exactly on
  the `F0` halt probe and on fuel exhaustion — nothing else.
* the word orbit `worbit` from the blank anchor `(A, [])`, and the
  keystone `safeDvisetuRawStep_nonhalting`:
  `SafeDvisetuRawStep → ¬ RawHalts blankStart`.

`SafeDvisetuRawStep` is the single conjecture `∀ k, worbit k ≠ none`:
the fail-closed record orbit never dies.  **No `DivideFaithful` and no
`Faithful` component remains**: because the engine is the raw step
itself, every branch of the dossier-6 timed law — drift, collapse,
micro, both linear renewals, *and the recursive divide renewal* — is
simulated exactly rather than assumed.

The conjecture is exactly the empirical substrate validated by the
record-mirror differential test (`tests/bb6/test_dvisetu_rawstep_theorems.py`):
every fresh-right-extreme record reproduced exactly — state, word, step
count — over 22M raw steps (2,949 arrivals, all exact, F-probe-safe at
every step), with the five divide renewals reproduced exactly by the
raw-step orbit — `n = 120, 186, 918, 2976, 18648` with raw gaps
`15155, 36581, 498299, 9195841, …`.

Fuel form.  The divide renewal is quadratic-time (`dt ≈ 0.6 n²` in the
block length `n`) and the sweep fuel `wfuel w = 64·(|w|+64)²` is also
quadratic in the arrival word length, so their ratio is bounded (about
`0.6/64 ≈ 0.0094`) independently of size: the maximum fuel fraction
measured over the 22M horizon — including the depth-2 divide cascade at
`n = 918` (raw gap 498,299) — is `0.00907`, a margin above `110×`.  The
same margin holds at the depth-1 event `n = 18,648` (raw gap `≈ 0.6 n²`),
so the quadratic fuel is empirically safe on the very long divide runs;
exhaustion is fail-closed (an orbit death) regardless.
-/

namespace QIG.DvisetuRawStepTM

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

/-- The Dvisetu transition table.  `none` is the undefined halt
transition `F0`. -/
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

/-- State `F` is entered only by `E` reading `0` (the transition
`E0 = 0RF`: write `0`, move right).  The successor sits one cell to the
*right* of the probed cell, whose value the entry write left at `0`.

Informally: the turnstile into death — `F` is reachable only through `E`
reading a `0`, stepping right over it. -/
theorem into_F_only_from_E0 {c c' : Config} (h : step c = some c')
    (hF : c'.state = State.F) :
    c'.head = c.head + 1 ∧ c.state = State.E ∧ c.tape c.head = false ∧
      c'.tape = writeAt c.tape c.head false := by
  cases hs : c.state <;> cases ht : c.tape c.head <;>
    simp [step, instr, hs, ht] at h
  all_goals
    first
      | exact ⟨by rw [← h]; simp [move], rfl, rfl, by rw [← h]⟩
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

/-- Halt localization, direct form: a raw halt passes through a
reachable configuration in state `F` reading `0`.

Informally: on this machine the halt *is* the probe — `F0` is itself the
undefined transition, so no predecessor analysis is needed: to die the
machine must first stand in state `F` on a `0`. -/
theorem halt_requires_f_read_0 {c : Config} (hh : RawHalts c) :
    ∃ d : Config, Reaches c d ∧ d.state = State.F ∧
      d.tape d.head = false := by
  obtain ⟨n, hn⟩ := hh
  obtain ⟨k, _, d0, hd0, hstop⟩ := stepN_none_last n c hn
  have hF := (step_eq_none_iff d0).mp hstop
  exact ⟨d0, ⟨k, hd0⟩, hF.1, hF.2⟩

/-- Halt localization, corridor form: from any non-`F` start, a raw halt
forces a reachable configuration in state `E` reading `0` whose *right*
neighbour is a `0` — the cell the machine dies on one step later.

Informally: the only door into `F` is `E0`, stepping right onto the fatal
cell, and its write cannot touch that neighbour. -/
theorem halt_requires_entry_probe {c : Config} (hne : c.state ≠ State.F)
    (hh : RawHalts c) :
    ∃ d : Config, Reaches c d ∧ d.tape (d.head + 1) = false ∧
      d.state = State.E ∧ d.tape d.head = false := by
  obtain ⟨n, hn⟩ := hh
  obtain ⟨k, _, d0, hd0, hstop⟩ := stepN_none_last n c hn
  have hF := (step_eq_none_iff d0).mp hstop
  cases k with
  | zero =>
      have hcd : c = d0 := by simpa [stepN] using hd0
      exact absurd (hcd ▸ hF.1) hne
  | succ k' =>
      obtain ⟨e, he, hstepe⟩ := stepN_some_pred k' c d0 hd0
      obtain ⟨hhead, hst, hrd, htape⟩ := into_F_only_from_E0 hstepe hF.1
      have hread : d0.tape d0.head = false := hF.2
      refine ⟨e, ⟨k', he⟩, ?_, hst, hrd⟩
      rw [htape, hhead] at hread
      rwa [writeAt_other e.tape e.head (e.head + 1) false (by omega)] at hread

/-- The F-probe-safety invariant: state `F` never reads a `0` in any
reachable configuration.

Informally: a sentry on the probed cell itself.  If every cell `F` ever
probes is a `1`, the fatal pattern of `halt_requires_f_read_0` can never
occur, so the machine runs forever.  The rest of this file discharges
this one predicate from the word-orbit dynamics. -/
def FProbeSafe (c : Config) : Prop :=
  ∀ d : Config, Reaches c d → d.state = State.F → d.tape d.head = true

/-- F-probe safety implies the machine never halts. -/
theorem nonhalting_of_f_probe_safe {c : Config}
    (hsafe : FProbeSafe c) : ¬ RawHalts c := by
  intro hh
  obtain ⟨d, hreach, hF, h0⟩ := halt_requires_f_read_0 hh
  have h1 := hsafe d hreach hF
  rw [h1] at h0
  exact Bool.noConfusion h0

/-- Specialization to the blank start. -/
theorem blank_nonhalting_of_f_probe_safe
    (hsafe : FProbeSafe blankStart) : ¬ RawHalts blankStart :=
  nonhalting_of_f_probe_safe hsafe

/-!
## Segment safety machinery

Conditional probe safety over the first `N` steps of a run, composition,
and the segment-induction keystone that turns the per-sweep safety of the
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

/-- Conditional F-probe safety over the first `N` steps of a run: state
`F` never reads a `0`. -/
def FSafeSeg (c : Config) (N : Nat) : Prop :=
  ∀ k d, k < N → stepN k c = some d → d.state = State.F →
    d.tape d.head = true

theorem fsafe_compose {c c' : Config} {m n : Nat}
    (hm : stepN m c = some c') (h1 : FSafeSeg c m) (h2 : FSafeSeg c' n) :
    FSafeSeg c (m + n) := by
  intro k d hk hkd hF
  by_cases hkm : k < m
  · exact h1 k d hkm hkd hF
  · have hkeq : k = m + (k - m) := by omega
    rw [hkeq, stepN_add, hm] at hkd
    exact h2 (k - m) d (by omega) hkd hF

/-- The segment-induction keystone: an invariant maintained by positive
safe segments gives `FProbeSafe` for the whole infinite run.

Informally: *safety in pieces is safety forever*.  If from every
invariant-satisfying configuration the machine runs some positive number
of steps safely and lands on the invariant again, then every moment of
the infinite run falls inside one of these safe segments. -/
theorem fprobe_safe_of_segments {Inv : Config → Prop} {c0 : Config}
    (h0 : Inv c0)
    (hseg : ∀ c, Inv c → ∃ k, 0 < k ∧ ∃ c', stepN k c = some c' ∧
      Inv c' ∧ FSafeSeg c k) :
    FProbeSafe c0 := by
  have main : ∀ (N n : Nat) (c : Config), n ≤ N → Inv c →
      ∀ d, stepN n c = some d → d.state = State.F →
        d.tape d.head = true := by
    intro N
    induction N with
    | zero =>
        intro n c hn hInv d hd hF
        obtain ⟨k, hk, c', _hs, _hInv', hsafe⟩ := hseg c hInv
        exact hsafe n d (by omega) hd hF
    | succ N ihN =>
        intro n c hn hInv d hd hF
        obtain ⟨k, hk, c', hs, hInv', hsafe⟩ := hseg c hInv
        by_cases hlt : n < k
        · exact hsafe n d hlt hd hF
        · have hneq : n = k + (n - k) := by omega
          rw [hneq, stepN_add, hs] at hd
          exact ihN (n - k) c' (by omega) hInv' d hd hF
  intro d hreach hF
  obtain ⟨n, hn⟩ := hreach
  exact main n n c0 (Nat.le_refl n) h0 d hn hF

/-!
## One-step evaluator scaffolding and list foundation
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

At every moment the whole configuration is pinned by two lists and a base
position: `em` — the cells *above* the head, nearest first (blank above
`base`, subsumed by `getD`'s default), and `rest` — the cells from the
head downward (head cell included, `rest.getD 0`).
-/

/-- The boundary invariant: state `st`, head at `base - em.length`, cells
above the head read `em` (nearest first, blank above `base`), cells from
the head downward read `rest`. -/
def Inv (st : State) (base : Int) (em rest : List Bool) (cfg : Config) : Prop :=
  cfg.state = st ∧ cfg.head = base - em.length ∧
  (∀ k : Nat, cfg.tape (base - em.length + 1 + k) = em.getD k false) ∧
  (∀ j : Nat, cfg.tape (base - em.length - j) = rest.getD j false)

/-!
## The three one-step episodes

Push (left move), interior pop, and extreme-extending pop.  On Dvisetu
the fatal state `F` *pushes* (its only defined move `F1` is a left move)
and never pops, the coordinate mirror of dossier-9's `B`: so `push`
carries the fatal-cell safety hypothesis and `pop` carries `st ≠ F`.
-/

/-- Push: any left-moving instruction transfers the written head cell
onto the stack `em`.  One raw step; F-probe-safe because when the fatal
state `F` pushes (its only left move `F1`) the probed cell was a `1`. -/
theorem push_step {st st' : State} {wv : Bool} {base : Int} {em rest : List Bool}
    {cfg : Config}
    (hInv : Inv st base em rest cfg)
    (hins : instr st (rest.getD 0 false) = some ⟨st', wv, Dir.L⟩)
    (hFsafe : st = State.F → rest.getD 0 false = true) :
    ∃ cfg', stepN 1 cfg = some cfg' ∧
      Inv st' base (wv :: em) (rest.drop 1) cfg' ∧ FSafeSeg cfg 1 := by
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
  intro k d hk hkd hF
  have hk0 : k = 0 := by omega
  subst hk0
  have hdd : (⟨cs, base - (em.length : Int), t⟩ : Config) = d := by
    simpa [stepN] using hkd
  rw [← hdd] at hF
  have hrf : rest.getD 0 false = true := hFsafe hF
  rw [← hdd]
  show t (base - (em.length : Int)) = true
  rw [r0]
  exact hrf

/-- Interior pop: any right-moving instruction with a nonempty stack
transfers `em`'s top back onto `rest`.  One raw step; F-probe-safe
because the fatal state `F` never right-moves (`hnF`). -/
theorem pop_step_cons {st st' : State} {wv e0 : Bool} {base : Int}
    {em2 rest : List Bool} {cfg : Config}
    (hInv : Inv st base (e0 :: em2) rest cfg)
    (hins : instr st (rest.getD 0 false) = some ⟨st', wv, Dir.R⟩)
    (hnF : st ≠ State.F) :
    ∃ cfg', stepN 1 cfg = some cfg' ∧
      Inv st' base em2 (e0 :: wv :: rest.drop 1) cfg' ∧ FSafeSeg cfg 1 := by
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
  intro k d hk hkd hF
  have hk0 : k = 0 := by omega
  subst hk0
  have hdd : (⟨cs, base - ((em2.length + 1 : Nat) : Int), t⟩ : Config) = d := by
    simpa [stepN] using hkd
  rw [← hdd] at hF
  exact absurd hF hnF

/-- Extreme-extending pop: a right move with an empty stack steps above
`base` onto blank tape — the *arrival*, a fresh right extreme, the record
event.  One raw step; F-probe-safe because `F` never right-moves. -/
theorem pop_step_nil {st st' : State} {wv : Bool} {base : Int}
    {rest : List Bool} {cfg : Config}
    (hInv : Inv st base [] rest cfg)
    (hins : instr st (rest.getD 0 false) = some ⟨st', wv, Dir.R⟩)
    (hnF : st ≠ State.F) :
    ∃ cfg', stepN 1 cfg = some cfg' ∧
      Inv st' (base + 1) [] (false :: wv :: rest.drop 1) cfg' ∧ FSafeSeg cfg 1 := by
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
  intro k d hk hkd hF
  have hk0 : k = 0 := by omega
  subst hk0
  have hdd : (⟨cs, base, t⟩ : Config) = d := by
    simpa [stepN] using hkd
  rw [← hdd] at hF
  exact absurd hF hnF

/-!
## The certified sweep: `go` and `wstep`

`go` runs single-raw-step surgery until the first above-base pop — the
next arrival — and returns `(state, arrival word, raw steps)`.  It
returns `none` exactly on the fatal `F0` probe (`F` reading `0` — the
undefined halt transition) and on fuel exhaustion.  Nothing else fails.
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
        match em with
        | [] => some (State.B, false :: false :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.B em2 (e0 :: false :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.B, false =>
        (go fuel State.B (true :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.B, true =>
        (go fuel State.C (false :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.C, false =>
        match em with
        | [] => some (State.D, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.D em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.C, true =>
        (go fuel State.C (true :: em) (rest.drop 1)).map
          (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.D, false =>
        match em with
        | [] => some (State.E, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.E em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.D, true =>
        match em with
        | [] => some (State.A, false :: false :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.A em2 (e0 :: false :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.E, false =>
        match em with
        | [] => some (State.F, false :: false :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.F em2 (e0 :: false :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.E, true =>
        match em with
        | [] => some (State.A, false :: true :: rest.drop 1, 1)
        | e0 :: em2 =>
            (go fuel State.A em2 (e0 :: true :: rest.drop 1)).map
              (fun r => (r.1, r.2.1, 1 + r.2.2))
    | State.F, false => none
    | State.F, true =>
        (go fuel State.B (true :: em) (rest.drop 1)).map
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

/-- Faithfulness of the sweep, by induction on fuel: every `some` output
of `go` is realized by the raw machine in exactly the returned step
count, F-probe-safely, landing on an arrival configuration of the
returned word (head at the new base, the fresh right extreme). -/
theorem go_faithful :
    ∀ (fuel : Nat) (st : State) (em rest : List Bool) (st' : State)
      (w' : List Bool) (d : Nat),
      go fuel st em rest = some (st', w', d) →
      ∀ (base : Int) (cfg : Config), Inv st base em rest cfg →
        ∃ (cfg' : Config) (base' : Int), stepN d cfg = some cfg' ∧
          Inv st' base' [] w' cfg' ∧ FSafeSeg cfg d ∧ 0 < d := by
  intro fuel
  induction fuel with
  | zero =>
      intro st em rest st' w' d hgo base cfg hInv
      simp [go] at hgo
  | succ fuel ih =>
      intro st em rest st' w' d hgo base cfg hInv
      simp only [go] at hgo
      split at hgo
      · -- A0: pop to B, write 1
        next hr =>
          split at hgo
          · obtain ⟨hs, hw, hd⟩ : State.B = st' ∧
                false :: true :: rest.drop 1 = w' ∧ 1 = d := by
              simpa using hgo
            subst hs; subst hw; subst hd
            obtain ⟨cfg', h1, h2, h3⟩ := pop_step_nil hInv (by rw [hr]; rfl)
              (by decide)
            exact ⟨cfg', base + 1, h1, h2, h3, by omega⟩
          · next e0 em2 =>
              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
              subst hd
              obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                (by decide)
              obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
              · rw [stepN_add, h1]
                exact h1'
              · exact fsafe_compose h1 h3 h3'
      · -- A1: pop to B, write 0
        next hr =>
          split at hgo
          · obtain ⟨hs, hw, hd⟩ : State.B = st' ∧
                false :: false :: rest.drop 1 = w' ∧ 1 = d := by
              simpa using hgo
            subst hs; subst hw; subst hd
            obtain ⟨cfg', h1, h2, h3⟩ := pop_step_nil hInv (by rw [hr]; rfl)
              (by decide)
            exact ⟨cfg', base + 1, h1, h2, h3, by omega⟩
          · next e0 em2 =>
              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
              subst hd
              obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                (by decide)
              obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
              · rw [stepN_add, h1]
                exact h1'
              · exact fsafe_compose h1 h3 h3'
      · -- B0: push to B, write 1
        next hr =>
          obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
          subst hd
          obtain ⟨cfg₂, h1, h2, h3⟩ := push_step hInv (by rw [hr]; rfl)
            (fun h => absurd h (by decide))
          obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
          refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
          · rw [stepN_add, h1]
            exact h1'
          · exact fsafe_compose h1 h3 h3'
      · -- B1: push to C, write 0
        next hr =>
          obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
          subst hd
          obtain ⟨cfg₂, h1, h2, h3⟩ := push_step hInv (by rw [hr]; rfl)
            (fun h => absurd h (by decide))
          obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
          refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
          · rw [stepN_add, h1]
            exact h1'
          · exact fsafe_compose h1 h3 h3'
      · -- C0: pop to D, write 1
        next hr =>
          split at hgo
          · obtain ⟨hs, hw, hd⟩ : State.D = st' ∧
                false :: true :: rest.drop 1 = w' ∧ 1 = d := by
              simpa using hgo
            subst hs; subst hw; subst hd
            obtain ⟨cfg', h1, h2, h3⟩ := pop_step_nil hInv (by rw [hr]; rfl)
              (by decide)
            exact ⟨cfg', base + 1, h1, h2, h3, by omega⟩
          · next e0 em2 =>
              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
              subst hd
              obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                (by decide)
              obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
              · rw [stepN_add, h1]
                exact h1'
              · exact fsafe_compose h1 h3 h3'
      · -- C1: push to C, write 1
        next hr =>
          obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
          subst hd
          obtain ⟨cfg₂, h1, h2, h3⟩ := push_step hInv (by rw [hr]; rfl)
            (fun h => absurd h (by decide))
          obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
          refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
          · rw [stepN_add, h1]
            exact h1'
          · exact fsafe_compose h1 h3 h3'
      · -- D0: pop to E, write 1
        next hr =>
          split at hgo
          · obtain ⟨hs, hw, hd⟩ : State.E = st' ∧
                false :: true :: rest.drop 1 = w' ∧ 1 = d := by
              simpa using hgo
            subst hs; subst hw; subst hd
            obtain ⟨cfg', h1, h2, h3⟩ := pop_step_nil hInv (by rw [hr]; rfl)
              (by decide)
            exact ⟨cfg', base + 1, h1, h2, h3, by omega⟩
          · next e0 em2 =>
              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
              subst hd
              obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                (by decide)
              obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
              · rw [stepN_add, h1]
                exact h1'
              · exact fsafe_compose h1 h3 h3'
      · -- D1: pop to A, write 0
        next hr =>
          split at hgo
          · obtain ⟨hs, hw, hd⟩ : State.A = st' ∧
                false :: false :: rest.drop 1 = w' ∧ 1 = d := by
              simpa using hgo
            subst hs; subst hw; subst hd
            obtain ⟨cfg', h1, h2, h3⟩ := pop_step_nil hInv (by rw [hr]; rfl)
              (by decide)
            exact ⟨cfg', base + 1, h1, h2, h3, by omega⟩
          · next e0 em2 =>
              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
              subst hd
              obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                (by decide)
              obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
              · rw [stepN_add, h1]
                exact h1'
              · exact fsafe_compose h1 h3 h3'
      · -- E0: pop to F, write 0
        next hr =>
          split at hgo
          · obtain ⟨hs, hw, hd⟩ : State.F = st' ∧
                false :: false :: rest.drop 1 = w' ∧ 1 = d := by
              simpa using hgo
            subst hs; subst hw; subst hd
            obtain ⟨cfg', h1, h2, h3⟩ := pop_step_nil hInv (by rw [hr]; rfl)
              (by decide)
            exact ⟨cfg', base + 1, h1, h2, h3, by omega⟩
          · next e0 em2 =>
              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
              subst hd
              obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                (by decide)
              obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
              · rw [stepN_add, h1]
                exact h1'
              · exact fsafe_compose h1 h3 h3'
      · -- E1: pop to A, write 1
        next hr =>
          split at hgo
          · obtain ⟨hs, hw, hd⟩ : State.A = st' ∧
                false :: true :: rest.drop 1 = w' ∧ 1 = d := by
              simpa using hgo
            subst hs; subst hw; subst hd
            obtain ⟨cfg', h1, h2, h3⟩ := pop_step_nil hInv (by rw [hr]; rfl)
              (by decide)
            exact ⟨cfg', base + 1, h1, h2, h3, by omega⟩
          · next e0 em2 =>
              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
              subst hd
              obtain ⟨cfg₂, h1, h2, h3⟩ := pop_step_cons hInv (by rw [hr]; rfl)
                (by decide)
              obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
              · rw [stepN_add, h1]
                exact h1'
              · exact fsafe_compose h1 h3 h3'
      · -- F0: the halt probe — fail-closed
        simp at hgo
      · -- F1: push to B, write 1 — the fatal state pushes, probed cell was 1
        next hr =>
          obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo
          subst hd
          obtain ⟨cfg₂, h1, h2, h3⟩ := push_step hInv (by rw [hr]; rfl)
            (fun _ => hr)
          obtain ⟨cfg', base', h1', h2', h3', _⟩ := ih _ _ _ _ _ _ hrec base cfg₂ h2
          refine ⟨cfg', base', ?_, h2', ?_, by omega⟩
          · rw [stepN_add, h1]
            exact h1'
          · exact fsafe_compose h1 h3 h3'

/-- Generous fuel: raw steps per record gap, comfortably quadratic in the
arrival word length.  The divide renewal is itself quadratic
(`dt ≈ 0.6 |w|²`), so the fuel fraction stays bounded (~`0.0094`,
measured max `0.00907` over 22M steps, margin above `110×`); exhaustion
is fail-closed. -/
def wfuel (w : List Bool) : Nat := 64 * (w.length + 64) * (w.length + 64)

/-- One certified record-to-record sweep: from an arrival `(st, w)` run
the raw machine to the next fresh right extreme. -/
def wstep (st : State) (w : List Bool) : Option (State × List Bool × Nat) :=
  go (wfuel w) st [] w

/-- **The sweep is faithful**: whenever `wstep` yields a successor
arrival, the raw machine, started on any realization of the input
arrival, runs *exactly* the returned number of steps, stays F-probe-safe
throughout, and lands on a realization of the successor arrival.  No
`Faithful` and no `DivideFaithful` assumption remains anywhere. -/
theorem wstep_faithful {st st' : State} {w w' : List Bool} {d : Nat}
    (hw : wstep st w = some (st', w', d)) :
    ∀ (base : Int) (cfg : Config), Inv st base [] w cfg →
      ∃ (cfg' : Config) (base' : Int), stepN d cfg = some cfg' ∧
        Inv st' base' [] w' cfg' ∧ FSafeSeg cfg d ∧ 0 < d :=
  fun base cfg hInv => go_faithful (wfuel w) st [] w st' w' d hw base cfg hInv

/-!
## The word orbit and the keystone
-/

/-- The word orbit: `wstep` iterated from the blank anchor `(A, [])`. -/
def worbit : Nat → Option (State × List Bool)
  | 0 => some (State.A, [])
  | k + 1 =>
      match worbit k with
      | none => none
      | some s => (wstep s.1 s.2).map (fun r => (r.1, r.2.1))

/-- **The Dvisetu raw-step record-orbit conjecture**, in the exact form
the machine needs: the fail-closed record orbit never dies — no sweep
ever meets the fatal `F0` probe or fuel exhaustion.  A statement about a
sequence of `(state, word)` pairs with no tape, no head, no machine;
every clause of the sweep dynamics behind it — including the recursive
divide renewal — is proven, so **no `DivideFaithful` and no `Faithful`
component accompanies it**. -/
def SafeDvisetuRawStep : Prop := ∀ k : Nat, worbit k ≠ none

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
theorem orbit_segment (hso : SafeDvisetuRawStep) (cfg : Config)
    (hinv : OrbitInv cfg) :
    ∃ n : Nat, 0 < n ∧ ∃ cfg' : Config, stepN n cfg = some cfg' ∧
      OrbitInv cfg' ∧ FSafeSeg cfg n := by
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

/-- **The conditional closure**: the Dvisetu raw-step record-orbit
conjecture implies the machine never halts from blank.

Informally: the blank start realizes the empty arrival; from every
realized orbit word the certified sweep runs probe-safely to the next
record; segment induction turns the faithful sweep into
`FProbeSafe blankStart`; and the one-cell halt pattern `F0` is closed
forever.  The assumption-free re-closure of Dvisetu at raw-step grain:
the recursive divide renewal is simulated exactly, so **no
`DivideFaithful` clause conditions this theorem** — the sole hypothesis
is orbit liveness. -/
theorem safeDvisetuRawStep_nonhalting (hso : SafeDvisetuRawStep) :
    ¬ RawHalts blankStart := by
  apply blank_nonhalting_of_f_probe_safe
  exact fprobe_safe_of_segments orbitInv_start
    (fun c hinv => orbit_segment hso c hinv)

#print axioms safeDvisetuRawStep_nonhalting

end QIG.DvisetuRawStepTM
