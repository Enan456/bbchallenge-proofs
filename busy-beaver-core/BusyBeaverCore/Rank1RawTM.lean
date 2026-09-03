import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000

/-!
# Rank-1 array-class machine: raw semantics and conditional closure

Bare-Lean model of the concrete BB(6) machine

`1RB1RD_1LC0LC_0RD0LB_1RF0LE_0RD---_0RA1RC`  (dossier-5: the rank-1
array-class machine, the block-trisection odometer).

This is the program's seventh conditional closure and the first over a
*growing-dimension* state space: the abstract state is an unboundedly
growing word (`List Bool`), not a fixed tuple of integers.

Checked statements (no sorry, no extra axioms):

* `step_eq_none_iff` — the machine halts in one step exactly at the
  unique undefined transition `E1`.
* `into_E_only_from_D1` — state `E` is entered only via `D` reading `1`
  (the transition `D1 = 0LE`: write `0`, move left).
* `halt_requires_d_probe_11` — any raw halt from a non-`E` start passes
  through a reachable configuration in state `D` reading `1` whose
  *left* neighbour is also `1`.
* `nonhalting_of_d_probe_safe` — the D-probe-safety invariant ("every
  `1` that state `D` reads has a `0` to its left") implies the machine
  never halts.
* the micro-episode theorems (`dip_step`, `chunkA_step`, `chunkC_step`,
  `aterm_step`, `c1turn_step`, `descend_run`) — the exact validated
  cell-level choreography of every sweep: the 2-step `E`-probe dip, the
  two 3-step rise chunks, the 3-step arrival terminator, the 3-step
  `C1` turn, and the parametric leftward descent (the shoot and every
  interior dance are instances).
* the classical unit-rule theorems of the trisection calculus as
  corollaries with their exact costs: `bcopy_step` (12), `babsorb_step`
  (8), `dinsert_step` (12), and the parametric `dregroup_step` (8+6k).
* `descendExec_faithful` / `passGo_faithful` / `wstep_faithful` — the
  certified word-level sweep: `wstep` is a fail-closed executable map
  on words (`List Bool` + head offset) whose every `some` output is
  realized by the raw machine in *exactly* the returned step count,
  probe-safely.
* the word orbit `worbit` from the 1-step startup anchor, and the
  keystone `safeWordOrbit_nonhalting`:
  `SafeWordOrbit → ¬ RawHalts blankStart`.

`SafeWordOrbit` is the single conjecture `∀ k, worbit k ≠ none`: the
fail-closed word orbit never dies.  Unlike the divide branch of the
dossier-6 closure, *no* per-family `Faithful` assumption remains: the
entire sweep dynamics — interior units, boundary tails, head rules,
mini-arrival floors — is subsumed by the certified cell-level pass
simulator and proven faithful unconditionally.  The conjecture is
exactly the empirical substrate validated in
`tests/bb6/test_rank1_theorems.py` (every raw segment reproduced
exactly — word, step count, head offset — over multi-million-step
horizons).
-/

namespace QIG.Rank1RawTM

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

/-- The rank-1 transition table.  `none` is the undefined halt
transition `E1`. -/
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

theorem writeAt_self (tape : Int → Bool) (pos : Int) {value : Bool}
    (h : tape pos = value) : writeAt tape pos value = tape := by
  funext x
  by_cases hx : x = pos
  · subst hx; simp [writeAt, h]
  · simp [writeAt, hx]

theorem writeAt_overwrite (tape : Int → Bool) (pos : Int) (v w : Bool) :
    writeAt (writeAt tape pos v) pos w = writeAt tape pos w := by
  funext x
  by_cases hx : x = pos <;> simp [writeAt, hx]

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

/-- The raw machine halts in one step exactly at the unique undefined
transition `E1`. -/
theorem step_eq_none_iff (c : Config) :
    step c = none ↔ c.state = State.E ∧ c.tape c.head = true := by
  cases hs : c.state <;> cases ht : c.tape c.head <;>
    simp [step, instr, hs, ht]

def RawHalts (c : Config) : Prop := ∃ n : Nat, stepN n c = none

def Reaches (c d : Config) : Prop := ∃ n : Nat, stepN n c = some d

def blankTape : Int → Bool := fun _ => false

def blankStart : Config where
  state := State.A
  head := 0
  tape := blankTape

/-- State `E` is entered only by `D` reading `1` (the transition
`D1 = 0LE`): the predecessor is in state `D` on a `1`, and the
successor sits one cell to the left with the probed cell rewritten
to `0`.

Informally: the turnstile into death — `E` is reachable only through
`D` reading a `1`, stepping left over it.  So the final two
configurations of any halting run are completely determined. -/
theorem into_E_only_from_D1 {c c' : Config} (h : step c = some c')
    (hE : c'.state = State.E) :
    c.state = State.D ∧ c.tape c.head = true ∧
      c'.head = c.head - 1 ∧ c'.tape = writeAt c.tape c.head false := by
  cases hs : c.state <;> cases ht : c.tape c.head <;>
    simp [step, instr, hs, ht] at h
  all_goals
    first
      | exact ⟨rfl, rfl, by rw [← h]; simp [move], by rw [← h]⟩
      | (rw [← h] at hE; simp at hE)

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

/-- Halt localization: from any non-`E` start, a raw halt forces a
reachable configuration where `D` reads a `1` whose left neighbour is
also `1`.

Informally: *to die, the machine must first stand in state `D` on a
`1` with another `1` immediately to its left* — because the only door
into the halting state `E` is the transition `D1`, which writes the
`0` back and steps left, so the cell `E` then dies on was already `1`
when `D` probed.  An unbounded question ("does it ever halt?") becomes
the reachability of a two-cell pattern. -/
theorem halt_requires_d_probe_11 {c : Config} (hne : c.state ≠ State.E)
    (hh : RawHalts c) :
    ∃ d : Config, Reaches c d ∧ d.state = State.D ∧
      d.tape d.head = true ∧ d.tape (d.head - 1) = true := by
  obtain ⟨n, hn⟩ := hh
  obtain ⟨k, _, d0, hd0, hstop⟩ := stepN_none_last n c hn
  have hE := (step_eq_none_iff d0).mp hstop
  cases k with
  | zero =>
      have hcd : c = d0 := by simpa [stepN] using hd0
      exact absurd (hcd ▸ hE.1) hne
  | succ k' =>
      obtain ⟨e, he, hstepe⟩ := stepN_some_pred k' c d0 hd0
      obtain ⟨hD, h1, hhead, htape⟩ := into_E_only_from_D1 hstepe hE.1
      refine ⟨e, ⟨k', he⟩, hD, h1, ?_⟩
      have hread : d0.tape d0.head = true := hE.2
      rw [htape, hhead] at hread
      rwa [writeAt_other e.tape e.head (e.head - 1) false (by omega)] at hread

/-- The D-probe-safety invariant: every `1` that state `D` reads in any
reachable configuration has a `0` immediately to its left.

Informally: a sentry condition.  If a `0` always guards the left flank
of whatever `D` probes, the fatal pattern of `halt_requires_d_probe_11`
can never occur, so the machine runs forever.  The rest of this file
exists to discharge this one predicate from the word-orbit dynamics. -/
def DProbeSafe (c : Config) : Prop :=
  ∀ d : Config, Reaches c d → d.state = State.D → d.tape d.head = true →
    d.tape (d.head - 1) = false

/-- D-probe safety implies the machine never halts. -/
theorem nonhalting_of_d_probe_safe {c : Config} (hne : c.state ≠ State.E)
    (hsafe : DProbeSafe c) : ¬ RawHalts c := by
  intro hh
  obtain ⟨d, hreach, hD, h1, h11⟩ := halt_requires_d_probe_11 hne hh
  have h0 := hsafe d hreach hD h1
  rw [h0] at h11
  exact Bool.noConfusion h11

/-- Specialization to the blank start. -/
theorem blank_nonhalting_of_d_probe_safe
    (hsafe : DProbeSafe blankStart) : ¬ RawHalts blankStart := by
  have hne : blankStart.state ≠ State.E := by
    simp [blankStart]
  exact nonhalting_of_d_probe_safe hne hsafe

/-!
## Segment safety machinery

Identical in structure to the dossier-6 layer: conditional probe
safety over the first `N` steps of a run, composition, and the
segment-induction keystone that turns finitely many episode theorems
into safety of the infinite run.
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

/-- Conditional D-probe safety over the first `N` steps of a run:
every `1` probed by state `D` has a `0` immediately to its left. -/
def DSafeSeg (c : Config) (N : Nat) : Prop :=
  ∀ k d, k < N → stepN k c = some d → d.state = State.D →
    d.tape d.head = true → d.tape (d.head - 1) = false

theorem dsafe_compose {c c' : Config} {m n : Nat}
    (hm : stepN m c = some c') (h1 : DSafeSeg c m) (h2 : DSafeSeg c' n) :
    DSafeSeg c (m + n) := by
  intro k d hk hkd hD hread
  by_cases hkm : k < m
  · exact h1 k d hkm hkd hD hread
  · have hkeq : k = m + (k - m) := by omega
    rw [hkeq, stepN_add, hm] at hkd
    exact h2 (k - m) d (by omega) hkd hD hread

theorem dsafe_mono {c : Config} {m n : Nat} (h : DSafeSeg c n)
    (hmn : m ≤ n) : DSafeSeg c m := by
  intro k d hk hkd hD hread
  exact h k d (by omega) hkd hD hread

/-- The segment-induction keystone: an invariant maintained by positive
safe segments gives `DProbeSafe` for the whole infinite run.

Informally: *safety in pieces is safety forever*.  If from every
invariant-satisfying configuration the machine runs some positive
number of steps safely and lands on the invariant again, then every
moment of the infinite run falls inside one of these safe segments —
strong induction on how many segments precede it. -/
theorem dprobe_safe_of_segments {Inv : Config → Prop} {c0 : Config}
    (h0 : Inv c0)
    (hseg : ∀ c, Inv c → ∃ k, 0 < k ∧ ∃ c', stepN k c = some c' ∧
      Inv c' ∧ DSafeSeg c k) :
    DProbeSafe c0 := by
  have main : ∀ (N n : Nat) (c : Config), n ≤ N → Inv c →
      ∀ d, stepN n c = some d → d.state = State.D →
        d.tape d.head = true → d.tape (d.head - 1) = false := by
    intro N
    induction N with
    | zero =>
        intro n c hn hInv d hd hD hread
        obtain ⟨k, hk, c', _hs, _hInv', hsafe⟩ := hseg c hInv
        exact hsafe n d (by omega) hd hD hread
    | succ N ihN =>
        intro n c hn hInv d hd hD hread
        obtain ⟨k, hk, c', hs, hInv', hsafe⟩ := hseg c hInv
        by_cases hlt : n < k
        · exact hsafe n d hlt hd hD hread
        · have hneq : n = k + (n - k) := by omega
          rw [hneq, stepN_add, hs] at hd
          exact ihN (n - k) c' (by omega) hInv' d hd hD hread
  intro d hreach hD hread
  obtain ⟨n, hn⟩ := hreach
  exact main n n c0 (Nat.le_refl n) h0 d hn hD hread

/-- Prefix safety plus tail safety gives whole-run safety. -/
theorem dprobe_safe_prefix {c d : Config} {M : Nat}
    (hM : stepN M c = some d)
    (hpre : DSafeSeg c M) (hpost : DProbeSafe d) : DProbeSafe c := by
  intro e hreach hD hread
  obtain ⟨n, hn⟩ := hreach
  by_cases h : n < M
  · exact hpre n e h hn hD hread
  · have hsplit : n = M + (n - M) := by omega
    rw [hsplit, stepN_add, hM] at hn
    exact hpost e ⟨n - M, hn⟩ hD hread

/-!
## The list foundation — words as `List Bool`

The dossier-5 abstract state is an unboundedly growing word.  Unlike
the fixed-integer grammars of dossiers 2/3/6, the tape here is pinned
by a *list* of cells laid out from a base position, with blank tape
outside.  (`ArrayShape`'s `List Nat` block-length language is the
grammar of on-orbit words; mid-orbit words carry bounded gap relics,
so the certified layer works one level down, on the raw cell list —
exactly the state of the validated trisection calculus.)  `getD`
with default `false` makes trailing blanks semantically invisible.
-/

theorem getD_oob :
    ∀ (l : List Bool) (n : Nat), l.length ≤ n → l.getD n false = false := by
  intro l
  induction l with
  | nil => intro n _; simp
  | cons a t ih =>
      intro n h
      cases n with
      | zero => simp at h
      | succ n =>
          rw [List.getD_cons_succ]
          exact ih n (by simp at h; omega)

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

theorem getD_app_lt :
    ∀ (l1 l2 : List Bool) (i : Nat), i < l1.length →
      (l1 ++ l2).getD i false = l1.getD i false := by
  intro l1
  induction l1 with
  | nil => intro l2 i h; simp at h
  | cons a t ih =>
      intro l2 i h
      cases i with
      | zero => rfl
      | succ i =>
          rw [show (a :: t) ++ l2 = a :: (t ++ l2) from rfl,
              List.getD_cons_succ, List.getD_cons_succ]
          exact ih l2 i (by simp at h; omega)

theorem getD_app_ge :
    ∀ (l1 l2 : List Bool) (i : Nat),
      (l1 ++ l2).getD (l1.length + i) false = l2.getD i false := by
  intro l1
  induction l1 with
  | nil => intro l2 i; simp
  | cons a t ih =>
      intro l2 i
      rw [show (a :: t) ++ l2 = a :: (t ++ l2) from rfl,
          show (a :: t).length + i = (t.length + i) + 1 by simp; omega,
          List.getD_cons_succ]
      exact ih l2 i

theorem getD_app_ge' (l1 l2 : List Bool) (i : Nat) (h : l1.length ≤ i) :
    (l1 ++ l2).getD i false = l2.getD (i - l1.length) false := by
  have hg := getD_app_ge l1 l2 (i - l1.length)
  rw [show l1.length + (i - l1.length) = i by omega] at hg
  exact hg

theorem getD_rev :
    ∀ (l : List Bool) (k : Nat), k < l.length →
      l.reverse.getD k false = l.getD (l.length - 1 - k) false := by
  intro l
  induction l with
  | nil => intro k h; simp at h
  | cons a t ih =>
      intro k h
      rw [List.reverse_cons]
      by_cases hk : k < t.length
      · rw [getD_app_lt _ _ _ (by simpa using hk), ih k hk,
            show (a :: t).length - 1 - k = (t.length - 1 - k) + 1 by
              simp; omega,
            List.getD_cons_succ]
      · have hke : k = t.length := by simp at h; omega
        subst hke
        rw [show t.length = t.reverse.length + 0 by simp, getD_app_ge,
            show (a :: t).length - 1 - (t.reverse.length + 0) = 0 by simp]
        rfl

theorem getD_take :
    ∀ (n : Nat) (l : List Bool) (i : Nat), i < n →
      (l.take n).getD i false = l.getD i false := by
  intro n
  induction n with
  | zero => intro l i h; omega
  | succ n ih =>
      intro l i h
      cases l with
      | nil => simp
      | cons a t =>
          cases i with
          | zero => rfl
          | succ i =>
              rw [show (a :: t).take (n + 1) = a :: t.take n from rfl,
                  List.getD_cons_succ, List.getD_cons_succ]
              exact ih t i (by omega)

/-!
## The pass invariant

Mid-sweep, the machine's whole configuration is pinned by two lists
and a base position: `em` — the cells *below* the head, nearest
first (a stack of everything the pass has laid down plus the
untouched prefix), and `rest` — the cells from the head upward
(head cell included, `rest.getD 0`).  All four sweep micro-moves are
local surgery on these two lists.
-/

/-- The mid-sweep configuration invariant: state `st`, head at
`base + em.length`, cells below the head read `em` (nearest first,
blank below `base` — subsumed by `getD`'s default), cells from the
head upward read `rest`. -/
def Inv (st : State) (base : Int) (em rest : List Bool) (cfg : Config) : Prop :=
  cfg.state = st ∧ cfg.head = base + em.length ∧
  (∀ k : Nat, cfg.tape (base + em.length - 1 - k) = em.getD k false) ∧
  (∀ j : Nat, cfg.tape (base + em.length + j) = rest.getD j false)

/-- An arrival configuration: state `B` at offset `poff` into the word
`w` laid out from `base`, blank tape strictly below `base`. -/
def ArrivalInv (base : Int) (w : List Bool) (poff : Nat) (cfg : Config) : Prop :=
  cfg.state = State.B ∧ cfg.head = base + poff ∧
  (∀ x : Int, x < base → cfg.tape x = false) ∧
  (∀ i : Nat, cfg.tape (base + i) = w.getD i false)

theorem inv_below {st : State} {base : Int} {em rest : List Bool}
    {cfg : Config} (h : Inv st base em rest cfg) :
    ∀ x : Int, x < base → cfg.tape x = false := by
  intro x hx
  obtain ⟨-, -, hdown, -⟩ := h
  have hk := hdown (em.length + (base - 1 - x).toNat)
  rw [show base + (em.length : Int) - 1 -
        ((em.length + (base - 1 - x).toNat : Nat) : Int) = x by omega] at hk
  rw [hk]
  exact getD_oob _ _ (by omega)

/-- `Inv` only sees `rest` through `getD`: representations differing
by list surgery that preserves every read are interchangeable. -/
theorem inv_congr_rest {st : State} {base : Int} {em rest1 rest2 : List Bool}
    {cfg : Config} (hg : ∀ j : Nat, rest1.getD j false = rest2.getD j false)
    (h : Inv st base em rest1 cfg) : Inv st base em rest2 cfg := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, fun j => (h4 j).trans (hg j)⟩

/-- Converting a completed sweep back to an arrival word: the word is
`em.reverse ++ rest`, the head offset is `em.length`. -/
theorem inv_to_arrival {base : Int} {em rest : List Bool} {cfg : Config}
    (h : Inv State.B base em rest cfg) :
    ArrivalInv base (em.reverse ++ rest) em.length cfg := by
  obtain ⟨h1, h2, hdown, hup⟩ := h
  refine ⟨h1, h2, inv_below ⟨h1, h2, hdown, hup⟩, ?_⟩
  intro i
  by_cases hi : i < em.length
  · rw [getD_app_lt _ _ _ (by simpa using hi), getD_rev _ _ (by simpa using hi)]
    have hk := hdown (em.length - 1 - i)
    rw [show base + (em.length : Int) - 1 -
          ((em.length - 1 - i : Nat) : Int) = base + i by omega] at hk
    rw [hk]
  · rw [getD_app_ge' _ _ _ (by simp; omega)]
    have hj := hup (i - em.length)
    rw [show base + (em.length : Int) + ((i - em.length : Nat) : Int)
          = base + i by omega] at hj
    rw [hj, List.length_reverse]

/-- Converting an arrival into the mid-sweep representation: below the
head the word prefix reversed, above it the suffix (head cell first,
reading `0`). -/
theorem arrival_to_inv {base : Int} {w : List Bool} {poff : Nat} {cfg : Config}
    (h : ArrivalInv base w poff cfg) (hle : poff ≤ w.length)
    (hread : w.getD poff false = false) :
    Inv State.B base ((w.take poff).reverse) (false :: w.drop (poff + 1)) cfg := by
  obtain ⟨h1, h2, hbelow, hat⟩ := h
  have hlen : ((w.take poff).reverse).length = poff := by
    simp [List.length_take]; omega
  refine ⟨h1, by rw [h2, hlen], ?_, ?_⟩
  · intro k
    rw [hlen]
    by_cases hk : k < poff
    · rw [getD_rev _ _ (by simp [List.length_take]; omega)]
      rw [show (w.take poff).length - 1 - k = poff - 1 - k by
            simp [List.length_take]; omega]
      rw [getD_take _ _ _ (by omega)]
      have hi := hat (poff - 1 - k)
      rw [show base + ((poff - 1 - k : Nat) : Int)
            = base + poff - 1 - k by omega] at hi
      exact hi
    · rw [getD_oob _ _ (by rw [hlen]; omega)]
      exact hbelow _ (by omega)
  · intro j
    cases j with
    | zero =>
        rw [hlen, List.getD_cons_zero,
            show base + (poff : Int) + ((0 : Nat) : Int) = base + poff by omega]
        have hi := hat poff
        rw [hi, hread]
    | succ j =>
        rw [hlen, List.getD_cons_succ, getD_drop]
        have hi := hat (poff + 1 + j)
        rw [show base + ((poff + 1 + j : Nat) : Int)
              = base + (poff : Int) + ((j + 1 : Nat) : Int) by omega] at hi
        exact hi

/-!
## One-step evaluator lemmas and term-mode chaining

Never rewrite on a `stepN` goal: chains are glued in term mode from
single-step evaluator lemmas (the standing proof-engineering
convention of this repository).
-/

theorem stepN_zero (c : Config) : stepN 0 c = some c := rfl

theorem stepN_succ_of_step {c d e : Config} {n : Nat}
    (h1 : step c = some d) (h2 : stepN n d = some e) :
    stepN (n + 1) c = some e := by
  rw [show stepN (n + 1) c = (step c).bind (stepN n) from rfl, h1]
  exact h2

theorem step_A0 {t : Int → Bool} {h : Int} (hr : t h = false) :
    step ⟨State.A, h, t⟩ = some ⟨State.B, h + 1, writeAt t h true⟩ := by
  simp [step, instr, hr, move]

theorem step_A1 {t : Int → Bool} {h : Int} (hr : t h = true) :
    step ⟨State.A, h, t⟩ = some ⟨State.D, h + 1, writeAt t h true⟩ := by
  simp [step, instr, hr, move]

theorem step_B {t : Int → Bool} {h : Int} {r : Bool} (hr : t h = r) :
    step ⟨State.B, h, t⟩ = some ⟨State.C, h - 1, writeAt t h (!r)⟩ := by
  cases r <;> simp [step, instr, hr, move]

theorem step_C0 {t : Int → Bool} {h : Int} (hr : t h = false) :
    step ⟨State.C, h, t⟩ = some ⟨State.D, h + 1, writeAt t h false⟩ := by
  simp [step, instr, hr, move]

theorem step_C1 {t : Int → Bool} {h : Int} (hr : t h = true) :
    step ⟨State.C, h, t⟩ = some ⟨State.B, h - 1, writeAt t h false⟩ := by
  simp [step, instr, hr, move]

theorem step_D0 {t : Int → Bool} {h : Int} (hr : t h = false) :
    step ⟨State.D, h, t⟩ = some ⟨State.F, h + 1, writeAt t h true⟩ := by
  simp [step, instr, hr, move]

theorem step_D1 {t : Int → Bool} {h : Int} (hr : t h = true) :
    step ⟨State.D, h, t⟩ = some ⟨State.E, h - 1, writeAt t h false⟩ := by
  simp [step, instr, hr, move]

theorem step_E0 {t : Int → Bool} {h : Int} (hr : t h = false) :
    step ⟨State.E, h, t⟩ = some ⟨State.D, h + 1, writeAt t h false⟩ := by
  simp [step, instr, hr, move]

theorem step_F0 {t : Int → Bool} {h : Int} (hr : t h = false) :
    step ⟨State.F, h, t⟩ = some ⟨State.A, h + 1, writeAt t h false⟩ := by
  simp [step, instr, hr, move]

theorem step_F1 {t : Int → Bool} {h : Int} (hr : t h = true) :
    step ⟨State.F, h, t⟩ = some ⟨State.C, h + 1, writeAt t h true⟩ := by
  simp [step, instr, hr, move]

/-!
## The sweep micro-episodes (phase 3, fine grain)

Instrumentation of 400k–20M raw steps (`instrument_rank1.py`,
`wstep_mirror.py`: 1249/1249 segments exact at 20M) shows every sweep
tiles into exactly five bounded micro-moves plus a parametric descent:

* `dip_step`     — `D` reads `1`: the 2-step `E`-probe dip.  The only
  place state `E` ever occurs; the guard `em.getD 0 = false` is
  exactly the D-probe-safety cell.
* `chunkA_step`  — `D` over `(0,0,1) ↦ (1,0,1)`, 3 steps (`D F A`).
* `chunkC_step`  — `D` over `(0,1,0) ↦ (1,1,0)`, 3 steps (`D F C`).
* `aterm_step`   — `D` over `(0,0,0) ↦ (1,0,1)`, 3 steps, ending in a
  `B` maximum-turn (the next word-level unit boundary or arrival).
* `c1turn_step`  — `D` over `(0,1,1) ↦ (1,1,0)`, 3 steps, ending in
  `B` one cell above the start (the `C1`-dance entry).
* `descend_*` / `descendExec` — the parametric leftward `B/C`
  alternation: the arrival shoot, every interior 6-step dance prefix,
  and the mini-arrival floor are all instances.

The classical unit rules of the trisection calculus (B-copy 12,
B-absorb 8, D-insert 12, D-regroup 8+6k) are proved below as
compositions of these.
-/

/-- Push three written cells below the head: the shared tape-algebra
of `chunkA`/`chunkC`/`aterm` (writes `v0 v1 v2` at `h, h+1, h+2`,
head to `h+3`). -/
theorem inv_push3 {st : State} {base : Int} {em rest : List Bool}
    {t : Int → Bool}
    (hdown : ∀ k : Nat, t (base + em.length - 1 - k) = em.getD k false)
    (hup : ∀ j : Nat, t (base + em.length + j) = rest.getD j false)
    (v0 v1 v2 : Bool) :
    Inv st base (v2 :: v1 :: v0 :: em) (rest.drop 3)
      ⟨st, base + em.length + 2 + 1,
        writeAt (writeAt (writeAt t (base + em.length) v0)
          (base + em.length + 1) v1) (base + em.length + 2) v2⟩ := by
  have hh : base + (em.length : Int) + 2 + 1
      = base + ((v2 :: v1 :: v0 :: em).length : Int) := by
    simp only [List.length_cons]; omega
  have hdown' : ∀ k : Nat,
      (writeAt (writeAt (writeAt t (base + (em.length : Int)) v0)
        (base + (em.length : Int) + 1) v1) (base + (em.length : Int) + 2) v2)
        (base + ((v2 :: v1 :: v0 :: em).length : Int) - 1 - (k : Int))
        = (v2 :: v1 :: v0 :: em).getD k false := by
    intro k
    simp only [List.length_cons]
    by_cases hk : k < 3
    · have hcase : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hcase with rfl | rfl | rfl
      · rw [show base + ((em.length + 1 + 1 + 1 : Nat) : Int) - 1 - ((0 : Nat) : Int)
              = base + (em.length : Int) + 2 by omega, writeAt_same]
        rfl
      · rw [show base + ((em.length + 1 + 1 + 1 : Nat) : Int) - 1 - ((1 : Nat) : Int)
              = base + (em.length : Int) + 1 by omega,
            writeAt_other _ _ _ _ (by omega), writeAt_same]
        rfl
      · rw [show base + ((em.length + 1 + 1 + 1 : Nat) : Int) - 1 - ((2 : Nat) : Int)
              = base + (em.length : Int) by omega,
            writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
            writeAt_same]
        rfl
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
      rw [show base + ((em.length + 1 + 1 + 1 : Nat) : Int) - 1 - ((k' + 3 : Nat) : Int)
            = base + (em.length : Int) - 1 - (k' : Int) by omega,
          writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ (by omega),
          List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
      exact hdown k'
  have hup' : ∀ j : Nat,
      (writeAt (writeAt (writeAt t (base + (em.length : Int)) v0)
        (base + (em.length : Int) + 1) v1) (base + (em.length : Int) + 2) v2)
        (base + ((v2 :: v1 :: v0 :: em).length : Int) + (j : Int))
        = (rest.drop 3).getD j false := by
    intro j
    simp only [List.length_cons]
    rw [show base + ((em.length + 1 + 1 + 1 : Nat) : Int) + (j : Int)
          = base + (em.length : Int) + ((3 + j : Nat) : Int) by omega,
        writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega), hup (3 + j), getD_drop]
  exact ⟨rfl, hh, hdown', hup'⟩

/-- The `E`-probe dip: `D` reads `1`, dips left through `E`, returns.
2 steps; the probed cell (`em.getD 0`) must be `0` — this is the
machine's entire mortality, localized. -/
theorem dip_step {base : Int} {em rest : List Bool} {cfg : Config}
    (hInv : Inv State.D base em rest cfg)
    (hc0 : rest.getD 0 false = true)
    (hguard : em.getD 0 false = false) :
    ∃ cfg', stepN 2 cfg = some cfg' ∧
      Inv State.D base em (false :: rest.drop 1) cfg' ∧ DSafeSeg cfg 2 := by
  obtain ⟨hst, hhd, hdown, hup⟩ := hInv
  obtain ⟨st, hd, t⟩ := cfg
  simp only at hst hhd hdown hup
  subst hst
  subst hhd
  have r0 : t (base + (em.length : Int)) = true := by
    have h := hup 0
    rw [show base + (em.length : Int) + ((0 : Nat) : Int)
          = base + (em.length : Int) by omega] at h
    rw [h]; exact hc0
  have rp : t (base + (em.length : Int) - 1) = false := by
    have h := hdown 0
    rw [show base + (em.length : Int) - 1 - ((0 : Nat) : Int)
          = base + (em.length : Int) - 1 by omega] at h
    rw [h]; exact hguard
  have s1 := step_D1 r0
  have rE : (writeAt t (base + (em.length : Int)) false)
      (base + (em.length : Int) - 1) = false := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact rp
  have s2 := step_E0 rE
  rw [show base + (em.length : Int) - 1 + 1 = base + (em.length : Int) by omega] at s2
  have hdown' : ∀ k : Nat,
      (writeAt (writeAt t (base + (em.length : Int)) false)
        (base + (em.length : Int) - 1) false)
        (base + (em.length : Int) - 1 - (k : Int)) = em.getD k false := by
    intro k
    cases k with
    | zero =>
        rw [show base + (em.length : Int) - 1 - ((0 : Nat) : Int)
              = base + (em.length : Int) - 1 by omega, writeAt_same]
        exact hguard.symm
    | succ k =>
        rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
        exact hdown (k + 1)
  have hup' : ∀ j : Nat,
      (writeAt (writeAt t (base + (em.length : Int)) false)
        (base + (em.length : Int) - 1) false)
        (base + (em.length : Int) + (j : Int))
        = (false :: rest.drop 1).getD j false := by
    intro j
    cases j with
    | zero =>
        rw [show base + (em.length : Int) + ((0 : Nat) : Int)
              = base + (em.length : Int) by omega,
            writeAt_other _ _ _ _ (by omega), writeAt_same]
        rfl
    | succ j =>
        rw [List.getD_cons_succ, getD_drop, Nat.add_comm 1 j,
            writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
        exact hup (j + 1)
  refine ⟨_, stepN_succ_of_step s1 (stepN_succ_of_step s2 (stepN_zero _)),
    ⟨rfl, rfl, hdown', hup'⟩, ?_⟩
  intro k d hk hkd hD hread
  have hcase : k = 0 ∨ k = 1 := by omega
  rcases hcase with rfl | rfl
  · have hdd : (⟨State.D, base + (em.length : Int), t⟩ : Config) = d := by
      simpa [stepN] using hkd
    rw [← hdd]
    exact rp
  · have hk1 : stepN 1 (⟨State.D, base + (em.length : Int), t⟩ : Config)
        = some ⟨State.E, base + (em.length : Int) - 1,
            writeAt t (base + (em.length : Int)) false⟩ :=
      stepN_succ_of_step s1 (stepN_zero _)
    rw [hk1] at hkd
    rw [← Option.some_inj.mp hkd] at hD
    simp at hD

/-- Rise chunk `dfa`: `D` over `(0,0,1) ↦ (1,0,1)` in 3 steps
(`D0 F0 A1`), staying in `D`. -/
theorem chunkA_step {base : Int} {em rest : List Bool} {cfg : Config}
    (hInv : Inv State.D base em rest cfg)
    (h0 : rest.getD 0 false = false) (h1 : rest.getD 1 false = false)
    (h2 : rest.getD 2 false = true) :
    ∃ cfg', stepN 3 cfg = some cfg' ∧
      Inv State.D base (true :: false :: true :: em) (rest.drop 3) cfg' ∧
      DSafeSeg cfg 3 := by
  obtain ⟨hst, hhd, hdown, hup⟩ := hInv
  obtain ⟨st, hd, t⟩ := cfg
  simp only at hst hhd hdown hup
  subst hst
  subst hhd
  have r0 : t (base + (em.length : Int)) = false := by
    have h := hup 0
    rw [show base + (em.length : Int) + ((0 : Nat) : Int)
          = base + (em.length : Int) by omega] at h
    rw [h]; exact h0
  have r1 : t (base + (em.length : Int) + 1) = false := by
    have h := hup 1
    rw [show base + (em.length : Int) + ((1 : Nat) : Int)
          = base + (em.length : Int) + 1 by omega] at h
    rw [h]; exact h1
  have r2 : t (base + (em.length : Int) + 2) = true := by
    have h := hup 2
    rw [show base + (em.length : Int) + ((2 : Nat) : Int)
          = base + (em.length : Int) + 2 by omega] at h
    rw [h]; exact h2
  have s1 := step_D0 r0
  have w1 : (writeAt t (base + (em.length : Int)) true)
      (base + (em.length : Int) + 1) = false := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact r1
  have s2 := step_F0 w1
  rw [show base + (em.length : Int) + 1 + 1 = base + (em.length : Int) + 2 by omega] at s2
  have w2 : (writeAt (writeAt t (base + (em.length : Int)) true)
      (base + (em.length : Int) + 1) false) (base + (em.length : Int) + 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact r2
  have s3 := step_A1 w2
  refine ⟨_, stepN_succ_of_step s1 (stepN_succ_of_step s2
      (stepN_succ_of_step s3 (stepN_zero _))),
    inv_push3 hdown hup true false true, ?_⟩
  intro k d hk hkd hD hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcase with rfl | rfl | rfl
  · have hdd : (⟨State.D, base + (em.length : Int), t⟩ : Config) = d := by
      simpa [stepN] using hkd
    rw [← hdd] at hread
    simp only at hread
    rw [r0] at hread
    exact absurd hread (by simp)
  · have hk1 : stepN 1 (⟨State.D, base + (em.length : Int), t⟩ : Config)
        = some ⟨State.F, base + (em.length : Int) + 1,
            writeAt t (base + (em.length : Int)) true⟩ :=
      stepN_succ_of_step s1 (stepN_zero _)
    rw [hk1] at hkd
    rw [← Option.some_inj.mp hkd] at hD
    simp at hD
  · have hk2 : stepN 2 (⟨State.D, base + (em.length : Int), t⟩ : Config)
        = some ⟨State.A, base + (em.length : Int) + 2,
            writeAt (writeAt t (base + (em.length : Int)) true)
              (base + (em.length : Int) + 1) false⟩ :=
      stepN_succ_of_step s1 (stepN_succ_of_step s2 (stepN_zero _))
    rw [hk2] at hkd
    rw [← Option.some_inj.mp hkd] at hD
    simp at hD

/-- Rise chunk `dfc`: `D` over `(0,1,0) ↦ (1,1,0)` in 3 steps
(`D0 F1 C0`), staying in `D`. -/
theorem chunkC_step {base : Int} {em rest : List Bool} {cfg : Config}
    (hInv : Inv State.D base em rest cfg)
    (h0 : rest.getD 0 false = false) (h1 : rest.getD 1 false = true)
    (h2 : rest.getD 2 false = false) :
    ∃ cfg', stepN 3 cfg = some cfg' ∧
      Inv State.D base (false :: true :: true :: em) (rest.drop 3) cfg' ∧
      DSafeSeg cfg 3 := by
  obtain ⟨hst, hhd, hdown, hup⟩ := hInv
  obtain ⟨st, hd, t⟩ := cfg
  simp only at hst hhd hdown hup
  subst hst
  subst hhd
  have r0 : t (base + (em.length : Int)) = false := by
    have h := hup 0
    rw [show base + (em.length : Int) + ((0 : Nat) : Int)
          = base + (em.length : Int) by omega] at h
    rw [h]; exact h0
  have r1 : t (base + (em.length : Int) + 1) = true := by
    have h := hup 1
    rw [show base + (em.length : Int) + ((1 : Nat) : Int)
          = base + (em.length : Int) + 1 by omega] at h
    rw [h]; exact h1
  have r2 : t (base + (em.length : Int) + 2) = false := by
    have h := hup 2
    rw [show base + (em.length : Int) + ((2 : Nat) : Int)
          = base + (em.length : Int) + 2 by omega] at h
    rw [h]; exact h2
  have s1 := step_D0 r0
  have w1 : (writeAt t (base + (em.length : Int)) true)
      (base + (em.length : Int) + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact r1
  have s2 := step_F1 w1
  rw [show base + (em.length : Int) + 1 + 1 = base + (em.length : Int) + 2 by omega] at s2
  have w2 : (writeAt (writeAt t (base + (em.length : Int)) true)
      (base + (em.length : Int) + 1) true) (base + (em.length : Int) + 2) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact r2
  have s3 := step_C0 w2
  refine ⟨_, stepN_succ_of_step s1 (stepN_succ_of_step s2
      (stepN_succ_of_step s3 (stepN_zero _))),
    inv_push3 hdown hup true true false, ?_⟩
  intro k d hk hkd hD hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcase with rfl | rfl | rfl
  · have hdd : (⟨State.D, base + (em.length : Int), t⟩ : Config) = d := by
      simpa [stepN] using hkd
    rw [← hdd] at hread
    simp only at hread
    rw [r0] at hread
    exact absurd hread (by simp)
  · have hk1 : stepN 1 (⟨State.D, base + (em.length : Int), t⟩ : Config)
        = some ⟨State.F, base + (em.length : Int) + 1,
            writeAt t (base + (em.length : Int)) true⟩ :=
      stepN_succ_of_step s1 (stepN_zero _)
    rw [hk1] at hkd
    rw [← Option.some_inj.mp hkd] at hD
    simp at hD
  · have hk2 : stepN 2 (⟨State.D, base + (em.length : Int), t⟩ : Config)
        = some ⟨State.C, base + (em.length : Int) + 2,
            writeAt (writeAt t (base + (em.length : Int)) true)
              (base + (em.length : Int) + 1) true⟩ :=
      stepN_succ_of_step s1 (stepN_succ_of_step s2 (stepN_zero _))
    rw [hk2] at hkd
    rw [← Option.some_inj.mp hkd] at hD
    simp at hD

/-- The arrival terminator: `D` over `(0,0,0) ↦ (1,0,1)` in 3 steps
(`D0 F0 A0`), ending in a `B` maximum-turn at `+3` — the boundary at
which the sweep either continues with a bounded dance or stops at the
next arrival. -/
theorem aterm_step {base : Int} {em rest : List Bool} {cfg : Config}
    (hInv : Inv State.D base em rest cfg)
    (h0 : rest.getD 0 false = false) (h1 : rest.getD 1 false = false)
    (h2 : rest.getD 2 false = false) :
    ∃ cfg', stepN 3 cfg = some cfg' ∧
      Inv State.B base (true :: false :: true :: em) (rest.drop 3) cfg' ∧
      DSafeSeg cfg 3 := by
  obtain ⟨hst, hhd, hdown, hup⟩ := hInv
  obtain ⟨st, hd, t⟩ := cfg
  simp only at hst hhd hdown hup
  subst hst
  subst hhd
  have r0 : t (base + (em.length : Int)) = false := by
    have h := hup 0
    rw [show base + (em.length : Int) + ((0 : Nat) : Int)
          = base + (em.length : Int) by omega] at h
    rw [h]; exact h0
  have r1 : t (base + (em.length : Int) + 1) = false := by
    have h := hup 1
    rw [show base + (em.length : Int) + ((1 : Nat) : Int)
          = base + (em.length : Int) + 1 by omega] at h
    rw [h]; exact h1
  have r2 : t (base + (em.length : Int) + 2) = false := by
    have h := hup 2
    rw [show base + (em.length : Int) + ((2 : Nat) : Int)
          = base + (em.length : Int) + 2 by omega] at h
    rw [h]; exact h2
  have s1 := step_D0 r0
  have w1 : (writeAt t (base + (em.length : Int)) true)
      (base + (em.length : Int) + 1) = false := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact r1
  have s2 := step_F0 w1
  rw [show base + (em.length : Int) + 1 + 1 = base + (em.length : Int) + 2 by omega] at s2
  have w2 : (writeAt (writeAt t (base + (em.length : Int)) true)
      (base + (em.length : Int) + 1) false) (base + (em.length : Int) + 2) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact r2
  have s3 := step_A0 w2
  refine ⟨_, stepN_succ_of_step s1 (stepN_succ_of_step s2
      (stepN_succ_of_step s3 (stepN_zero _))),
    inv_push3 hdown hup true false true, ?_⟩
  intro k d hk hkd hD hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcase with rfl | rfl | rfl
  · have hdd : (⟨State.D, base + (em.length : Int), t⟩ : Config) = d := by
      simpa [stepN] using hkd
    rw [← hdd] at hread
    simp only at hread
    rw [r0] at hread
    exact absurd hread (by simp)
  · have hk1 : stepN 1 (⟨State.D, base + (em.length : Int), t⟩ : Config)
        = some ⟨State.F, base + (em.length : Int) + 1,
            writeAt t (base + (em.length : Int)) true⟩ :=
      stepN_succ_of_step s1 (stepN_zero _)
    rw [hk1] at hkd
    rw [← Option.some_inj.mp hkd] at hD
    simp at hD
  · have hk2 : stepN 2 (⟨State.D, base + (em.length : Int), t⟩ : Config)
        = some ⟨State.A, base + (em.length : Int) + 2,
            writeAt (writeAt t (base + (em.length : Int)) true)
              (base + (em.length : Int) + 1) false⟩ :=
      stepN_succ_of_step s1 (stepN_succ_of_step s2 (stepN_zero _))
    rw [hk2] at hkd
    rw [← Option.some_inj.mp hkd] at hD
    simp at hD

/-- The `C1` turn: `D` over `(0,1,1) ↦ (1,1,0)` in 3 steps
(`D0 F1 C1`), ending in state `B` one cell *above* the start — the
entry into the interior `C1`-dance (a shallow descent follows). -/
theorem c1turn_step {base : Int} {em rest : List Bool} {cfg : Config}
    (hInv : Inv State.D base em rest cfg)
    (h0 : rest.getD 0 false = false) (h1 : rest.getD 1 false = true)
    (h2 : rest.getD 2 false = true) :
    ∃ cfg', stepN 3 cfg = some cfg' ∧
      Inv State.B base (true :: em) (true :: false :: rest.drop 3) cfg' ∧
      DSafeSeg cfg 3 := by
  obtain ⟨hst, hhd, hdown, hup⟩ := hInv
  obtain ⟨st, hd, t⟩ := cfg
  simp only at hst hhd hdown hup
  subst hst
  subst hhd
  have r0 : t (base + (em.length : Int)) = false := by
    have h := hup 0
    rw [show base + (em.length : Int) + ((0 : Nat) : Int)
          = base + (em.length : Int) by omega] at h
    rw [h]; exact h0
  have r1 : t (base + (em.length : Int) + 1) = true := by
    have h := hup 1
    rw [show base + (em.length : Int) + ((1 : Nat) : Int)
          = base + (em.length : Int) + 1 by omega] at h
    rw [h]; exact h1
  have r2 : t (base + (em.length : Int) + 2) = true := by
    have h := hup 2
    rw [show base + (em.length : Int) + ((2 : Nat) : Int)
          = base + (em.length : Int) + 2 by omega] at h
    rw [h]; exact h2
  have s1 := step_D0 r0
  have w1 : (writeAt t (base + (em.length : Int)) true)
      (base + (em.length : Int) + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact r1
  have s2 := step_F1 w1
  rw [show base + (em.length : Int) + 1 + 1 = base + (em.length : Int) + 2 by omega] at s2
  have w2 : (writeAt (writeAt t (base + (em.length : Int)) true)
      (base + (em.length : Int) + 1) true) (base + (em.length : Int) + 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact r2
  have s3 := step_C1 w2
  rw [show base + (em.length : Int) + 2 - 1 = base + (em.length : Int) + 1 by omega] at s3
  have hh : base + (em.length : Int) + 1 = base + (((true :: em).length : Nat) : Int) := by
    simp only [List.length_cons]; omega
  have hdown' : ∀ k : Nat,
      (writeAt (writeAt (writeAt t (base + (em.length : Int)) true)
        (base + (em.length : Int) + 1) true) (base + (em.length : Int) + 2) false)
        (base + (((true :: em).length : Nat) : Int) - 1 - (k : Int))
        = (true :: em).getD k false := by
    intro k
    simp only [List.length_cons]
    cases k with
    | zero =>
        rw [show base + ((em.length + 1 : Nat) : Int) - 1 - ((0 : Nat) : Int)
              = base + (em.length : Int) by omega,
            writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
            writeAt_same]
        rfl
    | succ k =>
        rw [show base + ((em.length + 1 : Nat) : Int) - 1 - ((k + 1 : Nat) : Int)
              = base + (em.length : Int) - 1 - (k : Int) by omega,
            writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
            writeAt_other _ _ _ _ (by omega), List.getD_cons_succ]
        exact hdown k
  have hup' : ∀ j : Nat,
      (writeAt (writeAt (writeAt t (base + (em.length : Int)) true)
        (base + (em.length : Int) + 1) true) (base + (em.length : Int) + 2) false)
        (base + (((true :: em).length : Nat) : Int) + (j : Int))
        = (true :: false :: rest.drop 3).getD j false := by
    intro j
    simp only [List.length_cons]
    by_cases hj : j < 2
    · have hcase : j = 0 ∨ j = 1 := by omega
      rcases hcase with rfl | rfl
      · rw [show base + ((em.length + 1 : Nat) : Int) + ((0 : Nat) : Int)
              = base + (em.length : Int) + 1 by omega,
            writeAt_other _ _ _ _ (by omega), writeAt_same]
        rfl
      · rw [show base + ((em.length + 1 : Nat) : Int) + ((1 : Nat) : Int)
              = base + (em.length : Int) + 2 by omega, writeAt_same]
        rfl
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
      rw [show base + ((em.length + 1 : Nat) : Int) + ((j' + 2 : Nat) : Int)
            = base + (em.length : Int) + ((3 + j' : Nat) : Int) by omega,
          writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ (by omega), hup (3 + j'),
          List.getD_cons_succ, List.getD_cons_succ, getD_drop]
  refine ⟨_, stepN_succ_of_step s1 (stepN_succ_of_step s2
      (stepN_succ_of_step s3 (stepN_zero _))), ⟨rfl, hh, hdown', hup'⟩, ?_⟩
  intro k d hk hkd hD hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcase with rfl | rfl | rfl
  · have hdd : (⟨State.D, base + (em.length : Int), t⟩ : Config) = d := by
      simpa [stepN] using hkd
    rw [← hdd] at hread
    simp only at hread
    rw [r0] at hread
    exact absurd hread (by simp)
  · have hk1 : stepN 1 (⟨State.D, base + (em.length : Int), t⟩ : Config)
        = some ⟨State.F, base + (em.length : Int) + 1,
            writeAt t (base + (em.length : Int)) true⟩ :=
      stepN_succ_of_step s1 (stepN_zero _)
    rw [hk1] at hkd
    rw [← Option.some_inj.mp hkd] at hD
    simp at hD
  · have hk2 : stepN 2 (⟨State.D, base + (em.length : Int), t⟩ : Config)
        = some ⟨State.C, base + (em.length : Int) + 2,
            writeAt (writeAt t (base + (em.length : Int)) true)
              (base + (em.length : Int) + 1) true⟩ :=
      stepN_succ_of_step s1 (stepN_succ_of_step s2 (stepN_zero _))
    rw [hk2] at hkd
    rw [← Option.some_inj.mp hkd] at hD
    simp at hD


/-!
## The parametric descent (the shoot, the dances, the mini floor)

Leftward travel is a strict `B/C` alternation: `B` flips the cell it
reads, `C` needs a `1` (writing `0`) to continue and turns right on a
`0`.  `descendExec` executes it as list surgery on the stack `em`:
the four constructor cases are the immediate turn, the two
blank-region terminations below `base` (the *full-arrival* far end,
extending the left extreme by 1 or 2), and the two-cell recursion.
Every shoot, every interior 6-step dance prefix, and every
mini-arrival floor stop is an instance of this one function.
Cost: exactly one raw step per visited cell, plus the turn. -/
def descendExec : List Bool → Bool → List Bool → Nat × Nat × List Bool × List Bool
  | [], r, rest => (2, 1, [false], (!r) :: rest)
  | [true], r, rest => (4, 2, [false], true :: false :: (!r) :: rest)
  | false :: em2, r, rest => (2, 0, false :: em2, (!r) :: rest)
  | true :: b :: em2, r, rest =>
      ((descendExec em2 b (false :: (!r) :: rest)).1 + 2,
       (descendExec em2 b (false :: (!r) :: rest)).2)

theorem descend_nil {base : Int} {r : Bool} {rest : List Bool} {cfg : Config}
    (hInv : Inv State.B base [] (r :: rest) cfg) :
    ∃ cfg', stepN 2 cfg = some cfg' ∧
      Inv State.D (base - 1) [false] ((!r) :: rest) cfg' ∧ DSafeSeg cfg 2 := by
  obtain ⟨hst, hhd, hdown, hup⟩ := hInv
  obtain ⟨st, hd, t⟩ := cfg
  simp only at hst hhd hdown hup
  simp only [List.length_nil] at hhd hdown hup
  subst hst
  subst hhd
  rw [show base + ((0 : Nat) : Int) = base by omega]
  have r0 : t base = r := by
    have h := hup 0
    rw [show base + ((0 : Nat) : Int) + ((0 : Nat) : Int) = base by omega] at h
    exact h
  have rd0 : t (base - 1) = false := by
    have h := hdown 0
    rw [show base + ((0 : Nat) : Int) - 1 - ((0 : Nat) : Int) = base - 1 by omega] at h
    exact h
  have s1 := step_B r0
  have w1 : (writeAt t base (!r)) (base - 1) = false := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact rd0
  have s2 := step_C0 w1
  rw [show base - 1 + 1 = base by omega] at s2
  have hh : base = base - 1 + (((false :: ([] : List Bool)).length : Nat) : Int) := by
    simp only [List.length_cons, List.length_nil]; omega
  have hdown' : ∀ k : Nat,
      (writeAt (writeAt t base (!r)) (base - 1) false)
        (base - 1 + (((false :: ([] : List Bool)).length : Nat) : Int) - 1 - (k : Int))
        = (false :: ([] : List Bool)).getD k false := by
    intro k
    simp only [List.length_cons, List.length_nil]
    cases k with
    | zero =>
        rw [show base - 1 + ((0 + 1 : Nat) : Int) - 1 - ((0 : Nat) : Int)
              = base - 1 by omega, writeAt_same]
        rfl
    | succ k =>
        rw [show base - 1 + ((0 + 1 : Nat) : Int) - 1 - ((k + 1 : Nat) : Int)
              = base + ((0 : Nat) : Int) - 1 - ((k + 1 : Nat) : Int) by omega,
            writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
        exact hdown (k + 1)
  have hup' : ∀ j : Nat,
      (writeAt (writeAt t base (!r)) (base - 1) false)
        (base - 1 + (((false :: ([] : List Bool)).length : Nat) : Int) + (j : Int))
        = ((!r) :: rest).getD j false := by
    intro j
    simp only [List.length_cons, List.length_nil]
    cases j with
    | zero =>
        rw [show base - 1 + ((0 + 1 : Nat) : Int) + ((0 : Nat) : Int) = base by omega,
            writeAt_other _ _ _ _ (by omega), writeAt_same]
        rfl
    | succ j =>
        rw [show base - 1 + ((0 + 1 : Nat) : Int) + ((j + 1 : Nat) : Int)
              = base + ((0 : Nat) : Int) + ((j + 1 : Nat) : Int) by omega,
            writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
        exact hup (j + 1)
  refine ⟨_, stepN_succ_of_step s1 (stepN_succ_of_step s2 (stepN_zero _)),
    ⟨rfl, hh, hdown', hup'⟩, ?_⟩
  intro k d hk hkd hD hread
  have hcase : k = 0 ∨ k = 1 := by omega
  rcases hcase with rfl | rfl
  · have hdd : (⟨State.B, base, t⟩ : Config) = d := by
      simpa [stepN] using hkd
    rw [← hdd] at hD
    simp at hD
  · have hk1 : stepN 1 (⟨State.B, base, t⟩ : Config)
        = some ⟨State.C, base - 1, writeAt t base (!r)⟩ :=
      stepN_succ_of_step s1 (stepN_zero _)
    rw [hk1] at hkd
    rw [← Option.some_inj.mp hkd] at hD
    simp at hD

theorem descend_single {base : Int} {r : Bool} {rest : List Bool} {cfg : Config}
    (hInv : Inv State.B base [true] (r :: rest) cfg) :
    ∃ cfg', stepN 4 cfg = some cfg' ∧
      Inv State.D (base - 2) [false] (true :: false :: (!r) :: rest) cfg' ∧
      DSafeSeg cfg 4 := by
  obtain ⟨hst, hhd, hdown, hup⟩ := hInv
  obtain ⟨st, hd, t⟩ := cfg
  simp only at hst hhd hdown hup
  simp only [List.length_cons, List.length_nil] at hhd hdown hup
  subst hst
  subst hhd
  rw [show base + ((0 + 1 : Nat) : Int) = base + 1 by omega]
  have r0 : t (base + 1) = r := by
    have h := hup 0
    rw [show base + ((0 + 1 : Nat) : Int) + ((0 : Nat) : Int) = base + 1 by omega] at h
    exact h
  have rd0 : t base = true := by
    have h := hdown 0
    rw [show base + ((0 + 1 : Nat) : Int) - 1 - ((0 : Nat) : Int) = base by omega] at h
    exact h
  have rd1 : t (base - 1) = false := by
    have h := hdown 1
    rw [show base + ((0 + 1 : Nat) : Int) - 1 - ((1 : Nat) : Int) = base - 1 by omega] at h
    exact h
  have rd2 : t (base - 2) = false := by
    have h := hdown 2
    rw [show base + ((0 + 1 : Nat) : Int) - 1 - ((2 : Nat) : Int) = base - 2 by omega] at h
    exact h
  have s1 := step_B r0
  rw [show base + 1 - 1 = base by omega] at s1
  have w1 : (writeAt t (base + 1) (!r)) base = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact rd0
  have s2 := step_C1 w1
  have w2 : (writeAt (writeAt t (base + 1) (!r)) base false) (base - 1) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact rd1
  have s3 := step_B w2
  simp only [Bool.not_false] at s3
  rw [show base - 1 - 1 = base - 2 by omega] at s3
  have w3 : (writeAt (writeAt (writeAt t (base + 1) (!r)) base false) (base - 1) true)
      (base - 2) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega)]
    exact rd2
  have s4 := step_C0 w3
  rw [show base - 2 + 1 = base - 1 by omega] at s4
  have hh : base - 1 = base - 2 + (((false :: ([] : List Bool)).length : Nat) : Int) := by
    simp only [List.length_cons, List.length_nil]; omega
  have hdown' : ∀ k : Nat,
      (writeAt (writeAt (writeAt (writeAt t (base + 1) (!r)) base false)
        (base - 1) true) (base - 2) false)
        (base - 2 + (((false :: ([] : List Bool)).length : Nat) : Int) - 1 - (k : Int))
        = (false :: ([] : List Bool)).getD k false := by
    intro k
    simp only [List.length_cons, List.length_nil]
    cases k with
    | zero =>
        rw [show base - 2 + ((0 + 1 : Nat) : Int) - 1 - ((0 : Nat) : Int)
              = base - 2 by omega, writeAt_same]
        rfl
    | succ k =>
        rw [show base - 2 + ((0 + 1 : Nat) : Int) - 1 - ((k + 1 : Nat) : Int)
              = base + ((0 + 1 : Nat) : Int) - 1 - ((k + 3 : Nat) : Int) by omega,
            writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
            writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
        exact hdown (k + 3)
  have hup' : ∀ j : Nat,
      (writeAt (writeAt (writeAt (writeAt t (base + 1) (!r)) base false)
        (base - 1) true) (base - 2) false)
        (base - 2 + (((false :: ([] : List Bool)).length : Nat) : Int) + (j : Int))
        = (true :: false :: (!r) :: rest).getD j false := by
    intro j
    simp only [List.length_cons, List.length_nil]
    by_cases hj : j < 3
    · have hcase : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hcase with rfl | rfl | rfl
      · rw [show base - 2 + ((0 + 1 : Nat) : Int) + ((0 : Nat) : Int)
              = base - 1 by omega,
            writeAt_other _ _ _ _ (by omega), writeAt_same]
        rfl
      · rw [show base - 2 + ((0 + 1 : Nat) : Int) + ((1 : Nat) : Int)
              = base by omega,
            writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
            writeAt_same]
        rfl
      · rw [show base - 2 + ((0 + 1 : Nat) : Int) + ((2 : Nat) : Int)
              = base + 1 by omega,
            writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
            writeAt_other _ _ _ _ (by omega), writeAt_same]
        rfl
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 3 := ⟨j - 3, by omega⟩
      rw [show base - 2 + ((0 + 1 : Nat) : Int) + ((j' + 3 : Nat) : Int)
            = base + ((0 + 1 : Nat) : Int) + ((j' + 1 : Nat) : Int) by omega,
          writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
      exact hup (j' + 1)
  refine ⟨_, stepN_succ_of_step s1 (stepN_succ_of_step s2 (stepN_succ_of_step s3
      (stepN_succ_of_step s4 (stepN_zero _)))),
    ⟨rfl, hh, hdown', hup'⟩, ?_⟩
  intro k d hk hkd hD hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hcase with rfl | rfl | rfl | rfl
  · have hdd : (⟨State.B, base + 1, t⟩ : Config) = d := by
      simpa [stepN] using hkd
    rw [← hdd] at hD
    simp at hD
  · have hk1 : stepN 1 (⟨State.B, base + 1, t⟩ : Config)
        = some ⟨State.C, base, writeAt t (base + 1) (!r)⟩ :=
      stepN_succ_of_step s1 (stepN_zero _)
    rw [hk1] at hkd
    rw [← Option.some_inj.mp hkd] at hD
    simp at hD
  · have hk2 : stepN 2 (⟨State.B, base + 1, t⟩ : Config)
        = some ⟨State.B, base - 1, writeAt (writeAt t (base + 1) (!r)) base false⟩ :=
      stepN_succ_of_step s1 (stepN_succ_of_step s2 (stepN_zero _))
    rw [hk2] at hkd
    rw [← Option.some_inj.mp hkd] at hD
    simp at hD
  · have hk3 : stepN 3 (⟨State.B, base + 1, t⟩ : Config)
        = some ⟨State.C, base - 2,
            writeAt (writeAt (writeAt t (base + 1) (!r)) base false) (base - 1) true⟩ :=
      stepN_succ_of_step s1 (stepN_succ_of_step s2 (stepN_succ_of_step s3 (stepN_zero _)))
    rw [hk3] at hkd
    rw [← Option.some_inj.mp hkd] at hD
    simp at hD

theorem descend_stop {base : Int} {em2 : List Bool} {r : Bool} {rest : List Bool}
    {cfg : Config}
    (hInv : Inv State.B base (false :: em2) (r :: rest) cfg) :
    ∃ cfg', stepN 2 cfg = some cfg' ∧
      Inv State.D base (false :: em2) ((!r) :: rest) cfg' ∧ DSafeSeg cfg 2 := by
  obtain ⟨hst, hhd, hdown, hup⟩ := hInv
  obtain ⟨st, hd, t⟩ := cfg
  simp only at hst hhd hdown hup
  simp only [List.length_cons] at hhd hdown hup
  subst hst
  subst hhd
  have r0 : t (base + ((em2.length + 1 : Nat) : Int)) = r := by
    have h := hup 0
    rw [show base + ((em2.length + 1 : Nat) : Int) + ((0 : Nat) : Int)
          = base + ((em2.length + 1 : Nat) : Int) by omega] at h
    exact h
  have rd0 : t (base + ((em2.length + 1 : Nat) : Int) - 1) = false := by
    have h := hdown 0
    rw [show base + ((em2.length + 1 : Nat) : Int) - 1 - ((0 : Nat) : Int)
          = base + ((em2.length + 1 : Nat) : Int) - 1 by omega] at h
    exact h
  have s1 := step_B r0
  have w1 : (writeAt t (base + ((em2.length + 1 : Nat) : Int)) (!r))
      (base + ((em2.length + 1 : Nat) : Int) - 1) = false := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact rd0
  have s2 := step_C0 w1
  rw [show base + ((em2.length + 1 : Nat) : Int) - 1 + 1
        = base + ((em2.length + 1 : Nat) : Int) by omega] at s2
  have hdown' : ∀ k : Nat,
      (writeAt (writeAt t (base + ((em2.length + 1 : Nat) : Int)) (!r))
        (base + ((em2.length + 1 : Nat) : Int) - 1) false)
        (base + (((false :: em2).length : Nat) : Int) - 1 - (k : Int))
        = (false :: em2).getD k false := by
    intro k
    simp only [List.length_cons]
    cases k with
    | zero =>
        rw [show base + ((em2.length + 1 : Nat) : Int) - 1 - ((0 : Nat) : Int)
              = base + ((em2.length + 1 : Nat) : Int) - 1 by omega, writeAt_same]
        rfl
    | succ k =>
        rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
        exact hdown (k + 1)
  have hup' : ∀ j : Nat,
      (writeAt (writeAt t (base + ((em2.length + 1 : Nat) : Int)) (!r))
        (base + ((em2.length + 1 : Nat) : Int) - 1) false)
        (base + (((false :: em2).length : Nat) : Int) + (j : Int))
        = ((!r) :: rest).getD j false := by
    intro j
    simp only [List.length_cons]
    cases j with
    | zero =>
        rw [show base + ((em2.length + 1 : Nat) : Int) + ((0 : Nat) : Int)
              = base + ((em2.length + 1 : Nat) : Int) by omega,
            writeAt_other _ _ _ _ (by omega), writeAt_same]
        rfl
    | succ j =>
        rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
        exact hup (j + 1)
  refine ⟨_, stepN_succ_of_step s1 (stepN_succ_of_step s2 (stepN_zero _)),
    ⟨rfl, by simp only [List.length_cons], hdown', hup'⟩, ?_⟩
  intro k d hk hkd hD hread
  have hcase : k = 0 ∨ k = 1 := by omega
  rcases hcase with rfl | rfl
  · have hdd : (⟨State.B, base + ((em2.length + 1 : Nat) : Int), t⟩ : Config) = d := by
      simpa [stepN] using hkd
    rw [← hdd] at hD
    simp at hD
  · have hk1 : stepN 1 (⟨State.B, base + ((em2.length + 1 : Nat) : Int), t⟩ : Config)
        = some ⟨State.C, base + ((em2.length + 1 : Nat) : Int) - 1,
            writeAt t (base + ((em2.length + 1 : Nat) : Int)) (!r)⟩ :=
      stepN_succ_of_step s1 (stepN_zero _)
    rw [hk1] at hkd
    rw [← Option.some_inj.mp hkd] at hD
    simp at hD

theorem descend_pair {base : Int} {b : Bool} {em2 : List Bool} {r : Bool}
    {rest : List Bool} {cfg : Config}
    (hInv : Inv State.B base (true :: b :: em2) (r :: rest) cfg) :
    ∃ cfg', stepN 2 cfg = some cfg' ∧
      Inv State.B base em2 (b :: false :: (!r) :: rest) cfg' ∧ DSafeSeg cfg 2 := by
  obtain ⟨hst, hhd, hdown, hup⟩ := hInv
  obtain ⟨st, hd, t⟩ := cfg
  simp only at hst hhd hdown hup
  simp only [List.length_cons] at hhd hdown hup
  subst hst
  subst hhd
  have r0 : t (base + ((em2.length + 1 + 1 : Nat) : Int)) = r := by
    have h := hup 0
    rw [show base + ((em2.length + 1 + 1 : Nat) : Int) + ((0 : Nat) : Int)
          = base + ((em2.length + 1 + 1 : Nat) : Int) by omega] at h
    exact h
  have rd0 : t (base + ((em2.length + 1 + 1 : Nat) : Int) - 1) = true := by
    have h := hdown 0
    rw [show base + ((em2.length + 1 + 1 : Nat) : Int) - 1 - ((0 : Nat) : Int)
          = base + ((em2.length + 1 + 1 : Nat) : Int) - 1 by omega] at h
    exact h
  have s1 := step_B r0
  have w1 : (writeAt t (base + ((em2.length + 1 + 1 : Nat) : Int)) (!r))
      (base + ((em2.length + 1 + 1 : Nat) : Int) - 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact rd0
  have s2 := step_C1 w1
  rw [show base + ((em2.length + 1 + 1 : Nat) : Int) - 1 - 1
        = base + ((em2.length : Nat) : Int) by omega] at s2
  have hdown' : ∀ k : Nat,
      (writeAt (writeAt t (base + ((em2.length + 1 + 1 : Nat) : Int)) (!r))
        (base + ((em2.length + 1 + 1 : Nat) : Int) - 1) false)
        (base + ((em2.length : Nat) : Int) - 1 - (k : Int))
        = em2.getD k false := by
    intro k
    have hdk := hdown (k + 2)
    rw [show base + ((em2.length + 1 + 1 : Nat) : Int) - 1 - ((k + 2 : Nat) : Int)
          = base + ((em2.length : Nat) : Int) - 1 - (k : Int) by omega] at hdk
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact hdk
  have hup' : ∀ j : Nat,
      (writeAt (writeAt t (base + ((em2.length + 1 + 1 : Nat) : Int)) (!r))
        (base + ((em2.length + 1 + 1 : Nat) : Int) - 1) false)
        (base + ((em2.length : Nat) : Int) + (j : Int))
        = (b :: false :: (!r) :: rest).getD j false := by
    intro j
    by_cases hj : j < 3
    · have hcase : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hcase with rfl | rfl | rfl
      · have hd1 := hdown 1
        rw [show base + ((em2.length + 1 + 1 : Nat) : Int) - 1 - ((1 : Nat) : Int)
              = base + ((em2.length : Nat) : Int) by omega] at hd1
        rw [show base + ((em2.length : Nat) : Int) + ((0 : Nat) : Int)
              = base + ((em2.length : Nat) : Int) by omega,
            writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
        exact hd1
      · rw [show base + ((em2.length : Nat) : Int) + ((1 : Nat) : Int)
              = base + ((em2.length + 1 + 1 : Nat) : Int) - 1 by omega,
            writeAt_same]
        rfl
      · rw [show base + ((em2.length : Nat) : Int) + ((2 : Nat) : Int)
              = base + ((em2.length + 1 + 1 : Nat) : Int) by omega,
            writeAt_other _ _ _ _ (by omega), writeAt_same]
        rfl
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 3 := ⟨j - 3, by omega⟩
      rw [show base + ((em2.length : Nat) : Int) + ((j' + 3 : Nat) : Int)
            = base + ((em2.length + 1 + 1 : Nat) : Int) + ((j' + 1 : Nat) : Int) by omega,
          writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
      exact hup (j' + 1)
  refine ⟨_, stepN_succ_of_step s1 (stepN_succ_of_step s2 (stepN_zero _)),
    ⟨rfl, rfl, hdown', hup'⟩, ?_⟩
  intro k d hk hkd hD hread
  have hcase : k = 0 ∨ k = 1 := by omega
  rcases hcase with rfl | rfl
  · have hdd : (⟨State.B, base + ((em2.length + 1 + 1 : Nat) : Int), t⟩ : Config) = d := by
      simpa [stepN] using hkd
    rw [← hdd] at hD
    simp at hD
  · have hk1 : stepN 1 (⟨State.B, base + ((em2.length + 1 + 1 : Nat) : Int), t⟩ : Config)
        = some ⟨State.C, base + ((em2.length + 1 + 1 : Nat) : Int) - 1,
            writeAt t (base + ((em2.length + 1 + 1 : Nat) : Int)) (!r)⟩ :=
      stepN_succ_of_step s1 (stepN_zero _)
    rw [hk1] at hkd
    rw [← Option.some_inj.mp hkd] at hD
    simp at hD

/-- Faithfulness of the executed descent, by strong induction on the
stack.  The raw machine runs exactly `(descendExec em r rest).1` steps
from any realization and lands in state `D` on the returned
configuration, with the base shifted by the returned extreme
extension; no `D`-probe occurs anywhere in a descent. -/
theorem descendExec_faithful :
    ∀ (n : Nat) (em : List Bool), em.length ≤ n →
      ∀ (r : Bool) (rest : List Bool) (base : Int) (cfg : Config),
        Inv State.B base em (r :: rest) cfg →
        ∃ cfg', stepN (descendExec em r rest).1 cfg = some cfg' ∧
          Inv State.D (base - (((descendExec em r rest).2.1 : Nat) : Int))
            (descendExec em r rest).2.2.1 (descendExec em r rest).2.2.2 cfg' ∧
          DSafeSeg cfg (descendExec em r rest).1 := by
  intro n
  induction n with
  | zero =>
      intro em hlen r rest base cfg hInv
      cases em with
      | nil =>
          obtain ⟨cfg', h1, h2, h3⟩ := descend_nil hInv
          simp only [descendExec]
          rw [show base - ((1 : Nat) : Int) = base - 1 by omega]
          exact ⟨cfg', h1, h2, h3⟩
      | cons c em2 => simp at hlen
  | succ n ih =>
      intro em hlen r rest base cfg hInv
      rcases em with _ | ⟨c, em2⟩
      · obtain ⟨cfg', h1, h2, h3⟩ := descend_nil hInv
        simp only [descendExec]
        rw [show base - ((1 : Nat) : Int) = base - 1 by omega]
        exact ⟨cfg', h1, h2, h3⟩
      · cases c
        · obtain ⟨cfg', h1, h2, h3⟩ := descend_stop hInv
          simp only [descendExec]
          rw [show base - ((0 : Nat) : Int) = base by omega]
          exact ⟨cfg', h1, h2, h3⟩
        · rcases em2 with _ | ⟨b, em3⟩
          · obtain ⟨cfg', h1, h2, h3⟩ := descend_single hInv
            simp only [descendExec]
            rw [show base - ((2 : Nat) : Int) = base - 2 by omega]
            exact ⟨cfg', h1, h2, h3⟩
          · obtain ⟨cfg₂, h1, h2, h3⟩ := descend_pair hInv
            obtain ⟨cfg', h1', h2', h3'⟩ :=
              ih em3 (by simp at hlen; omega) b (false :: (!r) :: rest) base cfg₂ h2
            simp only [descendExec]
            refine ⟨cfg', ?_, h2', ?_⟩
            · rw [show (descendExec em3 b (false :: (!r) :: rest)).1 + 2
                    = 2 + (descendExec em3 b (false :: (!r) :: rest)).1 by omega,
                  stepN_add, h1]
              exact h1'
            · rw [show (descendExec em3 b (false :: (!r) :: rest)).1 + 2
                    = 2 + (descendExec em3 b (false :: (!r) :: rest)).1 by omega]
              exact dsafe_compose h1 h3 h3'

/-- The descent, packaged: every `B`-turn's leftward excursion runs
faithfully. -/
theorem descend_run {em : List Bool} {r : Bool} {rest : List Bool} {base : Int}
    {cfg : Config} (hInv : Inv State.B base em (r :: rest) cfg) :
    ∃ cfg', stepN (descendExec em r rest).1 cfg = some cfg' ∧
      Inv State.D (base - (((descendExec em r rest).2.1 : Nat) : Int))
        (descendExec em r rest).2.2.1 (descendExec em r rest).2.2.2 cfg' ∧
      DSafeSeg cfg (descendExec em r rest).1 :=
  descendExec_faithful em.length em (Nat.le_refl _) r rest base cfg hInv

theorem descendExec_steps_pos :
    ∀ (em : List Bool) (r : Bool) (rest : List Bool),
      0 < (descendExec em r rest).1 := by
  intro em r rest
  rcases em with _ | ⟨c, em2⟩
  · simp [descendExec]
  · cases c
    · simp [descendExec]
    · rcases em2 with _ | ⟨b, em3⟩
      · simp [descendExec]
      · simp only [descendExec]
        omega


/-!
## The classical unit rules (phase 3, word grain)

The interior transducer rules of the validated trisection calculus,
with their exact frozen costs, as compositions of the micro-episodes.
`bcopy_step` is simultaneously the B-copy *and* the B-cursor unit —
instrumentation shows the two share one 12-step cell-level
choreography (they differ only in word-level bookkeeping).  The
`em`-stack prefix `[1,0,1,1,0]` is the interior flux invariant
(`'.##.#'` read outward), re-established by every unit.
-/

/-- B-copy / B-cursor: the 12-step interior dance
(descent 6 + `dfa` 3 + terminator 3), advancing the maximum-turn two
cells and re-establishing the flux. -/
theorem bcopy_step {base : Int} {em5 rest : List Bool} {cfg : Config}
    (hInv : Inv State.B base
      (true :: false :: true :: true :: false :: em5)
      (true :: false :: rest) cfg) :
    ∃ cfg', stepN 12 cfg = some cfg' ∧
      Inv State.B base
        (true :: false :: true :: true :: false :: true :: false :: em5)
        rest cfg' ∧
      DSafeSeg cfg 12 := by
  obtain ⟨cfgd, hd1, hd2, hd3⟩ := descend_run hInv
  simp only [descendExec, Bool.not_true, Bool.not_false] at hd1 hd2 hd3
  rw [show base - ((0 : Nat) : Int) = base by omega] at hd2
  obtain ⟨cfga, ha1, ha2, ha3⟩ := chunkA_step hd2 rfl rfl rfl
  simp only [List.drop_succ_cons, List.drop_zero] at ha2
  obtain ⟨cfgb, hb1, hb2, hb3⟩ := aterm_step ha2 rfl rfl rfl
  simp only [List.drop_succ_cons, List.drop_zero] at hb2
  rw [show (2 : Nat) + 2 + 2 = 6 by omega] at hd1 hd3
  refine ⟨cfgb, ?_, hb2, ?_⟩
  · rw [show (12 : Nat) = 6 + (3 + 3) by omega, stepN_add, hd1,
        show Option.bind (some cfgd) (stepN (3 + 3)) = stepN (3 + 3) cfgd from rfl,
        stepN_add, ha1]
    exact hb1
  · rw [show (12 : Nat) = 6 + (3 + 3) by omega]
    exact dsafe_compose hd1 hd3 (dsafe_compose ha1 ha3 hb3)

/-- B-absorb: the 8-step interior unit (dip 2 + `dfa` 3 +
terminator 3).  The word-level rule `'#.###.' → '#.'`. -/
theorem babsorb_step {base : Int} {em rest : List Bool} {cfg : Config}
    (hguard : em.getD 0 false = false)
    (hInv : Inv State.D base em
      (true :: false :: true :: false :: false :: false :: rest) cfg) :
    ∃ cfg', stepN 8 cfg = some cfg' ∧
      Inv State.B base
        (true :: false :: true :: true :: false :: true :: em) rest cfg' ∧
      DSafeSeg cfg 8 := by
  obtain ⟨cfgp, hp1, hp2, hp3⟩ := dip_step hInv rfl hguard
  simp only [List.drop_succ_cons, List.drop_zero] at hp2
  obtain ⟨cfga, ha1, ha2, ha3⟩ := chunkA_step hp2 rfl rfl rfl
  simp only [List.drop_succ_cons, List.drop_zero] at ha2
  obtain ⟨cfgb, hb1, hb2, hb3⟩ := aterm_step ha2 rfl rfl rfl
  simp only [List.drop_succ_cons, List.drop_zero] at hb2
  refine ⟨cfgb, ?_, hb2, ?_⟩
  · rw [show (8 : Nat) = 2 + (3 + 3) by omega, stepN_add, hp1,
        show Option.bind (some cfgp) (stepN (3 + 3)) = stepN (3 + 3) cfgp from rfl,
        stepN_add, ha1]
    exact hb1
  · rw [show (8 : Nat) = 2 + (3 + 3) by omega]
    exact dsafe_compose hp1 hp3 (dsafe_compose ha1 ha3 hb3)

/-- D-insert: the 12-step interior unit (descent 6 + `dfa` 3 +
`dfc` 3).  The word-level rule `'#.' → '#.###.'`. -/
theorem dinsert_step {base : Int} {em5 rest : List Bool} {cfg : Config}
    (hInv : Inv State.B base
      (true :: false :: true :: true :: false :: em5)
      (false :: false :: rest) cfg) :
    ∃ cfg', stepN 12 cfg = some cfg' ∧
      Inv State.D base
        (false :: true :: true :: true :: false :: true :: false :: em5)
        rest cfg' ∧
      DSafeSeg cfg 12 := by
  obtain ⟨cfgd, hd1, hd2, hd3⟩ := descend_run hInv
  simp only [descendExec, Bool.not_true, Bool.not_false] at hd1 hd2 hd3
  rw [show base - ((0 : Nat) : Int) = base by omega] at hd2
  obtain ⟨cfga, ha1, ha2, ha3⟩ := chunkA_step hd2 rfl rfl rfl
  simp only [List.drop_succ_cons, List.drop_zero] at ha2
  obtain ⟨cfgc, hc1, hc2, hc3⟩ := chunkC_step ha2 rfl rfl rfl
  simp only [List.drop_succ_cons, List.drop_zero] at hc2
  rw [show (2 : Nat) + 2 + 2 = 6 by omega] at hd1 hd3
  refine ⟨cfgc, ?_, hc2, ?_⟩
  · rw [show (12 : Nat) = 6 + (3 + 3) by omega, stepN_add, hd1,
        show Option.bind (some cfgd) (stepN (3 + 3)) = stepN (3 + 3) cfgd from rfl,
        stepN_add, ha1]
    exact hc1
  · rw [show (12 : Nat) = 6 + (3 + 3) by omega]
    exact dsafe_compose hd1 hd3 (dsafe_compose ha1 ha3 hc3)

/-- The regroup wave input pattern: `k` repetitions of the six cells
`'.#...#'` (a `dfc`+`dfa` pair). -/
def waves : Nat → List Bool
  | 0 => []
  | k + 1 => false :: true :: false :: false :: false :: true :: waves k

/-- The regroup wave output (as `em`-stack cells, nearest first):
`k` repetitions of the push `[1,0,1,0,1,1]`. -/
def wavesOut : Nat → List Bool
  | 0 => []
  | k + 1 => true :: false :: true :: false :: true :: true :: wavesOut k

theorem wavesOut_shift : ∀ (k : Nat) (em : List Bool),
    wavesOut k ++ (true :: false :: true :: false :: true :: true :: em)
      = true :: false :: true :: false :: true :: true :: (wavesOut k ++ em) := by
  intro k
  induction k with
  | zero => intro em; rfl
  | succ k ih => intro em; simp only [wavesOut, List.cons_append, ih]

/-- The parametric wave train: `k` `dfc`+`dfa` pairs and the closing
`dfc`, in `6k + 3` steps. -/
theorem rise_waves : ∀ (k : Nat) {base : Int} {em rest : List Bool} {cfg : Config},
    Inv State.D base em (waves k ++ (false :: true :: false :: rest)) cfg →
    ∃ cfg', stepN (6 * k + 3) cfg = some cfg' ∧
      Inv State.D base (false :: true :: true :: wavesOut k ++ em) rest cfg' ∧
      DSafeSeg cfg (6 * k + 3) := by
  intro k
  induction k with
  | zero =>
      intro base em rest cfg hInv
      rw [show waves 0 ++ (false :: true :: false :: rest)
            = false :: true :: false :: rest from rfl] at hInv
      obtain ⟨cfg', h1, h2, h3⟩ := chunkC_step hInv rfl rfl rfl
      simp only [List.drop_succ_cons, List.drop_zero] at h2
      exact ⟨cfg', h1, h2, h3⟩
  | succ k ih =>
      intro base em rest cfg hInv
      rw [show waves (k + 1) ++ (false :: true :: false :: rest)
            = false :: true :: false :: false :: false :: true ::
              (waves k ++ (false :: true :: false :: rest)) from by
            simp only [waves, List.cons_append]] at hInv
      obtain ⟨cfgc, hc1, hc2, hc3⟩ := chunkC_step hInv rfl rfl rfl
      simp only [List.drop_succ_cons, List.drop_zero] at hc2
      obtain ⟨cfga, ha1, ha2, ha3⟩ := chunkA_step hc2 rfl rfl rfl
      simp only [List.drop_succ_cons, List.drop_zero] at ha2
      obtain ⟨cfg', h1, h2, h3⟩ := ih ha2
      simp only [List.cons_append] at h2
      rw [wavesOut_shift] at h2
      refine ⟨cfg', ?_, ?_, ?_⟩
      · rw [show 6 * (k + 1) + 3 = 3 + (3 + (6 * k + 3)) by omega, stepN_add, hc1,
            show Option.bind (some cfgc) (stepN (3 + (6 * k + 3)))
              = stepN (3 + (6 * k + 3)) cfgc from rfl,
            stepN_add, ha1]
        exact h1
      · simp only [wavesOut, List.cons_append]
        exact h2
      · rw [show 6 * (k + 1) + 3 = 3 + (3 + (6 * k + 3)) by omega]
        exact dsafe_compose hc1 hc3 (dsafe_compose ha1 ha3 h3)

/-- D-regroup, the parametric family: the word-level rule
`'#.#.(###.#.)^k#.' → '(#.###.)^{k+1}'` at its exact frozen cost
`8 + 6k` (dip 2 + `dfa` 3 + wave train `6k+3`). -/
theorem dregroup_step (k : Nat) {base : Int} {em rest : List Bool} {cfg : Config}
    (hguard : em.getD 0 false = false)
    (hInv : Inv State.D base em
      (true :: false :: true :: (waves k ++ (false :: true :: false :: rest))) cfg) :
    ∃ cfg', stepN (8 + 6 * k) cfg = some cfg' ∧
      Inv State.D base
        (false :: true :: true :: wavesOut k ++ (true :: false :: true :: em))
        rest cfg' ∧
      DSafeSeg cfg (8 + 6 * k) := by
  obtain ⟨cfgp, hp1, hp2, hp3⟩ := dip_step hInv rfl hguard
  simp only [List.drop_succ_cons, List.drop_zero] at hp2
  obtain ⟨cfga, ha1, ha2, ha3⟩ := chunkA_step hp2 rfl rfl rfl
  simp only [List.drop_succ_cons, List.drop_zero] at ha2
  obtain ⟨cfg', h1, h2, h3⟩ := rise_waves k ha2
  refine ⟨cfg', ?_, h2, ?_⟩
  · rw [show 8 + 6 * k = 2 + (3 + (6 * k + 3)) by omega, stepN_add, hp1,
        show Option.bind (some cfgp) (stepN (3 + (6 * k + 3)))
          = stepN (3 + (6 * k + 3)) cfgp from rfl,
        stepN_add, ha1]
    exact h1
  · rw [show 8 + 6 * k = 2 + (3 + (6 * k + 3)) by omega]
    exact dsafe_compose hp1 hp3 (dsafe_compose ha1 ha3 h3)


/-!
## The certified sweep (phases 4–5): `passGo` and `wstep`

`wstep` is the certified-side mirror of the validated calculus's
`Calculus2.step`, one level down: instead of the learned unit/tail
tables it runs the underlying cell-level pass those tables were
extracted from — dips, rise chunks, terminators, `C1` turns, and
descents — as a fail-closed, fuel-driven executable function on the
word.  Any would-halt (`E` reading `1`), any `C`-state arrival, any
arrival reading `1`, and fuel exhaustion all return `none`.  Interior
units, boundary tails, head rules and mini-arrival floors are all
subsumed; a sweep stops exactly at the first `B` maximum-turn whose
descent is deep (`≥ 8`, the calculus's `MINI_DEPTH`) or
extreme-extending — the next arrival.

`passGo_faithful` / `wstep_faithful`: every `some` output is realized
by the raw machine in *exactly* the returned step count, D-probe-safe
throughout.  Validated against raw segmentation: 1249/1249 segments
exact over 20M raw steps (word, dt, head offset, extreme growth, and
arrival kind), and mirrored in `tests/bb6/test_rank1_theorems.py`.
-/

/-- Descent scan: `some i` = the descent from a `B`-turn over this
stack turns at stack index `2i` (depth `2i+1`); `none` = it runs off
the bottom (extends the left extreme: a full arrival). -/
def dScan : List Bool → Option Nat
  | [] => none
  | false :: _ => some 0
  | true :: [] => none
  | true :: _ :: t => (dScan t).map (· + 1)

/-- A `B`-turn is the *next arrival* iff its descent is deep
(`2i+1 ≥ 8`, i.e. `i ≥ 4` — the calculus's `MINI_DEPTH`) or
extreme-extending. -/
def stopDeep (em : List Bool) : Bool :=
  match dScan em with
  | none => true
  | some i => decide (4 ≤ i)

/-- The fail-closed pass: from state `D` at the boundary of `em`
(below, nearest first) and `rest` (head cell first), run the sweep to
the next arrival.  Returns `(word, head offset, steps)`. -/
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

theorem map_add_eq_some {o : Option (List Bool × Nat × Nat)} {c : Nat}
    {w : List Bool} {p d : Nat}
    (h : o.map (fun r => (r.1, r.2.1, c + r.2.2)) = some (w, p, d)) :
    ∃ d', o = some (w, p, d') ∧ d = c + d' := by
  cases o with
  | none => simp at h
  | some r =>
      obtain ⟨w0, p0, d0⟩ := r
      simp at h
      obtain ⟨hw, hp, hd⟩ := h
      exact ⟨d0, by rw [hw, hp], by omega⟩

theorem getD_head_expand (l : List Bool) :
    ∀ j : Nat, l.getD j false = ((l.getD 0 false) :: l.drop 1).getD j false := by
  intro j
  cases j with
  | zero => rfl
  | succ j =>
      rw [List.getD_cons_succ, getD_drop, Nat.add_comm 1 j]

/-- Faithfulness of the pass, by induction on fuel: every `some`
output of `passGo` is realized by the raw machine in exactly the
returned step count, probe-safely, landing on an arrival
configuration of the returned word. -/
theorem passGo_faithful :
    ∀ (fuel : Nat) (em rest w : List Bool) (poff d : Nat),
      passGo fuel em rest = some (w, poff, d) →
      ∀ (base : Int) (cfg : Config), Inv State.D base em rest cfg →
        ∃ (cfg' : Config) (base' : Int), stepN d cfg = some cfg' ∧
          ArrivalInv base' w poff cfg' ∧ DSafeSeg cfg d := by
  intro fuel
  induction fuel with
  | zero =>
      intro em rest w poff d hpg base cfg hInv
      simp [passGo] at hpg
  | succ fuel ih =>
      intro em rest w poff d hpg base cfg hInv
      simp only [passGo] at hpg
      split at hpg
      · -- dip with a fatal probe: fail-closed
        simp at hpg
      · -- dip
        next x1 x2 hc0 hg =>
          obtain ⟨d', hrec, hd⟩ := map_add_eq_some hpg
          subst hd
          obtain ⟨cfg₂, h1, h2, h3⟩ := dip_step hInv hc0 hg
          obtain ⟨cfg', base', h1', h2', h3'⟩ := ih _ _ _ _ _ hrec _ cfg₂ h2
          refine ⟨cfg', base', ?_, h2', ?_⟩
          · rw [stepN_add, h1]
            exact h1'
          · exact dsafe_compose h1 h3 h3'
      · -- dfa chunk
        next x1 hc0 hc1 hc2 =>
          obtain ⟨d', hrec, hd⟩ := map_add_eq_some hpg
          subst hd
          obtain ⟨cfg₂, h1, h2, h3⟩ := chunkA_step hInv hc0 hc1 hc2
          obtain ⟨cfg', base', h1', h2', h3'⟩ := ih _ _ _ _ _ hrec _ cfg₂ h2
          refine ⟨cfg', base', ?_, h2', ?_⟩
          · rw [stepN_add, h1]
            exact h1'
          · exact dsafe_compose h1 h3 h3'
      · -- dfc chunk
        next x1 hc0 hc1 hc2 =>
          obtain ⟨d', hrec, hd⟩ := map_add_eq_some hpg
          subst hd
          obtain ⟨cfg₂, h1, h2, h3⟩ := chunkC_step hInv hc0 hc1 hc2
          obtain ⟨cfg', base', h1', h2', h3'⟩ := ih _ _ _ _ _ hrec _ cfg₂ h2
          refine ⟨cfg', base', ?_, h2', ?_⟩
          · rw [stepN_add, h1]
            exact h1'
          · exact dsafe_compose h1 h3 h3'
      · -- arrival terminator
        next x1 hc0 hc1 hc2 =>
          obtain ⟨cfgb, hb1, hb2, hb3⟩ := aterm_step hInv hc0 hc1 hc2
          split at hpg
          · -- deep or extreme-extending: the next arrival — stop
            split at hpg
            · simp at hpg
            · obtain ⟨hw, hp, hd⟩ : (true :: false :: true :: em).reverse ++ rest.drop 3 = w
                  ∧ em.length + 3 = poff ∧ 3 = d := by
                simpa using hpg
              subst hw
              subst hp
              subst hd
              exact ⟨cfgb, base, hb1, inv_to_arrival hb2, hb3⟩
          · -- shallow: execute the descent and continue
            obtain ⟨d', hrec, hd⟩ := map_add_eq_some hpg
            subst hd
            have hb2' := inv_congr_rest (getD_head_expand (rest.drop 3)) hb2
            obtain ⟨cfgd, hd1, hd2, hd3⟩ := descend_run hb2'
            obtain ⟨cfg', base', h1', h2', h3'⟩ := ih _ _ _ _ _ hrec _ cfgd hd2
            refine ⟨cfg', base', ?_, h2', ?_⟩
            · rw [show 3 + (descendExec (true :: false :: true :: em)
                    ((rest.drop 3).getD 0 false) ((rest.drop 3).drop 1)).1 + d'
                  = 3 + ((descendExec (true :: false :: true :: em)
                    ((rest.drop 3).getD 0 false) ((rest.drop 3).drop 1)).1 + d') by omega,
                  stepN_add, hb1,
                  show Option.bind (some cfgb) (stepN ((descendExec (true :: false :: true :: em)
                    ((rest.drop 3).getD 0 false) ((rest.drop 3).drop 1)).1 + d'))
                    = stepN ((descendExec (true :: false :: true :: em)
                    ((rest.drop 3).getD 0 false) ((rest.drop 3).drop 1)).1 + d') cfgb from rfl,
                  stepN_add, hd1]
              exact h1'
            · rw [show 3 + (descendExec (true :: false :: true :: em)
                    ((rest.drop 3).getD 0 false) ((rest.drop 3).drop 1)).1 + d'
                  = 3 + ((descendExec (true :: false :: true :: em)
                    ((rest.drop 3).getD 0 false) ((rest.drop 3).drop 1)).1 + d') by omega]
              exact dsafe_compose hb1 hb3 (dsafe_compose hd1 hd3 h3')
      · -- C1 turn
        next x1 hc0 hc1 hc2 =>
          split at hpg
          · simp at hpg
          · obtain ⟨d', hrec, hd⟩ := map_add_eq_some hpg
            subst hd
            obtain ⟨cfgb, hb1, hb2, hb3⟩ := c1turn_step hInv hc0 hc1 hc2
            obtain ⟨cfgd, hd1, hd2, hd3⟩ := descend_run hb2
            obtain ⟨cfg', base', h1', h2', h3'⟩ := ih _ _ _ _ _ hrec _ cfgd hd2
            refine ⟨cfg', base', ?_, h2', ?_⟩
            · rw [show 3 + (descendExec (true :: em) true (false :: rest.drop 3)).1 + d'
                  = 3 + ((descendExec (true :: em) true (false :: rest.drop 3)).1 + d') by omega,
                  stepN_add, hb1,
                  show Option.bind (some cfgb)
                    (stepN ((descendExec (true :: em) true (false :: rest.drop 3)).1 + d'))
                    = stepN ((descendExec (true :: em) true (false :: rest.drop 3)).1 + d')
                      cfgb from rfl,
                  stepN_add, hd1]
              exact h1'
            · rw [show 3 + (descendExec (true :: em) true (false :: rest.drop 3)).1 + d'
                  = 3 + ((descendExec (true :: em) true (false :: rest.drop 3)).1 + d') by omega]
              exact dsafe_compose hb1 hb3 (dsafe_compose hd1 hd3 h3')

/-- Generous fuel: recursion depth is bounded by the raw step count of
one sweep, comfortably quadratic in the word length.  Fail-closed —
exhaustion is an orbit death, and the empirical margin is enormous. -/
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

/-- **The sweep is faithful**: whenever `wstep` yields a successor
word, the raw machine, started on any realization of the input
arrival, runs *exactly* the returned number of steps, stays
D-probe-safe throughout, and lands on a realization of the successor
arrival.  No `Faithful` assumption remains anywhere in this file. -/
theorem wstep_faithful {w : List Bool} {poff : Nat} {w' : List Bool}
    {poff' d : Nat} (hw : wstep w poff = some (w', poff', d)) :
    ∀ (base : Int) (cfg : Config), ArrivalInv base w poff cfg →
      ∃ (cfg' : Config) (base' : Int), stepN d cfg = some cfg' ∧
        ArrivalInv base' w' poff' cfg' ∧ DSafeSeg cfg d ∧ 0 < d := by
  intro base cfg harr
  simp only [wstep] at hw
  split at hw
  · next hguard =>
      obtain ⟨hle, hread⟩ := hguard
      obtain ⟨d', hrec, hd⟩ := map_add_eq_some hw
      subst hd
      have hInvB := arrival_to_inv harr hle hread
      obtain ⟨cfgd, hd1, hd2, hd3⟩ := descend_run hInvB
      obtain ⟨cfg', base', h1', h2', h3'⟩ := passGo_faithful _ _ _ _ _ _ hrec _ cfgd hd2
      refine ⟨cfg', base', ?_, h2', ?_, ?_⟩
      · rw [stepN_add, hd1]
        exact h1'
      · exact dsafe_compose hd1 hd3 h3'
      · have := descendExec_steps_pos ((w.take poff).reverse) false (w.drop (poff + 1))
        omega
  · simp at hw

end QIG.Rank1RawTM
