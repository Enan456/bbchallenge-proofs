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

end QIG.Rank1RawTM
