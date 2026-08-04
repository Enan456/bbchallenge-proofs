import Lean.Elab.Tactic.Omega

/-!
# Dossier-1 raw Turing-machine semantics and halt localization

Bare-Lean model of the concrete BB(6) machine

`1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB`.

Checked statements (no sorry, no extra axioms):

* `step_eq_none_iff` — the machine halts in one step exactly at the unique
  undefined transition `F0`.
* `into_F_only_from_C0` — state `F` is entered only via `C` reading `0`.
* `halt_requires_c_probe_00` — any raw halt from a non-`F` start passes
  through a reachable configuration in state `C` reading `0` whose right
  neighbour is also `0`.
* `nonhalting_of_c_probe_safe` / `blank_nonhalting_of_c_probe_safe` — the
  C-probe-safety invariant ("every 0 that state C reads has a 1 to its
  right") implies the machine never halts.

`CProbeSafe blankStart` is exactly the invariant discharged empirically by
stages 748–750 (window census, rule alignment, uniformity + fresh-value
replay).  Proving it from the 33 macro obligations is the remaining
raw-to-macro contract, in the style of `DvisetuRawTM`'s layered endgame.
-/

namespace QIG.Dossier1RawTM

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

/-- The dossier-1 transition table.  `none` is the undefined halt transition. -/
def instr : State → Bool → Option Instr
  | State.A, false => some ⟨State.B, true, Dir.R⟩
  | State.A, true => some ⟨State.E, false, Dir.L⟩
  | State.B, false => some ⟨State.B, true, Dir.L⟩
  | State.B, true => some ⟨State.C, true, Dir.R⟩
  | State.C, false => some ⟨State.F, false, Dir.R⟩
  | State.C, true => some ⟨State.D, false, Dir.R⟩
  | State.D, false => some ⟨State.E, true, Dir.R⟩
  | State.D, true => some ⟨State.A, false, Dir.L⟩
  | State.E, false => some ⟨State.A, true, Dir.L⟩
  | State.E, true => some ⟨State.E, true, Dir.R⟩
  | State.F, false => none
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

/-- One raw TM step.  `none` means the undefined `F0` halt was reached. -/
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

/-- State `F` is entered only by `C` reading `0` (the transition `C0 = 0RF`):
the predecessor is in state `C` on a `0`, and the successor sits one cell to
the right on the tape with that `0` (re)written. -/
theorem into_F_only_from_C0 {c c' : Config} (h : step c = some c')
    (hF : c'.state = State.F) :
    c.state = State.C ∧ c.tape c.head = false ∧
      c'.head = c.head + 1 ∧ c'.tape = writeAt c.tape c.head false := by
  cases hs : c.state <;> cases ht : c.tape c.head <;>
    simp [step, instr, hs, ht] at h
  all_goals
    first
      | exact ⟨rfl, rfl, by rw [← h]; simp [move], by rw [← h]⟩
      | (rw [← h] at hF; simp at hF)

/-- Any finite run ending in a halt contains a strictly earlier configuration
whose single step halts. -/
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

/-- A successful `k+1`-step run has an immediate predecessor of its endpoint. -/
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

/-- Halt localization: from any non-`F` start, a raw halt forces a reachable
configuration where `C` reads a `0` whose right neighbour is also `0`. -/
theorem halt_requires_c_probe_00 {c : Config} (hne : c.state ≠ State.F)
    (hh : RawHalts c) :
    ∃ d : Config, Reaches c d ∧ d.state = State.C ∧
      d.tape d.head = false ∧ d.tape (d.head + 1) = false := by
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
      rwa [writeAt_other e.tape e.head (e.head + 1) false (by omega)] at hread

/-- The C-probe-safety invariant: every `0` that state `C` reads in any
reachable configuration has a `1` immediately to its right.  This is exactly
the invariant discharged empirically by stages 748–750. -/
def CProbeSafe (c : Config) : Prop :=
  ∀ d : Config, Reaches c d → d.state = State.C → d.tape d.head = false →
    d.tape (d.head + 1) = true

/-- C-probe safety implies the machine never halts. -/
theorem nonhalting_of_c_probe_safe {c : Config} (hne : c.state ≠ State.F)
    (hsafe : CProbeSafe c) : ¬ RawHalts c := by
  intro hh
  obtain ⟨d, hreach, hC, h0, h00⟩ := halt_requires_c_probe_00 hne hh
  have h1 := hsafe d hreach hC h0
  rw [h1] at h00
  exact Bool.noConfusion h00

/-- Specialization to the blank start: the remaining raw-to-macro contract is
exactly `CProbeSafe blankStart`. -/
theorem blank_nonhalting_of_c_probe_safe
    (hsafe : CProbeSafe blankStart) : ¬ RawHalts blankStart := by
  have hne : blankStart.state ≠ State.F := by
    simp [blankStart]
  exact nonhalting_of_c_probe_safe hne hsafe

/-!
## The caterpillar lemma — the unbounded core of the dominant macro rule

Empirically (stage747/749), 97.8% of dossier-1's record transitions are the
frozen-prefix sweep `(…, a, b, c) ↦ (…, a+2, b−2, c+1)`, and its raw
micro-trajectory is a five-step cycle crawling right across the middle
block:

`A@h → B@(h+1) → B@h → C@(h+1) → D@(h+2) → A@(h+1)`

with cycle preconditions `tape h = 0`, `tape (h+1) = 0`, `tape (h+2) = 1`
and net writes `h ↦ 1, (h+1) ↦ 0, (h+2) ↦ 0`.  Inside the cycle, state `C`
reads only the `1` that `B` just wrote — the unbounded part of the dominant
rule contains **no C-probe of a 0 at all**.  The only C0 probes live in the
rule's bounded boundary steps.  `cat_run` proves both facts symbolically
for every block length `n`.
-/

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

/-- Sequential-composition law for `stepN`. -/
theorem stepN_add :
    ∀ (m n : Nat) (c : Config),
      stepN (m + n) c = (stepN m c).bind (stepN n) := by
  intro m
  induction m with
  | zero =>
      intro n c
      simp [stepN, Nat.zero_add]
  | succ m ih =>
      intro n c
      rw [Nat.succ_add]
      cases hstep : step c with
      | none => simp [stepN, hstep]
      | some c1 => simp [stepN, hstep, ih]

/-- One caterpillar cycle: five raw steps, explicit output tape, and the
only intermediate `C` configuration reads `1`. -/
theorem cat_cycle {c : Config} {h : Int}
    (hs : c.state = State.A) (hh : c.head = h)
    (h0 : c.tape h = false) (h1 : c.tape (h + 1) = false)
    (h2 : c.tape (h + 2) = true) :
    stepN 5 c = some ⟨State.A, h + 1,
        writeAt (writeAt (writeAt c.tape h true) (h + 1) false) (h + 2) false⟩ ∧
      (∀ k d, k < 5 → stepN k c = some d → d.state = State.C →
        d.tape d.head = true) := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hs hh h0 h1 h2
  subst hs hd
  -- the five configurations
  have r1 : writeAt t h true (h + 1) = false := by
    rw [writeAt_other t h (h + 1) true (by omega)]; exact h1
  have r2 : writeAt (writeAt t h true) (h + 1) true h = true := by
    rw [writeAt_other (writeAt t h true) (h + 1) h true (by omega)]
    exact writeAt_same t h true
  have r3 : writeAt (writeAt t h true) (h + 1) true (h + 1) = true :=
    writeAt_same (writeAt t h true) (h + 1) true
  have r4 : writeAt (writeAt t h true) (h + 1) false (h + 2) = true := by
    rw [writeAt_other _ (h + 1) (h + 2) false (by omega)]
    rw [writeAt_other t h (h + 2) true (by omega)]
    exact h2
  have s1 : step ⟨State.A, h, t⟩ = some ⟨State.B, h + 1, writeAt t h true⟩ := by
    simp [step, instr, h0, move]
  have s2 : step ⟨State.B, h + 1, writeAt t h true⟩ =
      some ⟨State.B, h, writeAt (writeAt t h true) (h + 1) true⟩ := by
    simp [step, instr, r1, move]
  have s3 : step ⟨State.B, h, writeAt (writeAt t h true) (h + 1) true⟩ =
      some ⟨State.C, h + 1, writeAt (writeAt t h true) (h + 1) true⟩ := by
    have hself := writeAt_self (writeAt (writeAt t h true) (h + 1) true) h r2
    simp [step, instr, r2, move, hself]
  have s4 : step ⟨State.C, h + 1, writeAt (writeAt t h true) (h + 1) true⟩ =
      some ⟨State.D, h + 2, writeAt (writeAt t h true) (h + 1) false⟩ := by
    have hover := writeAt_overwrite (writeAt t h true) (h + 1) true false
    simp [step, instr, r3, move, hover]
    try omega
  have s5 : step ⟨State.D, h + 2, writeAt (writeAt t h true) (h + 1) false⟩ =
      some ⟨State.A, h + 1,
        writeAt (writeAt (writeAt t h true) (h + 1) false) (h + 2) false⟩ := by
    simp [step, instr, r4, move]
    try omega
  have p1 : stepN 1 ⟨State.A, h, t⟩ =
      some ⟨State.B, h + 1, writeAt t h true⟩ := by
    simp [stepN, s1]
  have p2 : stepN 2 ⟨State.A, h, t⟩ =
      some ⟨State.B, h, writeAt (writeAt t h true) (h + 1) true⟩ := by
    simp [stepN, s1, s2]
  have p3 : stepN 3 ⟨State.A, h, t⟩ =
      some ⟨State.C, h + 1, writeAt (writeAt t h true) (h + 1) true⟩ := by
    simp [stepN, s1, s2, s3]
  have p4 : stepN 4 ⟨State.A, h, t⟩ =
      some ⟨State.D, h + 2, writeAt (writeAt t h true) (h + 1) false⟩ := by
    simp [stepN, s1, s2, s3, s4]
  refine ⟨?_, ?_⟩
  · show stepN 5 ⟨State.A, h, t⟩ = _
    simp [stepN, s1, s2, s3, s4, s5]
  · intro k d hk hkd hC
    have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl
    · have hd : (⟨State.A, h, t⟩ : Config) = d := by
        simpa [stepN] using hkd
      rw [← hd] at hC
      simp at hC
    · rw [p1] at hkd
      rw [← Option.some_inj.mp hkd] at hC
      simp at hC
    · rw [p2] at hkd
      rw [← Option.some_inj.mp hkd] at hC
      simp at hC
    · rw [p3] at hkd
      rw [← Option.some_inj.mp hkd]
      exact r3
    · rw [p4] at hkd
      rw [← Option.some_inj.mp hkd] at hC
      simp at hC

/-- The tape after `n` caterpillar cycles starting at `h`. -/
def catTape (t : Int → Bool) (h : Int) : Nat → (Int → Bool)
  | 0 => t
  | n + 1 =>
      catTape (writeAt (writeAt (writeAt t h true) (h + 1) false) (h + 2) false)
        (h + 1) n

/-- The caterpillar runs `5n` steps across a middle block of `n` ones,
ends in `A` at `h + n`, and **no intermediate configuration has `C`
reading a `0`** — the unbounded core of the dominant rule is C0-free. -/
theorem cat_run :
    ∀ (n : Nat) (c : Config) (h : Int), c.state = State.A → c.head = h →
      c.tape h = false → c.tape (h + 1) = false →
      (∀ i : Nat, i < n → c.tape (h + 2 + i) = true) →
      stepN (5 * n) c = some ⟨State.A, h + n, catTape c.tape h n⟩ ∧
        (∀ k d, k < 5 * n → stepN k c = some d → d.state = State.C →
          d.tape d.head = true) := by
  intro n
  induction n with
  | zero =>
      intro c h hs hh h0 h1 _
      obtain ⟨s, hd, t⟩ := c
      simp only at hs hh
      subst hs hd
      refine ⟨?_, ?_⟩
      · simp [stepN, catTape]
      · intro k d hk
        exact absurd hk (by omega)
  | succ n ih =>
      intro c h hs hh h0 h1 hones
      have h2 : c.tape (h + 2) = true := by
        have := hones 0 (Nat.succ_pos n)
        simpa using this
      obtain ⟨s5, safe5⟩ := cat_cycle hs hh h0 h1 h2
      have h0' : writeAt (writeAt (writeAt c.tape h true) (h + 1) false)
          (h + 2) false (h + 1) = false := by
        rw [writeAt_other _ (h + 2) (h + 1) false (by omega)]
        exact writeAt_same (writeAt c.tape h true) (h + 1) false
      have h1' : writeAt (writeAt (writeAt c.tape h true) (h + 1) false)
          (h + 2) false (h + 1 + 1) = false := by
        rw [show h + 1 + 1 = h + 2 by omega]
        exact writeAt_same _ (h + 2) false
      have hones' : ∀ i : Nat, i < n →
          writeAt (writeAt (writeAt c.tape h true) (h + 1) false)
            (h + 2) false (h + 1 + 2 + i) = true := by
        intro i hi
        rw [writeAt_other _ (h + 2) _ false (by omega),
            writeAt_other _ (h + 1) _ false (by omega),
            writeAt_other _ h _ true (by omega)]
        have := hones (i + 1) (by omega)
        rw [show h + 1 + 2 + (i : Int) = h + 2 + ((i + 1 : Nat) : Int) by omega]
        exact this
      obtain ⟨srun, saferun⟩ :=
        ih ⟨State.A, h + 1,
            writeAt (writeAt (writeAt c.tape h true) (h + 1) false) (h + 2) false⟩
          (h + 1) rfl rfl h0' h1' hones'
      have hsplit : 5 * (n + 1) = 5 + 5 * n := by omega
      refine ⟨?_, ?_⟩
      · rw [hsplit, stepN_add, s5]
        rw [show ((some (⟨State.A, h + 1,
              writeAt (writeAt (writeAt c.tape h true) (h + 1) false)
                (h + 2) false⟩ : Config) : Option Config).bind (stepN (5 * n)))
              = stepN (5 * n) ⟨State.A, h + 1,
                  writeAt (writeAt (writeAt c.tape h true) (h + 1) false)
                    (h + 2) false⟩ from rfl]
        rw [srun]
        rw [show h + 1 + (n : Int) = h + ((n + 1 : Nat) : Int) by omega]
        rfl
      · intro k d hk hkd hC
        by_cases hk5 : k < 5
        · exact safe5 k d hk5 hkd hC
        · have hkeq : k = 5 + (k - 5) := by omega
          rw [hkeq, stepN_add, s5] at hkd
          exact saferun (k - 5) d (by omega) hkd hC

/-!
## Boundary lemmas and the composed dominant-rule theorem

The dominant rule's raw trajectory on an L-record of shape `(1, b, 1)`
(single-0 gaps) decomposes as

* a 7-step **prefix** `A → B → C → F → B → C → D → A` containing the ONE
  C0 probe of the whole rule — safe because the probed gap's right
  neighbour is the first `1` of the middle block;
* the C0-free **caterpillar** across the middle block (`cat_run`);
* a 6-step **suffix** `A → B → B → C → D → E` crossing the right block to
  the new frontier, with no C0 probe.

`dominant_rule_run` composes all three: exact step count `13 + 5m` for
middle block `b = m + 4`, final state `E` at the new right frontier, and
`CSafeSeg` — every C-probe of a `0` during the entire rule has a `1` to
its right, for **all** block lengths.
-/

/-- Conditional C-probe safety over the first `N` steps of a run: every
intermediate configuration in state `C` reading a `0` has a `1` to its
right.  This is the per-segment form of `CProbeSafe`. -/
def CSafeSeg (c : Config) (N : Nat) : Prop :=
  ∀ k d, k < N → stepN k c = some d → d.state = State.C →
    d.tape d.head = false → d.tape (d.head + 1) = true

theorem csafe_compose {c c' : Config} {m n : Nat}
    (hm : stepN m c = some c') (h1 : CSafeSeg c m) (h2 : CSafeSeg c' n) :
    CSafeSeg c (m + n) := by
  intro k d hk hkd hC hread
  by_cases hkm : k < m
  · exact h1 k d hkm hkd hC hread
  · have hkeq : k = m + (k - m) := by omega
    rw [hkeq, stepN_add, hm] at hkd
    exact h2 (k - m) d (by omega) hkd hC hread

theorem csafe_of_strong {c : Config} {N : Nat}
    (h : ∀ k d, k < N → stepN k c = some d → d.state = State.C →
      d.tape d.head = true) : CSafeSeg c N := by
  intro k d hk hkd hC hread
  rw [h k d hk hkd hC] at hread
  exact absurd hread (by simp)

/-- The 7-step prefix of the dominant rule.  Contains the rule's single C0
probe (at `p + 2`, the single-0 gap), safe because `p + 3` holds a `1`. -/
theorem prefix_run {c : Config} {p : Int}
    (hs : c.state = State.A) (hh : c.head = p)
    (t0 : c.tape p = false) (t1 : c.tape (p + 1) = true)
    (t2 : c.tape (p + 2) = false) (t3 : c.tape (p + 3) = true)
    (t4 : c.tape (p + 4) = true) (t5 : c.tape (p + 5) = true)
    (t6 : c.tape (p + 6) = true) :
    stepN 7 c = some ⟨State.A, p + 5,
        writeAt (writeAt (writeAt (writeAt c.tape p true) (p + 3) false)
          (p + 5) false) (p + 6) false⟩ ∧
      CSafeSeg c 7 := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hs hh t0 t1 t2 t3 t4 t5 t6
  subst hs hd
  have r1 : writeAt t p true (p + 1) = true := by
    rw [writeAt_other t p (p + 1) true (by omega)]; exact t1
  have r2 : writeAt t p true (p + 2) = false := by
    rw [writeAt_other t p (p + 2) true (by omega)]; exact t2
  have r3 : writeAt t p true (p + 3) = true := by
    rw [writeAt_other t p (p + 3) true (by omega)]; exact t3
  have r4 : writeAt (writeAt t p true) (p + 3) false (p + 4) = true := by
    rw [writeAt_other _ (p + 3) (p + 4) false (by omega),
        writeAt_other t p (p + 4) true (by omega)]
    exact t4
  have r5 : writeAt (writeAt t p true) (p + 3) false (p + 5) = true := by
    rw [writeAt_other _ (p + 3) (p + 5) false (by omega),
        writeAt_other t p (p + 5) true (by omega)]
    exact t5
  have r6 : writeAt (writeAt (writeAt t p true) (p + 3) false) (p + 5) false
      (p + 6) = true := by
    rw [writeAt_other _ (p + 5) (p + 6) false (by omega),
        writeAt_other _ (p + 3) (p + 6) false (by omega),
        writeAt_other t p (p + 6) true (by omega)]
    exact t6
  have s1 : step ⟨State.A, p, t⟩ =
      some ⟨State.B, p + 1, writeAt t p true⟩ := by
    simp [step, instr, t0, move]
  have s2 : step ⟨State.B, p + 1, writeAt t p true⟩ =
      some ⟨State.C, p + 2, writeAt t p true⟩ := by
    have hself := writeAt_self (writeAt t p true) (p + 1) r1
    simp [step, instr, r1, move, hself]
    try omega
  have s3 : step ⟨State.C, p + 2, writeAt t p true⟩ =
      some ⟨State.F, p + 3, writeAt t p true⟩ := by
    have hself := writeAt_self (writeAt t p true) (p + 2) r2
    simp [step, instr, r2, move, hself]
    try omega
  have s4 : step ⟨State.F, p + 3, writeAt t p true⟩ =
      some ⟨State.B, p + 4, writeAt (writeAt t p true) (p + 3) false⟩ := by
    simp [step, instr, r3, move]
    try omega
  have s5 : step ⟨State.B, p + 4, writeAt (writeAt t p true) (p + 3) false⟩ =
      some ⟨State.C, p + 5, writeAt (writeAt t p true) (p + 3) false⟩ := by
    have hself := writeAt_self (writeAt (writeAt t p true) (p + 3) false)
      (p + 4) r4
    simp [step, instr, r4, move, hself]
    try omega
  have s6 : step ⟨State.C, p + 5, writeAt (writeAt t p true) (p + 3) false⟩ =
      some ⟨State.D, p + 6,
        writeAt (writeAt (writeAt t p true) (p + 3) false) (p + 5) false⟩ := by
    simp [step, instr, r5, move]
    try omega
  have s7 : step ⟨State.D, p + 6,
      writeAt (writeAt (writeAt t p true) (p + 3) false) (p + 5) false⟩ =
      some ⟨State.A, p + 5,
        writeAt (writeAt (writeAt (writeAt t p true) (p + 3) false)
          (p + 5) false) (p + 6) false⟩ := by
    simp [step, instr, r6, move]
    try omega
  have p1 : stepN 1 ⟨State.A, p, t⟩ =
      some ⟨State.B, p + 1, writeAt t p true⟩ := by simp [stepN, s1]
  have p2 : stepN 2 ⟨State.A, p, t⟩ =
      some ⟨State.C, p + 2, writeAt t p true⟩ := by simp [stepN, s1, s2]
  have p3 : stepN 3 ⟨State.A, p, t⟩ =
      some ⟨State.F, p + 3, writeAt t p true⟩ := by simp [stepN, s1, s2, s3]
  have p4 : stepN 4 ⟨State.A, p, t⟩ =
      some ⟨State.B, p + 4, writeAt (writeAt t p true) (p + 3) false⟩ := by
    simp [stepN, s1, s2, s3, s4]
  have p5 : stepN 5 ⟨State.A, p, t⟩ =
      some ⟨State.C, p + 5, writeAt (writeAt t p true) (p + 3) false⟩ := by
    simp [stepN, s1, s2, s3, s4, s5]
  have p6 : stepN 6 ⟨State.A, p, t⟩ =
      some ⟨State.D, p + 6,
        writeAt (writeAt (writeAt t p true) (p + 3) false) (p + 5) false⟩ := by
    simp [stepN, s1, s2, s3, s4, s5, s6]
  refine ⟨?_, ?_⟩
  · show stepN 7 ⟨State.A, p, t⟩ = _
    simp [stepN, s1, s2, s3, s4, s5, s6, s7]
  · intro k d hk hkd hC hread
    have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by
      omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hd : (⟨State.A, p, t⟩ : Config) = d := by simpa [stepN] using hkd
      rw [← hd] at hC; simp at hC
    · rw [p1] at hkd; rw [← Option.some_inj.mp hkd] at hC; simp at hC
    · -- THE probe: C at p + 2 reads the gap 0; its right neighbour is the
      -- first 1 of the middle block.
      rw [p2] at hkd
      rw [← Option.some_inj.mp hkd]
      show writeAt t p true (p + 2 + 1) = true
      rw [show p + 2 + 1 = p + 3 by omega]
      exact r3
    · rw [p3] at hkd; rw [← Option.some_inj.mp hkd] at hC; simp at hC
    · rw [p4] at hkd; rw [← Option.some_inj.mp hkd] at hC; simp at hC
    · rw [p5] at hkd
      rw [← Option.some_inj.mp hkd] at hread
      rw [show (⟨State.C, p + 5,
            writeAt (writeAt t p true) (p + 3) false⟩ : Config).tape
            (⟨State.C, p + 5,
              writeAt (writeAt t p true) (p + 3) false⟩ : Config).head
          = writeAt (writeAt t p true) (p + 3) false (p + 5) from rfl] at hread
      rw [r5] at hread
      exact absurd hread (by simp)
    · rw [p6] at hkd; rw [← Option.some_inj.mp hkd] at hC; simp at hC

/-- The 6-step suffix of the dominant rule: the exhausted partial cycle,
the `D` exit across the gap, and `E` crossing the size-1 right block to
the new frontier.  No C0 probe occurs. -/
theorem suffix_run {c : Config} {q : Int}
    (hs : c.state = State.A) (hh : c.head = q)
    (t0 : c.tape q = false) (t1 : c.tape (q + 1) = false)
    (t2 : c.tape (q + 2) = false) (t3 : c.tape (q + 3) = true) :
    stepN 6 c = some ⟨State.E, q + 4,
        writeAt (writeAt (writeAt c.tape q true) (q + 1) false)
          (q + 2) true⟩ ∧
      CSafeSeg c 6 := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hs hh t0 t1 t2 t3
  subst hs hd
  have r1 : writeAt t q true (q + 1) = false := by
    rw [writeAt_other t q (q + 1) true (by omega)]; exact t1
  have r2 : writeAt (writeAt t q true) (q + 1) true q = true := by
    rw [writeAt_other _ (q + 1) q true (by omega)]
    exact writeAt_same t q true
  have r3 : writeAt (writeAt t q true) (q + 1) true (q + 1) = true :=
    writeAt_same (writeAt t q true) (q + 1) true
  have r4 : writeAt (writeAt t q true) (q + 1) false (q + 2) = false := by
    rw [writeAt_other _ (q + 1) (q + 2) false (by omega),
        writeAt_other t q (q + 2) true (by omega)]
    exact t2
  have r5 : writeAt (writeAt (writeAt t q true) (q + 1) false) (q + 2) true
      (q + 3) = true := by
    rw [writeAt_other _ (q + 2) (q + 3) true (by omega),
        writeAt_other _ (q + 1) (q + 3) false (by omega),
        writeAt_other t q (q + 3) true (by omega)]
    exact t3
  have s1 : step ⟨State.A, q, t⟩ =
      some ⟨State.B, q + 1, writeAt t q true⟩ := by
    simp [step, instr, t0, move]
  have s2 : step ⟨State.B, q + 1, writeAt t q true⟩ =
      some ⟨State.B, q, writeAt (writeAt t q true) (q + 1) true⟩ := by
    simp [step, instr, r1, move]
  have s3 : step ⟨State.B, q, writeAt (writeAt t q true) (q + 1) true⟩ =
      some ⟨State.C, q + 1, writeAt (writeAt t q true) (q + 1) true⟩ := by
    have hself := writeAt_self (writeAt (writeAt t q true) (q + 1) true) q r2
    simp [step, instr, r2, move, hself]
  have s4 : step ⟨State.C, q + 1, writeAt (writeAt t q true) (q + 1) true⟩ =
      some ⟨State.D, q + 2, writeAt (writeAt t q true) (q + 1) false⟩ := by
    have hover := writeAt_overwrite (writeAt t q true) (q + 1) true false
    simp [step, instr, r3, move, hover]
    try omega
  have s5 : step ⟨State.D, q + 2, writeAt (writeAt t q true) (q + 1) false⟩ =
      some ⟨State.E, q + 3,
        writeAt (writeAt (writeAt t q true) (q + 1) false) (q + 2) true⟩ := by
    simp [step, instr, r4, move]
    try omega
  have s6 : step ⟨State.E, q + 3,
      writeAt (writeAt (writeAt t q true) (q + 1) false) (q + 2) true⟩ =
      some ⟨State.E, q + 4,
        writeAt (writeAt (writeAt t q true) (q + 1) false) (q + 2) true⟩ := by
    have hself := writeAt_self
      (writeAt (writeAt (writeAt t q true) (q + 1) false) (q + 2) true)
      (q + 3) r5
    simp [step, instr, r5, move, hself]
    try omega
  have p1 : stepN 1 ⟨State.A, q, t⟩ =
      some ⟨State.B, q + 1, writeAt t q true⟩ := by simp [stepN, s1]
  have p2 : stepN 2 ⟨State.A, q, t⟩ =
      some ⟨State.B, q, writeAt (writeAt t q true) (q + 1) true⟩ := by
    simp [stepN, s1, s2]
  have p3 : stepN 3 ⟨State.A, q, t⟩ =
      some ⟨State.C, q + 1, writeAt (writeAt t q true) (q + 1) true⟩ := by
    simp [stepN, s1, s2, s3]
  have p4 : stepN 4 ⟨State.A, q, t⟩ =
      some ⟨State.D, q + 2, writeAt (writeAt t q true) (q + 1) false⟩ := by
    simp [stepN, s1, s2, s3, s4]
  have p5 : stepN 5 ⟨State.A, q, t⟩ =
      some ⟨State.E, q + 3,
        writeAt (writeAt (writeAt t q true) (q + 1) false) (q + 2) true⟩ := by
    simp [stepN, s1, s2, s3, s4, s5]
  refine ⟨?_, ?_⟩
  · show stepN 6 ⟨State.A, q, t⟩ = _
    simp [stepN, s1, s2, s3, s4, s5, s6]
  · intro k d hk hkd hC hread
    have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl
    · have hd : (⟨State.A, q, t⟩ : Config) = d := by simpa [stepN] using hkd
      rw [← hd] at hC; simp at hC
    · rw [p1] at hkd; rw [← Option.some_inj.mp hkd] at hC; simp at hC
    · rw [p2] at hkd; rw [← Option.some_inj.mp hkd] at hC; simp at hC
    · rw [p3] at hkd
      rw [← Option.some_inj.mp hkd] at hread
      rw [show (⟨State.C, q + 1,
            writeAt (writeAt t q true) (q + 1) true⟩ : Config).tape
            (⟨State.C, q + 1,
              writeAt (writeAt t q true) (q + 1) true⟩ : Config).head
          = writeAt (writeAt t q true) (q + 1) true (q + 1) from rfl] at hread
      rw [r3] at hread
      exact absurd hread (by simp)
    · rw [p4] at hkd; rw [← Option.some_inj.mp hkd] at hC; simp at hC
    · rw [p5] at hkd; rw [← Option.some_inj.mp hkd] at hC; simp at hC

/-- `catTape` leaves cells outside `[h, h + n + 1]` untouched. -/
theorem catTape_outside :
    ∀ (n : Nat) (t : Int → Bool) (h x : Int),
      (x < h ∨ h + n + 1 < x) → catTape t h n x = t x := by
  intro n
  induction n with
  | zero => intro t h x _; rfl
  | succ n ih =>
      intro t h x hx
      show catTape (writeAt (writeAt (writeAt t h true) (h + 1) false)
        (h + 2) false) (h + 1) n x = t x
      rw [ih _ (h + 1) x (by omega)]
      rw [writeAt_other _ (h + 2) x false (by omega),
          writeAt_other _ (h + 1) x false (by omega),
          writeAt_other t h x true (by omega)]

/-- `catTape` lays a trail of `1`s on `[h, h + n)`. -/
theorem catTape_trail :
    ∀ (n : Nat) (t : Int → Bool) (h x : Int),
      h ≤ x → x < h + n → catTape t h n x = true := by
  intro n
  induction n with
  | zero => intro t h x h1 h2; exact absurd h2 (by omega)
  | succ n ih =>
      intro t h x h1 h2
      show catTape (writeAt (writeAt (writeAt t h true) (h + 1) false)
        (h + 2) false) (h + 1) n x = true
      by_cases hx : x = h
      · rw [hx]
        rw [catTape_outside n _ (h + 1) h (by omega)]
        rw [writeAt_other _ (h + 2) h false (by omega),
            writeAt_other _ (h + 1) h false (by omega)]
        exact writeAt_same t h true
      · exact ih _ (h + 1) x (by omega) (by omega)

/-- `catTape` ends with two `0`s at `h + n` and `h + n + 1`, given the two
initial `0`s of the cycle precondition. -/
theorem catTape_end :
    ∀ (n : Nat) (t : Int → Bool) (h : Int), t h = false → t (h + 1) = false →
      catTape t h n (h + n) = false ∧ catTape t h n (h + n + 1) = false := by
  intro n
  induction n with
  | zero =>
      intro t h h0 h1
      constructor
      · show catTape t h 0 (h + (0 : Nat)) = false
        rw [show h + ((0 : Nat) : Int) = h by omega]
        exact h0
      · rw [show h + ((0 : Nat) : Int) + 1 = h + 1 by omega]
        exact h1
  | succ n ih =>
      intro t h h0 h1
      have hz0 : writeAt (writeAt (writeAt t h true) (h + 1) false)
          (h + 2) false (h + 1) = false := by
        rw [writeAt_other _ (h + 2) (h + 1) false (by omega)]
        exact writeAt_same (writeAt t h true) (h + 1) false
      have hz1 : writeAt (writeAt (writeAt t h true) (h + 1) false)
          (h + 2) false (h + 1 + 1) = false := by
        rw [show h + 1 + 1 = h + 2 by omega]
        exact writeAt_same _ (h + 2) false
      obtain ⟨e0, e1⟩ := ih _ (h + 1) hz0 hz1
      constructor
      · show catTape (writeAt (writeAt (writeAt t h true) (h + 1) false)
          (h + 2) false) (h + 1) n (h + ((n + 1 : Nat) : Int)) = false
        rw [show h + ((n + 1 : Nat) : Int) = h + 1 + (n : Int) by omega]
        exact e0
      · rw [show h + ((n + 1 : Nat) : Int) + 1 = h + 1 + (n : Int) + 1 by omega]
        exact e1

/-- **The dominant rule, end to end.**  From an L-record of shape
`(1, m+4, 1)` with single-0 gaps: exactly `13 + 5m` raw steps, ending in
state `E` at the new right frontier, and every C-probe of a `0` along the
way has a `1` to its right — for all `m`. -/
theorem dominant_rule_run {c : Config} {p : Int} (m : Nat)
    (hs : c.state = State.A) (hh : c.head = p)
    (t0 : c.tape p = false) (t1 : c.tape (p + 1) = true)
    (t2 : c.tape (p + 2) = false)
    (tb : ∀ i : Nat, i < m + 4 → c.tape (p + 3 + i) = true)
    (tg : c.tape (p + 7 + m) = false)
    (tr : c.tape (p + 8 + m) = true) :
    (∃ tf : Int → Bool,
        stepN (13 + 5 * m) c = some ⟨State.E, p + 9 + m, tf⟩) ∧
      CSafeSeg c (13 + 5 * m) := by
  have hb3 : c.tape (p + 3) = true := by
    have := tb 0 (by omega)
    simpa using this
  have hb4 : c.tape (p + 4) = true := by
    have := tb 1 (by omega)
    rw [show p + 3 + ((1 : Nat) : Int) = p + 4 by omega] at this
    exact this
  have hb5 : c.tape (p + 5) = true := by
    have := tb 2 (by omega)
    rw [show p + 3 + ((2 : Nat) : Int) = p + 5 by omega] at this
    exact this
  have hb6 : c.tape (p + 6) = true := by
    have := tb 3 (by omega)
    rw [show p + 3 + ((3 : Nat) : Int) = p + 6 by omega] at this
    exact this
  obtain ⟨sP, safeP⟩ := prefix_run hs hh t0 t1 t2 hb3 hb4 hb5 hb6
  -- the tape after the prefix
  have hTP0 : writeAt (writeAt (writeAt (writeAt c.tape p true) (p + 3) false)
      (p + 5) false) (p + 6) false (p + 5) = false := by
    rw [writeAt_other _ (p + 6) (p + 5) false (by omega)]
    exact writeAt_same _ (p + 5) false
  have hTP1 : writeAt (writeAt (writeAt (writeAt c.tape p true) (p + 3) false)
      (p + 5) false) (p + 6) false (p + 5 + 1) = false := by
    rw [show p + 5 + 1 = p + 6 by omega]
    exact writeAt_same _ (p + 6) false
  have hTPones : ∀ i : Nat, i < m →
      writeAt (writeAt (writeAt (writeAt c.tape p true) (p + 3) false)
        (p + 5) false) (p + 6) false (p + 5 + 2 + i) = true := by
    intro i hi
    rw [writeAt_other _ (p + 6) _ false (by omega),
        writeAt_other _ (p + 5) _ false (by omega),
        writeAt_other _ (p + 3) _ false (by omega),
        writeAt_other _ p _ true (by omega)]
    have := tb (i + 4) (by omega)
    rw [show p + 5 + 2 + (i : Int) = p + 3 + ((i + 4 : Nat) : Int) by omega]
    exact this
  obtain ⟨sC, safeC⟩ := cat_run m
    ⟨State.A, p + 5,
      writeAt (writeAt (writeAt (writeAt c.tape p true) (p + 3) false)
        (p + 5) false) (p + 6) false⟩
    (p + 5) rfl rfl hTP0 hTP1 hTPones
  -- the tape after the caterpillar; suffix preconditions at q = p + 5 + m
  obtain ⟨e0, e1⟩ := catTape_end m
    (writeAt (writeAt (writeAt (writeAt c.tape p true) (p + 3) false)
      (p + 5) false) (p + 6) false) (p + 5) hTP0 hTP1
  have hq2 : catTape
      (writeAt (writeAt (writeAt (writeAt c.tape p true) (p + 3) false)
        (p + 5) false) (p + 6) false) (p + 5) m (p + 5 + m + 2) = false := by
    rw [catTape_outside m _ (p + 5) _ (by omega)]
    rw [writeAt_other _ (p + 6) _ false (by omega),
        writeAt_other _ (p + 5) _ false (by omega),
        writeAt_other _ (p + 3) _ false (by omega),
        writeAt_other _ p _ true (by omega)]
    rw [show p + 5 + (m : Int) + 2 = p + 7 + (m : Int) by omega]
    exact tg
  have hq3 : catTape
      (writeAt (writeAt (writeAt (writeAt c.tape p true) (p + 3) false)
        (p + 5) false) (p + 6) false) (p + 5) m (p + 5 + m + 3) = true := by
    rw [catTape_outside m _ (p + 5) _ (by omega)]
    rw [writeAt_other _ (p + 6) _ false (by omega),
        writeAt_other _ (p + 5) _ false (by omega),
        writeAt_other _ (p + 3) _ false (by omega),
        writeAt_other _ p _ true (by omega)]
    rw [show p + 5 + (m : Int) + 3 = p + 8 + (m : Int) by omega]
    exact tr
  obtain ⟨sS, safeS⟩ := suffix_run
    (c := ⟨State.A, p + 5 + m, catTape
      (writeAt (writeAt (writeAt (writeAt c.tape p true) (p + 3) false)
        (p + 5) false) (p + 6) false) (p + 5) m⟩)
    (q := p + 5 + m) rfl rfl e0 e1 hq2 hq3
  refine ⟨⟨writeAt (writeAt (writeAt
      (catTape (writeAt (writeAt (writeAt (writeAt c.tape p true)
          (p + 3) false) (p + 5) false) (p + 6) false) (p + 5) m)
      (p + 5 + m) true) (p + 5 + m + 1) false) (p + 5 + m + 2) true, ?_⟩, ?_⟩
  · rw [show 13 + 5 * m = 7 + (5 * m + 6) by omega, stepN_add, sP]
    show stepN (5 * m + 6)
        ⟨State.A, p + 5,
          writeAt (writeAt (writeAt (writeAt c.tape p true) (p + 3) false)
            (p + 5) false) (p + 6) false⟩ = _
    rw [stepN_add, sC]
    show stepN 6
        ⟨State.A, p + 5 + m, catTape
          (writeAt (writeAt (writeAt (writeAt c.tape p true) (p + 3) false)
            (p + 5) false) (p + 6) false) (p + 5) m⟩ = _
    rw [sS]
    rw [show p + 5 + (m : Int) + 4 = p + 9 + (m : Int) by omega]
  · rw [show 13 + 5 * m = 7 + (5 * m + 6) by omega]
    exact csafe_compose sP safeP
      (csafe_compose sC (csafe_of_strong safeC) safeS)

end QIG.Dossier1RawTM

#print axioms QIG.Dossier1RawTM.halt_requires_c_probe_00
#print axioms QIG.Dossier1RawTM.blank_nonhalting_of_c_probe_safe
#print axioms QIG.Dossier1RawTM.cat_cycle
#print axioms QIG.Dossier1RawTM.cat_run
#print axioms QIG.Dossier1RawTM.prefix_run
#print axioms QIG.Dossier1RawTM.suffix_run
#print axioms QIG.Dossier1RawTM.dominant_rule_run
