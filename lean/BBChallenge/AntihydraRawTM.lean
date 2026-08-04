import Lean.Elab.Tactic.Omega

/-!
# Antihydra raw Turing-machine semantics and halt localization

Bare-Lean model of the concrete BB(6) machine

`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`  (Antihydra).

Checked statements (no sorry, no extra axioms):

* `step_eq_none_iff` — the machine halts in one step exactly at the unique
  undefined transition `F0`.
* `into_F_only_from_E0` — state `F` is entered only via `E` reading `0`
  (the transition `E0 = 1LF`: write `1`, move left).
* `halt_requires_e_probe_00` — any raw halt from a non-`F` start passes
  through a reachable configuration in state `E` reading `0` whose left
  neighbour is also `0`.
* `nonhalting_of_e_probe_safe` / `blank_nonhalting_of_e_probe_safe` — the
  E-probe-safety invariant ("every 0 that state E reads has a 1 to its
  left") implies the machine never halts.

`EProbeSafe blankStart` is exactly the invariant discharged empirically by
stage753 (13/13 (rule, window) obligations `DISCHARGED_UNIFORM`; 14,109
entry events over 10^8 steps, zero unsafe landings).  Proving it from the
13 macro obligations is the remaining raw-to-macro contract, in the style
of `Dossier1RawTM` / `DvisetuRawTM`'s layered endgame.
-/

namespace QIG.AntihydraRawTM

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

/-- The Antihydra transition table.  `none` is the undefined halt
transition. -/
def instr : State → Bool → Option Instr
  | State.A, false => some ⟨State.B, true, Dir.R⟩
  | State.A, true => some ⟨State.A, true, Dir.R⟩
  | State.B, false => some ⟨State.C, false, Dir.L⟩
  | State.B, true => some ⟨State.E, true, Dir.L⟩
  | State.C, false => some ⟨State.D, true, Dir.L⟩
  | State.C, true => some ⟨State.C, true, Dir.L⟩
  | State.D, false => some ⟨State.A, true, Dir.L⟩
  | State.D, true => some ⟨State.B, false, Dir.L⟩
  | State.E, false => some ⟨State.F, true, Dir.L⟩
  | State.E, true => some ⟨State.E, true, Dir.R⟩
  | State.F, false => none
  | State.F, true => some ⟨State.A, false, Dir.R⟩

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

/-- State `F` is entered only by `E` reading `0` (the transition
`E0 = 1LF`): the predecessor is in state `E` on a `0`, and the successor
sits one cell to the left with a `1` written at the probed cell. -/
theorem into_F_only_from_E0 {c c' : Config} (h : step c = some c')
    (hF : c'.state = State.F) :
    c.state = State.E ∧ c.tape c.head = false ∧
      c'.head = c.head - 1 ∧ c'.tape = writeAt c.tape c.head true := by
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
configuration where `E` reads a `0` whose left neighbour is also `0`. -/
theorem halt_requires_e_probe_00 {c : Config} (hne : c.state ≠ State.F)
    (hh : RawHalts c) :
    ∃ d : Config, Reaches c d ∧ d.state = State.E ∧
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
      obtain ⟨hE, h0, hhead, htape⟩ := into_F_only_from_E0 hstepe hF.1
      refine ⟨e, ⟨k', he⟩, hE, h0, ?_⟩
      have hread : d0.tape d0.head = false := hF.2
      rw [htape, hhead] at hread
      rwa [writeAt_other e.tape e.head (e.head - 1) true (by omega)] at hread

/-- The E-probe-safety invariant: every `0` that state `E` reads in any
reachable configuration has a `1` immediately to its left.  This is exactly
the invariant discharged empirically by stage753. -/
def EProbeSafe (c : Config) : Prop :=
  ∀ d : Config, Reaches c d → d.state = State.E → d.tape d.head = false →
    d.tape (d.head - 1) = true

/-- E-probe safety implies the machine never halts. -/
theorem nonhalting_of_e_probe_safe {c : Config} (hne : c.state ≠ State.F)
    (hsafe : EProbeSafe c) : ¬ RawHalts c := by
  intro hh
  obtain ⟨d, hreach, hE, h0, h00⟩ := halt_requires_e_probe_00 hne hh
  have h1 := hsafe d hreach hE h0
  rw [h1] at h00
  exact Bool.noConfusion h00

/-- Specialization to the blank start: the remaining raw-to-macro contract is
exactly `EProbeSafe blankStart`. -/
theorem blank_nonhalting_of_e_probe_safe
    (hsafe : EProbeSafe blankStart) : ¬ RawHalts blankStart := by
  have hne : blankStart.state ≠ State.F := by
    simp [blankStart]
  exact nonhalting_of_e_probe_safe hne hsafe

/-!
## Sweep lemmas — the atoms of the raw-to-macro rule lemmas

Antihydra's three self-looping transitions (`A1 = 1RA`, `C1 = 1LC`,
`E1 = 1RE`) each rewrite `1` over `1`, so the tape is literally unchanged
and a head crossing a block of `n` ones is a clean induction.  Every
stage753 macro-rule micro-trajectory decomposes into these sweeps plus a
bounded number of boundary steps.
-/

theorem writeAt_self (tape : Int → Bool) (pos : Int) {value : Bool}
    (h : tape pos = value) : writeAt tape pos value = tape := by
  funext x
  by_cases hx : x = pos
  · subst hx; simp [writeAt, h]
  · simp [writeAt, hx]

theorem step_A_on_one {c : Config} (hs : c.state = State.A)
    (ht : c.tape c.head = true) :
    step c = some ⟨State.A, c.head + 1, c.tape⟩ := by
  have hw := writeAt_self c.tape c.head ht
  simp [step, instr, hs, ht, move, hw]

theorem step_C_on_one {c : Config} (hs : c.state = State.C)
    (ht : c.tape c.head = true) :
    step c = some ⟨State.C, c.head - 1, c.tape⟩ := by
  have hw := writeAt_self c.tape c.head ht
  simp [step, instr, hs, ht, move, hw]

theorem step_E_on_one {c : Config} (hs : c.state = State.E)
    (ht : c.tape c.head = true) :
    step c = some ⟨State.E, c.head + 1, c.tape⟩ := by
  have hw := writeAt_self c.tape c.head ht
  simp [step, instr, hs, ht, move, hw]

/-- State `E` sweeps right across `n` ones without touching the tape. -/
theorem sweep_E :
    ∀ (n : Nat) (c : Config), c.state = State.E →
      (∀ i : Nat, i < n → c.tape (c.head + i) = true) →
      stepN n c = some ⟨State.E, c.head + n, c.tape⟩ := by
  intro n
  induction n with
  | zero =>
      intro c hs _
      obtain ⟨s, h, t⟩ := c
      simp_all [stepN]
  | succ n ih =>
      intro c hs hones
      have h0 : c.tape c.head = true := by
        simpa using hones 0 (Nat.succ_pos n)
      have hstep := step_E_on_one hs h0
      have hnext : stepN n ⟨State.E, c.head + 1, c.tape⟩ =
          some ⟨State.E, c.head + 1 + (n : Int), c.tape⟩ :=
        ih ⟨State.E, c.head + 1, c.tape⟩ rfl
          (fun i hi => by
            have h := hones (i + 1) (by omega)
            have heq : c.head + 1 + (i : Int) = c.head + ((i + 1 : Nat) : Int) := by
              omega
            rw [heq]; exact h)
      have harith : c.head + 1 + (n : Int) = c.head + ((n + 1 : Nat) : Int) := by
        omega
      rw [show stepN (n + 1) c = (step c).bind (stepN n) from rfl, hstep]
      rw [show ((some ⟨State.E, c.head + 1, c.tape⟩ : Option Config).bind (stepN n))
            = stepN n ⟨State.E, c.head + 1, c.tape⟩ from rfl]
      rw [hnext, harith]

/-- State `A` sweeps right across `n` ones without touching the tape. -/
theorem sweep_A :
    ∀ (n : Nat) (c : Config), c.state = State.A →
      (∀ i : Nat, i < n → c.tape (c.head + i) = true) →
      stepN n c = some ⟨State.A, c.head + n, c.tape⟩ := by
  intro n
  induction n with
  | zero =>
      intro c hs _
      obtain ⟨s, h, t⟩ := c
      simp_all [stepN]
  | succ n ih =>
      intro c hs hones
      have h0 : c.tape c.head = true := by
        simpa using hones 0 (Nat.succ_pos n)
      have hstep := step_A_on_one hs h0
      have hnext : stepN n ⟨State.A, c.head + 1, c.tape⟩ =
          some ⟨State.A, c.head + 1 + (n : Int), c.tape⟩ :=
        ih ⟨State.A, c.head + 1, c.tape⟩ rfl
          (fun i hi => by
            have h := hones (i + 1) (by omega)
            have heq : c.head + 1 + (i : Int) = c.head + ((i + 1 : Nat) : Int) := by
              omega
            rw [heq]; exact h)
      have harith : c.head + 1 + (n : Int) = c.head + ((n + 1 : Nat) : Int) := by
        omega
      rw [show stepN (n + 1) c = (step c).bind (stepN n) from rfl, hstep]
      rw [show ((some ⟨State.A, c.head + 1, c.tape⟩ : Option Config).bind (stepN n))
            = stepN n ⟨State.A, c.head + 1, c.tape⟩ from rfl]
      rw [hnext, harith]

/-- State `C` sweeps left across `n` ones without touching the tape. -/
theorem sweep_C :
    ∀ (n : Nat) (c : Config), c.state = State.C →
      (∀ i : Nat, i < n → c.tape (c.head - i) = true) →
      stepN n c = some ⟨State.C, c.head - n, c.tape⟩ := by
  intro n
  induction n with
  | zero =>
      intro c hs _
      obtain ⟨s, h, t⟩ := c
      simp_all [stepN]
  | succ n ih =>
      intro c hs hones
      have h0 : c.tape c.head = true := by
        simpa using hones 0 (Nat.succ_pos n)
      have hstep := step_C_on_one hs h0
      have hnext : stepN n ⟨State.C, c.head - 1, c.tape⟩ =
          some ⟨State.C, c.head - 1 - (n : Int), c.tape⟩ :=
        ih ⟨State.C, c.head - 1, c.tape⟩ rfl
          (fun i hi => by
            have h := hones (i + 1) (by omega)
            have heq : c.head - 1 - (i : Int) = c.head - ((i + 1 : Nat) : Int) := by
              omega
            rw [heq]; exact h)
      have harith : c.head - 1 - (n : Int) = c.head - ((n + 1 : Nat) : Int) := by
        omega
      rw [show stepN (n + 1) c = (step c).bind (stepN n) from rfl, hstep]
      rw [show ((some ⟨State.C, c.head - 1, c.tape⟩ : Option Config).bind (stepN n))
            = stepN n ⟨State.C, c.head - 1, c.tape⟩ from rfl]
      rw [hnext, harith]

/-!
## Segment algebra and the E-probe keystone

Mirror of the dossier-1 development, with `E` in place of `C` as the
danger state (Antihydra enters `F` only via `E0`, moving *left*).
-/

theorem writeAt_overwrite (tape : Int → Bool) (pos : Int) (v w : Bool) :
    writeAt (writeAt tape pos v) pos w = writeAt tape pos w := by
  funext x
  by_cases hx : x = pos <;> simp [writeAt, hx]

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

/-- Conditional E-probe safety over the first `N` steps of a run. -/
def ESafeSeg (c : Config) (N : Nat) : Prop :=
  ∀ k d, k < N → stepN k c = some d → d.state = State.E →
    d.tape d.head = false → d.tape (d.head - 1) = true

theorem esafe_compose {c c' : Config} {m n : Nat}
    (hm : stepN m c = some c') (h1 : ESafeSeg c m) (h2 : ESafeSeg c' n) :
    ESafeSeg c (m + n) := by
  intro k d hk hkd hE hread
  by_cases hkm : k < m
  · exact h1 k d hkm hkd hE hread
  · have hkeq : k = m + (k - m) := by omega
    rw [hkeq, stepN_add, hm] at hkd
    exact h2 (k - m) d (by omega) hkd hE hread

/-- A segment in which every `E` configuration reads a `1` is safe. -/
theorem esafe_of_strong {c : Config} {N : Nat}
    (h : ∀ k d, k < N → stepN k c = some d → d.state = State.E →
      d.tape d.head = true) : ESafeSeg c N := by
  intro k d hk hkd hE hread
  rw [h k d hk hkd hE] at hread
  exact absurd hread (by simp)

/-- A segment with no `E` configuration at all is safe. -/
theorem esafe_of_noE {c : Config} {N : Nat}
    (h : ∀ k d, k < N → stepN k c = some d → d.state ≠ State.E) :
    ESafeSeg c N := by
  intro k d hk hkd hE _
  exact absurd hE (h k d hk hkd)

/-- The segment-induction keystone: an invariant maintained by positive
safe segments gives `EProbeSafe` for the whole infinite run. -/
theorem eprobe_safe_of_segments {Inv : Config → Prop} {c0 : Config}
    (h0 : Inv c0)
    (hseg : ∀ c, Inv c → ∃ k, 0 < k ∧ ∃ c', stepN k c = some c' ∧
      Inv c' ∧ ESafeSeg c k) :
    EProbeSafe c0 := by
  have main : ∀ (N n : Nat) (c : Config), n ≤ N → Inv c →
      ∀ d, stepN n c = some d → d.state = State.E →
        d.tape d.head = false → d.tape (d.head - 1) = true := by
    intro N
    induction N with
    | zero =>
        intro n c hn hInv d hd hE hread
        obtain ⟨k, hk, c', _hs, _hInv', hsafe⟩ := hseg c hInv
        exact hsafe n d (by omega) hd hE hread
    | succ N ihN =>
        intro n c hn hInv d hd hE hread
        obtain ⟨k, hk, c', hs, hInv', hsafe⟩ := hseg c hInv
        by_cases hlt : n < k
        · exact hsafe n d hlt hd hE hread
        · have hneq : n = k + (n - k) := by omega
          rw [hneq, stepN_add, hs] at hd
          exact ihN (n - k) c' (by omega) hInv' d hd hE hread
  intro d hreach hE hread
  obtain ⟨n, hn⟩ := hreach
  exact main n n c0 (Nat.le_refl n) h0 d hn hE hread

/-- Prefix safety plus tail safety gives whole-run safety. -/
theorem eprobe_safe_prefix {c d : Config} {M : Nat} (hM : stepN M c = some d)
    (hpre : ESafeSeg c M) (hpost : EProbeSafe d) : EProbeSafe c := by
  intro e hreach hE hread
  obtain ⟨n, hn⟩ := hreach
  by_cases h : n < M
  · exact hpre n e h hn hE hread
  · have hsplit : n = M + (n - M) := by omega
    rw [hsplit, stepN_add, hM] at hn
    exact hpost e ⟨n - M, hn⟩ hE hread

/-!
## The hydra rule — 96% of Antihydra's record dynamics

From a record `(a, m, c)` (blocks separated by single-`0` gaps, head on
the fresh right frontier, `m ≥ 3`), the machine runs exactly `2c + 11`
raw steps to the next record `(a, m - 2, c + 3)`.  The trajectory reads
only the top three cells of the `m`-block and everything right of it, so
the counter block `a` is untouched — the counter moves only in the rare
merge and drop rules.

Anchoring at `p`, the right end of the `m`-block: cells `p-2, p-1, p` are
`1`, `p+1` is the gap, `p+2 .. p+1+c` is the `c`-block, `p+2+c` is the
frontier.  Net effect: `p-1 ↦ 0`, `p+1 ↦ 1`, `p+2+c ↦ 1`, head to
`p+3+c`.  The single `E`-probe of a `0` occurs at `p`, and is safe
because `p-1` still holds a `1` at that moment. -/
theorem hydra_step {cfg : Config} {p : Int} (k : Nat)
    (hs : cfg.state = State.B) (hh : cfg.head = p + 2 + k)
    (tm2 : cfg.tape (p - 2) = true) (tm1 : cfg.tape (p - 1) = true)
    (tm0 : cfg.tape p = true) (tg : cfg.tape (p + 1) = false)
    (tc : ∀ i : Nat, i < k → cfg.tape (p + 2 + i) = true)
    (tf : cfg.tape (p + 2 + k) = false) :
    stepN (2 * k + 11) cfg = some ⟨State.B, p + 3 + k,
        writeAt (writeAt (writeAt cfg.tape (p + 1) true) (p - 1) false)
          (p + 2 + k) true⟩ ∧
      ESafeSeg cfg (2 * k + 11) := by
  obtain ⟨s, hd, t⟩ := cfg
  simp only at hs hh tm2 tm1 tm0 tg tc tf
  subst hs hd
  have hw2p : (writeAt t (p + 1) true) p = true := by
    rw [writeAt_other t (p + 1) p true (by omega)]; exact tm0
  have hw2m1 : (writeAt t (p + 1) true) (p - 1) = true := by
    rw [writeAt_other t (p + 1) _ true (by omega)]; exact tm1
  have hw2m2 : (writeAt t (p + 1) true) (p - 2) = true := by
    rw [writeAt_other t (p + 1) _ true (by omega)]; exact tm2
  have hw3p : (writeAt (writeAt t (p + 1) true) p false) p = false := writeAt_same _ p false
  have hw3m1 : (writeAt (writeAt t (p + 1) true) p false) (p - 1) = true := by
    rw [writeAt_other _ p _ false (by omega)]; exact hw2m1
  have hw3m2 : (writeAt (writeAt t (p + 1) true) p false) (p - 2) = true := by
    rw [writeAt_other _ p _ false (by omega)]; exact hw2m2
  have s1 : step ⟨State.B, p + 2 + k, t⟩ = some ⟨State.C, p + 1 + k, t⟩ := by
    have hself : writeAt t (p + 2 + (k : Int)) false = t := writeAt_self t _ tf
    simp [step, instr, tf, move, hself]
    try omega
  have sC : stepN k ⟨State.C, p + 1 + k, t⟩ = some ⟨State.C, p + 1, t⟩ := by
    have h := sweep_C k ⟨State.C, p + 1 + k, t⟩ rfl
      (fun i hi => by
        show t (p + 1 + (k : Int) - (i : Int)) = true
        have := tc (k - 1 - i) (by omega)
        rw [show p + 1 + (k : Int) - (i : Int)
              = p + 2 + ((k - 1 - i : Nat) : Int) by omega]
        exact this)
    rw [show p + 1 + (k : Int) - (k : Int) = p + 1 by omega] at h
    exact h
  have s2 : step ⟨State.C, p + 1, t⟩ = some ⟨State.D, p, (writeAt t (p + 1) true)⟩ := by
    simp [step, instr, tg, move]
    try omega
  have s3 : step ⟨State.D, p, (writeAt t (p + 1) true)⟩ = some ⟨State.B, p - 1, (writeAt (writeAt t (p + 1) true) p false)⟩ := by
    simp [step, instr, hw2p, move]
    try omega
  have s4 : step ⟨State.B, p - 1, (writeAt (writeAt t (p + 1) true) p false)⟩ = some ⟨State.E, p - 2, (writeAt (writeAt t (p + 1) true) p false)⟩ := by
    have hself : writeAt (writeAt (writeAt t (p + 1) true) p false) (p - 1) true = (writeAt (writeAt t (p + 1) true) p false) := writeAt_self _ _ hw3m1
    simp [step, instr, hw3m1, move, hself]
    try omega
  have s5 : step ⟨State.E, p - 2, (writeAt (writeAt t (p + 1) true) p false)⟩ = some ⟨State.E, p - 1, (writeAt (writeAt t (p + 1) true) p false)⟩ := by
    have hself : writeAt (writeAt (writeAt t (p + 1) true) p false) (p - 2) true = (writeAt (writeAt t (p + 1) true) p false) := writeAt_self _ _ hw3m2
    simp [step, instr, hw3m2, move, hself]
    try omega
  have s6 : step ⟨State.E, p - 1, (writeAt (writeAt t (p + 1) true) p false)⟩ = some ⟨State.E, p, (writeAt (writeAt t (p + 1) true) p false)⟩ := by
    have hself : writeAt (writeAt (writeAt t (p + 1) true) p false) (p - 1) true = (writeAt (writeAt t (p + 1) true) p false) := writeAt_self _ _ hw3m1
    simp [step, instr, hw3m1, move, hself]
    try omega
  have s7 : step ⟨State.E, p, (writeAt (writeAt t (p + 1) true) p false)⟩ = some ⟨State.F, p - 1, (writeAt t (p + 1) true)⟩ := by
    have hover : writeAt (writeAt (writeAt t (p + 1) true) p false) p true = (writeAt t (p + 1) true) := by
      rw [writeAt_overwrite]
      exact writeAt_self _ p hw2p
    simp [step, instr, hw3p, move, hover]
    try omega
  have s8 : step ⟨State.F, p - 1, (writeAt t (p + 1) true)⟩ = some ⟨State.A, p, (writeAt (writeAt t (p + 1) true) (p - 1) false)⟩ := by
    simp [step, instr, hw2m1, move]
    try omega
  have hw6c : ∀ i : Nat, i < k + 2 → (writeAt (writeAt t (p + 1) true) (p - 1) false) (p + i) = true := by
    intro i hi
    rw [writeAt_other _ (p - 1) _ false (by omega)]
    by_cases hi0 : i = 0
    · rw [hi0, show p + ((0 : Nat) : Int) = p by omega]; exact hw2p
    · by_cases hi1 : i = 1
      · rw [hi1, show p + ((1 : Nat) : Int) = p + 1 by omega]
        exact writeAt_same t (p + 1) true
      · rw [writeAt_other t (p + 1) _ true (by omega)]
        have := tc (i - 2) (by omega)
        rw [show p + (i : Int) = p + 2 + ((i - 2 : Nat) : Int) by omega]
        exact this
  have sA : stepN (k + 2) ⟨State.A, p, (writeAt (writeAt t (p + 1) true) (p - 1) false)⟩ =
      some ⟨State.A, p + 2 + k, (writeAt (writeAt t (p + 1) true) (p - 1) false)⟩ := by
    have h := sweep_A (k + 2) ⟨State.A, p, (writeAt (writeAt t (p + 1) true) (p - 1) false)⟩ rfl (fun i hi => hw6c i hi)
    rw [show p + ((k + 2 : Nat) : Int) = p + 2 + (k : Int) by omega] at h
    exact h
  have hw6f : (writeAt (writeAt t (p + 1) true) (p - 1) false) (p + 2 + k) = false := by
    rw [writeAt_other _ (p - 1) _ false (by omega),
        writeAt_other t (p + 1) _ true (by omega)]
    exact tf
  have s9 : step ⟨State.A, p + 2 + k, (writeAt (writeAt t (p + 1) true) (p - 1) false)⟩ =
      some ⟨State.B, p + 3 + k, writeAt (writeAt (writeAt t (p + 1) true) (p - 1) false) (p + 2 + k) true⟩ := by
    simp [step, instr, hw6f, move]
    try omega
  have a1 : stepN 1 ⟨State.B, p + 2 + k, t⟩ = some ⟨State.C, p + 1 + k, t⟩ := by
    simp [stepN, s1]
  have a2 : stepN (1 + k) ⟨State.B, p + 2 + k, t⟩ =
      some ⟨State.C, p + 1, t⟩ := by rw [stepN_add, a1]; exact sC
  have hmid : stepN 6 ⟨State.C, p + 1, t⟩ = some ⟨State.F, p - 1, (writeAt t (p + 1) true)⟩ := by
    simp [stepN, s2, s3, s4, s5, s6, s7]
  have a3 : stepN (1 + k + 6) ⟨State.B, p + 2 + k, t⟩ =
      some ⟨State.F, p - 1, (writeAt t (p + 1) true)⟩ := by rw [stepN_add, a2]; exact hmid
  have hF1 : stepN 1 ⟨State.F, p - 1, (writeAt t (p + 1) true)⟩ = some ⟨State.A, p, (writeAt (writeAt t (p + 1) true) (p - 1) false)⟩ := by
    simp [stepN, s8]
  have a4 : stepN (1 + k + 6 + 1) ⟨State.B, p + 2 + k, t⟩ =
      some ⟨State.A, p, (writeAt (writeAt t (p + 1) true) (p - 1) false)⟩ := by rw [stepN_add, a3]; exact hF1
  have a5 : stepN (1 + k + 6 + 1 + (k + 2)) ⟨State.B, p + 2 + k, t⟩ =
      some ⟨State.A, p + 2 + k, (writeAt (writeAt t (p + 1) true) (p - 1) false)⟩ := by rw [stepN_add, a4]; exact sA
  have hA1 : stepN 1 ⟨State.A, p + 2 + k, (writeAt (writeAt t (p + 1) true) (p - 1) false)⟩ =
      some ⟨State.B, p + 3 + k, writeAt (writeAt (writeAt t (p + 1) true) (p - 1) false) (p + 2 + k) true⟩ := by
    simp [stepN, s9]
  have a6 : stepN (1 + k + 6 + 1 + (k + 2) + 1) ⟨State.B, p + 2 + k, t⟩ =
      some ⟨State.B, p + 3 + k, writeAt (writeAt (writeAt t (p + 1) true) (p - 1) false) (p + 2 + k) true⟩ := by
    rw [stepN_add, a5]; exact hA1
  refine ⟨?_, ?_⟩
  · rw [show 2 * k + 11 = 1 + k + 6 + 1 + (k + 2) + 1 by omega]
    exact a6
  · rw [show 2 * k + 11 = 1 + (k + (6 + (1 + ((k + 2) + 1)))) by omega]
    refine esafe_compose a1 (esafe_of_noE ?_) (esafe_compose sC
      (esafe_of_noE ?_) (esafe_compose hmid ?_ (esafe_compose hF1
        (esafe_of_noE ?_) (esafe_compose sA (esafe_of_noE ?_)
          (esafe_of_noE ?_)))))
    · intro j d hj hjd
      have hj0 : j = 0 := by omega
      subst hj0
      have hdd : (⟨State.B, p + 2 + k, t⟩ : Config) = d := by
        simpa [stepN] using hjd
      rw [← hdd]; simp
    · intro j d hj hjd
      have hpart := sweep_C j ⟨State.C, p + 1 + k, t⟩ rfl
        (fun i hi => by
          show t (p + 1 + (k : Int) - (i : Int)) = true
          have := tc (k - 1 - i) (by omega)
          rw [show p + 1 + (k : Int) - (i : Int)
                = p + 2 + ((k - 1 - i : Nat) : Int) by omega]
          exact this)
      rw [hpart] at hjd
      rw [← Option.some_inj.mp hjd]; simp
    · intro j d hj hjd hE hread
      have hcase : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl
      · have hdd : (⟨State.C, p + 1, t⟩ : Config) = d := by
          simpa [stepN] using hjd
        rw [← hdd] at hE; simp at hE
      · rw [show stepN 1 ⟨State.C, p + 1, t⟩ = some ⟨State.D, p, (writeAt t (p + 1) true)⟩ from by
              simp [stepN, s2]] at hjd
        rw [← Option.some_inj.mp hjd] at hE; simp at hE
      · rw [show stepN 2 ⟨State.C, p + 1, t⟩
              = some ⟨State.B, p - 1, (writeAt (writeAt t (p + 1) true) p false)⟩ from by
              simp [stepN, s2, s3]] at hjd
        rw [← Option.some_inj.mp hjd] at hE; simp at hE
      · rw [show stepN 3 ⟨State.C, p + 1, t⟩
              = some ⟨State.E, p - 2, (writeAt (writeAt t (p + 1) true) p false)⟩ from by
              simp [stepN, s2, s3, s4]] at hjd
        rw [← Option.some_inj.mp hjd] at hread
        rw [show (⟨State.E, p - 2, (writeAt (writeAt t (p + 1) true) p false)⟩ : Config).tape
              (⟨State.E, p - 2, (writeAt (writeAt t (p + 1) true) p false)⟩ : Config).head
            = (writeAt (writeAt t (p + 1) true) p false) (p - 2) from rfl] at hread
        rw [hw3m2] at hread
        exact absurd hread (by simp)
      · rw [show stepN 4 ⟨State.C, p + 1, t⟩
              = some ⟨State.E, p - 1, (writeAt (writeAt t (p + 1) true) p false)⟩ from by
              simp [stepN, s2, s3, s4, s5]] at hjd
        rw [← Option.some_inj.mp hjd] at hread
        rw [show (⟨State.E, p - 1, (writeAt (writeAt t (p + 1) true) p false)⟩ : Config).tape
              (⟨State.E, p - 1, (writeAt (writeAt t (p + 1) true) p false)⟩ : Config).head
            = (writeAt (writeAt t (p + 1) true) p false) (p - 1) from rfl] at hread
        rw [hw3m1] at hread
        exact absurd hread (by simp)
      · -- THE probe: E reads the 0 at p; its left neighbour still holds a 1
        rw [show stepN 5 ⟨State.C, p + 1, t⟩
              = some ⟨State.E, p, (writeAt (writeAt t (p + 1) true) p false)⟩ from by
              simp [stepN, s2, s3, s4, s5, s6]] at hjd
        rw [← Option.some_inj.mp hjd]
        show (writeAt (writeAt t (p + 1) true) p false) (p - 1) = true
        exact hw3m1
    · intro j d hj hjd
      have hj0 : j = 0 := by omega
      subst hj0
      have hdd : (⟨State.F, p - 1, (writeAt t (p + 1) true)⟩ : Config) = d := by
        simpa [stepN] using hjd
      rw [← hdd]; simp
    · intro j d hj hjd
      have hpart := sweep_A j ⟨State.A, p, (writeAt (writeAt t (p + 1) true) (p - 1) false)⟩ rfl
        (fun i hi => hw6c i (by omega))
      rw [hpart] at hjd
      rw [← Option.some_inj.mp hjd]; simp
    · intro j d hj hjd
      have hj0 : j = 0 := by omega
      subst hj0
      have hdd : (⟨State.A, p + 2 + k, (writeAt (writeAt t (p + 1) true) (p - 1) false)⟩ : Config) = d := by
        simpa [stepN] using hjd
      rw [← hdd]; simp

end QIG.AntihydraRawTM

#print axioms QIG.AntihydraRawTM.halt_requires_e_probe_00
#print axioms QIG.AntihydraRawTM.blank_nonhalting_of_e_probe_safe
#print axioms QIG.AntihydraRawTM.sweep_E
#print axioms QIG.AntihydraRawTM.sweep_C
#print axioms QIG.AntihydraRawTM.eprobe_safe_of_segments
#print axioms QIG.AntihydraRawTM.hydra_step
