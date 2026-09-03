import Lean.Elab.Tactic.Omega

/-!
# Dvisetu raw Turing-machine semantics and conditional closure

Bare-Lean model of the concrete BB(6) machine

`1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB`  (Dvisetu, dossier-6: the
one-hole two-counter machine).

Checked statements (no sorry, no extra axioms):

* `step_eq_none_iff` — the machine halts in one step exactly at the unique
  undefined transition `F0`.
* `into_F_only_from_E0` — state `F` is entered only via `E` reading `0`
  (the transition `E0 = 0RF`: write `0`, move right).
* `halt_requires_e_probe_00` — any raw halt from a non-`F` start passes
  through a reachable configuration in state `E` reading `0` whose *right*
  neighbour is also `0`.
* `nonhalting_of_e_probe_safe` / `blank_nonhalting_of_e_probe_safe` — the
  E-probe-safety invariant ("every 0 that state E reads has a 1 to its
  right") implies the machine never halts.
* episode theorems (`passA_step`, `passE_step`, `drift_step`,
  `renew2_step`, `collapse_step`, `micro_step`) — the exact validated
  choreography of the timed abstract map of 2026-09-02: drift
  `(a, b) → (a+4, b-3)` in `(32b-41)/3` steps, collapse `(a, 1) → (a+3)`
  in 5, micro `(m) → (m+1)` in 1, and the two linear renewal branches.
* the abstract checkpoint orbit `corbit` / `cstep` with transport
  theorems, and the keystone `safeDvisetuOrbit_nonhalting`:
  `SafeCheckpointOrbit → ¬ RawHalts blankStart`.

`SafeCheckpointOrbit` is the conjunction of (i) the checkpoint conjecture
— the timed abstract orbit from the startup anchor never leaves its
guards — and (ii) `DivideFaithful`, the assumption that the recursive
divide renewal branch (`n ≡ 0 (mod 3)`, quadratic-time, validated on all
raw events to `n = 2,976` but not yet given an episode proof) realizes
its abstract output on the tape.  Both components are exactly the
empirical substrate of the dossier-6 law set (2,746/2,746 record
transitions exact at 20M raw steps); everything else in this file is
proven unconditionally.
-/

namespace QIG.DvisetuRawTM

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
transition. -/
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
`E0 = 0RF`): the predecessor is in state `E` on a `0`, and the successor
sits one cell to the right with the probed cell left at `0`.

Informally: the turnstile into death — `F` is reachable only through `E`
reading a `0`, stepping right over it.  So the final two configurations
of any halting run are completely determined. -/
theorem into_F_only_from_E0 {c c' : Config} (h : step c = some c')
    (hF : c'.state = State.F) :
    c.state = State.E ∧ c.tape c.head = false ∧
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
configuration where `E` reads a `0` whose right neighbour is also `0`.

Informally: *to die, the machine must first stand in state `E` on a `0`
with another `0` immediately to its right* — because the only door into
the halting state `F` is the transition `E0`, which writes the `0` back
and steps right, so the cell `F` then dies on was already `0` when `E`
probed.  An unbounded question ("does it ever halt?") becomes the
reachability of a two-cell pattern. -/
theorem halt_requires_e_probe_00 {c : Config} (hne : c.state ≠ State.F)
    (hh : RawHalts c) :
    ∃ d : Config, Reaches c d ∧ d.state = State.E ∧
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
      obtain ⟨hE, h0, hhead, htape⟩ := into_F_only_from_E0 hstepe hF.1
      refine ⟨e, ⟨k', he⟩, hE, h0, ?_⟩
      have hread : d0.tape d0.head = false := hF.2
      rw [htape, hhead] at hread
      rwa [writeAt_other e.tape e.head (e.head + 1) false (by omega)] at hread

/-- The E-probe-safety invariant: every `0` that state `E` reads in any
reachable configuration has a `1` immediately to its right.

Informally: a sentry condition.  If a `1` always guards the right flank
of whatever `E` probes, the fatal pattern of `halt_requires_e_probe_00`
can never occur, so the machine runs forever.  The rest of this file
exists to discharge this one predicate from the checkpoint dynamics. -/
def EProbeSafe (c : Config) : Prop :=
  ∀ d : Config, Reaches c d → d.state = State.E → d.tape d.head = false →
    d.tape (d.head + 1) = true

/-- E-probe safety implies the machine never halts. -/
theorem nonhalting_of_e_probe_safe {c : Config} (hne : c.state ≠ State.F)
    (hsafe : EProbeSafe c) : ¬ RawHalts c := by
  intro hh
  obtain ⟨d, hreach, hE, h0, h00⟩ := halt_requires_e_probe_00 hne hh
  have h1 := hsafe d hreach hE h0
  rw [h1] at h00
  exact Bool.noConfusion h00

/-- Specialization to the blank start. -/
theorem blank_nonhalting_of_e_probe_safe
    (hsafe : EProbeSafe blankStart) : ¬ RawHalts blankStart := by
  have hne : blankStart.state ≠ State.F := by
    simp [blankStart]
  exact nonhalting_of_e_probe_safe hne hsafe

/-!
## Sweep lemmas, write algebra, and segment safety

Dvisetu's only pure self-loop is `C1 = 1LC` (rewrite `1` over `1`,
move left), so the C-sweep is the sole unbounded straight-line atom.
Rightward travel over ones is the 5-step *gait motif*
`A1 B1 C0 D0 E1` — it zeroes two cells and immediately restores them,
advancing three cells per five steps with the tape literally unchanged.
Every episode of the timed abstract map decomposes into C-sweeps, gait
runs, and a bounded number of boundary steps.
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

/-- Conditional E-probe safety over the first `N` steps of a run: every
`0` probed by state `E` has a `1` immediately to its right. -/
def ESafeSeg (c : Config) (N : Nat) : Prop :=
  ∀ k d, k < N → stepN k c = some d → d.state = State.E →
    d.tape d.head = false → d.tape (d.head + 1) = true

theorem esafe_compose {c c' : Config} {m n : Nat}
    (hm : stepN m c = some c') (h1 : ESafeSeg c m) (h2 : ESafeSeg c' n) :
    ESafeSeg c (m + n) := by
  intro k d hk hkd hE hread
  by_cases hkm : k < m
  · exact h1 k d hkm hkd hE hread
  · have hkeq : k = m + (k - m) := by omega
    rw [hkeq, stepN_add, hm] at hkd
    exact h2 (k - m) d (by omega) hkd hE hread

/-- A segment with no `E` configuration at all is safe. -/
theorem esafe_of_noE {c : Config} {N : Nat}
    (h : ∀ k d, k < N → stepN k c = some d → d.state ≠ State.E) :
    ESafeSeg c N := by
  intro k d hk hkd hE _
  exact absurd hE (h k d hk hkd)

/-- The segment-induction keystone: an invariant maintained by positive
safe segments gives `EProbeSafe` for the whole infinite run.

Informally: *safety in pieces is safety forever*.  If from every
invariant-satisfying configuration the machine runs some positive number
of steps safely and lands on the invariant again, then every moment of
the infinite run falls inside one of these safe segments — strong
induction on how many segments precede it.  This is how finitely many
episode theorems control an infinite trajectory. -/
theorem eprobe_safe_of_segments {Inv : Config → Prop} {c0 : Config}
    (h0 : Inv c0)
    (hseg : ∀ c, Inv c → ∃ k, 0 < k ∧ ∃ c', stepN k c = some c' ∧
      Inv c' ∧ ESafeSeg c k) :
    EProbeSafe c0 := by
  have main : ∀ (N n : Nat) (c : Config), n ≤ N → Inv c →
      ∀ d, stepN n c = some d → d.state = State.E →
        d.tape d.head = false → d.tape (d.head + 1) = true := by
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

theorem step_C_on_one {c : Config} (hs : c.state = State.C)
    (ht : c.tape c.head = true) :
    step c = some ⟨State.C, c.head - 1, c.tape⟩ := by
  have hw := writeAt_self c.tape c.head ht
  simp [step, instr, hs, ht, move, hw]

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
## The gait motif — rightward travel in units of three

From state `A` on a `1` with two more `1`s ahead, the five steps
`A1 B1 C0 D0 E1` zero cells `x` and `x+1`, immediately repaint them, and
leave the head three cells to the right in state `A` — with the tape
function *literally equal* to what it was.  The single `E` configuration
reads a `1`, so the motif is unconditionally probe-safe.
-/

theorem gait_motif {cfg : Config} {x : Int}
    (hs : cfg.state = State.A) (hh : cfg.head = x)
    (h0 : cfg.tape x = true) (h1 : cfg.tape (x + 1) = true)
    (h2 : cfg.tape (x + 2) = true) :
    stepN 5 cfg = some ⟨State.A, x + 3, cfg.tape⟩ ∧ ESafeSeg cfg 5 := by
  obtain ⟨s, hd, t⟩ := cfg
  simp only at hs hh h0 h1 h2
  subst hs hd
  have s1 : step ⟨State.A, x, t⟩ = some ⟨State.B, x + 1, writeAt t x false⟩ := by
    simp [step, instr, h0, move]
  have hr1 : (writeAt t x false) (x + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact h1
  have s2 : step ⟨State.B, x + 1, writeAt t x false⟩ =
      some ⟨State.C, x, writeAt (writeAt t x false) (x + 1) false⟩ := by
    simp [step, instr, hr1, move]
  have hr2 : (writeAt (writeAt t x false) (x + 1) false) x = false := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact writeAt_same _ _ _
  have s3 : step ⟨State.C, x, writeAt (writeAt t x false) (x + 1) false⟩ =
      some ⟨State.D, x + 1,
        writeAt (writeAt (writeAt t x false) (x + 1) false) x true⟩ := by
    simp [step, instr, hr2, move]
  have hr3 : (writeAt (writeAt (writeAt t x false) (x + 1) false) x true) (x + 1) = false := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact writeAt_same _ _ _
  have s4 : step ⟨State.D, x + 1,
      writeAt (writeAt (writeAt t x false) (x + 1) false) x true⟩ =
      some ⟨State.E, x + 2,
        writeAt (writeAt (writeAt (writeAt t x false) (x + 1) false) x true) (x + 1) true⟩ := by
    simp [step, instr, hr3, move]
    omega
  have hrestore :
      writeAt (writeAt (writeAt (writeAt t x false) (x + 1) false) x true) (x + 1) true = t := by
    funext y
    by_cases hy1 : y = x + 1
    · subst hy1
      rw [writeAt_same]; exact h1.symm
    · by_cases hy0 : y = x
      · subst hy0
        rw [writeAt_other _ _ _ _ (by omega), writeAt_same]; exact h0.symm
      · rw [writeAt_other _ _ _ _ hy1, writeAt_other _ _ _ _ hy0,
            writeAt_other _ _ _ _ hy1, writeAt_other _ _ _ _ hy0]
  have hr4 : (writeAt (writeAt (writeAt (writeAt t x false) (x + 1) false) x true) (x + 1) true) (x + 2) = true := by
    rw [hrestore]; exact h2
  have s5 : step ⟨State.E, x + 2,
      writeAt (writeAt (writeAt (writeAt t x false) (x + 1) false) x true) (x + 1) true⟩ =
      some ⟨State.A, x + 3, t⟩ := by
    have hself : writeAt (writeAt (writeAt (writeAt (writeAt t x false) (x + 1) false) x true) (x + 1) true) (x + 2) true = t := by
      rw [writeAt_self _ _ hr4]; exact hrestore
    simp [step, instr, hr4, move, hself]
    omega
  refine ⟨by simp [stepN, s1, s2, s3, s4, s5], ?_⟩
  intro k d hk hkd hE hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl
  · have hdd : (⟨State.A, x, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hE; simp at hE
  · rw [show stepN 1 ⟨State.A, x, t⟩ = some ⟨State.B, x + 1, writeAt t x false⟩ from by
        simp [stepN, s1]] at hkd
    rw [← Option.some_inj.mp hkd] at hE; simp at hE
  · rw [show stepN 2 ⟨State.A, x, t⟩ =
        some ⟨State.C, x, writeAt (writeAt t x false) (x + 1) false⟩ from by
        simp [stepN, s1, s2]] at hkd
    rw [← Option.some_inj.mp hkd] at hE; simp at hE
  · rw [show stepN 3 ⟨State.A, x, t⟩ =
        some ⟨State.D, x + 1,
          writeAt (writeAt (writeAt t x false) (x + 1) false) x true⟩ from by
        simp [stepN, s1, s2, s3]] at hkd
    rw [← Option.some_inj.mp hkd] at hE; simp at hE
  · rw [show stepN 4 ⟨State.A, x, t⟩ =
        some ⟨State.E, x + 2,
          writeAt (writeAt (writeAt (writeAt t x false) (x + 1) false) x true) (x + 1) true⟩ from by
        simp [stepN, s1, s2, s3, s4]] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    simp only at hread
    rw [hrestore] at hread
    rw [hread] at h2
    exact absurd h2 (by simp)

/-- A gait run: `s` motifs cross `3s` ones in `5s` steps, tape literally
unchanged, every `E` configuration reading a `1`. -/
theorem gait_run :
    ∀ (s : Nat) (cfg : Config) (x : Int), cfg.state = State.A → cfg.head = x →
      (∀ i : Nat, i < 3 * s → cfg.tape (x + i) = true) →
      stepN (5 * s) cfg = some ⟨State.A, x + 3 * s, cfg.tape⟩ ∧
        ESafeSeg cfg (5 * s) := by
  intro s
  induction s with
  | zero =>
      intro cfg x hs hh _
      obtain ⟨st, hd, t⟩ := cfg
      simp only at hs hh
      subst hs
      subst hd
      refine ⟨?_, ?_⟩
      · rw [show x + 3 * ((0 : Nat) : Int) = x by omega]
        simp [stepN]
      · intro k d hk
        omega
  | succ s ih =>
      intro cfg x hs hh hones
      obtain ⟨st, hd, t⟩ := cfg
      simp only at hs hh hones
      subst hs
      subst hd
      have h0 : t x = true := by
        have := hones 0 (by omega)
        rw [show x + ((0 : Nat) : Int) = x by omega] at this
        exact this
      have h1 : t (x + 1) = true := by
        have := hones 1 (by omega)
        rw [show x + ((1 : Nat) : Int) = x + 1 by omega] at this
        exact this
      have h2 : t (x + 2) = true := by
        have := hones 2 (by omega)
        rw [show x + ((2 : Nat) : Int) = x + 2 by omega] at this
        exact this
      obtain ⟨hmot, hmots⟩ := gait_motif (cfg := ⟨State.A, x, t⟩) (x := x)
        rfl rfl h0 h1 h2
      obtain ⟨hrun, hruns⟩ := ih ⟨State.A, x + 3, t⟩ (x + 3) rfl rfl
        (fun i hi => by
          have := hones (i + 3) (by omega)
          show t (x + 3 + (i : Int)) = true
          rw [show x + 3 + (i : Int) = x + ((i + 3 : Nat) : Int) by omega]
          exact this)
      rw [show x + 3 + 3 * (s : Int) = x + 3 * ((s + 1 : Nat) : Int) by omega] at hrun
      refine ⟨?_, ?_⟩
      · rw [show 5 * (s + 1) = 5 + 5 * s by omega, stepN_add, hmot]
        exact hrun
      · rw [show 5 * (s + 1) = 5 + 5 * s by omega]
        exact esafe_compose hmot hmots hruns

/-!
## The inner pass — the workhorse of drift and renewal

From state `B` on the last `1` of a block whose left boundary is the
gap `g` (with `h = g + 3s + 2`), one pass zeroes the entry cell, sweeps
left to the gap, paints the gap, digs a new gap one cell to the right,
gaits back up, and repaints the entry cell — net effect
`g ↦ 1, g+1 ↦ 0`, head one cell further right, `8s + 5` steps, with no
`E`-probe of a `0` anywhere.
-/

theorem passA_step {cfg : Config} {g : Int} (s : Nat)
    (hs : cfg.state = State.B) (hh : cfg.head = g + 3 * s + 2)
    (hgap : cfg.tape g = false)
    (hones : ∀ i : Nat, i < 3 * s + 2 → cfg.tape (g + 1 + i) = true) :
    stepN (8 * s + 5) cfg =
      some ⟨State.B, g + 3 * s + 3,
        writeAt (writeAt cfg.tape g true) (g + 1) false⟩ ∧
      ESafeSeg cfg (8 * s + 5) := by
  obtain ⟨st, hd, t⟩ := cfg
  simp only at hs hh hgap hones ⊢
  subst hs
  subst hd
  have hread_h : t (g + 3 * s + 2) = true := by
    have := hones (3 * s + 1) (by omega)
    rw [show g + 1 + ((3 * s + 1 : Nat) : Int) = g + 3 * s + 2 by omega] at this
    exact this
  have hread_g1 : t (g + 1) = true := by
    have := hones 0 (by omega)
    rw [show g + 1 + ((0 : Nat) : Int) = g + 1 by omega] at this
    exact this
  have e1 : step ⟨State.B, g + 3 * s + 2, t⟩ =
      some ⟨State.C, g + 3 * s + 1, writeAt t (g + 3 * s + 2) false⟩ := by
    simp [step, instr, hread_h, move]
    omega
  have hsweep_ones : ∀ j : Nat, j ≤ 3 * s + 1 →
      ∀ i : Nat, i < j → (writeAt t (g + 3 * s + 2) false) (g + 3 * s + 1 - i) = true := by
    intro j hj i hi
    rw [writeAt_other _ _ _ _ (by omega)]
    have := hones (3 * s - i) (by omega)
    rw [show g + 1 + ((3 * s - i : Nat) : Int) = g + 3 * s + 1 - i by omega] at this
    exact this
  have hsC : stepN (3 * s + 1) ⟨State.C, g + 3 * s + 1, writeAt t (g + 3 * s + 2) false⟩ =
      some ⟨State.C, g, writeAt t (g + 3 * s + 2) false⟩ := by
    have h := sweep_C (3 * s + 1) ⟨State.C, g + 3 * s + 1, writeAt t (g + 3 * s + 2) false⟩
      rfl (fun i hi => hsweep_ones (3 * s + 1) (by omega) i hi)
    rw [show g + 3 * s + 1 - ((3 * s + 1 : Nat) : Int) = g by omega] at h
    exact h
  have hU1g : (writeAt t (g + 3 * s + 2) false) g = false := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact hgap
  have e2 : step ⟨State.C, g, writeAt t (g + 3 * s + 2) false⟩ =
      some ⟨State.D, g + 1, writeAt (writeAt t (g + 3 * s + 2) false) g true⟩ := by
    simp [step, instr, hU1g, move]
  have hU2g1 : (writeAt (writeAt t (g + 3 * s + 2) false) g true) (g + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact hread_g1
  have e3 : step ⟨State.D, g + 1, writeAt (writeAt t (g + 3 * s + 2) false) g true⟩ =
      some ⟨State.A, g + 2,
        writeAt (writeAt (writeAt t (g + 3 * s + 2) false) g true) (g + 1) false⟩ := by
    simp [step, instr, hU2g1, move]
    omega
  obtain ⟨hgrun, hgsafe⟩ := gait_run s
    ⟨State.A, g + 2,
      writeAt (writeAt (writeAt t (g + 3 * s + 2) false) g true) (g + 1) false⟩
    (g + 2) rfl rfl
    (fun i hi => by
      show (writeAt (writeAt (writeAt t (g + 3 * s + 2) false) g true) (g + 1) false)
        (g + 2 + (i : Int)) = true
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ (by omega)]
      have := hones (i + 1) (by omega)
      rw [show g + 1 + ((i + 1 : Nat) : Int) = g + 2 + i by omega] at this
      exact this)
  rw [show g + 2 + 3 * (s : Int) = g + 3 * s + 2 by omega] at hgrun
  have hU3h : (writeAt (writeAt (writeAt t (g + 3 * s + 2) false) g true) (g + 1) false)
      (g + 3 * s + 2) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hVeq : writeAt (writeAt (writeAt (writeAt t (g + 3 * s + 2) false) g true) (g + 1) false)
      (g + 3 * s + 2) true = writeAt (writeAt t g true) (g + 1) false := by
    funext y
    by_cases hy2 : y = g + 3 * s + 2
    · subst hy2
      rw [writeAt_same, writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ (by omega)]
      exact hread_h.symm
    · by_cases hy1 : y = g + 1
      · subst hy1
        rw [writeAt_other _ _ _ _ (by omega), writeAt_same, writeAt_same]
      · by_cases hy0 : y = g
        · subst hy0
          rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
              writeAt_same, writeAt_other _ _ _ _ (by omega), writeAt_same]
        · rw [writeAt_other _ _ _ _ hy2, writeAt_other _ _ _ _ hy1,
              writeAt_other _ _ _ _ hy0, writeAt_other _ _ _ _ hy2,
              writeAt_other _ _ _ _ hy1, writeAt_other _ _ _ _ hy0]
  have e4 : step ⟨State.A, g + 3 * s + 2,
      writeAt (writeAt (writeAt t (g + 3 * s + 2) false) g true) (g + 1) false⟩ =
      some ⟨State.B, g + 3 * s + 3, writeAt (writeAt t g true) (g + 1) false⟩ := by
    simp [step, instr, hU3h, move, hVeq]
    omega
  have a1 : stepN 1 ⟨State.B, g + 3 * s + 2, t⟩ =
      some ⟨State.C, g + 3 * s + 1, writeAt t (g + 3 * s + 2) false⟩ := by
    simp [stepN, e1]
  have a2 : stepN (1 + (3 * s + 1)) ⟨State.B, g + 3 * s + 2, t⟩ =
      some ⟨State.C, g, writeAt t (g + 3 * s + 2) false⟩ := by
    rw [stepN_add, a1]; exact hsC
  have b1 : stepN 1 ⟨State.C, g, writeAt t (g + 3 * s + 2) false⟩ =
      some ⟨State.D, g + 1, writeAt (writeAt t (g + 3 * s + 2) false) g true⟩ := by
    simp [stepN, e2]
  have a3 : stepN (1 + (3 * s + 1) + 1) ⟨State.B, g + 3 * s + 2, t⟩ =
      some ⟨State.D, g + 1, writeAt (writeAt t (g + 3 * s + 2) false) g true⟩ := by
    rw [stepN_add, a2]; exact b1
  have b2 : stepN 1 ⟨State.D, g + 1, writeAt (writeAt t (g + 3 * s + 2) false) g true⟩ =
      some ⟨State.A, g + 2,
        writeAt (writeAt (writeAt t (g + 3 * s + 2) false) g true) (g + 1) false⟩ := by
    simp [stepN, e3]
  have a4 : stepN (1 + (3 * s + 1) + 1 + 1) ⟨State.B, g + 3 * s + 2, t⟩ =
      some ⟨State.A, g + 2,
        writeAt (writeAt (writeAt t (g + 3 * s + 2) false) g true) (g + 1) false⟩ := by
    rw [stepN_add, a3]; exact b2
  have a5 : stepN (1 + (3 * s + 1) + 1 + 1 + 5 * s) ⟨State.B, g + 3 * s + 2, t⟩ =
      some ⟨State.A, g + 3 * s + 2,
        writeAt (writeAt (writeAt t (g + 3 * s + 2) false) g true) (g + 1) false⟩ := by
    rw [stepN_add, a4]; exact hgrun
  have b3 : stepN 1 ⟨State.A, g + 3 * s + 2,
      writeAt (writeAt (writeAt t (g + 3 * s + 2) false) g true) (g + 1) false⟩ =
      some ⟨State.B, g + 3 * s + 3, writeAt (writeAt t g true) (g + 1) false⟩ := by
    simp [stepN, e4]
  have a6 : stepN (1 + (3 * s + 1) + 1 + 1 + 5 * s + 1) ⟨State.B, g + 3 * s + 2, t⟩ =
      some ⟨State.B, g + 3 * s + 3, writeAt (writeAt t g true) (g + 1) false⟩ := by
    rw [stepN_add, a5]; exact b3
  refine ⟨?_, ?_⟩
  · rw [show 8 * s + 5 = 1 + (3 * s + 1) + 1 + 1 + 5 * s + 1 by omega]
    exact a6
  · rw [show 8 * s + 5 = 1 + ((3 * s + 1) + (1 + (1 + (5 * s + 1)))) by omega]
    refine esafe_compose a1 (esafe_of_noE ?_) (esafe_compose hsC (esafe_of_noE ?_)
      (esafe_compose b1 (esafe_of_noE ?_) (esafe_compose b2 (esafe_of_noE ?_)
        (esafe_compose hgrun hgsafe (esafe_of_noE ?_)))))
    · intro j d hj hjd
      have hj0 : j = 0 := by omega
      subst hj0
      have hdd : (⟨State.B, g + 3 * s + 2, t⟩ : Config) = d := by
        simpa [stepN] using hjd
      rw [← hdd]; simp
    · intro j d hj hjd
      have hpart := sweep_C j ⟨State.C, g + 3 * s + 1, writeAt t (g + 3 * s + 2) false⟩
        rfl (fun i hi => hsweep_ones j (by omega) i hi)
      rw [hpart] at hjd
      rw [← Option.some_inj.mp hjd]; simp
    · intro j d hj hjd
      have hj0 : j = 0 := by omega
      subst hj0
      have hdd : (⟨State.C, g, writeAt t (g + 3 * s + 2) false⟩ : Config) = d := by
        simpa [stepN] using hjd
      rw [← hdd]; simp
    · intro j d hj hjd
      have hj0 : j = 0 := by omega
      subst hj0
      have hdd : (⟨State.D, g + 1, writeAt (writeAt t (g + 3 * s + 2) false) g true⟩ : Config) = d := by
        simpa [stepN] using hjd
      rw [← hdd]; simp
    · intro j d hj hjd
      have hj0 : j = 0 := by omega
      subst hj0
      have hdd : (⟨State.A, g + 3 * s + 2,
          writeAt (writeAt (writeAt t (g + 3 * s + 2) false) g true) (g + 1) false⟩ : Config) = d := by
        simpa [stepN] using hjd
      rw [← hdd]; simp

/-!
## Collapse and micro — the bounded checkpoint episodes

Collapse absorbs a lone `1` and the gap into the block (`(a, 1) → (a+3)`
at the record level) in exactly five steps; micro extends a one-block
checkpoint by one cell in a single `A0` step.  Neither contains an
`E`-probe of a `0`.
-/

theorem collapse_step {cfg : Config} {g : Int}
    (hs : cfg.state = State.B) (hh : cfg.head = g + 2)
    (hgap : cfg.tape g = false) (hone : cfg.tape (g + 1) = true)
    (hfront : cfg.tape (g + 2) = false) :
    stepN 5 cfg =
      some ⟨State.A, g + 3, writeAt (writeAt cfg.tape (g + 2) true) g true⟩ ∧
      ESafeSeg cfg 5 := by
  obtain ⟨st, hd, t⟩ := cfg
  simp only at hs hh hgap hone hfront ⊢
  subst hs
  subst hd
  have c1 : step ⟨State.B, g + 2, t⟩ =
      some ⟨State.B, g + 1, writeAt t (g + 2) true⟩ := by
    simp [step, instr, hfront, move]
    omega
  have hr1 : (writeAt t (g + 2) true) (g + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact hone
  have c2 : step ⟨State.B, g + 1, writeAt t (g + 2) true⟩ =
      some ⟨State.C, g, writeAt (writeAt t (g + 2) true) (g + 1) false⟩ := by
    simp [step, instr, hr1, move]
  have hr2 : (writeAt (writeAt t (g + 2) true) (g + 1) false) g = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact hgap
  have c3 : step ⟨State.C, g, writeAt (writeAt t (g + 2) true) (g + 1) false⟩ =
      some ⟨State.D, g + 1,
        writeAt (writeAt (writeAt t (g + 2) true) (g + 1) false) g true⟩ := by
    simp [step, instr, hr2, move]
  have hr3 : (writeAt (writeAt (writeAt t (g + 2) true) (g + 1) false) g true) (g + 1) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_same]
  have c4 : step ⟨State.D, g + 1,
      writeAt (writeAt (writeAt t (g + 2) true) (g + 1) false) g true⟩ =
      some ⟨State.E, g + 2,
        writeAt (writeAt (writeAt (writeAt t (g + 2) true) (g + 1) false) g true) (g + 1) true⟩ := by
    simp [step, instr, hr3, move]
    omega
  have hrestore :
      writeAt (writeAt (writeAt (writeAt t (g + 2) true) (g + 1) false) g true) (g + 1) true
        = writeAt (writeAt t (g + 2) true) g true := by
    funext y
    by_cases hy1 : y = g + 1
    · subst hy1
      rw [writeAt_same, writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ (by omega)]
      exact hone.symm
    · by_cases hy0 : y = g
      · subst hy0
        rw [writeAt_other _ _ _ _ (by omega), writeAt_same, writeAt_same]
      · rw [writeAt_other _ _ _ _ hy1, writeAt_other _ _ _ _ hy0,
            writeAt_other _ _ _ _ hy1, writeAt_other _ _ _ _ hy0]
  have hr4 : (writeAt (writeAt (writeAt (writeAt t (g + 2) true) (g + 1) false) g true) (g + 1) true)
      (g + 2) = true := by
    rw [hrestore, writeAt_other _ _ _ _ (by omega), writeAt_same]
  have c5 : step ⟨State.E, g + 2,
      writeAt (writeAt (writeAt (writeAt t (g + 2) true) (g + 1) false) g true) (g + 1) true⟩ =
      some ⟨State.A, g + 3, writeAt (writeAt t (g + 2) true) g true⟩ := by
    have hself : writeAt
        (writeAt (writeAt (writeAt (writeAt t (g + 2) true) (g + 1) false) g true) (g + 1) true)
        (g + 2) true = writeAt (writeAt t (g + 2) true) g true := by
      rw [writeAt_self _ _ hr4]; exact hrestore
    simp [step, instr, hr4, move, hself]
    omega
  refine ⟨by simp [stepN, c1, c2, c3, c4, c5], ?_⟩
  intro k d hk hkd hE hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl
  · have hdd : (⟨State.B, g + 2, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hE; simp at hE
  · rw [show stepN 1 ⟨State.B, g + 2, t⟩ =
        some ⟨State.B, g + 1, writeAt t (g + 2) true⟩ from by
        simp [stepN, c1]] at hkd
    rw [← Option.some_inj.mp hkd] at hE; simp at hE
  · rw [show stepN 2 ⟨State.B, g + 2, t⟩ =
        some ⟨State.C, g, writeAt (writeAt t (g + 2) true) (g + 1) false⟩ from by
        simp [stepN, c1, c2]] at hkd
    rw [← Option.some_inj.mp hkd] at hE; simp at hE
  · rw [show stepN 3 ⟨State.B, g + 2, t⟩ =
        some ⟨State.D, g + 1,
          writeAt (writeAt (writeAt t (g + 2) true) (g + 1) false) g true⟩ from by
        simp [stepN, c1, c2, c3]] at hkd
    rw [← Option.some_inj.mp hkd] at hE; simp at hE
  · rw [show stepN 4 ⟨State.B, g + 2, t⟩ =
        some ⟨State.E, g + 2,
          writeAt (writeAt (writeAt (writeAt t (g + 2) true) (g + 1) false) g true) (g + 1) true⟩ from by
        simp [stepN, c1, c2, c3, c4]] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    simp only at hread
    rw [hr4] at hread
    exact absurd hread (by simp)

theorem micro_step {cfg : Config} {h : Int}
    (hs : cfg.state = State.A) (hh : cfg.head = h)
    (hread : cfg.tape h = false) :
    stepN 1 cfg = some ⟨State.B, h + 1, writeAt cfg.tape h true⟩ ∧
      ESafeSeg cfg 1 := by
  obtain ⟨st, hd, t⟩ := cfg
  simp only at hs hh hread ⊢
  subst hs
  subst hd
  refine ⟨by simp [stepN, step, instr, hread, move], ?_⟩
  intro k d hk hkd hE hread'
  have hk0 : k = 0 := by omega
  subst hk0
  have hdd : (⟨State.A, h, t⟩ : Config) = d := by simpa [stepN] using hkd
  rw [← hdd] at hE
  simp at hE

/-!
## The entry pass — where the machine risks its life

A drift cycle opens from the record frontier: paint the frontier `1`,
zero the cell below it, sweep to the gap, advance the gap, gait back up
— and here the gait's `E` lands exactly on the cell the entry zeroed.
The `E0` probe fires, and survival depends on the frontier `1` written
at the very first step: `F` reads it and turns back.  This is the *only*
`E`-probe of a `0` in the entire record dynamics, and it is safe by
construction.  `8n + 6` steps; net effect `f ↦ 1, g ↦ 1, g+1 ↦ 0`, head
to `f - 2`.
-/

theorem passE_step {cfg : Config} {g : Int} (n : Nat) (hn : 1 ≤ n)
    (hs : cfg.state = State.B) (hh : cfg.head = g + 3 * n + 2)
    (hgap : cfg.tape g = false)
    (hones : ∀ i : Nat, i < 3 * n + 1 → cfg.tape (g + 1 + i) = true)
    (hfront : cfg.tape (g + 3 * n + 2) = false) :
    stepN (8 * n + 6) cfg =
      some ⟨State.B, g + 3 * n,
        writeAt (writeAt (writeAt cfg.tape (g + 3 * n + 2) true) g true) (g + 1) false⟩ ∧
      ESafeSeg cfg (8 * n + 6) := by
  obtain ⟨st, hd, t⟩ := cfg
  simp only at hs hh hgap hones hfront ⊢
  subst hs
  subst hd
  have hr_f1 : t (g + 3 * n + 1) = true := by
    have := hones (3 * n) (by omega)
    rw [show g + 1 + ((3 * n : Nat) : Int) = g + 3 * n + 1 by omega] at this
    exact this
  have hr_g1 : t (g + 1) = true := by
    have := hones 0 (by omega)
    rw [show g + 1 + ((0 : Nat) : Int) = g + 1 by omega] at this
    exact this
  have hr_m1 : t (g + 3 * n - 1) = true := by
    have := hones (3 * n - 2) (by omega)
    rw [show g + 1 + ((3 * n - 2 : Nat) : Int) = g + 3 * n - 1 by omega] at this
    exact this
  have hr_m0 : t (g + 3 * n) = true := by
    have := hones (3 * n - 1) (by omega)
    rw [show g + 1 + ((3 * n - 1 : Nat) : Int) = g + 3 * n by omega] at this
    exact this
  have p1 : step ⟨State.B, g + 3 * n + 2, t⟩ =
      some ⟨State.B, g + 3 * n + 1, writeAt t (g + 3 * n + 2) true⟩ := by
    simp [step, instr, hfront, move]
    try omega
  have hW1r : (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact hr_f1
  have p2 : step ⟨State.B, g + 3 * n + 1, writeAt t (g + 3 * n + 2) true⟩ =
      some ⟨State.C, g + 3 * n, writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false⟩ := by
    simp [step, instr, hW1r, move]
    try omega
  have hsweep_ones : ∀ j : Nat, j ≤ 3 * n →
      ∀ i : Nat, i < j → (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) (g + 3 * n - i) = true := by
    intro j hj i hi
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    have := hones (3 * n - 1 - i) (by omega)
    rw [show g + 1 + ((3 * n - 1 - i : Nat) : Int) = g + 3 * n - i by omega] at this
    exact this
  have hsC : stepN (3 * n) ⟨State.C, g + 3 * n, writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false⟩ =
      some ⟨State.C, g, writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false⟩ := by
    have h := sweep_C (3 * n) ⟨State.C, g + 3 * n, writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false⟩
      rfl (fun i hi => hsweep_ones (3 * n) (by omega) i hi)
    rw [show g + 3 * n - ((3 * n : Nat) : Int) = g by omega] at h
    exact h
  have hW2g : (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact hgap
  have p3 : step ⟨State.C, g, writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false⟩ =
      some ⟨State.D, g + 1, writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true⟩ := by
    simp [step, instr, hW2g, move]
  have hW3g1 : (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega)]
    exact hr_g1
  have p4 : step ⟨State.D, g + 1, writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true⟩ =
      some ⟨State.A, g + 2, writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false⟩ := by
    simp [step, instr, hW3g1, move]
    try omega
  obtain ⟨hgrun, hgsafe⟩ := gait_run (n - 1) ⟨State.A, g + 2, writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false⟩ (g + 2) rfl rfl
    (fun i hi => by
      show (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 2 + (i : Int)) = true
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
      have := hones (i + 1) (by omega)
      rw [show g + 1 + ((i + 1 : Nat) : Int) = g + 2 + i by omega] at this
      exact this)
  rw [show g + 2 + 3 * ((n - 1 : Nat) : Int) = g + 3 * n - 1 by omega] at hgrun
  have hW4r : (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact hr_m1
  have p5 : step ⟨State.A, g + 3 * n - 1, writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false⟩ =
      some ⟨State.B, g + 3 * n, writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false⟩ := by
    simp [step, instr, hW4r, move]
    try omega
  have hW5r : (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega)]
    exact hr_m0
  have p6 : step ⟨State.B, g + 3 * n, writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false⟩ =
      some ⟨State.C, g + 3 * n - 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false⟩ := by
    simp [step, instr, hW5r, move]
    try omega
  have hW6r : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) = false := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have p7 : step ⟨State.C, g + 3 * n - 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false⟩ =
      some ⟨State.D, g + 3 * n, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true⟩ := by
    simp [step, instr, hW6r, move]
    try omega
  have hW7r : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true) (g + 3 * n) = false := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have p8 : step ⟨State.D, g + 3 * n, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true⟩ =
      some ⟨State.E, g + 3 * n + 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true) (g + 3 * n) true⟩ := by
    simp [step, instr, hW7r, move]
    try omega
  have hW8r : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true) (g + 3 * n) true) (g + 3 * n + 1) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hW8f : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true) (g + 3 * n) true) (g + 3 * n + 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have p9 : step ⟨State.E, g + 3 * n + 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true) (g + 3 * n) true⟩ =
      some ⟨State.F, g + 3 * n + 2, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true) (g + 3 * n) true⟩ := by
    have hself : writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true) (g + 3 * n) true) (g + 3 * n + 1) false = writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true) (g + 3 * n) true :=
      writeAt_self _ _ hW8r
    simp [step, instr, hW8r, move, hself]
    try omega
  have p10 : step ⟨State.F, g + 3 * n + 2, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true) (g + 3 * n) true⟩ =
      some ⟨State.B, g + 3 * n + 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true) (g + 3 * n) true⟩ := by
    have hself : writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true) (g + 3 * n) true) (g + 3 * n + 2) true = writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true) (g + 3 * n) true :=
      writeAt_self _ _ hW8f
    simp [step, instr, hW8f, move, hself]
    try omega
  have hVeq : writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true) (g + 3 * n) true) (g + 3 * n + 1) true = writeAt (writeAt (writeAt t (g + 3 * n + 2) true) g true) (g + 1) false := by
    funext y
    by_cases hy1 : y = g + 3 * n + 1
    · subst hy1
      rw [writeAt_same, writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
      exact hr_f1.symm
    · by_cases hy2 : y = g + 3 * n
      · subst hy2
        rw [writeAt_other _ _ _ _ (by omega), writeAt_same,
            writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
            writeAt_other _ _ _ _ (by omega)]
        exact hr_m0.symm
      · by_cases hy3 : y = g + 3 * n - 1
        · subst hy3
          rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
              writeAt_same, writeAt_other _ _ _ _ (by omega),
              writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
          exact hr_m1.symm
        · by_cases hy4 : y = g + 1
          · subst hy4
            rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
                writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
                writeAt_other _ _ _ _ (by omega), writeAt_same, writeAt_same]
          · by_cases hy5 : y = g
            · subst hy5
              rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
                  writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
                  writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
                  writeAt_same, writeAt_other _ _ _ _ (by omega), writeAt_same]
            · rw [writeAt_other _ _ _ _ hy1, writeAt_other _ _ _ _ hy2,
                  writeAt_other _ _ _ _ hy3, writeAt_other _ _ _ _ hy2,
                  writeAt_other _ _ _ _ hy3, writeAt_other _ _ _ _ hy4,
                  writeAt_other _ _ _ _ hy5, writeAt_other _ _ _ _ hy1,
                  writeAt_other _ _ _ _ hy4, writeAt_other _ _ _ _ hy5]
  have p11 : step ⟨State.B, g + 3 * n + 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true) (g + 3 * n) true⟩ =
      some ⟨State.B, g + 3 * n, writeAt (writeAt (writeAt t (g + 3 * n + 2) true) g true) (g + 1) false⟩ := by
    simp [step, instr, hW8r, move, hVeq]
    try omega
  have hmid : stepN 7 ⟨State.A, g + 3 * n - 1, writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false⟩ =
      some ⟨State.B, g + 3 * n, writeAt (writeAt (writeAt t (g + 3 * n + 2) true) g true) (g + 1) false⟩ := by
    simp [stepN, p5, p6, p7, p8, p9, p10, p11]
  have a1 : stepN 1 ⟨State.B, g + 3 * n + 2, t⟩ =
      some ⟨State.B, g + 3 * n + 1, writeAt t (g + 3 * n + 2) true⟩ := by
    simp [stepN, p1]
  have b1 : stepN 1 ⟨State.B, g + 3 * n + 1, writeAt t (g + 3 * n + 2) true⟩ =
      some ⟨State.C, g + 3 * n, writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false⟩ := by
    simp [stepN, p2]
  have a2 : stepN (1 + 1) ⟨State.B, g + 3 * n + 2, t⟩ =
      some ⟨State.C, g + 3 * n, writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false⟩ := by
    rw [stepN_add, a1]; exact b1
  have a3 : stepN (1 + 1 + 3 * n) ⟨State.B, g + 3 * n + 2, t⟩ =
      some ⟨State.C, g, writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false⟩ := by
    rw [stepN_add, a2]; exact hsC
  have b2 : stepN 1 ⟨State.C, g, writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false⟩ =
      some ⟨State.D, g + 1, writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true⟩ := by
    simp [stepN, p3]
  have a4 : stepN (1 + 1 + 3 * n + 1) ⟨State.B, g + 3 * n + 2, t⟩ =
      some ⟨State.D, g + 1, writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true⟩ := by
    rw [stepN_add, a3]; exact b2
  have b3 : stepN 1 ⟨State.D, g + 1, writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true⟩ =
      some ⟨State.A, g + 2, writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false⟩ := by
    simp [stepN, p4]
  have a5 : stepN (1 + 1 + 3 * n + 1 + 1) ⟨State.B, g + 3 * n + 2, t⟩ =
      some ⟨State.A, g + 2, writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false⟩ := by
    rw [stepN_add, a4]; exact b3
  have a6 : stepN (1 + 1 + 3 * n + 1 + 1 + 5 * (n - 1)) ⟨State.B, g + 3 * n + 2, t⟩ =
      some ⟨State.A, g + 3 * n - 1, writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false⟩ := by
    rw [stepN_add, a5]; exact hgrun
  have a7 : stepN (1 + 1 + 3 * n + 1 + 1 + 5 * (n - 1) + 7) ⟨State.B, g + 3 * n + 2, t⟩ =
      some ⟨State.B, g + 3 * n, writeAt (writeAt (writeAt t (g + 3 * n + 2) true) g true) (g + 1) false⟩ := by
    rw [stepN_add, a6]; exact hmid
  have hmidsafe : ESafeSeg ⟨State.A, g + 3 * n - 1, writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false⟩ 7 := by
    intro j d hj hjd hE hread
    have hcase : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hdd : (⟨State.A, g + 3 * n - 1, writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false⟩ : Config) = d := by
        simpa [stepN] using hjd
      rw [← hdd] at hE; simp at hE
    · rw [show stepN 1 ⟨State.A, g + 3 * n - 1, writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false⟩ =
          some ⟨State.B, g + 3 * n, writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false⟩ from by simp [stepN, p5]] at hjd
      rw [← Option.some_inj.mp hjd] at hE; simp at hE
    · rw [show stepN 2 ⟨State.A, g + 3 * n - 1, writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false⟩ =
          some ⟨State.C, g + 3 * n - 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false⟩ from by simp [stepN, p5, p6]] at hjd
      rw [← Option.some_inj.mp hjd] at hE; simp at hE
    · rw [show stepN 3 ⟨State.A, g + 3 * n - 1, writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false⟩ =
          some ⟨State.D, g + 3 * n, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true⟩ from by simp [stepN, p5, p6, p7]] at hjd
      rw [← Option.some_inj.mp hjd] at hE; simp at hE
    · rw [show stepN 4 ⟨State.A, g + 3 * n - 1, writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false⟩ =
          some ⟨State.E, g + 3 * n + 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true) (g + 3 * n) true⟩ from by simp [stepN, p5, p6, p7, p8]] at hjd
      rw [← Option.some_inj.mp hjd]
      simp only
      rw [show g + 3 * (n : Int) + 1 + 1 = g + 3 * (n : Int) + 2 by omega]
      exact hW8f
    · rw [show stepN 5 ⟨State.A, g + 3 * n - 1, writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false⟩ =
          some ⟨State.F, g + 3 * n + 2, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true) (g + 3 * n) true⟩ from by simp [stepN, p5, p6, p7, p8, p9]] at hjd
      rw [← Option.some_inj.mp hjd] at hE; simp at hE
    · rw [show stepN 6 ⟨State.A, g + 3 * n - 1, writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false⟩ =
          some ⟨State.B, g + 3 * n + 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true) (g + 1) false) (g + 3 * n - 1) false) (g + 3 * n) false) (g + 3 * n - 1) true) (g + 3 * n) true⟩ from by simp [stepN, p5, p6, p7, p8, p9, p10]] at hjd
      rw [← Option.some_inj.mp hjd] at hE; simp at hE
  refine ⟨?_, ?_⟩
  · rw [show 8 * n + 6 = 1 + 1 + 3 * n + 1 + 1 + 5 * (n - 1) + 7 by omega]
    exact a7
  · rw [show 8 * n + 6 = 1 + (1 + (3 * n + (1 + (1 + (5 * (n - 1) + 7))))) by omega]
    refine esafe_compose a1 (esafe_of_noE ?_) (esafe_compose b1 (esafe_of_noE ?_)
      (esafe_compose hsC (esafe_of_noE ?_) (esafe_compose b2 (esafe_of_noE ?_)
        (esafe_compose b3 (esafe_of_noE ?_)
          (esafe_compose hgrun hgsafe hmidsafe)))))
    · intro j d hj hjd
      have hj0 : j = 0 := by omega
      subst hj0
      have hdd : (⟨State.B, g + 3 * n + 2, t⟩ : Config) = d := by
        simpa [stepN] using hjd
      rw [← hdd]; simp
    · intro j d hj hjd
      have hj0 : j = 0 := by omega
      subst hj0
      have hdd : (⟨State.B, g + 3 * n + 1, writeAt t (g + 3 * n + 2) true⟩ : Config) = d := by
        simpa [stepN] using hjd
      rw [← hdd]; simp
    · intro j d hj hjd
      have hpart := sweep_C j ⟨State.C, g + 3 * n, writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false⟩
        rfl (fun i hi => hsweep_ones j (by omega) i hi)
      rw [hpart] at hjd
      rw [← Option.some_inj.mp hjd]; simp
    · intro j d hj hjd
      have hj0 : j = 0 := by omega
      subst hj0
      have hdd : (⟨State.C, g, writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false⟩ : Config) = d := by
        simpa [stepN] using hjd
      rw [← hdd]; simp
    · intro j d hj hjd
      have hj0 : j = 0 := by omega
      subst hj0
      have hdd : (⟨State.D, g + 1, writeAt (writeAt (writeAt t (g + 3 * n + 2) true) (g + 3 * n + 1) false) g true⟩ : Config) = d := by
        simpa [stepN] using hjd
      rw [← hdd]; simp

/-!
## Drift and the second renewal — pass composition

A full drift record transition `(a, b) → (a+4, b-3)` is the entry pass
followed by exactly three inner passes; with `b = 3n + 1` the step count
telescopes to `(8n+6) + 3(8(n-1)+5) = 32n - 3 = (32b - 41)/3`.  The gap
advances four cells, the frontier one.  The same theorem *is* the
`n ≡ 1 (mod 3)` renewal (`n → (4, n-3)`): a one-block checkpoint is a
two-block record whose left block is empty, anchored at the blank cell
left of the block, and the trajectory never reads left of the gap.

The `n ≡ 2 (mod 3)` renewal (`n → (2, n-1)`, `(16n+1)/3` steps) is one
`B0` frontier paint followed by two inner passes anchored one cell
further left — no entry pass, hence no `E`-probe at all.
-/

theorem drift_step {cfg : Config} {g : Int} (n : Nat) (hn : 1 ≤ n)
    (hs : cfg.state = State.B) (hh : cfg.head = g + 3 * n + 2)
    (hgap : cfg.tape g = false)
    (hones : ∀ i : Nat, i < 3 * n + 1 → cfg.tape (g + 1 + i) = true)
    (hfront : cfg.tape (g + 3 * n + 2) = false) :
    stepN (32 * n - 3) cfg =
      some ⟨State.B, g + 3 * n + 3,
        writeAt (writeAt (writeAt cfg.tape (g + 3 * n + 2) true) g true) (g + 4) false⟩ ∧
      ESafeSeg cfg (32 * n - 3) := by
  obtain ⟨st, hd, t⟩ := cfg
  simp only at hs hh hgap hones hfront ⊢
  subst hs
  subst hd
  have hr1 : t (g + 1) = true := by
    have := hones 0 (by omega)
    rw [show g + 1 + ((0 : Nat) : Int) = g + 1 by omega] at this
    exact this
  have hr2 : t (g + 2) = true := by
    have := hones 1 (by omega)
    rw [show g + 1 + ((1 : Nat) : Int) = g + 2 by omega] at this
    exact this
  have hr3 : t (g + 3) = true := by
    have := hones 2 (by omega)
    rw [show g + 1 + ((2 : Nat) : Int) = g + 3 by omega] at this
    exact this
  have hXg1 : (writeAt (writeAt t (g + 3 * n + 2) true) g true) (g + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact hr1
  have hXg2 : (writeAt (writeAt t (g + 3 * n + 2) true) g true) (g + 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact hr2
  have hXg3 : (writeAt (writeAt t (g + 3 * n + 2) true) g true) (g + 3) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact hr3
  obtain ⟨hrunE, hsafeE⟩ := passE_step (cfg := ⟨State.B, g + 3 * n + 2, t⟩)
    (g := g) n hn rfl rfl hgap hones hfront
  obtain ⟨hrun2, hsafe2⟩ := passA_step
    (cfg := ⟨State.B, g + 3 * n,
      writeAt (writeAt (writeAt t (g + 3 * n + 2) true) g true) (g + 1) false⟩)
    (g := g + 1) (n - 1) rfl
    (show g + 3 * (n : Int) = g + 1 + 3 * ((n - 1 : Nat) : Int) + 2 by omega)
    (writeAt_same _ _ _)
    (fun i hi => by
      show (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) g true) (g + 1) false)
        (g + 1 + 1 + (i : Int)) = true
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ (by omega)]
      have := hones (i + 1) (by omega)
      rw [show g + 1 + ((i + 1 : Nat) : Int) = g + 1 + 1 + i by omega] at this
      exact this)
  rw [show g + 1 + 3 * ((n - 1 : Nat) : Int) + 3 = g + 3 * n + 1 by omega,
      show g + 1 + 1 = g + 2 by omega] at hrun2
  have hcol1 : writeAt
      (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) g true) (g + 1) false)
      (g + 1) true = writeAt (writeAt t (g + 3 * n + 2) true) g true := by
    rw [writeAt_overwrite]
    exact writeAt_self _ _ hXg1
  rw [hcol1] at hrun2
  obtain ⟨hrun3, hsafe3⟩ := passA_step
    (cfg := ⟨State.B, g + 3 * n + 1,
      writeAt (writeAt (writeAt t (g + 3 * n + 2) true) g true) (g + 2) false⟩)
    (g := g + 2) (n - 1) rfl
    (show g + 3 * (n : Int) + 1 = g + 2 + 3 * ((n - 1 : Nat) : Int) + 2 by omega)
    (writeAt_same _ _ _)
    (fun i hi => by
      show (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) g true) (g + 2) false)
        (g + 2 + 1 + (i : Int)) = true
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ (by omega)]
      have := hones (i + 2) (by omega)
      rw [show g + 1 + ((i + 2 : Nat) : Int) = g + 2 + 1 + i by omega] at this
      exact this)
  rw [show g + 2 + 3 * ((n - 1 : Nat) : Int) + 3 = g + 3 * n + 2 by omega,
      show g + 2 + 1 = g + 3 by omega] at hrun3
  have hcol2 : writeAt
      (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) g true) (g + 2) false)
      (g + 2) true = writeAt (writeAt t (g + 3 * n + 2) true) g true := by
    rw [writeAt_overwrite]
    exact writeAt_self _ _ hXg2
  rw [hcol2] at hrun3
  obtain ⟨hrun4, hsafe4⟩ := passA_step
    (cfg := ⟨State.B, g + 3 * n + 2,
      writeAt (writeAt (writeAt t (g + 3 * n + 2) true) g true) (g + 3) false⟩)
    (g := g + 3) (n - 1) rfl
    (show g + 3 * (n : Int) + 2 = g + 3 + 3 * ((n - 1 : Nat) : Int) + 2 by omega)
    (writeAt_same _ _ _)
    (fun i hi => by
      show (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) g true) (g + 3) false)
        (g + 3 + 1 + (i : Int)) = true
      rw [writeAt_other _ _ _ _ (by omega)]
      by_cases hif : g + 3 + 1 + (i : Int) = g + 3 * n + 2
      · rw [hif, writeAt_other _ _ _ _ (by omega)]
        exact writeAt_same _ _ _
      · rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ hif]
        have := hones (i + 3) (by omega)
        rw [show g + 1 + ((i + 3 : Nat) : Int) = g + 3 + 1 + i by omega] at this
        exact this)
  rw [show g + 3 + 3 * ((n - 1 : Nat) : Int) + 3 = g + 3 * n + 3 by omega,
      show g + 3 + 1 = g + 4 by omega] at hrun4
  have hcol3 : writeAt
      (writeAt (writeAt (writeAt t (g + 3 * n + 2) true) g true) (g + 3) false)
      (g + 3) true = writeAt (writeAt t (g + 3 * n + 2) true) g true := by
    rw [writeAt_overwrite]
    exact writeAt_self _ _ hXg3
  rw [hcol3] at hrun4
  have A2 : stepN ((8 * n + 6) + (8 * (n - 1) + 5)) ⟨State.B, g + 3 * n + 2, t⟩ =
      some ⟨State.B, g + 3 * n + 1,
        writeAt (writeAt (writeAt t (g + 3 * n + 2) true) g true) (g + 2) false⟩ := by
    rw [stepN_add, hrunE]; exact hrun2
  have A3 : stepN ((8 * n + 6) + (8 * (n - 1) + 5) + (8 * (n - 1) + 5))
      ⟨State.B, g + 3 * n + 2, t⟩ =
      some ⟨State.B, g + 3 * n + 2,
        writeAt (writeAt (writeAt t (g + 3 * n + 2) true) g true) (g + 3) false⟩ := by
    rw [stepN_add, A2]; exact hrun3
  have A4 : stepN ((8 * n + 6) + (8 * (n - 1) + 5) + (8 * (n - 1) + 5) + (8 * (n - 1) + 5))
      ⟨State.B, g + 3 * n + 2, t⟩ =
      some ⟨State.B, g + 3 * n + 3,
        writeAt (writeAt (writeAt t (g + 3 * n + 2) true) g true) (g + 4) false⟩ := by
    rw [stepN_add, A3]; exact hrun4
  refine ⟨?_, ?_⟩
  · rw [show 32 * n - 3
        = (8 * n + 6) + (8 * (n - 1) + 5) + (8 * (n - 1) + 5) + (8 * (n - 1) + 5) by omega]
    exact A4
  · rw [show 32 * n - 3
        = (8 * n + 6) + ((8 * (n - 1) + 5) + ((8 * (n - 1) + 5) + (8 * (n - 1) + 5))) by omega]
    exact esafe_compose hrunE hsafeE (esafe_compose hrun2 hsafe2
      (esafe_compose hrun3 hsafe3 hsafe4))

theorem renew2_step {cfg : Config} {L : Int} (n : Nat)
    (hs : cfg.state = State.B) (hh : cfg.head = L + 3 * n + 2)
    (hblank : cfg.tape (L - 1) = false)
    (hones : ∀ i : Nat, i < 3 * n + 2 → cfg.tape (L + i) = true)
    (hfront : cfg.tape (L + 3 * n + 2) = false) :
    stepN (16 * n + 11) cfg =
      some ⟨State.B, L + 3 * n + 3,
        writeAt (writeAt (writeAt cfg.tape (L + 3 * n + 2) true) (L - 1) true) (L + 1) false⟩ ∧
      ESafeSeg cfg (16 * n + 11) := by
  obtain ⟨st, hd, t⟩ := cfg
  simp only at hs hh hblank hones hfront ⊢
  subst hs
  subst hd
  have hrL : t L = true := by
    have := hones 0 (by omega)
    rw [show L + ((0 : Nat) : Int) = L by omega] at this
    exact this
  have p1 : step ⟨State.B, L + 3 * n + 2, t⟩ =
      some ⟨State.B, L + 3 * n + 1, writeAt t (L + 3 * n + 2) true⟩ := by
    simp [step, instr, hfront, move]
    try omega
  have a1 : stepN 1 ⟨State.B, L + 3 * n + 2, t⟩ =
      some ⟨State.B, L + 3 * n + 1, writeAt t (L + 3 * n + 2) true⟩ := by
    simp [stepN, p1]
  obtain ⟨hrun1, hsafe1⟩ := passA_step
    (cfg := ⟨State.B, L + 3 * n + 1, writeAt t (L + 3 * n + 2) true⟩)
    (g := L - 1) n rfl
    (show L + 3 * (n : Int) + 1 = L - 1 + 3 * (n : Int) + 2 by omega)
    (by show (writeAt t (L + 3 * n + 2) true) (L - 1) = false
        rw [writeAt_other _ _ _ _ (by omega)]; exact hblank)
    (fun i hi => by
      show (writeAt t (L + 3 * n + 2) true) (L - 1 + 1 + (i : Int)) = true
      rw [writeAt_other _ _ _ _ (by omega)]
      have := hones i hi
      rw [show L + (i : Int) = L - 1 + 1 + i by omega] at this
      exact this)
  rw [show L - 1 + 3 * (n : Int) + 3 = L + 3 * n + 2 by omega,
      show L - 1 + 1 = L by omega] at hrun1
  obtain ⟨hrun2, hsafe2⟩ := passA_step
    (cfg := ⟨State.B, L + 3 * n + 2,
      writeAt (writeAt (writeAt t (L + 3 * n + 2) true) (L - 1) true) L false⟩)
    (g := L) n rfl
    (show L + 3 * (n : Int) + 2 = L + 3 * (n : Int) + 2 from rfl)
    (writeAt_same _ _ _)
    (fun i hi => by
      show (writeAt (writeAt (writeAt t (L + 3 * n + 2) true) (L - 1) true) L false)
        (L + 1 + (i : Int)) = true
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
      by_cases hif : L + 1 + (i : Int) = L + 3 * n + 2
      · rw [hif]
        exact writeAt_same _ _ _
      · rw [writeAt_other _ _ _ _ hif]
        have := hones (i + 1) (by omega)
        rw [show L + ((i + 1 : Nat) : Int) = L + 1 + i by omega] at this
        exact this)
  have hcol : writeAt
      (writeAt (writeAt (writeAt t (L + 3 * n + 2) true) (L - 1) true) L false)
      L true = writeAt (writeAt t (L + 3 * n + 2) true) (L - 1) true := by
    rw [writeAt_overwrite]
    refine writeAt_self _ _ ?_
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact hrL
  rw [hcol] at hrun2
  have A1 : stepN (1 + (8 * n + 5)) ⟨State.B, L + 3 * n + 2, t⟩ =
      some ⟨State.B, L + 3 * n + 2,
        writeAt (writeAt (writeAt t (L + 3 * n + 2) true) (L - 1) true) L false⟩ := by
    rw [stepN_add, a1]; exact hrun1
  have A2 : stepN (1 + (8 * n + 5) + (8 * n + 5)) ⟨State.B, L + 3 * n + 2, t⟩ =
      some ⟨State.B, L + 3 * n + 3,
        writeAt (writeAt (writeAt t (L + 3 * n + 2) true) (L - 1) true) (L + 1) false⟩ := by
    rw [stepN_add, A1]; exact hrun2
  refine ⟨?_, ?_⟩
  · rw [show 16 * n + 11 = 1 + (8 * n + 5) + (8 * n + 5) by omega]
    exact A2
  · rw [show 16 * n + 11 = 1 + ((8 * n + 5) + (8 * n + 5)) by omega]
    refine esafe_compose a1 (esafe_of_noE ?_) (esafe_compose hrun1 hsafe1 hsafe2)
    intro j d hj hjd
    have hj0 : j = 0 := by omega
    subst hj0
    have hdd : (⟨State.B, L + 3 * n + 2, t⟩ : Config) = d := by
      simpa [stepN] using hjd
    rw [← hdd]; simp

/-!
## The concrete startup anchor

Six raw steps take the blank tape to the first checkpoint: `1^3` with
the head on the fresh right frontier in state `A` — the abstract state
`oneA 3`, the seed of the checkpoint orbit.  The prefix is certified
safe by the executable checker.
-/

/-- Executable probe-safety check for one configuration. -/
def safeCfg (c : Config) : Bool :=
  match c.state with
  | State.E => c.tape c.head || c.tape (c.head + 1)
  | _ => true

def checkSafe : Nat → Config → Bool
  | 0, _ => true
  | k + 1, c =>
      safeCfg c &&
        (match step c with
         | none => true
         | some c' => checkSafe k c')

theorem safeCfg_spec {c : Config} (hE : c.state = State.E)
    (h : safeCfg c = true) (hr : c.tape c.head = false) :
    c.tape (c.head + 1) = true := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hE hr ⊢
  subst hE
  simp only [safeCfg] at h
  simp [hr] at h
  exact h

theorem esafe_of_checkSafe :
    ∀ (N : Nat) (c : Config), checkSafe N c = true → ESafeSeg c N := by
  intro N
  induction N with
  | zero =>
      intro c _ k d hk _ _ _
      exact absurd hk (by omega)
  | succ N ih =>
      intro c h k d hk hkd hE hread
      rw [show checkSafe (N + 1) c
            = (safeCfg c &&
                (match step c with
                 | none => true
                 | some c' => checkSafe N c')) from rfl] at h
      have h1 : safeCfg c = true := by
        cases hsc : safeCfg c
        · rw [hsc] at h; simp at h
        · rfl
      have h2 : (match step c with
                 | none => true
                 | some c' => checkSafe N c') = true := by
        rw [h1] at h; simpa using h
      cases k with
      | zero =>
          have hdd : c = d := by simpa [stepN] using hkd
          subst hdd
          exact safeCfg_spec hE h1 hread
      | succ j =>
          cases hstep : step c with
          | none =>
              rw [show stepN (j + 1) c = (step c).bind (stepN j) from rfl,
                  hstep] at hkd
              simp at hkd
          | some c1 =>
              rw [hstep] at h2
              rw [show stepN (j + 1) c = (step c).bind (stepN j) from rfl,
                  hstep] at hkd
              exact ih c1 h2 j d (by omega) hkd hE hread

/-- The concrete 6-step startup tape, in execution order:
`A0 B0 B1 C0 D0 E1` from the blank tape. -/
def startTape : Int → Bool :=
  writeAt (writeAt (writeAt (writeAt (writeAt (writeAt blankTape
    0 true) 1 true) 0 false) (-1 : Int) true) 0 true) 1 true

theorem startup_run :
    stepN 6 blankStart = some ⟨State.A, 2, startTape⟩ := by
  rfl

theorem startup_safe : ESafeSeg blankStart 6 := by
  apply esafe_of_checkSafe
  rfl

theorem startTape_blank_left : ∀ x : Int, x < -1 → startTape x = false := by
  intro x hx
  unfold startTape
  rw [writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
      writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
      writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega)]
  rfl

theorem startTape_blank_right : ∀ x : Int, 2 ≤ x → startTape x = false := by
  intro x hx
  unfold startTape
  rw [writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
      writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
      writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega)]
  rfl

/-!
## The abstract checkpoint orbit

The checkpoint state space has three shapes: two-block records
`1^a 0 1^b` (head at the right frontier, state `B`), post-collapse
one-block checkpoints `1^m` (state `A`), and post-micro one-block
checkpoints `1^n` (state `B`).  The timed abstract map of 2026-09-02:

* `twoBlock a 1 → oneA (a+3)` (collapse, 5 steps);
* `twoBlock a b → twoBlock (a+4) (b-3)` for `b ≡ 1 (mod 3)`, `b ≥ 4`
  (drift, `(32b-41)/3` steps);
* `oneA m → oneB (m+1)` (micro, 1 step);
* `oneB n → twoBlock 4 (n-3)` for `n ≡ 1 (mod 3)`, `n ≥ 4` (the drift
  law replayed with an empty left block);
* `oneB n → twoBlock 2 (n-1)` for `n ≡ 2 (mod 3)` (`(16n+1)/3` steps);
* `oneB n → divideStep n` for `n ≡ 0 (mod 3)`: the recursive divide
  branch — divide by 3 while the quotient stays `0 (mod 9)` (`d`
  divisions) reaching `m* ≡ 3` or `6 (mod 9)`; then `y = (m*-9)/3` or
  `(m*-3)/3` respectively and `x = n + 2 + d - y`.

Every branch except the divide has a proven episode theorem; the divide
branch (quadratic-time, recursive; validated on all four raw orbit
events to `n = 2,976`) enters the conjecture through `DivideFaithful`
below.  All other guard failures (`none`) mark exactly the value
patterns whose absence from the orbit is the Dvisetu checkpoint
conjecture.
-/

inductive CState where
  | twoBlock (a b : Nat)
  | oneA (m : Nat)
  | oneB (n : Nat)
deriving Repr, DecidableEq

/-- Iterated division for the divide renewal: divide by 3 while the
value is `0 (mod 9)`, returning the terminal value and the division
count.  Fuel-driven; called with fuel `n ≥ n`'s division depth. -/
def divCount : Nat → Nat → Nat × Nat
  | 0, m => (m, 0)
  | fuel + 1, m =>
      if m % 9 = 0 then
        let p := divCount fuel (m / 3)
        (p.1, p.2 + 1)
      else (m, 0)

/-- The divide renewal branch: `n ≡ 0 (mod 3)` splits into
`(n + 2 + d - y, y)` with `y` read off the terminal value of the
division cascade.  Guarded fail-closed. -/
def divideStep (n : Nat) : Option CState :=
  let m := (divCount n n).1
  let d := (divCount n n).2
  let y := if m % 9 = 3 then (m - 9) / 3 else (m - 3) / 3
  if 1 ≤ y ∧ y + 1 ≤ n + 2 + d then
    some (CState.twoBlock (n + 2 + d - y) y)
  else none

/-- The abstract checkpoint transition.  `none` marks exactly the value
patterns whose absence from the orbit is the checkpoint conjecture. -/
def cstep : CState → Option CState
  | CState.twoBlock a b =>
      if b = 1 then some (CState.oneA (a + 3))
      else if b % 3 = 1 then some (CState.twoBlock (a + 4) (b - 3))
      else none
  | CState.oneA m => some (CState.oneB (m + 1))
  | CState.oneB n =>
      if n % 3 = 1 then
        if 4 ≤ n then some (CState.twoBlock 4 (n - 3)) else none
      else if n % 3 = 2 then some (CState.twoBlock 2 (n - 1))
      else divideStep n

/-- The checkpoint orbit from the startup anchor `oneA 3` (the tape
`1^3` reached six raw steps from blank). -/
def corbit : Nat → Option CState
  | 0 => some (CState.oneA 3)
  | k + 1 => match corbit k with
      | none => none
      | some s => cstep s

/-- A configuration realizing an abstract checkpoint state: the tape
grammar pinning every cell from at most two integers and an anchor.
Two-block records anchor at the gap `g`; one-block checkpoints at the
left end `L`.  The head always sits on the fresh right frontier. -/
def Realizes : CState → Config → Prop
  | CState.twoBlock a b, cfg =>
      1 ≤ a ∧ 1 ≤ b ∧ cfg.state = State.B ∧
      ∃ g : Int,
        (∀ x : Int, x < g - a → cfg.tape x = false) ∧
        (∀ i : Nat, i < a → cfg.tape (g - a + i) = true) ∧
        cfg.tape g = false ∧
        (∀ i : Nat, i < b → cfg.tape (g + 1 + i) = true) ∧
        (∀ x : Int, g + b + 1 ≤ x → cfg.tape x = false) ∧
        cfg.head = g + b + 1
  | CState.oneA m, cfg =>
      1 ≤ m ∧ cfg.state = State.A ∧
      ∃ L : Int,
        (∀ x : Int, x < L → cfg.tape x = false) ∧
        (∀ i : Nat, i < m → cfg.tape (L + i) = true) ∧
        (∀ x : Int, L + m ≤ x → cfg.tape x = false) ∧
        cfg.head = L + m
  | CState.oneB n, cfg =>
      1 ≤ n ∧ cfg.state = State.B ∧
      ∃ L : Int,
        (∀ x : Int, x < L → cfg.tape x = false) ∧
        (∀ i : Nat, i < n → cfg.tape (L + i) = true) ∧
        (∀ x : Int, L + n ≤ x → cfg.tape x = false) ∧
        cfg.head = L + n

/-- The divide-episode assumption: whenever a one-block checkpoint
`1^n` with `n ≡ 0 (mod 3)` is realized on the tape and the abstract
divide branch produces an output, the raw machine reaches a
configuration realizing that output through a probe-safe segment.

This is the one episode of the timed abstract map without a proof in
this file: the divide renewal is quadratic-time with a recursive
sub-structure (its `dt` law is still empirical).  It is validated
fail-closed on every raw divide event observed (four events, to
`n = 2,976`, including a depth-2 cascade), and enters the final theorem
only through `SafeCheckpointOrbit`. -/
def DivideFaithful : Prop :=
  ∀ (n : Nat) (s : CState) (cfg : Config), n % 3 = 0 →
    divideStep n = some s → Realizes (CState.oneB n) cfg →
    ∃ (N : Nat) (cfg' : Config), 0 < N ∧ stepN N cfg = some cfg' ∧
      Realizes s cfg' ∧ ESafeSeg cfg N

/-- **The Dvisetu checkpoint conjecture**, in the exact form the machine
needs: (i) the abstract checkpoint orbit never dies — no renewal at
`n = 1`, no divide with an undersized terminal value, no two-block
record off the `b ≡ 1 (mod 3)` lattice — and (ii) the divide renewals
realize their abstract outputs on the tape (`DivideFaithful`).

Component (i) is a statement about a sequence of integer states with no
tape, no head, no machine.  Component (ii) is the assumed episode for
the one branch whose choreography is not yet certified.  Everything
else in this file converts the machine's fate into exactly this
sentence. -/
def SafeCheckpointOrbit : Prop :=
  (∀ k : Nat, corbit k ≠ none) ∧ DivideFaithful

theorem realizes_start : Realizes (CState.oneA 3) ⟨State.A, 2, startTape⟩ := by
  refine ⟨by omega, rfl, -1, ?_, ?_, ?_,
    by show (2 : Int) = -1 + ((3 : Nat) : Int); omega⟩
  · intro x hx
    exact startTape_blank_left x hx
  · intro i hi
    have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hcase with rfl | rfl | rfl
    · rw [show (-1 : Int) + ((0 : Nat) : Int) = -1 by omega]
      rfl
    · rw [show (-1 : Int) + ((1 : Nat) : Int) = 0 by omega]
      rfl
    · rw [show (-1 : Int) + ((2 : Nat) : Int) = 1 by omega]
      rfl
  · intro x hx
    refine startTape_blank_right x (by omega)

/-- The raw-side orbit invariant: the configuration realizes some live
state of the checkpoint orbit. -/
def OrbitInv (cfg : Config) : Prop :=
  ∃ (k : Nat) (s : CState), corbit k = some s ∧ Realizes s cfg

theorem orbitInv_start : OrbitInv ⟨State.A, 2, startTape⟩ :=
  ⟨0, CState.oneA 3, rfl, realizes_start⟩

theorem corbit_succ {k : Nat} {s : CState} (horb : corbit k = some s) :
    corbit (k + 1) = cstep s := by
  rw [show corbit (k + 1) = (match corbit k with
      | none => none
      | some s => cstep s) from rfl, horb]

/-!
## Transport — the abstract map, played on the tape

Each proven episode theorem is lifted through the `Realizes` grammar:
given a configuration realizing an abstract state whose guard holds, the
episode runs and the grammar conjuncts are re-established for the
successor state — cell-by-cell bookkeeping, no new ideas.
-/

/-- Transport for drift: `twoBlock a b → twoBlock (a+4) (b-3)` for
`b ≡ 1 (mod 3)`, `b ≥ 4`. -/
theorem transport_drift {cfg : Config} {a b : Nat}
    (hb3 : b % 3 = 1) (hb4 : 4 ≤ b)
    (h : Realizes (CState.twoBlock a b) cfg) :
    ∃ (N : Nat) (cfg' : Config), 0 < N ∧ stepN N cfg = some cfg' ∧
      Realizes (CState.twoBlock (a + 4) (b - 3)) cfg' ∧ ESafeSeg cfg N := by
  obtain ⟨ha, hb, hsB, g, hbl, haones, hgap, hbones, hbr, hhead⟩ := h
  obtain ⟨n, rfl⟩ : ∃ n : Nat, b = 3 * n + 1 := ⟨(b - 1) / 3, by omega⟩
  obtain ⟨hrun, hsafe⟩ := drift_step (cfg := cfg) (g := g) n (by omega) hsB
    (by rw [hhead]; omega)
    hgap
    (fun i hi => hbones i (by omega))
    (by have := hbr (g + 3 * n + 2) (by omega); exact this)
  refine ⟨32 * n - 3, _, by omega, hrun, ?_, hsafe⟩
  refine ⟨by omega, by omega, rfl, g + 4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    show (writeAt (writeAt (writeAt cfg.tape (g + 3 * n + 2) true) g true) (g + 4) false) x = false
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega)]
    exact hbl x (by omega)
  · intro i hi
    show (writeAt (writeAt (writeAt cfg.tape (g + 3 * n + 2) true) g true) (g + 4) false) (g + 4 - ((a + 4 : Nat) : Int) + (i : Int)) = true
    have hcase : i < a ∨ i = a ∨ i = a + 1 ∨ i = a + 2 ∨ i = a + 3 := by omega
    rcases hcase with hia | rfl | rfl | rfl | rfl
    · rw [show g + 4 - ((a + 4 : Nat) : Int) + (i : Int)
            = g - (a : Nat) + (i : Int) by omega]
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ (by omega)]
      exact haones i hia
    · rw [show g + 4 - ((i + 4 : Nat) : Int) + (i : Int) = g by omega]
      rw [writeAt_other _ _ _ _ (by omega)]
      exact writeAt_same _ _ _
    · rw [show g + 4 - ((a + 4 : Nat) : Int) + ((a + 1 : Nat) : Int) = g + 1 by omega]
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ (by omega)]
      have := hbones 0 (by omega)
      rwa [show g + 1 + ((0 : Nat) : Int) = g + 1 by omega] at this
    · rw [show g + 4 - ((a + 4 : Nat) : Int) + ((a + 2 : Nat) : Int) = g + 2 by omega]
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ (by omega)]
      have := hbones 1 (by omega)
      rwa [show g + 1 + ((1 : Nat) : Int) = g + 2 by omega] at this
    · rw [show g + 4 - ((a + 4 : Nat) : Int) + ((a + 3 : Nat) : Int) = g + 3 by omega]
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ (by omega)]
      have := hbones 2 (by omega)
      rwa [show g + 1 + ((2 : Nat) : Int) = g + 3 by omega] at this
  · show (writeAt (writeAt (writeAt cfg.tape (g + 3 * n + 2) true) g true) (g + 4) false) (g + 4) = false
    exact writeAt_same _ _ _
  · intro i hi
    show (writeAt (writeAt (writeAt cfg.tape (g + 3 * n + 2) true) g true) (g + 4) false) (g + 4 + 1 + i) = true
    by_cases hif : g + 4 + 1 + (i : Int) = g + 3 * (n : Int) + 2
    · rw [hif]
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
      exact writeAt_same _ _ _
    · rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ hif]
      have := hbones (i + 4) (by omega)
      rwa [show g + 1 + ((i + 4 : Nat) : Int) = g + 4 + 1 + i by omega] at this
  · intro x hx
    show (writeAt (writeAt (writeAt cfg.tape (g + 3 * n + 2) true) g true) (g + 4) false) x = false
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega)]
    exact hbr x (by omega)
  · show g + 3 * (n : Int) + 3 = g + 4 + ((3 * n + 1 - 3 : Nat) : Int) + 1
    omega

/-- Transport for collapse: `twoBlock a 1 → oneA (a+3)`. -/
theorem transport_collapse {cfg : Config} {a : Nat}
    (h : Realizes (CState.twoBlock a 1) cfg) :
    ∃ (N : Nat) (cfg' : Config), 0 < N ∧ stepN N cfg = some cfg' ∧
      Realizes (CState.oneA (a + 3)) cfg' ∧ ESafeSeg cfg N := by
  obtain ⟨ha, _hb, hsB, g, hbl, haones, hgap, hbones, hbr, hhead⟩ := h
  obtain ⟨hrun, hsafe⟩ := collapse_step (cfg := cfg) (g := g) hsB
    (by rw [hhead]; omega)
    hgap
    (by have := hbones 0 (by omega)
        rwa [show g + 1 + ((0 : Nat) : Int) = g + 1 by omega] at this)
    (hbr (g + 2) (by omega))
  refine ⟨5, _, by omega, hrun, ?_, hsafe⟩
  refine ⟨by omega, rfl, g - a, ?_, ?_, ?_, ?_⟩
  · intro x hx
    show (writeAt (writeAt cfg.tape (g + 2) true) g true) x = false
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact hbl x (by omega)
  · intro i hi
    show (writeAt (writeAt cfg.tape (g + 2) true) g true) (g - a + i) = true
    have hcase : i < a ∨ i = a ∨ i = a + 1 ∨ i = a + 2 := by omega
    rcases hcase with hia | rfl | rfl | rfl
    · rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
      exact haones i hia
    · rw [show g - (i : Int) + (i : Int) = g by omega]
      exact writeAt_same _ _ _
    · rw [show g - ((a : Nat) : Int) + ((a + 1 : Nat) : Int) = g + 1 by omega]
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
      have := hbones 0 (by omega)
      rwa [show g + 1 + ((0 : Nat) : Int) = g + 1 by omega] at this
    · rw [show g - ((a : Nat) : Int) + ((a + 2 : Nat) : Int) = g + 2 by omega]
      rw [writeAt_other _ _ _ _ (by omega)]
      exact writeAt_same _ _ _
  · intro x hx
    show (writeAt (writeAt cfg.tape (g + 2) true) g true) x = false
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact hbr x (by omega)
  · show g + 3 = g - (a : Nat) + ((a + 3 : Nat) : Int)
    omega

/-- Transport for micro: `oneA m → oneB (m+1)`. -/
theorem transport_micro {cfg : Config} {m : Nat}
    (h : Realizes (CState.oneA m) cfg) :
    ∃ (N : Nat) (cfg' : Config), 0 < N ∧ stepN N cfg = some cfg' ∧
      Realizes (CState.oneB (m + 1)) cfg' ∧ ESafeSeg cfg N := by
  obtain ⟨hm, hsA, L, hbl, hones, hbr, hhead⟩ := h
  obtain ⟨hrun, hsafe⟩ := micro_step (cfg := cfg) (h := L + m) hsA hhead
    (hbr (L + m) (by omega))
  refine ⟨1, _, by omega, hrun, ?_, hsafe⟩
  refine ⟨by omega, rfl, L, ?_, ?_, ?_, ?_⟩
  · intro x hx
    show (writeAt cfg.tape (L + m) true) x = false
    rw [writeAt_other _ _ _ _ (by omega)]
    exact hbl x hx
  · intro i hi
    show (writeAt cfg.tape (L + m) true) (L + i) = true
    by_cases him : i = m
    · subst him
      exact writeAt_same _ _ _
    · rw [writeAt_other _ _ _ _ (by omega)]
      exact hones i (by omega)
  · intro x hx
    show (writeAt cfg.tape (L + m) true) x = false
    rw [writeAt_other _ _ _ _ (by omega)]
    exact hbr x (by omega)
  · show L + (m : Int) + 1 = L + ((m + 1 : Nat) : Int)
    omega

/-- Transport for the `n ≡ 1 (mod 3)` renewal: `oneB n → twoBlock 4 (n-3)`
for `n ≥ 4` — the drift episode replayed with an empty left block. -/
theorem transport_renew1 {cfg : Config} {n : Nat}
    (hn3 : n % 3 = 1) (hn4 : 4 ≤ n)
    (h : Realizes (CState.oneB n) cfg) :
    ∃ (N : Nat) (cfg' : Config), 0 < N ∧ stepN N cfg = some cfg' ∧
      Realizes (CState.twoBlock 4 (n - 3)) cfg' ∧ ESafeSeg cfg N := by
  obtain ⟨hn1, hsB, L, hbl, hones, hbr, hhead⟩ := h
  obtain ⟨u, rfl⟩ : ∃ u : Nat, n = 3 * u + 1 := ⟨(n - 1) / 3, by omega⟩
  obtain ⟨hrun, hsafe⟩ := drift_step (cfg := cfg) (g := L - 1) u (by omega) hsB
    (by rw [hhead]; omega)
    (hbl (L - 1) (by omega))
    (fun i hi => by
      have := hones i (by omega)
      rwa [show L + (i : Int) = L - 1 + 1 + i by omega] at this)
    (by have := hbr (L - 1 + 3 * u + 2) (by omega); exact this)
  rw [show L - 1 + 3 * (u : Int) + 2 = L + 3 * u + 1 by omega,
      show L - 1 + 4 = L + 3 by omega,
      show L - 1 + 3 * (u : Int) + 3 = L + 3 * u + 2 by omega] at hrun
  refine ⟨32 * u - 3, _, by omega, hrun, ?_, hsafe⟩
  refine ⟨by omega, by omega, rfl, L + 3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    show (writeAt (writeAt (writeAt cfg.tape (L + 3 * u + 1) true) (L - 1) true) (L + 3) false) x = false
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega)]
    exact hbl x (by omega)
  · intro i hi
    show (writeAt (writeAt (writeAt cfg.tape (L + 3 * u + 1) true) (L - 1) true) (L + 3) false) (L + 3 - (4 : Nat) + i) = true
    have hcase : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hcase with rfl | rfl | rfl | rfl
    · rw [show L + 3 - ((4 : Nat) : Int) + ((0 : Nat) : Int) = L - 1 by omega]
      rw [writeAt_other _ _ _ _ (by omega)]
      exact writeAt_same _ _ _
    · rw [show L + 3 - ((4 : Nat) : Int) + ((1 : Nat) : Int) = L by omega]
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ (by omega)]
      have := hones 0 (by omega)
      rwa [show L + ((0 : Nat) : Int) = L by omega] at this
    · rw [show L + 3 - ((4 : Nat) : Int) + ((2 : Nat) : Int) = L + 1 by omega]
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ (by omega)]
      have := hones 1 (by omega)
      rwa [show L + ((1 : Nat) : Int) = L + 1 by omega] at this
    · rw [show L + 3 - ((4 : Nat) : Int) + ((3 : Nat) : Int) = L + 2 by omega]
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ (by omega)]
      have := hones 2 (by omega)
      rwa [show L + ((2 : Nat) : Int) = L + 2 by omega] at this
  · show (writeAt (writeAt (writeAt cfg.tape (L + 3 * u + 1) true) (L - 1) true) (L + 3) false) (L + 3) = false
    exact writeAt_same _ _ _
  · intro i hi
    show (writeAt (writeAt (writeAt cfg.tape (L + 3 * u + 1) true) (L - 1) true) (L + 3) false) (L + 3 + 1 + i) = true
    by_cases hif : L + 3 + 1 + (i : Int) = L + 3 * (u : Int) + 1
    · rw [hif]
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
      exact writeAt_same _ _ _
    · rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ hif]
      have := hones (i + 4) (by omega)
      rwa [show L + ((i + 4 : Nat) : Int) = L + 3 + 1 + i by omega] at this
  · intro x hx
    show (writeAt (writeAt (writeAt cfg.tape (L + 3 * u + 1) true) (L - 1) true) (L + 3) false) x = false
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega)]
    exact hbr x (by omega)
  · show L + 3 * (u : Int) + 2 = L + 3 + ((3 * u + 1 - 3 : Nat) : Int) + 1
    omega

/-- Transport for the `n ≡ 2 (mod 3)` renewal: `oneB n → twoBlock 2 (n-1)`. -/
theorem transport_renew2 {cfg : Config} {n : Nat}
    (hn3 : n % 3 = 2)
    (h : Realizes (CState.oneB n) cfg) :
    ∃ (N : Nat) (cfg' : Config), 0 < N ∧ stepN N cfg = some cfg' ∧
      Realizes (CState.twoBlock 2 (n - 1)) cfg' ∧ ESafeSeg cfg N := by
  obtain ⟨hn1, hsB, L, hbl, hones, hbr, hhead⟩ := h
  obtain ⟨u, rfl⟩ : ∃ u : Nat, n = 3 * u + 2 := ⟨(n - 2) / 3, by omega⟩
  obtain ⟨hrun, hsafe⟩ := renew2_step (cfg := cfg) (L := L) u hsB
    (by rw [hhead]; omega)
    (hbl (L - 1) (by omega))
    (fun i hi => hones i (by omega))
    (by have := hbr (L + 3 * u + 2) (by omega); exact this)
  refine ⟨16 * u + 11, _, by omega, hrun, ?_, hsafe⟩
  refine ⟨by omega, by omega, rfl, L + 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    show (writeAt (writeAt (writeAt cfg.tape (L + 3 * u + 2) true) (L - 1) true) (L + 1) false) x = false
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega)]
    exact hbl x (by omega)
  · intro i hi
    show (writeAt (writeAt (writeAt cfg.tape (L + 3 * u + 2) true) (L - 1) true) (L + 1) false) (L + 1 - (2 : Nat) + i) = true
    have hcase : i = 0 ∨ i = 1 := by omega
    rcases hcase with rfl | rfl
    · rw [show L + 1 - ((2 : Nat) : Int) + ((0 : Nat) : Int) = L - 1 by omega]
      rw [writeAt_other _ _ _ _ (by omega)]
      exact writeAt_same _ _ _
    · rw [show L + 1 - ((2 : Nat) : Int) + ((1 : Nat) : Int) = L by omega]
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ (by omega)]
      have := hones 0 (by omega)
      rwa [show L + ((0 : Nat) : Int) = L by omega] at this
  · show (writeAt (writeAt (writeAt cfg.tape (L + 3 * u + 2) true) (L - 1) true) (L + 1) false) (L + 1) = false
    exact writeAt_same _ _ _
  · intro i hi
    show (writeAt (writeAt (writeAt cfg.tape (L + 3 * u + 2) true) (L - 1) true) (L + 1) false) (L + 1 + 1 + i) = true
    by_cases hif : L + 1 + 1 + (i : Int) = L + 3 * (u : Int) + 2
    · rw [hif]
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
      exact writeAt_same _ _ _
    · rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
          writeAt_other _ _ _ _ hif]
      have := hones (i + 2) (by omega)
      rwa [show L + ((i + 2 : Nat) : Int) = L + 1 + 1 + i by omega] at this
  · intro x hx
    show (writeAt (writeAt (writeAt cfg.tape (L + 3 * u + 2) true) (L - 1) true) (L + 1) false) x = false
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega)]
    exact hbr x (by omega)
  · show L + 3 * (u : Int) + 3 = L + 1 + ((3 * u + 2 - 1 : Nat) : Int) + 1
    omega

/-!
## The keystone

Segment induction over the checkpoint orbit: from any configuration
realizing a live orbit state, some positive number of raw steps runs
probe-safely to a configuration realizing the next orbit state.  With
the 6-step startup prefix, `EProbeSafe blankStart` follows, and the halt
corridor closes.
-/

theorem orbit_segment (hso : SafeCheckpointOrbit) (cfg : Config)
    (hinv : OrbitInv cfg) :
    ∃ k : Nat, 0 < k ∧ ∃ cfg' : Config, stepN k cfg = some cfg' ∧
      OrbitInv cfg' ∧ ESafeSeg cfg k := by
  obtain ⟨k, s, horb, hreal⟩ := hinv
  have hlive : corbit (k + 1) ≠ none := hso.1 (k + 1)
  rw [corbit_succ horb] at hlive
  cases s with
  | twoBlock a b =>
      by_cases hb1 : b = 1
      · subst hb1
        obtain ⟨N, cfg', hN, hrun, hreal', hsafe⟩ := transport_collapse hreal
        exact ⟨N, hN, cfg', hrun,
          ⟨k + 1, CState.oneA (a + 3),
            by rw [corbit_succ horb]; simp [cstep], hreal'⟩, hsafe⟩
      · by_cases hb3 : b % 3 = 1
        · have hb1le : 1 ≤ b := hreal.2.1
          have hb4 : 4 ≤ b := by omega
          obtain ⟨N, cfg', hN, hrun, hreal', hsafe⟩ := transport_drift hb3 hb4 hreal
          exact ⟨N, hN, cfg', hrun,
            ⟨k + 1, CState.twoBlock (a + 4) (b - 3),
              by rw [corbit_succ horb]; simp [cstep, hb1, hb3], hreal'⟩, hsafe⟩
        · exact absurd (by simp [cstep, hb1, hb3]) hlive
  | oneA m =>
      obtain ⟨N, cfg', hN, hrun, hreal', hsafe⟩ := transport_micro hreal
      exact ⟨N, hN, cfg', hrun,
        ⟨k + 1, CState.oneB (m + 1),
          by rw [corbit_succ horb]; simp [cstep], hreal'⟩, hsafe⟩
  | oneB n =>
      by_cases hn1 : n % 3 = 1
      · by_cases hn4 : 4 ≤ n
        · obtain ⟨N, cfg', hN, hrun, hreal', hsafe⟩ := transport_renew1 hn1 hn4 hreal
          exact ⟨N, hN, cfg', hrun,
            ⟨k + 1, CState.twoBlock 4 (n - 3),
              by rw [corbit_succ horb]; simp [cstep, hn1, hn4], hreal'⟩, hsafe⟩
        · exact absurd (by simp [cstep, hn1, hn4]) hlive
      · by_cases hn2 : n % 3 = 2
        · obtain ⟨N, cfg', hN, hrun, hreal', hsafe⟩ := transport_renew2 hn2 hreal
          exact ⟨N, hN, cfg', hrun,
            ⟨k + 1, CState.twoBlock 2 (n - 1),
              by rw [corbit_succ horb]; simp [cstep, hn2], hreal'⟩, hsafe⟩
        · have hn0 : n % 3 = 0 := by omega
          cases hdiv : divideStep n with
          | none =>
              refine absurd ?_ hlive
              simp [cstep, hn1, hn2]
              exact hdiv
          | some s' =>
              obtain ⟨N, cfg', hN, hrun, hreal', hsafe⟩ :=
                hso.2 n s' cfg hn0 hdiv hreal
              exact ⟨N, hN, cfg', hrun,
                ⟨k + 1, s',
                  by rw [corbit_succ horb]; simp [cstep, hn1, hn2]; exact hdiv,
                  hreal'⟩, hsafe⟩

/-- **The conditional closure**: the Dvisetu checkpoint conjecture
implies the machine never halts from blank.

Informally: the six-step startup lands on `oneA 3`; from every realized
orbit state the proven (or, for the divide branch, assumed) episode runs
probe-safely to the next; segment induction turns finitely many episode
theorems into `EProbeSafe blankStart`; and the halt corridor `E0 → F0`
is closed forever. -/
theorem safeDvisetuOrbit_nonhalting (hso : SafeCheckpointOrbit) :
    ¬ RawHalts blankStart := by
  apply blank_nonhalting_of_e_probe_safe
  refine eprobe_safe_prefix startup_run startup_safe ?_
  exact eprobe_safe_of_segments orbitInv_start
    (fun c hinv => orbit_segment hso c hinv)

#print axioms safeDvisetuOrbit_nonhalting

end QIG.DvisetuRawTM
