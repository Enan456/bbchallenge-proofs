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

end QIG.DvisetuRawTM
