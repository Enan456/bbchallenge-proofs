import Lean.Elab.Tactic.Omega

/-!
# Dossier-3 raw semantics and halt localization

Bare-Lean model of the BB(6) holdout
`1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE` (stage757: exact orbit spec).

* halt in one step exactly at the undefined `C0`;
* state `C` is entered only via `B0` (write 1, move left);
* any raw halt passes through a reachable `B`-probe of a `00` pattern
  (the probed 0's LEFT neighbour is also 0);
* `BProbeSafe blankStart → ¬ RawHalts blankStart` — the contract the
  machine's (future) certified orbit must discharge.
-/

namespace QIG.Dossier3RawTM

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

/-- The dossier-3 transition table.  `none` at `C0` is the halt. -/
def instr : State → Bool → Option Instr
  | State.A, false => some ⟨State.B, true, Dir.R⟩
  | State.A, true => some ⟨State.B, true, Dir.R⟩
  | State.B, false => some ⟨State.C, true, Dir.L⟩
  | State.B, true => some ⟨State.E, false, Dir.R⟩
  | State.C, false => none
  | State.C, true => some ⟨State.D, true, Dir.L⟩
  | State.D, false => some ⟨State.A, false, Dir.R⟩
  | State.D, true => some ⟨State.B, true, Dir.L⟩
  | State.E, false => some ⟨State.A, true, Dir.R⟩
  | State.E, true => some ⟨State.F, true, Dir.L⟩
  | State.F, false => some ⟨State.E, false, Dir.L⟩
  | State.F, true => some ⟨State.E, true, Dir.L⟩

def move : Int → Dir → Int
  | h, Dir.L => h - 1
  | h, Dir.R => h + 1

def writeAt (tape : Int → Bool) (pos : Int) (value : Bool) : Int → Bool :=
  fun x => if x = pos then value else tape x

theorem writeAt_other (tape : Int → Bool) (pos x : Int) (value : Bool)
    (h : x ≠ pos) : writeAt tape pos value x = tape x := by
  simp [writeAt, h]

structure Config where
  state : State
  head : Int
  tape : Int → Bool

def step (c : Config) : Option Config := do
  let ins ← instr c.state (c.tape c.head)
  some {
    state := ins.next
    head := move c.head ins.dir
    tape := writeAt c.tape c.head ins.write
  }

def stepN : Nat → Config → Option Config
  | 0, c => some c
  | n + 1, c => do
      let c' ← step c
      stepN n c'

theorem step_eq_none_iff (c : Config) :
    step c = none ↔ c.state = State.C ∧ c.tape c.head = false := by
  cases hs : c.state <;> cases ht : c.tape c.head <;>
    simp [step, instr, hs, ht]

/-- Informally: halting is the existence of a finite step count after
which the iterated dynamics return `none` — the one global property this
file localizes into a two-cell tape pattern. -/
def RawHalts (c : Config) : Prop := ∃ n : Nat, stepN n c = none

def Reaches (c d : Config) : Prop := ∃ n : Nat, stepN n c = some d

def blankTape : Int → Bool := fun _ => false

def blankStart : Config where
  state := State.A
  head := 0
  tape := blankTape

/-- State `C` is entered only by `B` reading `0` (`B0 = 1LC`). -/
theorem into_C_only_from_B0 {c c' : Config} (h : step c = some c')
    (hE : c'.state = State.C) :
    c.state = State.B ∧ c.tape c.head = false ∧
      c'.head = c.head - 1 ∧ c'.tape = writeAt c.tape c.head true := by
  cases hs : c.state <;> cases ht : c.tape c.head <;>
    simp [step, instr, hs, ht] at h
  all_goals
    first
      | exact ⟨rfl, rfl, by rw [← h]; simp [move], by rw [← h]⟩
      | (rw [← h] at hE; simp at hE)

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

/-- Informally: the two-cell death pattern for this machine — a halting
run must first stand in `B` on a `0` whose left neighbour is also
`0`.  Same argument as its elder siblings: rewind to the last living
configuration, enter through the unique turnstile, observe the fatal cell
was not written by the entering step.

Halt localization: any raw halt from a non-`C` start forces a reachable
`B` reading a `0` whose LEFT neighbour is also `0`. -/
theorem halt_requires_b_probe_00 {c : Config} (hne : c.state ≠ State.C)
    (hh : RawHalts c) :
    ∃ d : Config, Reaches c d ∧ d.state = State.B ∧
      d.tape d.head = false ∧ d.tape (d.head - 1) = false := by
  obtain ⟨n, hn⟩ := hh
  obtain ⟨k, _, d0, hd0, hstop⟩ := stepN_none_last n c hn
  have hE := (step_eq_none_iff d0).mp hstop
  cases k with
  | zero =>
      have hcd : c = d0 := by simpa [stepN] using hd0
      exact absurd (hcd ▸ hE.1) hne
  | succ k' =>
      obtain ⟨e, he, hstepe⟩ := stepN_some_pred k' c d0 hd0
      obtain ⟨hB, h0, hhead, htape⟩ := into_C_only_from_B0 hstepe hE.1
      refine ⟨e, ⟨k', he⟩, hB, h0, ?_⟩
      have hread : d0.tape d0.head = false := hE.2
      rw [htape, hhead] at hread
      rwa [writeAt_other e.tape e.head (e.head - 1) true (by omega)] at hread

/-- The B-probe-safety contract: every `0` that `B` reads has a `1` to its
left. -/
def BProbeSafe (c : Config) : Prop :=
  ∀ d : Config, Reaches c d → d.state = State.B → d.tape d.head = false →
    d.tape (d.head - 1) = true

theorem nonhalting_of_b_probe_safe {c : Config} (hne : c.state ≠ State.C)
    (hsafe : BProbeSafe c) : ¬ RawHalts c := by
  intro hh
  obtain ⟨d, hreach, hB, h0, h00⟩ := halt_requires_b_probe_00 hne hh
  have h1 := hsafe d hreach hB h0
  rw [h1] at h00
  exact Bool.noConfusion h00

theorem blank_nonhalting_of_b_probe_safe
    (hsafe : BProbeSafe blankStart) : ¬ RawHalts blankStart := by
  have hne : blankStart.state ≠ State.C := by
    simp [blankStart]
  exact nonhalting_of_b_probe_safe hne hsafe


/-!
## Orbit certification, layer 1: segment algebra, keystone, decider, atoms

The certified foundation beneath a future rule-by-rule orbit proof —
mirrors of the Antihydra development's machinery, instantiated for this
machine's probe shape.  Informally: everything here is machine-checked
scaffolding; the remaining climb is the rule trajectories of the stage757
spec, which will slot into `bsafe_compose` and the keystone exactly as
Antihydra's rules did.
-/

theorem writeAt_same (tape : Int → Bool) (pos : Int) (value : Bool) :
    writeAt tape pos value pos = value := by
  simp [writeAt]

theorem writeAt_self (tape : Int → Bool) (pos : Int) {value : Bool}
    (h : tape pos = value) : writeAt tape pos value = tape := by
  funext x
  by_cases hx : x = pos
  · subst hx; simp [writeAt, h]
  · simp [writeAt, hx]

/-- Sequential-composition law for `stepN`. -/
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

/-- Informally: the machine's tape-preserving gait — `E` on a `1`
rewrites `1` over `1` and hands off to `F`, leaving the tape function
*literally equal*.  These two atoms are what block-crossing sweeps will be
built from. -/
theorem step_E_on_one {c : Config} (hs : c.state = State.E)
    (ht : c.tape c.head = true) :
    step c = some ⟨State.F, c.head - 1, c.tape⟩ := by
  have hw := writeAt_self c.tape c.head ht
  simp [step, instr, hs, ht, move, hw]

theorem step_F_on_one {c : Config} (hs : c.state = State.F)
    (ht : c.tape c.head = true) :
    step c = some ⟨State.E, c.head - 1, c.tape⟩ := by
  have hw := writeAt_self c.tape c.head ht
  simp [step, instr, hs, ht, move, hw]

/-- Conditional B-probe safety over the first `N` steps of a run. -/
def BSafeSeg (c : Config) (N : Nat) : Prop :=
  ∀ k d, k < N → stepN k c = some d → d.state = State.B →
    d.tape d.head = false → d.tape (d.head - 1) = true

theorem bsafe_compose {c c' : Config} {m n : Nat}
    (hm : stepN m c = some c') (h1 : BSafeSeg c m) (h2 : BSafeSeg c' n) :
    BSafeSeg c (m + n) := by
  intro k d hk hkd hP hread
  by_cases hkm : k < m
  · exact h1 k d hkm hkd hP hread
  · have hkeq : k = m + (k - m) := by omega
    rw [hkeq, stepN_add, hm] at hkd
    exact h2 (k - m) d (by omega) hkd hP hread

/-- A segment in which every `B` configuration reads a `1` is safe. -/
theorem bsafe_of_strong {c : Config} {N : Nat}
    (h : ∀ k d, k < N → stepN k c = some d → d.state = State.B →
      d.tape d.head = true) : BSafeSeg c N := by
  intro k d hk hkd hP hread
  rw [h k d hk hkd hP] at hread
  exact absurd hread (by simp)

/-- A segment with no `B` configuration at all is safe. -/
theorem bsafe_of_noB {c : Config} {N : Nat}
    (h : ∀ k d, k < N → stepN k c = some d → d.state ≠ State.B) :
    BSafeSeg c N := by
  intro k d hk hkd hP _
  exact absurd hP (h k d hk hkd)

/-- The segment-induction keystone.  Informally: safety in pieces is
safety forever — an invariant maintained by positive safe segments gives
`BProbeSafe` for the whole infinite run, by strong induction on how many
segments precede any given moment. -/
theorem bprobe_safe_of_segments {Inv : Config → Prop} {c0 : Config}
    (h0 : Inv c0)
    (hseg : ∀ c, Inv c → ∃ k, 0 < k ∧ ∃ c', stepN k c = some c' ∧
      Inv c' ∧ BSafeSeg c k) :
    BProbeSafe c0 := by
  have main : ∀ (N n : Nat) (c : Config), n ≤ N → Inv c →
      ∀ d, stepN n c = some d → d.state = State.B →
        d.tape d.head = false → d.tape (d.head - 1) = true := by
    intro N
    induction N with
    | zero =>
        intro n c hn hInv d hd hP hread
        obtain ⟨k, hk, c', _hs, _hInv', hsafe⟩ := hseg c hInv
        exact hsafe n d (by omega) hd hP hread
    | succ N ihN =>
        intro n c hn hInv d hd hP hread
        obtain ⟨k, hk, c', hs, hInv', hsafe⟩ := hseg c hInv
        by_cases hlt : n < k
        · exact hsafe n d hlt hd hP hread
        · have hneq : n = k + (n - k) := by omega
          rw [hneq, stepN_add, hs] at hd
          exact ihN (n - k) c' (by omega) hInv' d hd hP hread
  intro d hreach hP hread
  obtain ⟨n, hn⟩ := hreach
  exact main n n c0 (Nat.le_refl n) h0 d hn hP hread

/-- Prefix safety plus tail safety gives whole-run safety. -/
theorem bprobe_safe_prefix {c d : Config} {M : Nat}
    (hM : stepN M c = some d)
    (hpre : BSafeSeg c M) (hpost : BProbeSafe d) : BProbeSafe c := by
  intro e hreach hP hread
  obtain ⟨n, hn⟩ := hreach
  by_cases h : n < M
  · exact hpre n e h hn hP hread
  · have hsplit : n = M + (n - M) := by omega
    rw [hsplit, stepN_add, hM] at hn
    exact hpost e ⟨n - M, hn⟩ hP hread

/-- Executable per-configuration safety check.  Informally: the boolean
twin of the probe contract, so finite prefixes (startups, rule boundary
windows) can be certified by `rfl` instead of hand analysis. -/
def safeCfg (c : Config) : Bool :=
  match c.state with
  | State.B => c.tape c.head || c.tape (c.head - 1)
  | _ => true

def checkSafe : Nat → Config → Bool
  | 0, _ => true
  | k + 1, c =>
      safeCfg c &&
        (match step c with
         | none => true
         | some c' => checkSafe k c')

theorem safeCfg_spec {c : Config} (hB : c.state = State.B)
    (h : safeCfg c = true) (hr : c.tape c.head = false) :
    c.tape (c.head - 1) = true := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hB hr ⊢
  subst hB
  simp only [safeCfg] at h
  simp [hr] at h
  exact h

theorem bsafe_of_checkSafe :
    ∀ (N : Nat) (c : Config), checkSafe N c = true → BSafeSeg c N := by
  intro N
  induction N with
  | zero =>
      intro c _ k d hk _ _ _
      exact absurd hk (by omega)
  | succ N ih =>
      intro c h k d hk hkd hB hread
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
          exact safeCfg_spec hB h1 hread
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
              exact ih c1 h2 j d (by omega) hkd hB hread

end QIG.Dossier3RawTM

#print axioms QIG.Dossier3RawTM.halt_requires_b_probe_00
#print axioms QIG.Dossier3RawTM.blank_nonhalting_of_b_probe_safe
#print axioms QIG.Dossier3RawTM.bprobe_safe_of_segments
#print axioms QIG.Dossier3RawTM.bsafe_of_checkSafe
#print axioms QIG.Dossier3RawTM.step_E_on_one
