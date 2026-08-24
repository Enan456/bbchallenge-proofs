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


/-- **The dominant spawn rule**, certified (stage757 spec key
`(3, 4, sig)`, support ~150): a constant **7-step** frontier event.  From
a record head on the fresh frontier with the adjacent block at least three
deep, exactly seven raw steps split off a fresh 2-block:  the net tape
change is two cells (`p + 2 ↦ 0`, `p ↦ 1`), realizing the abstract map
`(x, y, z) → (x, y, z−2, 2)` at cost 7 — independent of every block size.

Informally: the machine's cheapest and commonest move — a purely local
stitch at the frontier, no sweeps required.  The single `B`-moment inside
reads a `1`, so the rule is probe-free and its safety certificate is
immediate. -/
theorem spawn_step {cfg : Config} {p : Int}
    (hs : cfg.state = State.E) (hh : cfg.head = p)
    (tf : cfg.tape p = false) (t1 : cfg.tape (p + 1) = true)
    (t2 : cfg.tape (p + 2) = true) (t3 : cfg.tape (p + 3) = true) :
    stepN 7 cfg = some ⟨State.E, p - 1,
        writeAt (writeAt cfg.tape p true) (p + 2) false⟩ ∧
      BSafeSeg cfg 7 := by
  obtain ⟨s, hd, t⟩ := cfg
  simp only at hs hh tf t1 t2 t3
  subst hs
  have hp : p = hd := hh.symm
  subst hp
  have hT1m1 : (writeAt t p true) (p + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact t1
  have hT1m2 : (writeAt t p true) (p + 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact t2
  have hT1m3 : (writeAt t p true) (p + 3) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact t3
  have hT2m3 : (writeAt (writeAt t p true) (p + 2) false) (p + 3) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact hT1m3
  have hT2m2 : (writeAt (writeAt t p true) (p + 2) false) (p + 2) = false :=
    writeAt_same _ _ _
  have hT2m1 : (writeAt (writeAt t p true) (p + 2) false) (p + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact hT1m1
  have hT2p : (writeAt (writeAt t p true) (p + 2) false) p = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact writeAt_same t p true
  have s0 : step ⟨State.E, p, t⟩
      = some ⟨State.A, p + 1, writeAt t p true⟩ := by
    simp [step, instr, tf, move]
    try omega
  have s1 : step ⟨State.A, p + 1, writeAt t p true⟩
      = some ⟨State.B, p + 2, writeAt t p true⟩ := by
    have hself := writeAt_self _ _ hT1m1
    simp [step, instr, hT1m1, move, hself]
    try omega
  have s2 : step ⟨State.B, p + 2, writeAt t p true⟩
      = some ⟨State.E, p + 3, writeAt (writeAt t p true) (p + 2) false⟩ := by
    simp [step, instr, hT1m2, move]
    try omega
  have s3 : step ⟨State.E, p + 3, writeAt (writeAt t p true) (p + 2) false⟩
      = some ⟨State.F, p + 2, writeAt (writeAt t p true) (p + 2) false⟩ := by
    have hself := writeAt_self _ _ hT2m3
    simp [step, instr, hT2m3, move, hself]
    try omega
  have s4 : step ⟨State.F, p + 2, writeAt (writeAt t p true) (p + 2) false⟩
      = some ⟨State.E, p + 1, writeAt (writeAt t p true) (p + 2) false⟩ := by
    have hself := writeAt_self _ _ hT2m2
    simp [step, instr, hT2m2, move, hself]
    try omega
  have s5 : step ⟨State.E, p + 1, writeAt (writeAt t p true) (p + 2) false⟩
      = some ⟨State.F, p, writeAt (writeAt t p true) (p + 2) false⟩ := by
    have hself := writeAt_self _ _ hT2m1
    simp [step, instr, hT2m1, move, hself]
    try omega
  have s6 : step ⟨State.F, p, writeAt (writeAt t p true) (p + 2) false⟩
      = some ⟨State.E, p - 1, writeAt (writeAt t p true) (p + 2) false⟩ := by
    have hself := writeAt_self _ _ hT2p
    simp [step, instr, hT2p, move, hself]
    try omega
  have p1 : stepN 1 ⟨State.E, p, t⟩
      = some ⟨State.A, p + 1, writeAt t p true⟩ := by simp [stepN, s0]
  have p2 : stepN 2 ⟨State.E, p, t⟩
      = some ⟨State.B, p + 2, writeAt t p true⟩ := by simp [stepN, s0, s1]
  have p3 : stepN 3 ⟨State.E, p, t⟩
      = some ⟨State.E, p + 3, writeAt (writeAt t p true) (p + 2) false⟩ := by
    simp [stepN, s0, s1, s2]
  have p4 : stepN 4 ⟨State.E, p, t⟩
      = some ⟨State.F, p + 2, writeAt (writeAt t p true) (p + 2) false⟩ := by
    simp [stepN, s0, s1, s2, s3]
  have p5 : stepN 5 ⟨State.E, p, t⟩
      = some ⟨State.E, p + 1, writeAt (writeAt t p true) (p + 2) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4]
  have p6 : stepN 6 ⟨State.E, p, t⟩
      = some ⟨State.F, p, writeAt (writeAt t p true) (p + 2) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5]
  refine ⟨by simp [stepN, s0, s1, s2, s3, s4, s5, s6], ?_⟩
  intro k d hk hkd hB hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by
    omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hdd : (⟨State.E, p, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hB; simp at hB
  · rw [p1] at hkd
    rw [← Option.some_inj.mp hkd] at hB; simp at hB
  · rw [p2] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.B, p + 2, writeAt t p true⟩ : Config).tape
          (⟨State.B, p + 2, writeAt t p true⟩ : Config).head
        = (writeAt t p true) (p + 2) from rfl] at hread
    rw [hT1m2] at hread
    exact absurd hread (by simp)
  · rw [p3] at hkd
    rw [← Option.some_inj.mp hkd] at hB; simp at hB
  · rw [p4] at hkd
    rw [← Option.some_inj.mp hkd] at hB; simp at hB
  · rw [p5] at hkd
    rw [← Option.some_inj.mp hkd] at hB; simp at hB
  · rw [p6] at hkd
    rw [← Option.some_inj.mp hkd] at hB; simp at hB


/-- **The sweep-pair induction**: the `E↔F` gait crosses `2n` ones
without touching the tape.  Informally: the return stroke of the traversal
rule — each pair of steps rewrites `1` over `1` twice (E then F),
so after any number of pairs the tape function is *literally unchanged*
and the head has moved `2n` cells.  Built by induction on the pair count
from the two proven atoms. -/
theorem sweep_EF :
    ∀ (n : Nat) (c : Config), c.state = State.E →
      (∀ i : Nat, i < 2 * n → c.tape (c.head - i) = true) →
      stepN (2 * n) c = some ⟨State.E, c.head - (2 * n : Int), c.tape⟩ := by
  intro n
  induction n with
  | zero =>
      intro c hs _
      obtain ⟨s, h, t⟩ := c
      simp_all [stepN]
  | succ n ih =>
      intro c hs hones
      have h0 : c.tape c.head = true := by
        have := hones 0 (by omega)
        simpa using this
      have h1 : c.tape (c.head - 1) = true := by
        have := hones 1 (by omega)
        rwa [show c.head - ((1 : Nat) : Int) = c.head - 1 by omega] at this
      have hstep1 := step_E_on_one hs h0
      have hstep2 : step ⟨State.F, c.head - 1, c.tape⟩
          = some ⟨State.E, c.head - 1 - 1, c.tape⟩ :=
        step_F_on_one rfl h1
      have hnext := ih ⟨State.E, c.head - 1 - 1, c.tape⟩ rfl
        (fun i hi => by
          have := hones (i + 2) (by omega)
          show c.tape (c.head - 1 - 1 - (i : Int)) = true
          rwa [show c.head - ((i + 2 : Nat) : Int)
                = c.head - 1 - 1 - (i : Int) by omega] at this)
      have a2 : stepN 2 c = some ⟨State.E, c.head - 1 - 1, c.tape⟩ := by
        simp [stepN, hstep1, hstep2]
      have hcomp : stepN (2 * (n + 1)) c
          = (stepN 2 c).bind (stepN (2 * n)) := by
        rw [show 2 * (n + 1) = 2 + 2 * n by omega, stepN_add]
      simp only at hnext
      rw [hcomp, a2]
      show stepN (2 * n) ⟨State.E, c.head - 1 - 1, c.tape⟩
          = some ⟨State.E, c.head - (2 * ((n + 1 : Nat) : Int)), c.tape⟩
      rw [hnext,
          show c.head - 1 - 1 - 2 * (n : Int)
            = c.head - 2 * ((n + 1 : Nat) : Int) from by omega]


/-- **The caterpillar cycle** of the traversal rule: ten raw steps, net
two cells of travel, four tape writes, and both `B`-moments read a `1`.

Informally: the machine's traversal gait — three steps marching, three
more marching, then the `E↔F` pair backing up four; the cycle
carries a moving 0-hole (at offset 3) and consumes two fresh `1`s per
iteration.  This is the unbounded middle of the traversal rule; iterating
it (`cat_run`-style) and bolting on the boundary segments yields the full
`6y + 6z + 1` trajectory. -/
theorem cat_cycle {c : Config} {h : Int}
    (hs : c.state = State.E) (hh : c.head = h)
    (t0 : c.tape h = false)
    (t1 : c.tape (h + 1) = true) (t2 : c.tape (h + 2) = true)
    (t3 : c.tape (h + 3) = false)
    (t4 : c.tape (h + 4) = true) (t5 : c.tape (h + 5) = true)
    (t6 : c.tape (h + 6) = true) :
    stepN 10 c = some ⟨State.E, h + 2, writeAt (writeAt (writeAt (writeAt c.tape h true) (h + 2) false) (h + 3) true) (h + 5) false⟩ ∧ BSafeSeg c 10 := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hs hh t0 t1 t2 t3 t4 t5 t6
  subst hs
  have hp : h = hd := hh.symm
  subst hp
  have hT1m1 : (writeAt t h true) (h + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact t1
  have hT1m2 : (writeAt t h true) (h + 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact t2
  have hT2m3 : (writeAt (writeAt t h true) (h + 2) false) (h + 3) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact t3
  have hT3m4 : (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 4) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega)]
    exact t4
  have hT3m5 : (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 5) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega)]
    exact t5
  have hT4m6 : (writeAt (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact t6
  have hT4m5 : (writeAt (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 5) = false := writeAt_same _ _ _
  have hT4m4 : (writeAt (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 4) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact hT3m4
  have hT4m3 : (writeAt (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 3) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have s0 : step ⟨State.E, h, t⟩ = some ⟨State.A, h + 1, writeAt t h true⟩ := by
    simp [step, instr, t0, move]
    try omega
  have s1 : step ⟨State.A, h + 1, writeAt t h true⟩
      = some ⟨State.B, h + 2, writeAt t h true⟩ := by
    have hself := writeAt_self _ _ hT1m1
    simp [step, instr, hT1m1, move, hself]
    try omega
  have s2 : step ⟨State.B, h + 2, writeAt t h true⟩
      = some ⟨State.E, h + 3, writeAt (writeAt t h true) (h + 2) false⟩ := by
    simp [step, instr, hT1m2, move]
    try omega
  have s3 : step ⟨State.E, h + 3, writeAt (writeAt t h true) (h + 2) false⟩
      = some ⟨State.A, h + 4, writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true⟩ := by
    simp [step, instr, hT2m3, move]
    try omega
  have s4 : step ⟨State.A, h + 4, writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true⟩
      = some ⟨State.B, h + 5, writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true⟩ := by
    have hself := writeAt_self _ _ hT3m4
    simp [step, instr, hT3m4, move, hself]
    try omega
  have s5 : step ⟨State.B, h + 5, writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true⟩
      = some ⟨State.E, h + 6, writeAt (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 5) false⟩ := by
    simp [step, instr, hT3m5, move]
    try omega
  have s6 : step ⟨State.E, h + 6, writeAt (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 5) false⟩
      = some ⟨State.F, h + 5, writeAt (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 5) false⟩ := by
    have hself := writeAt_self _ _ hT4m6
    simp [step, instr, hT4m6, move, hself]
    try omega
  have s7 : step ⟨State.F, h + 5, writeAt (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 5) false⟩
      = some ⟨State.E, h + 4, writeAt (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 5) false⟩ := by
    have hself := writeAt_self _ _ hT4m5
    simp [step, instr, hT4m5, move, hself]
    try omega
  have s8 : step ⟨State.E, h + 4, writeAt (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 5) false⟩
      = some ⟨State.F, h + 3, writeAt (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 5) false⟩ := by
    have hself := writeAt_self _ _ hT4m4
    simp [step, instr, hT4m4, move, hself]
    try omega
  have s9 : step ⟨State.F, h + 3, writeAt (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 5) false⟩
      = some ⟨State.E, h + 2, writeAt (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 5) false⟩ := by
    have hself := writeAt_self _ _ hT4m3
    simp [step, instr, hT4m3, move, hself]
    try omega
  have p1 : stepN 1 ⟨State.E, h, t⟩ = some ⟨State.A, h + 1, writeAt t h true⟩ := by
    simp [stepN, s0]
  have p2 : stepN 2 ⟨State.E, h, t⟩ = some ⟨State.B, h + 2, writeAt t h true⟩ := by
    simp [stepN, s0, s1]
  have p3 : stepN 3 ⟨State.E, h, t⟩ = some ⟨State.E, h + 3, writeAt (writeAt t h true) (h + 2) false⟩ := by
    simp [stepN, s0, s1, s2]
  have p4 : stepN 4 ⟨State.E, h, t⟩ = some ⟨State.A, h + 4, writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true⟩ := by
    simp [stepN, s0, s1, s2, s3]
  have p5 : stepN 5 ⟨State.E, h, t⟩ = some ⟨State.B, h + 5, writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4]
  have p6 : stepN 6 ⟨State.E, h, t⟩ = some ⟨State.E, h + 6, writeAt (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 5) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5]
  have p7 : stepN 7 ⟨State.E, h, t⟩ = some ⟨State.F, h + 5, writeAt (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 5) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6]
  have p8 : stepN 8 ⟨State.E, h, t⟩ = some ⟨State.E, h + 4, writeAt (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 5) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7]
  have p9 : stepN 9 ⟨State.E, h, t⟩ = some ⟨State.F, h + 3, writeAt (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 5) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8]
  refine ⟨by simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9], ?_⟩
  intro k d hk hkd hB hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
      k = 7 ∨ k = 8 ∨ k = 9 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hdd : (⟨State.E, h, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hB; simp at hB
  · rw [p1] at hkd; rw [← Option.some_inj.mp hkd] at hB; simp at hB
  · rw [p2] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.B, h + 2, writeAt t h true⟩ : Config).tape
          (⟨State.B, h + 2, writeAt t h true⟩ : Config).head
        = (writeAt t h true) (h + 2) from rfl] at hread
    rw [hT1m2] at hread
    exact absurd hread (by simp)
  · rw [p3] at hkd; rw [← Option.some_inj.mp hkd] at hB; simp at hB
  · rw [p4] at hkd; rw [← Option.some_inj.mp hkd] at hB; simp at hB
  · rw [p5] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.B, h + 5, writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true⟩ : Config).tape
          (⟨State.B, h + 5, writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true⟩ : Config).head
        = (writeAt (writeAt (writeAt t h true) (h + 2) false) (h + 3) true) (h + 5) from rfl] at hread
    rw [hT3m5] at hread
    exact absurd hread (by simp)
  · rw [p6] at hkd; rw [← Option.some_inj.mp hkd] at hB; simp at hB
  · rw [p7] at hkd; rw [← Option.some_inj.mp hkd] at hB; simp at hB
  · rw [p8] at hkd; rw [← Option.some_inj.mp hkd] at hB; simp at hB
  · rw [p9] at hkd; rw [← Option.some_inj.mp hkd] at hB; simp at hB


/-- State `F` preserves whatever it reads (`F0=0LE`, `F1=1LE`): one step
left, tape literally unchanged — the mirror of dossier-2's free-crossing
return cell. -/
theorem step_F_any {c : Config} (hs : c.state = State.F) :
    step c = some ⟨State.E, c.head - 1, c.tape⟩ := by
  cases hb : c.tape c.head
  · simp [step, instr, hs, hb, move, writeAt_self c.tape c.head hb]
  · simp [step, instr, hs, hb, move, writeAt_self c.tape c.head hb]

/-- **The mixed sweep** (mirror): the `E↔F` return gait needs `1`s only
on the `E`-cells; `F`-cells are arbitrary and preserved, so the sweep
crosses holes sitting at `F`-parity for free. -/
theorem sweep_mixed :
    ∀ (n : Nat) (c : Config), c.state = State.E →
      (∀ i : Nat, i < n → c.tape (c.head - 2 * i) = true) →
      stepN (2 * n) c = some ⟨State.E, c.head - (2 * n : Int), c.tape⟩ := by
  intro n
  induction n with
  | zero => intro c hs _; obtain ⟨s, h, t⟩ := c; simp_all [stepN]
  | succ n ih =>
      intro c hs hones
      have h0 : c.tape c.head = true := by
        have := hones 0 (by omega); simpa using this
      have hstep1 := step_E_on_one hs h0
      have hstep2 : step ⟨State.F, c.head - 1, c.tape⟩
          = some ⟨State.E, c.head - 1 - 1, c.tape⟩ := step_F_any rfl
      have hnext := ih ⟨State.E, c.head - 1 - 1, c.tape⟩ rfl
        (fun i hi => by
          have := hones (i + 1) (by omega)
          show c.tape (c.head - 1 - 1 - 2 * (i : Int)) = true
          rwa [show c.head - 2 * ((i + 1 : Nat) : Int)
                = c.head - 1 - 1 - 2 * (i : Int) by omega] at this)
      have a2 : stepN 2 c = some ⟨State.E, c.head - 1 - 1, c.tape⟩ := by
        simp [stepN, hstep1, hstep2]
      have hcomp : stepN (2 * (n + 1)) c
          = (stepN 2 c).bind (stepN (2 * n)) := by
        rw [show 2 * (n + 1) = 2 + 2 * n by omega, stepN_add]
      simp only at hnext
      rw [hcomp, a2]
      show stepN (2 * n) ⟨State.E, c.head - 1 - 1, c.tape⟩
          = some ⟨State.E, c.head - (2 * ((n + 1 : Nat) : Int)), c.tape⟩
      rw [hnext,
          show c.head - 1 - 1 - 2 * (n : Int)
            = c.head - 2 * ((n + 1 : Nat) : Int) from by omega]

/-- The mixed sweep never enters the danger state `B`. -/
theorem sweep_mixed_safe :
    ∀ (n : Nat) (c : Config), c.state = State.E →
      (∀ i : Nat, i < n → c.tape (c.head - 2 * i) = true) →
      BSafeSeg c (2 * n) := by
  intro n
  induction n with
  | zero => intro c _ _ k d hk; exact absurd hk (by omega)
  | succ n ih =>
      intro c hs hones
      have h0 : c.tape c.head = true := by
        have := hones 0 (by omega); simpa using this
      have hstep1 := step_E_on_one hs h0
      have hstep2 : step ⟨State.F, c.head - 1, c.tape⟩
          = some ⟨State.E, c.head - 1 - 1, c.tape⟩ := step_F_any rfl
      have a2 : stepN 2 c = some ⟨State.E, c.head - 1 - 1, c.tape⟩ := by
        simp [stepN, hstep1, hstep2]
      have hsafe2 : BSafeSeg c 2 := by
        intro k d hk hkd hP hread
        have hk01 : k = 0 ∨ k = 1 := by omega
        rcases hk01 with rfl | rfl
        · have hdd : c = d := by simpa [stepN] using hkd
          rw [← hdd] at hP
          rw [hs] at hP
          exact absurd hP (by simp)
        · have h1 : stepN 1 c = some ⟨State.F, c.head - 1, c.tape⟩ := by
            simp [stepN, hstep1]
          rw [h1] at hkd
          rw [← Option.some_inj.mp hkd] at hP
          exact absurd hP (by simp)
      have hnext := ih ⟨State.E, c.head - 1 - 1, c.tape⟩ rfl
        (fun i hi => by
          have := hones (i + 1) (by omega)
          show c.tape (c.head - 1 - 1 - 2 * (i : Int)) = true
          rwa [show c.head - 2 * ((i + 1 : Nat) : Int)
                = c.head - 1 - 1 - 2 * (i : Int) by omega] at this)
      have hc : BSafeSeg c (2 + 2 * n) := bsafe_compose a2 hsafe2 hnext
      rw [show 2 * (n + 1) = 2 + 2 * n by omega]
      exact hc


/-- **Spawn over the edge hole** (mirror): 7 steps, fills the `r+1` hole, digs at `r+2`, hands back at `r-1`. -/
theorem spawn_variant_step {c : Config} {h : Int}
    (hs : c.state = State.E) (hh : c.head = h)
    (tp0 : c.tape (h) = false) (tp1 : c.tape (h + 1) = false)
    (tp2 : c.tape (h + 2) = true) (tp3 : c.tape (h + 3) = true)
    :
    stepN 7 c = some ⟨State.E, h - 1,
        writeAt (writeAt (writeAt c.tape (h) true) (h + 1) true) (h + 2) false⟩ ∧
      BSafeSeg c 7 := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hs hh tp0 tp1 tp2 tp3
  subst hs
  have hp : h = hd := hh.symm
  subst hp
  have hf0 : (writeAt t (h) true) (h + 1) = false := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tp1
  have hf1 : (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp2
  have hf2 : (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) false) (h + 3) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp3
  have hf3 : (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) false) (h + 2) = false := writeAt_same _ _ _
  have hf4 : (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) false) (h + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf5 : (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) false) (h) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have s0 : step ⟨State.E, h, t⟩
      = some ⟨State.A, h + 1, writeAt t (h) true⟩ := by
    simp [step, instr, tp0, move]
    try omega
  have s1 : step ⟨State.A, h + 1, writeAt t (h) true⟩
      = some ⟨State.B, h + 2, writeAt (writeAt t (h) true) (h + 1) true⟩ := by
    simp [step, instr, hf0, move]
    try omega
  have s2 : step ⟨State.B, h + 2, writeAt (writeAt t (h) true) (h + 1) true⟩
      = some ⟨State.E, h + 3, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) false⟩ := by
    simp [step, instr, hf1, move]
    try omega
  have s3 : step ⟨State.E, h + 3, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) false⟩
      = some ⟨State.F, h + 2, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) false⟩ := by
    have hself := writeAt_self _ _ hf2
    simp [step, instr, hf2, move, hself]
    try omega
  have s4 : step ⟨State.F, h + 2, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) false⟩
      = some ⟨State.E, h + 1, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) false⟩ := by
    have hself := writeAt_self _ _ hf3
    simp [step, instr, hf3, move, hself]
    try omega
  have s5 : step ⟨State.E, h + 1, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) false⟩
      = some ⟨State.F, h, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) false⟩ := by
    have hself := writeAt_self _ _ hf4
    simp [step, instr, hf4, move, hself]
    try omega
  have s6 : step ⟨State.F, h, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) false⟩
      = some ⟨State.E, h - 1, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) false⟩ := by
    have hself := writeAt_self _ _ hf5
    simp [step, instr, hf5, move, hself]
    try omega
  have p1 : stepN 1 ⟨State.E, h, t⟩ = some ⟨State.A, h + 1, writeAt t (h) true⟩ := by
    simp [stepN, s0]
  have p2 : stepN 2 ⟨State.E, h, t⟩ = some ⟨State.B, h + 2, writeAt (writeAt t (h) true) (h + 1) true⟩ := by
    simp [stepN, s0, s1]
  have p3 : stepN 3 ⟨State.E, h, t⟩ = some ⟨State.E, h + 3, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) false⟩ := by
    simp [stepN, s0, s1, s2]
  have p4 : stepN 4 ⟨State.E, h, t⟩ = some ⟨State.F, h + 2, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) false⟩ := by
    simp [stepN, s0, s1, s2, s3]
  have p5 : stepN 5 ⟨State.E, h, t⟩ = some ⟨State.E, h + 1, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4]
  have p6 : stepN 6 ⟨State.E, h, t⟩ = some ⟨State.F, h, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5]
  refine ⟨by simp [stepN, s0, s1, s2, s3, s4, s5, s6], ?_⟩
  intro k d hk hkd hP hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hdd : (⟨State.E, h, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hP
    simp at hP
  · rw [p1] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p2] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.B, h + 2, writeAt (writeAt t (h) true) (h + 1) true⟩ : Config).tape (⟨State.B, h + 2, writeAt (writeAt t (h) true) (h + 1) true⟩ : Config).head
        = (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) from rfl] at hread
    rw [hf1] at hread
    exact absurd hread (by simp)
  · rw [p3] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p4] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p5] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p6] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP

/-- **Hole crossing** (mirror): static hole at offset +6, 13 steps, hole reappears 4 cells left, front lands at `h+5` with flipped arrival parity. -/
theorem cross_cycle {c : Config} {h : Int}
    (hs : c.state = State.E) (hh : c.head = h)
    (tp0 : c.tape (h) = false) (tp1 : c.tape (h + 1) = true)
    (tp2 : c.tape (h + 2) = true) (tp3 : c.tape (h + 3) = false)
    (tp4 : c.tape (h + 4) = true) (tp5 : c.tape (h + 5) = true)
    (tp6 : c.tape (h + 6) = false) (tp7 : c.tape (h + 7) = true)
    (tp8 : c.tape (h + 8) = true) (tp9 : c.tape (h + 9) = true)
    :
    stepN 13 c = some ⟨State.E, h + 5,
        writeAt (writeAt (writeAt (writeAt (writeAt (writeAt c.tape (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) false⟩ ∧
      BSafeSeg c 13 := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hs hh tp0 tp1 tp2 tp3 tp4 tp5 tp6 tp7 tp8 tp9
  subst hs
  have hp : h = hd := hh.symm
  subst hp
  have hf0 : (writeAt t (h) true) (h + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tp1
  have hf1 : (writeAt t (h) true) (h + 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tp2
  have hf2 : (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp3
  have hf3 : (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 4) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp4
  have hf4 : (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp5
  have hf5 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp6
  have hf6 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 7) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp7
  have hf7 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp8
  have hf8 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) false) (h + 9) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp9
  have hf9 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) false) (h + 8) = false := writeAt_same _ _ _
  have hf10 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) false) (h + 7) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp7
  have hf11 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) false) (h + 6) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have s0 : step ⟨State.E, h, t⟩
      = some ⟨State.A, h + 1, writeAt t (h) true⟩ := by
    simp [step, instr, tp0, move]
    try omega
  have s1 : step ⟨State.A, h + 1, writeAt t (h) true⟩
      = some ⟨State.B, h + 2, writeAt t (h) true⟩ := by
    have hself := writeAt_self _ _ hf0
    simp [step, instr, hf0, move, hself]
    try omega
  have s2 : step ⟨State.B, h + 2, writeAt t (h) true⟩
      = some ⟨State.E, h + 3, writeAt (writeAt t (h) true) (h + 2) false⟩ := by
    simp [step, instr, hf1, move]
    try omega
  have s3 : step ⟨State.E, h + 3, writeAt (writeAt t (h) true) (h + 2) false⟩
      = some ⟨State.A, h + 4, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ := by
    simp [step, instr, hf2, move]
    try omega
  have s4 : step ⟨State.A, h + 4, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩
      = some ⟨State.B, h + 5, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ := by
    have hself := writeAt_self _ _ hf3
    simp [step, instr, hf3, move, hself]
    try omega
  have s5 : step ⟨State.B, h + 5, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩
      = some ⟨State.E, h + 6, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false⟩ := by
    simp [step, instr, hf4, move]
    try omega
  have s6 : step ⟨State.E, h + 6, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false⟩
      = some ⟨State.A, h + 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true⟩ := by
    simp [step, instr, hf5, move]
    try omega
  have s7 : step ⟨State.A, h + 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true⟩
      = some ⟨State.B, h + 8, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true⟩ := by
    have hself := writeAt_self _ _ hf6
    simp [step, instr, hf6, move, hself]
    try omega
  have s8 : step ⟨State.B, h + 8, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true⟩
      = some ⟨State.E, h + 9, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) false⟩ := by
    simp [step, instr, hf7, move]
    try omega
  have s9 : step ⟨State.E, h + 9, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) false⟩
      = some ⟨State.F, h + 8, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) false⟩ := by
    have hself := writeAt_self _ _ hf8
    simp [step, instr, hf8, move, hself]
    try omega
  have s10 : step ⟨State.F, h + 8, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) false⟩
      = some ⟨State.E, h + 7, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) false⟩ := by
    have hself := writeAt_self _ _ hf9
    simp [step, instr, hf9, move, hself]
    try omega
  have s11 : step ⟨State.E, h + 7, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) false⟩
      = some ⟨State.F, h + 6, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) false⟩ := by
    have hself := writeAt_self _ _ hf10
    simp [step, instr, hf10, move, hself]
    try omega
  have s12 : step ⟨State.F, h + 6, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) false⟩
      = some ⟨State.E, h + 5, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) false⟩ := by
    have hself := writeAt_self _ _ hf11
    simp [step, instr, hf11, move, hself]
    try omega
  have p1 : stepN 1 ⟨State.E, h, t⟩ = some ⟨State.A, h + 1, writeAt t (h) true⟩ := by
    simp [stepN, s0]
  have p2 : stepN 2 ⟨State.E, h, t⟩ = some ⟨State.B, h + 2, writeAt t (h) true⟩ := by
    simp [stepN, s0, s1]
  have p3 : stepN 3 ⟨State.E, h, t⟩ = some ⟨State.E, h + 3, writeAt (writeAt t (h) true) (h + 2) false⟩ := by
    simp [stepN, s0, s1, s2]
  have p4 : stepN 4 ⟨State.E, h, t⟩ = some ⟨State.A, h + 4, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ := by
    simp [stepN, s0, s1, s2, s3]
  have p5 : stepN 5 ⟨State.E, h, t⟩ = some ⟨State.B, h + 5, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4]
  have p6 : stepN 6 ⟨State.E, h, t⟩ = some ⟨State.E, h + 6, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5]
  have p7 : stepN 7 ⟨State.E, h, t⟩ = some ⟨State.A, h + 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6]
  have p8 : stepN 8 ⟨State.E, h, t⟩ = some ⟨State.B, h + 8, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7]
  have p9 : stepN 9 ⟨State.E, h, t⟩ = some ⟨State.E, h + 9, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8]
  have p10 : stepN 10 ⟨State.E, h, t⟩ = some ⟨State.F, h + 8, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9]
  have p11 : stepN 11 ⟨State.E, h, t⟩ = some ⟨State.E, h + 7, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]
  have p12 : stepN 12 ⟨State.E, h, t⟩ = some ⟨State.F, h + 6, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  refine ⟨by simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12], ?_⟩
  intro k d hk hkd hP hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hdd : (⟨State.E, h, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hP
    simp at hP
  · rw [p1] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p2] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.B, h + 2, writeAt t (h) true⟩ : Config).tape (⟨State.B, h + 2, writeAt t (h) true⟩ : Config).head
        = (writeAt t (h) true) (h + 2) from rfl] at hread
    rw [hf1] at hread
    exact absurd hread (by simp)
  · rw [p3] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p4] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p5] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.B, h + 5, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ : Config).tape (⟨State.B, h + 5, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ : Config).head
        = (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) from rfl] at hread
    rw [hf4] at hread
    exact absurd hread (by simp)
  · rw [p6] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p7] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p8] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.B, h + 8, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true⟩ : Config).tape (⟨State.B, h + 8, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true⟩ : Config).head
        = (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) from rfl] at hread
    rw [hf7] at hread
    exact absurd hread (by simp)
  · rw [p9] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p10] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p11] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p12] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP

/-- **Termination at a hole** (mirror, odd arrival parity): the C-D-B business chain fills the static and plants the new hole 6 cells left, pivoting into the return at `F(h-1)`.  The two danger reads have a `1` on the probe side.  13 steps. -/
theorem term_cycle {c : Config} {h : Int}
    (hs : c.state = State.E) (hh : c.head = h)
    (tm1 : c.tape (h - 1) = true) (tp0 : c.tape (h) = false)
    (tp1 : c.tape (h + 1) = true) (tp2 : c.tape (h + 2) = true)
    (tp3 : c.tape (h + 3) = false) (tp4 : c.tape (h + 4) = true)
    (tp5 : c.tape (h + 5) = false)
    :
    stepN 13 c = some ⟨State.F, h - 1,
        writeAt (writeAt (writeAt (writeAt (writeAt (writeAt c.tape (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true) (h - 1) false⟩ ∧
      BSafeSeg c 13 := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hs hh tm1 tp0 tp1 tp2 tp3 tp4 tp5
  subst hs
  have hp : h = hd := hh.symm
  subst hp
  have hf0 : (writeAt t (h) true) (h + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tp1
  have hf1 : (writeAt t (h) true) (h + 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tp2
  have hf2 : (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp3
  have hf3 : (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 4) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp4
  have hf4 : (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp5
  have hf5 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 4) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp4
  have hf6 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 3) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf7 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf8 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true) (h + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp1
  have hf9 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true) (h) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf10 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true) (h - 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm1
  have hf11 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true) (h - 1) false) (h) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf12 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp1
  have s0 : step ⟨State.E, h, t⟩
      = some ⟨State.A, h + 1, writeAt t (h) true⟩ := by
    simp [step, instr, tp0, move]
    try omega
  have s1 : step ⟨State.A, h + 1, writeAt t (h) true⟩
      = some ⟨State.B, h + 2, writeAt t (h) true⟩ := by
    have hself := writeAt_self _ _ hf0
    simp [step, instr, hf0, move, hself]
    try omega
  have s2 : step ⟨State.B, h + 2, writeAt t (h) true⟩
      = some ⟨State.E, h + 3, writeAt (writeAt t (h) true) (h + 2) false⟩ := by
    simp [step, instr, hf1, move]
    try omega
  have s3 : step ⟨State.E, h + 3, writeAt (writeAt t (h) true) (h + 2) false⟩
      = some ⟨State.A, h + 4, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ := by
    simp [step, instr, hf2, move]
    try omega
  have s4 : step ⟨State.A, h + 4, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩
      = some ⟨State.B, h + 5, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ := by
    have hself := writeAt_self _ _ hf3
    simp [step, instr, hf3, move, hself]
    try omega
  have s5 : step ⟨State.B, h + 5, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩
      = some ⟨State.C, h + 4, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true⟩ := by
    simp [step, instr, hf4, move]
    try omega
  have s6 : step ⟨State.C, h + 4, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true⟩
      = some ⟨State.D, h + 3, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true⟩ := by
    have hself := writeAt_self _ _ hf5
    simp [step, instr, hf5, move, hself]
    try omega
  have s7 : step ⟨State.D, h + 3, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true⟩
      = some ⟨State.B, h + 2, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true⟩ := by
    have hself := writeAt_self _ _ hf6
    simp [step, instr, hf6, move, hself]
    try omega
  have s8 : step ⟨State.B, h + 2, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true⟩
      = some ⟨State.C, h + 1, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true⟩ := by
    simp [step, instr, hf7, move]
    try omega
  have s9 : step ⟨State.C, h + 1, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true⟩
      = some ⟨State.D, h, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true⟩ := by
    have hself := writeAt_self _ _ hf8
    simp [step, instr, hf8, move, hself]
    try omega
  have s10 : step ⟨State.D, h, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true⟩
      = some ⟨State.B, h - 1, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true⟩ := by
    have hself := writeAt_self _ _ hf9
    simp [step, instr, hf9, move, hself]
    try omega
  have s11 : step ⟨State.B, h - 1, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true⟩
      = some ⟨State.E, h, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true) (h - 1) false⟩ := by
    simp [step, instr, hf10, move]
    try omega
  have s12 : step ⟨State.E, h, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true) (h - 1) false⟩
      = some ⟨State.F, h - 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true) (h - 1) false⟩ := by
    have hself := writeAt_self _ _ hf11
    simp [step, instr, hf11, move, hself]
    try omega
  have p1 : stepN 1 ⟨State.E, h, t⟩ = some ⟨State.A, h + 1, writeAt t (h) true⟩ := by
    simp [stepN, s0]
  have p2 : stepN 2 ⟨State.E, h, t⟩ = some ⟨State.B, h + 2, writeAt t (h) true⟩ := by
    simp [stepN, s0, s1]
  have p3 : stepN 3 ⟨State.E, h, t⟩ = some ⟨State.E, h + 3, writeAt (writeAt t (h) true) (h + 2) false⟩ := by
    simp [stepN, s0, s1, s2]
  have p4 : stepN 4 ⟨State.E, h, t⟩ = some ⟨State.A, h + 4, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ := by
    simp [stepN, s0, s1, s2, s3]
  have p5 : stepN 5 ⟨State.E, h, t⟩ = some ⟨State.B, h + 5, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4]
  have p6 : stepN 6 ⟨State.E, h, t⟩ = some ⟨State.C, h + 4, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5]
  have p7 : stepN 7 ⟨State.E, h, t⟩ = some ⟨State.D, h + 3, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6]
  have p8 : stepN 8 ⟨State.E, h, t⟩ = some ⟨State.B, h + 2, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7]
  have p9 : stepN 9 ⟨State.E, h, t⟩ = some ⟨State.C, h + 1, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8]
  have p10 : stepN 10 ⟨State.E, h, t⟩ = some ⟨State.D, h, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9]
  have p11 : stepN 11 ⟨State.E, h, t⟩ = some ⟨State.B, h - 1, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]
  have p12 : stepN 12 ⟨State.E, h, t⟩ = some ⟨State.E, h, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true) (h - 1) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  refine ⟨by simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12], ?_⟩
  intro k d hk hkd hP hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hdd : (⟨State.E, h, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hP
    simp at hP
  · rw [p1] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p2] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.B, h + 2, writeAt t (h) true⟩ : Config).tape (⟨State.B, h + 2, writeAt t (h) true⟩ : Config).head
        = (writeAt t (h) true) (h + 2) from rfl] at hread
    rw [hf1] at hread
    exact absurd hread (by simp)
  · rw [p3] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p4] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p5] at hkd
    rw [← Option.some_inj.mp hkd]
    show (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5 - 1) = true
    rw [show h + 5 - 1 = h + 4 by omega]
    exact hf3
  · rw [p6] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p7] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p8] at hkd
    rw [← Option.some_inj.mp hkd]
    show (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2 - 1) = true
    rw [show h + 2 - 1 = h + 1 by omega]
    exact hf12
  · rw [p9] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p10] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p11] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.B, h - 1, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true⟩ : Config).tape (⟨State.B, h - 1, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true⟩ : Config).head
        = (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) true) (h + 2) true) (h - 1) from rfl] at hread
    rw [hf10] at hread
    exact absurd hread (by simp)
  · rw [p12] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP

/-- **Hole fusion** (mirror, `b = 1`): three fills, plant 9 cells left of the upper hole, parity-shifted return.  19 steps. -/
theorem fuse_cycle {c : Config} {h : Int}
    (hs : c.state = State.E) (hh : c.head = h)
    (tm1 : c.tape (h - 1) = true) (tp0 : c.tape (h) = false)
    (tp1 : c.tape (h + 1) = true) (tp2 : c.tape (h + 2) = true)
    (tp3 : c.tape (h + 3) = false) (tp4 : c.tape (h + 4) = true)
    (tp5 : c.tape (h + 5) = true) (tp6 : c.tape (h + 6) = false)
    (tp7 : c.tape (h + 7) = true) (tp8 : c.tape (h + 8) = false)
    :
    stepN 19 c = some ⟨State.F, h - 1,
        writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt c.tape (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true) (h - 1) false⟩ ∧
      BSafeSeg c 19 := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hs hh tm1 tp0 tp1 tp2 tp3 tp4 tp5 tp6 tp7 tp8
  subst hs
  have hp : h = hd := hh.symm
  subst hp
  have hf0 : (writeAt t (h) true) (h + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tp1
  have hf1 : (writeAt t (h) true) (h + 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tp2
  have hf2 : (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp3
  have hf3 : (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 4) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp4
  have hf4 : (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp5
  have hf5 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp6
  have hf6 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 7) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp7
  have hf7 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp8
  have hf8 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 7) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp7
  have hf9 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 6) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf10 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf11 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 4) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp4
  have hf12 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 3) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf13 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf14 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true) (h + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp1
  have hf15 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true) (h) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf16 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true) (h - 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm1
  have hf17 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true) (h - 1) false) (h) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf18 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 4) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp4
  have hf19 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp1
  have s0 : step ⟨State.E, h, t⟩
      = some ⟨State.A, h + 1, writeAt t (h) true⟩ := by
    simp [step, instr, tp0, move]
    try omega
  have s1 : step ⟨State.A, h + 1, writeAt t (h) true⟩
      = some ⟨State.B, h + 2, writeAt t (h) true⟩ := by
    have hself := writeAt_self _ _ hf0
    simp [step, instr, hf0, move, hself]
    try omega
  have s2 : step ⟨State.B, h + 2, writeAt t (h) true⟩
      = some ⟨State.E, h + 3, writeAt (writeAt t (h) true) (h + 2) false⟩ := by
    simp [step, instr, hf1, move]
    try omega
  have s3 : step ⟨State.E, h + 3, writeAt (writeAt t (h) true) (h + 2) false⟩
      = some ⟨State.A, h + 4, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ := by
    simp [step, instr, hf2, move]
    try omega
  have s4 : step ⟨State.A, h + 4, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩
      = some ⟨State.B, h + 5, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ := by
    have hself := writeAt_self _ _ hf3
    simp [step, instr, hf3, move, hself]
    try omega
  have s5 : step ⟨State.B, h + 5, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩
      = some ⟨State.E, h + 6, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false⟩ := by
    simp [step, instr, hf4, move]
    try omega
  have s6 : step ⟨State.E, h + 6, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false⟩
      = some ⟨State.A, h + 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true⟩ := by
    simp [step, instr, hf5, move]
    try omega
  have s7 : step ⟨State.A, h + 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true⟩
      = some ⟨State.B, h + 8, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true⟩ := by
    have hself := writeAt_self _ _ hf6
    simp [step, instr, hf6, move, hself]
    try omega
  have s8 : step ⟨State.B, h + 8, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true⟩
      = some ⟨State.C, h + 7, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true⟩ := by
    simp [step, instr, hf7, move]
    try omega
  have s9 : step ⟨State.C, h + 7, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true⟩
      = some ⟨State.D, h + 6, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true⟩ := by
    have hself := writeAt_self _ _ hf8
    simp [step, instr, hf8, move, hself]
    try omega
  have s10 : step ⟨State.D, h + 6, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true⟩
      = some ⟨State.B, h + 5, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true⟩ := by
    have hself := writeAt_self _ _ hf9
    simp [step, instr, hf9, move, hself]
    try omega
  have s11 : step ⟨State.B, h + 5, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true⟩
      = some ⟨State.C, h + 4, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true⟩ := by
    simp [step, instr, hf10, move]
    try omega
  have s12 : step ⟨State.C, h + 4, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true⟩
      = some ⟨State.D, h + 3, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true⟩ := by
    have hself := writeAt_self _ _ hf11
    simp [step, instr, hf11, move, hself]
    try omega
  have s13 : step ⟨State.D, h + 3, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true⟩
      = some ⟨State.B, h + 2, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true⟩ := by
    have hself := writeAt_self _ _ hf12
    simp [step, instr, hf12, move, hself]
    try omega
  have s14 : step ⟨State.B, h + 2, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true⟩
      = some ⟨State.C, h + 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true⟩ := by
    simp [step, instr, hf13, move]
    try omega
  have s15 : step ⟨State.C, h + 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true⟩
      = some ⟨State.D, h, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true⟩ := by
    have hself := writeAt_self _ _ hf14
    simp [step, instr, hf14, move, hself]
    try omega
  have s16 : step ⟨State.D, h, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true⟩
      = some ⟨State.B, h - 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true⟩ := by
    have hself := writeAt_self _ _ hf15
    simp [step, instr, hf15, move, hself]
    try omega
  have s17 : step ⟨State.B, h - 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true⟩
      = some ⟨State.E, h, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true) (h - 1) false⟩ := by
    simp [step, instr, hf16, move]
    try omega
  have s18 : step ⟨State.E, h, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true) (h - 1) false⟩
      = some ⟨State.F, h - 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true) (h - 1) false⟩ := by
    have hself := writeAt_self _ _ hf17
    simp [step, instr, hf17, move, hself]
    try omega
  have p1 : stepN 1 ⟨State.E, h, t⟩ = some ⟨State.A, h + 1, writeAt t (h) true⟩ := by
    simp [stepN, s0]
  have p2 : stepN 2 ⟨State.E, h, t⟩ = some ⟨State.B, h + 2, writeAt t (h) true⟩ := by
    simp [stepN, s0, s1]
  have p3 : stepN 3 ⟨State.E, h, t⟩ = some ⟨State.E, h + 3, writeAt (writeAt t (h) true) (h + 2) false⟩ := by
    simp [stepN, s0, s1, s2]
  have p4 : stepN 4 ⟨State.E, h, t⟩ = some ⟨State.A, h + 4, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ := by
    simp [stepN, s0, s1, s2, s3]
  have p5 : stepN 5 ⟨State.E, h, t⟩ = some ⟨State.B, h + 5, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4]
  have p6 : stepN 6 ⟨State.E, h, t⟩ = some ⟨State.E, h + 6, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5]
  have p7 : stepN 7 ⟨State.E, h, t⟩ = some ⟨State.A, h + 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6]
  have p8 : stepN 8 ⟨State.E, h, t⟩ = some ⟨State.B, h + 8, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7]
  have p9 : stepN 9 ⟨State.E, h, t⟩ = some ⟨State.C, h + 7, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8]
  have p10 : stepN 10 ⟨State.E, h, t⟩ = some ⟨State.D, h + 6, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9]
  have p11 : stepN 11 ⟨State.E, h, t⟩ = some ⟨State.B, h + 5, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]
  have p12 : stepN 12 ⟨State.E, h, t⟩ = some ⟨State.C, h + 4, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  have p13 : stepN 13 ⟨State.E, h, t⟩ = some ⟨State.D, h + 3, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12]
  have p14 : stepN 14 ⟨State.E, h, t⟩ = some ⟨State.B, h + 2, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13]
  have p15 : stepN 15 ⟨State.E, h, t⟩ = some ⟨State.C, h + 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14]
  have p16 : stepN 16 ⟨State.E, h, t⟩ = some ⟨State.D, h, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15]
  have p17 : stepN 17 ⟨State.E, h, t⟩ = some ⟨State.B, h - 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16]
  have p18 : stepN 18 ⟨State.E, h, t⟩ = some ⟨State.E, h, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true) (h - 1) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17]
  refine ⟨by simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18], ?_⟩
  intro k d hk hkd hP hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hdd : (⟨State.E, h, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hP
    simp at hP
  · rw [p1] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p2] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.B, h + 2, writeAt t (h) true⟩ : Config).tape (⟨State.B, h + 2, writeAt t (h) true⟩ : Config).head
        = (writeAt t (h) true) (h + 2) from rfl] at hread
    rw [hf1] at hread
    exact absurd hread (by simp)
  · rw [p3] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p4] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p5] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.B, h + 5, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ : Config).tape (⟨State.B, h + 5, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ : Config).head
        = (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) from rfl] at hread
    rw [hf4] at hread
    exact absurd hread (by simp)
  · rw [p6] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p7] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p8] at hkd
    rw [← Option.some_inj.mp hkd]
    show (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8 - 1) = true
    rw [show h + 8 - 1 = h + 7 by omega]
    exact hf6
  · rw [p9] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p10] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p11] at hkd
    rw [← Option.some_inj.mp hkd]
    show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5 - 1) = true
    rw [show h + 5 - 1 = h + 4 by omega]
    exact hf18
  · rw [p12] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p13] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p14] at hkd
    rw [← Option.some_inj.mp hkd]
    show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2 - 1) = true
    rw [show h + 2 - 1 = h + 1 by omega]
    exact hf19
  · rw [p15] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p16] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p17] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.B, h - 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true⟩ : Config).tape (⟨State.B, h - 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true⟩ : Config).head
        = (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 6) true) (h + 8) true) (h + 5) true) (h + 2) true) (h - 1) from rfl] at hread
    rw [hf16] at hread
    exact absurd hread (by simp)
  · rw [p18] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP

/-- **Right-edge business, odd `a`** (mirror): one virgin cell, plant at `(l+1)-6`.  10 steps. -/
theorem edge_odd_seg {c : Config} {h : Int}
    (hs : c.state = State.E) (hh : c.head = h)
    (tm4 : c.tape (h - 4) = true) (tm3 : c.tape (h - 3) = true)
    (tm2 : c.tape (h - 2) = true) (tm1 : c.tape (h - 1) = false)
    (tp0 : c.tape (h) = false) (tp1 : c.tape (h + 1) = true)
    (tp2 : c.tape (h + 2) = false)
    :
    stepN 10 c = some ⟨State.F, h - 4,
        writeAt (writeAt (writeAt (writeAt c.tape (h) true) (h + 2) true) (h - 1) true) (h - 4) false⟩ ∧
      BSafeSeg c 10 := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hs hh tm4 tm3 tm2 tm1 tp0 tp1 tp2
  subst hs
  have hp : h = hd := hh.symm
  subst hp
  have hf0 : (writeAt t (h) true) (h + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tp1
  have hf1 : (writeAt t (h) true) (h + 2) = false := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tp2
  have hf2 : (writeAt (writeAt t (h) true) (h + 2) true) (h + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp1
  have hf3 : (writeAt (writeAt t (h) true) (h + 2) true) (h) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf4 : (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm1
  have hf5 : (writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true) (h - 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm2
  have hf6 : (writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true) (h - 3) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm3
  have hf7 : (writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true) (h - 4) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm4
  have hf8 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true) (h - 4) false) (h - 3) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm3
  have hf9 : (writeAt (writeAt t (h) true) (h + 2) true) (h - 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm2
  have s0 : step ⟨State.E, h, t⟩
      = some ⟨State.A, h + 1, writeAt t (h) true⟩ := by
    simp [step, instr, tp0, move]
    try omega
  have s1 : step ⟨State.A, h + 1, writeAt t (h) true⟩
      = some ⟨State.B, h + 2, writeAt t (h) true⟩ := by
    have hself := writeAt_self _ _ hf0
    simp [step, instr, hf0, move, hself]
    try omega
  have s2 : step ⟨State.B, h + 2, writeAt t (h) true⟩
      = some ⟨State.C, h + 1, writeAt (writeAt t (h) true) (h + 2) true⟩ := by
    simp [step, instr, hf1, move]
    try omega
  have s3 : step ⟨State.C, h + 1, writeAt (writeAt t (h) true) (h + 2) true⟩
      = some ⟨State.D, h, writeAt (writeAt t (h) true) (h + 2) true⟩ := by
    have hself := writeAt_self _ _ hf2
    simp [step, instr, hf2, move, hself]
    try omega
  have s4 : step ⟨State.D, h, writeAt (writeAt t (h) true) (h + 2) true⟩
      = some ⟨State.B, h - 1, writeAt (writeAt t (h) true) (h + 2) true⟩ := by
    have hself := writeAt_self _ _ hf3
    simp [step, instr, hf3, move, hself]
    try omega
  have s5 : step ⟨State.B, h - 1, writeAt (writeAt t (h) true) (h + 2) true⟩
      = some ⟨State.C, h - 2, writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true⟩ := by
    simp [step, instr, hf4, move]
    try omega
  have s6 : step ⟨State.C, h - 2, writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true⟩
      = some ⟨State.D, h - 3, writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true⟩ := by
    have hself := writeAt_self _ _ hf5
    simp [step, instr, hf5, move, hself]
    try omega
  have s7 : step ⟨State.D, h - 3, writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true⟩
      = some ⟨State.B, h - 4, writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true⟩ := by
    have hself := writeAt_self _ _ hf6
    simp [step, instr, hf6, move, hself]
    try omega
  have s8 : step ⟨State.B, h - 4, writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true⟩
      = some ⟨State.E, h - 3, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true) (h - 4) false⟩ := by
    simp [step, instr, hf7, move]
    try omega
  have s9 : step ⟨State.E, h - 3, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true) (h - 4) false⟩
      = some ⟨State.F, h - 4, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true) (h - 4) false⟩ := by
    have hself := writeAt_self _ _ hf8
    simp [step, instr, hf8, move, hself]
    try omega
  have p1 : stepN 1 ⟨State.E, h, t⟩ = some ⟨State.A, h + 1, writeAt t (h) true⟩ := by
    simp [stepN, s0]
  have p2 : stepN 2 ⟨State.E, h, t⟩ = some ⟨State.B, h + 2, writeAt t (h) true⟩ := by
    simp [stepN, s0, s1]
  have p3 : stepN 3 ⟨State.E, h, t⟩ = some ⟨State.C, h + 1, writeAt (writeAt t (h) true) (h + 2) true⟩ := by
    simp [stepN, s0, s1, s2]
  have p4 : stepN 4 ⟨State.E, h, t⟩ = some ⟨State.D, h, writeAt (writeAt t (h) true) (h + 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3]
  have p5 : stepN 5 ⟨State.E, h, t⟩ = some ⟨State.B, h - 1, writeAt (writeAt t (h) true) (h + 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4]
  have p6 : stepN 6 ⟨State.E, h, t⟩ = some ⟨State.C, h - 2, writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5]
  have p7 : stepN 7 ⟨State.E, h, t⟩ = some ⟨State.D, h - 3, writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6]
  have p8 : stepN 8 ⟨State.E, h, t⟩ = some ⟨State.B, h - 4, writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7]
  have p9 : stepN 9 ⟨State.E, h, t⟩ = some ⟨State.E, h - 3, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true) (h - 4) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8]
  refine ⟨by simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9], ?_⟩
  intro k d hk hkd hP hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hdd : (⟨State.E, h, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hP
    simp at hP
  · rw [p1] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p2] at hkd
    rw [← Option.some_inj.mp hkd]
    show (writeAt t (h) true) (h + 2 - 1) = true
    rw [show h + 2 - 1 = h + 1 by omega]
    exact hf0
  · rw [p3] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p4] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p5] at hkd
    rw [← Option.some_inj.mp hkd]
    show (writeAt (writeAt t (h) true) (h + 2) true) (h - 1 - 1) = true
    rw [show h - 1 - 1 = h - 2 by omega]
    exact hf9
  · rw [p6] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p7] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p8] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.B, h - 4, writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true⟩ : Config).tape (⟨State.B, h - 4, writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true⟩ : Config).head
        = (writeAt (writeAt (writeAt t (h) true) (h + 2) true) (h - 1) true) (h - 4) from rfl] at hread
    rw [hf7] at hread
    exact absurd hread (by simp)
  · rw [p9] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP

/-- **Right-edge business, even `a`** (mirror): three virgin cells, plant at `(l+3)-9`.  13 steps. -/
theorem edge_even_seg {c : Config} {h : Int}
    (hs : c.state = State.E) (hh : c.head = h)
    (tm7 : c.tape (h - 7) = true) (tm6 : c.tape (h - 6) = true)
    (tm5 : c.tape (h - 5) = true) (tm4 : c.tape (h - 4) = false)
    (tm3 : c.tape (h - 3) = true) (tm2 : c.tape (h - 2) = true)
    (tm1 : c.tape (h - 1) = false) (tp0 : c.tape (h) = false)
    (tp1 : c.tape (h + 1) = false) (tp2 : c.tape (h + 2) = false)
    :
    stepN 13 c = some ⟨State.F, h - 7,
        writeAt (writeAt (writeAt (writeAt (writeAt (writeAt c.tape (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true) (h - 7) false⟩ ∧
      BSafeSeg c 13 := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hs hh tm7 tm6 tm5 tm4 tm3 tm2 tm1 tp0 tp1 tp2
  subst hs
  have hp : h = hd := hh.symm
  subst hp
  have hf0 : (writeAt t (h) true) (h + 1) = false := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tp1
  have hf1 : (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp2
  have hf2 : (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf3 : (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf4 : (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm1
  have hf5 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm2
  have hf6 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 3) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm3
  have hf7 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm4
  have hf8 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true) (h - 5) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm5
  have hf9 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true) (h - 6) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm6
  have hf10 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true) (h - 7) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm7
  have hf11 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true) (h - 7) false) (h - 6) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm6
  have hf12 : (writeAt (writeAt t (h) true) (h + 1) true) (h + 1) = true := writeAt_same _ _ _
  have hf13 : (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm2
  have hf14 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 5) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm5
  have s0 : step ⟨State.E, h, t⟩
      = some ⟨State.A, h + 1, writeAt t (h) true⟩ := by
    simp [step, instr, tp0, move]
    try omega
  have s1 : step ⟨State.A, h + 1, writeAt t (h) true⟩
      = some ⟨State.B, h + 2, writeAt (writeAt t (h) true) (h + 1) true⟩ := by
    simp [step, instr, hf0, move]
    try omega
  have s2 : step ⟨State.B, h + 2, writeAt (writeAt t (h) true) (h + 1) true⟩
      = some ⟨State.C, h + 1, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true⟩ := by
    simp [step, instr, hf1, move]
    try omega
  have s3 : step ⟨State.C, h + 1, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true⟩
      = some ⟨State.D, h, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true⟩ := by
    have hself := writeAt_self _ _ hf2
    simp [step, instr, hf2, move, hself]
    try omega
  have s4 : step ⟨State.D, h, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true⟩
      = some ⟨State.B, h - 1, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true⟩ := by
    have hself := writeAt_self _ _ hf3
    simp [step, instr, hf3, move, hself]
    try omega
  have s5 : step ⟨State.B, h - 1, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true⟩
      = some ⟨State.C, h - 2, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true⟩ := by
    simp [step, instr, hf4, move]
    try omega
  have s6 : step ⟨State.C, h - 2, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true⟩
      = some ⟨State.D, h - 3, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true⟩ := by
    have hself := writeAt_self _ _ hf5
    simp [step, instr, hf5, move, hself]
    try omega
  have s7 : step ⟨State.D, h - 3, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true⟩
      = some ⟨State.B, h - 4, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true⟩ := by
    have hself := writeAt_self _ _ hf6
    simp [step, instr, hf6, move, hself]
    try omega
  have s8 : step ⟨State.B, h - 4, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true⟩
      = some ⟨State.C, h - 5, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true⟩ := by
    simp [step, instr, hf7, move]
    try omega
  have s9 : step ⟨State.C, h - 5, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true⟩
      = some ⟨State.D, h - 6, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true⟩ := by
    have hself := writeAt_self _ _ hf8
    simp [step, instr, hf8, move, hself]
    try omega
  have s10 : step ⟨State.D, h - 6, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true⟩
      = some ⟨State.B, h - 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true⟩ := by
    have hself := writeAt_self _ _ hf9
    simp [step, instr, hf9, move, hself]
    try omega
  have s11 : step ⟨State.B, h - 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true⟩
      = some ⟨State.E, h - 6, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true) (h - 7) false⟩ := by
    simp [step, instr, hf10, move]
    try omega
  have s12 : step ⟨State.E, h - 6, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true) (h - 7) false⟩
      = some ⟨State.F, h - 7, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true) (h - 7) false⟩ := by
    have hself := writeAt_self _ _ hf11
    simp [step, instr, hf11, move, hself]
    try omega
  have p1 : stepN 1 ⟨State.E, h, t⟩ = some ⟨State.A, h + 1, writeAt t (h) true⟩ := by
    simp [stepN, s0]
  have p2 : stepN 2 ⟨State.E, h, t⟩ = some ⟨State.B, h + 2, writeAt (writeAt t (h) true) (h + 1) true⟩ := by
    simp [stepN, s0, s1]
  have p3 : stepN 3 ⟨State.E, h, t⟩ = some ⟨State.C, h + 1, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true⟩ := by
    simp [stepN, s0, s1, s2]
  have p4 : stepN 4 ⟨State.E, h, t⟩ = some ⟨State.D, h, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3]
  have p5 : stepN 5 ⟨State.E, h, t⟩ = some ⟨State.B, h - 1, writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4]
  have p6 : stepN 6 ⟨State.E, h, t⟩ = some ⟨State.C, h - 2, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5]
  have p7 : stepN 7 ⟨State.E, h, t⟩ = some ⟨State.D, h - 3, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6]
  have p8 : stepN 8 ⟨State.E, h, t⟩ = some ⟨State.B, h - 4, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7]
  have p9 : stepN 9 ⟨State.E, h, t⟩ = some ⟨State.C, h - 5, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8]
  have p10 : stepN 10 ⟨State.E, h, t⟩ = some ⟨State.D, h - 6, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9]
  have p11 : stepN 11 ⟨State.E, h, t⟩ = some ⟨State.B, h - 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]
  have p12 : stepN 12 ⟨State.E, h, t⟩ = some ⟨State.E, h - 6, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true) (h - 7) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  refine ⟨by simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12], ?_⟩
  intro k d hk hkd hP hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hdd : (⟨State.E, h, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hP
    simp at hP
  · rw [p1] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p2] at hkd
    rw [← Option.some_inj.mp hkd]
    show (writeAt (writeAt t (h) true) (h + 1) true) (h + 2 - 1) = true
    rw [show h + 2 - 1 = h + 1 by omega]
    exact hf12
  · rw [p3] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p4] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p5] at hkd
    rw [← Option.some_inj.mp hkd]
    show (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1 - 1) = true
    rw [show h - 1 - 1 = h - 2 by omega]
    exact hf13
  · rw [p6] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p7] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p8] at hkd
    rw [← Option.some_inj.mp hkd]
    show (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4 - 1) = true
    rw [show h - 4 - 1 = h - 5 by omega]
    exact hf14
  · rw [p9] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p10] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p11] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.B, h - 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true⟩ : Config).tape (⟨State.B, h - 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true⟩ : Config).head
        = (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h + 1) true) (h + 2) true) (h - 1) true) (h - 4) true) (h - 7) from rfl] at hread
    rw [hf10] at hread
    exact absurd hread (by simp)
  · rw [p12] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP


/-- Constructive De Morgan for the interval guards (mirror): hands
`omega` a positive disjunction instead of a negated conjunction (which
would pull `Classical.choice` into the axiom print). -/
theorem not_and_ge {a b q : Int} (h : ¬(a ≤ q ∧ q < b)) :
    q < a ∨ b ≤ q := by
  by_cases hx : a ≤ q
  · right
    by_cases hy : q < b
    · exact absurd ⟨hx, hy⟩ h
    · omega
  · left
    omega

/-- Closed form of the tape after `n` caterpillar cycles from entry `h`
(mirror): the crawled zone `[h, h + 2n + 3)` is all `1`s except the new
front cell `h + 2n`; the new carried hole sits at `h + 2n + 3`. -/
def catTape (t : Int → Bool) (h : Int) (n : Nat) : Int → Bool :=
  fun q =>
    if q = h + 2 * n ∨ q = h + 2 * n + 3 then false
    else if h ≤ q ∧ q < h + 2 * n + 3 then true
    else t q

/-- **The caterpillar run** (mirror): `n` cycles glued end-to-end —
`10n` steps, `2n` cells of rightward travel, probe-safe throughout. -/
theorem cat_run :
    ∀ (n : Nat) (c : Config) (h : Int), c.state = State.E → c.head = h →
      c.tape h = false → c.tape (h + 3) = false →
      (∀ q : Int, h ≤ q → q ≤ h + 2 * n + 4 → q ≠ h → q ≠ h + 3 →
        c.tape q = true) →
      stepN (10 * n) c = some ⟨State.E, h + 2 * n, catTape c.tape h n⟩ ∧
        BSafeSeg c (10 * n) := by
  intro n
  induction n with
  | zero =>
      intro c h hs hh t0 t3 hpre
      obtain ⟨s, hd, t⟩ := c
      simp only at hs hh t0 t3 hpre
      subst hs
      have hp : h = hd := hh.symm
      subst hp
      refine ⟨?_, ?_⟩
      · have htape : catTape t h 0 = t := by
          funext q
          show (if q = h + 2 * ((0 : Nat) : Int) ∨
                  q = h + 2 * ((0 : Nat) : Int) + 3 then false
                else if h ≤ q ∧ q < h + 2 * ((0 : Nat) : Int) + 3 then true
                else t q) = t q
          split
          · rename_i hA
            rcases hA with h1 | h1
            · have hq : q = h := by omega
              rw [hq]
              exact t0.symm
            · have hq : q = h + 3 := by omega
              rw [hq]
              exact t3.symm
          · split
            · rename_i hA hB
              exact (hpre q (by omega) (by omega) (by omega)
                (by omega)).symm
            · rfl
        show some (⟨State.E, h, t⟩ : Config) = _
        rw [htape,
            show h + 2 * ((0 : Nat) : Int) = h from by omega]
      · intro k d hk
        exact absurd hk (by omega)
  | succ n ih =>
      intro c h hs hh t0 t3 hpre
      have h1 := hpre (h + 1) (by omega) (by omega) (by omega) (by omega)
      have h2 := hpre (h + 2) (by omega) (by omega) (by omega) (by omega)
      have h4 := hpre (h + 4) (by omega) (by omega) (by omega) (by omega)
      have h5 := hpre (h + 5) (by omega) (by omega) (by omega) (by omega)
      have h6 := hpre (h + 6) (by omega) (by omega) (by omega) (by omega)
      obtain ⟨hrun10, hsafe10⟩ := cat_cycle hs hh t0 h1 h2 t3 h4 h5 h6
      have hT1f : (writeAt (writeAt (writeAt (writeAt c.tape h true)
          (h + 2) false) (h + 3) true) (h + 5) false) (h + 2) = false := by
        rw [writeAt_other _ _ _ _ (by omega),
            writeAt_other _ _ _ _ (by omega)]
        exact writeAt_same _ _ _
      have hT1c : (writeAt (writeAt (writeAt (writeAt c.tape h true)
          (h + 2) false) (h + 3) true) (h + 5) false) (h + 2 + 3)
          = false := by
        rw [show h + 2 + 3 = h + 5 from by omega]
        exact writeAt_same _ _ _
      have hT1pre : ∀ q : Int, h + 2 ≤ q → q ≤ h + 2 + 2 * (n : Int) + 4 →
          q ≠ h + 2 → q ≠ h + 2 + 3 →
          (writeAt (writeAt (writeAt (writeAt c.tape h true)
            (h + 2) false) (h + 3) true) (h + 5) false) q = true := by
        intro q hq1 hq2 hq3 hq4
        by_cases hq5 : q = h + 3
        · rw [hq5, writeAt_other _ _ _ _ (by omega)]
          exact writeAt_same _ _ _
        · rw [writeAt_other _ _ _ _ (by omega),
              writeAt_other _ _ _ _ (by omega),
              writeAt_other _ _ _ _ (by omega),
              writeAt_other _ _ _ _ (by omega)]
          exact hpre q (by omega) (by omega) (by omega) (by omega)
      obtain ⟨hrunN, hsafeN⟩ :=
        ih ⟨State.E, h + 2, writeAt (writeAt (writeAt (writeAt c.tape h
          true) (h + 2) false) (h + 3) true) (h + 5) false⟩ (h + 2)
          rfl rfl hT1f hT1c hT1pre
      have heq : catTape (writeAt (writeAt (writeAt (writeAt c.tape h
          true) (h + 2) false) (h + 3) true) (h + 5) false) (h + 2) n
          = catTape c.tape h (n + 1) := by
        funext q
        show (if q = h + 2 + 2 * (n : Int) ∨
                q = h + 2 + 2 * (n : Int) + 3 then false
              else if h + 2 ≤ q ∧ q < h + 2 + 2 * (n : Int) + 3 then true
              else (writeAt (writeAt (writeAt (writeAt c.tape h true)
                (h + 2) false) (h + 3) true) (h + 5) false) q) =
            (if q = h + 2 * ((n + 1 : Nat) : Int) ∨
                q = h + 2 * ((n + 1 : Nat) : Int) + 3 then false
              else if h ≤ q ∧ q < h + 2 * ((n + 1 : Nat) : Int) + 3
                then true
              else c.tape q)
        split
        · rename_i hA
          split
          · rfl
          · rename_i hA2
            exfalso
            rcases hA with hx | hx
            · exact hA2 (Or.inl (by omega))
            · exact hA2 (Or.inr (by omega))
        · rename_i hA
          have hA2 : ¬(q = h + 2 * ((n + 1 : Nat) : Int) ∨
              q = h + 2 * ((n + 1 : Nat) : Int) + 3) := by
            intro hc
            rcases hc with hx | hx
            · exact hA (Or.inl (by omega))
            · exact hA (Or.inr (by omega))
          rw [if_neg hA2]
          split
          · rename_i hB
            rw [if_pos (show h ≤ q ∧
                q < h + 2 * ((n + 1 : Nat) : Int) + 3 from
                ⟨by omega, by omega⟩)]
          · rename_i hB
            have hB' := not_and_ge hB
            clear hB
            split
            · rename_i hB2
              obtain ⟨hB2a, hB2b⟩ := hB2
              by_cases hq : q = h
              · rw [hq, writeAt_other _ _ _ _ (by omega),
                    writeAt_other _ _ _ _ (by omega),
                    writeAt_other _ _ _ _ (by omega)]
                exact writeAt_same _ _ _
              · have hq1 : q = h + 1 := by omega
                rw [hq1, writeAt_other _ _ _ _ (by omega),
                    writeAt_other _ _ _ _ (by omega),
                    writeAt_other _ _ _ _ (by omega),
                    writeAt_other _ _ _ _ (by omega)]
                exact hpre (h + 1) (by omega) (by omega) (by omega)
                  (by omega)
            · rename_i hB2
              have hB2' := not_and_ge hB2
              clear hB2
              rw [writeAt_other _ _ _ _ (by omega),
                  writeAt_other _ _ _ _ (by omega),
                  writeAt_other _ _ _ _ (by omega),
                  writeAt_other _ _ _ _ (by omega)]
      have hcomp : stepN (10 * (n + 1)) c
          = (stepN 10 c).bind (stepN (10 * n)) := by
        rw [show 10 * (n + 1) = 10 + 10 * n from by omega, stepN_add]
      refine ⟨?_, ?_⟩
      · rw [hcomp, hrun10]
        show stepN (10 * n) ⟨State.E, h + 2, writeAt (writeAt (writeAt
            (writeAt c.tape h true) (h + 2) false) (h + 3) true)
            (h + 5) false⟩
            = some ⟨State.E, h + 2 * ((n + 1 : Nat) : Int),
                catTape c.tape h (n + 1)⟩
        rw [hrunN, heq,
            show h + 2 + 2 * (n : Int)
              = h + 2 * ((n + 1 : Nat) : Int) from by omega]
      · have hc := bsafe_compose hrun10 hsafe10 hsafeN
        rw [show 10 * (n + 1) = 10 + 10 * n from by omega]
        exact hc

/-- **March triple**: the first three steps of a cycle in isolation — used when the crawl's final segment is a partial cycle ending at the left-edge business.  Digs at offset 2 behind, fills the front, hands to the next march position. -/
theorem march_triple {c : Config} {h : Int}
    (hs : c.state = State.E) (hh : c.head = h)
    (tp0 : c.tape (h) = false) (tp1 : c.tape (h + 1) = true)
    (tp2 : c.tape (h + 2) = true)
    :
    stepN 3 c = some ⟨State.E, h + 3,
        writeAt (writeAt c.tape (h) true) (h + 2) false⟩ ∧
      BSafeSeg c 3 := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hs hh tp0 tp1 tp2
  subst hs
  have hp : h = hd := hh.symm
  subst hp
  have hf0 : (writeAt t (h) true) (h + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tp1
  have hf1 : (writeAt t (h) true) (h + 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tp2
  have s0 : step ⟨State.E, h, t⟩
      = some ⟨State.A, h + 1, writeAt t (h) true⟩ := by
    simp [step, instr, tp0, move]
    try omega
  have s1 : step ⟨State.A, h + 1, writeAt t (h) true⟩
      = some ⟨State.B, h + 2, writeAt t (h) true⟩ := by
    have hself := writeAt_self _ _ hf0
    simp [step, instr, hf0, move, hself]
    try omega
  have s2 : step ⟨State.B, h + 2, writeAt t (h) true⟩
      = some ⟨State.E, h + 3, writeAt (writeAt t (h) true) (h + 2) false⟩ := by
    simp [step, instr, hf1, move]
    try omega
  have p1 : stepN 1 ⟨State.E, h, t⟩ = some ⟨State.A, h + 1, writeAt t (h) true⟩ := by
    simp [stepN, s0]
  have p2 : stepN 2 ⟨State.E, h, t⟩ = some ⟨State.B, h + 2, writeAt t (h) true⟩ := by
    simp [stepN, s0, s1]
  refine ⟨by simp [stepN, s0, s1, s2], ?_⟩
  intro k d hk hkd hP hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcase with rfl | rfl | rfl
  · have hdd : (⟨State.E, h, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hP
    simp at hP
  · rw [p1] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p2] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.B, h + 2, writeAt t (h) true⟩ : Config).tape (⟨State.B, h + 2, writeAt t (h) true⟩ : Config).head
        = (writeAt t (h) true) (h + 2) from rfl] at hread
    rw [hf1] at hread
    exact absurd hread (by simp)

/-- **March pair**: the first six steps of a cycle in isolation — the even-`a` partial segment before the edge business. -/
theorem march_pair {c : Config} {h : Int}
    (hs : c.state = State.E) (hh : c.head = h)
    (tp0 : c.tape (h) = false) (tp1 : c.tape (h + 1) = true)
    (tp2 : c.tape (h + 2) = true) (tp3 : c.tape (h + 3) = false)
    (tp4 : c.tape (h + 4) = true) (tp5 : c.tape (h + 5) = true)
    :
    stepN 6 c = some ⟨State.E, h + 6,
        writeAt (writeAt (writeAt (writeAt c.tape (h) true) (h + 2) false) (h + 3) true) (h + 5) false⟩ ∧
      BSafeSeg c 6 := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hs hh tp0 tp1 tp2 tp3 tp4 tp5
  subst hs
  have hp : h = hd := hh.symm
  subst hp
  have hf0 : (writeAt t (h) true) (h + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tp1
  have hf1 : (writeAt t (h) true) (h + 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tp2
  have hf2 : (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp3
  have hf3 : (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 4) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp4
  have hf4 : (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp5
  have s0 : step ⟨State.E, h, t⟩
      = some ⟨State.A, h + 1, writeAt t (h) true⟩ := by
    simp [step, instr, tp0, move]
    try omega
  have s1 : step ⟨State.A, h + 1, writeAt t (h) true⟩
      = some ⟨State.B, h + 2, writeAt t (h) true⟩ := by
    have hself := writeAt_self _ _ hf0
    simp [step, instr, hf0, move, hself]
    try omega
  have s2 : step ⟨State.B, h + 2, writeAt t (h) true⟩
      = some ⟨State.E, h + 3, writeAt (writeAt t (h) true) (h + 2) false⟩ := by
    simp [step, instr, hf1, move]
    try omega
  have s3 : step ⟨State.E, h + 3, writeAt (writeAt t (h) true) (h + 2) false⟩
      = some ⟨State.A, h + 4, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ := by
    simp [step, instr, hf2, move]
    try omega
  have s4 : step ⟨State.A, h + 4, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩
      = some ⟨State.B, h + 5, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ := by
    have hself := writeAt_self _ _ hf3
    simp [step, instr, hf3, move, hself]
    try omega
  have s5 : step ⟨State.B, h + 5, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩
      = some ⟨State.E, h + 6, writeAt (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) false⟩ := by
    simp [step, instr, hf4, move]
    try omega
  have p1 : stepN 1 ⟨State.E, h, t⟩ = some ⟨State.A, h + 1, writeAt t (h) true⟩ := by
    simp [stepN, s0]
  have p2 : stepN 2 ⟨State.E, h, t⟩ = some ⟨State.B, h + 2, writeAt t (h) true⟩ := by
    simp [stepN, s0, s1]
  have p3 : stepN 3 ⟨State.E, h, t⟩ = some ⟨State.E, h + 3, writeAt (writeAt t (h) true) (h + 2) false⟩ := by
    simp [stepN, s0, s1, s2]
  have p4 : stepN 4 ⟨State.E, h, t⟩ = some ⟨State.A, h + 4, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ := by
    simp [stepN, s0, s1, s2, s3]
  have p5 : stepN 5 ⟨State.E, h, t⟩ = some ⟨State.B, h + 5, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4]
  refine ⟨by simp [stepN, s0, s1, s2, s3, s4, s5], ?_⟩
  intro k d hk hkd hP hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl
  · have hdd : (⟨State.E, h, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hP
    simp at hP
  · rw [p1] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p2] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.B, h + 2, writeAt t (h) true⟩ : Config).tape (⟨State.B, h + 2, writeAt t (h) true⟩ : Config).head
        = (writeAt t (h) true) (h + 2) from rfl] at hread
    rw [hf1] at hread
    exact absurd hread (by simp)
  · rw [p3] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p4] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p5] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.B, h + 5, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ : Config).tape (⟨State.B, h + 5, writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true⟩ : Config).head
        = (writeAt (writeAt (writeAt t (h) true) (h + 2) false) (h + 3) true) (h + 5) from rfl] at hread
    rw [hf4] at hread
    exact absurd hread (by simp)


/-- A finite-support shape: `1` on `[l, r]` minus four (possibly
duplicated) hole positions, `0` outside.  Every spawn-entry tape of the
machine's eternal run has this form — the whole closure proof moves
between `holeTape`s. -/
def holeTape (l r a b c d : Int) : Int → Bool :=
  fun q =>
    if q = a ∨ q = b ∨ q = c ∨ q = d then false
    else if l ≤ q ∧ q ≤ r then true
    else false

theorem holeTape_hole {l r a b c d q : Int}
    (h : q = a ∨ q = b ∨ q = c ∨ q = d) :
    holeTape l r a b c d q = false := by
  unfold holeTape
  rw [if_pos h]

theorem holeTape_one {l r a b c d q : Int}
    (h1 : ¬(q = a ∨ q = b ∨ q = c ∨ q = d)) (h2 : l ≤ q) (h3 : q ≤ r) :
    holeTape l r a b c d q = true := by
  unfold holeTape
  rw [if_neg h1, if_pos ⟨h2, h3⟩]

theorem holeTape_out {l r a b c d q : Int}
    (h1 : ¬(q = a ∨ q = b ∨ q = c ∨ q = d)) (h2 : ¬(l ≤ q ∧ q ≤ r)) :
    holeTape l r a b c d q = false := by
  unfold holeTape
  rw [if_neg h1, if_neg h2]

end QIG.Dossier3RawTM

#print axioms QIG.Dossier3RawTM.halt_requires_b_probe_00
#print axioms QIG.Dossier3RawTM.blank_nonhalting_of_b_probe_safe
#print axioms QIG.Dossier3RawTM.bprobe_safe_of_segments
#print axioms QIG.Dossier3RawTM.bsafe_of_checkSafe
#print axioms QIG.Dossier3RawTM.step_E_on_one
#print axioms QIG.Dossier3RawTM.spawn_step
#print axioms QIG.Dossier3RawTM.sweep_EF
#print axioms QIG.Dossier3RawTM.cat_cycle
#print axioms QIG.Dossier3RawTM.spawn_variant_step
#print axioms QIG.Dossier3RawTM.cross_cycle
#print axioms QIG.Dossier3RawTM.term_cycle
#print axioms QIG.Dossier3RawTM.fuse_cycle
#print axioms QIG.Dossier3RawTM.edge_odd_seg
#print axioms QIG.Dossier3RawTM.edge_even_seg
#print axioms QIG.Dossier3RawTM.cat_run
#print axioms QIG.Dossier3RawTM.march_triple
#print axioms QIG.Dossier3RawTM.march_pair
