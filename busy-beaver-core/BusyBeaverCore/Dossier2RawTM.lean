import Lean.Elab.Tactic.Omega

/-!
# Dossier-2 raw semantics and halt localization

Bare-Lean model of the BB(6) holdout
`1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD` (stage757: exact orbit spec).

* halt in one step exactly at the undefined `E0`;
* state `E` is entered only via `C0` (write 1, move right);
* any raw halt passes through a reachable `C`-probe of a `00` pattern
  (the probed 0's RIGHT neighbour is also 0);
* `CProbeSafe blankStart → ¬ RawHalts blankStart` — the contract the
  machine's (future) certified orbit must discharge.
-/

namespace QIG.Dossier2RawTM

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

/-- The dossier-2 transition table.  `none` at `E0` is the halt. -/
def instr : State → Bool → Option Instr
  | State.A, false => some ⟨State.B, true, Dir.R⟩
  | State.A, true => some ⟨State.C, true, Dir.R⟩
  | State.B, false => some ⟨State.C, true, Dir.L⟩
  | State.B, true => some ⟨State.C, true, Dir.L⟩
  | State.C, false => some ⟨State.E, true, Dir.R⟩
  | State.C, true => some ⟨State.D, false, Dir.L⟩
  | State.D, false => some ⟨State.B, true, Dir.L⟩
  | State.D, true => some ⟨State.F, true, Dir.R⟩
  | State.E, false => none
  | State.E, true => some ⟨State.A, true, Dir.R⟩
  | State.F, false => some ⟨State.D, false, Dir.R⟩
  | State.F, true => some ⟨State.D, true, Dir.R⟩

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
    step c = none ↔ c.state = State.E ∧ c.tape c.head = false := by
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

/-- State `E` is entered only by `C` reading `0` (`C0 = 1RE`). -/
theorem into_E_only_from_C0 {c c' : Config} (h : step c = some c')
    (hE : c'.state = State.E) :
    c.state = State.C ∧ c.tape c.head = false ∧
      c'.head = c.head + 1 ∧ c'.tape = writeAt c.tape c.head true := by
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
run must first stand in `C` on a `0` whose right neighbour is also
`0`.  Same argument as its elder siblings: rewind to the last living
configuration, enter through the unique turnstile, observe the fatal cell
was not written by the entering step.

Halt localization: any raw halt from a non-`E` start forces a reachable
`C` reading a `0` whose RIGHT neighbour is also `0`. -/
theorem halt_requires_c_probe_00 {c : Config} (hne : c.state ≠ State.E)
    (hh : RawHalts c) :
    ∃ d : Config, Reaches c d ∧ d.state = State.C ∧
      d.tape d.head = false ∧ d.tape (d.head + 1) = false := by
  obtain ⟨n, hn⟩ := hh
  obtain ⟨k, _, d0, hd0, hstop⟩ := stepN_none_last n c hn
  have hE := (step_eq_none_iff d0).mp hstop
  cases k with
  | zero =>
      have hcd : c = d0 := by simpa [stepN] using hd0
      exact absurd (hcd ▸ hE.1) hne
  | succ k' =>
      obtain ⟨e, he, hstepe⟩ := stepN_some_pred k' c d0 hd0
      obtain ⟨hC, h0, hhead, htape⟩ := into_E_only_from_C0 hstepe hE.1
      refine ⟨e, ⟨k', he⟩, hC, h0, ?_⟩
      have hread : d0.tape d0.head = false := hE.2
      rw [htape, hhead] at hread
      rwa [writeAt_other e.tape e.head (e.head + 1) true (by omega)] at hread

/-- The C-probe-safety contract: every `0` that `C` reads has a `1` to its
right. -/
def CProbeSafe (c : Config) : Prop :=
  ∀ d : Config, Reaches c d → d.state = State.C → d.tape d.head = false →
    d.tape (d.head + 1) = true

theorem nonhalting_of_c_probe_safe {c : Config} (hne : c.state ≠ State.E)
    (hsafe : CProbeSafe c) : ¬ RawHalts c := by
  intro hh
  obtain ⟨d, hreach, hC, h0, h00⟩ := halt_requires_c_probe_00 hne hh
  have h1 := hsafe d hreach hC h0
  rw [h1] at h00
  exact Bool.noConfusion h00

theorem blank_nonhalting_of_c_probe_safe
    (hsafe : CProbeSafe blankStart) : ¬ RawHalts blankStart := by
  have hne : blankStart.state ≠ State.E := by
    simp [blankStart]
  exact nonhalting_of_c_probe_safe hne hsafe


/-!
## Orbit certification, layer 1: segment algebra, keystone, decider, atoms

The certified foundation beneath a future rule-by-rule orbit proof —
mirrors of the Antihydra development's machinery, instantiated for this
machine's probe shape.  Informally: everything here is machine-checked
scaffolding; the remaining climb is the rule trajectories of the stage757
spec, which will slot into `csafe_compose` and the keystone exactly as
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

/-- Informally: the machine's tape-preserving gait — `D` on a `1`
rewrites `1` over `1` and hands off to `F`, leaving the tape function
*literally equal*.  These two atoms are what block-crossing sweeps will be
built from. -/
theorem step_D_on_one {c : Config} (hs : c.state = State.D)
    (ht : c.tape c.head = true) :
    step c = some ⟨State.F, c.head + 1, c.tape⟩ := by
  have hw := writeAt_self c.tape c.head ht
  simp [step, instr, hs, ht, move, hw]

theorem step_F_on_one {c : Config} (hs : c.state = State.F)
    (ht : c.tape c.head = true) :
    step c = some ⟨State.D, c.head + 1, c.tape⟩ := by
  have hw := writeAt_self c.tape c.head ht
  simp [step, instr, hs, ht, move, hw]

/-- Conditional C-probe safety over the first `N` steps of a run. -/
def CSafeSeg (c : Config) (N : Nat) : Prop :=
  ∀ k d, k < N → stepN k c = some d → d.state = State.C →
    d.tape d.head = false → d.tape (d.head + 1) = true

theorem csafe_compose {c c' : Config} {m n : Nat}
    (hm : stepN m c = some c') (h1 : CSafeSeg c m) (h2 : CSafeSeg c' n) :
    CSafeSeg c (m + n) := by
  intro k d hk hkd hP hread
  by_cases hkm : k < m
  · exact h1 k d hkm hkd hP hread
  · have hkeq : k = m + (k - m) := by omega
    rw [hkeq, stepN_add, hm] at hkd
    exact h2 (k - m) d (by omega) hkd hP hread

/-- A segment in which every `C` configuration reads a `1` is safe. -/
theorem csafe_of_strong {c : Config} {N : Nat}
    (h : ∀ k d, k < N → stepN k c = some d → d.state = State.C →
      d.tape d.head = true) : CSafeSeg c N := by
  intro k d hk hkd hP hread
  rw [h k d hk hkd hP] at hread
  exact absurd hread (by simp)

/-- A segment with no `C` configuration at all is safe. -/
theorem csafe_of_noC {c : Config} {N : Nat}
    (h : ∀ k d, k < N → stepN k c = some d → d.state ≠ State.C) :
    CSafeSeg c N := by
  intro k d hk hkd hP _
  exact absurd hP (h k d hk hkd)

/-- The segment-induction keystone.  Informally: safety in pieces is
safety forever — an invariant maintained by positive safe segments gives
`CProbeSafe` for the whole infinite run, by strong induction on how many
segments precede any given moment. -/
theorem cprobe_safe_of_segments {Inv : Config → Prop} {c0 : Config}
    (h0 : Inv c0)
    (hseg : ∀ c, Inv c → ∃ k, 0 < k ∧ ∃ c', stepN k c = some c' ∧
      Inv c' ∧ CSafeSeg c k) :
    CProbeSafe c0 := by
  have main : ∀ (N n : Nat) (c : Config), n ≤ N → Inv c →
      ∀ d, stepN n c = some d → d.state = State.C →
        d.tape d.head = false → d.tape (d.head + 1) = true := by
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
theorem cprobe_safe_prefix {c d : Config} {M : Nat}
    (hM : stepN M c = some d)
    (hpre : CSafeSeg c M) (hpost : CProbeSafe d) : CProbeSafe c := by
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
  | State.C => c.tape c.head || c.tape (c.head + 1)
  | _ => true

def checkSafe : Nat → Config → Bool
  | 0, _ => true
  | k + 1, c =>
      safeCfg c &&
        (match step c with
         | none => true
         | some c' => checkSafe k c')

theorem safeCfg_spec {c : Config} (hC : c.state = State.C)
    (h : safeCfg c = true) (hr : c.tape c.head = false) :
    c.tape (c.head + 1) = true := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hC hr ⊢
  subst hC
  simp only [safeCfg] at h
  simp [hr] at h
  exact h

theorem csafe_of_checkSafe :
    ∀ (N : Nat) (c : Config), checkSafe N c = true → CSafeSeg c N := by
  intro N
  induction N with
  | zero =>
      intro c _ k d hk _ _ _
      exact absurd hk (by omega)
  | succ N ih =>
      intro c h k d hk hkd hC hread
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
          exact safeCfg_spec hC h1 hread
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
              exact ih c1 h2 j d (by omega) hkd hC hread


/-- **The dominant spawn rule**, certified (stage757 spec key
`(3, 4, sig)`, support ~150): a constant **7-step** frontier event.  From
a record head on the fresh frontier with the adjacent block at least three
deep, exactly seven raw steps split off a fresh 2-block:  the net tape
change is two cells (`p - 2 ↦ 0`, `p ↦ 1`), realizing the abstract map
`(x, y, z) → (x, y, z−2, 2)` at cost 7 — independent of every block size.

Informally: the machine's cheapest and commonest move — a purely local
stitch at the frontier, no sweeps required.  The single `C`-moment inside
reads a `1`, so the rule is probe-free and its safety certificate is
immediate. -/
theorem spawn_step {cfg : Config} {p : Int}
    (hs : cfg.state = State.D) (hh : cfg.head = p)
    (tf : cfg.tape p = false) (t1 : cfg.tape (p - 1) = true)
    (t2 : cfg.tape (p - 2) = true) (t3 : cfg.tape (p - 3) = true) :
    stepN 7 cfg = some ⟨State.D, p + 1,
        writeAt (writeAt cfg.tape p true) (p - 2) false⟩ ∧
      CSafeSeg cfg 7 := by
  obtain ⟨s, hd, t⟩ := cfg
  simp only at hs hh tf t1 t2 t3
  subst hs
  have hp : p = hd := hh.symm
  subst hp
  have hT1m1 : (writeAt t p true) (p - 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact t1
  have hT1m2 : (writeAt t p true) (p - 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact t2
  have hT1m3 : (writeAt t p true) (p - 3) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact t3
  have hT2m3 : (writeAt (writeAt t p true) (p - 2) false) (p - 3) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact hT1m3
  have hT2m2 : (writeAt (writeAt t p true) (p - 2) false) (p - 2) = false :=
    writeAt_same _ _ _
  have hT2m1 : (writeAt (writeAt t p true) (p - 2) false) (p - 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact hT1m1
  have hT2p : (writeAt (writeAt t p true) (p - 2) false) p = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact writeAt_same t p true
  have s0 : step ⟨State.D, p, t⟩
      = some ⟨State.B, p - 1, writeAt t p true⟩ := by
    simp [step, instr, tf, move]
    try omega
  have s1 : step ⟨State.B, p - 1, writeAt t p true⟩
      = some ⟨State.C, p - 2, writeAt t p true⟩ := by
    have hself := writeAt_self _ _ hT1m1
    simp [step, instr, hT1m1, move, hself]
    try omega
  have s2 : step ⟨State.C, p - 2, writeAt t p true⟩
      = some ⟨State.D, p - 3, writeAt (writeAt t p true) (p - 2) false⟩ := by
    simp [step, instr, hT1m2, move]
    try omega
  have s3 : step ⟨State.D, p - 3, writeAt (writeAt t p true) (p - 2) false⟩
      = some ⟨State.F, p - 2, writeAt (writeAt t p true) (p - 2) false⟩ := by
    have hself := writeAt_self _ _ hT2m3
    simp [step, instr, hT2m3, move, hself]
    try omega
  have s4 : step ⟨State.F, p - 2, writeAt (writeAt t p true) (p - 2) false⟩
      = some ⟨State.D, p - 1, writeAt (writeAt t p true) (p - 2) false⟩ := by
    have hself := writeAt_self _ _ hT2m2
    simp [step, instr, hT2m2, move, hself]
    try omega
  have s5 : step ⟨State.D, p - 1, writeAt (writeAt t p true) (p - 2) false⟩
      = some ⟨State.F, p, writeAt (writeAt t p true) (p - 2) false⟩ := by
    have hself := writeAt_self _ _ hT2m1
    simp [step, instr, hT2m1, move, hself]
    try omega
  have s6 : step ⟨State.F, p, writeAt (writeAt t p true) (p - 2) false⟩
      = some ⟨State.D, p + 1, writeAt (writeAt t p true) (p - 2) false⟩ := by
    have hself := writeAt_self _ _ hT2p
    simp [step, instr, hT2p, move, hself]
    try omega
  have p1 : stepN 1 ⟨State.D, p, t⟩
      = some ⟨State.B, p - 1, writeAt t p true⟩ := by simp [stepN, s0]
  have p2 : stepN 2 ⟨State.D, p, t⟩
      = some ⟨State.C, p - 2, writeAt t p true⟩ := by simp [stepN, s0, s1]
  have p3 : stepN 3 ⟨State.D, p, t⟩
      = some ⟨State.D, p - 3, writeAt (writeAt t p true) (p - 2) false⟩ := by
    simp [stepN, s0, s1, s2]
  have p4 : stepN 4 ⟨State.D, p, t⟩
      = some ⟨State.F, p - 2, writeAt (writeAt t p true) (p - 2) false⟩ := by
    simp [stepN, s0, s1, s2, s3]
  have p5 : stepN 5 ⟨State.D, p, t⟩
      = some ⟨State.D, p - 1, writeAt (writeAt t p true) (p - 2) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4]
  have p6 : stepN 6 ⟨State.D, p, t⟩
      = some ⟨State.F, p, writeAt (writeAt t p true) (p - 2) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5]
  refine ⟨by simp [stepN, s0, s1, s2, s3, s4, s5, s6], ?_⟩
  intro k d hk hkd hC hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by
    omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hdd : (⟨State.D, p, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hC; simp at hC
  · rw [p1] at hkd
    rw [← Option.some_inj.mp hkd] at hC; simp at hC
  · rw [p2] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.C, p - 2, writeAt t p true⟩ : Config).tape
          (⟨State.C, p - 2, writeAt t p true⟩ : Config).head
        = (writeAt t p true) (p - 2) from rfl] at hread
    rw [hT1m2] at hread
    exact absurd hread (by simp)
  · rw [p3] at hkd
    rw [← Option.some_inj.mp hkd] at hC; simp at hC
  · rw [p4] at hkd
    rw [← Option.some_inj.mp hkd] at hC; simp at hC
  · rw [p5] at hkd
    rw [← Option.some_inj.mp hkd] at hC; simp at hC
  · rw [p6] at hkd
    rw [← Option.some_inj.mp hkd] at hC; simp at hC


/-- **The sweep-pair induction**: the `D↔F` gait crosses `2n` ones
without touching the tape.  Informally: the return stroke of the traversal
rule — each pair of steps rewrites `1` over `1` twice (D then F),
so after any number of pairs the tape function is *literally unchanged*
and the head has moved `2n` cells.  Built by induction on the pair count
from the two proven atoms. -/
theorem sweep_DF :
    ∀ (n : Nat) (c : Config), c.state = State.D →
      (∀ i : Nat, i < 2 * n → c.tape (c.head + i) = true) →
      stepN (2 * n) c = some ⟨State.D, c.head + (2 * n : Int), c.tape⟩ := by
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
      have h1 : c.tape (c.head + 1) = true := by
        have := hones 1 (by omega)
        rwa [show c.head + ((1 : Nat) : Int) = c.head + 1 by omega] at this
      have hstep1 := step_D_on_one hs h0
      have hstep2 : step ⟨State.F, c.head + 1, c.tape⟩
          = some ⟨State.D, c.head + 1 + 1, c.tape⟩ :=
        step_F_on_one rfl h1
      have hnext := ih ⟨State.D, c.head + 1 + 1, c.tape⟩ rfl
        (fun i hi => by
          have := hones (i + 2) (by omega)
          show c.tape (c.head + 1 + 1 + (i : Int)) = true
          rwa [show c.head + ((i + 2 : Nat) : Int)
                = c.head + 1 + 1 + (i : Int) by omega] at this)
      have a2 : stepN 2 c = some ⟨State.D, c.head + 1 + 1, c.tape⟩ := by
        simp [stepN, hstep1, hstep2]
      have hcomp : stepN (2 * (n + 1)) c
          = (stepN 2 c).bind (stepN (2 * n)) := by
        rw [show 2 * (n + 1) = 2 + 2 * n by omega, stepN_add]
      simp only at hnext
      rw [hcomp, a2]
      show stepN (2 * n) ⟨State.D, c.head + 1 + 1, c.tape⟩
          = some ⟨State.D, c.head + (2 * ((n + 1 : Nat) : Int)), c.tape⟩
      rw [hnext,
          show c.head + 1 + 1 + 2 * (n : Int)
            = c.head + 2 * ((n + 1 : Nat) : Int) from by omega]


/-- **The caterpillar cycle** of the traversal rule: ten raw steps, net
two cells of travel, four tape writes, and both `C`-moments read a `1`.

Informally: the machine's traversal gait — three steps marching, three
more marching, then the `D↔F` pair backing up four; the cycle
carries a moving 0-hole (at offset 3) and consumes two fresh `1`s per
iteration.  This is the unbounded middle of the traversal rule; iterating
it (`cat_run`-style) and bolting on the boundary segments yields the full
`6y + 6z + 1` trajectory. -/
theorem cat_cycle {c : Config} {h : Int}
    (hs : c.state = State.D) (hh : c.head = h)
    (t0 : c.tape h = false)
    (t1 : c.tape (h - 1) = true) (t2 : c.tape (h - 2) = true)
    (t3 : c.tape (h - 3) = false)
    (t4 : c.tape (h - 4) = true) (t5 : c.tape (h - 5) = true)
    (t6 : c.tape (h - 6) = true) :
    stepN 10 c = some ⟨State.D, h - 2, writeAt (writeAt (writeAt (writeAt c.tape h true) (h - 2) false) (h - 3) true) (h - 5) false⟩ ∧ CSafeSeg c 10 := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hs hh t0 t1 t2 t3 t4 t5 t6
  subst hs
  have hp : h = hd := hh.symm
  subst hp
  have hT1m1 : (writeAt t h true) (h - 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact t1
  have hT1m2 : (writeAt t h true) (h - 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact t2
  have hT2m3 : (writeAt (writeAt t h true) (h - 2) false) (h - 3) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact t3
  have hT3m4 : (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 4) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega)]
    exact t4
  have hT3m5 : (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 5) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega)]
    exact t5
  have hT4m6 : (writeAt (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega),
        writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact t6
  have hT4m5 : (writeAt (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 5) = false := writeAt_same _ _ _
  have hT4m4 : (writeAt (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 4) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]; exact hT3m4
  have hT4m3 : (writeAt (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 3) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have s0 : step ⟨State.D, h, t⟩ = some ⟨State.B, h - 1, writeAt t h true⟩ := by
    simp [step, instr, t0, move]
    try omega
  have s1 : step ⟨State.B, h - 1, writeAt t h true⟩
      = some ⟨State.C, h - 2, writeAt t h true⟩ := by
    have hself := writeAt_self _ _ hT1m1
    simp [step, instr, hT1m1, move, hself]
    try omega
  have s2 : step ⟨State.C, h - 2, writeAt t h true⟩
      = some ⟨State.D, h - 3, writeAt (writeAt t h true) (h - 2) false⟩ := by
    simp [step, instr, hT1m2, move]
    try omega
  have s3 : step ⟨State.D, h - 3, writeAt (writeAt t h true) (h - 2) false⟩
      = some ⟨State.B, h - 4, writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true⟩ := by
    simp [step, instr, hT2m3, move]
    try omega
  have s4 : step ⟨State.B, h - 4, writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true⟩
      = some ⟨State.C, h - 5, writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true⟩ := by
    have hself := writeAt_self _ _ hT3m4
    simp [step, instr, hT3m4, move, hself]
    try omega
  have s5 : step ⟨State.C, h - 5, writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true⟩
      = some ⟨State.D, h - 6, writeAt (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 5) false⟩ := by
    simp [step, instr, hT3m5, move]
    try omega
  have s6 : step ⟨State.D, h - 6, writeAt (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 5) false⟩
      = some ⟨State.F, h - 5, writeAt (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 5) false⟩ := by
    have hself := writeAt_self _ _ hT4m6
    simp [step, instr, hT4m6, move, hself]
    try omega
  have s7 : step ⟨State.F, h - 5, writeAt (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 5) false⟩
      = some ⟨State.D, h - 4, writeAt (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 5) false⟩ := by
    have hself := writeAt_self _ _ hT4m5
    simp [step, instr, hT4m5, move, hself]
    try omega
  have s8 : step ⟨State.D, h - 4, writeAt (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 5) false⟩
      = some ⟨State.F, h - 3, writeAt (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 5) false⟩ := by
    have hself := writeAt_self _ _ hT4m4
    simp [step, instr, hT4m4, move, hself]
    try omega
  have s9 : step ⟨State.F, h - 3, writeAt (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 5) false⟩
      = some ⟨State.D, h - 2, writeAt (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 5) false⟩ := by
    have hself := writeAt_self _ _ hT4m3
    simp [step, instr, hT4m3, move, hself]
    try omega
  have p1 : stepN 1 ⟨State.D, h, t⟩ = some ⟨State.B, h - 1, writeAt t h true⟩ := by
    simp [stepN, s0]
  have p2 : stepN 2 ⟨State.D, h, t⟩ = some ⟨State.C, h - 2, writeAt t h true⟩ := by
    simp [stepN, s0, s1]
  have p3 : stepN 3 ⟨State.D, h, t⟩ = some ⟨State.D, h - 3, writeAt (writeAt t h true) (h - 2) false⟩ := by
    simp [stepN, s0, s1, s2]
  have p4 : stepN 4 ⟨State.D, h, t⟩ = some ⟨State.B, h - 4, writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true⟩ := by
    simp [stepN, s0, s1, s2, s3]
  have p5 : stepN 5 ⟨State.D, h, t⟩ = some ⟨State.C, h - 5, writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4]
  have p6 : stepN 6 ⟨State.D, h, t⟩ = some ⟨State.D, h - 6, writeAt (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 5) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5]
  have p7 : stepN 7 ⟨State.D, h, t⟩ = some ⟨State.F, h - 5, writeAt (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 5) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6]
  have p8 : stepN 8 ⟨State.D, h, t⟩ = some ⟨State.D, h - 4, writeAt (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 5) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7]
  have p9 : stepN 9 ⟨State.D, h, t⟩ = some ⟨State.F, h - 3, writeAt (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 5) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8]
  refine ⟨by simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9], ?_⟩
  intro k d hk hkd hC hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
      k = 7 ∨ k = 8 ∨ k = 9 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hdd : (⟨State.D, h, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hC; simp at hC
  · rw [p1] at hkd; rw [← Option.some_inj.mp hkd] at hC; simp at hC
  · rw [p2] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.C, h - 2, writeAt t h true⟩ : Config).tape
          (⟨State.C, h - 2, writeAt t h true⟩ : Config).head
        = (writeAt t h true) (h - 2) from rfl] at hread
    rw [hT1m2] at hread
    exact absurd hread (by simp)
  · rw [p3] at hkd; rw [← Option.some_inj.mp hkd] at hC; simp at hC
  · rw [p4] at hkd; rw [← Option.some_inj.mp hkd] at hC; simp at hC
  · rw [p5] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.C, h - 5, writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true⟩ : Config).tape
          (⟨State.C, h - 5, writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true⟩ : Config).head
        = (writeAt (writeAt (writeAt t h true) (h - 2) false) (h - 3) true) (h - 5) from rfl] at hread
    rw [hT3m5] at hread
    exact absurd hread (by simp)
  · rw [p6] at hkd; rw [← Option.some_inj.mp hkd] at hC; simp at hC
  · rw [p7] at hkd; rw [← Option.some_inj.mp hkd] at hC; simp at hC
  · rw [p8] at hkd; rw [← Option.some_inj.mp hkd] at hC; simp at hC
  · rw [p9] at hkd; rw [← Option.some_inj.mp hkd] at hC; simp at hC


/-- State `F` preserves whatever it reads (`F0=0RD`, `F1=1RD`): one step
right, tape literally unchanged.  This is why the return sweep can cross
holes: the `F`-cells of the gait carry no constraint at all. -/
theorem step_F_any {c : Config} (hs : c.state = State.F) :
    step c = some ⟨State.D, c.head + 1, c.tape⟩ := by
  cases hb : c.tape c.head
  · simp [step, instr, hs, hb, move, writeAt_self c.tape c.head hb]
  · simp [step, instr, hs, hb, move, writeAt_self c.tape c.head hb]

/-- **The mixed sweep**: the `D↔F` return gait needs `1`s only on the
`D`-cells (even offsets); the `F`-cells are arbitrary and *preserved*.
Informally: the sweep crosses interior holes for free, provided every
hole sits at `F`-parity — which is exactly what the `+4/+6/+9` shifts
of the interaction calculus maintain. -/
theorem sweep_mixed :
    ∀ (n : Nat) (c : Config), c.state = State.D →
      (∀ i : Nat, i < n → c.tape (c.head + 2 * i) = true) →
      stepN (2 * n) c = some ⟨State.D, c.head + (2 * n : Int), c.tape⟩ := by
  intro n
  induction n with
  | zero => intro c hs _; obtain ⟨s, h, t⟩ := c; simp_all [stepN]
  | succ n ih =>
      intro c hs hones
      have h0 : c.tape c.head = true := by
        have := hones 0 (by omega); simpa using this
      have hstep1 := step_D_on_one hs h0
      have hstep2 : step ⟨State.F, c.head + 1, c.tape⟩
          = some ⟨State.D, c.head + 1 + 1, c.tape⟩ := step_F_any rfl
      have hnext := ih ⟨State.D, c.head + 1 + 1, c.tape⟩ rfl
        (fun i hi => by
          have := hones (i + 1) (by omega)
          show c.tape (c.head + 1 + 1 + 2 * (i : Int)) = true
          rwa [show c.head + 2 * ((i + 1 : Nat) : Int)
                = c.head + 1 + 1 + 2 * (i : Int) by omega] at this)
      have a2 : stepN 2 c = some ⟨State.D, c.head + 1 + 1, c.tape⟩ := by
        simp [stepN, hstep1, hstep2]
      have hcomp : stepN (2 * (n + 1)) c
          = (stepN 2 c).bind (stepN (2 * n)) := by
        rw [show 2 * (n + 1) = 2 + 2 * n by omega, stepN_add]
      simp only at hnext
      rw [hcomp, a2]
      show stepN (2 * n) ⟨State.D, c.head + 1 + 1, c.tape⟩
          = some ⟨State.D, c.head + (2 * ((n + 1 : Nat) : Int)), c.tape⟩
      rw [hnext,
          show c.head + 1 + 1 + 2 * (n : Int)
            = c.head + 2 * ((n + 1 : Nat) : Int) from by omega]

/-- The mixed sweep never enters the danger state, so it is trivially
probe-safe for its whole duration. -/
theorem sweep_mixed_safe :
    ∀ (n : Nat) (c : Config), c.state = State.D →
      (∀ i : Nat, i < n → c.tape (c.head + 2 * i) = true) →
      CSafeSeg c (2 * n) := by
  intro n
  induction n with
  | zero => intro c _ _ k d hk; exact absurd hk (by omega)
  | succ n ih =>
      intro c hs hones
      have h0 : c.tape c.head = true := by
        have := hones 0 (by omega); simpa using this
      have hstep1 := step_D_on_one hs h0
      have hstep2 : step ⟨State.F, c.head + 1, c.tape⟩
          = some ⟨State.D, c.head + 1 + 1, c.tape⟩ := step_F_any rfl
      have a2 : stepN 2 c = some ⟨State.D, c.head + 1 + 1, c.tape⟩ := by
        simp [stepN, hstep1, hstep2]
      have hsafe2 : CSafeSeg c 2 := by
        intro k d hk hkd hP hread
        have hk01 : k = 0 ∨ k = 1 := by omega
        rcases hk01 with rfl | rfl
        · have hdd : c = d := by simpa [stepN] using hkd
          rw [← hdd] at hP
          rw [hs] at hP
          exact absurd hP (by simp)
        · have h1 : stepN 1 c = some ⟨State.F, c.head + 1, c.tape⟩ := by
            simp [stepN, hstep1]
          rw [h1] at hkd
          rw [← Option.some_inj.mp hkd] at hP
          exact absurd hP (by simp)
      have hnext := ih ⟨State.D, c.head + 1 + 1, c.tape⟩ rfl
        (fun i hi => by
          have := hones (i + 1) (by omega)
          show c.tape (c.head + 1 + 1 + 2 * (i : Int)) = true
          rwa [show c.head + 2 * ((i + 1 : Nat) : Int)
                = c.head + 1 + 1 + 2 * (i : Int) by omega] at this)
      have hc : CSafeSeg c (2 + 2 * n) := csafe_compose a2 hsafe2 hnext
      rw [show 2 * (n + 1) = 2 + 2 * n by omega]
      exact hc


/-- **Spawn over the edge hole**: when the fresh-edge hole sits at `r−1` (the aftermath of a fuse), the 7-step spawn variant fills it, digs at `r−2`, and hands the machine back at `r+1`.  All D2 probe-moments read 1. -/
theorem spawn_variant_step {c : Config} {h : Int}
    (hs : c.state = State.D) (hh : c.head = h)
    (tm3 : c.tape (h - 3) = true) (tm2 : c.tape (h - 2) = true)
    (tm1 : c.tape (h - 1) = false) (tp0 : c.tape (h) = false)
    :
    stepN 7 c = some ⟨State.D, h + 1,
        writeAt (writeAt (writeAt c.tape (h) true) (h - 1) true) (h - 2) false⟩ ∧
      CSafeSeg c 7 := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hs hh tm3 tm2 tm1 tp0
  subst hs
  have hp : h = hd := hh.symm
  subst hp
  have hf0 : (writeAt t (h) true) (h - 1) = false := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tm1
  have hf1 : (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm2
  have hf2 : (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) false) (h - 3) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm3
  have hf3 : (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) false) (h - 2) = false := writeAt_same _ _ _
  have hf4 : (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) false) (h - 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf5 : (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) false) (h) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have s0 : step ⟨State.D, h, t⟩
      = some ⟨State.B, h - 1, writeAt t (h) true⟩ := by
    simp [step, instr, tp0, move]
    try omega
  have s1 : step ⟨State.B, h - 1, writeAt t (h) true⟩
      = some ⟨State.C, h - 2, writeAt (writeAt t (h) true) (h - 1) true⟩ := by
    simp [step, instr, hf0, move]
    try omega
  have s2 : step ⟨State.C, h - 2, writeAt (writeAt t (h) true) (h - 1) true⟩
      = some ⟨State.D, h - 3, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) false⟩ := by
    simp [step, instr, hf1, move]
    try omega
  have s3 : step ⟨State.D, h - 3, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) false⟩
      = some ⟨State.F, h - 2, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) false⟩ := by
    have hself := writeAt_self _ _ hf2
    simp [step, instr, hf2, move, hself]
    try omega
  have s4 : step ⟨State.F, h - 2, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) false⟩
      = some ⟨State.D, h - 1, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) false⟩ := by
    have hself := writeAt_self _ _ hf3
    simp [step, instr, hf3, move, hself]
    try omega
  have s5 : step ⟨State.D, h - 1, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) false⟩
      = some ⟨State.F, h, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) false⟩ := by
    have hself := writeAt_self _ _ hf4
    simp [step, instr, hf4, move, hself]
    try omega
  have s6 : step ⟨State.F, h, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) false⟩
      = some ⟨State.D, h + 1, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) false⟩ := by
    have hself := writeAt_self _ _ hf5
    simp [step, instr, hf5, move, hself]
    try omega
  have p1 : stepN 1 ⟨State.D, h, t⟩ = some ⟨State.B, h - 1, writeAt t (h) true⟩ := by
    simp [stepN, s0]
  have p2 : stepN 2 ⟨State.D, h, t⟩ = some ⟨State.C, h - 2, writeAt (writeAt t (h) true) (h - 1) true⟩ := by
    simp [stepN, s0, s1]
  have p3 : stepN 3 ⟨State.D, h, t⟩ = some ⟨State.D, h - 3, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) false⟩ := by
    simp [stepN, s0, s1, s2]
  have p4 : stepN 4 ⟨State.D, h, t⟩ = some ⟨State.F, h - 2, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) false⟩ := by
    simp [stepN, s0, s1, s2, s3]
  have p5 : stepN 5 ⟨State.D, h, t⟩ = some ⟨State.D, h - 1, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4]
  have p6 : stepN 6 ⟨State.D, h, t⟩ = some ⟨State.F, h, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5]
  refine ⟨by simp [stepN, s0, s1, s2, s3, s4, s5, s6], ?_⟩
  intro k d hk hkd hP hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hdd : (⟨State.D, h, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hP
    simp at hP
  · rw [p1] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p2] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.C, h - 2, writeAt (writeAt t (h) true) (h - 1) true⟩ : Config).tape (⟨State.C, h - 2, writeAt (writeAt t (h) true) (h - 1) true⟩ : Config).head
        = (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) from rfl] at hread
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

/-- **Hole crossing**: when a static hole aligns at offset 6 of the caterpillar cycle (even arrival parity), the march extends to three triples and the cycle absorbs the hole — net effect: the hole reappears 4 cells to the right (the cat's own trail hole at `h−2` becomes static) and the front lands at `h−5`, flipping the arrival parity for the next static.  13 steps, probe-free. -/
theorem cross_cycle {c : Config} {h : Int}
    (hs : c.state = State.D) (hh : c.head = h)
    (tm9 : c.tape (h - 9) = true) (tm8 : c.tape (h - 8) = true)
    (tm7 : c.tape (h - 7) = true) (tm6 : c.tape (h - 6) = false)
    (tm5 : c.tape (h - 5) = true) (tm4 : c.tape (h - 4) = true)
    (tm3 : c.tape (h - 3) = false) (tm2 : c.tape (h - 2) = true)
    (tm1 : c.tape (h - 1) = true) (tp0 : c.tape (h) = false)
    :
    stepN 13 c = some ⟨State.D, h - 5,
        writeAt (writeAt (writeAt (writeAt (writeAt (writeAt c.tape (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) false⟩ ∧
      CSafeSeg c 13 := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hs hh tm9 tm8 tm7 tm6 tm5 tm4 tm3 tm2 tm1 tp0
  subst hs
  have hp : h = hd := hh.symm
  subst hp
  have hf0 : (writeAt t (h) true) (h - 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tm1
  have hf1 : (writeAt t (h) true) (h - 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tm2
  have hf2 : (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm3
  have hf3 : (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 4) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm4
  have hf4 : (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm5
  have hf5 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm6
  have hf6 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 7) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm7
  have hf7 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm8
  have hf8 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) false) (h - 9) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm9
  have hf9 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) false) (h - 8) = false := writeAt_same _ _ _
  have hf10 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) false) (h - 7) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm7
  have hf11 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) false) (h - 6) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have s0 : step ⟨State.D, h, t⟩
      = some ⟨State.B, h - 1, writeAt t (h) true⟩ := by
    simp [step, instr, tp0, move]
    try omega
  have s1 : step ⟨State.B, h - 1, writeAt t (h) true⟩
      = some ⟨State.C, h - 2, writeAt t (h) true⟩ := by
    have hself := writeAt_self _ _ hf0
    simp [step, instr, hf0, move, hself]
    try omega
  have s2 : step ⟨State.C, h - 2, writeAt t (h) true⟩
      = some ⟨State.D, h - 3, writeAt (writeAt t (h) true) (h - 2) false⟩ := by
    simp [step, instr, hf1, move]
    try omega
  have s3 : step ⟨State.D, h - 3, writeAt (writeAt t (h) true) (h - 2) false⟩
      = some ⟨State.B, h - 4, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩ := by
    simp [step, instr, hf2, move]
    try omega
  have s4 : step ⟨State.B, h - 4, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩
      = some ⟨State.C, h - 5, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩ := by
    have hself := writeAt_self _ _ hf3
    simp [step, instr, hf3, move, hself]
    try omega
  have s5 : step ⟨State.C, h - 5, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩
      = some ⟨State.D, h - 6, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false⟩ := by
    simp [step, instr, hf4, move]
    try omega
  have s6 : step ⟨State.D, h - 6, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false⟩
      = some ⟨State.B, h - 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true⟩ := by
    simp [step, instr, hf5, move]
    try omega
  have s7 : step ⟨State.B, h - 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true⟩
      = some ⟨State.C, h - 8, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true⟩ := by
    have hself := writeAt_self _ _ hf6
    simp [step, instr, hf6, move, hself]
    try omega
  have s8 : step ⟨State.C, h - 8, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true⟩
      = some ⟨State.D, h - 9, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) false⟩ := by
    simp [step, instr, hf7, move]
    try omega
  have s9 : step ⟨State.D, h - 9, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) false⟩
      = some ⟨State.F, h - 8, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) false⟩ := by
    have hself := writeAt_self _ _ hf8
    simp [step, instr, hf8, move, hself]
    try omega
  have s10 : step ⟨State.F, h - 8, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) false⟩
      = some ⟨State.D, h - 7, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) false⟩ := by
    have hself := writeAt_self _ _ hf9
    simp [step, instr, hf9, move, hself]
    try omega
  have s11 : step ⟨State.D, h - 7, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) false⟩
      = some ⟨State.F, h - 6, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) false⟩ := by
    have hself := writeAt_self _ _ hf10
    simp [step, instr, hf10, move, hself]
    try omega
  have s12 : step ⟨State.F, h - 6, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) false⟩
      = some ⟨State.D, h - 5, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) false⟩ := by
    have hself := writeAt_self _ _ hf11
    simp [step, instr, hf11, move, hself]
    try omega
  have p1 : stepN 1 ⟨State.D, h, t⟩ = some ⟨State.B, h - 1, writeAt t (h) true⟩ := by
    simp [stepN, s0]
  have p2 : stepN 2 ⟨State.D, h, t⟩ = some ⟨State.C, h - 2, writeAt t (h) true⟩ := by
    simp [stepN, s0, s1]
  have p3 : stepN 3 ⟨State.D, h, t⟩ = some ⟨State.D, h - 3, writeAt (writeAt t (h) true) (h - 2) false⟩ := by
    simp [stepN, s0, s1, s2]
  have p4 : stepN 4 ⟨State.D, h, t⟩ = some ⟨State.B, h - 4, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩ := by
    simp [stepN, s0, s1, s2, s3]
  have p5 : stepN 5 ⟨State.D, h, t⟩ = some ⟨State.C, h - 5, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4]
  have p6 : stepN 6 ⟨State.D, h, t⟩ = some ⟨State.D, h - 6, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5]
  have p7 : stepN 7 ⟨State.D, h, t⟩ = some ⟨State.B, h - 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6]
  have p8 : stepN 8 ⟨State.D, h, t⟩ = some ⟨State.C, h - 8, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7]
  have p9 : stepN 9 ⟨State.D, h, t⟩ = some ⟨State.D, h - 9, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8]
  have p10 : stepN 10 ⟨State.D, h, t⟩ = some ⟨State.F, h - 8, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9]
  have p11 : stepN 11 ⟨State.D, h, t⟩ = some ⟨State.D, h - 7, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]
  have p12 : stepN 12 ⟨State.D, h, t⟩ = some ⟨State.F, h - 6, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  refine ⟨by simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12], ?_⟩
  intro k d hk hkd hP hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hdd : (⟨State.D, h, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hP
    simp at hP
  · rw [p1] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p2] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.C, h - 2, writeAt t (h) true⟩ : Config).tape (⟨State.C, h - 2, writeAt t (h) true⟩ : Config).head
        = (writeAt t (h) true) (h - 2) from rfl] at hread
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
    rw [show (⟨State.C, h - 5, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩ : Config).tape (⟨State.C, h - 5, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩ : Config).head
        = (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) from rfl] at hread
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
    rw [show (⟨State.C, h - 8, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true⟩ : Config).tape (⟨State.C, h - 8, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true⟩ : Config).head
        = (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) from rfl] at hread
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

/-- **Termination at a hole** (odd arrival parity): the second `C`-moment of the cycle reads the static `0` — the E-A-C business chain fills it and the trail, then plants the new hole 6 cells right and pivots into the return sweep at `F(h+1)`.  The two danger reads both have a `1` on the probe side — these are the only probe-moments of the whole traversal.  13 steps. -/
theorem term_cycle {c : Config} {h : Int}
    (hs : c.state = State.D) (hh : c.head = h)
    (tm5 : c.tape (h - 5) = false) (tm4 : c.tape (h - 4) = true)
    (tm3 : c.tape (h - 3) = false) (tm2 : c.tape (h - 2) = true)
    (tm1 : c.tape (h - 1) = true) (tp0 : c.tape (h) = false)
    (tp1 : c.tape (h + 1) = true)
    :
    stepN 13 c = some ⟨State.F, h + 1,
        writeAt (writeAt (writeAt (writeAt (writeAt (writeAt c.tape (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true) (h + 1) false⟩ ∧
      CSafeSeg c 13 := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hs hh tm5 tm4 tm3 tm2 tm1 tp0 tp1
  subst hs
  have hp : h = hd := hh.symm
  subst hp
  have hf0 : (writeAt t (h) true) (h - 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tm1
  have hf1 : (writeAt t (h) true) (h - 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tm2
  have hf2 : (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm3
  have hf3 : (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 4) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm4
  have hf4 : (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm5
  have hf5 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 4) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm4
  have hf6 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 3) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf7 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf8 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true) (h - 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm1
  have hf9 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true) (h) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf10 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true) (h + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp1
  have hf11 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true) (h + 1) false) (h) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf12 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm1
  have s0 : step ⟨State.D, h, t⟩
      = some ⟨State.B, h - 1, writeAt t (h) true⟩ := by
    simp [step, instr, tp0, move]
    try omega
  have s1 : step ⟨State.B, h - 1, writeAt t (h) true⟩
      = some ⟨State.C, h - 2, writeAt t (h) true⟩ := by
    have hself := writeAt_self _ _ hf0
    simp [step, instr, hf0, move, hself]
    try omega
  have s2 : step ⟨State.C, h - 2, writeAt t (h) true⟩
      = some ⟨State.D, h - 3, writeAt (writeAt t (h) true) (h - 2) false⟩ := by
    simp [step, instr, hf1, move]
    try omega
  have s3 : step ⟨State.D, h - 3, writeAt (writeAt t (h) true) (h - 2) false⟩
      = some ⟨State.B, h - 4, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩ := by
    simp [step, instr, hf2, move]
    try omega
  have s4 : step ⟨State.B, h - 4, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩
      = some ⟨State.C, h - 5, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩ := by
    have hself := writeAt_self _ _ hf3
    simp [step, instr, hf3, move, hself]
    try omega
  have s5 : step ⟨State.C, h - 5, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩
      = some ⟨State.E, h - 4, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true⟩ := by
    simp [step, instr, hf4, move]
    try omega
  have s6 : step ⟨State.E, h - 4, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true⟩
      = some ⟨State.A, h - 3, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true⟩ := by
    have hself := writeAt_self _ _ hf5
    simp [step, instr, hf5, move, hself]
    try omega
  have s7 : step ⟨State.A, h - 3, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true⟩
      = some ⟨State.C, h - 2, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true⟩ := by
    have hself := writeAt_self _ _ hf6
    simp [step, instr, hf6, move, hself]
    try omega
  have s8 : step ⟨State.C, h - 2, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true⟩
      = some ⟨State.E, h - 1, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true⟩ := by
    simp [step, instr, hf7, move]
    try omega
  have s9 : step ⟨State.E, h - 1, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true⟩
      = some ⟨State.A, h, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true⟩ := by
    have hself := writeAt_self _ _ hf8
    simp [step, instr, hf8, move, hself]
    try omega
  have s10 : step ⟨State.A, h, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true⟩
      = some ⟨State.C, h + 1, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true⟩ := by
    have hself := writeAt_self _ _ hf9
    simp [step, instr, hf9, move, hself]
    try omega
  have s11 : step ⟨State.C, h + 1, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true⟩
      = some ⟨State.D, h, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true) (h + 1) false⟩ := by
    simp [step, instr, hf10, move]
    try omega
  have s12 : step ⟨State.D, h, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true) (h + 1) false⟩
      = some ⟨State.F, h + 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true) (h + 1) false⟩ := by
    have hself := writeAt_self _ _ hf11
    simp [step, instr, hf11, move, hself]
    try omega
  have p1 : stepN 1 ⟨State.D, h, t⟩ = some ⟨State.B, h - 1, writeAt t (h) true⟩ := by
    simp [stepN, s0]
  have p2 : stepN 2 ⟨State.D, h, t⟩ = some ⟨State.C, h - 2, writeAt t (h) true⟩ := by
    simp [stepN, s0, s1]
  have p3 : stepN 3 ⟨State.D, h, t⟩ = some ⟨State.D, h - 3, writeAt (writeAt t (h) true) (h - 2) false⟩ := by
    simp [stepN, s0, s1, s2]
  have p4 : stepN 4 ⟨State.D, h, t⟩ = some ⟨State.B, h - 4, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩ := by
    simp [stepN, s0, s1, s2, s3]
  have p5 : stepN 5 ⟨State.D, h, t⟩ = some ⟨State.C, h - 5, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4]
  have p6 : stepN 6 ⟨State.D, h, t⟩ = some ⟨State.E, h - 4, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5]
  have p7 : stepN 7 ⟨State.D, h, t⟩ = some ⟨State.A, h - 3, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6]
  have p8 : stepN 8 ⟨State.D, h, t⟩ = some ⟨State.C, h - 2, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7]
  have p9 : stepN 9 ⟨State.D, h, t⟩ = some ⟨State.E, h - 1, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8]
  have p10 : stepN 10 ⟨State.D, h, t⟩ = some ⟨State.A, h, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9]
  have p11 : stepN 11 ⟨State.D, h, t⟩ = some ⟨State.C, h + 1, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]
  have p12 : stepN 12 ⟨State.D, h, t⟩ = some ⟨State.D, h, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true) (h + 1) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  refine ⟨by simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12], ?_⟩
  intro k d hk hkd hP hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hdd : (⟨State.D, h, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hP
    simp at hP
  · rw [p1] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p2] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.C, h - 2, writeAt t (h) true⟩ : Config).tape (⟨State.C, h - 2, writeAt t (h) true⟩ : Config).head
        = (writeAt t (h) true) (h - 2) from rfl] at hread
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
    show (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5 + 1) = true
    rw [show h - 5 + 1 = h - 4 by omega]
    exact hf3
  · rw [p6] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p7] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p8] at hkd
    rw [← Option.some_inj.mp hkd]
    show (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2 + 1) = true
    rw [show h - 2 + 1 = h - 1 by omega]
    exact hf12
  · rw [p9] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p10] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p11] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.C, h + 1, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true⟩ : Config).tape (⟨State.C, h + 1, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true⟩ : Config).head
        = (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) true) (h - 2) true) (h + 1) from rfl] at hread
    rw [hf10] at hread
    exact absurd hread (by simp)
  · rw [p12] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP

/-- **Hole fusion** (`b = 1`): the march reaches the adjacent hole pair; the E-A-C chain runs three fills instead of two, planting the fused hole 9 cells right of the lower hole and exiting into a parity-shifted return sweep.  19 steps, three probe-moments, all safe. -/
theorem fuse_cycle {c : Config} {h : Int}
    (hs : c.state = State.D) (hh : c.head = h)
    (tm8 : c.tape (h - 8) = false) (tm7 : c.tape (h - 7) = true)
    (tm6 : c.tape (h - 6) = false) (tm5 : c.tape (h - 5) = true)
    (tm4 : c.tape (h - 4) = true) (tm3 : c.tape (h - 3) = false)
    (tm2 : c.tape (h - 2) = true) (tm1 : c.tape (h - 1) = true)
    (tp0 : c.tape (h) = false) (tp1 : c.tape (h + 1) = true)
    :
    stepN 19 c = some ⟨State.F, h + 1,
        writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt c.tape (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true) (h + 1) false⟩ ∧
      CSafeSeg c 19 := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hs hh tm8 tm7 tm6 tm5 tm4 tm3 tm2 tm1 tp0 tp1
  subst hs
  have hp : h = hd := hh.symm
  subst hp
  have hf0 : (writeAt t (h) true) (h - 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tm1
  have hf1 : (writeAt t (h) true) (h - 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tm2
  have hf2 : (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm3
  have hf3 : (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 4) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm4
  have hf4 : (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm5
  have hf5 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm6
  have hf6 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 7) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm7
  have hf7 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm8
  have hf8 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 7) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm7
  have hf9 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 6) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf10 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf11 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 4) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm4
  have hf12 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 3) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf13 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf14 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true) (h - 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm1
  have hf15 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true) (h) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf16 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true) (h + 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp1
  have hf17 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true) (h + 1) false) (h) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf18 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 4) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm4
  have hf19 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm1
  have s0 : step ⟨State.D, h, t⟩
      = some ⟨State.B, h - 1, writeAt t (h) true⟩ := by
    simp [step, instr, tp0, move]
    try omega
  have s1 : step ⟨State.B, h - 1, writeAt t (h) true⟩
      = some ⟨State.C, h - 2, writeAt t (h) true⟩ := by
    have hself := writeAt_self _ _ hf0
    simp [step, instr, hf0, move, hself]
    try omega
  have s2 : step ⟨State.C, h - 2, writeAt t (h) true⟩
      = some ⟨State.D, h - 3, writeAt (writeAt t (h) true) (h - 2) false⟩ := by
    simp [step, instr, hf1, move]
    try omega
  have s3 : step ⟨State.D, h - 3, writeAt (writeAt t (h) true) (h - 2) false⟩
      = some ⟨State.B, h - 4, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩ := by
    simp [step, instr, hf2, move]
    try omega
  have s4 : step ⟨State.B, h - 4, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩
      = some ⟨State.C, h - 5, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩ := by
    have hself := writeAt_self _ _ hf3
    simp [step, instr, hf3, move, hself]
    try omega
  have s5 : step ⟨State.C, h - 5, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩
      = some ⟨State.D, h - 6, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false⟩ := by
    simp [step, instr, hf4, move]
    try omega
  have s6 : step ⟨State.D, h - 6, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false⟩
      = some ⟨State.B, h - 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true⟩ := by
    simp [step, instr, hf5, move]
    try omega
  have s7 : step ⟨State.B, h - 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true⟩
      = some ⟨State.C, h - 8, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true⟩ := by
    have hself := writeAt_self _ _ hf6
    simp [step, instr, hf6, move, hself]
    try omega
  have s8 : step ⟨State.C, h - 8, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true⟩
      = some ⟨State.E, h - 7, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true⟩ := by
    simp [step, instr, hf7, move]
    try omega
  have s9 : step ⟨State.E, h - 7, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true⟩
      = some ⟨State.A, h - 6, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true⟩ := by
    have hself := writeAt_self _ _ hf8
    simp [step, instr, hf8, move, hself]
    try omega
  have s10 : step ⟨State.A, h - 6, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true⟩
      = some ⟨State.C, h - 5, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true⟩ := by
    have hself := writeAt_self _ _ hf9
    simp [step, instr, hf9, move, hself]
    try omega
  have s11 : step ⟨State.C, h - 5, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true⟩
      = some ⟨State.E, h - 4, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true⟩ := by
    simp [step, instr, hf10, move]
    try omega
  have s12 : step ⟨State.E, h - 4, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true⟩
      = some ⟨State.A, h - 3, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true⟩ := by
    have hself := writeAt_self _ _ hf11
    simp [step, instr, hf11, move, hself]
    try omega
  have s13 : step ⟨State.A, h - 3, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true⟩
      = some ⟨State.C, h - 2, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true⟩ := by
    have hself := writeAt_self _ _ hf12
    simp [step, instr, hf12, move, hself]
    try omega
  have s14 : step ⟨State.C, h - 2, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true⟩
      = some ⟨State.E, h - 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true⟩ := by
    simp [step, instr, hf13, move]
    try omega
  have s15 : step ⟨State.E, h - 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true⟩
      = some ⟨State.A, h, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true⟩ := by
    have hself := writeAt_self _ _ hf14
    simp [step, instr, hf14, move, hself]
    try omega
  have s16 : step ⟨State.A, h, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true⟩
      = some ⟨State.C, h + 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true⟩ := by
    have hself := writeAt_self _ _ hf15
    simp [step, instr, hf15, move, hself]
    try omega
  have s17 : step ⟨State.C, h + 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true⟩
      = some ⟨State.D, h, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true) (h + 1) false⟩ := by
    simp [step, instr, hf16, move]
    try omega
  have s18 : step ⟨State.D, h, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true) (h + 1) false⟩
      = some ⟨State.F, h + 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true) (h + 1) false⟩ := by
    have hself := writeAt_self _ _ hf17
    simp [step, instr, hf17, move, hself]
    try omega
  have p1 : stepN 1 ⟨State.D, h, t⟩ = some ⟨State.B, h - 1, writeAt t (h) true⟩ := by
    simp [stepN, s0]
  have p2 : stepN 2 ⟨State.D, h, t⟩ = some ⟨State.C, h - 2, writeAt t (h) true⟩ := by
    simp [stepN, s0, s1]
  have p3 : stepN 3 ⟨State.D, h, t⟩ = some ⟨State.D, h - 3, writeAt (writeAt t (h) true) (h - 2) false⟩ := by
    simp [stepN, s0, s1, s2]
  have p4 : stepN 4 ⟨State.D, h, t⟩ = some ⟨State.B, h - 4, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩ := by
    simp [stepN, s0, s1, s2, s3]
  have p5 : stepN 5 ⟨State.D, h, t⟩ = some ⟨State.C, h - 5, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4]
  have p6 : stepN 6 ⟨State.D, h, t⟩ = some ⟨State.D, h - 6, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5]
  have p7 : stepN 7 ⟨State.D, h, t⟩ = some ⟨State.B, h - 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6]
  have p8 : stepN 8 ⟨State.D, h, t⟩ = some ⟨State.C, h - 8, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7]
  have p9 : stepN 9 ⟨State.D, h, t⟩ = some ⟨State.E, h - 7, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8]
  have p10 : stepN 10 ⟨State.D, h, t⟩ = some ⟨State.A, h - 6, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9]
  have p11 : stepN 11 ⟨State.D, h, t⟩ = some ⟨State.C, h - 5, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]
  have p12 : stepN 12 ⟨State.D, h, t⟩ = some ⟨State.E, h - 4, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  have p13 : stepN 13 ⟨State.D, h, t⟩ = some ⟨State.A, h - 3, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12]
  have p14 : stepN 14 ⟨State.D, h, t⟩ = some ⟨State.C, h - 2, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13]
  have p15 : stepN 15 ⟨State.D, h, t⟩ = some ⟨State.E, h - 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14]
  have p16 : stepN 16 ⟨State.D, h, t⟩ = some ⟨State.A, h, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15]
  have p17 : stepN 17 ⟨State.D, h, t⟩ = some ⟨State.C, h + 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16]
  have p18 : stepN 18 ⟨State.D, h, t⟩ = some ⟨State.D, h, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true) (h + 1) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17]
  refine ⟨by simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18], ?_⟩
  intro k d hk hkd hP hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hdd : (⟨State.D, h, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hP
    simp at hP
  · rw [p1] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p2] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.C, h - 2, writeAt t (h) true⟩ : Config).tape (⟨State.C, h - 2, writeAt t (h) true⟩ : Config).head
        = (writeAt t (h) true) (h - 2) from rfl] at hread
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
    rw [show (⟨State.C, h - 5, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩ : Config).tape (⟨State.C, h - 5, writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true⟩ : Config).head
        = (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) from rfl] at hread
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
    show (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8 + 1) = true
    rw [show h - 8 + 1 = h - 7 by omega]
    exact hf6
  · rw [p9] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p10] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p11] at hkd
    rw [← Option.some_inj.mp hkd]
    show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5 + 1) = true
    rw [show h - 5 + 1 = h - 4 by omega]
    exact hf18
  · rw [p12] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p13] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p14] at hkd
    rw [← Option.some_inj.mp hkd]
    show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2 + 1) = true
    rw [show h - 2 + 1 = h - 1 by omega]
    exact hf19
  · rw [p15] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p16] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p17] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.C, h + 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true⟩ : Config).tape (⟨State.C, h + 1, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true⟩ : Config).head
        = (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 6) true) (h - 8) true) (h - 5) true) (h - 2) true) (h + 1) from rfl] at hread
    rw [hf16] at hread
    exact absurd hread (by simp)
  · rw [p18] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP

/-- **Left-edge business, odd `a`**: the march steps one cell into virgin territory, the chain fills back and plants the new first hole at `(l−1)+6`.  10 steps. -/
theorem edge_odd_seg {c : Config} {h : Int}
    (hs : c.state = State.D) (hh : c.head = h)
    (tm2 : c.tape (h - 2) = false) (tm1 : c.tape (h - 1) = true)
    (tp0 : c.tape (h) = false) (tp1 : c.tape (h + 1) = false)
    (tp2 : c.tape (h + 2) = true) (tp3 : c.tape (h + 3) = true)
    (tp4 : c.tape (h + 4) = true)
    :
    stepN 10 c = some ⟨State.F, h + 4,
        writeAt (writeAt (writeAt (writeAt c.tape (h) true) (h - 2) true) (h + 1) true) (h + 4) false⟩ ∧
      CSafeSeg c 10 := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hs hh tm2 tm1 tp0 tp1 tp2 tp3 tp4
  subst hs
  have hp : h = hd := hh.symm
  subst hp
  have hf0 : (writeAt t (h) true) (h - 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tm1
  have hf1 : (writeAt t (h) true) (h - 2) = false := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tm2
  have hf2 : (writeAt (writeAt t (h) true) (h - 2) true) (h - 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm1
  have hf3 : (writeAt (writeAt t (h) true) (h - 2) true) (h) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf4 : (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp1
  have hf5 : (writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true) (h + 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp2
  have hf6 : (writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true) (h + 3) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp3
  have hf7 : (writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true) (h + 4) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp4
  have hf8 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true) (h + 4) false) (h + 3) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp3
  have hf9 : (writeAt (writeAt t (h) true) (h - 2) true) (h + 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp2
  have s0 : step ⟨State.D, h, t⟩
      = some ⟨State.B, h - 1, writeAt t (h) true⟩ := by
    simp [step, instr, tp0, move]
    try omega
  have s1 : step ⟨State.B, h - 1, writeAt t (h) true⟩
      = some ⟨State.C, h - 2, writeAt t (h) true⟩ := by
    have hself := writeAt_self _ _ hf0
    simp [step, instr, hf0, move, hself]
    try omega
  have s2 : step ⟨State.C, h - 2, writeAt t (h) true⟩
      = some ⟨State.E, h - 1, writeAt (writeAt t (h) true) (h - 2) true⟩ := by
    simp [step, instr, hf1, move]
    try omega
  have s3 : step ⟨State.E, h - 1, writeAt (writeAt t (h) true) (h - 2) true⟩
      = some ⟨State.A, h, writeAt (writeAt t (h) true) (h - 2) true⟩ := by
    have hself := writeAt_self _ _ hf2
    simp [step, instr, hf2, move, hself]
    try omega
  have s4 : step ⟨State.A, h, writeAt (writeAt t (h) true) (h - 2) true⟩
      = some ⟨State.C, h + 1, writeAt (writeAt t (h) true) (h - 2) true⟩ := by
    have hself := writeAt_self _ _ hf3
    simp [step, instr, hf3, move, hself]
    try omega
  have s5 : step ⟨State.C, h + 1, writeAt (writeAt t (h) true) (h - 2) true⟩
      = some ⟨State.E, h + 2, writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true⟩ := by
    simp [step, instr, hf4, move]
    try omega
  have s6 : step ⟨State.E, h + 2, writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true⟩
      = some ⟨State.A, h + 3, writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true⟩ := by
    have hself := writeAt_self _ _ hf5
    simp [step, instr, hf5, move, hself]
    try omega
  have s7 : step ⟨State.A, h + 3, writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true⟩
      = some ⟨State.C, h + 4, writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true⟩ := by
    have hself := writeAt_self _ _ hf6
    simp [step, instr, hf6, move, hself]
    try omega
  have s8 : step ⟨State.C, h + 4, writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true⟩
      = some ⟨State.D, h + 3, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true) (h + 4) false⟩ := by
    simp [step, instr, hf7, move]
    try omega
  have s9 : step ⟨State.D, h + 3, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true) (h + 4) false⟩
      = some ⟨State.F, h + 4, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true) (h + 4) false⟩ := by
    have hself := writeAt_self _ _ hf8
    simp [step, instr, hf8, move, hself]
    try omega
  have p1 : stepN 1 ⟨State.D, h, t⟩ = some ⟨State.B, h - 1, writeAt t (h) true⟩ := by
    simp [stepN, s0]
  have p2 : stepN 2 ⟨State.D, h, t⟩ = some ⟨State.C, h - 2, writeAt t (h) true⟩ := by
    simp [stepN, s0, s1]
  have p3 : stepN 3 ⟨State.D, h, t⟩ = some ⟨State.E, h - 1, writeAt (writeAt t (h) true) (h - 2) true⟩ := by
    simp [stepN, s0, s1, s2]
  have p4 : stepN 4 ⟨State.D, h, t⟩ = some ⟨State.A, h, writeAt (writeAt t (h) true) (h - 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3]
  have p5 : stepN 5 ⟨State.D, h, t⟩ = some ⟨State.C, h + 1, writeAt (writeAt t (h) true) (h - 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4]
  have p6 : stepN 6 ⟨State.D, h, t⟩ = some ⟨State.E, h + 2, writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5]
  have p7 : stepN 7 ⟨State.D, h, t⟩ = some ⟨State.A, h + 3, writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6]
  have p8 : stepN 8 ⟨State.D, h, t⟩ = some ⟨State.C, h + 4, writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7]
  have p9 : stepN 9 ⟨State.D, h, t⟩ = some ⟨State.D, h + 3, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true) (h + 4) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8]
  refine ⟨by simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9], ?_⟩
  intro k d hk hkd hP hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hdd : (⟨State.D, h, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hP
    simp at hP
  · rw [p1] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p2] at hkd
    rw [← Option.some_inj.mp hkd]
    show (writeAt t (h) true) (h - 2 + 1) = true
    rw [show h - 2 + 1 = h - 1 by omega]
    exact hf0
  · rw [p3] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p4] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p5] at hkd
    rw [← Option.some_inj.mp hkd]
    show (writeAt (writeAt t (h) true) (h - 2) true) (h + 1 + 1) = true
    rw [show h + 1 + 1 = h + 2 by omega]
    exact hf9
  · rw [p6] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p7] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p8] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.C, h + 4, writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true⟩ : Config).tape (⟨State.C, h + 4, writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true⟩ : Config).head
        = (writeAt (writeAt (writeAt t (h) true) (h - 2) true) (h + 1) true) (h + 4) from rfl] at hread
    rw [hf7] at hread
    exact absurd hread (by simp)
  · rw [p9] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP

/-- **Left-edge business, even `a`**: the march steps three cells into virgin territory before the chain fires, extending the field by 3 and planting at `(l−3)+9`.  13 steps. -/
theorem edge_even_seg {c : Config} {h : Int}
    (hs : c.state = State.D) (hh : c.head = h)
    (tm2 : c.tape (h - 2) = false) (tm1 : c.tape (h - 1) = false)
    (tp0 : c.tape (h) = false) (tp1 : c.tape (h + 1) = false)
    (tp2 : c.tape (h + 2) = true) (tp3 : c.tape (h + 3) = true)
    (tp4 : c.tape (h + 4) = false) (tp5 : c.tape (h + 5) = true)
    (tp6 : c.tape (h + 6) = true) (tp7 : c.tape (h + 7) = true)
    :
    stepN 13 c = some ⟨State.F, h + 7,
        writeAt (writeAt (writeAt (writeAt (writeAt (writeAt c.tape (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true) (h + 7) false⟩ ∧
      CSafeSeg c 13 := by
  obtain ⟨s, hd, t⟩ := c
  simp only at hs hh tm2 tm1 tp0 tp1 tp2 tp3 tp4 tp5 tp6 tp7
  subst hs
  have hp : h = hd := hh.symm
  subst hp
  have hf0 : (writeAt t (h) true) (h - 1) = false := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact tm1
  have hf1 : (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tm2
  have hf2 : (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h - 1) = true := by
    rw [writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf3 : (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ _ _
  have hf4 : (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp1
  have hf5 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp2
  have hf6 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 3) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp3
  have hf7 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp4
  have hf8 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true) (h + 5) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp5
  have hf9 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true) (h + 6) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp6
  have hf10 : (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true) (h + 7) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp7
  have hf11 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true) (h + 7) false) (h + 6) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp6
  have hf12 : (writeAt (writeAt t (h) true) (h - 1) true) (h - 1) = true := writeAt_same _ _ _
  have hf13 : (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 2) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp2
  have hf14 : (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 5) = true := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact tp5
  have s0 : step ⟨State.D, h, t⟩
      = some ⟨State.B, h - 1, writeAt t (h) true⟩ := by
    simp [step, instr, tp0, move]
    try omega
  have s1 : step ⟨State.B, h - 1, writeAt t (h) true⟩
      = some ⟨State.C, h - 2, writeAt (writeAt t (h) true) (h - 1) true⟩ := by
    simp [step, instr, hf0, move]
    try omega
  have s2 : step ⟨State.C, h - 2, writeAt (writeAt t (h) true) (h - 1) true⟩
      = some ⟨State.E, h - 1, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true⟩ := by
    simp [step, instr, hf1, move]
    try omega
  have s3 : step ⟨State.E, h - 1, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true⟩
      = some ⟨State.A, h, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true⟩ := by
    have hself := writeAt_self _ _ hf2
    simp [step, instr, hf2, move, hself]
    try omega
  have s4 : step ⟨State.A, h, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true⟩
      = some ⟨State.C, h + 1, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true⟩ := by
    have hself := writeAt_self _ _ hf3
    simp [step, instr, hf3, move, hself]
    try omega
  have s5 : step ⟨State.C, h + 1, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true⟩
      = some ⟨State.E, h + 2, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true⟩ := by
    simp [step, instr, hf4, move]
    try omega
  have s6 : step ⟨State.E, h + 2, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true⟩
      = some ⟨State.A, h + 3, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true⟩ := by
    have hself := writeAt_self _ _ hf5
    simp [step, instr, hf5, move, hself]
    try omega
  have s7 : step ⟨State.A, h + 3, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true⟩
      = some ⟨State.C, h + 4, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true⟩ := by
    have hself := writeAt_self _ _ hf6
    simp [step, instr, hf6, move, hself]
    try omega
  have s8 : step ⟨State.C, h + 4, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true⟩
      = some ⟨State.E, h + 5, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true⟩ := by
    simp [step, instr, hf7, move]
    try omega
  have s9 : step ⟨State.E, h + 5, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true⟩
      = some ⟨State.A, h + 6, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true⟩ := by
    have hself := writeAt_self _ _ hf8
    simp [step, instr, hf8, move, hself]
    try omega
  have s10 : step ⟨State.A, h + 6, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true⟩
      = some ⟨State.C, h + 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true⟩ := by
    have hself := writeAt_self _ _ hf9
    simp [step, instr, hf9, move, hself]
    try omega
  have s11 : step ⟨State.C, h + 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true⟩
      = some ⟨State.D, h + 6, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true) (h + 7) false⟩ := by
    simp [step, instr, hf10, move]
    try omega
  have s12 : step ⟨State.D, h + 6, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true) (h + 7) false⟩
      = some ⟨State.F, h + 7, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true) (h + 7) false⟩ := by
    have hself := writeAt_self _ _ hf11
    simp [step, instr, hf11, move, hself]
    try omega
  have p1 : stepN 1 ⟨State.D, h, t⟩ = some ⟨State.B, h - 1, writeAt t (h) true⟩ := by
    simp [stepN, s0]
  have p2 : stepN 2 ⟨State.D, h, t⟩ = some ⟨State.C, h - 2, writeAt (writeAt t (h) true) (h - 1) true⟩ := by
    simp [stepN, s0, s1]
  have p3 : stepN 3 ⟨State.D, h, t⟩ = some ⟨State.E, h - 1, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true⟩ := by
    simp [stepN, s0, s1, s2]
  have p4 : stepN 4 ⟨State.D, h, t⟩ = some ⟨State.A, h, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3]
  have p5 : stepN 5 ⟨State.D, h, t⟩ = some ⟨State.C, h + 1, writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4]
  have p6 : stepN 6 ⟨State.D, h, t⟩ = some ⟨State.E, h + 2, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5]
  have p7 : stepN 7 ⟨State.D, h, t⟩ = some ⟨State.A, h + 3, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6]
  have p8 : stepN 8 ⟨State.D, h, t⟩ = some ⟨State.C, h + 4, writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7]
  have p9 : stepN 9 ⟨State.D, h, t⟩ = some ⟨State.E, h + 5, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8]
  have p10 : stepN 10 ⟨State.D, h, t⟩ = some ⟨State.A, h + 6, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9]
  have p11 : stepN 11 ⟨State.D, h, t⟩ = some ⟨State.C, h + 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]
  have p12 : stepN 12 ⟨State.D, h, t⟩ = some ⟨State.D, h + 6, writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true) (h + 7) false⟩ := by
    simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  refine ⟨by simp [stepN, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12], ?_⟩
  intro k d hk hkd hP hread
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hdd : (⟨State.D, h, t⟩ : Config) = d := by simpa [stepN] using hkd
    rw [← hdd] at hP
    simp at hP
  · rw [p1] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p2] at hkd
    rw [← Option.some_inj.mp hkd]
    show (writeAt (writeAt t (h) true) (h - 1) true) (h - 2 + 1) = true
    rw [show h - 2 + 1 = h - 1 by omega]
    exact hf12
  · rw [p3] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p4] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p5] at hkd
    rw [← Option.some_inj.mp hkd]
    show (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1 + 1) = true
    rw [show h + 1 + 1 = h + 2 by omega]
    exact hf13
  · rw [p6] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p7] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p8] at hkd
    rw [← Option.some_inj.mp hkd]
    show (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4 + 1) = true
    rw [show h + 4 + 1 = h + 5 by omega]
    exact hf14
  · rw [p9] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p10] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP
  · rw [p11] at hkd
    rw [← Option.some_inj.mp hkd] at hread
    rw [show (⟨State.C, h + 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true⟩ : Config).tape (⟨State.C, h + 7, writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true⟩ : Config).head
        = (writeAt (writeAt (writeAt (writeAt (writeAt t (h) true) (h - 1) true) (h - 2) true) (h + 1) true) (h + 4) true) (h + 7) from rfl] at hread
    rw [hf10] at hread
    exact absurd hread (by simp)
  · rw [p12] at hkd
    rw [← Option.some_inj.mp hkd] at hP
    simp at hP


/-- Constructive De Morgan for the interval guards: hands `omega` a
positive disjunction instead of a negated conjunction (which would pull
`Classical.choice` into the axiom print). -/
theorem not_and_le {a b q : Int} (h : ¬(a < q ∧ q ≤ b)) :
    q ≤ a ∨ b < q := by
  by_cases hx : a < q
  · right
    by_cases hy : q ≤ b
    · exact absurd ⟨hx, hy⟩ h
    · omega
  · left
    omega

/-- Closed form of the tape after `n` caterpillar cycles from entry `h`:
the crawled zone `(h − 2n − 3, h]` is all `1`s except the new front cell
`h − 2n`; the new carried hole sits at `h − 2n − 3`; everything outside
the zone is untouched. -/
def catTape (t : Int → Bool) (h : Int) (n : Nat) : Int → Bool :=
  fun q =>
    if q = h - 2 * n ∨ q = h - 2 * n - 3 then false
    else if h - 2 * n - 3 < q ∧ q ≤ h then true
    else t q

/-- **The caterpillar run**: `n` cycles glued end-to-end — `10n` steps,
`2n` cells of leftward travel, the crawled zone rewritten to the
closed-form `catTape`, probe-safe throughout.  This is the unbounded
middle of every traversal episode. -/
theorem cat_run :
    ∀ (n : Nat) (c : Config) (h : Int), c.state = State.D → c.head = h →
      c.tape h = false → c.tape (h - 3) = false →
      (∀ q : Int, h - 2 * n - 4 ≤ q → q ≤ h → q ≠ h → q ≠ h - 3 →
        c.tape q = true) →
      stepN (10 * n) c = some ⟨State.D, h - 2 * n, catTape c.tape h n⟩ ∧
        CSafeSeg c (10 * n) := by
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
          show (if q = h - 2 * ((0 : Nat) : Int) ∨
                  q = h - 2 * ((0 : Nat) : Int) - 3 then false
                else if h - 2 * ((0 : Nat) : Int) - 3 < q ∧ q ≤ h then true
                else t q) = t q
          split
          · rename_i hA
            rcases hA with h1 | h1
            · have hq : q = h := by omega
              rw [hq]
              exact t0.symm
            · have hq : q = h - 3 := by omega
              rw [hq]
              exact t3.symm
          · split
            · rename_i hA hB
              exact (hpre q (by omega) (by omega) (by omega)
                (by omega)).symm
            · rfl
        show some (⟨State.D, h, t⟩ : Config) = _
        rw [htape,
            show h - 2 * ((0 : Nat) : Int) = h from by omega]
      · intro k d hk
        exact absurd hk (by omega)
  | succ n ih =>
      intro c h hs hh t0 t3 hpre
      have h1 := hpre (h - 1) (by omega) (by omega) (by omega) (by omega)
      have h2 := hpre (h - 2) (by omega) (by omega) (by omega) (by omega)
      have h4 := hpre (h - 4) (by omega) (by omega) (by omega) (by omega)
      have h5 := hpre (h - 5) (by omega) (by omega) (by omega) (by omega)
      have h6 := hpre (h - 6) (by omega) (by omega) (by omega) (by omega)
      obtain ⟨hrun10, hsafe10⟩ := cat_cycle hs hh t0 h1 h2 t3 h4 h5 h6
      have hT1f : (writeAt (writeAt (writeAt (writeAt c.tape h true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 2) = false := by
        rw [writeAt_other _ _ _ _ (by omega),
            writeAt_other _ _ _ _ (by omega)]
        exact writeAt_same _ _ _
      have hT1c : (writeAt (writeAt (writeAt (writeAt c.tape h true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 2 - 3) = false := by
        rw [show h - 2 - 3 = h - 5 from by omega]
        exact writeAt_same _ _ _
      have hT1pre : ∀ q : Int, h - 2 - 2 * (n : Int) - 4 ≤ q →
          q ≤ h - 2 → q ≠ h - 2 → q ≠ h - 2 - 3 → (writeAt (writeAt (writeAt (writeAt c.tape h true) (h - 2) false) (h - 3) true) (h - 5) false) q = true := by
        intro q hq1 hq2 hq3 hq4
        by_cases hq5 : q = h - 3
        · rw [hq5, writeAt_other _ _ _ _ (by omega)]
          exact writeAt_same _ _ _
        · rw [writeAt_other _ _ _ _ (by omega),
              writeAt_other _ _ _ _ (by omega),
              writeAt_other _ _ _ _ (by omega),
              writeAt_other _ _ _ _ (by omega)]
          exact hpre q (by omega) (by omega) (by omega) (by omega)
      obtain ⟨hrunN, hsafeN⟩ :=
        ih ⟨State.D, h - 2, (writeAt (writeAt (writeAt (writeAt c.tape h true) (h - 2) false) (h - 3) true) (h - 5) false)⟩ (h - 2) rfl rfl hT1f hT1c hT1pre
      have heq : catTape (writeAt (writeAt (writeAt (writeAt c.tape h true) (h - 2) false) (h - 3) true) (h - 5) false) (h - 2) n = catTape c.tape h (n + 1) := by
        funext q
        show (if q = h - 2 - 2 * (n : Int) ∨
                q = h - 2 - 2 * (n : Int) - 3 then false
              else if h - 2 - 2 * (n : Int) - 3 < q ∧ q ≤ h - 2 then true
              else (writeAt (writeAt (writeAt (writeAt c.tape h true) (h - 2) false) (h - 3) true) (h - 5) false) q) =
            (if q = h - 2 * ((n + 1 : Nat) : Int) ∨
                q = h - 2 * ((n + 1 : Nat) : Int) - 3 then false
              else if h - 2 * ((n + 1 : Nat) : Int) - 3 < q ∧ q ≤ h
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
          have hA2 : ¬(q = h - 2 * ((n + 1 : Nat) : Int) ∨
              q = h - 2 * ((n + 1 : Nat) : Int) - 3) := by
            intro hc
            rcases hc with hx | hx
            · exact hA (Or.inl (by omega))
            · exact hA (Or.inr (by omega))
          rw [if_neg hA2]
          split
          · rename_i hB
            rw [if_pos (show h - 2 * ((n + 1 : Nat) : Int) - 3 < q ∧
                q ≤ h from ⟨by omega, by omega⟩)]
          · rename_i hB
            have hB' := not_and_le hB
            clear hB
            split
            · rename_i hB2
              obtain ⟨hB2a, hB2b⟩ := hB2
              by_cases hq : q = h
              · rw [hq, writeAt_other _ _ _ _ (by omega),
                    writeAt_other _ _ _ _ (by omega),
                    writeAt_other _ _ _ _ (by omega)]
                exact writeAt_same _ _ _
              · have hq1 : q = h - 1 := by omega
                rw [hq1, writeAt_other _ _ _ _ (by omega),
                    writeAt_other _ _ _ _ (by omega),
                    writeAt_other _ _ _ _ (by omega),
                    writeAt_other _ _ _ _ (by omega)]
                exact hpre (h - 1) (by omega) (by omega) (by omega)
                  (by omega)
            · rename_i hB2
              have hB2' := not_and_le hB2
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
        show stepN (10 * n) ⟨State.D, h - 2, (writeAt (writeAt (writeAt (writeAt c.tape h true) (h - 2) false) (h - 3) true) (h - 5) false)⟩
            = some ⟨State.D, h - 2 * ((n + 1 : Nat) : Int),
                catTape c.tape h (n + 1)⟩
        rw [hrunN, heq,
            show h - 2 - 2 * (n : Int)
              = h - 2 * ((n + 1 : Nat) : Int) from by omega]
      · have hc := csafe_compose hrun10 hsafe10 hsafeN
        rw [show 10 * (n + 1) = 10 + 10 * n from by omega]
        exact hc

end QIG.Dossier2RawTM

#print axioms QIG.Dossier2RawTM.halt_requires_c_probe_00
#print axioms QIG.Dossier2RawTM.blank_nonhalting_of_c_probe_safe
#print axioms QIG.Dossier2RawTM.cprobe_safe_of_segments
#print axioms QIG.Dossier2RawTM.csafe_of_checkSafe
#print axioms QIG.Dossier2RawTM.step_D_on_one
#print axioms QIG.Dossier2RawTM.spawn_step
#print axioms QIG.Dossier2RawTM.sweep_DF
#print axioms QIG.Dossier2RawTM.cat_cycle
#print axioms QIG.Dossier2RawTM.spawn_variant_step
#print axioms QIG.Dossier2RawTM.cross_cycle
#print axioms QIG.Dossier2RawTM.term_cycle
#print axioms QIG.Dossier2RawTM.fuse_cycle
#print axioms QIG.Dossier2RawTM.edge_odd_seg
#print axioms QIG.Dossier2RawTM.edge_even_seg
#print axioms QIG.Dossier2RawTM.cat_run
