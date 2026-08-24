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

end QIG.Dossier2RawTM

#print axioms QIG.Dossier2RawTM.halt_requires_c_probe_00
#print axioms QIG.Dossier2RawTM.blank_nonhalting_of_c_probe_safe
#print axioms QIG.Dossier2RawTM.cprobe_safe_of_segments
#print axioms QIG.Dossier2RawTM.csafe_of_checkSafe
#print axioms QIG.Dossier2RawTM.step_D_on_one
#print axioms QIG.Dossier2RawTM.spawn_step
