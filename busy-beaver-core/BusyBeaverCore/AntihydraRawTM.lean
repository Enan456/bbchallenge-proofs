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

/-- One raw TM step.  `none` means the undefined `F0` halt was reached.

Informally: read the cell under the head, look it up in the program, and
either die (the one undefined entry) or write, move, and change state.
Everything ever proven about this machine is a statement about iterating
this ten-line function. -/
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
transition `F0`.

Informally: twelve cases, one door.  The machine's program has a single
undefined cell, and this case split is the whole proof that halting means
standing on it. -/
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
sits one cell to the left with a `1` written at the probed cell. 

Informally: the turnstile into death — `F` is reachable only through
`E` reading a `0`, stepping left, leaving a `1` behind.  So the final two
configurations of any halting run are completely determined. -/
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
configuration where `E` reads a `0` whose left neighbour is also `0`.

Informally: *to die, the machine must first stand in state `E` on a `0`
with another `0` immediately to its left* — because the only door into the
halting state `F` is the transition `E0`, which steps left, and the cell
`F` then dies on was not touched by that step.  An unbounded question
("does it ever halt?") becomes the reachability of a two-cell pattern. -/
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
the invariant discharged empirically by stage753.

Informally: a sentry condition.  If a `1` always guards the left flank of
whatever `E` probes, the fatal pattern of `halt_requires_e_probe_00` can
never occur, so the machine runs forever.  The remaining 1,800 lines of
this file exist to discharge this one predicate from the record dynamics. -/
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

/-- State `E` sweeps right across `n` ones without touching the tape.

Informally: the three self-loop transitions rewrite `1` over `1`, so the
tape function after the sweep is *literally equal* to the tape before —
not merely equivalent.  These three lemmas are the atoms every macro rule
decomposes into. -/
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
safe segments gives `EProbeSafe` for the whole infinite run.

Informally: *safety in pieces is safety forever*.  If from every
invariant-satisfying configuration the machine runs some positive number
of steps safely and lands on the invariant again, then every moment of
the infinite run falls inside one of these safe segments — strong
induction on how many segments precede it.  This is how finitely many
rule theorems control an infinite trajectory. -/
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

/-- **The drop rule** (`m = 2`): the counter loses a cell.  From a record
`(a, 2, c)` anchored at `q`, the right end of the counter block: exactly
`2c + 15` raw steps to state `A` on the new frontier, with the counter
block one shorter and the tape reshaped to `(a-1, c+3, 1)`.  Both
`E`-probes of a `0` are safe. -/
theorem drop_step {cfg : Config} {q : Int} (k : Nat)
    (hs : cfg.state = State.B) (hh : cfg.head = q + 5 + k)
    (ta : cfg.tape q = true) (tg1 : cfg.tape (q + 1) = false)
    (tm0 : cfg.tape (q + 2) = true) (tm1 : cfg.tape (q + 3) = true)
    (tg2 : cfg.tape (q + 4) = false)
    (tc : ∀ i : Nat, i < k → cfg.tape (q + 5 + i) = true)
    (tf : cfg.tape (q + 5 + k) = false) :
    stepN (2 * k + 15) cfg = some ⟨State.A, q + 6 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 5 + k) true) (q + 4 + k) false)⟩ ∧
      ESafeSeg cfg (2 * k + 15) := by
  obtain ⟨s, hd, t⟩ := cfg
  simp only at hs hh ta tg1 tm0 tm1 tg2 tc tf
  subst hs hd
  -- pointwise values of the intermediate tapes
  have h1_3 : (writeAt t (q + 4) true) (q + 3) = true := by
    rw [writeAt_other t (q + 4) _ true (by omega)]; exact tm1
  have h2_2 : (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 2) = true := by
    rw [writeAt_other _ (q + 3) _ false (by omega),
        writeAt_other t (q + 4) _ true (by omega)]; exact tm0
  have h2_1 : (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) = false := by
    rw [writeAt_other _ (q + 3) _ false (by omega),
        writeAt_other t (q + 4) _ true (by omega)]; exact tg1
  have h2_q : (writeAt (writeAt t (q + 4) true) (q + 3) false) q = true := by
    rw [writeAt_other _ (q + 3) _ false (by omega),
        writeAt_other t (q + 4) _ true (by omega)]; exact ta
  have h3_q : (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q = true := by
    rw [writeAt_other _ (q + 1) _ true (by omega)]; exact h2_q
  have h4_1 : (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 1) = true := by
    rw [writeAt_other _ q _ false (by omega)]
    exact writeAt_same _ (q + 1) true
  have h4_2 : (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 2) = true := by
    rw [writeAt_other _ q _ false (by omega),
        writeAt_other _ (q + 1) _ true (by omega)]; exact h2_2
  have h4_3 : (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) = false := by
    rw [writeAt_other _ q _ false (by omega),
        writeAt_other _ (q + 1) _ true (by omega)]
    exact writeAt_same _ (q + 3) false
  have h5_4 : (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 4) = true := by
    rw [writeAt_other _ (q + 3) _ true (by omega),
        writeAt_other _ q _ false (by omega),
        writeAt_other _ (q + 1) _ true (by omega),
        writeAt_other _ (q + 3) _ false (by omega)]
    exact writeAt_same t (q + 4) true
  have h5_c : ∀ i : Nat, i < k + 2 → (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 3 + i) = true := by
    intro i hi
    by_cases hi0 : i = 0
    · rw [hi0, show q + 3 + ((0 : Nat) : Int) = q + 3 by omega]
      exact writeAt_same _ (q + 3) true
    · by_cases hi1 : i = 1
      · rw [hi1, show q + 3 + ((1 : Nat) : Int) = q + 4 by omega]; exact h5_4
      · rw [writeAt_other _ (q + 3) _ true (by omega),
            writeAt_other _ q _ false (by omega),
            writeAt_other _ (q + 1) _ true (by omega),
            writeAt_other _ (q + 3) _ false (by omega),
            writeAt_other t (q + 4) _ true (by omega)]
        have := tc (i - 2) (by omega)
        rw [show q + 3 + (i : Int) = q + 5 + ((i - 2 : Nat) : Int) by omega]
        exact this
  have h5_f : (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 5 + k) = false := by
    rw [writeAt_other _ (q + 3) _ true (by omega),
        writeAt_other _ q _ false (by omega),
        writeAt_other _ (q + 1) _ true (by omega),
        writeAt_other _ (q + 3) _ false (by omega),
        writeAt_other t (q + 4) _ true (by omega)]
    exact tf
  have h5_top : (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 4 + k) = true := by
    by_cases hk0 : k = 0
    · rw [hk0, show q + 4 + ((0 : Nat) : Int) = q + 4 by omega]; exact h5_4
    · rw [writeAt_other _ (q + 3) _ true (by omega),
          writeAt_other _ q _ false (by omega),
          writeAt_other _ (q + 1) _ true (by omega),
          writeAt_other _ (q + 3) _ false (by omega),
          writeAt_other t (q + 4) _ true (by omega)]
      have := tc (k - 1) (by omega)
      rw [show q + 4 + (k : Int) = q + 5 + ((k - 1 : Nat) : Int) by omega]
      exact this
  have h6_top : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 5 + k) true) (q + 4 + k) = true := by
    rw [writeAt_other _ (q + 5 + k) _ true (by omega)]; exact h5_top
  -- the raw trajectory
  have s1 : step ⟨State.B, q + 5 + k, t⟩ = some ⟨State.C, q + 4 + k, t⟩ := by
    have hself : writeAt t (q + 5 + (k : Int)) false = t := writeAt_self t _ tf
    simp [step, instr, tf, move, hself]
    try omega
  have sC : stepN k ⟨State.C, q + 4 + k, t⟩ = some ⟨State.C, q + 4, t⟩ := by
    have h := sweep_C k ⟨State.C, q + 4 + k, t⟩ rfl
      (fun i hi => by
        show t (q + 4 + (k : Int) - (i : Int)) = true
        have := tc (k - 1 - i) (by omega)
        rw [show q + 4 + (k : Int) - (i : Int)
              = q + 5 + ((k - 1 - i : Nat) : Int) by omega]
        exact this)
    rw [show q + 4 + (k : Int) - (k : Int) = q + 4 by omega] at h
    exact h
  have s2 : step ⟨State.C, q + 4, t⟩ = some ⟨State.D, q + 3, (writeAt t (q + 4) true)⟩ := by
    simp [step, instr, tg2, move]
    try omega
  have s3 : step ⟨State.D, q + 3, (writeAt t (q + 4) true)⟩ = some ⟨State.B, q + 2, (writeAt (writeAt t (q + 4) true) (q + 3) false)⟩ := by
    simp [step, instr, h1_3, move]
    try omega
  have s4 : step ⟨State.B, q + 2, (writeAt (writeAt t (q + 4) true) (q + 3) false)⟩ = some ⟨State.E, q + 1, (writeAt (writeAt t (q + 4) true) (q + 3) false)⟩ := by
    have hself : writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 2) true = (writeAt (writeAt t (q + 4) true) (q + 3) false) := writeAt_self _ _ h2_2
    simp [step, instr, h2_2, move, hself]
    try omega
  have s5 : step ⟨State.E, q + 1, (writeAt (writeAt t (q + 4) true) (q + 3) false)⟩ = some ⟨State.F, q, (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true)⟩ := by
    simp [step, instr, h2_1, move]
    try omega
  have s6 : step ⟨State.F, q, (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true)⟩ = some ⟨State.A, q + 1, (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false)⟩ := by
    simp [step, instr, h3_q, move]
    try omega
  have sA : stepN 2 ⟨State.A, q + 1, (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false)⟩ = some ⟨State.A, q + 3, (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false)⟩ := by
    have h := sweep_A 2 ⟨State.A, q + 1, (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false)⟩ rfl
      (fun i hi => by
        have hcase : i = 0 ∨ i = 1 := by omega
        rcases hcase with rfl | rfl
        · show (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 1 + ((0 : Nat) : Int)) = true
          rw [show q + 1 + ((0 : Nat) : Int) = q + 1 by omega]; exact h4_1
        · show (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 1 + ((1 : Nat) : Int)) = true
          rw [show q + 1 + ((1 : Nat) : Int) = q + 2 by omega]; exact h4_2)
    rw [show q + 1 + ((2 : Nat) : Int) = q + 3 by omega] at h
    exact h
  have s7 : step ⟨State.A, q + 3, (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false)⟩ = some ⟨State.B, q + 4, (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true)⟩ := by
    simp [step, instr, h4_3, move]
    try omega
  have s8 : step ⟨State.B, q + 4, (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true)⟩ = some ⟨State.E, q + 3, (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true)⟩ := by
    have hself : writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 4) true = (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) := writeAt_self _ _ h5_4
    simp [step, instr, h5_4, move, hself]
    try omega
  have sE : stepN (k + 2) ⟨State.E, q + 3, (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true)⟩ =
      some ⟨State.E, q + 5 + k, (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true)⟩ := by
    have h := sweep_E (k + 2) ⟨State.E, q + 3, (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true)⟩ rfl
      (fun i hi => h5_c i hi)
    rw [show q + 3 + ((k + 2 : Nat) : Int) = q + 5 + (k : Int) by omega] at h
    exact h
  have s9 : step ⟨State.E, q + 5 + k, (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true)⟩ =
      some ⟨State.F, q + 4 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 5 + k) true)⟩ := by
    simp [step, instr, h5_f, move]
    try omega
  have s10 : step ⟨State.F, q + 4 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 5 + k) true)⟩ =
      some ⟨State.A, q + 5 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 5 + k) true) (q + 4 + k) false)⟩ := by
    simp [step, instr, h6_top, move]
    try omega
  have h7_f : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 5 + k) true) (q + 4 + k) false) (q + 5 + k) = true := by
    rw [writeAt_other _ (q + 4 + k) _ false (by omega)]
    exact writeAt_same _ (q + 5 + k) true
  have s11 : step ⟨State.A, q + 5 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 5 + k) true) (q + 4 + k) false)⟩ =
      some ⟨State.A, q + 6 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 5 + k) true) (q + 4 + k) false)⟩ := by
    have hself : writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 5 + k) true) (q + 4 + k) false) (q + 5 + (k : Int)) true = (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 5 + k) true) (q + 4 + k) false) :=
      writeAt_self _ _ h7_f
    simp [step, instr, h7_f, move, hself]
    try omega
  -- assemble
  have a1 : stepN 1 ⟨State.B, q + 5 + k, t⟩ =
      some ⟨State.C, q + 4 + k, t⟩ := by simp [stepN, s1]
  have a2 : stepN (1 + k) ⟨State.B, q + 5 + k, t⟩ =
      some ⟨State.C, q + 4, t⟩ := by rw [stepN_add, a1]; exact sC
  have hmid : stepN 5 ⟨State.C, q + 4, t⟩ = some ⟨State.A, q + 1, (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false)⟩ := by
    simp [stepN, s2, s3, s4, s5, s6]
  have a3 : stepN (1 + k + 5) ⟨State.B, q + 5 + k, t⟩ =
      some ⟨State.A, q + 1, (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false)⟩ := by rw [stepN_add, a2]; exact hmid
  have a4 : stepN (1 + k + 5 + 2) ⟨State.B, q + 5 + k, t⟩ =
      some ⟨State.A, q + 3, (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false)⟩ := by rw [stepN_add, a3]; exact sA
  have hmid2 : stepN 2 ⟨State.A, q + 3, (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false)⟩ =
      some ⟨State.E, q + 3, (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true)⟩ := by simp [stepN, s7, s8]
  have a5 : stepN (1 + k + 5 + 2 + 2) ⟨State.B, q + 5 + k, t⟩ =
      some ⟨State.E, q + 3, (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true)⟩ := by rw [stepN_add, a4]; exact hmid2
  have a6 : stepN (1 + k + 5 + 2 + 2 + (k + 2)) ⟨State.B, q + 5 + k, t⟩ =
      some ⟨State.E, q + 5 + k, (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true)⟩ := by rw [stepN_add, a5]; exact sE
  have hend : stepN 3 ⟨State.E, q + 5 + k, (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true)⟩ =
      some ⟨State.A, q + 6 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 5 + k) true) (q + 4 + k) false)⟩ := by simp [stepN, s9, s10, s11]
  have a7 : stepN (1 + k + 5 + 2 + 2 + (k + 2) + 3)
      ⟨State.B, q + 5 + k, t⟩ = some ⟨State.A, q + 6 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 5 + k) true) (q + 4 + k) false)⟩ := by
    rw [stepN_add, a6]; exact hend
  refine ⟨?_, ?_⟩
  · rw [show 2 * k + 15 = 1 + k + 5 + 2 + 2 + (k + 2) + 3 by omega]
    exact a7
  · rw [show 2 * k + 15
        = 1 + (k + (5 + (2 + (2 + ((k + 2) + 3))))) by omega]
    refine esafe_compose a1 (esafe_of_noE ?_) (esafe_compose sC
      (esafe_of_noE ?_) (esafe_compose hmid ?_ (esafe_compose sA
        (esafe_of_noE ?_) (esafe_compose hmid2 (esafe_of_noE ?_)
          (esafe_compose sE (esafe_of_strong ?_) ?_)))))
    · intro j d hj hjd
      have hj0 : j = 0 := by omega
      subst hj0
      have hdd : (⟨State.B, q + 5 + k, t⟩ : Config) = d := by
        simpa [stepN] using hjd
      rw [← hdd]; simp
    · intro j d hj hjd
      have hpart := sweep_C j ⟨State.C, q + 4 + k, t⟩ rfl
        (fun i hi => by
          show t (q + 4 + (k : Int) - (i : Int)) = true
          have := tc (k - 1 - i) (by omega)
          rw [show q + 4 + (k : Int) - (i : Int)
                = q + 5 + ((k - 1 - i : Nat) : Int) by omega]
          exact this)
      rw [hpart] at hjd
      rw [← Option.some_inj.mp hjd]; simp
    · intro j d hj hjd hE hread
      have hcase : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl
      · have hdd : (⟨State.C, q + 4, t⟩ : Config) = d := by
          simpa [stepN] using hjd
        rw [← hdd] at hE; simp at hE
      · rw [show stepN 1 ⟨State.C, q + 4, t⟩
              = some ⟨State.D, q + 3, (writeAt t (q + 4) true)⟩ from by simp [stepN, s2]] at hjd
        rw [← Option.some_inj.mp hjd] at hE; simp at hE
      · rw [show stepN 2 ⟨State.C, q + 4, t⟩
              = some ⟨State.B, q + 2, (writeAt (writeAt t (q + 4) true) (q + 3) false)⟩ from by
              simp [stepN, s2, s3]] at hjd
        rw [← Option.some_inj.mp hjd] at hE; simp at hE
      · -- PROBE 1: E reads the 0 at q+1; the counter cell q still holds 1
        rw [show stepN 3 ⟨State.C, q + 4, t⟩
              = some ⟨State.E, q + 1, (writeAt (writeAt t (q + 4) true) (q + 3) false)⟩ from by
              simp [stepN, s2, s3, s4]] at hjd
        rw [← Option.some_inj.mp hjd]
        show (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1 - 1) = true
        rw [show q + 1 - 1 = q by omega]; exact h2_q
      · rw [show stepN 4 ⟨State.C, q + 4, t⟩
              = some ⟨State.F, q, (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true)⟩ from by
              simp [stepN, s2, s3, s4, s5]] at hjd
        rw [← Option.some_inj.mp hjd] at hE; simp at hE
    · intro j d hj hjd
      have hpart := sweep_A j ⟨State.A, q + 1, (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false)⟩ rfl
        (fun i hi => by
          have hcase : i = 0 ∨ i = 1 := by omega
          rcases hcase with rfl | rfl
          · show (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 1 + ((0 : Nat) : Int)) = true
            rw [show q + 1 + ((0 : Nat) : Int) = q + 1 by omega]; exact h4_1
          · show (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 1 + ((1 : Nat) : Int)) = true
            rw [show q + 1 + ((1 : Nat) : Int) = q + 2 by omega]; exact h4_2)
      rw [hpart] at hjd
      rw [← Option.some_inj.mp hjd]; simp
    · intro j d hj hjd
      have hcase : j = 0 ∨ j = 1 := by omega
      rcases hcase with rfl | rfl
      · have hdd : (⟨State.A, q + 3, (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false)⟩ : Config) = d := by
          simpa [stepN] using hjd
        rw [← hdd]; simp
      · rw [show stepN 1 ⟨State.A, q + 3, (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false)⟩
              = some ⟨State.B, q + 4, (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true)⟩ from by simp [stepN, s7]] at hjd
        rw [← Option.some_inj.mp hjd]; simp
    · intro j d hj hjd hE
      have hpart := sweep_E j ⟨State.E, q + 3, (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true)⟩ rfl
        (fun i hi => h5_c i (by omega))
      rw [hpart] at hjd
      rw [← Option.some_inj.mp hjd]
      show (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 3 + (j : Int)) = true
      exact h5_c j (by omega)
    · intro j d hj hjd hE hread
      have hcase : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hcase with rfl | rfl | rfl
      · -- PROBE 2: E reads the 0 on the frontier; the c-top still holds 1
        have hdd : (⟨State.E, q + 5 + k, (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true)⟩ : Config) = d := by
          simpa [stepN] using hjd
        rw [← hdd]
        show (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 5 + (k : Int) - 1) = true
        rw [show q + 5 + (k : Int) - 1 = q + 4 + (k : Int) by omega]
        exact h5_top
      · rw [show stepN 1 ⟨State.E, q + 5 + k, (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true)⟩
              = some ⟨State.F, q + 4 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 5 + k) true)⟩ from by
              simp [stepN, s9]] at hjd
        rw [← Option.some_inj.mp hjd] at hE; simp at hE
      · rw [show stepN 2 ⟨State.E, q + 5 + k, (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true)⟩
              = some ⟨State.A, q + 5 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (q + 4) true) (q + 3) false) (q + 1) true) q false) (q + 3) true) (q + 5 + k) true) (q + 4 + k) false)⟩ from by
              simp [stepN, s9, s10]] at hjd
        rw [← Option.some_inj.mp hjd] at hE; simp at hE

/-- **The merge chain** (`m = 1`): the counter gains two cells.  From a
record `(a, 1, c)` anchored at `p`, the right end of the counter block
(`a = n ≥ 1`), exactly `2n + 2k + 22` raw steps land on the next
`B`-record with shape `(a+2, c+2, 2)`.  Both `E`-probes are safe; the
first one is safe precisely because the counter is non-empty. -/
theorem merge_chain {cfg : Config} {p : Int} (n k : Nat) (hn : 1 ≤ n)
    (hs : cfg.state = State.B) (hh : cfg.head = p + 4 + k)
    (ta : ∀ i : Nat, i < n → cfg.tape (p - i) = true)
    (tb0 : cfg.tape (p - n) = false) (tb1 : cfg.tape (p - n - 1) = false)
    (tb2 : cfg.tape (p - n - 2) = false)
    (tg1 : cfg.tape (p + 1) = false) (tm : cfg.tape (p + 2) = true)
    (tg2 : cfg.tape (p + 3) = false)
    (tc : ∀ i : Nat, i < k → cfg.tape (p + 4 + i) = true)
    (tf : cfg.tape (p + 4 + k) = false) (tf2 : cfg.tape (p + 5 + k) = false) :
    stepN (2 * n + 2 * k + 22) cfg = some ⟨State.B, p + 6 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + k) true) (p + 3 + k) false) (p + 5 + k) true)⟩ ∧
      ESafeSeg cfg (2 * n + 2 * k + 22) := by
  obtain ⟨s, hd, t⟩ := cfg
  simp only at hs hh ta tb0 tb1 tb2 tg1 tm tg2 tc tf tf2
  subst hs hd
  have hp : t p = true := by
    have := ta 0 (by omega); rw [show p - ((0 : Nat) : Int) = p by omega] at this
    exact this
  -- pointwise values
  have v1_2 : (writeAt t (p + 3) true) (p + 2) = true := by
    rw [writeAt_other t (p + 3) _ true (by omega)]; exact tm
  have v2_1 : (writeAt (writeAt t (p + 3) true) (p + 2) false) (p + 1) = false := by
    rw [writeAt_other _ (p + 2) _ false (by omega),
        writeAt_other t (p + 3) _ true (by omega)]; exact tg1
  have v2_a : ∀ i : Nat, i < n → (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - i) = true := by
    intro i hi
    rw [writeAt_other _ (p + 2) _ false (by omega),
        writeAt_other t (p + 3) _ true (by omega)]
    exact ta i hi
  have v2_b0 : (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) = false := by
    rw [writeAt_other _ (p + 2) _ false (by omega),
        writeAt_other t (p + 3) _ true (by omega)]; exact tb0
  have v3_b1 : (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) = false := by
    rw [writeAt_other _ (p - n) _ true (by omega),
        writeAt_other _ (p + 2) _ false (by omega),
        writeAt_other t (p + 3) _ true (by omega)]; exact tb1
  have v4_b2 : (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) = false := by
    rw [writeAt_other _ (p - n - 1) _ true (by omega),
        writeAt_other _ (p - n) _ true (by omega),
        writeAt_other _ (p + 2) _ false (by omega),
        writeAt_other t (p + 3) _ true (by omega)]; exact tb2
  have v5_b1 : (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p - n - 1) = true := by
    rw [writeAt_other _ (p - n - 2) _ true (by omega)]
    exact writeAt_same _ (p - n - 1) true
  have v5_seq : ∀ i : Nat, i < n + 3 → (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p - n - 2 + i) = true := by
    intro i hi
    by_cases hi0 : i = 0
    · rw [hi0, show p - (n : Int) - 2 + ((0 : Nat) : Int) = p - n - 2 by omega]
      exact writeAt_same _ (p - n - 2) true
    · by_cases hi1 : i = 1
      · rw [hi1, show p - (n : Int) - 2 + ((1 : Nat) : Int) = p - n - 1 by omega]
        exact v5_b1
      · by_cases hi2 : i = 2
        · rw [hi2, show p - (n : Int) - 2 + ((2 : Nat) : Int) = p - n by omega,
              writeAt_other _ (p - n - 2) _ true (by omega),
              writeAt_other _ (p - n - 1) _ true (by omega)]
          exact writeAt_same _ (p - n) true
        · rw [writeAt_other _ (p - n - 2) _ true (by omega),
              writeAt_other _ (p - n - 1) _ true (by omega),
              writeAt_other _ (p - n) _ true (by omega)]
          have := v2_a (n + 2 - i) (by omega)
          rw [show p - (n : Int) - 2 + (i : Int)
                = p - ((n + 2 - i : Nat) : Int) by omega]
          exact this
  have v5_p : (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) p = true := by
    rw [writeAt_other _ (p - n - 2) _ true (by omega),
        writeAt_other _ (p - n - 1) _ true (by omega),
        writeAt_other _ (p - n) _ true (by omega)]
    have h0 := v2_a 0 (by omega)
    rw [show (p : Int) - ((0 : Nat) : Int) = p by omega] at h0
    exact h0
  have v5_1 : (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) = false := by
    rw [writeAt_other _ (p - n - 2) _ true (by omega),
        writeAt_other _ (p - n - 1) _ true (by omega),
        writeAt_other _ (p - n) _ true (by omega)]
    exact v2_1
  have v6_p : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p = true := by
    rw [writeAt_other _ (p + 1) _ true (by omega)]; exact v5_p
  have v7_1 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 1) = true := by
    rw [writeAt_other _ p _ false (by omega)]
    exact writeAt_same _ (p + 1) true
  have v7_2 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) = false := by
    rw [writeAt_other _ p _ false (by omega),
        writeAt_other _ (p + 1) _ true (by omega),
        writeAt_other _ (p - n - 2) _ true (by omega),
        writeAt_other _ (p - n - 1) _ true (by omega),
        writeAt_other _ (p - n) _ true (by omega)]
    exact writeAt_same _ (p + 2) false
  have v8_3 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 3) = true := by
    rw [writeAt_other _ (p + 2) _ true (by omega),
        writeAt_other _ p _ false (by omega),
        writeAt_other _ (p + 1) _ true (by omega),
        writeAt_other _ (p - n - 2) _ true (by omega),
        writeAt_other _ (p - n - 1) _ true (by omega),
        writeAt_other _ (p - n) _ true (by omega),
        writeAt_other _ (p + 2) _ false (by omega)]
    exact writeAt_same t (p + 3) true
  have v8_seq : ∀ i : Nat, i < k + 2 → (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 2 + i) = true := by
    intro i hi
    by_cases hi0 : i = 0
    · rw [hi0, show (p : Int) + 2 + ((0 : Nat) : Int) = p + 2 by omega]
      exact writeAt_same _ (p + 2) true
    · by_cases hi1 : i = 1
      · rw [hi1, show (p : Int) + 2 + ((1 : Nat) : Int) = p + 3 by omega]
        exact v8_3
      · rw [writeAt_other _ (p + 2) _ true (by omega),
            writeAt_other _ p _ false (by omega),
            writeAt_other _ (p + 1) _ true (by omega),
            writeAt_other _ (p - n - 2) _ true (by omega),
            writeAt_other _ (p - n - 1) _ true (by omega),
            writeAt_other _ (p - n) _ true (by omega),
            writeAt_other _ (p + 2) _ false (by omega),
            writeAt_other t (p + 3) _ true (by omega)]
        have := tc (i - 2) (by omega)
        rw [show (p : Int) + 2 + (i : Int) = p + 4 + ((i - 2 : Nat) : Int)
              by omega]
        exact this
  have v8_top : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 3 + k) = true := by
    by_cases hk0 : k = 0
    · rw [hk0, show (p : Int) + 3 + ((0 : Nat) : Int) = p + 3 by omega]
      exact v8_3
    · have := v8_seq (k + 1) (by omega)
      rw [show (p : Int) + 2 + ((k + 1 : Nat) : Int) = p + 3 + (k : Int)
            by omega] at this
      exact this
  have v8_f : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + k) = false := by
    rw [writeAt_other _ (p + 2) _ true (by omega),
        writeAt_other _ p _ false (by omega),
        writeAt_other _ (p + 1) _ true (by omega),
        writeAt_other _ (p - n - 2) _ true (by omega),
        writeAt_other _ (p - n - 1) _ true (by omega),
        writeAt_other _ (p - n) _ true (by omega),
        writeAt_other _ (p + 2) _ false (by omega),
        writeAt_other t (p + 3) _ true (by omega)]
    exact tf
  have v9_top : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + k) true) (p + 3 + k) = true := by
    rw [writeAt_other _ (p + 4 + k) _ true (by omega)]; exact v8_top
  have v10_f : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + k) true) (p + 3 + k) false) (p + 4 + k) = true := by
    rw [writeAt_other _ (p + 3 + k) _ false (by omega)]
    exact writeAt_same _ (p + 4 + k) true
  have v10_f2 : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + k) true) (p + 3 + k) false) (p + 5 + k) = false := by
    rw [writeAt_other _ (p + 3 + k) _ false (by omega),
        writeAt_other _ (p + 4 + k) _ true (by omega),
        writeAt_other _ (p + 2) _ true (by omega),
        writeAt_other _ p _ false (by omega),
        writeAt_other _ (p + 1) _ true (by omega),
        writeAt_other _ (p - n - 2) _ true (by omega),
        writeAt_other _ (p - n - 1) _ true (by omega),
        writeAt_other _ (p - n) _ true (by omega),
        writeAt_other _ (p + 2) _ false (by omega),
        writeAt_other t (p + 3) _ true (by omega)]
    exact tf2
  -- the trajectory
  have s1 : step ⟨State.B, p + 4 + k, t⟩ = some ⟨State.C, p + 3 + k, t⟩ := by
    have hself : writeAt t (p + 4 + (k : Int)) false = t := writeAt_self t _ tf
    simp [step, instr, tf, move, hself]
    try omega
  have sC1 : stepN k ⟨State.C, p + 3 + k, t⟩ = some ⟨State.C, p + 3, t⟩ := by
    have h := sweep_C k ⟨State.C, p + 3 + k, t⟩ rfl
      (fun i hi => by
        show t (p + 3 + (k : Int) - (i : Int)) = true
        have := tc (k - 1 - i) (by omega)
        rw [show p + 3 + (k : Int) - (i : Int)
              = p + 4 + ((k - 1 - i : Nat) : Int) by omega]
        exact this)
    rw [show p + 3 + (k : Int) - (k : Int) = p + 3 by omega] at h
    exact h
  have s2 : step ⟨State.C, p + 3, t⟩ = some ⟨State.D, p + 2, (writeAt t (p + 3) true)⟩ := by
    simp [step, instr, tg2, move]
    try omega
  have s3 : step ⟨State.D, p + 2, (writeAt t (p + 3) true)⟩ = some ⟨State.B, p + 1, (writeAt (writeAt t (p + 3) true) (p + 2) false)⟩ := by
    simp [step, instr, v1_2, move]
    try omega
  have s4 : step ⟨State.B, p + 1, (writeAt (writeAt t (p + 3) true) (p + 2) false)⟩ = some ⟨State.C, p, (writeAt (writeAt t (p + 3) true) (p + 2) false)⟩ := by
    have hself : writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p + 1) false = (writeAt (writeAt t (p + 3) true) (p + 2) false) :=
      writeAt_self _ _ v2_1
    simp [step, instr, v2_1, move, hself]
    try omega
  have sC2 : stepN n ⟨State.C, p, (writeAt (writeAt t (p + 3) true) (p + 2) false)⟩ = some ⟨State.C, p - n, (writeAt (writeAt t (p + 3) true) (p + 2) false)⟩ := by
    have h := sweep_C n ⟨State.C, p, (writeAt (writeAt t (p + 3) true) (p + 2) false)⟩ rfl (fun i hi => v2_a i hi)
    exact h
  have s5 : step ⟨State.C, p - n, (writeAt (writeAt t (p + 3) true) (p + 2) false)⟩ = some ⟨State.D, p - n - 1, (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true)⟩ := by
    simp [step, instr, v2_b0, move]
    try omega
  have s6 : step ⟨State.D, p - n - 1, (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true)⟩ =
      some ⟨State.A, p - n - 2, (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true)⟩ := by
    simp [step, instr, v3_b1, move]
    try omega
  have s7 : step ⟨State.A, p - n - 2, (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true)⟩ =
      some ⟨State.B, p - n - 1, (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true)⟩ := by
    simp [step, instr, v4_b2, move]
    try omega
  have s8 : step ⟨State.B, p - n - 1, (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true)⟩ =
      some ⟨State.E, p - n - 2, (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true)⟩ := by
    have hself : writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p - n - 1) true = (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) :=
      writeAt_self _ _ v5_b1
    simp [step, instr, v5_b1, move, hself]
    try omega
  have sE1 : stepN (n + 3) ⟨State.E, p - n - 2, (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true)⟩ =
      some ⟨State.E, p + 1, (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true)⟩ := by
    have h := sweep_E (n + 3) ⟨State.E, p - n - 2, (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true)⟩ rfl
      (fun i hi => v5_seq i hi)
    rw [show p - (n : Int) - 2 + ((n + 3 : Nat) : Int) = p + 1 by omega] at h
    exact h
  have s9 : step ⟨State.E, p + 1, (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true)⟩ = some ⟨State.F, p, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true)⟩ := by
    simp [step, instr, v5_1, move]
    try omega
  have s10 : step ⟨State.F, p, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true)⟩ = some ⟨State.A, p + 1, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false)⟩ := by
    simp [step, instr, v6_p, move]
    try omega
  have s11 : step ⟨State.A, p + 1, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false)⟩ = some ⟨State.A, p + 2, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false)⟩ := by
    have hself : writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 1) true = (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) := writeAt_self _ _ v7_1
    simp [step, instr, v7_1, move, hself]
    try omega
  have s12 : step ⟨State.A, p + 2, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false)⟩ = some ⟨State.B, p + 3, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true)⟩ := by
    simp [step, instr, v7_2, move]
    try omega
  have s13 : step ⟨State.B, p + 3, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true)⟩ = some ⟨State.E, p + 2, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true)⟩ := by
    have hself : writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 3) true = (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) := writeAt_self _ _ v8_3
    simp [step, instr, v8_3, move, hself]
    try omega
  have sE2 : stepN (k + 2) ⟨State.E, p + 2, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true)⟩ =
      some ⟨State.E, p + 4 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true)⟩ := by
    have h := sweep_E (k + 2) ⟨State.E, p + 2, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true)⟩ rfl
      (fun i hi => v8_seq i hi)
    rw [show (p : Int) + 2 + ((k + 2 : Nat) : Int) = p + 4 + (k : Int)
          by omega] at h
    exact h
  have s14 : step ⟨State.E, p + 4 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true)⟩ =
      some ⟨State.F, p + 3 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + k) true)⟩ := by
    simp [step, instr, v8_f, move]
    try omega
  have s15 : step ⟨State.F, p + 3 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + k) true)⟩ =
      some ⟨State.A, p + 4 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + k) true) (p + 3 + k) false)⟩ := by
    simp [step, instr, v9_top, move]
    try omega
  have s16 : step ⟨State.A, p + 4 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + k) true) (p + 3 + k) false)⟩ =
      some ⟨State.A, p + 5 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + k) true) (p + 3 + k) false)⟩ := by
    have hself : writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + k) true) (p + 3 + k) false) (p + 4 + (k : Int)) true = (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + k) true) (p + 3 + k) false) :=
      writeAt_self _ _ v10_f
    simp [step, instr, v10_f, move, hself]
    try omega
  have s17 : step ⟨State.A, p + 5 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + k) true) (p + 3 + k) false)⟩ =
      some ⟨State.B, p + 6 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + k) true) (p + 3 + k) false) (p + 5 + k) true)⟩ := by
    simp [step, instr, v10_f2, move]
    try omega
  -- assemble
  have a1 : stepN 1 ⟨State.B, p + 4 + k, t⟩ =
      some ⟨State.C, p + 3 + k, t⟩ := by simp [stepN, s1]
  have a2 : stepN (1 + k) ⟨State.B, p + 4 + k, t⟩ =
      some ⟨State.C, p + 3, t⟩ := by rw [stepN_add, a1]; exact sC1
  have m1 : stepN 3 ⟨State.C, p + 3, t⟩ = some ⟨State.C, p, (writeAt (writeAt t (p + 3) true) (p + 2) false)⟩ := by
    simp [stepN, s2, s3, s4]
  have a3 : stepN (1 + k + 3) ⟨State.B, p + 4 + k, t⟩ =
      some ⟨State.C, p, (writeAt (writeAt t (p + 3) true) (p + 2) false)⟩ := by rw [stepN_add, a2]; exact m1
  have a4 : stepN (1 + k + 3 + n) ⟨State.B, p + 4 + k, t⟩ =
      some ⟨State.C, p - n, (writeAt (writeAt t (p + 3) true) (p + 2) false)⟩ := by rw [stepN_add, a3]; exact sC2
  have m2 : stepN 4 ⟨State.C, p - n, (writeAt (writeAt t (p + 3) true) (p + 2) false)⟩ =
      some ⟨State.E, p - n - 2, (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true)⟩ := by simp [stepN, s5, s6, s7, s8]
  have a5 : stepN (1 + k + 3 + n + 4) ⟨State.B, p + 4 + k, t⟩ =
      some ⟨State.E, p - n - 2, (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true)⟩ := by rw [stepN_add, a4]; exact m2
  have a6 : stepN (1 + k + 3 + n + 4 + (n + 3)) ⟨State.B, p + 4 + k, t⟩ =
      some ⟨State.E, p + 1, (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true)⟩ := by rw [stepN_add, a5]; exact sE1
  have m3 : stepN 5 ⟨State.E, p + 1, (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true)⟩ =
      some ⟨State.E, p + 2, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true)⟩ := by simp [stepN, s9, s10, s11, s12, s13]
  have a7 : stepN (1 + k + 3 + n + 4 + (n + 3) + 5) ⟨State.B, p + 4 + k, t⟩ =
      some ⟨State.E, p + 2, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true)⟩ := by rw [stepN_add, a6]; exact m3
  have a8 : stepN (1 + k + 3 + n + 4 + (n + 3) + 5 + (k + 2))
      ⟨State.B, p + 4 + k, t⟩ = some ⟨State.E, p + 4 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true)⟩ := by
    rw [stepN_add, a7]; exact sE2
  have m4 : stepN 4 ⟨State.E, p + 4 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true)⟩ =
      some ⟨State.B, p + 6 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + k) true) (p + 3 + k) false) (p + 5 + k) true)⟩ := by simp [stepN, s14, s15, s16, s17]
  have a9 : stepN (1 + k + 3 + n + 4 + (n + 3) + 5 + (k + 2) + 4)
      ⟨State.B, p + 4 + k, t⟩ = some ⟨State.B, p + 6 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + k) true) (p + 3 + k) false) (p + 5 + k) true)⟩ := by
    rw [stepN_add, a8]; exact m4
  refine ⟨?_, ?_⟩
  · rw [show 2 * n + 2 * k + 22
          = 1 + k + 3 + n + 4 + (n + 3) + 5 + (k + 2) + 4 by omega]
    exact a9
  · rw [show 2 * n + 2 * k + 22
        = 1 + (k + (3 + (n + (4 + ((n + 3) + (5 + ((k + 2) + 4))))))) by omega]
    refine esafe_compose a1 (esafe_of_noE ?_) (esafe_compose sC1
      (esafe_of_noE ?_) (esafe_compose m1 (esafe_of_noE ?_) (esafe_compose sC2
        (esafe_of_noE ?_) (esafe_compose m2 (esafe_of_noE ?_) (esafe_compose sE1
          (esafe_of_strong ?_) (esafe_compose m3 ?_ (esafe_compose sE2
            (esafe_of_strong ?_) ?_)))))))
    · intro j d hj hjd
      have hj0 : j = 0 := by omega
      subst hj0
      have hdd : (⟨State.B, p + 4 + k, t⟩ : Config) = d := by
        simpa [stepN] using hjd
      rw [← hdd]; simp
    · intro j d hj hjd
      have hpart := sweep_C j ⟨State.C, p + 3 + k, t⟩ rfl
        (fun i hi => by
          show t (p + 3 + (k : Int) - (i : Int)) = true
          have := tc (k - 1 - i) (by omega)
          rw [show p + 3 + (k : Int) - (i : Int)
                = p + 4 + ((k - 1 - i : Nat) : Int) by omega]
          exact this)
      rw [hpart] at hjd
      rw [← Option.some_inj.mp hjd]; simp
    · intro j d hj hjd
      have hcase : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hcase with rfl | rfl | rfl
      · have hdd : (⟨State.C, p + 3, t⟩ : Config) = d := by
          simpa [stepN] using hjd
        rw [← hdd]; simp
      · rw [show stepN 1 ⟨State.C, p + 3, t⟩
              = some ⟨State.D, p + 2, (writeAt t (p + 3) true)⟩ from by simp [stepN, s2]] at hjd
        rw [← Option.some_inj.mp hjd]; simp
      · rw [show stepN 2 ⟨State.C, p + 3, t⟩
              = some ⟨State.B, p + 1, (writeAt (writeAt t (p + 3) true) (p + 2) false)⟩ from by
              simp [stepN, s2, s3]] at hjd
        rw [← Option.some_inj.mp hjd]; simp
    · intro j d hj hjd
      have hpart := sweep_C j ⟨State.C, p, (writeAt (writeAt t (p + 3) true) (p + 2) false)⟩ rfl
        (fun i hi => v2_a i (by omega))
      rw [hpart] at hjd
      rw [← Option.some_inj.mp hjd]; simp
    · intro j d hj hjd
      have hcase : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · have hdd : (⟨State.C, p - n, (writeAt (writeAt t (p + 3) true) (p + 2) false)⟩ : Config) = d := by
          simpa [stepN] using hjd
        rw [← hdd]; simp
      · rw [show stepN 1 ⟨State.C, p - n, (writeAt (writeAt t (p + 3) true) (p + 2) false)⟩
              = some ⟨State.D, p - n - 1, (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true)⟩ from by
              simp [stepN, s5]] at hjd
        rw [← Option.some_inj.mp hjd]; simp
      · rw [show stepN 2 ⟨State.C, p - n, (writeAt (writeAt t (p + 3) true) (p + 2) false)⟩
              = some ⟨State.A, p - n - 2, (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true)⟩ from by
              simp [stepN, s5, s6]] at hjd
        rw [← Option.some_inj.mp hjd]; simp
      · rw [show stepN 3 ⟨State.C, p - n, (writeAt (writeAt t (p + 3) true) (p + 2) false)⟩
              = some ⟨State.B, p - n - 1, (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true)⟩ from by
              simp [stepN, s5, s6, s7]] at hjd
        rw [← Option.some_inj.mp hjd]; simp
    · intro j d hj hjd hE
      have hpart := sweep_E j ⟨State.E, p - n - 2, (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true)⟩ rfl
        (fun i hi => v5_seq i (by omega))
      rw [hpart] at hjd
      rw [← Option.some_inj.mp hjd]
      show (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p - n - 2 + (j : Int)) = true
      exact v5_seq j (by omega)
    · intro j d hj hjd hE hread
      have hcase : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl
      · -- PROBE 1: safe exactly because the counter block is non-empty
        have hdd : (⟨State.E, p + 1, (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true)⟩ : Config) = d := by
          simpa [stepN] using hjd
        rw [← hdd]
        show (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1 - 1) = true
        rw [show (p : Int) + 1 - 1 = p by omega]; exact v5_p
      · rw [show stepN 1 ⟨State.E, p + 1, (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true)⟩
              = some ⟨State.F, p, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true)⟩ from by simp [stepN, s9]] at hjd
        rw [← Option.some_inj.mp hjd] at hE; simp at hE
      · rw [show stepN 2 ⟨State.E, p + 1, (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true)⟩
              = some ⟨State.A, p + 1, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false)⟩ from by
              simp [stepN, s9, s10]] at hjd
        rw [← Option.some_inj.mp hjd] at hE; simp at hE
      · rw [show stepN 3 ⟨State.E, p + 1, (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true)⟩
              = some ⟨State.A, p + 2, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false)⟩ from by
              simp [stepN, s9, s10, s11]] at hjd
        rw [← Option.some_inj.mp hjd] at hE; simp at hE
      · rw [show stepN 4 ⟨State.E, p + 1, (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true)⟩
              = some ⟨State.B, p + 3, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true)⟩ from by
              simp [stepN, s9, s10, s11, s12]] at hjd
        rw [← Option.some_inj.mp hjd] at hE; simp at hE
    · intro j d hj hjd hE
      have hpart := sweep_E j ⟨State.E, p + 2, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true)⟩ rfl
        (fun i hi => v8_seq i (by omega))
      rw [hpart] at hjd
      rw [← Option.some_inj.mp hjd]
      show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 2 + (j : Int)) = true
      exact v8_seq j (by omega)
    · intro j d hj hjd hE hread
      have hcase : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · -- PROBE 2: the c-block top still holds a 1
        have hdd : (⟨State.E, p + 4 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true)⟩ : Config) = d := by
          simpa [stepN] using hjd
        rw [← hdd]
        show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + (k : Int) - 1) = true
        rw [show (p : Int) + 4 + (k : Int) - 1 = p + 3 + (k : Int) by omega]
        exact v8_top
      · rw [show stepN 1 ⟨State.E, p + 4 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true)⟩
              = some ⟨State.F, p + 3 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + k) true)⟩ from by
              simp [stepN, s14]] at hjd
        rw [← Option.some_inj.mp hjd] at hE; simp at hE
      · rw [show stepN 2 ⟨State.E, p + 4 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true)⟩
              = some ⟨State.A, p + 4 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + k) true) (p + 3 + k) false)⟩ from by
              simp [stepN, s14, s15]] at hjd
        rw [← Option.some_inj.mp hjd] at hE; simp at hE
      · rw [show stepN 3 ⟨State.E, p + 4 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true)⟩
              = some ⟨State.A, p + 5 + k, (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt t (p + 3) true) (p + 2) false) (p - n) true) (p - n - 1) true) (p - n - 2) true) (p + 1) true) p false) (p + 2) true) (p + 4 + k) true) (p + 3 + k) false)⟩ from by
              simp [stepN, s14, s15, s16]] at hjd
        rw [← Option.some_inj.mp hjd] at hE; simp at hE

/-!
## The abstract orbit, the grammar, and the main theorem

Antihydra's records stay at dimension three, so the abstract state is a
plain triple `(a, m, c)` — no level hierarchy, no chain induction.  `a`
is the counter: frozen by the hydra rule, decremented by the drop,
incremented by two by the merge.
-/

structure AState where
  a : Nat
  m : Nat
  c : Nat
deriving Repr, DecidableEq

/-- The abstract transition.  `none` marks exactly the value patterns
whose absence from the orbit is the Antihydra conjecture. -/
def astep : AState → Option AState
  | ⟨a, m, c⟩ =>
      if 3 ≤ m then some ⟨a, m - 2, c + 3⟩
      else if m = 2 then (if 2 ≤ a then some ⟨a - 1, c + 3, 2⟩ else none)
      else if m = 1 then some ⟨a + 2, c + 2, 2⟩
      else none

def aorbit : Nat → Option AState
  | 0 => some ⟨2, 7, 2⟩
  | k + 1 => match aorbit k with
      | none => none
      | some s => astep s

/-- **The Antihydra conjecture**, in the exact form the machine needs:
the abstract orbit never dies.  Equivalently, the counter never runs out
when the drop rule fires.

Informally: this is the *only* unproven sentence in the whole development
— a statement about a sequence of integer triples, with no tape, no head,
no machine.  Everything else in this file converts the machine's fate
into exactly this sentence. -/
def SafeOrbitA : Prop := ∀ k : Nat, aorbit k ≠ none

/-- A configuration realizing an abstract state: blank, the counter
block ending at `p`, a `0`, the `m`-block, a `0`, the `c`-block, then the
head on the fresh frontier and blank beyond.

Informally: the *tape grammar* — eight conjuncts that pin every one of the
infinitely many cells from just three numbers and an anchor.  Transport
lemmas push it through each rule, and its demand for a non-empty counter
block (`1 ≤ a`) is the origin of the one honest delta against the
community's conjecture statement. -/
def Realizes : AState → Config → Prop
  | ⟨a, m, c⟩, cfg =>
      1 ≤ a ∧ 1 ≤ m ∧ 1 ≤ c ∧ cfg.state = State.B ∧
      ∃ p : Int,
        (∀ x : Int, x < p - a + 1 → cfg.tape x = false) ∧
        (∀ i : Nat, i < a → cfg.tape (p - i) = true) ∧
        cfg.tape (p + 1) = false ∧
        (∀ i : Nat, i < m → cfg.tape (p + 2 + i) = true) ∧
        cfg.tape (p + 2 + m) = false ∧
        (∀ i : Nat, i < c → cfg.tape (p + 3 + m + i) = true) ∧
        (∀ x : Int, p + 3 + m + c ≤ x → cfg.tape x = false) ∧
        cfg.head = p + 3 + m + c

def OrbitInv (cfg : Config) : Prop :=
  ∃ (k : Nat) (s : AState), aorbit k = some s ∧ Realizes s cfg

/-- The concrete 62-step startup tape, in execution order. -/
def startTape : Int → Bool :=
  writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (blankTape) 0 true) 1 false) 0 true) (-1 : Int) true) (-2 : Int) true) (-3 : Int) true) (-2 : Int) true) (-3 : Int) true) (-2 : Int) true) (-1 : Int) true) 0 true) 1 true) 0 false) 1 true) 2 true) 3 false) 2 true) 1 true) 0 true) (-1 : Int) false) (-2 : Int) true) (-3 : Int) true) (-2 : Int) true) (-1 : Int) true) (-2 : Int) false) (-1 : Int) true) 0 true) 1 true) 2 true) 3 true) 4 false) 3 true) 2 true) 1 true) 0 true) (-1 : Int) true) (-2 : Int) true) (-3 : Int) false) (-4 : Int) false) (-5 : Int) true) (-6 : Int) true) (-7 : Int) true) (-6 : Int) true) (-7 : Int) true) (-6 : Int) true) (-5 : Int) true) (-4 : Int) true) (-5 : Int) false) (-4 : Int) true) (-3 : Int) true) (-2 : Int) true) (-3 : Int) true) (-2 : Int) true) (-1 : Int) true) 0 true) 1 true) 2 true) 3 true) 4 true) 3 false) 4 true) 5 true

def safeCfg (c : Config) : Bool :=
  match c.state with
  | State.E => c.tape c.head || c.tape (c.head - 1)
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
    c.tape (c.head - 1) = true := by
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

set_option maxRecDepth 100000 in
theorem startup_run :
    stepN 62 blankStart = some ⟨State.B, 6, startTape⟩ := by
  rfl

set_option maxRecDepth 100000 in
theorem startup_safe : ESafeSeg blankStart 62 := by
  apply esafe_of_checkSafe
  rfl

theorem startTape_blank_left : ∀ x : Int, x < -7 → startTape x = false := by
  intro x hx
  unfold startTape
  rw [writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega)]
  rfl

theorem startTape_blank_right : ∀ x : Int, 6 ≤ x → startTape x = false := by
  intro x hx
  unfold startTape
  rw [writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega),
          writeAt_other _ _ x _ (by omega), writeAt_other _ _ x _ (by omega)]
  rfl

/-- Transport for the hydra rule: `(a, m+3, c) → (a, m+1, c+3)`. 

Informally: the abstract hydra rule, played on the tape.  Given a
configuration realizing `(a, m+3, c)`, the proven trajectory of
`hydra_step` runs and the eight grammar conjuncts are re-established for
`(a, m+1, c+3)` — cell-by-cell bookkeeping, no new ideas.  Its two
siblings do the same for drop and merge. -/
theorem transport_hydra {cfg : Config} {a m c : Nat}
    (h : Realizes ⟨a, m + 3, c⟩ cfg) :
    ∃ (N : Nat) (cfg' : Config), 0 < N ∧ stepN N cfg = some cfg' ∧
      Realizes ⟨a, m + 1, c + 3⟩ cfg' ∧ ESafeSeg cfg N := by
  obtain ⟨ha1, _hm1, hc1, hsB, p, hbl, ha, hg1, hm, hg2, hc, hbr, hhead⟩ := h
  obtain ⟨hrun, hsafe⟩ := hydra_step (cfg := cfg) (p := p + m + 4) c hsB
    (by rw [hhead]; omega)
    (by rw [show p + (m : Int) + 4 - 2 = p + 2 + ((m : Nat) : Int) by omega]
        exact hm m (by omega))
    (by rw [show p + (m : Int) + 4 - 1 = p + 2 + ((m + 1 : Nat) : Int) by omega]
        exact hm (m + 1) (by omega))
    (by rw [show p + (m : Int) + 4 = p + 2 + ((m + 2 : Nat) : Int) by omega]
        exact hm (m + 2) (by omega))
    (by rw [show p + (m : Int) + 4 + 1 = p + 2 + ((m + 3 : Nat) : Int) by omega]
        exact hg2)
    (fun i hi => by
      rw [show p + (m : Int) + 4 + 2 + (i : Int)
            = p + 3 + ((m + 3 : Nat) : Int) + (i : Int) by omega]
      exact hc i hi)
    (by rw [show p + (m : Int) + 4 + 2 + (c : Int)
              = p + 3 + ((m + 3 : Nat) : Int) + (c : Int) by omega]
        exact hbr _ (by omega))
  rw [show p + (m : Int) + 4 + 1 = p + (m : Int) + 5 by omega,
      show p + (m : Int) + 4 - 1 = p + (m : Int) + 3 by omega,
      show p + (m : Int) + 4 + 2 + (c : Int)
        = p + (m : Int) + 6 + (c : Int) by omega,
      show p + (m : Int) + 4 + 3 + (c : Int)
        = p + (m : Int) + 7 + (c : Int) by omega] at hrun
  refine ⟨2 * c + 11, ⟨State.B, p + m + 7 + c, writeAt (writeAt (writeAt cfg.tape (p + (m : Int) + 5) true)
      (p + (m : Int) + 3) false) (p + (m : Int) + 6 + (c : Int)) true⟩, by omega, hrun, ?_, hsafe⟩
  refine ⟨ha1, by omega, by omega, rfl, p, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    show (writeAt (writeAt (writeAt cfg.tape (p + (m : Int) + 5) true)
      (p + (m : Int) + 3) false) (p + (m : Int) + 6 + (c : Int)) true) x = false
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact hbl x hx
  · intro i hi
    show (writeAt (writeAt (writeAt cfg.tape (p + (m : Int) + 5) true)
      (p + (m : Int) + 3) false) (p + (m : Int) + 6 + (c : Int)) true) (p - i) = true
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact ha i hi
  · show (writeAt (writeAt (writeAt cfg.tape (p + (m : Int) + 5) true)
      (p + (m : Int) + 3) false) (p + (m : Int) + 6 + (c : Int)) true) (p + 1) = false
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact hg1
  · intro i hi
    show (writeAt (writeAt (writeAt cfg.tape (p + (m : Int) + 5) true)
      (p + (m : Int) + 3) false) (p + (m : Int) + 6 + (c : Int)) true) (p + 2 + i) = true
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact hm i (by omega)
  · show (writeAt (writeAt (writeAt cfg.tape (p + (m : Int) + 5) true)
      (p + (m : Int) + 3) false) (p + (m : Int) + 6 + (c : Int)) true) (p + 2 + ((m + 1 : Nat) : Int)) = false
    rw [show p + 2 + ((m + 1 : Nat) : Int) = p + (m : Int) + 3 by omega]
    rw [writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ (p + (m : Int) + 3) false
  · intro i hi
    by_cases hi0 : i = 0
    · rw [hi0]
      show (writeAt (writeAt (writeAt cfg.tape (p + (m : Int) + 5) true)
      (p + (m : Int) + 3) false) (p + (m : Int) + 6 + (c : Int)) true) (p + 3 + ((m + 1 : Nat) : Int) + ((0 : Nat) : Int)) = true
      rw [show p + 3 + ((m + 1 : Nat) : Int) + ((0 : Nat) : Int)
            = p + 2 + ((m + 2 : Nat) : Int) by omega]
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
      exact hm (m + 2) (by omega)
    · by_cases hi1 : i = 1
      · rw [hi1]
        show (writeAt (writeAt (writeAt cfg.tape (p + (m : Int) + 5) true)
      (p + (m : Int) + 3) false) (p + (m : Int) + 6 + (c : Int)) true) (p + 3 + ((m + 1 : Nat) : Int) + ((1 : Nat) : Int)) = true
        rw [show p + 3 + ((m + 1 : Nat) : Int) + ((1 : Nat) : Int)
              = p + (m : Int) + 5 by omega]
        rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
        exact writeAt_same _ (p + (m : Int) + 5) true
      · by_cases hilast : i = c + 2
        · rw [hilast]
          show (writeAt (writeAt (writeAt cfg.tape (p + (m : Int) + 5) true)
      (p + (m : Int) + 3) false) (p + (m : Int) + 6 + (c : Int)) true) (p + 3 + ((m + 1 : Nat) : Int) + ((c + 2 : Nat) : Int)) = true
          rw [show p + 3 + ((m + 1 : Nat) : Int) + ((c + 2 : Nat) : Int)
                = p + (m : Int) + 6 + (c : Int) by omega]
          exact writeAt_same _ (p + (m : Int) + 6 + (c : Int)) true
        · show (writeAt (writeAt (writeAt cfg.tape (p + (m : Int) + 5) true)
      (p + (m : Int) + 3) false) (p + (m : Int) + 6 + (c : Int)) true) (p + 3 + ((m + 1 : Nat) : Int) + (i : Int)) = true
          rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
          have := hc (i - 2) (by omega)
          rw [show p + 3 + ((m + 3 : Nat) : Int) + ((i - 2 : Nat) : Int)
                = p + 3 + ((m + 1 : Nat) : Int) + (i : Int) by omega] at this
          exact this
  · intro x hx
    show (writeAt (writeAt (writeAt cfg.tape (p + (m : Int) + 5) true)
      (p + (m : Int) + 3) false) (p + (m : Int) + 6 + (c : Int)) true) x = false
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact hbr x (by omega)
  · show p + (m : Int) + 7 + (c : Int)
        = p + 3 + ((m + 1 : Nat) : Int) + ((c + 3 : Nat) : Int)
    omega

/-- Transport for the drop rule: `(a+2, 2, c) → (a+1, c+3, 2)`. -/
theorem transport_drop {cfg : Config} {a c : Nat}
    (h : Realizes ⟨a + 2, 2, c⟩ cfg) :
    ∃ (N : Nat) (cfg' : Config), 0 < N ∧ stepN N cfg = some cfg' ∧
      Realizes ⟨a + 1, c + 3, 2⟩ cfg' ∧ ESafeSeg cfg N := by
  obtain ⟨ha1, _hm1, hc1, hsB, p, hbl, ha, hg1, hm, hg2, hc, hbr, hhead⟩ := h
  obtain ⟨hrun, hsafe⟩ := drop_step (cfg := cfg) (q := p) c hsB
    (by rw [hhead]; omega)
    (by have := ha 0 (by omega)
        rw [show p - ((0 : Nat) : Int) = p by omega] at this; exact this)
    hg1
    (by have := hm 0 (by omega)
        rw [show p + 2 + ((0 : Nat) : Int) = p + 2 by omega] at this; exact this)
    (by have := hm 1 (by omega)
        rw [show p + 2 + ((1 : Nat) : Int) = p + 3 by omega] at this; exact this)
    (by rw [show p + 4 = p + 2 + ((2 : Nat) : Int) by omega]; exact hg2)
    (fun i hi => by
      rw [show p + 5 + (i : Int) = p + 3 + ((2 : Nat) : Int) + (i : Int)
            by omega]
      exact hc i hi)
    (by rw [show p + 5 + (c : Int) = p + 3 + ((2 : Nat) : Int) + (c : Int)
              by omega]
        exact hbr _ (by omega))
  have hfresh : (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape
        (p + 4) true) (p + 3) false) (p + 1) true) p false) (p + 3) true)
        (p + 5 + (c : Int)) true) (p + 4 + (c : Int)) false) (p + 6 + (c : Int)) = false := by
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact hbr _ (by omega)
  have hbump : step ⟨State.A, p + 6 + (c : Int), writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape
        (p + 4) true) (p + 3) false) (p + 1) true) p false) (p + 3) true)
        (p + 5 + (c : Int)) true) (p + 4 + (c : Int)) false⟩ =
      some ⟨State.B, p + 7 + (c : Int), writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape
        (p + 4) true) (p + 3) false) (p + 1) true) p false) (p + 3) true)
        (p + 5 + (c : Int)) true) (p + 4 + (c : Int)) false) (p + 6 + (c : Int)) true⟩ := by
    simp [step, instr, hfresh, move]
    try omega
  refine ⟨2 * c + 15 + 1, ⟨State.B, p + 7 + (c : Int), writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape
        (p + 4) true) (p + 3) false) (p + 1) true) p false) (p + 3) true)
        (p + 5 + (c : Int)) true) (p + 4 + (c : Int)) false) (p + 6 + (c : Int)) true⟩, by omega, ?_,
    ?_, ?_⟩
  · rw [stepN_add, hrun]
    show stepN 1 ⟨State.A, p + 6 + (c : Int), writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape
        (p + 4) true) (p + 3) false) (p + 1) true) p false) (p + 3) true)
        (p + 5 + (c : Int)) true) (p + 4 + (c : Int)) false⟩ = _
    simp [stepN, hbump]
  · refine ⟨by omega, by omega, by omega, rfl, p - 1, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · intro x hx
      show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape
        (p + 4) true) (p + 3) false) (p + 1) true) p false) (p + 3) true)
        (p + 5 + (c : Int)) true) (p + 4 + (c : Int)) false) (p + 6 + (c : Int)) true) x = false
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
      exact hbl x (by omega)
    · intro i hi
      show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape
        (p + 4) true) (p + 3) false) (p + 1) true) p false) (p + 3) true)
        (p + 5 + (c : Int)) true) (p + 4 + (c : Int)) false) (p + 6 + (c : Int)) true) (p - 1 - i) = true
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
      have := ha (i + 1) (by omega)
      rw [show p - ((i + 1 : Nat) : Int) = p - 1 - (i : Int) by omega] at this
      exact this
    · show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape
        (p + 4) true) (p + 3) false) (p + 1) true) p false) (p + 3) true)
        (p + 5 + (c : Int)) true) (p + 4 + (c : Int)) false) (p + 6 + (c : Int)) true) (p - 1 + 1) = false
      rw [show p - 1 + 1 = p by omega]
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
      exact writeAt_same _ p false
    · intro i hi
      by_cases hi0 : i = 0
      · rw [hi0]
        show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape
        (p + 4) true) (p + 3) false) (p + 1) true) p false) (p + 3) true)
        (p + 5 + (c : Int)) true) (p + 4 + (c : Int)) false) (p + 6 + (c : Int)) true) (p - 1 + 2 + ((0 : Nat) : Int)) = true
        rw [show p - 1 + 2 + ((0 : Nat) : Int) = p + 1 by omega]
        rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
        exact writeAt_same _ (p + 1) true
      · by_cases hi1 : i = 1
        · rw [hi1]
          show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape
        (p + 4) true) (p + 3) false) (p + 1) true) p false) (p + 3) true)
        (p + 5 + (c : Int)) true) (p + 4 + (c : Int)) false) (p + 6 + (c : Int)) true) (p - 1 + 2 + ((1 : Nat) : Int)) = true
          rw [show p - 1 + 2 + ((1 : Nat) : Int) = p + 2 by omega]
          rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
          have := hm 0 (by omega)
          rw [show p + 2 + ((0 : Nat) : Int) = p + 2 by omega] at this
          exact this
        · by_cases hi2 : i = 2
          · rw [hi2]
            show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape
        (p + 4) true) (p + 3) false) (p + 1) true) p false) (p + 3) true)
        (p + 5 + (c : Int)) true) (p + 4 + (c : Int)) false) (p + 6 + (c : Int)) true) (p - 1 + 2 + ((2 : Nat) : Int)) = true
            rw [show p - 1 + 2 + ((2 : Nat) : Int) = p + 3 by omega]
            rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
            exact writeAt_same _ (p + 3) true
          · by_cases hi3 : i = 3
            · rw [hi3]
              show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape
        (p + 4) true) (p + 3) false) (p + 1) true) p false) (p + 3) true)
        (p + 5 + (c : Int)) true) (p + 4 + (c : Int)) false) (p + 6 + (c : Int)) true) (p - 1 + 2 + ((3 : Nat) : Int)) = true
              rw [show p - 1 + 2 + ((3 : Nat) : Int) = p + 4 by omega]
              rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
              exact writeAt_same _ (p + 4) true
            · show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape
        (p + 4) true) (p + 3) false) (p + 1) true) p false) (p + 3) true)
        (p + 5 + (c : Int)) true) (p + 4 + (c : Int)) false) (p + 6 + (c : Int)) true) (p - 1 + 2 + (i : Int)) = true
              rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
              have := hc (i - 4) (by omega)
              rw [show p + 3 + ((2 : Nat) : Int) + ((i - 4 : Nat) : Int)
                    = p - 1 + 2 + (i : Int) by omega] at this
              exact this
    · show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape
        (p + 4) true) (p + 3) false) (p + 1) true) p false) (p + 3) true)
        (p + 5 + (c : Int)) true) (p + 4 + (c : Int)) false) (p + 6 + (c : Int)) true) (p - 1 + 2 + ((c + 3 : Nat) : Int)) = false
      rw [show p - 1 + 2 + ((c + 3 : Nat) : Int) = p + 4 + (c : Int) by omega]
      rw [writeAt_other _ _ _ _ (by omega)]
      exact writeAt_same _ (p + 4 + (c : Int)) false
    · intro i hi
      by_cases hi0 : i = 0
      · rw [hi0]
        show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape
        (p + 4) true) (p + 3) false) (p + 1) true) p false) (p + 3) true)
        (p + 5 + (c : Int)) true) (p + 4 + (c : Int)) false) (p + 6 + (c : Int)) true) (p - 1 + 3 + ((c + 3 : Nat) : Int) + ((0 : Nat) : Int)) = true
        rw [show p - 1 + 3 + ((c + 3 : Nat) : Int) + ((0 : Nat) : Int)
              = p + 5 + (c : Int) by omega]
        rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
        exact writeAt_same _ (p + 5 + (c : Int)) true
      · have hi1 : i = 1 := by omega
        rw [hi1]
        show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape
        (p + 4) true) (p + 3) false) (p + 1) true) p false) (p + 3) true)
        (p + 5 + (c : Int)) true) (p + 4 + (c : Int)) false) (p + 6 + (c : Int)) true) (p - 1 + 3 + ((c + 3 : Nat) : Int) + ((1 : Nat) : Int)) = true
        rw [show p - 1 + 3 + ((c + 3 : Nat) : Int) + ((1 : Nat) : Int)
              = p + 6 + (c : Int) by omega]
        exact writeAt_same _ (p + 6 + (c : Int)) true
    · intro x hx
      show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape
        (p + 4) true) (p + 3) false) (p + 1) true) p false) (p + 3) true)
        (p + 5 + (c : Int)) true) (p + 4 + (c : Int)) false) (p + 6 + (c : Int)) true) x = false
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
      exact hbr x (by omega)
    · show p + 7 + (c : Int)
          = p - 1 + 3 + ((c + 3 : Nat) : Int) + ((2 : Nat) : Int)
      omega
  · rw [show 2 * c + 15 + 1 = (2 * c + 15) + 1 from rfl]
    refine esafe_compose hrun hsafe (esafe_of_noE ?_)
    intro j d hj hjd
    have hj0 : j = 0 := by omega
    subst hj0
    have hdd : (⟨State.A, p + 6 + (c : Int), writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt cfg.tape
        (p + 4) true) (p + 3) false) (p + 1) true) p false) (p + 3) true)
        (p + 5 + (c : Int)) true) (p + 4 + (c : Int)) false⟩ : Config) = d := by
      simpa [stepN] using hjd
    rw [← hdd]; simp

/-- Transport for the merge chain: `(a, 1, c) → (a+2, c+2, 2)`. -/
theorem transport_merge {cfg : Config} {a c : Nat}
    (h : Realizes ⟨a, 1, c⟩ cfg) :
    ∃ (N : Nat) (cfg' : Config), 0 < N ∧ stepN N cfg = some cfg' ∧
      Realizes ⟨a + 2, c + 2, 2⟩ cfg' ∧ ESafeSeg cfg N := by
  obtain ⟨ha1, _hm1, hc1, hsB, p, hbl, ha, hg1, hm, hg2, hc, hbr, hhead⟩ := h
  obtain ⟨hrun, hsafe⟩ := merge_chain (cfg := cfg) (p := p) a c ha1 hsB
    (by rw [hhead]; omega)
    ha
    (hbl _ (by omega)) (hbl _ (by omega)) (hbl _ (by omega))
    hg1
    (by have := hm 0 (by omega)
        rw [show p + 2 + ((0 : Nat) : Int) = p + 2 by omega] at this; exact this)
    (by rw [show p + 3 = p + 2 + ((1 : Nat) : Int) by omega]; exact hg2)
    (fun i hi => by
      rw [show p + 4 + (i : Int) = p + 3 + ((1 : Nat) : Int) + (i : Int)
            by omega]
      exact hc i hi)
    (by rw [show p + 4 + (c : Int) = p + 3 + ((1 : Nat) : Int) + (c : Int)
              by omega]
        exact hbr _ (by omega))
    (by rw [show p + 5 + (c : Int) = p + 3 + ((1 : Nat) : Int) + (c : Int) + 1
              by omega]
        exact hbr _ (by omega))
  refine ⟨2 * a + 2 * c + 22, ⟨State.B, p + 6 + (c : Int), writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt
        (writeAt (writeAt (writeAt cfg.tape (p + 3) true) (p + 2) false)
        (p - (a : Int)) true) (p - (a : Int) - 1) true) (p - (a : Int) - 2) true)
        (p + 1) true) p false) (p + 2) true) (p + 4 + (c : Int)) true)
        (p + 3 + (c : Int)) false) (p + 5 + (c : Int)) true⟩, by omega,
    hrun, ?_, hsafe⟩
  refine ⟨by omega, by omega, by omega, rfl, p - 1, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro x hx
    show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt
        (writeAt (writeAt (writeAt cfg.tape (p + 3) true) (p + 2) false)
        (p - (a : Int)) true) (p - (a : Int) - 1) true) (p - (a : Int) - 2) true)
        (p + 1) true) p false) (p + 2) true) (p + 4 + (c : Int)) true)
        (p + 3 + (c : Int)) false) (p + 5 + (c : Int)) true) x = false
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact hbl x (by omega)
  · intro i hi
    by_cases hlo : i = a + 1
    · rw [hlo]
      show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt
        (writeAt (writeAt (writeAt cfg.tape (p + 3) true) (p + 2) false)
        (p - (a : Int)) true) (p - (a : Int) - 1) true) (p - (a : Int) - 2) true)
        (p + 1) true) p false) (p + 2) true) (p + 4 + (c : Int)) true)
        (p + 3 + (c : Int)) false) (p + 5 + (c : Int)) true) (p - 1 - ((a + 1 : Nat) : Int)) = true
      rw [show p - 1 - ((a + 1 : Nat) : Int) = p - (a : Int) - 2 by omega]
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
      exact writeAt_same _ (p - (a : Int) - 2) true
    · by_cases hlo1 : i = a
      · rw [hlo1]
        show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt
        (writeAt (writeAt (writeAt cfg.tape (p + 3) true) (p + 2) false)
        (p - (a : Int)) true) (p - (a : Int) - 1) true) (p - (a : Int) - 2) true)
        (p + 1) true) p false) (p + 2) true) (p + 4 + (c : Int)) true)
        (p + 3 + (c : Int)) false) (p + 5 + (c : Int)) true) (p - 1 - (a : Int)) = true
        rw [show p - 1 - (a : Int) = p - (a : Int) - 1 by omega]
        rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
        exact writeAt_same _ (p - (a : Int) - 1) true
      · by_cases hlo2 : i = a - 1
        · rw [hlo2]
          show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt
        (writeAt (writeAt (writeAt cfg.tape (p + 3) true) (p + 2) false)
        (p - (a : Int)) true) (p - (a : Int) - 1) true) (p - (a : Int) - 2) true)
        (p + 1) true) p false) (p + 2) true) (p + 4 + (c : Int)) true)
        (p + 3 + (c : Int)) false) (p + 5 + (c : Int)) true) (p - 1 - ((a - 1 : Nat) : Int)) = true
          rw [show p - 1 - ((a - 1 : Nat) : Int) = p - (a : Int) by omega]
          rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
          exact writeAt_same _ (p - (a : Int)) true
        · show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt
        (writeAt (writeAt (writeAt cfg.tape (p + 3) true) (p + 2) false)
        (p - (a : Int)) true) (p - (a : Int) - 1) true) (p - (a : Int) - 2) true)
        (p + 1) true) p false) (p + 2) true) (p + 4 + (c : Int)) true)
        (p + 3 + (c : Int)) false) (p + 5 + (c : Int)) true) (p - 1 - (i : Int)) = true
          rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
          have := ha (i + 1) (by omega)
          rw [show p - ((i + 1 : Nat) : Int) = p - 1 - (i : Int) by omega] at this
          exact this
  · show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt
        (writeAt (writeAt (writeAt cfg.tape (p + 3) true) (p + 2) false)
        (p - (a : Int)) true) (p - (a : Int) - 1) true) (p - (a : Int) - 2) true)
        (p + 1) true) p false) (p + 2) true) (p + 4 + (c : Int)) true)
        (p + 3 + (c : Int)) false) (p + 5 + (c : Int)) true) (p - 1 + 1) = false
    rw [show p - 1 + 1 = p by omega]
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ p false
  · intro i hi
    by_cases hi0 : i = 0
    · rw [hi0]
      show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt
        (writeAt (writeAt (writeAt cfg.tape (p + 3) true) (p + 2) false)
        (p - (a : Int)) true) (p - (a : Int) - 1) true) (p - (a : Int) - 2) true)
        (p + 1) true) p false) (p + 2) true) (p + 4 + (c : Int)) true)
        (p + 3 + (c : Int)) false) (p + 5 + (c : Int)) true) (p - 1 + 2 + ((0 : Nat) : Int)) = true
      rw [show p - 1 + 2 + ((0 : Nat) : Int) = p + 1 by omega]
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
      exact writeAt_same _ (p + 1) true
    · by_cases hi1 : i = 1
      · rw [hi1]
        show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt
        (writeAt (writeAt (writeAt cfg.tape (p + 3) true) (p + 2) false)
        (p - (a : Int)) true) (p - (a : Int) - 1) true) (p - (a : Int) - 2) true)
        (p + 1) true) p false) (p + 2) true) (p + 4 + (c : Int)) true)
        (p + 3 + (c : Int)) false) (p + 5 + (c : Int)) true) (p - 1 + 2 + ((1 : Nat) : Int)) = true
        rw [show p - 1 + 2 + ((1 : Nat) : Int) = p + 2 by omega]
        rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
        exact writeAt_same _ (p + 2) true
      · by_cases hi2 : i = 2
        · rw [hi2]
          show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt
        (writeAt (writeAt (writeAt cfg.tape (p + 3) true) (p + 2) false)
        (p - (a : Int)) true) (p - (a : Int) - 1) true) (p - (a : Int) - 2) true)
        (p + 1) true) p false) (p + 2) true) (p + 4 + (c : Int)) true)
        (p + 3 + (c : Int)) false) (p + 5 + (c : Int)) true) (p - 1 + 2 + ((2 : Nat) : Int)) = true
          rw [show p - 1 + 2 + ((2 : Nat) : Int) = p + 3 by omega]
          rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
          exact writeAt_same _ (p + 3) true
        · show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt
        (writeAt (writeAt (writeAt cfg.tape (p + 3) true) (p + 2) false)
        (p - (a : Int)) true) (p - (a : Int) - 1) true) (p - (a : Int) - 2) true)
        (p + 1) true) p false) (p + 2) true) (p + 4 + (c : Int)) true)
        (p + 3 + (c : Int)) false) (p + 5 + (c : Int)) true) (p - 1 + 2 + (i : Int)) = true
          rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
          have := hc (i - 3) (by omega)
          rw [show p + 3 + ((1 : Nat) : Int) + ((i - 3 : Nat) : Int)
                = p - 1 + 2 + (i : Int) by omega] at this
          exact this
  · show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt
        (writeAt (writeAt (writeAt cfg.tape (p + 3) true) (p + 2) false)
        (p - (a : Int)) true) (p - (a : Int) - 1) true) (p - (a : Int) - 2) true)
        (p + 1) true) p false) (p + 2) true) (p + 4 + (c : Int)) true)
        (p + 3 + (c : Int)) false) (p + 5 + (c : Int)) true) (p - 1 + 2 + ((c + 2 : Nat) : Int)) = false
    rw [show p - 1 + 2 + ((c + 2 : Nat) : Int) = p + 3 + (c : Int) by omega]
    rw [writeAt_other _ _ _ _ (by omega)]
    exact writeAt_same _ (p + 3 + (c : Int)) false
  · intro i hi
    by_cases hi0 : i = 0
    · rw [hi0]
      show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt
        (writeAt (writeAt (writeAt cfg.tape (p + 3) true) (p + 2) false)
        (p - (a : Int)) true) (p - (a : Int) - 1) true) (p - (a : Int) - 2) true)
        (p + 1) true) p false) (p + 2) true) (p + 4 + (c : Int)) true)
        (p + 3 + (c : Int)) false) (p + 5 + (c : Int)) true) (p - 1 + 3 + ((c + 2 : Nat) : Int) + ((0 : Nat) : Int)) = true
      rw [show p - 1 + 3 + ((c + 2 : Nat) : Int) + ((0 : Nat) : Int)
            = p + 4 + (c : Int) by omega]
      rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
      exact writeAt_same _ (p + 4 + (c : Int)) true
    · have hi1 : i = 1 := by omega
      rw [hi1]
      show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt
        (writeAt (writeAt (writeAt cfg.tape (p + 3) true) (p + 2) false)
        (p - (a : Int)) true) (p - (a : Int) - 1) true) (p - (a : Int) - 2) true)
        (p + 1) true) p false) (p + 2) true) (p + 4 + (c : Int)) true)
        (p + 3 + (c : Int)) false) (p + 5 + (c : Int)) true) (p - 1 + 3 + ((c + 2 : Nat) : Int) + ((1 : Nat) : Int)) = true
      rw [show p - 1 + 3 + ((c + 2 : Nat) : Int) + ((1 : Nat) : Int)
            = p + 5 + (c : Int) by omega]
      exact writeAt_same _ (p + 5 + (c : Int)) true
  · intro x hx
    show (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt
        (writeAt (writeAt (writeAt cfg.tape (p + 3) true) (p + 2) false)
        (p - (a : Int)) true) (p - (a : Int) - 1) true) (p - (a : Int) - 2) true)
        (p + 1) true) p false) (p + 2) true) (p + 4 + (c : Int)) true)
        (p + 3 + (c : Int)) false) (p + 5 + (c : Int)) true) x = false
    rw [writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega), writeAt_other _ _ _ _ (by omega)]
    exact hbr x (by omega)
  · show p + 6 + (c : Int)
        = p - 1 + 3 + ((c + 2 : Nat) : Int) + ((2 : Nat) : Int)
    omega

theorem realizes_start : Realizes ⟨2, 7, 2⟩ ⟨State.B, 6, startTape⟩ := by
  refine ⟨by omega, by omega, by omega, rfl, -6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact startTape_blank_left x (by omega)
  · intro i hi
    have hcase : i = 0 ∨ i = 1 := by omega
    rcases hcase with rfl | rfl
    · show startTape (-6 - ((0 : Nat) : Int)) = true
      rw [show (-6 : Int) - ((0 : Nat) : Int) = -6 by omega]; rfl
    · show startTape (-6 - ((1 : Nat) : Int)) = true
      rw [show (-6 : Int) - ((1 : Nat) : Int) = -7 by omega]; rfl
  · show startTape (-6 + 1) = false
    rw [show (-6 : Int) + 1 = -5 by omega]; rfl
  · intro i hi
    have hcase : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
      omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show startTape (-6 + 2 + ((0 : Nat) : Int)) = true
      rw [show (-6 : Int) + 2 + ((0 : Nat) : Int) = -4 by omega]; rfl
    · show startTape (-6 + 2 + ((1 : Nat) : Int)) = true
      rw [show (-6 : Int) + 2 + ((1 : Nat) : Int) = -3 by omega]; rfl
    · show startTape (-6 + 2 + ((2 : Nat) : Int)) = true
      rw [show (-6 : Int) + 2 + ((2 : Nat) : Int) = -2 by omega]; rfl
    · show startTape (-6 + 2 + ((3 : Nat) : Int)) = true
      rw [show (-6 : Int) + 2 + ((3 : Nat) : Int) = -1 by omega]; rfl
    · show startTape (-6 + 2 + ((4 : Nat) : Int)) = true
      rw [show (-6 : Int) + 2 + ((4 : Nat) : Int) = 0 by omega]; rfl
    · show startTape (-6 + 2 + ((5 : Nat) : Int)) = true
      rw [show (-6 : Int) + 2 + ((5 : Nat) : Int) = 1 by omega]; rfl
    · show startTape (-6 + 2 + ((6 : Nat) : Int)) = true
      rw [show (-6 : Int) + 2 + ((6 : Nat) : Int) = 2 by omega]; rfl
  · show startTape (-6 + 2 + ((7 : Nat) : Int)) = false
    rw [show (-6 : Int) + 2 + ((7 : Nat) : Int) = 3 by omega]; rfl
  · intro i hi
    have hcase : i = 0 ∨ i = 1 := by omega
    rcases hcase with rfl | rfl
    · show startTape (-6 + 3 + ((7 : Nat) : Int) + ((0 : Nat) : Int)) = true
      rw [show (-6 : Int) + 3 + ((7 : Nat) : Int) + ((0 : Nat) : Int) = 4
            by omega]; rfl
    · show startTape (-6 + 3 + ((7 : Nat) : Int) + ((1 : Nat) : Int)) = true
      rw [show (-6 : Int) + 3 + ((7 : Nat) : Int) + ((1 : Nat) : Int) = 5
            by omega]; rfl
  · intro x hx
    exact startTape_blank_right x (by omega)
  · show (6 : Int) = -6 + 3 + ((7 : Nat) : Int) + ((2 : Nat) : Int)
    omega

theorem orbitInv_start : OrbitInv ⟨State.B, 6, startTape⟩ :=
  ⟨0, ⟨2, 7, 2⟩, rfl, realizes_start⟩

theorem aorbit_succ {n : Nat} {s : AState} (horb : aorbit n = some s) :
    aorbit (n + 1) = astep s := by
  show (match aorbit n with
        | none => none
        | some s => astep s) = astep s
  rw [horb]

/-- **The dispatcher.**  Under the Antihydra conjecture, every realized
live abstract state advances safely to another one.

Informally: the conductor.  Ask the abstract orbit which rule fires next;
the matching transport theorem plays it on the tape, safely, landing on
the next realized state.  Feeding this to the keystone turns rule-by-rule
safety into eternal safety. -/
theorem orbit_segment (hso : SafeOrbitA) (cfg : Config) (hinv : OrbitInv cfg) :
    ∃ k, 0 < k ∧ ∃ cfg', stepN k cfg = some cfg' ∧ OrbitInv cfg' ∧
      ESafeSeg cfg k := by
  obtain ⟨n, s, horb, hreal⟩ := hinv
  have hsucc : aorbit (n + 1) = astep s := aorbit_succ horb
  have hlive : astep s ≠ none := by rw [← hsucc]; exact hso (n + 1)
  obtain ⟨sa, sm, sc⟩ := s
  have hm1 : 1 ≤ sm := hreal.2.1
  have ha1 : 1 ≤ sa := hreal.1
  have hmcase : sm = 1 ∨ sm = 2 ∨ 3 ≤ sm := by omega
  rcases hmcase with rfl | rfl | hge
  · -- merge: counter +2
    obtain ⟨K, cfg', hK, hst, hreal', hsf⟩ := transport_merge hreal
    refine ⟨K, hK, cfg', hst, ⟨n + 1, ⟨sa + 2, sc + 2, 2⟩, ?_, hreal'⟩, hsf⟩
    rw [hsucc]
    show (if 3 ≤ 1 then some (AState.mk sa (1 - 2) (sc + 3))
          else if (1 : Nat) = 2 then
            (if 2 ≤ sa then some (AState.mk (sa - 1) (sc + 3) 2) else none)
          else if (1 : Nat) = 1 then some (AState.mk (sa + 2) (sc + 2) 2)
          else none) = _
    rw [if_neg (show ¬(3 ≤ 1) by omega), if_neg (show ¬((1 : Nat) = 2) by omega),
        if_pos (show (1 : Nat) = 1 from rfl)]
  · -- drop: counter -1, needs a non-empty counter after the step
    have ha2 : 2 ≤ sa := by
      cases Nat.lt_or_ge sa 2 with
      | inr hge => exact hge
      | inl hlt =>
          refine absurd ?_ hlive
          show (if 3 ≤ 2 then some (AState.mk sa (2 - 2) (sc + 3))
                else if (2 : Nat) = 2 then
                  (if 2 ≤ sa then some (AState.mk (sa - 1) (sc + 3) 2) else none)
                else if (2 : Nat) = 1 then some (AState.mk (sa + 2) (sc + 2) 2)
                else none) = none
          rw [if_neg (show ¬(3 ≤ 2) by omega),
              if_pos (show (2 : Nat) = 2 from rfl),
              if_neg (show ¬(2 ≤ sa) by omega)]
    obtain ⟨a', rfl⟩ : ∃ a', sa = a' + 2 := ⟨sa - 2, by omega⟩
    obtain ⟨K, cfg', hK, hst, hreal', hsf⟩ := transport_drop hreal
    refine ⟨K, hK, cfg', hst, ⟨n + 1, ⟨a' + 1, sc + 3, 2⟩, ?_, hreal'⟩, hsf⟩
    rw [hsucc]
    show (if 3 ≤ 2 then some (AState.mk (a' + 2) (2 - 2) (sc + 3))
          else if (2 : Nat) = 2 then
            (if 2 ≤ a' + 2 then some (AState.mk (a' + 2 - 1) (sc + 3) 2)
             else none)
          else if (2 : Nat) = 1 then some (AState.mk (a' + 2 + 2) (sc + 2) 2)
          else none) = _
    rw [if_neg (show ¬(3 ≤ 2) by omega), if_pos (show (2 : Nat) = 2 from rfl),
        if_pos (show 2 ≤ a' + 2 by omega), show a' + 2 - 1 = a' + 1 by omega]
  · -- hydra: counter frozen
    obtain ⟨m', rfl⟩ : ∃ m', sm = m' + 3 := ⟨sm - 3, by omega⟩
    obtain ⟨K, cfg', hK, hst, hreal', hsf⟩ := transport_hydra hreal
    refine ⟨K, hK, cfg', hst, ⟨n + 1, ⟨sa, m' + 1, sc + 3⟩, ?_, hreal'⟩, hsf⟩
    rw [hsucc]
    show (if 3 ≤ m' + 3 then some (AState.mk sa (m' + 3 - 2) (sc + 3))
          else if (m' + 3 : Nat) = 2 then
            (if 2 ≤ sa then some (AState.mk (sa - 1) (sc + 3) 2) else none)
          else if (m' + 3 : Nat) = 1 then
            some (AState.mk (sa + 2) (sc + 2) 2)
          else none) = _
    rw [if_pos (show 3 ≤ m' + 3 by omega), show m' + 3 - 2 = m' + 1 by omega]

/-- **THE MAIN THEOREM.**  Informally: four layers compose in one line —
the dispatcher supplies safe segments, the keystone welds them into
eternal probe safety, the startup prefix bolts on the first 62 steps, and
the layer-2 contract concludes the machine never halts.  The only free
hypothesis is the conjecture itself.

Under the Antihydra conjecture `SafeOrbitA`,
Antihydra never halts from the blank tape. -/
theorem safeOrbitA_nonhalting (hso : SafeOrbitA) : ¬ RawHalts blankStart := by
  have hpost : EProbeSafe ⟨State.B, 6, startTape⟩ :=
    eprobe_safe_of_segments orbitInv_start (orbit_segment hso)
  have hall : EProbeSafe blankStart :=
    eprobe_safe_prefix startup_run startup_safe hpost
  exact blank_nonhalting_of_e_probe_safe hall

end QIG.AntihydraRawTM

#print axioms QIG.AntihydraRawTM.halt_requires_e_probe_00
#print axioms QIG.AntihydraRawTM.blank_nonhalting_of_e_probe_safe
#print axioms QIG.AntihydraRawTM.sweep_E
#print axioms QIG.AntihydraRawTM.sweep_C
#print axioms QIG.AntihydraRawTM.eprobe_safe_of_segments
#print axioms QIG.AntihydraRawTM.hydra_step
#print axioms QIG.AntihydraRawTM.drop_step
#print axioms QIG.AntihydraRawTM.merge_chain
#print axioms QIG.AntihydraRawTM.transport_hydra
#print axioms QIG.AntihydraRawTM.transport_drop
#print axioms QIG.AntihydraRawTM.transport_merge
#print axioms QIG.AntihydraRawTM.realizes_start
#print axioms QIG.AntihydraRawTM.orbit_segment
#print axioms QIG.AntihydraRawTM.safeOrbitA_nonhalting
