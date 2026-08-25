-- ABSTRACT-BEGIN (generated)
/-!
## The abstract orbit (mirror): five integers drive the whole machine

Everything the machine ever does after its 2044-step startup is one of
seven episodes — affine maps on the shape `(three?, l, h1, h2, r)`,
where `r` is the (leftward-moving) spawn edge and `l` the far right
edge.  The safety conjecture (`SafeMetaOrbit`) is the machine's entire
halting problem, compressed to arithmetic on five integers.
-/

/-- Abstract spawn-entry state (mirror).  `three` marks the 3-hole
family (implicit third hole at `r + 3`). -/
structure MetaState where
  three : Bool
  l : Int
  h1 : Int
  h2 : Int
  r : Int

/-- One abstract step (mirror). -/
def metaStep : MetaState → Option MetaState
  | ⟨true, l, h1, h2, r⟩ =>
      if h1 ≤ l ∧ h2 ≤ h1 - 4 ∧ r ≤ h2 - 6 ∧
          (h2 - r) % 2 = 0 ∧ (h1 - h2) % 2 = 0 then
        some ⟨false, l, h1 - 6, h2 - 4, r - 1⟩
      else if h1 ≤ l ∧ h2 = h1 - 2 ∧ r ≤ h2 - 7 ∧ (h2 - r) % 2 = 0 then
        some ⟨false, l, h1 - 9, r - 1, r - 2⟩
      else none
  | ⟨false, l, h1, h2, r⟩ =>
      if h2 = r + 1 then
        if h1 ≤ l ∧ r + 4 ≤ h1 then
          some ⟨false, l, h1, r + 2, r - 1⟩
        else none
      else if h2 = r + 3 then
        if (h1 - r) % 2 = 1 then
          if h1 ≤ l ∧ r ≤ h1 - 7 then
            some ⟨false, l, h1 - 6, r - 1, r - 2⟩
          else none
        else if (l - h1) % 2 = 1 then
          if h1 ≤ l - 3 ∧ r ≤ h1 - 6 then
            some ⟨false, l + 1, l - 5, h1 - 4, r - 1⟩
          else none
        else
          if h1 ≤ l - 5 ∧ r ≤ h1 - 6 then
            some ⟨false, l + 3, l - 6, h1 - 4, r - 1⟩
          else none
      else
        if h1 ≤ l ∧ h2 ≤ h1 - 1 ∧ r + 4 ≤ h2 then
          some ⟨true, l, h1, h2, r - 1⟩
        else none

/-- The concrete spawn-entry tape of an abstract state (mirror). -/
def entryTape (s : MetaState) : Int → Bool :=
  if s.three then holeTape (s.r + 1) s.l s.h1 s.h2 (s.r + 3) (s.r + 3)
  else holeTape (s.r + 1) s.l s.h1 s.h2 s.h2 s.h2

/-- The machine configuration realizing an abstract state (mirror). -/
def Realizes (s : MetaState) (c : Config) : Prop :=
  c.state = State.E ∧ c.head = s.r ∧ c.tape = entryTape s

/-- **Meta transport** (mirror). -/
theorem meta_transport {s s' : MetaState} {c : Config}
    (hr : Realizes s c) (hstep : metaStep s = some s') :
    ∃ k : Nat, 0 < k ∧ ∃ c' : Config,
      stepN k c = some c' ∧ Realizes s' c' ∧ BSafeSeg c k := by
  obtain ⟨hs, hh, ht⟩ := hr
  obtain ⟨three, l, h1, h2, r⟩ := s
  simp only at hs hh ht
  cases three with
  | true =>
      simp only [metaStep] at hstep
      split at hstep
      · rename_i hg
        obtain ⟨hg1, hg2, hg3, hg4, hg5⟩ := hg
        obtain rfl := Option.some_inj.mp hstep
        obtain ⟨k1, hk1⟩ : ∃ k1 : Nat, r + 2 * (k1 : Int) = h2 - 6 :=
          ⟨((h2 - r - 6) / 2).toNat, by omega⟩
        obtain ⟨k2, hk2⟩ : ∃ k2 : Nat,
            h2 - 1 + 2 * (k2 : Int) = h1 - 5 :=
          ⟨((h1 - h2 - 4) / 2).toNat, by omega⟩
        obtain ⟨m, hm⟩ : ∃ m : Nat, h1 - 7 - 2 * (m : Int) = r - 1 :=
          ⟨((h1 - r - 6) / 2).toNat, by omega⟩
        obtain ⟨hrun, hsafe⟩ := episode_generic (c := c) hs hh
          (by rw [ht]; rfl) hg1 hg2 hk1 hk2 hm
        refine ⟨_, by omega, _, hrun, ⟨rfl, rfl, ?_⟩, hsafe⟩
        show holeTape r l (h1 - 6) (h2 - 4) (h2 - 4) (h2 - 4) = _
        rw [show entryTape ⟨false, l, h1 - 6, h2 - 4, r - 1⟩
              = holeTape (r - 1 + 1) l (h1 - 6) (h2 - 4) (h2 - 4)
                  (h2 - 4) from rfl,
            show (r : Int) - 1 + 1 = r from by omega]
      · rename_i hng
        split at hstep
        · rename_i hg
          obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
          obtain rfl := Option.some_inj.mp hstep
          obtain ⟨k1, hk1⟩ : ∃ k1 : Nat, r + 2 * (k1 : Int) = h2 - 6 :=
            ⟨((h2 - r - 6) / 2).toNat, by omega⟩
          obtain ⟨m, hm⟩ : ∃ m : Nat, h2 - 8 - 2 * (m : Int) = r - 2 :=
            ⟨((h2 - r - 6) / 2).toNat, by omega⟩
          obtain ⟨hrun, hsafe⟩ := episode_fuse (c := c) hs hh
            (by rw [ht]; rfl) hg1 hg2 hk1 hg3 hm
          refine ⟨_, by omega, _, hrun, ⟨rfl, rfl, ?_⟩, hsafe⟩
          show holeTape r l (h2 - 7) (h2 - 7) (h2 - 7) (h2 - 7) = _
          rw [show entryTape ⟨false, l, h1 - 9, r - 1, r - 2⟩
                = holeTape (r - 2 + 1) l (h1 - 9) (r - 1) (r - 1) (r - 1)
                from rfl,
              show (r : Int) - 2 + 1 = r - 1 from by omega,
              show (h2 : Int) - 7 = h1 - 9 from by omega]
          exact holeTape_rebase l r (h1 - 9)
        · exact absurd hstep (by simp)
  | false =>
      simp only [metaStep] at hstep
      split at hstep
      · rename_i hv
        split at hstep
        · rename_i hg
          obtain ⟨hg1, hg2⟩ := hg
          obtain rfl := Option.some_inj.mp hstep
          obtain ⟨hrun, hsafe⟩ := episode_variant (c := c) hs hh
            (by rw [ht]; rfl) hg1 hg2 hv
          refine ⟨_, by omega, _, hrun, ⟨rfl, rfl, ?_⟩, hsafe⟩
          show holeTape r l h1 (r + 2) (r + 2) (r + 2) = _
          rw [show entryTape ⟨false, l, h1, r + 2, r - 1⟩
                = holeTape (r - 1 + 1) l h1 (r + 2) (r + 2) (r + 2)
                from rfl,
              show (r : Int) - 1 + 1 = r from by omega]
        · exact absurd hstep (by simp)
      · rename_i hnv
        split at hstep
        · rename_i hc3
          split at hstep
          · rename_i hodd
            split at hstep
            · rename_i hg
              obtain ⟨hg1, hg2⟩ := hg
              obtain rfl := Option.some_inj.mp hstep
              obtain ⟨k1, hk1⟩ : ∃ k1 : Nat,
                  r + 2 * (k1 : Int) = h1 - 5 :=
                ⟨((h1 - r - 5) / 2).toNat, by omega⟩
              obtain ⟨m, hm⟩ : ∃ m : Nat,
                  h1 - 7 - 2 * (m : Int) = r - 2 :=
                ⟨((h1 - r - 5) / 2).toNat, by omega⟩
              obtain ⟨hrun, hsafe⟩ := episode_carried_term (c := c)
                hs hh (by rw [ht]; rfl) hg1 hc3 hg2 hk1 hm
              refine ⟨_, by omega, _, hrun, ⟨rfl, rfl, ?_⟩, hsafe⟩
              show holeTape r l (h1 - 6) (h1 - 6) (h1 - 6) (h1 - 6) = _
              rw [show entryTape ⟨false, l, h1 - 6, r - 1, r - 2⟩
                    = holeTape (r - 2 + 1) l (h1 - 6) (r - 1) (r - 1)
                        (r - 1) from rfl,
                  show (r : Int) - 2 + 1 = r - 1 from by omega]
              exact holeTape_rebase l r (h1 - 6)
            · exact absurd hstep (by simp)
          · rename_i hev
            split at hstep
            · rename_i haodd
              split at hstep
              · rename_i hg
                obtain ⟨hg1, hg2⟩ := hg
                obtain rfl := Option.some_inj.mp hstep
                obtain ⟨k1, hk1⟩ : ∃ k1 : Nat,
                    r + 2 * (k1 : Int) = h1 - 6 :=
                  ⟨((h1 - r - 6) / 2).toNat, by omega⟩
                obtain ⟨k2, hk2⟩ : ∃ k2 : Nat,
                    h1 - 1 + 2 * (k2 : Int) = l - 4 :=
                  ⟨((l - h1 - 3) / 2).toNat, by omega⟩
                obtain ⟨m, hm⟩ : ∃ m : Nat,
                    l - 6 - 2 * (m : Int) = r - 1 :=
                  ⟨((l - r - 5) / 2).toNat, by omega⟩
                obtain ⟨hrun, hsafe⟩ := episode_deep_odd (c := c)
                  hs hh (by rw [ht]; rfl) hg1 hc3 hk1 hk2 hm
                refine ⟨_, by omega, _, hrun, ⟨rfl, rfl, ?_⟩, hsafe⟩
                show holeTape r (l + 1) (l - 5) (h1 - 4) (h1 - 4)
                    (h1 - 4) = _
                rw [show entryTape ⟨false, l + 1, l - 5, h1 - 4,
                      r - 1⟩
                      = holeTape (r - 1 + 1) (l + 1) (l - 5) (h1 - 4)
                          (h1 - 4) (h1 - 4) from rfl,
                    show (r : Int) - 1 + 1 = r from by omega]
              · exact absurd hstep (by simp)
            · rename_i haev
              split at hstep
              · rename_i hg
                obtain ⟨hg1, hg2⟩ := hg
                obtain rfl := Option.some_inj.mp hstep
                obtain ⟨k1, hk1⟩ : ∃ k1 : Nat,
                    r + 2 * (k1 : Int) = h1 - 6 :=
                  ⟨((h1 - r - 6) / 2).toNat, by omega⟩
                obtain ⟨k2, hk2⟩ : ∃ k2 : Nat,
                    h1 - 1 + 2 * (k2 : Int) = l - 5 :=
                  ⟨((l - h1 - 4) / 2).toNat, by omega⟩
                obtain ⟨m, hm⟩ : ∃ m : Nat,
                    l - 7 - 2 * (m : Int) = r - 1 :=
                  ⟨((l - r - 6) / 2).toNat, by omega⟩
                obtain ⟨hrun, hsafe⟩ := episode_deep_even (c := c)
                  hs hh (by rw [ht]; rfl) hg1 hc3 hk1 hk2 hm
                refine ⟨_, by omega, _, hrun, ⟨rfl, rfl, ?_⟩, hsafe⟩
                show holeTape r (l + 3) (l - 6) (h1 - 4) (h1 - 4)
                    (h1 - 4) = _
                rw [show entryTape ⟨false, l + 3, l - 6, h1 - 4,
                      r - 1⟩
                      = holeTape (r - 1 + 1) (l + 3) (l - 6) (h1 - 4)
                          (h1 - 4) (h1 - 4) from rfl,
                    show (r : Int) - 1 + 1 = r from by omega]
              · exact absurd hstep (by simp)
        · rename_i hnc3
          split at hstep
          · rename_i hg
            obtain ⟨hg1, hg2, hg3⟩ := hg
            obtain rfl := Option.some_inj.mp hstep
            obtain ⟨hrun, hsafe⟩ := episode_spawn (c := c) hs hh
              (by rw [ht]; rfl) hg1 hg2 hg3
            refine ⟨_, by omega, _, hrun, ⟨rfl, rfl, ?_⟩, hsafe⟩
            show holeTape r l h1 h2 (r + 2) (r + 2) = _
            rw [show entryTape ⟨true, l, h1, h2, r - 1⟩
                  = holeTape (r - 1 + 1) l h1 h2 (r - 1 + 3)
                      (r - 1 + 3) from rfl,
                show (r : Int) - 1 + 1 = r from by omega,
                show (r : Int) - 1 + 3 = r + 2 from by omega]
          · exact absurd hstep (by simp)

/-- The startup's landing state (mirror): spawn entry at `r = -40`
with holes `{11, -39}`. -/
def s0 : MetaState := ⟨false, 17, 11, -39, -40⟩

/-- The abstract orbit from the anchor. -/
def metaOrbit : Nat → Option MetaState
  | 0 => some s0
  | n + 1 =>
      match metaOrbit n with
      | none => none
      | some s => metaStep s

/-- **The dossier-3 safety conjecture** (mirror): the abstract orbit
never falls off the guarded region. -/
def SafeMetaOrbit : Prop := ∀ n, metaOrbit n ≠ none

/-- The orbit invariant transports to `BProbeSafe` via the keystone. -/
theorem bprobe_safe_of_safeMetaOrbit (hsafe : SafeMetaOrbit)
    {c0 : Config} (hr : Realizes s0 c0) : BProbeSafe c0 := by
  apply bprobe_safe_of_segments
    (Inv := fun c => ∃ n s, metaOrbit n = some s ∧ Realizes s c)
  · exact ⟨0, s0, rfl, hr⟩
  · rintro c ⟨n, s, hn, hrs⟩
    have heq : metaOrbit (n + 1) = metaStep s := by
      show (match metaOrbit n with
            | none => none
            | some s => metaStep s) = _
      rw [hn]
    cases hms : metaStep s with
    | none =>
        exact absurd (heq.trans hms) (hsafe (n + 1))
    | some s' =>
        obtain ⟨k, hk, c', hrun, hr', hsafe'⟩ := meta_transport hrs hms
        exact ⟨k, hk, c', hrun, ⟨n + 1, s', by rw [heq, hms], hr'⟩,
          hsafe'⟩

set_option maxRecDepth 100000 in
/-- **The conditional closure of dossier-3** (mirror). -/
theorem dossier3_nonhalting_of_safeMetaOrbit (hsafe : SafeMetaOrbit) :
    ¬ RawHalts blankStart := by
  obtain ⟨hrun, hseg⟩ := anchor_run
  have hr0 : Realizes s0
      ⟨State.E, (-40 : Int),
        holeTape (-39 : Int) (17 : Int) (11 : Int) (-39 : Int)
          (-39 : Int) (-39 : Int)⟩ := by
    refine ⟨rfl, rfl, ?_⟩
    show holeTape (-39 : Int) (17 : Int) (11 : Int) (-39 : Int)
        (-39 : Int) (-39 : Int) = entryTape s0
    rw [show entryTape s0
          = holeTape ((-40 : Int) + 1) (17 : Int) (11 : Int)
              (-39 : Int) (-39 : Int) (-39 : Int) from rfl,
        show (-40 : Int) + 1 = (-39 : Int) from by omega]
  have hbp : BProbeSafe ⟨State.E, (-40 : Int),
      holeTape (-39 : Int) (17 : Int) (11 : Int) (-39 : Int)
        (-39 : Int) (-39 : Int)⟩ :=
    bprobe_safe_of_safeMetaOrbit hsafe hr0
  have hblank : BProbeSafe blankStart := by
    intro d hreach hB h0
    obtain ⟨n, hd⟩ := hreach
    by_cases hn : n < 2044
    · exact hseg n d hn hd hB h0
    · have hsplit : stepN n blankStart
          = (stepN 2044 blankStart).bind (stepN (n - 2044)) := by
        have h := stepN_add 2044 (n - 2044) blankStart
        rw [show 2044 + (n - 2044) = n from by omega] at h
        exact h
      rw [hsplit, hrun] at hd
      exact hbp d ⟨n - 2044, hd⟩ hB h0
  exact blank_nonhalting_of_b_probe_safe hblank
