"""Episode compiler v2: emits Lean episode theorems for dossier-2/3.

All arithmetic goes through omega against the episode's guard
hypotheses; all ¬∧ eliminations use the constructive helpers.

holeTape state: (l, r, holes[4]) as strings.  Segments:
  catrun  k front               : cat_run + catN normalization
  atom    name h n_steps        : fixed atom + towerN normalization
  fstep                         : one F step
  sweep   m end_head            : sweep_mixed + safety
"""

SLOT = ["(Or.inl (by omega))",
        "(Or.inr (Or.inl (by omega)))",
        "(Or.inr (Or.inr (Or.inl (by omega))))",
        "(Or.inr (Or.inr (Or.inr (by omega))))"]

NOTOR = "(by intro hor; rcases hor with hx | hx | hx | hx <;> omega)"


def ht(l, r, holes):
    hs = (list(holes) + [holes[-1]] * 4)[:4]
    return (f"holeTape ({l}) ({r}) ({hs[0]}) ({hs[1]}) ({hs[2]}) "
            f"({hs[3]})")


class Compiler:
    def __init__(self, mirror):
        self.mir = mirror
        self.S = 'E' if mirror else 'D'
        self.SAFE = 'BSafeSeg' if mirror else 'CSafeSeg'
        self.comp = 'bsafe_compose' if mirror else 'csafe_compose'
        self.L = []
        self.ctr = 0

    def A(self, s):
        self.L.append(s)

    def o(self, base, k):
        """offset in crawl-direction convention: positive k = toward
        the crawl (left for D2, right for D3)."""
        k = k if self.mir else -k
        if k == 0:
            return base
        return f"{base} + {k}" if k > 0 else f"{base} - {-k}"

    def inner3(self, ind, in_l, in_r, in_holes, out_l, out_r,
               in_hole_fates):
        """Emit: goal `holeTape IN q = holeTape OUT q` under context
        establishing q ∉ zone / write positions.
        in_hole_fates: list of 4 entries: ('kept', out_slot) or 'dead'."""
        A = self.A
        A(f"{ind}by_cases hin : q = ({in_holes[0]}) ∨ q = ({in_holes[1]})"
          f" ∨ q = ({in_holes[2]}) ∨ q = ({in_holes[3]})")
        A(f"{ind}· rw [holeTape_hole hin]")
        A(f"{ind}  rcases hin with hx | hx | hx | hx")
        for fate in in_hole_fates:
            if fate == 'dead':
                A(f"{ind}  · exfalso")
                A(f"{ind}    omega")
            else:
                A(f"{ind}  · exact (holeTape_hole {SLOT[fate[1]]}).symm")
        A(f"{ind}· by_cases hrange : ({in_l}) ≤ q ∧ q ≤ ({in_r})")
        A(f"{ind}  · obtain ⟨hr1, hr2⟩ := hrange")
        A(f"{ind}    rw [holeTape_one hin hr1 hr2]")
        A(f"{ind}    exact (holeTape_one {NOTOR} (by omega) "
          f"(by omega)).symm")
        A(f"{ind}  · have hrr := not_and_le' hrange")
        A(f"{ind}    clear hrange")
        A(f"{ind}    rw [holeTape_out hin (by intro hcc; omega)]")
        A(f"{ind}    exact (holeTape_out {NOTOR} "
          f"(by intro hcc; omega)).symm")

    def emit_catN(self, name, in_l, in_r, in_holes, entry, k,
                  out_l, out_r, out_holes, fslot, cslot, in_hole_fates):
        A = self.A
        in_holes = (list(in_holes) + [in_holes[-1]] * 4)[:4]
        IN = ht(in_l, in_r, in_holes)
        OUT = ht(out_l, out_r, out_holes)
        if self.mir:
            front = f"({entry}) + 2 * ({k} : Int)"
            carried = f"({entry}) + 2 * ({k} : Int) + 3"
            zone = f"({entry}) ≤ q ∧ q < ({entry}) + 2 * ({k} : Int) + 3"
            na = "not_and_ge'"
        else:
            front = f"({entry}) - 2 * ({k} : Int)"
            carried = f"({entry}) - 2 * ({k} : Int) - 3"
            zone = (f"({entry}) - 2 * ({k} : Int) - 3 < q ∧ "
                    f"q ≤ ({entry})")
            na = "not_and_lt'" if False else "not_and_le"
        # D2 zone form (a < q ∧ q ≤ b) -> not_and_le; D3 (a ≤ q ∧ q < b)
        # -> not_and_ge'
        if self.mir:
            na = "not_and_ge"
        A(f"  have {name} : catTape ({IN}) ({entry}) {k} = {OUT} := by")
        A(f"    funext q")
        A(f"    show (if q = {front} ∨ q = {carried} then false")
        A(f"          else if {zone} then true")
        A(f"          else ({IN}) q) = ({OUT}) q")
        A(f"    by_cases hf : q = {front}")
        A(f"    · rw [if_pos (Or.inl hf)]")
        A(f"      exact (holeTape_hole {SLOT[fslot]}).symm")
        A(f"    · by_cases hc : q = {carried}")
        A(f"      · rw [if_pos (Or.inr hc)]")
        A(f"        exact (holeTape_hole {SLOT[cslot]}).symm")
        A(f"      · rw [if_neg (by intro hor; exact hor.elim hf hc)]")
        A(f"        by_cases hz : {zone}")
        A(f"        · rw [if_pos hz]")
        A(f"          obtain ⟨hz1, hz2⟩ := hz")
        A(f"          exact (holeTape_one {NOTOR} (by omega) "
          f"(by omega)).symm")
        A(f"        · have hzz := {na} hz")
        A(f"          clear hz")
        A(f"          rw [if_neg (by intro hcc; omega)]")
        self.inner3("          ", in_l, in_r, in_holes, out_l, out_r,
                    in_hole_fates)

    def emit_towerN(self, name, writes, in_l, in_r, in_holes,
                    out_l, out_r, out_holes, write_fates,
                    in_hole_fates):
        """writes: innermost-first [(pos, 'true'|'false')].
        write_fates: per UNIQUE position (latest value):
        ('one',) for true-filled cell or ('hole', slot)."""
        A = self.A
        in_holes = (list(in_holes) + [in_holes[-1]] * 4)[:4]
        IN = ht(in_l, in_r, in_holes)
        OUT = ht(out_l, out_r, out_holes)
        expr = f"({IN})"
        for pos, v in writes:
            expr = f"(writeAt {expr} ({pos}) {v})"
        A(f"  have {name} : {expr} = {OUT} := by")
        A(f"    funext q")
        ind = "    "
        seen = []
        for i, (pos, v) in enumerate(reversed(writes)):
            already = any(p == pos for p, _ in seen)
            if not already:
                hn = f"hw{i}"
                A(f"{ind}by_cases {hn} : q = ({pos})")
                A(f"{ind}· rw [{hn}, writeAt_same _ _ _]")
                fate = write_fates[pos]
                if fate[0] == 'one':
                    A(f"{ind}  exact (holeTape_one {NOTOR} (by omega) "
                      f"(by omega)).symm")
                else:
                    A(f"{ind}  exact (holeTape_hole "
                      f"{SLOT[fate[1]]}).symm")
                A(f"{ind}· rw [writeAt_other _ _ _ _ (by omega)]")
                ind += "  "
            else:
                A(f"{ind}rw [writeAt_other _ _ _ _ (by omega)]")
            seen.append((pos, v))
        self.inner3(ind, in_l, in_r, in_holes, out_l, out_r,
                    in_hole_fates)


def emit_episode(cp, name, doc, guards, in_shape, segments, out_head,
                 steps_expr, out_shape, extra_vars="", nat_vars=""):
    """in_shape: (l, r_in, holes). segments: list of dicts.
    Each segment transforms (state_letter, head, shape)."""
    A = cp.A
    S, SAFE = cp.S, cp.SAFE
    A(f"/-- {doc} -/")
    A(f"theorem {name} {{c : Config}} {{l h1 h2 r : Int}}{extra_vars}")
    if nat_vars:
        A(f"    {nat_vars}")
    A(f"    (hs : c.state = State.{S}) (hh : c.head = r)")
    A(f"    (ht : c.tape = {ht(*in_shape)})")
    for gname, gprop in guards:
        A(f"    ({gname} : {gprop})")
    A(f"    :")
    A(f"    stepN ({steps_expr}) c")
    A(f"        = some ⟨State.{S}, ({out_head}), {ht(*out_shape)}⟩ ∧")
    A(f"      {SAFE} c ({steps_expr}) := by")

    head = "r"
    shape = in_shape           # (l, r, holes)
    runs = []                  # (steps, run_hyp_name)
    seg_i = 0
    state = S
    for seg in segments:
        seg_i += 1
        kind = seg['kind']
        if kind == 'catrun':
            k, front = seg['k'], seg['front']
            l0, r0, holes0 = shape
            out_holes = seg['out_holes']
            fates = seg['in_hole_fates']
            fslot, cslot = seg['fslot'], seg['cslot']
            out_r = seg.get('out_high', seg.get('out_r', r0))
            out_l0 = seg.get('out_low', l0)
            t0j = seg['t0']    # justification for tape(head)=false
            t3j = seg['t3']
            A(f"  obtain ⟨hrun{seg_i}, hsafe{seg_i}⟩ := cat_run {k} "
              f"{'c' if seg_i == 1 else CFG(cp, state, head, shape)} "
              f"({head})")
            if seg_i == 1:
                A(f"    hs hh")
                A(f"    (by rw [ht]; exact {t0j})")
                A(f"    (by rw [ht]; exact {t3j})")
                A(f"    (by intro q hq1 hq2 hq3 hq4; rw [ht]; "
                  f"exact holeTape_one {NOTOR} (by omega) (by omega))")
            else:
                A(f"    rfl rfl")
                A(f"    {t0j}")
                A(f"    {t3j}")
                A(f"    (fun q hq1 hq2 hq3 hq4 => "
                  f"holeTape_one {NOTOR} (by omega) (by omega))")
            if seg_i == 1:
                A(f"  rw [ht] at hrun{seg_i}")
            cp.emit_catN(f"hN{seg_i}", l0, r0, holes0, head, k,
                         out_l0, out_r, out_holes, fslot, cslot, fates)
            A(f"  rw [hN{seg_i}] at hrun{seg_i}")
            if cp.mir:
                A(f"  rw [show ({head}) + 2 * ({k} : Int) = ({front}) "
                  f"from by omega] at hrun{seg_i}")
            else:
                A(f"  rw [show ({head}) - 2 * ({k} : Int) = ({front}) "
                  f"from by omega] at hrun{seg_i}")
            runs.append((f"10 * {k}", seg_i))
            head = front
            shape = (out_l0, out_r, out_holes)
            state = S
        elif kind == 'atom':
            aname, n = seg['name'], seg['n']
            cells = seg['cells']      # list of proof strings, ascending
            writes = seg['writes']    # [(pos, val)] innermost-first
            wfates = seg['write_fates']
            out_holes = seg['out_holes']
            out_l = seg.get('out_low', seg.get('out_l', shape[0]))
            out_r = seg.get('out_high', seg.get('out_r', shape[1]))
            fates = seg['in_hole_fates']
            end_state = seg['end_state']
            end_head = seg['end_head']
            l0, r0, holes0 = shape
            hv = seg.get('hvar', 'h')
            if seg_i == 1:
                A(f"  obtain ⟨hrun{seg_i}, hsafe{seg_i}⟩ := {aname}")
                A(f"    ({hv} := ({head})) hs hh")
                for cell in cells:
                    A(f"    (by rw [ht]; exact {cell})")
                A(f"  rw [ht] at hrun{seg_i}")
            else:
                A(f"  obtain ⟨hrun{seg_i}, hsafe{seg_i}⟩ := {aname}")
                A(f"    (c := {CFG(cp, state, head, shape)}) "
                  f"({hv} := ({head})) rfl rfl")
                for cell in cells:
                    A(f"    {cell}")
            cp.emit_towerN(f"hN{seg_i}", writes, l0, r0, holes0,
                           out_l, out_r, out_holes, wfates, fates)
            A(f"  rw [hN{seg_i}] at hrun{seg_i}")
            if seg.get('end_off_raw') and seg['end_off_raw'] != end_head:
                A(f"  rw [show ({seg['end_off_raw']}) = ({end_head}) "
                  f"from by omega] at hrun{seg_i}")
            runs.append((str(n), seg_i))
            head = end_head
            shape = (out_l, out_r, out_holes)
            state = end_state
        elif kind == 'fstep':
            nh = seg['end_head']
            A(f"  have hrun{seg_i} : stepN 1 "
              f"{CFG(cp, state, head, shape)}")
            A(f"      = some ⟨State.{S}, ({nh}), "
              f"{ht(*shape)}⟩ := by")
            A(f"    have hstp := step_F_any "
              f"(c := {CFG(cp, state, head, shape)}) rfl")
            A(f"    simp only at hstp")
            A(f"    rw [show ({head}) {'-' if cp.mir else '+'} 1 = "
              f"({nh}) from by omega] at hstp")
            A(f"    simp [stepN, hstp]")
            A(f"  have hsafe{seg_i} : {SAFE} "
              f"{CFG(cp, state, head, shape)} 1 := by")
            A(f"    intro k d hk hkd hP hread")
            A(f"    have hk0 : k = 0 := by omega")
            A(f"    subst hk0")
            A(f"    have hdd : ({CFG(cp, state, head, shape)} : Config) "
              f"= d := by simpa [stepN] using hkd")
            A(f"    rw [← hdd] at hP")
            A(f"    simp at hP")
            runs.append(("1", seg_i))
            head = nh
            state = S
        elif kind == 'sweep':
            mvar, endh = seg['m'], seg['end_head']
            sgn = '-' if cp.mir else '+'
            cell = (f"(fun i hi => by\n"
                    f"      show {ht(*shape)} (({head}) {sgn} 2 * (i : Int)) "
                    f"= true\n"
                    f"      exact holeTape_one {NOTOR} (by omega) "
                    f"(by omega))")
            A(f"  have hrun{seg_i} := sweep_mixed {mvar} "
              f"{CFG(cp, state, head, shape)} rfl")
            A(f"    {cell}")
            A(f"  have hsafe{seg_i} := sweep_mixed_safe {mvar} "
              f"{CFG(cp, state, head, shape)} rfl")
            A(f"    {cell}")
            A(f"  simp only at hrun{seg_i}")
            A(f"  rw [show ({head}) {'-' if cp.mir else '+'} "
              f"(2 * {mvar} : Int) = ({endh}) from by omega] "
              f"at hrun{seg_i}")
            runs.append((f"2 * {mvar}", seg_i))
            head = endh
    # composition
    A(f"  refine ⟨?_, ?_⟩")
    if len(runs) == 1:
        A(f"  · exact hrun1")
    else:
        A(f"  · rw [stepN_add, hrun1]")
    rest = [f"({t})" for t, _ in runs]
    for j in range(1, len(runs)):
        rem = " + (".join(rest[j:]) + ")" * (len(rest) - j - 1)
        A(f"    show stepN ({rem}) _ = _")
        if j < len(runs) - 1:
            A(f"    rw [stepN_add, hrun{runs[j][1]}]")
        else:
            A(f"    rw [hrun{runs[j][1]}]")
    chain = f"hsafe{runs[-1][1]}"
    for t, i in reversed(runs[:-1]):
        chain = f"({cp.comp} hrun{i} hsafe{i} {chain})"
    A(f"  · exact {chain}")


def CFG(cp, state, head, shape):
    return f"(⟨State.{state}, ({head}), {ht(*shape)}⟩ : Config)"
