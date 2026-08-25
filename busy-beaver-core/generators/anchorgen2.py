"""Composite anchor generator: short concrete runs (small towers)
glued by literal instantiations of the episode theorems.

Parts:
  A: blank -> first spawn entry (concrete, v5-style rfl/evaluator)
  B: chain of episode-theorem instances at literal parameters
  C: degenerate episode (concrete, holeTape base)
Glue: stepN_add + safety compose into one `anchor_run`.
"""
import sys
sys.path.insert(0, '.')
from atomgen2 import parse

CH = 40


def oint(k):
    return f"({k} : Int)" if k >= 0 else f"(-{-k} : Int)"


def htlit(l, hi, holes):
    hs = (list(holes) + [holes[-1]] * 4)[:4]
    return (f"holeTape {oint(l)} {oint(hi)} {oint(hs[0])} {oint(hs[1])} "
            f"{oint(hs[2])} {oint(hs[3])}")


def entry_cfg(S, ms, mirror):
    """Config text of a spawn-entry abstract state (actual coords)."""
    three, l, h1, h2, r = ms
    holes = [h1, h2] + ([r + 3 if mirror else r - 3] if three else [])
    lo, hi = (r + 1, l) if mirror else (l, r - 1)
    return (f"(⟨State.{S}, {oint(r)}, "
            f"{htlit(lo, hi, holes)}⟩ : Config)")


def gen_part(name, code, start, N, probe, probe_off, safeseg, mirror,
             end_state_letter):
    """Concrete run part. start = ('blank', None) or
    ('cfg', (state_letter, head, base_tape_fn, base_expr))."""
    tbl = parse(code)
    if start[0] == 'blank':
        tape = {}
        st, h = 'A', 0
        base_expr = "blankStart.tape"
        base_val = lambda q: 0
        cfg0 = "(⟨State.A, (0 : Int), blankStart.tape⟩ : Config)"
    else:
        st, h, base_val, base_expr, cfg0 = start[1]
        tape = {}
    script = []
    for _ in range(N):
        rd = tape[h] if h in tape else base_val(h)
        tr = tbl[(st, rd)]
        assert tr is not None
        wr, mv, nst = tr
        script.append((st, h, rd, wr, nst))
        tape[h] = wr
        h += 1 if mv == 'R' else -1
        st = nst
    end_st, end_h = st, h

    towers = []
    ws = []
    cur = {}
    for stt, k, rd, wr, nst in script:
        towers.append(tuple(ws))
        if cur.get(k, base_val(k)) != wr:
            ws.append((k, wr))
        cur[k] = wr
    final = tuple(ws)

    def texpr(tw):
        e = base_expr
        for k, v in tw:
            e = f"writeAt ({e}) {oint(k)} {'true' if v else 'false'}"
        return e

    def cfg(i):
        if i == 0:
            return cfg0
        if i == N:
            return (f"(⟨State.{end_st}, {oint(end_h)}, {texpr(final)}⟩ "
                    f": Config)")
        stt, k, rd, wr, nst = script[i]
        return (f"(⟨State.{stt}, {oint(k)}, {texpr(towers[i])}⟩ "
                f": Config)")

    facts = {}
    fact_lines = []
    fct = [0]

    def get_fact(tw, k, val):
        key = (tw, k)
        if key in facts:
            return facts[key]
        nm = f"{name}f{fct[0]}"
        fct[0] += 1
        fact_lines.append(
            f"  have {nm} : ({texpr(tw)}) {oint(k)} = "
            f"{'true' if val else 'false'} := rfl")
        facts[key] = nm
        return nm

    for i, (stt, k, rd, wr, nst) in enumerate(script):
        if stt == probe:
            get_fact(towers[i], k, bool(rd))
            if rd == 0:
                get_fact(towers[i], k + probe_off, True)

    L = []
    A = L.append
    A(f"set_option maxHeartbeats 64000000 in")
    A(f"set_option maxRecDepth 100000 in")
    A(f"theorem {name} :")
    A(f"    stepN {N} {cfg0}")
    A(f"        = some {cfg(N)} ∧")
    A(f"      {safeseg} {cfg0} {N} := by")
    L.extend(fact_lines)
    for i, (stt, k, rd, wr, nst) in enumerate(script):
        tw = towers[i]
        ntw = towers[i + 1] if i + 1 < N else final
        nxt_k = script[i + 1][1] if i + 1 < N else end_h
        ev = "step_evalR" if nxt_k == k + 1 else "step_evalL"
        rds = "true" if rd else "false"
        A(f"  have s{i} : step {cfg(i)} = some {cfg(i + 1)} := by")
        if tw == ntw:
            A(f"    rw [{ev} (rfl : ({texpr(tw)}) {oint(k)} = {rds}) "
              f"rfl,")
            A(f"      writeAt_self (value := "
              f"{'true' if wr else 'false'}) _ _ rfl]")
        else:
            A(f"    rw [{ev} (rfl : ({texpr(tw)}) {oint(k)} = {rds}) "
              f"rfl]")
        A(f"    rfl")
    chunks = []
    startc = 0
    while startc < N:
        chunks.append((startc, min(startc + CH, N)))
        startc += CH
    for ci, (a, b) in enumerate(chunks):
        for j in range(a + 1, b + 1):
            if j == a + 1:
                A(f"  have q{j} : stepN 1 {cfg(a)} = some {cfg(j)} :=")
                A(f"    (stepN_one _).trans s{j - 1}")
            else:
                A(f"  have q{j} : stepN {j - a} {cfg(a)} = some {cfg(j)} "
                  f":=")
                A(f"    stepN_chain q{j - 1} ((stepN_one _).trans "
                  f"s{j - 1})")
        A(f"  have hcs{ci} : {safeseg} {cfg(a)} {b - a} := by")
        A(f"    intro k d hk hkd hP hread")
        A(f"    have hcase : "
          f"{' ∨ '.join(f'k = {j}' for j in range(b - a))} := by omega")
        A(f"    rcases hcase with {' | '.join(['rfl'] * (b - a))}")
        for j in range(a, b):
            stt, k2, rd, wr, nst = script[j]
            tw = towers[j]
            if j == a:
                grab = (f"    · have hdd : {cfg(j)} = d := "
                        f"Option.some_inj.mp hkd")
                sub0 = "rw [← hdd]"
            else:
                grab = f"    · rw [q{j}] at hkd"
                sub0 = "rw [← Option.some_inj.mp hkd]"
            if stt != probe:
                A(grab)
                A(f"      {sub0} at hP")
                A(f"      exact absurd hP (by decide)")
            elif rd == 1:
                fn = facts[(tw, k2)]
                cfgj = cfg(j)
                A(grab)
                A(f"      {sub0} at hread")
                A(f"      rw [show ({cfgj} : Config).tape "
                  f"({cfgj} : Config).head")
                A(f"          = ({texpr(tw)}) {oint(k2)} from rfl] "
                  f"at hread")
                A(f"      rw [{fn}] at hread")
                A(f"      exact absurd hread (by simp)")
            else:
                side = k2 + probe_off
                sf = facts[(tw, side)]
                op = "+ 1" if probe_off == 1 else "- 1"
                A(grab)
                A(f"      {sub0}")
                A(f"      show ({texpr(tw)}) ({oint(k2)} {op}) = true")
                A(f"      rw [show {oint(k2)} {op} = {oint(side)} by "
                  f"omega]")
                A(f"      exact {sf}")
    A(f"  refine ⟨?_, ?_⟩")
    rchain = f"q{chunks[-1][1]}"
    for ci in range(len(chunks) - 2, -1, -1):
        a, b = chunks[ci]
        rchain = f"(stepN_chain q{b} {rchain})"
    A(f"  · exact {rchain}")
    chain = f"hcs{len(chunks) - 1}"
    for ci in range(len(chunks) - 2, -1, -1):
        a, b = chunks[ci]
        chain = f"({'bsafe_compose' if mirror else 'csafe_compose'} "\
                f"q{b} hcs{ci} {chain})"
    A(f"  · exact {chain}")
    end_cfg_txt = cfg(N)
    return "\n".join(L), script, final, (end_st, end_h), texpr(final)


SLOT = ["(Or.inl (by omega))",
        "(Or.inr (Or.inl (by omega)))",
        "(Or.inr (Or.inr (Or.inl (by omega))))",
        "(Or.inr (Or.inr (Or.inr (by omega))))"]
NOTOR = "(by intro hor; rcases hor with hx | hx | hx | hx <;> omega)"


def emit_shape_eq(A, name, final, base_expr, base, out, tape_of):
    """have {name} : (tower over base) = holeTape OUT.
    base: None (all-false) or (lo, hi, holes). out: (lo, hi, holes)."""
    lo, hi, holes = out
    tgt = htlit(lo, hi, holes)
    A(f"  have {name} : {tape_of(final)} = {tgt} := by")
    A(f"    funext q")
    ind = "    "
    seen = set()
    hw_i = 0
    outholes = (list(holes) + [holes[-1]] * 4)[:4]
    for k, v in reversed(final):
        if k in seen:
            A(f"{ind}rw [writeAt_other _ _ _ _ (by omega)]")
            continue
        seen.add(k)
        hn = f"hw{hw_i}"
        hw_i += 1
        A(f"{ind}by_cases {hn} : q = {oint(k)}")
        A(f"{ind}· rw [{hn}, writeAt_same _ _ _]")
        # target value at k
        tval = 0 if k in holes else (1 if lo <= k <= hi else 0)
        assert (1 if v else 1) == 1
        assert bool(v) == bool(tval), (k, v, tval)
        if v:
            A(f"{ind}  exact (holeTape_one {NOTOR} (by omega) "
              f"(by omega)).symm")
        else:
            if k in holes:
                A(f"{ind}  exact (holeTape_hole "
                  f"{SLOT[outholes.index(k)]}).symm")
            else:
                A(f"{ind}  exact (holeTape_out {NOTOR} "
                  f"(by intro hcc; omega)).symm")
        A(f"{ind}· rw [writeAt_other _ _ _ _ (by omega)]")
        ind += "  "
    if base is None:
        A(f"{ind}show false = holeTape _ _ _ _ _ _ q")
        A(f"{ind}by_cases hh1 : q = {oint(holes[0])}")
        A(f"{ind}· exact (holeTape_hole (Or.inl hh1)).symm")
        A(f"{ind}· by_cases hh2 : q = {oint(holes[1] if len(holes) > 1 else holes[0])}")
        A(f"{ind}  · exact (holeTape_hole (Or.inr (Or.inl hh2))).symm")
        A(f"{ind}  · exact (holeTape_out (by intro hor; rcases hor "
          f"with hx | hx | hx | hx <;> omega) "
          f"(by intro hcc; omega)).symm")
    else:
        blo, bhi, bholes = base
        bh4 = (list(bholes) + [bholes[-1]] * 4)[:4]
        A(f"{ind}by_cases hin : q = {oint(bh4[0])} ∨ q = {oint(bh4[1])}"
          f" ∨ q = {oint(bh4[2])} ∨ q = {oint(bh4[3])}")
        A(f"{ind}· rw [holeTape_hole hin]")
        A(f"{ind}  rcases hin with hx | hx | hx | hx")
        for bh in bh4:
            # unwritten base hole: target value must be 0
            if bh in seen:
                A(f"{ind}  · exfalso")
                A(f"{ind}    omega")
            else:
                tval = 0 if bh in holes else (1 if lo <= bh <= hi else 0)
                assert tval == 0, (bh, out)
                if bh in holes:
                    A(f"{ind}  · exact (holeTape_hole "
                      f"{SLOT[outholes.index(bh)]}).symm")
                else:
                    A(f"{ind}  · exact (holeTape_out {NOTOR} "
                      f"(by intro hcc; omega)).symm")
        oh4 = (list(holes) + [holes[-1]] * 4)[:4]
        A(f"{ind}· by_cases hrange : {oint(blo)} ≤ q ∧ q ≤ {oint(bhi)}")
        A(f"{ind}  · obtain ⟨hr1, hr2⟩ := hrange")
        A(f"{ind}    rw [holeTape_one hin hr1 hr2]")
        A(f"{ind}    exact (holeTape_one {NOTOR} (by omega) "
          f"(by omega)).symm")
        A(f"{ind}  · have hrr := not_and_le' hrange")
        A(f"{ind}    clear hrange")
        A(f"{ind}    rw [holeTape_out hin (by intro hcc; omega)]")
        A(f"{ind}    by_cases hoh : q = {oint(oh4[0])} ∨ "
          f"q = {oint(oh4[1])} ∨ q = {oint(oh4[2])} ∨ "
          f"q = {oint(oh4[3])}")
        A(f"{ind}    · exact (holeTape_hole hoh).symm")
        A(f"{ind}    · exact (holeTape_out hoh "
          f"(by intro hcc; omega)).symm")


def gen_part_normalized(name, code, start, N, probe, probe_off, safeseg,
                        mirror, out_shape):
    """gen_part + final shape normalization to holeTape `out_shape` and
    a theorem statement in holeTape form."""
    text, script, final, (end_st, end_h), final_expr = gen_part(
        name + "0", code, start, N, probe, probe_off, safeseg, mirror,
        None)
    # rebuild: we wrap the raw part theorem, then normalize
    if start[0] == 'blank':
        cfg0 = "(⟨State.A, (0 : Int), blankStart.tape⟩ : Config)"
        base = None
        base_expr = "blankStart.tape"
    else:
        st0, h0, base_val, base_expr, cfg0 = start[1]
        base = start[2]
    lo, hi, holes = out_shape
    L = [text, ""]
    A = L.append
    A(f"set_option maxRecDepth 100000 in")
    A(f"theorem {name} :")
    A(f"    stepN {N} {cfg0}")
    A(f"        = some (⟨State.{end_st}, {oint(end_h)}, "
      f"{htlit(lo, hi, holes)}⟩ : Config) ∧")
    A(f"      {safeseg} {cfg0} {N} := by")
    A(f"  obtain ⟨hrun, hsafe⟩ := {name}0")

    def tape_of(fin):
        e = base_expr
        for k, v in fin:
            e = f"writeAt ({e}) {oint(k)} {'true' if v else 'false'}"
        return e
    emit_shape_eq(A, "hshape", final, base_expr, base, out_shape,
                  tape_of)
    A(f"  rw [hshape] at hrun")
    A(f"  exact ⟨hrun, hsafe⟩")
    return "\n".join(L)
