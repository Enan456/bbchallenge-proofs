"""Simulation-driven Lean atom generator for dossier-2/3.

Each atom = (entry state, precondition pattern, step count). The script
is derived by running the real machine table over the pattern (any access
outside the pattern is an error), so the emitted theorem cannot diverge
from the machine. The emitter follows the proven cat_cycle template.
"""

def parse(code):
    tbl = {}
    for si, block in enumerate(code.split('_')):
        for b in range(2):
            tr = block[3 * b:3 * b + 3]
            tbl[('ABCDEF'[si], b)] = None if tr == '---' else \
                (int(tr[0]), tr[1], tr[2])
    return tbl


D2 = parse('1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD')
D3 = parse('1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE')


def simulate(tbl, entry, pattern, n):
    """Return script [(state, offset, read, write, next_state)]."""
    tape = dict(pattern)
    st, k = entry, 0
    script = []
    for _ in range(n):
        assert k in tape, f"access outside pattern at offset {k}"
        rd = tape[k]
        tr = tbl[(st, rd)]
        assert tr is not None, "halted inside atom"
        wr, mv, nst = tr
        script.append((st, k, rd, wr, nst))
        tape[k] = wr
        k += 1 if mv == 'R' else -1
        st = nst
    return script, st, k


def o(k, var='h'):
    if k == 0:
        return var
    return f"{var} + {k}" if k > 0 else f"{var} - {-k}"


def emit(name, doc, tbl, entry, pattern, n, probe, probe_off, safeseg):
    script, end_st, end_k = simulate(tbl, entry, pattern, n)
    pres = sorted(pattern.items())
    pname = {k: f"t{'m' if k < 0 else 'p'}{abs(k)}" for k, _ in pres}

    towers = []
    ws = []
    for st, k, rd, wr, nst in script:
        towers.append(tuple(ws))
        cur = None
        for x, v in reversed(ws):
            if x == k:
                cur = v
                break
        if cur is None:
            cur = pattern[k]
        if wr != cur:
            ws.append((k, wr))
    final = tuple(ws)

    def texpr(tw):
        e = 't'
        for k, v in tw:
            e = f"writeAt {'(' + e + ')' if e != 't' else 't'} ({o(k)}) " \
                f"{'true' if v else 'false'}"
        return e

    def ctexpr(tw):
        return texpr(tw).replace('writeAt t ', 'writeAt c.tape ', 1) \
            if tw else 'c.tape'

    # facts: value of cell k under tower tw
    facts = {}
    fact_lines = []
    fct = [0]

    def get_fact(tw, k):
        key = (tw, k)
        if key in facts:
            return facts[key]
        val = None
        depth = None
        for j in range(len(tw) - 1, -1, -1):
            if tw[j][0] == k:
                val, depth = tw[j][1], j
                break
        if depth is None:
            val = pattern[k]
            if not tw:
                facts[key] = pname[k]
                return pname[k]
            peel = ["writeAt_other _ _ _ _ (by omega)"] * len(tw)
            nm = f"hf{fct[0]}"; fct[0] += 1
            fact_lines.append(
                f"  have {nm} : ({texpr(tw)}) ({o(k)}) = "
                f"{'true' if val else 'false'} := by\n"
                f"    rw [{', '.join(peel)}]\n"
                f"    exact {pname[k]}")
            facts[key] = nm
            return nm
        peel = ["writeAt_other _ _ _ _ (by omega)"] * (len(tw) - 1 - depth)
        nm = f"hf{fct[0]}"; fct[0] += 1
        if peel:
            fact_lines.append(
                f"  have {nm} : ({texpr(tw)}) ({o(k)}) = "
                f"{'true' if val else 'false'} := by\n"
                f"    rw [{', '.join(peel)}]\n"
                f"    exact writeAt_same _ _ _")
        else:
            fact_lines.append(
                f"  have {nm} : ({texpr(tw)}) ({o(k)}) = "
                f"{'true' if val else 'false'} := writeAt_same _ _ _")
        facts[key] = nm
        return nm

    # pre-pass to create all facts in order
    for i, (st, k, rd, wr, nst) in enumerate(script):
        get_fact(towers[i], k)
    # probe-side facts
    for i, (st, k, rd, wr, nst) in enumerate(script):
        if st == probe and rd == 0:
            get_fact(towers[i], k + probe_off)

    L = []
    A = L.append
    A(f"/-- {doc} -/")
    A(f"theorem {name} {{c : Config}} {{h : Int}}")
    A(f"    (hs : c.state = State.{entry}) (hh : c.head = h)")
    conds = [f"({pname[k]} : c.tape ({o(k)}) = {'true' if v else 'false'})"
             for k, v in pres]
    for i in range(0, len(conds), 2):
        A("    " + " ".join(conds[i:i + 2]))
    A("    :")
    A(f"    stepN {n} c = some ⟨State.{end_st}, {o(end_k)},")
    A(f"        {ctexpr(final)}⟩ ∧")
    A(f"      {safeseg} c {n} := by")
    A("  obtain ⟨s, hd, t⟩ := c")
    A(f"  simp only at hs hh {' '.join(pname[k] for k, _ in pres)}")
    A("  subst hs")
    A("  have hp : h = hd := hh.symm")
    A("  subst hp")
    L.extend(fact_lines)
    for i, (st, k, rd, wr, nst) in enumerate(script):
        tw = towers[i]
        nxt = script[i + 1] if i + 1 < n else None
        nst2 = nxt[0] if nxt else end_st
        nk = nxt[1] if nxt else end_k
        ntw = towers[i + 1] if i + 1 < n else final
        fact = facts[(tw, k)]
        A(f"  have s{i} : step ⟨State.{st}, {o(k)}, {texpr(tw)}⟩")
        A(f"      = some ⟨State.{nst2}, {o(nk)}, {texpr(ntw)}⟩ := by")
        if tw == ntw:
            A(f"    have hself := writeAt_self _ _ {fact}")
            A(f"    simp [step, instr, {fact}, move, hself]")
        else:
            A(f"    simp [step, instr, {fact}, move]")
        A("    try omega")
    for i in range(1, n):
        st, k, rd, wr, nst = script[i]
        A(f"  have p{i} : stepN {i} ⟨State.{script[0][0]}, h, t⟩ = "
          f"some ⟨State.{st}, {o(k)}, {texpr(towers[i])}⟩ := by")
        A(f"    simp [stepN, {', '.join('s%d' % j for j in range(i))}]")
    A(f"  refine ⟨by simp [stepN, "
      f"{', '.join('s%d' % j for j in range(n))}], ?_⟩")
    A("  intro k d hk hkd hP hread")
    A(f"  have hcase : {' ∨ '.join(f'k = {i}' for i in range(n))} := by omega")
    A(f"  rcases hcase with {' | '.join(['rfl'] * n)}")
    for i, (st, k, rd, wr, nst) in enumerate(script):
        tw = towers[i]
        cfg = f"⟨State.{st}, {o(k)}, {texpr(tw)}⟩"
        if i == 0:
            grab = [f"    have hdd : ({cfg} : Config) = d := by "
                    f"simpa [stepN] using hkd"]
            sub = "rw [← hdd]"
        else:
            grab = [f"    rw [p{i}] at hkd"]
            sub = "rw [← Option.some_inj.mp hkd]"
        if st != probe:
            A("  ·" + grab[0][3:])
            A(f"    {sub} at hP")
            A("    simp at hP")
        elif rd == 1:
            A("  ·" + grab[0][3:])
            A(f"    {sub} at hread")
            A(f"    rw [show ({cfg} : Config).tape ({cfg} : Config).head")
            A(f"        = ({texpr(tw)}) ({o(k)}) from rfl] at hread")
            A(f"    rw [{facts[(tw, k)]}] at hread")
            A("    exact absurd hread (by simp)")
        else:
            side = k + probe_off
            sf = facts[(tw, side)]
            op = "+ 1" if probe_off == 1 else "- 1"
            A("  ·" + grab[0][3:])
            A(f"    {sub}")
            A(f"    show ({texpr(tw)}) ({o(k)} {op}) = true")
            A(f"    rw [show {o(k)} {op} = {o(side)} by omega]")
            A(f"    exact {sf}")
    return "\n".join(L), end_st, end_k, final
