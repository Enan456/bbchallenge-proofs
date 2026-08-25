"""Composite anchor driver for both machines."""
import sys, pathlib
sys.path.insert(0, '.')
from anchorgen2 import (gen_part_normalized, entry_cfg, htlit, oint,
                        gen_part)
from vpredict import predict

RULE_TH = {'spawn': 'episode_spawn', 'spawn-variant': 'episode_variant',
           'terminate': 'episode_generic',
           'terminate+hole': 'episode_carried_term',
           'fuse+hole': 'episode_fuse', 'edge-odd': 'episode_deep_odd',
           'edge-even': 'episode_deep_even'}
NGUARD = {'episode_spawn': 3, 'episode_variant': 3,
          'episode_generic': 5, 'episode_fuse': 5,
          'episode_carried_term': 5, 'episode_deep_odd': 5,
          'episode_deep_even': 5}


def kvals(rule, ms):
    l, hs, r = ms
    h1, h2 = hs[0], hs[1]
    if rule == 'terminate':
        return dict(k1=(r - h2 - 6) // 2, k2=(h2 - h1 - 4) // 2,
                    m=(r + 1 - h1 - 7) // 2)
    if rule == 'fuse+hole':
        return dict(k1=(r - h2 - 6) // 2, m=(r + 2 - h2 - 8) // 2)
    if rule == 'terminate+hole':
        return dict(k1=(r - h1 - 5) // 2, m=(r + 2 - h1 - 7) // 2)
    if rule == 'edge-odd':
        return dict(k1=(r - h1 - 6) // 2, k2=(h1 + 1 - l - 4) // 2,
                    m=(r + 1 - l - 6) // 2)
    if rule == 'edge-even':
        return dict(k1=(r - h1 - 6) // 2, k2=(h1 + 1 - l - 5) // 2,
                    m=(r + 1 - l - 7) // 2)
    return {}


def steps_of(rule, kv):
    if rule in ('spawn', 'spawn-variant'):
        return 7, "7"
    k1, m = kv['k1'], kv['m']
    if rule == 'terminate':
        k2 = kv['k2']
        return (10 * k1 + 13 + 10 * k2 + 13 + 1 + 2 * m,
                f"10 * {k1} + (13 + (10 * {k2} + (13 + (1 + 2 * {m}))))")
    if rule == 'fuse+hole':
        return (10 * k1 + 19 + 1 + 2 * m,
                f"10 * {k1} + (19 + (1 + 2 * {m}))")
    if rule == 'terminate+hole':
        return (10 * k1 + 13 + 1 + 2 * m,
                f"10 * {k1} + (13 + (1 + 2 * {m}))")
    if rule == 'edge-odd':
        k2 = kv['k2']
        return (10 * k1 + 13 + 10 * k2 + 3 + 10 + 1 + 2 * m,
                f"10 * {k1} + (13 + (10 * {k2} + (3 + (10 + (1 + 2 * "
                f"{m})))))")
    if rule == 'edge-even':
        k2 = kv['k2']
        return (10 * k1 + 13 + 10 * k2 + 6 + 13 + 1 + 2 * m,
                f"10 * {k1} + (13 + (10 * {k2} + (6 + (13 + (1 + 2 * "
                f"{m})))))")


def build(code, mirror, S, safeseg, comp, probe, poff, nA, ms1_norm,
          n_total, s_end_actual, marker_file, ns):
    sgn = -1 if mirror else 1

    def act(ms_norm):
        l, hs, r = ms_norm
        three = len(hs) == 3
        return (three, sgn * l, sgn * hs[0], sgn * hs[1], sgn * r)

    # chain
    chain = []
    s = ms1_norm
    while True:
        out, rule = predict(s)
        if out is None:
            break
        chain.append((rule, s, out))
        s = out
    deg_entry_norm = s
    # part A
    msa = act(ms1_norm)
    _, lA, h1A, h2A, rA = msa
    loA, hiA = (rA + 1, lA) if mirror else (lA, rA - 1)
    partA = gen_part_normalized(
        "anchor_partA", code, ('blank', None), nA, probe, poff, safeseg,
        mirror, (min(loA, hiA), max(loA, hiA), [h1A, h2A]))
    # episodes
    L = []
    A = L.append
    comps = []          # (steps_lit, run_name, safe_name, cfg_in, cfg_out)
    prev_holeexit = None   # (l, r_old, A) when prev rule was hole-exit
    cfg_in = entry_cfg(S, msa, mirror)
    for i, (rule, msn, mso) in enumerate(chain):
        th = RULE_TH[rule]
        kv = kvals(rule, msn)
        steps_lit, steps_expr = steps_of(rule, kv)
        three_in = len(msn[1]) == 3
        _, l_i, h1_i, h2_i, r_i = act(msn)
        mso_a = act(mso)
        # output config text
        if rule in ('terminate+hole', 'fuse+hole'):
            Ah = (h1_i + 6 * sgn) if rule == 'terminate+hole' \
                else (h2_i + 7 * sgn)
            r_out = r_i + 2 * sgn
            lo_i, hi_i = (r_i, l_i) if mirror else (l_i, r_i)
            cfg_out = (f"(⟨State.{S}, {oint(r_out)}, "
                       f"{htlit(min(lo_i, hi_i), max(lo_i, hi_i), [Ah])}"
                       f"⟩ : Config)")
            next_rebase = (l_i, r_i, Ah)
        else:
            cfg_out = entry_cfg(S, mso_a, mirror)
            next_rebase = None
        # ht argument
        if prev_holeexit is None:
            ht_arg = "rfl"
        else:
            lp, rp, Ap = prev_holeexit
            ht_arg = (f"(holeTape_rebase {oint(lp)} {oint(rp)} "
                      f"{oint(Ap)})")
        nat_args = " ".join(f"({k} := {v})" for k, v in kv.items())
        guards = " ".join(["(by omega)"] * NGUARD[th])
        A(f"  obtain ⟨he{i}0, hs{i}0⟩ := {th}")
        A(f"    (c := {cfg_in}) (l := {oint(l_i)}) (h1 := {oint(h1_i)}) "
          f"(h2 := {oint(h2_i)}) (r := {oint(r_i)}) {nat_args}")
        A(f"    rfl rfl {ht_arg}")
        A(f"    {guards}")
        A(f"  have he{i} : stepN {steps_lit} {cfg_in} = some "
          f"{cfg_out} := he{i}0")
        A(f"  have hs{i} : {safeseg} {cfg_in} {steps_lit} := hs{i}0")
        comps.append((steps_lit, f"he{i}", f"hs{i}", cfg_in, cfg_out))
        cfg_in = cfg_out
        prev_holeexit = next_rebase
    # part C
    lp, rp, Ap = prev_holeexit
    loC, hiC = (min(rp, lp), max(rp, lp))
    baseC = (loC, hiC, [Ap])

    def base_val(q):
        return 1 if (loC <= q <= hiC and q != Ap) else 0
    deg_a = act(deg_entry_norm)
    _, lD, h1D, h2D, rD = deg_a
    base_expr = htlit(loC, hiC, [Ap])
    cfgC0 = cfg_in
    stC, hC = S, rD
    nC = n_total - nA - sum(c[0] for c in comps)
    _, lE, h1E, h2E, rE = s_end_actual
    loE, hiE = (rE + 1, lE) if mirror else (lE, rE - 1)
    partC = gen_part_normalized(
        "anchor_partC", code,
        ('cfg', (stC, hC, base_val, base_expr, cfgC0), baseC),
        nC, probe, poff, safeseg, mirror,
        (min(loE, hiE), max(loE, hiE), [h1E, h2E]))
    # assembly
    G = []
    B = G.append
    B(f"set_option maxRecDepth 100000 in")
    B(f"/-- **The anchor run**: {n_total} steps from the blank tape to "
      f"the abstract orbit's start state — concrete startup, "
      f"{len(chain)} certified episode instances, and the concrete "
      f"degenerate episode, glued. -/")
    B(f"theorem anchor_run :")
    B(f"    stepN {n_total} blankStart")
    B(f"        = some (⟨State.{S}, {oint(rE)}, "
      f"{htlit(min(loE, hiE), max(loE, hiE), [h1E, h2E])}⟩ : Config) ∧")
    B(f"      {safeseg} blankStart {n_total} := by")
    B(f"  obtain ⟨hA, hsA⟩ := anchor_partA")
    G.extend(L)
    B(f"  obtain ⟨hC, hsC⟩ := anchor_partC")
    allc = [(nA, "hA", "hsA")] + \
        [(c[0], c[1], c[2]) for c in comps] + [(nC, "hC", "hsC")]
    B(f"  refine ⟨?_, ?_⟩")
    rchain = allc[-1][1]
    for i in range(len(allc) - 2, -1, -1):
        rchain = f"(stepN_chain {allc[i][1]} {rchain})"
    B(f"  · exact {rchain}")
    chain_s = allc[-1][2]
    for i in range(len(allc) - 2, -1, -1):
        chain_s = f"({comp} {allc[i][1]} {allc[i][2]} {chain_s})"
    B(f"  · exact {chain_s}")

    EVAL = """/-- One-step evaluator, rightward: a literal table row plus a
literal read gives the successor configuration by rewriting, with no
proof search. -/
theorem step_evalR {s s' : State} {b w : Bool} {t : Int → Bool}
    {p : Int} (ht : t p = b)
    (hi : instr s b = some ⟨s', w, Dir.R⟩) :
    step ⟨s, p, t⟩ = some ⟨s', p + 1, writeAt t p w⟩ := by
  simp [step, ht, hi, move]

/-- One-step evaluator, leftward. -/
theorem step_evalL {s s' : State} {b w : Bool} {t : Int → Bool}
    {p : Int} (ht : t p = b)
    (hi : instr s b = some ⟨s', w, Dir.L⟩) :
    step ⟨s, p, t⟩ = some ⟨s', p - 1, writeAt t p w⟩ := by
  simp [step, ht, hi, move]

theorem stepN_one (c : Config) : stepN 1 c = step c := by
  cases h : step c <;> simp [stepN, h]

/-- Term-mode run gluing: no rewriting on `stepN` goals, so the
elaborator never tries to evaluate a long run by unfolding. -/
theorem stepN_chain {a b : Nat} {c c' c'' : Config}
    (h1 : stepN a c = some c') (h2 : stepN b c' = some c'') :
    stepN (a + b) c = some c'' := by
  rw [stepN_add, h1]
  exact h2
"""
    if mirror:
        EVAL += """
/-- Rebasing a single-hole shape across a hole-exit (mirror). -/
theorem holeTape_rebase (l r A : Int) :
    holeTape r l A A A A
      = holeTape (r - 1) l A (r - 1) (r - 1) (r - 1) := by
  funext q
  by_cases hqa : q = A
  · rw [holeTape_hole (Or.inl hqa), holeTape_hole (Or.inl hqa)]
  · by_cases hqr : q = r - 1
    · rw [holeTape_hole (Or.inr (Or.inl hqr)),
          holeTape_out (by intro hor; rcases hor with hx | hx | hx | hx
                          <;> omega)
            (by intro hcc; omega)]
    · by_cases hrange : r ≤ q ∧ q ≤ l
      · obtain ⟨hr1, hr2⟩ := hrange
        rw [holeTape_one (by intro hor; rcases hor with hx | hx | hx | hx
              <;> omega) hr1 hr2,
            holeTape_one (by intro hor; rcases hor with hx | hx | hx | hx
              <;> omega) (by omega) (by omega)]
      · have hrr := not_and_le' hrange
        clear hrange
        rw [holeTape_out (by intro hor; rcases hor with hx | hx | hx | hx
              <;> omega) (by intro hcc; omega),
            holeTape_out (by intro hor; rcases hor with hx | hx | hx | hx
              <;> omega) (by intro hcc; omega)]
"""
    else:
        EVAL += """
/-- Rebasing a single-hole shape across a hole-exit: the untouched
virgin cell at `r + 1` becomes the shape's second hole. -/
theorem holeTape_rebase (l r A : Int) :
    holeTape l r A A A A
      = holeTape l (r + 1) A (r + 1) (r + 1) (r + 1) := by
  funext q
  by_cases hqa : q = A
  · rw [holeTape_hole (Or.inl hqa), holeTape_hole (Or.inl hqa)]
  · by_cases hqr : q = r + 1
    · rw [holeTape_hole (Or.inr (Or.inl hqr)),
          holeTape_out (by intro hor; rcases hor with hx | hx | hx | hx
                          <;> omega)
            (by intro hcc; omega)]
    · by_cases hrange : l ≤ q ∧ q ≤ r
      · obtain ⟨hr1, hr2⟩ := hrange
        rw [holeTape_one (by intro hor; rcases hor with hx | hx | hx | hx
              <;> omega) hr1 hr2,
            holeTape_one (by intro hor; rcases hor with hx | hx | hx | hx
              <;> omega) (by omega) (by omega)]
      · have hrr := not_and_le' hrange
        clear hrange
        rw [holeTape_out (by intro hor; rcases hor with hx | hx | hx | hx
              <;> omega) (by intro hcc; omega),
            holeTape_out (by intro hor; rcases hor with hx | hx | hx | hx
              <;> omega) (by intro hcc; omega)]
"""
    text = (EVAL + "\n" + partA + "\n\n" + partC + "\n\n" + "\n".join(G))
    p = pathlib.Path(f'/Users/enan/Documents/bbchallenge-proofs/'
                     f'busy-beaver-core/BusyBeaverCore/{marker_file}')
    src = p.read_text()
    MARK = '-- ANCHOR-BEGIN (generated)'
    if MARK in src:
        i = src.index(MARK)
        j = src.index('-- ABSTRACT-BEGIN (generated)', i)
        src = src[:i] + MARK + '\n' + text + '\n\n' + src[j:]
    p.write_text(src)
    print(f'{marker_file}: composite anchor '
          f'(nA={nA}, episodes={len(chain)}, nC={nC}, total='
          f'{nA + sum(c[0] for c in comps) + nC} vs {n_total})')
    assert nA + sum(c[0] for c in comps) + nC == n_total


build('1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD', False, 'D',
      'CSafeSeg', 'csafe_compose', 'C', 1,
      111, (-7, (2, 6), 9), 235, (False, -8, -2, 12, 13),
      'Dossier2RawTM.lean', 'Dossier2RawTM')
build('1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE', True, 'E',
      'BSafeSeg', 'bsafe_compose', 'B', -1,
      164, (-9, (-3, 5), 8), 2044, (False, 17, 11, -39, -40),
      'Dossier3RawTM.lean', 'Dossier3RawTM')
