"""Empirical validation of the proven dossier-2/3 Lean theorems.

For each raw step of a long run, whenever a theorem's precondition holds,
schedule its N-step prediction and later verify it against the actual
machine state: end state, end head, and the FULL tape restricted to the
window the run can reach (cells outside the visited head range are
untouched by construction). Also checks the global probe-safety
conjectures (CProbeSafe / BProbeSafe) over the whole horizon.
"""
import sys
from collections import defaultdict

def parse(code):
    tbl = {}
    for si, block in enumerate(code.split('_')):
        st = 'ABCDEF'[si]
        for b in range(2):
            tr = block[3*b:3*b+3]
            tbl[(st, b)] = None if tr == '---' else (int(tr[0]), tr[1], tr[2])
    return tbl

D2 = parse('1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD')
D3 = parse('1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE')

def validate(name, tbl, sgn, danger, probe_off, cyc_state, spawn_state,
             sweep_state, steps):
    # sgn=-1: dossier-2 (leftward caterpillar); sgn=+1: dossier-3 mirror
    N = steps
    SIZE = 1 << 22
    OFF = SIZE >> 1
    tape = bytearray(SIZE)
    st, h = 'A', OFF
    pending = defaultdict(list)
    stats = defaultdict(int)
    fails = []
    probe_reads = 0
    max_chain = chain = 0
    last_cyc_end = None

    for t in range(N):
        b = tape[h]
        # --- global probe-safety conjecture check
        if st == danger and b == 0:
            probe_reads += 1
            if tape[h + probe_off] != 1:
                fails.append((t, 'PROBE-SAFETY VIOLATED', st, h - OFF))
        # --- precondition detection (before stepping)
        if st == cyc_state:
            # cat_cycle: pattern 0,1,1,0,1,1,1 going sgn-ward from h
            pat = [tape[h + sgn*i] for i in range(7)]
            if pat == [0,1,1,0,1,1,1]:
                w = {h: 1, h + sgn*2: 0, h + sgn*3: 1, h + sgn*5: 0}
                snap = {q: tape[q] for q in range(h - 8, h + 9)}
                pending[t + 10].append(('cat_cycle', cyc_state,
                                        h + sgn*2, w, snap, t))
        if st == spawn_state:
            # spawn_step: 0 at h, three 1s behind (opposite of travel dir)
            if (tape[h] == 0 and tape[h + sgn*1] == 1 and
                    tape[h + sgn*2] == 1 and tape[h + sgn*3] == 1):
                w = {h: 1, h + sgn*2: 0}
                snap = {q: tape[q] for q in range(h - 8, h + 9)}
                pending[t + 7].append(('spawn_step', spawn_state,
                                       h - sgn*1, w, snap, t))
        if st == sweep_state and (stats['sweep_seen'] % 997 == 0
                                  or stats['sweep_seen'] < 5):
            # sweep: maximal run of 1s in travel direction (away from block)
            n = 0
            d = -sgn  # sweep travels opposite to caterpillar direction
            while tape[h + d*n] == 1 and n < 4000:
                n += 1
            n2 = (n // 2) * 2
            if n2 >= 2:
                snap = {h + d*i: 1 for i in range(n2)}
                pending[t + n2].append(('sweep', sweep_state,
                                        h + d*n2, {}, snap, t))
        if st == sweep_state:
            stats['sweep_seen'] += 1
        # --- verify predictions due now
        if t in pending:
            for kind, est, eh, w, snap, t0 in pending.pop(t):
                ok = (st == est and h == eh)
                if ok:
                    for q, v in snap.items():
                        expect = w.get(q, v)
                        if tape[q] != expect:
                            ok = False
                            break
                stats[kind] += 1
                if ok:
                    if kind == 'cat_cycle':
                        chain = chain + 1 if last_cyc_end == t0 else 1
                        last_cyc_end = t
                        max_chain = max(max_chain, chain)
                else:
                    fails.append((t0, kind, 'MISMATCH', st, est,
                                  h - OFF, eh - OFF))
        # --- raw step
        tr = tbl[(st, b)]
        if tr is None:
            fails.append((t, 'HALTED'))
            break
        wr, mv, nst = tr
        tape[h] = wr
        h += 1 if mv == 'R' else -1
        st = nst

    left = sum(len(v) for v in pending.values())
    print(f"== {name}: {N:,} raw steps")
    print(f"   cat_cycle  verified: {stats['cat_cycle']:,}  "
          f"(longest consecutive chain: {max_chain})")
    print(f"   spawn_step verified: {stats['spawn_step']:,}")
    print(f"   sweep      verified: {stats['sweep']:,} (sampled)")
    print(f"   danger-state 0-reads: {probe_reads:,} — all probe-safe: "
          f"{'YES' if not any('PROBE' in str(f) for f in fails) else 'NO'}")
    print(f"   pending past horizon (unverifiable, fine): {left}")
    if fails:
        print(f"   FAILURES ({len(fails)}):", fails[:5])
    else:
        print(f"   FAILURES: none")
    return not fails


def test_dossier2_theorems_match_raw_emulation():
    assert validate('dossier-2', D2, -1, 'C', +1, 'D', 'D', 'D', 1_000_000)

def test_dossier3_theorems_match_raw_emulation():
    assert validate('dossier-3', D3, +1, 'B', -1, 'E', 'E', 'E', 1_000_000)


# ---------------------------------------------------------------------------
# Abstract orbit (metaStep) validation: the Lean metaStep's exact python
# mirror must reproduce every raw spawn-entry snapshot after the anchor.

def meta_step_d2(three, l, h1, h2, r):
    if three:
        if l <= h1 and h1 + 4 <= h2 and h2 + 6 <= r and \
                (r - h2) % 2 == 0 and (h2 - h1) % 2 == 0:
            return (False, l, h1 + 6, h2 + 4, r + 1)
        if l <= h1 and h2 == h1 + 2 and h2 + 7 <= r and \
                (r - h2) % 2 == 0:
            return (False, l, h1 + 9, r + 1, r + 2)
        return None
    if h2 == r - 1:
        if l <= h1 and h1 <= r - 4:
            return (False, l, h1, r - 2, r + 1)
        return None
    if h2 == r - 3:
        if (r - h1) % 2 == 1:
            if l <= h1 and h1 + 7 <= r:
                return (False, l, h1 + 6, r + 1, r + 2)
            return None
        if (h1 - l) % 2 == 1:
            if l + 3 <= h1 and h1 + 6 <= r:
                return (False, l - 1, l + 5, h1 + 4, r + 1)
            return None
        if l + 5 <= h1 and h1 + 6 <= r:
            return (False, l - 3, l + 6, h1 + 4, r + 1)
        return None
    if l <= h1 and h1 + 1 <= h2 and h2 <= r - 4:
        return (True, l, h1, h2, r + 1)
    return None


def _abstract_matches_raw(code, mirror, s0, anchor_t, steps):
    tbl = parse(code)
    tape = {}
    st, h = 'A', 0
    ext = 0
    far = None
    spawn_st = 'E' if mirror else 'D'
    ms = s0
    checked = 0
    for t in range(steps):
        b = tape.get(h, 0)
        fresh = (h <= ext) if mirror else (h >= ext)
        if st == spawn_st and b == 0 and fresh and t >= anchor_t:
            three, l, h1, h2, r = ms
            assert h == r, (t, ms, h)
            holes = {h1, h2} | ({r + 3} if (mirror and three) else
                                ({r - 3} if three else set()))
            lo, hi = (r + 1, l) if mirror else (l, r - 1)
            for q in range(lo, hi + 1):
                want = 0 if q in holes else 1
                assert tape.get(q, 0) == want, (t, q, ms)
            checked += 1
            nxt = (meta_step_d2(three, -l, -h1, -h2, -r) if mirror
                   else meta_step_d2(three, l, h1, h2, r))
            assert nxt is not None, (t, ms)
            if mirror:
                nxt = (nxt[0], -nxt[1], -nxt[2], -nxt[3], -nxt[4])
            ms = nxt
        tr = tbl[(st, b)]
        wr, mv, nst = tr
        tape[h] = wr
        if wr and far is None:
            far = h
        h += 1 if mv == 'R' else -1
        st = nst
        ext = min(ext, h) if mirror else max(ext, h)
    assert checked > 100, checked
    return checked


def test_dossier2_abstract_orbit_matches_raw():
    n = _abstract_matches_raw('1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD',
                              False, (False, -8, -2, 12, 13), 235,
                              1_000_000)
    assert n > 500


def test_dossier3_abstract_orbit_matches_raw():
    n = _abstract_matches_raw('1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE',
                              True, (False, 17, 11, -39, -40), 2044,
                              1_000_000)
    assert n > 500
