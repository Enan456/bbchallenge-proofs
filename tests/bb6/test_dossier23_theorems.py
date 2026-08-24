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
