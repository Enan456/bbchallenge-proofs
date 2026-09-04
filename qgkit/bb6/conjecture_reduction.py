#!/usr/bin/env python3
"""conjecture_reduction.py -- structural reduction analysis of the 115
kernel-checked CONDITIONAL non-halting closures.

Question: the program treats the cohort as 115 independent "Safe...Orbit"
conjectures.  How many are genuinely INDEPENDENT, versus the same
generalized-Collatz map up to (a) exact state relabeling, (b) the BB
mirror (L<->R reversal + relabel), or (c) a single-transition skeleton
variant (same 11 transitions, only the fatal/probe cell changed)?

This script computes, with no hand-transcribed data:
  1. TM codes for all 115 closures, read straight from the Lean
     Dossier*RawTM / Rank1 / Dvisetu / Antihydra sources.
  2. Audit growth descriptors joined by code (sidedness, record_side,
     probe_kind, l_nstate, r_nstate, max_gap, word_len_at_max).
  3. EXACT equivalence classes under state relabeling (perm fixing the
     blank-start state A) and under the mirror transform.  These are
     rigorous graph-isomorphism-style facts, not heuristics.
  4. Single-transition "skeleton family" connected components (Hamming
     distance <= 1 over the 12 transition cells) -- strong structural
     evidence of a shared growth map with a moved fatal probe.
  5. The branching-constant census and a state-geometry cross-tab.

HONESTY: only (3) equivalence/mirror is a proof of equal dynamics.
Skeleton clustering (4) and growth-signature grouping are HEURISTIC
structural evidence that machines share a generalized-Collatz map; they
are NOT proofs that the Safe...Orbit conjectures are inter-reducible.
The known exact reductions are the proven d2/d3 mirror pair and the
per-family named siblings; everything else is measurement.
"""
import json
import glob
import os
import re
import itertools
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CORE = os.path.join(ROOT, 'busy-beaver-core', 'BusyBeaverCore')
AUDIT = os.path.join(ROOT, 'experiments', 'outputs', 'audit_openset.jsonl')

STATES = 'ABCDEF'

# Named machines whose closure conjecture is NOT SafeD<n>Orbit.
NAMED_FILES = {
    'Dossier1RawTM.lean': ('d1', 'Cohomo'),
    'Dossier2RawTM.lean': ('d2', 'Piasa'),
    'Dossier3RawTM.lean': ('d3', 'Grafton Piasa'),
    'Rank1RawTM.lean': ('d5', 'Big Muddy'),
    'DvisetuRawTM.lean': ('d6', 'Dvisetu'),
    'AntihydraRawTM.lean': ('ah', 'Antihydra'),
}

# Illinois-bestiary names for the low dossiers (docs/submissions/cryptid-names.md).
BESTIARY = {
    7: 'Kaskaskia', 8: 'Cahokia', 9: 'Enfield', 10: 'Farmer City',
    11: 'Cairo', 12: 'Mad Gasser', 13: 'Lawndale', 14: 'Mazon Tully',
    15: 'Braidwood Tully', 16: 'Coal City Tully', 17: 'Pit Eleven Tully',
    18: 'Essex Tully',
}

# Known EXACT branching / growth constants from the closure write-ups
# (docs/submissions/cryptid-names.md, campaign-consolidation).  These are
# derived from proven laws, not from the audit proxy.
KNOWN_CONST = {
    'd2': ('phi (golden ratio)', 'Fibonacci death-cone, no-TT constraint'),
    'd3': ('phi (golden ratio)', 'mirror of d2'),
    'd6': ('4/3 per cycle', 'n mod 3 renewal, divide-by-3 recursion'),
    'd7': ('~3/2 per renewal', 'unary ladder (10)^k, drift+reload'),
    'd8': ('~3/2 per renewal', 'unary ladder, extra epoch counter g'),
    'd5': ('2-adic (train lengths)', 'rank-1 trisection word odometer'),
    'ah': ('1 (linear cone)', 'guarded random walk, a>=2 merge throttle'),
}


def parse_code(code):
    """code 'aRb...' -> dict[(state,bit)] = (write,dir,next) or None."""
    tbl = {}
    for si, block in enumerate(code.split('_')):
        for b in range(2):
            tr = block[3 * b:3 * b + 3]
            tbl[(STATES[si], b)] = None if tr == '---' else (tr[0], tr[1], tr[2])
    return tbl


def load_codes():
    """Read every closure's TM code straight from its Lean source."""
    machs = {}  # key -> dict(name, code, dossier, kind)
    for lf in sorted(glob.glob(os.path.join(CORE, 'Dossier*RawTM.lean'))):
        base = os.path.basename(lf)
        n = int(re.search(r'Dossier(\d+)RawTM', base).group(1))
        txt = open(lf).read()
        m = re.search(r'1RB[0-9A-Z_-]{20,}', txt)
        if not m:
            continue
        code = m.group(0)
        if base in NAMED_FILES:
            key, name = NAMED_FILES[base]
        else:
            key, name = f'd{n}(D{n})', BESTIARY.get(n, f'D{n}')
        machs[key] = dict(name=name, code=code, dossier=n, conj=f'SafeD{n}Orbit')
    for base, (key, name) in NAMED_FILES.items():
        if base in ('Rank1RawTM.lean', 'DvisetuRawTM.lean', 'AntihydraRawTM.lean'):
            txt = open(os.path.join(CORE, base)).read()
            code = re.search(r'1RB[0-9A-Z_-]{20,}', txt).group(0)
            machs[key] = dict(name=name, code=code, dossier=None, conj=key)
    return machs


def load_audit():
    a = {}
    with open(AUDIT) as f:
        for line in f:
            d = json.loads(line)
            a[d['code']] = d
    return a


# ---------- exact equivalence: state relabeling & mirror ----------

def relabel(code, perm):
    """Apply state permutation perm (dict old->new, must fix 'A').
    Returns the canonical string of the relabeled table."""
    tbl = parse_code(code)
    new = {}
    for (st, b), tr in tbl.items():
        ns = perm[st]
        if tr is None:
            new[(ns, b)] = '---'
        else:
            w, d, nx = tr
            new[(ns, b)] = w + d + perm[nx]
    blocks = []
    for s in STATES:
        blocks.append(new.get((s, 0), '---') + new.get((s, 1), '---'))
    return '_'.join(blocks)


def canonical(code):
    """Lex-min over all state perms fixing A. Two codes share a canonical
    form iff they are identical up to relabeling states other than the
    blank-start state A."""
    best = None
    others = [s for s in STATES if s != 'A']
    for pr in itertools.permutations(others):
        perm = {'A': 'A'}
        perm.update(dict(zip(others, pr)))
        c = relabel(code, perm)
        if best is None or c < best:
            best = c
    return best


def mirror_code(code):
    """BB mirror: swap L<->R in every transition direction. (State
    relabeling is then absorbed by canonical().)"""
    tbl = parse_code(code)
    blocks = []
    for s in STATES:
        cells = []
        for b in range(2):
            tr = tbl[(s, b)]
            if tr is None:
                cells.append('---')
            else:
                w, d, nx = tr
                cells.append(w + ('L' if d == 'R' else 'R') + nx)
        blocks.append(''.join(cells))
    return '_'.join(blocks)


def cell_vector(code):
    """12 transition cells (6 states x 2 bits) as a tuple of 3-char strs."""
    tbl = parse_code(code)
    return tuple(
        ('---' if tbl[(s, b)] is None else ''.join(tbl[(s, b)]))
        for s in STATES for b in range(2)
    )


def hamming(u, v):
    return sum(1 for a, b in zip(u, v) if a != b)


def components(keys, adj):
    seen, comps = set(), []
    for k in keys:
        if k in seen:
            continue
        stack, comp = [k], []
        seen.add(k)
        while stack:
            x = stack.pop()
            comp.append(x)
            for y in adj[x]:
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        comps.append(sorted(comp))
    return comps


def main():
    machs = load_codes()
    audit = load_audit()
    keys = list(machs.keys())
    print(f"# closures loaded: {len(keys)}")

    # join audit
    joined = 0
    for k, m in machs.items():
        d = audit.get(m['code'])
        m['audit'] = d
        if d:
            joined += 1
    print(f"# audit-joined by exact code: {joined}/{len(keys)}")

    # ---- exact equivalence classes (relabeling) ----
    canon = {k: canonical(machs[k]['code']) for k in keys}
    by_canon = defaultdict(list)
    for k in keys:
        by_canon[canon[k]].append(k)
    iso_classes = [v for v in by_canon.values() if len(v) > 1]
    print("\n## EXACT state-relabeling equivalence classes (proof of identical dynamics)")
    if iso_classes:
        for cls in iso_classes:
            print("  ", [machs[k]['name'] for k in cls])
    else:
        print("   none (all 115 are distinct up to state relabeling)")

    # ---- mirror pairs ----
    mcanon = {k: canonical(mirror_code(machs[k]['code'])) for k in keys}
    mirror_pairs = []
    ks = keys
    for i in range(len(ks)):
        for j in range(i + 1, len(ks)):
            if canon[ks[i]] == mcanon[ks[j]] or canon[ks[j]] == mcanon[ks[i]]:
                mirror_pairs.append((ks[i], ks[j]))
    print("\n## EXACT mirror pairs (L<->R reversal + relabel; proof of mirrored dynamics)")
    if mirror_pairs:
        for a, b in mirror_pairs:
            print(f"   {machs[a]['name']} <-> {machs[b]['name']}  ({machs[a]['code']} | {machs[b]['code']})")
    else:
        print("   none detected by canonical mirror form")

    # ---- single-transition skeleton families (Hamming<=1) ----
    vecs = {k: cell_vector(machs[k]['code']) for k in keys}
    adj = defaultdict(set)
    for i in range(len(ks)):
        for j in range(i + 1, len(ks)):
            if hamming(vecs[ks[i]], vecs[ks[j]]) <= 1:
                adj[ks[i]].add(ks[j])
                adj[ks[j]].add(ks[i])
    comps1 = components(ks, adj)
    fam1 = sorted([c for c in comps1 if len(c) > 1], key=len, reverse=True)
    print(f"\n## Single-transition skeleton families (Hamming<=1 over 12 cells): "
          f"{len(comps1)} components, {len(fam1)} multi-member")
    for c in fam1:
        doss = sorted(machs[k]['dossier'] or -1 for k in c)
        print(f"   size {len(c):2d}: dossiers {doss}")

    # ---- looser skeleton (Hamming<=2) ----
    adj2 = defaultdict(set)
    for i in range(len(ks)):
        for j in range(i + 1, len(ks)):
            if hamming(vecs[ks[i]], vecs[ks[j]]) <= 2:
                adj2[ks[i]].add(ks[j])
                adj2[ks[j]].add(ks[i])
    comps2 = components(ks, adj2)
    fam2 = sorted([c for c in comps2 if len(c) > 1], key=len, reverse=True)
    print(f"\n## Looser skeleton families (Hamming<=2): {len(comps2)} components, "
          f"largest sizes {[len(c) for c in fam2[:8]]}")

    # ---- root count under the union of exact + Hamming<=1 relations ----
    # Merge iso classes and mirror pairs into the Hamming<=1 adjacency, then
    # recount components => an UPPER-BOUND-flavoured 'structural root' count.
    for cls in iso_classes:
        for x in cls[1:]:
            adj[cls[0]].add(x)
            adj[x].add(cls[0])
    for a, b in mirror_pairs:
        adj[a].add(b)
        adj[b].add(a)
    roots1 = components(ks, adj)
    print(f"\n## STRUCTURAL ROOT COUNT")
    print(f"   under exact-equiv + mirror + single-transition variant: "
          f"{len(roots1)} components  (from {len(keys)} conjectures)")
    # same but with Hamming<=2 merged
    for cls in iso_classes:
        for x in cls[1:]:
            adj2[cls[0]].add(x); adj2[x].add(cls[0])
    for a, b in mirror_pairs:
        adj2[a].add(b); adj2[b].add(a)
    roots2 = components(ks, adj2)
    print(f"   under exact-equiv + mirror + Hamming<=2 variant:        "
          f"{len(roots2)} components")

    # ---- branching-constant census + geometry cross-tab ----
    print("\n## Branching-constant census (KNOWN exact constants)")
    for k, (c, why) in KNOWN_CONST.items():
        m = machs.get(k)
        g = ''
        if m and m.get('audit'):
            a = m['audit']
            g = f" | audit: {a.get('sidedness')}, probe={a.get('probe_kind')}, l/r_nstate={a.get('l_nstate')}/{a.get('r_nstate')}"
        print(f"   {k:4s} {c:24s} {why}{g}")

    print("\n## State-geometry distribution across joined cohort (audit)")
    geo = Counter()
    ratios = []
    for k, m in machs.items():
        a = m.get('audit')
        if not a:
            continue
        geo[(a.get('sidedness'), a.get('record_side'), a.get('probe_kind'))] += 1
        if a.get('max_gap') and a.get('word_len_at_max'):
            ratios.append((k, a['max_gap'] / a['word_len_at_max'],
                           a.get('l_nstate'), a.get('r_nstate'),
                           a.get('sidedness')))
    for key, c in geo.most_common():
        print(f"   {key}: {c}")

    print("\n## gap/word-length proxy ratio (NOT the branching constant; a growth proxy)")
    ratios.sort(key=lambda t: t[1])
    print(f"   n={len(ratios)}, min={ratios[0][1]:.2f} ({ratios[0][0]}), "
          f"max={ratios[-1][1]:.2f} ({ratios[-1][0]})")
    # is state-geometry associated with the proxy ratio? group means
    import statistics
    bysided = defaultdict(list)
    for k, r, ln, rn, sd in ratios:
        bysided[sd].append(r)
    print("   mean proxy ratio by sidedness:")
    for sd, rs in sorted(bysided.items()):
        print(f"     {sd:12s} n={len(rs):3d} mean={statistics.mean(rs):8.1f} "
              f"median={statistics.median(rs):8.1f}")

    return dict(n=len(keys), joined=joined, iso=iso_classes,
                mirror=mirror_pairs, fam1=fam1, fam2=fam2,
                roots1=len(roots1), roots2=len(roots2))


if __name__ == '__main__':
    main()
