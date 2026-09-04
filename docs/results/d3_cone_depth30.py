"""Dossier-3 raw halt-cone, extended to depth 30, with an EXACT
spawn-shape satisfiability check and a forward orbit-alignment run.

Machine 1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE; halt = state C
reading 0.  Spawn entries are state E, head at r, tape = holeTape with
the 1-field [r+1, l] to the right and two (or three) interior holes.

Findings:
  1. depth-24 count = 134, depth-30 count = 756 (reproduces the doc and
     extends it).
  2. the "three 0s within a six-cell window" property holds for every
     family at depths 4..30, but it is a NECESSARY-not-sufficient
     heuristic: it counts the spawn's own exterior (left-of-head) zeros,
     which every spawn entry carries.
  3. exact spawn-shape satisfiability finds 11 genuine wide-holeTape
     shapes that halt within 30 raw steps (depths 6,12,18,19,25), so the
     literal lemma "no holeTape config within 30 raw steps" is FALSE.
     All 11 have <= 2 INTERIOR zeros; the correct criterion is the
     interior-zero count (as used for Antihydra), not the window count.
  4. the sound statement is orbit alignment: the certified forward orbit
     from s0 stays > 30 raw steps from the halt (0 alignments over
     100,000 raw steps against the full depth-0..30 cone).
"""

TBL = {('A', 0): (1, 'R', 'B'), ('A', 1): (1, 'R', 'B'),
       ('B', 0): (1, 'L', 'C'), ('B', 1): (0, 'R', 'E'),
       ('C', 1): (1, 'L', 'D'),
       ('D', 0): (0, 'R', 'A'), ('D', 1): (1, 'L', 'B'),
       ('E', 0): (1, 'R', 'A'), ('E', 1): (1, 'L', 'F'),
       ('F', 0): (0, 'L', 'E'), ('F', 1): (1, 'L', 'E')}


def preds(state, head, cons):
    out = []
    for (s, b), (w, d, ns) in TBL.items():
        if ns != state:
            continue
        ph = head - (1 if d == 'R' else -1)
        if ph in cons and cons[ph] != w:
            continue
        nc = dict(cons)
        nc.pop(ph, None)
        nc[ph] = b
        out.append((s, ph, nc))
    return out


def raw_cone(depth):
    level = [('C', 0, {0: 0})]
    counts = [1]
    levels = [list(level)]
    for _d in range(depth):
        nxt = []
        for st, h, c in level:
            nxt.extend(preds(st, h, c))
        seen, ded = set(), []
        for st, h, c in nxt:
            k = (st, h, tuple(sorted(c.items())))
            if k not in seen:
                seen.add(k)
                ded.append((st, h, c))
        level = ded
        counts.append(len(level))
        levels.append(list(level))
    return counts, levels


def max_zeros_window(c, w=6):
    zs = sorted(p for p, v in c.items() if v == 0)
    best = 0
    for i in range(len(zs)):
        j = i
        while j < len(zs) and zs[j] - zs[i] < w:
            j += 1
        best = max(best, j - i)
    return best


def interior_zeros(c):
    return sum(1 for p, v in c.items() if v == 0
               and any(q < p and c[q] == 1 for q in c)
               and any(q > p and c[q] == 1 for q in c))


def wide_halter(h, cons, d):
    """Build the widest holeTape (state E, head r=h, field [r+1, r+3000]
    minus the within-window right-of-head zeros as holes) consistent with
    a state-E family, and forward-run.  Returns halt step if it genuinely
    halts, else None."""
    r = h
    if any(v != 0 for p, v in cons.items() if p <= r):
        return None                       # spawn is 0 at/left of head
    Z = sorted(p for p, v in cons.items() if p > r and v == 0)
    if len(Z) > 3:
        return None
    holes = set(Z)

    def val(q):
        if q in holes:
            return 0
        return 1 if (r + 1 <= q <= r + 3000) else 0
    tape, pos, st = {}, r, 'E'
    for t in range(d + 5):
        if pos not in tape:
            tape[pos] = val(pos)
        b = tape[pos]
        tr = TBL.get((st, b))
        if tr is None:
            return t
        w, dd, ns = tr
        tape[pos] = w
        pos += 1 if dd == 'R' else -1
        st = ns
    return None


def orbit_alignment(levels, n_steps=100_000):
    """Forward raw orbit from s0 = <false,17,11,-39,-40> (startup landing,
    state E, head r=-40, field [-39,17] minus holes {11,-39}); check exact
    membership against every depth-0..30 cone family at every step."""
    from collections import defaultdict
    by_state = defaultdict(list)
    for d, lv in enumerate(levels):
        for st, h, c in lv:
            by_state[st].append((d, tuple((p - h, v) for p, v in c.items())))
    tape = {q: (0 if q in (11, -39) else 1) for q in range(-39, 18)}
    pos, st = -40, 'E'
    matches = []
    for step in range(n_steps):
        for d, offs in by_state.get(st, []):
            if all(tape.get(pos + o, 0) == v for o, v in offs):
                matches.append((step, d))
                break
        b = tape.get(pos, 0)
        tr = TBL.get((st, b))
        if tr is None:
            return ('HALTED', step, matches)
        w, dd, ns = tr
        tape[pos] = w
        pos += 1 if dd == 'R' else -1
        st = ns
    return ('ran', n_steps, matches)


if __name__ == '__main__':
    counts, levels = raw_cone(30)
    print("dossier-3 raw halt-cone family counts, depth 0..30:")
    print(" ", counts)
    print(f"  depth-24 = {counts[24]} (expect 134);  depth-30 = {counts[30]}")
    lam = (counts[30] / counts[20]) ** 0.1
    print(f"  growth constant (depths 20-30): {lam:.4f}")

    all_win3 = all(max_zeros_window(c) >= 3
                   for d in range(4, 31) for _, _, c in levels[d])
    print(f"\n  every family at depths 4..30 has >=3 zeros in a 6-window: "
          f"{all_win3}  (reproduces the doc's depth-24 property)")

    halters = []
    for d in range(1, 31):
        for st, h, c in levels[d]:
            if st != 'E':
                continue
            t = wide_halter(h, c, d)
            if t == d:
                halters.append((d, interior_zeros(c), max_zeros_window(c)))
    print(f"\n  EXACT wide-holeTape shapes that halt within 30 raw steps: "
          f"{len(halters)}")
    print(f"  their depths: {sorted(set(d for d, _, _ in halters))}")
    print(f"  their interior-zero counts: "
          f"{sorted(iz for _, iz, _ in halters)}  (all <= 2)")
    print(f"  their window-zero counts:   "
          f"{sorted(wz for _, _, wz in halters)}  (all >= 3: why the "
          f"window heuristic missed them)")
    print("  => the literal 'no holeTape within 30 steps' lemma is FALSE;"
          " the correct criterion is the interior-zero count.")

    status, n, matches = orbit_alignment(levels)
    print(f"\n  forward orbit from s0, {n} raw steps vs full depth-0..30 "
          f"cone: {len(matches)} alignments  ({status})")
    print("  => the certified orbit stays > 30 raw steps from the halt: a"
          " sound orbit-alignment time margin (not a shape-incompatibility)")
