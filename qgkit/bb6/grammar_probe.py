"""Generic grammar prober: is this machine caterpillar-class?

Detects recurring 'entry' configurations (state + fresh-extreme reads),
checks whether tapes at entries form a bounded-hole field family
(holeTape-like), and attempts fail-closed episode classification via
shape deltas. Output: class verdict + episode-delta alphabet.
"""
import sys
from collections import Counter


def parse(code):
    tbl = {}
    for si, block in enumerate(code.split('_')):
        for b in range(2):
            tr = block[3 * b:3 * b + 3]
            tbl[('ABCDEF'[si], b)] = None if tr == '---' else \
                (int(tr[0]), tr[1], tr[2])
    return tbl


def probe(code, steps=2_000_000, max_holes=4):
    tbl = parse(code)
    tape = {}
    st, hd = 'A', 0
    lo = hi = 0
    entries = Counter()      # (state, side) at fresh extremes
    for t in range(steps // 10):   # phase 1: find the dominant entry
        b = tape.get(hd, 0)
        if hd > hi:
            entries[(st, 'R', b)] += 1
            hi = hd
        elif hd < lo:
            entries[(st, 'L', b)] += 1
            lo = hd
        tr = tbl[(st, b)]
        if tr is None:
            return dict(verdict='HALTED', t=t)
        w, d, ns = tr
        tape[hd] = w
        hd += 1 if d == 'R' else -1
        st = ns
    if not entries:
        return dict(verdict='no-extremes')
    (est, eside, eb), _ = entries.most_common(1)[0]
    # phase 2: full run, snapshot shapes at the dominant entry
    tape = {}
    st, hd = 'A', 0
    lo = hi = 0
    far = None
    shapes = []
    for t in range(steps):
        b = tape.get(hd, 0)
        fresh = (hd > hi) if eside == 'R' else (hd < lo)
        if st == est and b == eb and fresh and t > 200:
            if far is not None:
                if eside == 'R':
                    cells = range(far, hd)
                    holes = [q for q in cells if tape.get(q, 0) == 0]
                    width = hd - far
                else:
                    cells = range(hd + 1, far + 1)
                    holes = [q for q in cells if tape.get(q, 0) == 0]
                    width = far - hd
                if len(holes) <= max_holes:
                    if eside == 'R':
                        rel = tuple(hd - q for q in holes)
                    else:
                        rel = tuple(q - hd for q in holes)
                    shapes.append((t, width, len(holes), rel))
                else:
                    shapes.append((t, width, len(holes), None))
        if hd > hi:
            hi = hd
        if hd < lo:
            lo = hd
        tr = tbl[(st, b)]
        if tr is None:
            return dict(verdict='HALTED', t=t)
        w, d, ns = tr
        tape[hd] = w
        if w and (far is None or (q_better := (hd < far if eside == 'R'
                                               else hd > far))):
            far = hd
        hd += 1 if d == 'R' else -1
        st = ns
    if len(shapes) < 50:
        return dict(verdict='few-entries', n=len(shapes))
    nh = Counter(s[2] for s in shapes)
    bounded = all(k <= max_holes for k in nh)
    # episode alphabet: deltas of (width, holecount, hole-offsets sig)
    deltas = Counter()
    for (t0, w0, h0, r0), (t1, w1, h1, r1) in zip(shapes, shapes[1:]):
        if r0 is None or r1 is None:
            deltas['UNBOUNDED'] += 1
            continue
        deltas[(w1 - w0, h0, h1, t1 - t0 if t1 - t0 < 40 else '>')] += 1
    return dict(verdict='CATERPILLAR' if bounded else 'unbounded-holes',
                entry=f"{est}/{eside}/read{eb}", n_entries=len(shapes),
                holecounts=dict(nh),
                alphabet=len(deltas),
                top=deltas.most_common(6))


if __name__ == '__main__':
    import json
    codes = json.load(open(sys.argv[1])) if len(sys.argv) > 1 else []
    for code in codes:
        r = probe(code, steps=1_000_000)
        print(code, '->', r.get('verdict'),
              {k: v for k, v in r.items()
               if k in ('entry', 'n_entries', 'holecounts', 'alphabet')})
