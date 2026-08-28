"""Dossier-5: vector grammar decoding — episodes as edits on the
run-length vector (array-class shape language, empirical layer)."""
import sys, json
sys.path.insert(0, '.')
from grammar_probe import parse
from collections import Counter


def entry_vectors(code, steps=2_000_000):
    tbl = parse(code)
    tape = {}
    st, hd = 'A', 0
    lo = hi = 0
    entries = Counter()
    for t in range(steps // 10):
        b = tape.get(hd, 0)
        if hd > hi:
            entries[(st, 'R', b)] += 1; hi = hd
        elif hd < lo:
            entries[(st, 'L', b)] += 1; lo = hd
        tr = tbl[(st, b)]
        if tr is None:
            return None, None
        w, d, ns = tr
        tape[hd] = w
        hd += 1 if d == 'R' else -1
        st = ns
    (est, eside, eb), _ = entries.most_common(1)[0]
    tape = {}
    st, hd = 'A', 0
    lo = hi = 0
    vecs = []
    for t in range(steps):
        b = tape.get(hd, 0)
        fresh = (hd > hi) if eside == 'R' else (hd < lo)
        if st == est and b == eb and fresh and t > 200:
            span = range(lo, hd) if eside == 'R' else \
                range(hd + 1, hi + 1)
            bits = [tape.get(q, 0) for q in span]
            while bits and bits[0] == 0:
                bits.pop(0)
            if eside == 'L':
                bits = bits[::-1]     # normalize: head end first
            else:
                bits = bits[::-1]
            rle = []
            for x in bits:
                if rle and rle[-1][0] == x:
                    rle[-1][1] += 1
                else:
                    rle.append([x, 1])
            vecs.append((t, tuple(tuple(r) for r in rle)))
        if hd > hi: hi = hd
        if hd < lo: lo = hd
        tr = tbl[(st, b)]
        if tr is None:
            return None, None
        w, d, ns = tr
        tape[hd] = w
        hd += 1 if d == 'R' else -1
        st = ns
    return (est, eside, eb), vecs


def edit(v0, v1):
    """Describe v0 -> v1 as (prefix kept, suffix kept, middle edit)."""
    p = 0
    while p < min(len(v0), len(v1)) and v0[p] == v1[p]:
        p += 1
    s = 0
    while s < min(len(v0), len(v1)) - p and v0[-1 - s] == v1[-1 - s]:
        s += 1
    mid0 = v0[p:len(v0) - s]
    mid1 = v1[p:len(v1) - s]
    return p, s, mid0, mid1


code = json.load(open('/tmp/cert_exact.json'))[0]
info, vecs = entry_vectors(code)
print(f"machine {code}")
print(f"entry {info}; {len(vecs)} entry vectors; dims "
      f"{[len(v) for _, v in vecs[:8]]} ... {[len(v) for _, v in vecs[-4:]]}")
print("\nfirst vectors (head end first):")
for t, v in vecs[:4]:
    print(f"  t={t}: {v}")
print("\nedit alphabet between consecutive entries:")
alpha = Counter()
examples = {}
for (t0, v0), (t1, v1) in zip(vecs, vecs[1:]):
    p, s, m0, m1 = edit(v0, v1)
    # abstract the edit: shapes of the replaced middles (bits + how
    # many runs), keeping lengths symbolic
    sig = (tuple(b for b, _ in m0), tuple(b for b, _ in m1),
           len(v1) - len(v0))
    alpha[sig] += 1
    if sig not in examples:
        examples[sig] = (v0, v1, p, s)
print(f"  distinct edit signatures: {len(alpha)}")
for sig, n in alpha.most_common(10):
    print(f"  x{n:>4}  mid {sig[0]} -> {sig[1]}  (dim {sig[2]:+d})")
