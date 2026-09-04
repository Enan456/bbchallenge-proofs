"""B2 abstract dying-at-k line-family enumeration for dossier-3,
extended far beyond depth 12. Pure combinatorics: preimages of the
fatal set under the verified renewal map R. No metastep_check needed.
"""

class F:
    __slots__ = ('A0', 'A1', 'B0', 'B1')

    def __init__(self, A0, A1, B0, B1):
        self.A0, self.A1, self.B0, self.B1 = A0, A1, B0, B1

    def key(self):
        return (self.A0, self.A1, self.B0, self.B1)


def sub_param(f, mult, off):
    return F(f.A0 + f.A1 * off, f.A1 * mult,
             f.B0 + f.B1 * off, f.B1 * mult)


def with_parity(f, which, want):
    C0, C1 = (f.A0, f.A1) if which == 'a' else (f.B0, f.B1)
    out = []
    for off in (0, 1):
        if (C0 + C1 * off) % 2 == want and (C1 * 2) % 2 == 0:
            out.append(sub_param(f, 2, off))
    if C1 % 2 == 0:
        return out[:1] if out and (C0 % 2 == want) else \
            ([sub_param(f, 1, 0)] if C0 % 2 == want else [])
    return out


def positive_part(f):
    if f.A1 < 0 and f.A0 < 1:
        return None
    if f.B1 < 0 and f.B0 < 1:
        return None
    return f


def preimages(f):
    out = []
    g = F(f.A0 - 6, f.A1, f.B0 + 3, f.B1)
    out.extend(with_parity(g, 'b', 0))
    for alpha, aoff, parity_a in ((6, 1, 1), (9, 2, 0)):
        for br in ('C', 'Fu'):
            need = alpha % 3 if br == 'C' else (alpha + 3) % 3
            cands = []
            if f.A1 % 3 == 0:
                if f.A0 % 3 == need:
                    cands.append(sub_param(f, 1, 0))
            else:
                for off in (0, 1, 2):
                    if (f.A0 + f.A1 * off) % 3 == need:
                        cands.append(sub_param(f, 3, off))
            for h in cands:
                if br == 'C':
                    dA0, dA1 = (h.A0 - alpha) // 3, h.A1 // 3
                    b0, b1 = dA0 + 3, dA1
                    beta0, beta1 = h.B0 + dA0, h.B1 + dA1
                    a0, a1 = beta0 + aoff, beta1
                else:
                    beta0, beta1 = (h.A0 - alpha - 3) // 3, h.A1 // 3
                    b0, b1 = h.B0 + beta0 + 4, h.B1 + beta1
                    a0, a1 = beta0 + aoff, beta1
                g2 = F(a0, a1, b0, b1)
                for g3 in with_parity(g2, 'b', 1):
                    for g4 in with_parity(g3, 'a', parity_a):
                        if positive_part(g4):
                            out.append(g4)
    return out


fatal_fams = [F(1, 1, 1, 0), F(1, 1, 2, 0), F(1, 1, 4, 0)]
for d in (0, 2, 4):
    fatal_fams.append(F(1, 2, 1 + d, 2))
for d in (-1, 1, 3):
    fatal_fams.append(F(2, 2, 2 + d + 0, 2))

import sys, time
MAXDEPTH = int(sys.argv[1]) if len(sys.argv) > 1 else 32
level = fatal_fams
counts = [len(level)]
first_violation = None
t0 = time.time()
print(f"{0:5d} : {counts[0]:10d} :          - : -", flush=True)
for k in range(1, MAXDEPTH + 1):
    nxt = []
    seen = set()
    add = seen.add
    for f in level:
        for g in preimages(f):
            gk = g.key()
            if gk not in seen:
                add(gk)
                nxt.append(g)
    level = nxt
    c = len(level)
    counts.append(c)
    pred = counts[k - 1] + counts[k - 2] if k >= 2 else None
    match = (pred == c) if pred is not None else None
    if match is False and first_violation is None:
        first_violation = k
    print(f"{k:5d} : {c:10d} : {str(pred):>10} : {match}"
          f"   [{time.time()-t0:6.1f}s]", flush=True)

print()
print("counts =", counts, flush=True)
print("first Fibonacci violation at depth:", first_violation, flush=True)

# growth ratios
print("\nmeasured growth ratios c[k]/c[k-1] (tail):")
for k in range(MAXDEPTH - 5, MAXDEPTH + 1):
    if counts[k - 1]:
        print(f"  {k}: {counts[k] / counts[k - 1]:.12f}")
phi = (1 + 5 ** 0.5) / 2
print("phi =", f"{phi:.12f}")
