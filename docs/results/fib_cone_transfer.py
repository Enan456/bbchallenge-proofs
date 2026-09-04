"""Derive the transfer matrix of the dossier-3 abstract cone.

Tag each preimage by the branch that produced it:
  T  = terminate inverse (even-b branch of R: (a,b)->(a+6,b-3))
  N  = non-terminate inverse (odd-b branch: C-inverse / Fu-inverse)

Track family type through the levels and measure, per parent type,
how many T-children and N-children it emits. This is the transfer
matrix. Test the 'no TT' claim: T-parents emit zero T-children.
"""

class F:
    __slots__ = ('A0', 'A1', 'B0', 'B1')
    def __init__(s, A0, A1, B0, B1):
        s.A0, s.A1, s.B0, s.B1 = A0, A1, B0, B1
    def key(s):
        return (s.A0, s.A1, s.B0, s.B1)


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


def preimages_tagged(f):
    """return list of (child, branch_type) with branch_type in {'T','N'}"""
    out = []
    g = F(f.A0 - 6, f.A1, f.B0 + 3, f.B1)
    for c in with_parity(g, 'b', 0):
        out.append((c, 'T'))
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
                            out.append((g4, 'N'))
    return out


fatal_fams = [F(1, 1, 1, 0), F(1, 1, 2, 0), F(1, 1, 4, 0)]
for d in (0, 2, 4):
    fatal_fams.append(F(1, 2, 1 + d, 2))
for d in (-1, 1, 3):
    fatal_fams.append(F(2, 2, 2 + d + 0, 2))

MAXDEPTH = 18
# level entries: (family, parent_type) ; seed type = 'N' (root, treat as N)
level = [(f, 'N') for f in fatal_fams]

# aggregate transfer counts across all depths (after global dedup per depth)
# tt[(ptype)] -> Counter of child types
from collections import Counter
global_transfer = {'T': Counter(), 'N': Counter()}
# also per-parent branching to check uniformity
branch_samples = {'T': [], 'N': []}

levelTN = [(sum(1 for _, t in level if t == 'T'),
            sum(1 for _, t in level if t == 'N'))]
for k in range(1, MAXDEPTH + 1):
    nxt = []
    seen = set()
    for (f, ptype) in level:
        kids = preimages_tagged(f)
        cT = sum(1 for _, t in kids if t == 'T')
        cN = sum(1 for _, t in kids if t == 'N')
        branch_samples[ptype].append((cT, cN))
        for (g, ctype) in kids:
            gk = g.key()
            if gk not in seen:
                seen.add(gk)
                nxt.append((g, ctype))
                global_transfer[ptype][ctype] += 1
    level = nxt
    levelTN.append((sum(1 for _, t in level if t == 'T'),
                    sum(1 for _, t in level if t == 'N')))

print("Per-level type counts and exact matrix-relation check")
print("k :   T_k :   N_k :  L_k : [T_k==N_{k-1}] [N_k==T_{k-1}+N_{k-1}]")
for k in range(len(levelTN)):
    T, N = levelTN[k]
    L = T + N
    if k >= 1:
        Tp, Np = levelTN[k - 1]
        c1 = (T == Np)
        c2 = (N == Tp + Np)
        print(f"{k:2d} : {T:6d} : {N:6d} : {L:6d} :  {c1}  {c2}")
    else:
        print(f"{k:2d} : {T:6d} : {N:6d} : {L:6d} :  seed")
print()

print("Per-parent-type branching (over the dedup'd tree, all depths 1..%d):" % MAXDEPTH)
for pt in ('T', 'N'):
    tot_parents = len(branch_samples[pt])
    if tot_parents == 0:
        print(f"  parent {pt}: no instances")
        continue
    sumT = sum(cT for cT, cN in branch_samples[pt])
    sumN = sum(cN for cT, cN in branch_samples[pt])
    distinctT = sorted(set(cT for cT, cN in branch_samples[pt]))
    distinctN = sorted(set(cN for cT, cN in branch_samples[pt]))
    print(f"  parent {pt}: {tot_parents} instances; "
          f"avg T-children={sumT/tot_parents:.4f} (values {distinctT}); "
          f"avg N-children={sumN/tot_parents:.4f} (values {distinctN})")

print("\nGlobal deduped transfer (edges kept after per-depth dedup):")
for pt in ('T', 'N'):
    print(f"  from {pt}: {dict(global_transfer[pt])}")
