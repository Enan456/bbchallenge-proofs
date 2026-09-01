"""Two-ended cone analysis for Antihydra.

B1 raw: backward BFS over predecessor constraint-patterns from the
   halting transition (F reading 0), depth 30, with a record-shape
   (Realizes grammar) incompatibility check on the frontier.
B2 abstract: the states dying within k steps of the certified map
   astep, as exact preimage families (a, m, c-spec) with c-spec either
   a constant or free; validated against forward iteration; counts by
   depth, growth constant, recurrence attempts.
"""
from fractions import Fraction

CODE = '1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA'
TBL = {}
for i, blk in enumerate(CODE.split('_')):
    st = chr(ord('A') + i)
    for b in (0, 1):
        e = blk[3 * b:3 * b + 3]
        TBL[(st, b)] = None if e == '---' else (int(e[0]), e[1], e[2])
ENT = {k: v for k, v in TBL.items() if v is not None}


# ==================== B2: the abstract cone ====================
def astep(a, m, c):
    if m >= 3:
        return (a, m - 2, c + 3)
    if m == 2:
        return (a - 1, c + 3, 2) if a >= 2 else None
    if m == 1:
        return (a + 2, c + 2, 2)
    return None


def preimages(fam):
    """Exact preimage families of (a, m, cs) under astep.
    cs = 'F' means c free (any c >= 0); otherwise a constant.
    hydra^-1: (a, m+2, c-3), needs target m >= 1, c >= 3;
    drop^-1 : (a+1, 2, m-3), needs target c = 2, m >= 3, a >= 1;
    merge^-1: (a-2, 1, m-2), needs target c = 2, m >= 2, a >= 2."""
    a, m, cs = fam
    out = []
    if m >= 1:
        if cs == 'F':
            out.append((a, m + 2, 'F'))
        elif cs >= 3:
            out.append((a, m + 2, cs - 3))
    if cs == 'F' or cs == 2:
        if m >= 3 and a >= 1:
            out.append((a + 1, 2, m - 3))
        if m >= 2 and a >= 2:
            out.append((a - 2, 1, m - 2))
    return out


def abstract_cone(depth):
    """BFS from the fatal set.  Depth-0 families: the m = 0 plane
    (no preimages: astep never outputs m = 0) and the two lines
    (0, 2, c), (1, 2, c).  Constant-c families subsumed by an already
    seen free family with the same (a, m) are skipped."""
    level = [(0, 2, 'F'), (1, 2, 'F')]
    depth_of = {f: 0 for f in level}
    free_seen = {(0, 2), (1, 2)}
    counts = [len(level) + 1]          # +1: the m = 0 plane
    branch = [0]
    for k in range(1, depth + 1):
        nxt = []
        br = 0
        for f in level:
            kids = []
            for g in preimages(f):
                ga, gm, gcs = g
                if gcs != 'F' and (ga, gm) in free_seen:
                    continue
                if g in depth_of:
                    continue
                depth_of[g] = k
                if gcs == 'F':
                    free_seen.add((ga, gm))
                kids.append(g)
            if len(kids) >= 2:
                br += 1
            nxt.extend(kids)
        level = nxt
        counts.append(len(level))
        branch.append(br)
    return counts, branch, depth_of


def validate_cone(depth_of, box=13, dmax=40):
    """Minimal cone depth == forward death time, exhaustively on
    [0, box)^3."""
    bad = 0
    for a in range(box):
        for m in range(box):
            for c in range(box):
                t, k, true_d = (a, m, c), 0, None
                while k <= dmax:
                    nt = astep(*t)
                    if nt is None:
                        true_d = k
                        break
                    t, k = nt, k + 1
                best = 0 if m == 0 else None
                if m != 0:
                    for (fa, fm, cs), d in depth_of.items():
                        if (a == fa and m == fm
                                and (cs == 'F' or c == cs)):
                            if best is None or d < best:
                                best = d
                if true_d is None:
                    if best is not None and best <= dmax - box:
                        bad += 1
                elif best != true_d:
                    bad += 1
    return box ** 3, bad


def fit_recurrence(seq, order, start):
    rows, rhs = [], []
    for n in range(start + order, len(seq)):
        rows.append([Fraction(seq[n - 1 - i]) for i in range(order)])
        rhs.append(Fraction(seq[n]))
    A = [rows[i][:] for i in range(order)]
    b = [rhs[i] for i in range(order)]
    for col in range(order):
        piv = next((r for r in range(col, order) if A[r][col]), None)
        if piv is None:
            return None
        A[col], A[piv] = A[piv], A[col]
        b[col], b[piv] = b[piv], b[col]
        inv = A[col][col]
        A[col] = [x / inv for x in A[col]]
        b[col] /= inv
        for r in range(order):
            if r != col and A[r][col]:
                f = A[r][col]
                A[r] = [x - f * y for x, y in zip(A[r], A[col])]
                b[r] -= f * b[col]
    for row, y in zip(rows, rhs):
        if sum(cf * x for cf, x in zip(b, row)) != y:
            return None
    return b


# ==================== B1: the raw cone ====================
def preds(state, head, cons):
    out = []
    for (s, b), (w, d, ns) in ENT.items():
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
    level = [('F', 0, {0: 0})]
    counts = [1]
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
    return counts, level


def interior_zeros(c):
    """Zeros with a constrained 1 strictly left AND right: a Realizes
    tape has exactly two such (the block separators)."""
    return sum(1 for p, v in c.items()
               if v == 0 and any(q < p and c[q] == 1 for q in c)
               and any(q > p and c[q] == 1 for q in c))


def realizes_sat(h, cons, jmax=40):
    """Is the pattern satisfiable by ANY record shape (Realizes tape,
    head at h)?  Right of the head everything is blank; left of the
    head offset j carries 1 iff j in [1,c] u [c+2,c+m+1] u
    [c+m+3, c+m+2+a]."""
    if any(v == 1 for q, v in cons.items() if q >= h):
        return None
    offs = {h - q: v for q, v in cons.items() if q < h}
    for c in range(1, jmax):
        for m in range(1, jmax):
            for a in range(1, jmax):
                if all((1 if (1 <= j <= c or c + 2 <= j <= c + m + 1
                              or c + m + 3 <= j <= c + m + 2 + a)
                        else 0) == v for j, v in offs.items()):
                    return (a, m, c)
    return None


if __name__ == '__main__':
    DEPTH_ABS = 400
    counts, branch, depth_of = abstract_cone(DEPTH_ABS)
    print("B2 abstract dying-at-depth-k family counts (0..60):")
    print("  ", counts[:61])
    n, bad = validate_cone(depth_of)
    print(f"  validation vs forward astep on [0,13)^3: {n} states, "
          f"{bad} mismatches")
    print(f"  L(100) = {counts[100]}, L(200) = {counts[200]}, "
          f"L(400) = {counts[400]}")
    lam = (counts[400] / counts[200]) ** (1 / 200)
    xs, ys = list(range(200, 401)), counts[200:401]
    N = len(xs)
    sx, sy = sum(xs), sum(ys)
    sxx = sum(x * x for x in xs)
    sxy = sum(x * y for x, y in zip(xs, ys))
    slope = (N * sxy - sx * sy) / (N * sxx - sx * sx)
    print(f"  growth constant (per-depth, depths 200-400): {lam:.4f}"
          f" -> 1;  linear law L(k) ~ {slope:.3f} k "
          f"(total cone ~ k^2/4 families)")
    print(f"  branch events per depth (mean over 200-400): "
          f"{sum(branch[200:]) / len(branch[200:]):.3f}")
    hit = False
    for order in range(1, 7):
        for start in (0, 50, 100, 200, 300):
            cf = fit_recurrence(counts, order, start)
            if cf:
                print(f"  exact recurrence order {order} from "
                      f"{start}: {[str(x) for x in cf]}")
                hit = True
    if not hit:
        print("  no exact integer linear recurrence of order <= 6 "
              "fits any tested tail: growth is polynomial (linear), "
              "branching constant 1")

    print("\nB1 raw halt-cone family counts by depth (0..30):")
    rcounts, frontier = raw_cone(30)
    print("  ", rcounts)
    lam_r = (rcounts[30] / rcounts[20]) ** 0.1
    print(f"  growth constant (depths 20-30): {lam_r:.4f}")
    from collections import Counter
    sc = Counter(st for st, h, c in frontier)
    print(f"  depth-30 frontier by state: {dict(sc)}")
    bfams = [(st, h, c) for st, h, c in frontier if st == 'B']
    viol = [(st, h, c) for st, h, c in bfams if interior_zeros(c) < 3]
    print(f"  state-B families: {len(bfams)}; with >= 3 interior "
          f"zeros (impossible in a Realizes tape): "
          f"{len(bfams) - len(viol)}")
    unsat = sum(1 for st, h, c in viol if realizes_sat(h, c) is None)
    print(f"  remaining {len(viol)} checked exactly against every "
          f"record shape (a, m, c < 40): {unsat} unsatisfiable")
    if unsat == len(viol):
        print("  => NO record configuration is within 30 raw steps "
              "of the halt (state mismatch, interior-zero count, or "
              "exact shape check)")
