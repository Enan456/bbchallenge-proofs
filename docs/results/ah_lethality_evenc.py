"""Antihydra even-c resolution: the raw fate of materialize(1, 2, c).

The abstract map astep gives astep(1, 2, c) = none (a drop with a = 1,
below the grammar floor a >= 2).  This is loss of certification, not a
raw halt.  Run on the raw machine, the tape 1^1 0 1^2 0 1^c does one of
two things by the parity of c:

  odd c : the a = 1 block runs into the undefined transition (state F
          reading 0).  Genuine halt, in exactly (3c^2 + 44c + 125)/4
          raw steps, with no grammar re-entry.
  even c: the a = 1 block folds and the raw machine re-materializes the
          LIVE grammar state (2, (3c + 14)/2, 2), a survivor-eligible
          seed.  From there the raw orbit is an ordinary Antihydra
          orbit; it genuinely halts only if that orbit later reaches a
          state (1, 2, c') with c' ODD.  Each (1, 2, even) boundary it
          crosses is itself another re-entry, not a halt.

This script reproduces the re-entry formula, the true-fate fold, and the
validation of the fold against direct raw simulation.
"""

CODE = '1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA'


def parse(code):
    tbl = {}
    for i, blk in enumerate(code.split('_')):
        st = chr(ord('A') + i)
        for b in (0, 1):
            e = blk[3 * b:3 * b + 3]
            tbl[(st, b)] = None if e == '---' else (int(e[0]), e[1], e[2])
    return tbl


TBL = parse(CODE)


def astep(a, m, c):
    if m >= 3:
        return (a, m - 2, c + 3)
    if m == 2:
        return (a - 1, c + 3, 2) if a >= 2 else None
    if m == 1:
        return (a + 2, c + 2, 2)
    return None


def materialize(s, p=0):
    a, m, c = s
    tape = {}
    for i in range(a):
        tape[p - i] = 1
    for i in range(m):
        tape[p + 2 + i] = 1
    for i in range(c):
        tape[p + 3 + m + i] = 1
    return tape, p + 3 + m + c, 'B'


def raw_run(s, ms):
    tape, pos, st = materialize(s)
    for t in range(ms):
        b = tape.get(pos, 0)
        tr = TBL[(st, b)]
        if tr is None:
            return t
        w, d, ns = tr
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        st = ns
    return None


def reparse(s, ms):
    """Run the materialized state raw; return the first LIVE grammar
    re-entry (state B, head on a fresh frontier, tape 1^a 0 1^m 0 1^c)."""
    tape, pos, st = materialize(s)
    for t in range(ms):
        b = tape.get(pos, 0)
        tr = TBL[(st, b)]
        if tr is None:
            return ('halt', t, None)
        w, d, ns = tr
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        st = ns
        if st == 'B':
            rp = _grammar(tape, pos)
            if rp is not None:
                return ('reentry', t + 1, rp)
    return ('escape', ms, None)


def _grammar(tape, pos):
    if any(q >= pos and v == 1 for q, v in tape.items()):
        return None
    qs = [q for q, v in tape.items() if v == 1]
    if not qs:
        return None
    bits = {pos - q: tape.get(q, 0) for q in range(min(qs), pos)}

    def run1(j):
        n = 0
        while bits.get(j, 0) == 1:
            n += 1
            j += 1
        return n, j
    c, j = run1(1)
    if bits.get(j, 0) != 0:
        return None
    j += 1
    m, j = run1(j)
    if m == 0 or bits.get(j, 0) != 0:
        return None
    j += 1
    a, j = run1(j)
    if a == 0:
        return None
    if any(bits.get(k, 0) == 1 for k in range(j, max(bits) + 1)):
        return None
    return (a, m, c)


def true_fate(seed, K):
    """True raw fate via re-entry fold: (1,2,odd) = genuine halt,
    (1,2,even) = re-enter (2,(3c+14)/2,2)."""
    a, m, c = seed
    reentries = 0
    for i in range(K):
        if a == 1 and m == 2:
            if c % 2 == 1:
                return ('genuine-halt', i, reentries, c)
            a, m, c = 2, (3 * c + 14) // 2, 2
            reentries += 1
            continue
        ns = astep(a, m, c)
        if ns is None:
            return ('other-death', i, reentries, (a, m, c))
        a, m, c = ns
    return ('survives', K, reentries, (a, m, c))


if __name__ == '__main__':
    print("== even-c re-entry: materialize(1,2,c) re-materializes a "
          "LIVE state (2,(3c+14)/2,2) ==")
    for c in (2, 4, 6, 8, 10):
        kind, step, rp = reparse((1, 2, c), 2000)
        pred = (2, (3 * c + 14) // 2, 2)
        print(f"  c={c:3d}: first re-entry {rp} at raw step {step}; "
              f"formula (2,(3c+14)/2,2)={pred}  match={rp == pred}")

    print("\n== true raw fate (fold: odd boundary = halt, even = re-enter) ==")
    for c in (2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 50, 100, 1000):
        print(f"  even c={c:4d}: {true_fate((1,2,c), 50_000_000)}")

    print("\n== fold validated against direct raw simulation ==")
    for c in (2, 14, 16):
        print(f"  even c={c}: raw halt = {raw_run((1,2,c), 200_000_000)} "
              f"(fold: genuine-halt)")
    for c in (4, 10):
        print(f"  even c={c}: raw halt within 5e7 = "
              f"{raw_run((1,2,c), 50_000_000)} (fold: survives)")
