"""Dossier-7/8: record extraction + conditional macro laws + fail-closed
validation for the two new fixed-shape-gate machines of 2026-08-31.

  dossier-7 (A): 1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA
  dossier-8 (B): 1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE

Both grow left. Record := fresh-left-extreme event; the tape support is
encoded as the tuple of 1-block lengths (every interior 0-run is a
singleton; the extractor verifies this and reports violations).

Standard family:
  A: state A, (a, 1, b, 1^k, 4, 2) with k odd, or terminal (a, 1, b, 2)
  B: state E, (a, 1, b, 1^k, 4^g, 2) with k even, g the grand-epoch counter

The law is a deterministic record-level rewrite system (13 rules for A,
12 for B) with parity guards; law_A/law_B return the applicable rules
for a record, and the validator demands that every consecutive record
transition is reproduced exactly (fail-closed: unmatched or mismatched
pairs are listed verbatim).

Usage: python3 d78_laws.py {A|B} [steps=20000000]

Validated 2026-08-31: A 5251/5251 and B 3879/3879 consecutive record
transitions exact at 20M raw steps (records with t > 200), zero
exceptions, zero ambiguous rule matches, zero non-singleton 0-runs.
"""
import sys
from collections import Counter

CODES = {
    'A': '1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA',
    'B': '1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE',
}


def parse_tm(code):
    tbl = {}
    for si, block in enumerate(code.split('_')):
        for b in range(2):
            tr = block[3 * b:3 * b + 3]
            tbl[('ABCDEF'[si], b)] = None if tr == '---' else \
                (int(tr[0]), tr[1], tr[2])
    return tbl


def run(code, steps):
    """Simulate; return records [(t, state, ones-tuple)] at fresh left
    extremes. Prints a warning on any non-singleton interior 0-run."""
    tbl = parse_tm(code)
    tape = {}
    tget = tape.get
    st, hd = 'A', 0
    lo = hi = 0
    records = []
    t = 0
    while t < steps:
        b = tget(hd, 0)
        if hd < lo:
            lo = hd
            a = hd + 1
            while a <= hi and tget(a, 0) == 0:
                a += 1
            bb = hi
            while bb >= a and tget(bb, 0) == 0:
                bb -= 1
            ones = []
            q = a
            while q <= bb:
                s = tget(q, 0)
                r = q
                while r <= bb and tget(r, 0) == s:
                    r += 1
                if s == 1:
                    ones.append(r - q)
                elif r - q != 1:
                    print(f'NONSINGLETON ZERO RUN t={t}')
                q = r
            records.append((t, st, tuple(ones)))
        elif hd > hi:
            hi = hd
        tr = tbl[(st, b)]
        if tr is None:
            print(f'HALTED t={t} {st}{b}')
            break
        w, d, ns = tr
        tape[hd] = w
        hd += 1 if d == 'R' else -1
        st = ns
        t += 1
    return records


def is_ones(seg):
    return all(x == 1 for x in seg)


def law_A(st, u):
    """Machine A record-level law. Returns [(rule, state', tuple')]."""
    n = len(u)
    rules = []
    if st == 'A' and n >= 3 and u[1] == 1:
        a = u[0]
        if a >= 3:
            rules.append(('R1-drift', 'A', (a - 2, 1, u[2] + 3) + u[3:]))
        elif a == 2:
            rules.append(('R2-merge', 'A', (1, u[2] + 3) + u[3:]))
        elif a == 1:
            rules.append(('R3a-oddbottom', 'D', (4, u[2]) + u[3:]))
    if st == 'A' and n >= 2 and u[0] == 1 and u[1] != 1:
        rules.append(('R4a-evenbottom', 'D', (3,) + u[1:]))
    if st == 'D' and n >= 2 and u[0] == 4 and u[1] != 1:
        rules.append(('R3b-check', 'A', (5,) + u[1:]))
    if st == 'D' and n >= 2 and u[0] == 3 and u[1] != 1:
        rules.append(('R4b-check', 'A', (4,) + u[1:]))
    if st == 'A' and n >= 2 and u[0] == 5 and u[1] != 1:
        B = u[1]
        rest = u[2:]
        if len(rest) >= 3 and rest[-2:] == (4, 2) and is_ones(rest[:-2]):
            k = len(rest) - 2
            if k >= 3:
                rules.append(('R3c-minor', 'A',
                              (B + 1, 1, 7) + (1,) * (k - 2) + (4, 2)))
            elif k == 1:
                rules.append(('R3c1-minor-last', 'A', (B + 1, 1, 10, 2)))
        elif rest == (2,) and B % 2 == 0:
            m = (B - 6) // 2
            rules.append(('T1-grand', 'D', (1, 1, 1, 4) + (1,) * m + (4, 2)))
    if st == 'A' and n >= 2 and u[0] == 4 and u[1] != 1:
        B = u[1]
        rest = u[2:]
        if len(rest) >= 3 and rest[-2:] == (4, 2) and is_ones(rest[:-2]):
            k = len(rest) - 2
            if k >= 3:
                rules.append(('R4c-minor', 'A',
                              (B, 1, 7) + (1,) * (k - 2) + (4, 2)))
        elif rest == (2,) and B % 2 == 1:
            m = (B + 1) // 2
            rules.append(('R4g-grand', 'A', (2,) + (1,) * m + (4, 2)))
    if st == 'D' and n >= 6 and u[:4] == (1, 1, 1, 4) and u[-2:] == (4, 2) \
            and is_ones(u[4:-2]):
        m = n - 6
        rules.append(('T2-grand', 'D', (1, 4, 4) + (1,) * m + (4, 2)))
    if st == 'D' and n >= 5 and u[:3] == (1, 4, 4) and u[-2:] == (4, 2) \
            and is_ones(u[3:-2]):
        m = n - 5
        rules.append(('T3-grand', 'A', (6, 1, 7) + (1,) * (m - 2) + (4, 2)))
    return rules


def _tail_split(rest):
    """rest = 1^k 4^g 2 -> (k, g) or None."""
    i = 0
    while i < len(rest) and rest[i] == 1:
        i += 1
    j = i
    while j < len(rest) and rest[j] == 4:
        j += 1
    if j == len(rest) - 1 and rest[-1] == 2:
        return i, j - i
    return None


def law_B(st, u):
    """Machine B record-level law. Returns [(rule, state', tuple')]."""
    n = len(u)
    rules = []
    if st == 'E' and n >= 3 and u[1] == 1:
        a = u[0]
        if a >= 3:
            rules.append(('S1-drift', 'E', (a - 2, 1, u[2] + 3) + u[3:]))
        elif a == 2:
            rules.append(('S2-merge', 'E', (1, u[2] + 3) + u[3:]))
        elif a == 1:
            rules.append(('S3a-oddbottom', 'A', (4, u[2]) + u[3:]))
    if st == 'E' and n >= 2 and u[0] == 1 and u[1] != 1:
        rules.append(('S4a-evenbottom', 'A', (3,) + u[1:]))
    if st == 'A' and n >= 2 and u[0] == 4 and u[1] != 1:
        B = u[1]
        ts = _tail_split(u[2:])
        if ts:
            k, g = ts
            if k >= 2:
                rules.append(('S3b-minor', 'E',
                              (B, 1, 7) + (1,) * (k - 2) + (4,) * g + (2,)))
            elif k == 1 and g == 1:
                rules.append(('S3b1-minor-last', 'E', (B, 1, 10, 2)))
    if st == 'A' and n >= 2 and u[0] == 3 and u[1] != 1:
        B = u[1]
        ts = _tail_split(u[2:])
        if ts:
            k, g = ts
            if k >= 2:
                rules.append(('S4b-minor', 'E',
                              (B - 1, 1, 7) + (1,) * (k - 2) + (4,) * g + (2,)))
            elif k == 0 and g >= 1 and B % 2 == 0:
                m = (B - 4) // 2
                rules.append(('S4g-grand', 'A',
                              (1, 4) + (1,) * m + (4,) * (g + 1) + (2,)))
            elif k == 0 and g == 0 and B % 2 == 1:
                m = (B + 3) // 2
                rules.append(('S4g0-grand', 'E', (1,) * m + (4, 2)))
    if st == 'A' and n >= 4 and u[:2] == (1, 4):
        ts = _tail_split(u[2:])
        if ts:
            m, g = ts
            rules.append(('G2-grand', 'A', (7,) + (1,) * m + (4,) * g + (2,)))
    if st == 'A' and n >= 3 and u[0] == 7:
        ts = _tail_split(u[1:])
        if ts:
            m, g = ts
            if m >= 3:
                rules.append(('G3-grand', 'E',
                              (5, 1, 4) + (1,) * (m - 2) + (4,) * g + (2,)))
    if st == 'A' and n >= 4 and u[0] == 4 and u[-2:] == (4, 2) \
            and is_ones(u[1:-2]):
        k = n - 3
        rules.append(('SU-startup', 'E', (2, 1, 4) + (1,) * (k - 2) + (4, 2)))
    return rules


def compress(u):
    out = []
    i = 0
    while i < len(u):
        j = i
        while j < len(u) and u[j] == u[i]:
            j += 1
        out.append(f'{u[i]}^{j - i}' if j - i > 2 else
                   ','.join(str(u[i]) for _ in range(j - i)))
        i = j
    return '(' + ','.join(out) + ')'


def validate(which, steps=20_000_000, tmin=200):
    law = law_A if which == 'A' else law_B
    records = run(CODES[which], steps)
    recs = [r for r in records if r[0] > tmin]
    total = len(recs) - 1
    ok = Counter()
    exceptions = []
    ambiguous = 0
    for (t0, s0, u0), (t1, s1, u1) in zip(recs, recs[1:]):
        rules = law(s0, u0)
        if len(rules) > 1:
            ambiguous += 1
        hits = [name for name, s, u in rules if s == s1 and u == u1]
        if hits:
            ok[hits[0]] += 1
        else:
            exceptions.append(((t0, s0, u0), (t1, s1, u1),
                               [r[0] for r in rules]))
    print(f'== {which} @ {steps} steps, records t>{tmin}: '
          f'{total} consecutive transitions ==')
    print(f'reproduced exactly: {sum(ok.values())}/{total}')
    for name, c in ok.most_common():
        print(f'  {name}: {c}')
    print(f'ambiguous rule matches: {ambiguous}')
    print(f'exceptions: {len(exceptions)}')
    for (t0, s0, u0), (t1, s1, u1), names in exceptions:
        print(f'  t={t0} {s0}0 {compress(u0)} -> {s1}0 {compress(u1)}'
              f'  [rules fired: {names}]')
    return len(exceptions) == 0


if __name__ == '__main__':
    which = sys.argv[1]
    steps = int(sys.argv[2]) if len(sys.argv) > 2 else 20_000_000
    validate(which, steps)
