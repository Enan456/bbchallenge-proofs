#!/usr/bin/env python3
"""dossier-58 record-orbit mirror (differential validation).

Literal transcription of the Lean `go` / `wstep` sweep for the machine
`1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_1RC---` (grows right; the fatal probe is the undefined transition
`F1`).  `main()` runs the raw machine and the fail-closed word orbit
side by side over a 20M-step horizon and asserts they agree exactly on
every record (state, word up to trailing zeros, cumulative step count),
that state `F` never reads a `1`, and that the quadratic fuel is never
exhausted."""
from collections import deque

TM_CODE = '1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_1RC---'
ANCHOR = ('A', ())
PROBE = 'F'
PUSH_DIR = 'L'


def parse_tm(code):
    tbl = {}
    for si, block in enumerate(code.split('_')):
        for b in range(2):
            tr = block[3 * b:3 * b + 3]
            tbl[('ABCDEF'[si], b)] = None if tr == '---' else \
                (int(tr[0]), tr[1], tr[2])
    return tbl


TBL = parse_tm(TM_CODE)


def micro(st, em, rest):
    """One Lean `go` micro-step; em/rest are deques (mutated).  Returns
    ('cont', st'), ('arrival', st', word-list), or None (halt probe)."""
    r = rest[0] if rest else 0
    tr = TBL[(st, r)]
    if tr is None:
        return None
    wv, d, ns = tr
    if rest:
        rest.popleft()
    if d == PUSH_DIR:
        em.appendleft(wv)
        return ('cont', ns)
    if em:
        rest.appendleft(wv)
        rest.appendleft(em.popleft())
        return ('cont', ns)
    rest.appendleft(wv)
    rest.appendleft(0)
    return ('arrival', ns, list(rest))


def wfuel(w):
    return 64 * (len(w) + 64) * (len(w) + 64)


def wstep(st, w):
    fuel = wfuel(w)
    em, rest = deque(), deque(w)
    dt = 0
    while fuel > 0:
        fuel -= 1
        out = micro(st, em, rest)
        if out is None:
            return None
        dt += 1
        if out[0] == 'arrival':
            return (out[1], tuple(out[2]), dt, dt / wfuel(w))
        st = out[1]
    return None


def record_orbit(n):
    """`worbit` iterated: the fail-closed record orbit, n records."""
    st, w = ANCHOR
    orbit = [(st, w)]
    for _ in range(n):
        out = wstep(st, w)
        if out is None:
            return orbit, False
        st, w = out[0], out[1]
        orbit.append((st, w))
    return orbit, True


def realize(st, em, rest, base):
    """Raw config realizing Inv st base em rest (right-grower:
    head at base - len(em), em above the head, rest downward)."""
    tape = {}
    for k, v in enumerate(em):
        tape[base - len(em) + 1 + k] = v
    for j, v in enumerate(rest):
        tape[base - len(em) - j] = v
    return st, base - len(em), tape


def raw_step(st, hd, tape):
    tr = TBL[(st, tape.get(hd, 0))]
    if tr is None:
        return None
    wv, d, ns = tr
    tape[hd] = wv
    return ns, hd + (1 if d == 'R' else -1), tape


def eqw(u, v):
    n = max(len(u), len(v))
    return all((u[i] if i < len(u) else 0) == (v[i] if i < len(v) else 0)
               for i in range(n))


def run_raw(steps):
    """Raw run: records at fresh right extremes, probe-safe at every step."""
    tape = {}
    st, hd = 'A', 0
    lo = hi = 0
    recs = [(0, 'A', ())]
    for t in range(steps):
        b = tape.get(hd, 0)
        if hd > hi:
            hi = hd
            recs.append((t, st,
                         tuple(tape.get(x, 0) for x in range(hd, lo - 1, -1))))
        elif hd < lo:
            lo = hd
        if st == PROBE:
            assert b == 0, f'F-probe unsafe at t={t}'
        tr = TBL[(st, b)]
        assert tr is not None, f'raw halt at t={t}'
        wv, d, ns = tr
        tape[hd] = wv
        hd += 1 if d == 'R' else -1
        st = ns
    return recs


def differential(horizon):
    recs = run_raw(horizon)
    st, w = ANCHOR
    t = 0
    max_frac = 0.0
    for i in range(1, len(recs)):
        out = wstep(st, w)
        assert out is not None, f'orbit died at index {i}'
        st, w, dt, frac = out
        max_frac = max(max_frac, frac)
        t += dt
        rt, rs, rw = recs[i]
        assert t == rt, f'step count mismatch at record {i}: {t} != {rt}'
        assert st == rs, f'state mismatch at record {i}: {st} != {rs}'
        assert eqw(w, rw), f'word mismatch at record {i}'
    assert max_frac < 1.0
    return len(recs) - 1, max_frac


def main():
    horizon = 20_000_000
    n, max_frac = differential(horizon)
    print(f'dossier-58: {n} record transitions exact over {horizon} raw '
          f'steps; max fuel fraction {max_frac:.6f}')


if __name__ == '__main__':
    main()
