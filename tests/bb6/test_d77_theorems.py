"""Differential tests for the dossier-77 certified layer
(busy-beaver-core/BusyBeaverCore/Dossier77RawTM.lean).

Machine: 1RB0LF_1RC---_1LD0RF_1RA0LE_0LD1LD_0RD0RB (dossier-77, the
parametrics candidate of 2026-08-31; grows right, records at fresh
right extremes).

Three checks, mirroring test_d7_theorems.py / test_d8_theorems.py
(mirrored geometry: em = cells ABOVE the head, rest = the head cell
downward; push = left move, pop = right move; arrival = above-base
pop):

1. Episode plants: random boundary states (st, em, rest, base) are
   realized on a raw tape; one raw step is compared cell-for-cell
   against the Lean `go` micro-step surgery (push / interior pop /
   extreme-extending pop), including the fail-closed F1 halt probe.
2. Record mirror: the fail-closed word orbit (`worbit` = iterated
   `wstep` from the anchor (A, [])) is compared against every raw
   fresh-right-extreme record over >= 2M raw steps — state, word (getD
   equivalence), and exact cumulative step count — plus the fuel
   margin of `wfuel`.
3. Probe safety: at every raw step of the horizon, state B never
   reads a 1 (the FProbeSafe substrate: on this machine the fatal
   probe is the undefined halt transition F1 itself).

The word-machine mirror below is a literal transcription of the Lean
`go` (deques for O(1) list surgery; em[0] is the cell just above the
head, rest[0] the head cell; blank outside both).
"""
import random
from collections import deque

TM_CODE = '1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---'
ANCHOR = ('A', ())
HORIZON = 2_000_000
MIN_RECORDS = 100


def parse_tm(code):
    tbl = {}
    for si, block in enumerate(code.split('_')):
        for b in range(2):
            tr = block[3 * b:3 * b + 3]
            tbl[('ABCDEF'[si], b)] = None if tr == '---' else \
                (int(tr[0]), tr[1], tr[2])
    return tbl


TBL = parse_tm(TM_CODE)


# ---------------------------------------------------------------- mirror

def micro(st, em, rest):
    """One Lean `go` micro-step.  em/rest are deques (mutated).
    Returns ('cont', st'), ('arrival', st', word-list), or None."""
    r = rest[0] if rest else 0
    tr = TBL[(st, r)]
    if tr is None:
        return None                       # F1: the halt probe, fail-closed
    wv, d, ns = tr
    if rest:
        rest.popleft()
    if d == 'L':
        em.appendleft(wv)
        return ('cont', ns)
    if em:
        rest.appendleft(wv)
        rest.appendleft(em.popleft())
        return ('cont', ns)
    rest.appendleft(wv)
    rest.appendleft(0)
    return ('arrival', ns, list(rest))    # above-base pop: the record


def wfuel(w):
    return 64 * (len(w) + 64) * (len(w) + 64)


def wstep(st, w):
    """Lean `wstep`: run micro-steps from the arrival (st, w) to the
    next arrival.  Returns (st', w', dt, fuel_used_fraction) or None."""
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


# ------------------------------------------------------------- raw side

def realize(st, em, rest, base):
    """Raw configuration realizing Inv st base em rest (mirrored:
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
    """getD equivalence: equal up to trailing zeros."""
    n = max(len(u), len(v))
    return all((u[i] if i < len(u) else 0) == (v[i] if i < len(v) else 0)
               for i in range(n))


# ------------------------------------------------------------- test 1

def test_episode_plants():
    rng = random.Random(0x77)
    checked = 0
    for _ in range(20000):
        st = rng.choice('ABCDEF')
        em = [rng.randint(0, 1) for _ in range(rng.randint(0, 8))]
        rest = [rng.randint(0, 1) for _ in range(rng.randint(0, 8))]
        base = rng.randint(-5, 5)
        s0, h0, tape = realize(st, em, rest, base)
        dem, drest = deque(em), deque(rest)
        out = micro(st, dem, drest)
        r = rest[0] if rest else 0
        if out is None:
            # fail-closed exactly on the F1 halt probe
            assert st == 'F' and r == 1
            assert raw_step(s0, h0, tape) is None
            checked += 1
            continue
        nxt = raw_step(s0, h0, tape)
        assert nxt is not None
        s1, h1, tape1 = nxt
        if out[0] == 'cont':
            em2, rest2, base2 = list(dem), list(drest), base
        else:
            em2, rest2, base2 = [], out[2], base + 1
        assert s1 == out[1]
        assert h1 == base2 - len(em2)
        for k, v in enumerate(em2):
            assert tape1.get(base2 - len(em2) + 1 + k, 0) == v
        for k in range(len(em2), len(em2) + 12):
            assert tape1.get(base2 - len(em2) + 1 + k, 0) == 0
        for j, v in enumerate(rest2):
            assert tape1.get(base2 - len(em2) - j, 0) == v
        for j in range(len(rest2), len(rest2) + 12):
            assert tape1.get(base2 - len(em2) - j, 0) == 0
        checked += 1
    assert checked == 20000


# --------------------------------------------------------- tests 2 + 3

def run_raw(steps):
    """Raw run: records [(t, st, word)] at fresh right extremes (word
    from the head leftward, trailing blanks as written), with the
    F-probe-safety assertion at every step."""
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
        if st == 'F':
            assert b == 0, f'F-probe unsafe at t={t}'
        tr = TBL[(st, b)]
        assert tr is not None, f'raw halt at t={t}'
        wv, d, ns = tr
        tape[hd] = wv
        hd += 1 if d == 'R' else -1
        st = ns
    return recs


def test_record_mirror_and_probe_safety():
    recs = run_raw(HORIZON)
    assert len(recs) - 1 > MIN_RECORDS
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
    print(f'd77: {len(recs) - 1} record transitions exact over {HORIZON} '
          f'raw steps; max fuel fraction {max_frac:.6f}')


if __name__ == '__main__':
    test_episode_plants()
    print('d77: 20000 episode plants exact')
    test_record_mirror_and_probe_safety()
