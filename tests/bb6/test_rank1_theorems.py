"""Empirical validation of the proven rank-1 (dossier-5) Lean theorems.

Machine: 1RB1RD_1LC0LC_0RD0LB_1RF0LE_0RD---_0RA1RC
Lean:    busy-beaver-core/BusyBeaverCore/Rank1RawTM.lean

Two layers, mirroring test_dvisetu_theorems.py:

1. Episode theorems (dip_step, chunkA/chunkC/aterm/c1turn_step,
   descendExec_faithful, and the classical unit rules bcopy_step 12 /
   babsorb_step 8 / dinsert_step 12 / dregroup_step 8+6k): whenever a
   theorem's precondition (the full `Inv` layout) is planted on a
   randomized word, run the raw machine for the theorem's exact step
   count and verify end state, end head, the FULL tape delta, and the
   D-probe ledger (dips: exactly one D1 probe with a 0 to its left;
   descents/chunks: none).

2. The certified word orbit: an exact python transliteration of the
   Lean `dScan`/`stopDeep`/`descendExec`/`passGo`/`passFuel`/`wstep`
   (fuel semantics included) is iterated from the anchor ([1], 1)
   against the raw machine for 2M+ raw steps (>100 arrivals):
   every predicted arrival configuration (state, head, full tape) must
   be realized exactly at the predicted cumulative step count, the
   orbit must never return None (SafeWordOrbit empirically), and
   D-probe safety is checked at every raw step.
"""
import random

TABLE = {
    ('A', 0): (1, +1, 'B'), ('A', 1): (1, +1, 'D'),
    ('B', 0): (1, -1, 'C'), ('B', 1): (0, -1, 'C'),
    ('C', 0): (0, +1, 'D'), ('C', 1): (0, -1, 'B'),
    ('D', 0): (1, +1, 'F'), ('D', 1): (0, -1, 'E'),
    ('E', 0): (0, +1, 'D'),
    ('F', 0): (0, +1, 'A'), ('F', 1): (1, +1, 'C'),
}


def run_episode(tape, head, state, nsteps):
    t = dict(tape)
    probes = []
    for _ in range(nsteps):
        b = t.get(head, 0)
        if state == 'D' and b == 1:
            probes.append((head, t.get(head - 1, 0)))
        key = (state, b)
        assert key in TABLE, "halted inside an episode"
        w, d, s2 = TABLE[key]
        t[head] = w
        head += d
        state = s2
    return state, head, t, probes


def tapes_equal(t1, t2):
    return all(t1.get(k, 0) == t2.get(k, 0) for k in set(t1) | set(t2))


def inv_config(base, em, rest):
    """The unique tape/head of `Inv _ base em rest` (blank outside)."""
    cells = list(reversed(em)) + list(rest)
    tape = {base + i: (1 if c else 0) for i, c in enumerate(cells)}
    return tape, base + len(em)


def rbools(rng, n):
    return [rng.random() < 0.5 for _ in range(n)]


# ------------------------------------------------------------------
# Exact transliteration of the Lean definitions
# ------------------------------------------------------------------

def getD(l, i):
    return l[i] if 0 <= i < len(l) else False


def dScan(em):
    i = 0
    while True:
        if len(em) - 2 * i <= 0:
            return None
        if not em[2 * i]:
            return i
        if len(em) - 2 * i == 1:      # true :: []
            return None
        i += 1


def stopDeep(em):
    i = dScan(em)
    return True if i is None else (4 <= i)


def descendExec(em, r, rest):
    """Exact mirror of Lean descendExec (iterative for stack depth)."""
    steps = 0
    idx = 0
    adds = []                          # (not r) values, outermost first
    while len(em) - idx >= 2 and em[idx]:
        adds.append(not r)
        r = em[idx + 1]
        idx += 2
        steps += 2
    prefix = []
    for a in reversed(adds):
        prefix += [False, a]
    tail = em[idx:]
    if not tail:
        return (steps + 2, 1, [False], [not r] + prefix + rest)
    if tail == [True]:
        return (steps + 4, 2, [False],
                [True, False, not r] + prefix + rest)
    # false :: em2
    return (steps + 2, 0, list(tail), [not r] + prefix + rest)


def descendExec_slow(em, r, rest):
    """Literal recursive transliteration (cross-checked vs the fast
    one on random inputs)."""
    if not em:
        return (2, 1, [False], [not r] + rest)
    if em == [True]:
        return (4, 2, [False], [True, False, not r] + rest)
    if not em[0]:
        return (2, 0, list(em), [not r] + rest)
    s, db, em2, rest2 = descendExec_slow(em[2:], em[1],
                                         [False, not r] + rest)
    return (s + 2, db, em2, rest2)


def passGo(fuel, em, rest):
    em = list(em)
    rest = list(rest)
    dt = 0
    while True:
        if fuel == 0:
            return None
        fuel -= 1
        c0 = getD(rest, 0)
        if c0:
            if getD(em, 0):
                return None
            rest = [False] + rest[1:]
            dt += 2
            continue
        c1, c2 = getD(rest, 1), getD(rest, 2)
        if not c1 and c2:
            em = [True, False, True] + em
            rest = rest[3:]
            dt += 3
            continue
        if c1 and not c2:
            em = [False, True, True] + em
            rest = rest[3:]
            dt += 3
            continue
        if not c1 and not c2:
            em2 = [True, False, True] + em
            rest2 = rest[3:]
            if stopDeep(em2):
                if getD(rest2, 0):
                    return None
                return (list(reversed(em2)) + rest2, len(em) + 3, dt + 3)
            s, _db, em3, rest3 = descendExec(em2, getD(rest2, 0),
                                             rest2[1:])
            em, rest = em3, rest3
            dt += 3 + s
            continue
        # c1 and c2
        em2 = [True] + em
        if stopDeep(em2):
            return None
        s, _db, em3, rest3 = descendExec(em2, True, [False] + rest[3:])
        em, rest = em3, rest3
        dt += 3 + s


def passFuel(w):
    return 64 * (len(w) + 64) * (len(w) + 64)


def wstep(w, poff):
    """-> (w', poff', d, dbase) or None.  dbase is a python-side extra
    (the extreme extension of the initial descent) used to track the
    absolute base; the Lean wstep returns (w', poff', d)."""
    if not (poff <= len(w) and getD(w, poff) is False):
        return None
    em = list(reversed(w[:poff]))
    s, db, em1, rest1 = descendExec(em, False, w[poff + 1:])
    out = passGo(passFuel(w), em1, rest1)
    if out is None:
        return None
    w2, poff2, d2 = out
    return (w2, poff2, s + d2, db)


def waves(k):
    return [False, True, False, False, False, True] * k


def wavesOut(k):
    return [True, False, True, False, True, True] * k


# ------------------------------------------------------------------
# Layer 1: episode plants
# ------------------------------------------------------------------

def check_episode(base, em, rest, state_in, nsteps, base2, em2, rest2,
                  state_out, n_probes):
    tape, head = inv_config(base, em, rest)
    st, hd, t2, probes = run_episode(tape, head, state_in, nsteps)
    tape_exp, head_exp = inv_config(base2, em2, rest2)
    assert st == state_out, (st, state_out)
    assert hd == head_exp, (hd, head_exp)
    assert tapes_equal(t2, tape_exp)
    assert len(probes) == n_probes
    for (_, left) in probes:
        assert left == 0                 # every probe was safe


def test_rank1_micro_episode_theorems_match_raw_emulation():
    rng = random.Random(0)
    for _ in range(300):
        base = rng.randint(-25, 25)
        em = rbools(rng, rng.randint(0, 14))
        rest = rbools(rng, rng.randint(0, 14))
        # dip_step: 2 steps, one safe probe
        em_d = ([False] + em[1:]) if em else []
        rest_d = [True] + rest[1:] if rest else [True]
        check_episode(base, em_d, rest_d, 'D', 2,
                      base, em_d, [False] + rest_d[1:], 'D', 1)
        # chunkA_step: (0,0,1) -> push [1,0,1], 3 steps
        rest_a = [False, False, True] + rest
        check_episode(base, em, rest_a, 'D', 3,
                      base, [True, False, True] + em, rest, 'D', 0)
        # chunkC_step: (0,1,0) -> push [0,1,1], 3 steps
        rest_c = [False, True, False] + rest
        check_episode(base, em, rest_c, 'D', 3,
                      base, [False, True, True] + em, rest, 'D', 0)
        # aterm_step: (0,0,0) -> push [1,0,1], B at +3
        rest_t = [False, False, False] + rest
        check_episode(base, em, rest_t, 'D', 3,
                      base, [True, False, True] + em, rest, 'B', 0)
        # c1turn_step: (0,1,1) -> B at +1
        rest_1 = [False, True, True] + rest
        check_episode(base, em, rest_1, 'D', 3,
                      base, [True] + em, [True, False] + rest, 'B', 0)
        # descendExec_faithful: arbitrary stack, exact cost & layout
        r = rng.random() < 0.5
        s, db, em3, rest3 = descendExec(em, r, rest)
        assert (s, db, em3, rest3) == descendExec_slow(em, r, rest)
        check_episode(base, em, [r] + rest, 'B', s,
                      base - db, em3, rest3, 'D', 0)
        # bcopy_step (= B-cursor): 12 steps
        flux = [True, False, True, True, False]
        check_episode(base, flux + em, [True, False] + rest, 'B', 12,
                      base, flux + [True, False] + em, rest, 'B', 0)
        # babsorb_step: 8 steps, one safe probe
        check_episode(base, em_d,
                      [True, False, True, False, False, False] + rest,
                      'D', 8,
                      base, [True, False, True, True, False, True] + em_d,
                      rest, 'B', 1)
        # dinsert_step: 12 steps
        check_episode(base, flux + em, [False, False] + rest, 'B', 12,
                      base,
                      [False, True, True, True, False, True, False] + em,
                      rest, 'D', 0)
        # dregroup_step: 8+6k steps, one safe probe
        k = rng.randint(0, 6)
        check_episode(base, em_d,
                      [True, False, True] + waves(k)
                      + [False, True, False] + rest,
                      'D', 8 + 6 * k,
                      base,
                      [False, True, True] + wavesOut(k)
                      + [True, False, True] + em_d,
                      rest, 'D', 1)


# ------------------------------------------------------------------
# Layer 2: the certified word orbit vs raw, 2M+ steps
# ------------------------------------------------------------------

def test_rank1_wstep_orbit_against_raw():
    HORIZON = 2_200_000
    # predicted arrival schedule from the pure word orbit
    w, poff, base = [True], 1, 0
    t_pred = 1
    schedule = {}                       # t -> (w, poff, base)
    n_arr = 0
    while t_pred <= HORIZON:
        schedule[t_pred] = (list(w), poff, base)
        n_arr += 1
        out = wstep(w, poff)
        assert out is not None, f"SafeWordOrbit violated at arrival {n_arr}"
        w, poff, d, db = out
        base -= db
        t_pred += d
    assert n_arr > 100

    # raw run: check probe safety everywhere and realization at
    # every predicted arrival time
    tape = {}
    pos, st = 0, 'A'
    checked = 0
    for t in range(HORIZON + 1):
        if t in schedule:
            wk, pk, bk = schedule[t]
            assert st == 'B'
            assert pos == bk + pk
            cells = {bk + i: (1 if c else 0) for i, c in enumerate(wk)}
            assert tapes_equal(tape, cells)
            checked += 1
        r = tape.get(pos, 0)
        if st == 'D' and r == 1:
            assert tape.get(pos - 1, 0) == 0, f"unsafe D-probe at t={t}"
        w_, d_, ns = TABLE[(st, r)]
        tape[pos] = w_
        pos += d_
        st = ns
    assert checked == n_arr
