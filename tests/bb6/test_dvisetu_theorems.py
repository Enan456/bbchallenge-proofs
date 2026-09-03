"""Empirical validation of the proven dossier-6 (Dvisetu) Lean theorems.

Two layers, mirroring test_dossier23_theorems.py:

1. Episode theorems (passA_step, passE_step, drift_step, renew2_step,
   collapse_step): whenever a theorem's precondition is planted on a
   randomized tape, run the raw machine for the theorem's exact step
   count and verify end state, end head, the FULL tape delta, and the
   theorem's E-probe ledger (passE: exactly one E0 probe at f-1 with a 1
   to its right; all others: none).

2. The abstract checkpoint orbit (cstep mirror: drift/collapse/micro/
   renewals with the guarded divide branch): driven from the 6-step
   startup anchor oneA(3) against the raw machine for 2M+ steps,
   checking every transition's end state, head, dt, and full tape
   window; divide renewals are resynced at their landing record and must
   realize the abstract output exactly.  The global E-probe-safety
   conjecture (every E0 probe has a 1 to its right) is checked at every
   raw step.
"""
import random
from collections import defaultdict

TABLE = {
    ('A', 0): (1, +1, 'B'), ('A', 1): (0, +1, 'B'),
    ('B', 0): (1, -1, 'B'), ('B', 1): (0, -1, 'C'),
    ('C', 0): (1, +1, 'D'), ('C', 1): (1, -1, 'C'),
    ('D', 0): (1, +1, 'E'), ('D', 1): (0, +1, 'A'),
    ('E', 0): (0, +1, 'F'), ('E', 1): (1, +1, 'A'),
    ('F', 1): (1, -1, 'B'),
}


def run_episode(tape, head, state, nsteps):
    t = dict(tape)
    probes = []
    for _ in range(nsteps):
        b = t.get(head, 0)
        if state == 'E' and b == 0:
            probes.append((head, t.get(head + 1, 0)))
        key = (state, b)
        assert key in TABLE, "halted inside an episode"
        w, d, s2 = TABLE[key]
        t[head] = w
        head += d
        state = s2
    return state, head, t, probes


def tapes_equal(t1, t2):
    return all(t1.get(k, 0) == t2.get(k, 0) for k in set(t1) | set(t2))


def base_tape(rng, lo, hi):
    t = {}
    for x in range(lo - 30, lo):
        t[x] = rng.randint(0, 1)
    for x in range(hi + 1, hi + 30):
        t[x] = rng.randint(0, 1)
    return t


def test_dvisetu_episode_theorems_match_raw_emulation():
    rng = random.Random(0)
    for _ in range(200):
        # passA_step: 8s+5 steps, tape[g:=1][g+1:=0], no E0 probe
        s = rng.randint(0, 12)
        g = rng.randint(-20, 20)
        h = g + 3 * s + 2
        t = base_tape(rng, g, h)
        t[g] = 0
        for x in range(g + 1, h + 1):
            t[x] = 1
        st, hd, t2, probes = run_episode(t, h, 'B', 8 * s + 5)
        exp = dict(t)
        exp[g] = 1
        exp[g + 1] = 0
        assert st == 'B' and hd == h + 1 and tapes_equal(t2, exp)
        assert probes == []
        # passE_step: 8n+6 steps, tape[f:=1][g:=1][g+1:=0], one safe probe
        n = rng.randint(1, 12)
        g = rng.randint(-20, 20)
        f = g + 3 * n + 2
        t = base_tape(rng, g, f)
        t[g] = 0
        for x in range(g + 1, f):
            t[x] = 1
        t[f] = 0
        st, hd, t2, probes = run_episode(t, f, 'B', 8 * n + 6)
        exp = dict(t)
        exp[f] = 1
        exp[g] = 1
        exp[g + 1] = 0
        assert st == 'B' and hd == f - 2 and tapes_equal(t2, exp)
        assert probes == [(f - 1, 1)]
        # drift_step: 32n-3 steps, tape[f:=1][g:=1][g+4:=0], one safe probe
        st, hd, t2, probes = run_episode(t, f, 'B', 32 * n - 3)
        exp = dict(t)
        exp[f] = 1
        exp[g] = 1
        exp[g + 4] = 0
        assert st == 'B' and hd == g + 3 * n + 3 and tapes_equal(t2, exp)
        assert probes == [(f - 1, 1)]
        # renew2_step: 16u+11 steps, tape[f:=1][L-1:=1][L+1:=0], no probe
        u = rng.randint(0, 12)
        L = rng.randint(-20, 20)
        f = L + 3 * u + 2
        t = base_tape(rng, L - 1, f)
        t[L - 1] = 0
        for x in range(L, f):
            t[x] = 1
        t[f] = 0
        st, hd, t2, probes = run_episode(t, f, 'B', 16 * u + 11)
        exp = dict(t)
        exp[f] = 1
        exp[L - 1] = 1
        exp[L + 1] = 0
        assert st == 'B' and hd == f + 1 and tapes_equal(t2, exp)
        assert probes == []
        # collapse_step: 5 steps, tape[g+2:=1][g:=1], no probe
        g = rng.randint(-20, 20)
        t = base_tape(rng, g, g + 2)
        t[g] = 0
        t[g + 1] = 1
        t[g + 2] = 0
        st, hd, t2, probes = run_episode(t, g + 2, 'B', 5)
        exp = dict(t)
        exp[g + 2] = 1
        exp[g] = 1
        assert st == 'A' and hd == g + 3 and tapes_equal(t2, exp)
        assert probes == []


# --- abstract checkpoint layer (python mirror of cstep) ---------------------

def divide(n):
    m, d = n, 0
    while m % 9 == 0:
        m //= 3
        d += 1
    y = (m - 9) // 3 if m % 9 == 3 else (m - 3) // 3
    x = n + 2 + d - y
    return x, y


def cstep(s):
    """Mirror of the Lean cstep on anchored states; dt None on divide."""
    kind = s[0]
    if kind == 'T':
        _, a, b, g = s
        if b == 1:
            return ('OA', a + 3, g - a), 5
        if b % 3 == 1 and b >= 4:
            return ('T', a + 4, b - 3, g + 4), (32 * b - 41) // 3
        return None, None
    if kind == 'OA':
        _, m, L = s
        return ('OB', m + 1, L), 1
    _, n, L = s
    if n % 3 == 1:
        if n >= 4:
            return ('T', 4, n - 3, L + 3), (32 * n - 41) // 3
        return None, None
    if n % 3 == 2:
        return ('T', 2, n - 1, L + 1), (16 * n + 1) // 3
    x, y = divide(n)
    if y < 1 or x < 1:
        return None, None
    return ('T', x, y, None), None


def expected_config(s):
    kind = s[0]
    cells = {}
    if kind == 'T':
        _, a, b, g = s
        for i in range(a):
            cells[g - a + i] = 1
        for i in range(b):
            cells[g + 1 + i] = 1
        return 'B', g + b + 1, cells
    _, m, L = s
    for i in range(m):
        cells[L + i] = 1
    return ('A' if kind == 'OA' else 'B'), L + m, cells


def test_dvisetu_abstract_orbit_matches_raw():
    max_steps = 2_000_000
    tape = defaultdict(int)
    head, state = 0, 'A'
    t = 0

    def raw_step():
        nonlocal head, state, t
        key = (state, tape[head])
        assert key in TABLE, f"HALT at t={t}"
        if state == 'E' and tape[head] == 0:
            # global E-probe-safety conjecture: a 1 to the right
            assert tape[head + 1] == 1, f"probe safety violated at t={t}"
        w, d, s2 = TABLE[key]
        tape[head] = w
        head += d
        state = s2
        t += 1

    for _ in range(6):  # startup anchor: 6 raw steps to oneA(3) at L=-1
        raw_step()
    cur = ('OA', 3, -1)
    st, hd, cells = expected_config(cur)
    assert state == st and head == hd
    checked = 0
    divides = 0
    while t < max_steps:
        nxt, dt = cstep(cur)
        assert nxt is not None, f"orbit died at {cur} t={t}"
        if dt is not None:
            for _ in range(dt):
                raw_step()
            st, hd, cells = expected_config(nxt)
            assert state == st and head == hd, (cur, nxt, t)
            lo, hi = min(cells) - 2, max(cells) + 2
            for x in range(lo, hi + 1):
                assert tape[x] == cells.get(x, 0), (cur, nxt, x, t)
            cur = nxt
        else:
            # divide renewal: run raw to the next fresh right extreme,
            # which must realize the abstract output exactly
            _, x, y, _ = nxt
            rmax = head
            found = False
            for _ in range(60_000_000):
                raw_step()
                if head > rmax:
                    rmax = head
                    cand = ('T', x, y, head - 1 - y)
                    st, hd, cells = expected_config(cand)
                    ok = state == st and head == hd
                    if ok:
                        lo, hi = min(cells) - 2, max(cells) + 2
                        ok = all(tape[q] == cells.get(q, 0)
                                 for q in range(lo, hi + 1))
                    assert ok, f"divide from {cur} missed T({x},{y}) at t={t}"
                    cur = cand
                    found = True
                    break
            assert found
            divides += 1
        checked += 1
    assert checked > 100, checked
    assert divides >= 3, divides
