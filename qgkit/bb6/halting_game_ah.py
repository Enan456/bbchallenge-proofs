"""The halting game at Antihydra's certified abstract layer.

Companion to halting_game.py (dossier-2/3 renewal layer) and
halting_game23.py (dossier-2 five-integer layer), for the machine

    1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA   (Antihydra).

Claim under verification: "the machine halts within K abstract steps."

  states         : the abstract hydra triples (a, m, c) of
                   AntihydraRawTM.lean (`AState`);
  law check      : one `astep` evaluation -- the exact python mirror
                   of the Lean-certified map (validated differentially:
                   anchor + first records re-checked at import, and
                   10^4 records against 51,854,692 raw steps offline);
  terminal check : the claimed dying state is MATERIALIZED as a
                   literal tape via the certified `Realizes` grammar
                   (1^a 0 1^m 0 1^c with the head on the fresh
                   frontier, state B) and run on the raw machine,
                   which must actually halt;
  forged terminals: states satisfying the dying condition
                   (astep = none).  Empirical lethality split: the
                   realizable fatal family is (1, 2, c); for ODD c the
                   raw machine halts in exactly (3c^2 + 44c + 125)/4
                   steps, for even c >= 4 it escapes the broken
                   grammar and does not halt within 2*10^7 steps.
                   Forgers therefore forge odd-c terminals.

Seed: the certified anchor (2, 7, 2), entered at raw step 62 with
anchor p = -6 (startup_run + realizes_start).
"""

import random

CODE = '1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA'


def parse(code):
    tbl = {}
    for i, blk in enumerate(code.split('_')):
        st = chr(ord('A') + i)
        for b in (0, 1):
            e = blk[3 * b:3 * b + 3]
            tbl[(st, b)] = None if e == '---' else (int(e[0]), e[1],
                                                    e[2])
    return tbl


TBL = parse(CODE)
SEED = (2, 7, 2)
STARTUP_STEPS, STARTUP_ANCHOR = 62, -6


def astep(a, m, c):
    """Exact mirror of AntihydraRawTM.astep (the Lean-certified map).
    None marks the dying condition (the Antihydra conjecture is that
    the orbit never reaches it)."""
    if m >= 3:
        return (a, m - 2, c + 3)
    if m == 2:
        return (a - 1, c + 3, 2) if a >= 2 else None
    if m == 1:
        return (a + 2, c + 2, 2)
    return None


def dying(s):
    return astep(*s) is None


def materialize(s, p=0):
    """The `Realizes` grammar as a literal tape: 1^a 0 1^m 0 1^c with
    the counter block ending at anchor p, head on the fresh frontier
    p + 3 + m + c, state B, blank elsewhere."""
    a, m, c = s
    tape = {}
    for i in range(a):
        tape[p - i] = 1
    for i in range(m):
        tape[p + 2 + i] = 1
    for i in range(c):
        tape[p + 3 + m + i] = 1
    return tape, p + 3 + m + c, 'B'


def raw_run(tape, pos, st, max_steps):
    for t in range(max_steps):
        b = tape.get(pos, 0)
        tr = TBL[(st, b)]
        if tr is None:
            return t
        w, d, ns = tr
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        st = ns
    return None


def raw_halts(s, max_steps=100_000):
    return raw_run(*materialize(s), max_steps)


# ---- differential validation at import: anchor + first records ----
# per-rule raw costs and anchor deltas (predictor.py; validated against
# the raw machine for 10^4 records / 51,854,692 raw steps)
def _validate(n_records=1000):
    # raw run from blank to the anchor
    tape, pos, st = {}, 0, 'A'
    for _ in range(STARTUP_STEPS):
        b = tape.get(pos, 0)
        w, d, ns = TBL[(st, b)]
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        st = ns
    mt, mh, ms = materialize(SEED, STARTUP_ANCHOR)
    assert st == ms and pos == mh, "anchor mismatch"
    lo, hi = min(tape) - 2, max(tape) + 2
    assert all(tape.get(q, 0) == mt.get(q, 0) for q in range(lo, hi)), \
        "anchor tape mismatch vs Realizes((2,7,2), p=-6)"
    # continue the raw run, checking each record on schedule
    s, p, t = SEED, STARTUP_ANCHOR, STARTUP_STEPS
    for _ in range(n_records):
        a, m, c = s
        if m >= 3:
            cost, dp = 2 * c + 11, 0
        elif m == 2:
            cost, dp = 2 * c + 16, -1
        else:
            cost, dp = 2 * a + 2 * c + 22, -1
        s, p, t = astep(a, m, c), p + dp, t + cost
        for _ in range(cost):
            b = tape.get(pos, 0)
            w, d, ns = TBL[(st, b)]
            tape[pos] = w
            pos += 1 if d == 'R' else -1
            st = ns
        mt, mh, ms = materialize(s, p)
        assert st == ms and pos == mh, f"record mismatch at step {t}"
        lo, hi = min(tape) - 2, max(tape) + 2
        assert all(tape.get(q, 0) == mt.get(q, 0)
                   for q in range(lo, hi)), f"tape mismatch at {t}"
    return n_records


def true_orbit(K):
    orb = [SEED]
    s = SEED
    for _ in range(K):
        s2 = astep(*s)
        if s2 is None:
            raise SystemExit("certified orbit died (refutes the "
                             "Antihydra conjecture; report immediately)")
        s = s2
        orb.append(s)
    return orb


def forged_pool(max_c=79):
    """Dying states, raw-verified lethal.  The realizable fatal family
    is (1, 2, c); odd c halts (quadratically), even c >= 4 does not."""
    pool = []
    for c in range(1, max_c + 1, 2):
        t = raw_halts((1, 2, c), 20_000)
        assert t is not None and t == (3 * c * c + 44 * c + 125) // 4
        pool.append(((1, 2, c), t))
    t2 = raw_halts((1, 2, 2), 20_000)   # the one even-c straggler
    if t2 is not None:
        pool.append(((1, 2, 2), t2))
    return pool


class Honest:
    def __init__(self, orbit):
        self.orbit = orbit

    def snapshot(self, j):
        return self.orbit[j]

    def halt_index(self):
        for i, s in enumerate(self.orbit):
            if dying(s):
                return i
        return None


class SeamForger(Honest):
    """Follows the true orbit to a chosen seam m, then splices a
    raw-verified lethal dying state at m + 1.  One law violation."""

    def __init__(self, orbit, m, lethal):
        super().__init__(orbit)
        self.m = m
        self.forged = lethal

    def snapshot(self, j):
        return self.forged if j == self.m + 1 else self.orbit[j]

    def halt_index(self):
        return self.m + 1


def play(pa, pb, K, r, rng):
    if pa.snapshot(0) != SEED or pb.snapshot(0) != SEED:
        return False, 'seed'
    k = pa.halt_index()
    if k is None or k != pb.halt_index():
        return False, 'no-halt-claim'
    sk = pa.snapshot(k)
    if sk != pb.snapshot(k):
        return False, 'terminal-cross'
    if raw_halts(sk, 100_000) is None:
        return False, 'terminal-not-fatal'
    for _ in range(r):
        j = rng.randrange(K)
        s1a = pa.snapshot(j + 1)
        if s1a != pb.snapshot(j + 1):
            return False, 'cross'
        if astep(*pa.snapshot(j)) != s1a:
            return False, f'law@{j}'
    return True, 'accept'


if __name__ == '__main__':
    n = _validate()
    print(f"mirror validated at import: anchor (raw step 62) + "
          f"{n} records, full-tape, against the raw machine")

    K = 100_000
    rng = random.Random(6)
    orbit = true_orbit(K)
    n_dying = sum(1 for s in orbit if dying(s))
    a_at_drops = [s[0] for s in orbit if s[1] == 2]
    print(f"true orbit: K={K} abstract steps; dying states on it: "
          f"{n_dying}; drop events: {len(a_at_drops)}; min counter at "
          f"a drop: {min(a_at_drops)}")

    pool = forged_pool()
    ts = sorted(t for _, t in pool)
    print(f"forged terminals (dying + raw-verified lethal): "
          f"{len(pool)}; halt times min/median/max: {ts[0]}/"
          f"{ts[len(ts) // 2]}/{ts[-1]} raw steps")

    honest = Honest(orbit)
    print("honest provers:", play(honest, honest, K, 64, rng),
          " [cannot name a halt index: no dying state in K steps]")

    print(f"{'r':>8} {'accept':>8} {'(1-1/K)^r':>10}  trials")
    for r, trials in ((64, 2000), (1024, 1000), (16384, 200),
                      (262144, 30), (1048576, 10)):
        n_acc = 0
        for _ in range(trials):
            f = SeamForger(orbit, rng.randrange(K - 1),
                           pool[rng.randrange(len(pool))][0])
            acc, _w = play(f, f, K, r, rng)
            n_acc += acc
        print(f"{r:>8} {n_acc / trials:>8.3f} {(1 - 1 / K) ** r:>10.4f}"
              f"  {trials}", flush=True)
