"""The halting game at the certified five-integer layer of dossier-2.

Upgrade of halting_game.py from the reduced renewal map to the full
certified abstraction, with the two strengthenings introduced by the
word-calculus game:

  law check      : one metaStep evaluation (the exact python mirror
                   of the Lean-certified map, validated against raw
                   spawn entries in tests/bb6);
  terminal check : the claimed halt state is MATERIALIZED as a
                   literal tape (the certified holeTape realization:
                   solid 1s on [l, r-1] minus the holes) and run on
                   the raw machine, which must actually halt;
  forged terminals: perturbed five-integer states inside the
                   provably lethal danger bands, found by search and
                   confirmed halting by raw execution.

States: (three, l, h1, h2, r); seed: the certified anchor
(False, -8, -2, 12, 13) entered at raw step 235; spawn state D.
"""

import random

CODE = '1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD'


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
SEED = (False, -8, -2, 12, 13)


def meta_step(three, l, h1, h2, r):
    if three:
        if l <= h1 and h1 + 4 <= h2 and h2 + 6 <= r and \
                (r - h2) % 2 == 0 and (h2 - h1) % 2 == 0:
            return (False, l, h1 + 6, h2 + 4, r + 1)
        if l <= h1 and h2 == h1 + 2 and h2 + 7 <= r and \
                (r - h2) % 2 == 0:
            return (False, l, h1 + 9, r + 1, r + 2)
        return None
    if h2 == r - 1:
        if l <= h1 and h1 <= r - 4:
            return (False, l, h1, r - 2, r + 1)
        return None
    if h2 == r - 3:
        if (r - h1) % 2 == 1:
            if l <= h1 and h1 + 7 <= r:
                return (False, l, h1 + 6, r + 1, r + 2)
            return None
        if (h1 - l) % 2 == 1:
            if l + 3 <= h1 and h1 + 6 <= r:
                return (False, l - 1, l + 5, h1 + 4, r + 1)
            return None
        if l + 5 <= h1 and h1 + 6 <= r:
            return (False, l - 3, l + 6, h1 + 4, r + 1)
        return None
    if l <= h1 and h1 + 1 <= h2 and h2 <= r - 4:
        return (True, l, h1, h2, r + 1)
    return None


def materialize(ms):
    three, l, h1, h2, r = ms
    holes = {h1, h2} | ({r - 3} if three else set())
    tape = {q: 0 if q in holes else 1 for q in range(l, r)}
    return tape, r, 'D'


def raw_halts(ms, max_steps=100_000):
    tape, pos, st = materialize(ms)
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


def true_orbit(K):
    orb = [SEED]
    ms = SEED
    for _ in range(K):
        ms = meta_step(*ms)
        if ms is None:
            raise SystemExit("certified orbit hit None (impossible)")
        orb.append(ms)
    return orb


def find_lethal(orbit, rng, want=40):
    """Construct danger-band corner states from true orbit geometry:
    collapse the inter-hole gap and force renewal-adjacent offsets,
    keep candidates that meta_step rejects AND that raw-halt when
    materialized (the provably lethal bands)."""
    pool = []
    tried = 0
    while len(pool) < want and tried < 60000:
        tried += 1
        three, l, h1, h2, r = orbit[rng.randrange(len(orbit))]
        mode = rng.randrange(3)
        if mode == 0:      # tiny inter-hole gap near the right end
            c2 = r - rng.choice((1, 3))
            c1 = c2 - rng.choice((1, 2, 3))
            cand = (False, l, c1, c2, r)
        elif mode == 1:    # small b at a carried entry
            c1 = h1
            c2 = h1 + rng.choice((1, 2, 3))
            cand = (three, l, c1, c2, r)
        else:              # parity-violating renewal corner
            c2 = r - 3
            c1 = r - rng.choice((4, 5, 6, 7, 8))
            cand = (False, l, c1, c2, r)
        _t, _l, c1, c2, _r = cand
        if not (_l < c1 < c2 < _r):
            continue
        if meta_step(*cand) is not None:
            continue
        t = raw_halts(cand, 5000)
        if t is not None:
            pool.append((cand, t))
    return pool


class Honest:
    def __init__(self, orbit):
        self.orbit = orbit

    def snapshot(self, j):
        return self.orbit[j]

    def halt_index(self):
        return None


class SeamForger(Honest):
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
    if raw_halts(sk, 5000) is None:
        return False, 'terminal-not-fatal'
    for _ in range(r):
        j = rng.randrange(K)
        s1a = pa.snapshot(j + 1)
        if s1a != pb.snapshot(j + 1):
            return False, 'cross'
        if meta_step(*pa.snapshot(j)) != s1a:
            return False, f'law@{j}'
    return True, 'accept'


if __name__ == '__main__':
    K = 200_000
    rng = random.Random(23)
    orbit = true_orbit(K)
    print(f"certified orbit: K={K} episodes from the anchor")

    # true states never raw-halt (sample)
    n_fatal = sum(1 for ms in orbit[::K // 50]
                  if raw_halts(ms, 50_000) is not None)
    print(f"raw-halting states on the true orbit (sampled): {n_fatal}")

    lethal = find_lethal(orbit, rng)
    ts = [t for _, t in lethal]
    print(f"lethal perturbed states found: {len(lethal)}; raw halt "
          f"times min/median/max: {min(ts)}/{sorted(ts)[len(ts)//2]}/"
          f"{max(ts)} steps")

    honest = Honest(orbit)
    print("honest provers:", play(honest, honest, K, 16, rng))

    print(f"{'r':>8} {'accept':>8} {'(1-1/K)^r':>10}  trials")
    for r, trials in ((64, 1000), (4096, 300), (65536, 40),
                      (524288, 10), (2097152, 4)):
        n_acc = 0
        for _ in range(trials):
            f = SeamForger(orbit, rng.randrange(K - 1),
                           lethal[rng.randrange(len(lethal))][0])
            acc, _w = play(f, f, K, r, rng)
            n_acc += acc
        print(f"{r:>8} {n_acc/trials:>8.3f} {(1-1/K)**r:>10.4f}  "
              f"{trials}", flush=True)
