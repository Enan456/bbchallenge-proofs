"""Literal Python ports of this repository's Lean abstract orbits for the
four shared machines:

  dossier-2 / dossier-3 : `MetaState`, `metaStep`, `s0`, `entryTape`,
                          `Realizes`  (Dossier2RawTM.lean / Dossier3RawTM.lean)
  dossier-7 / dossier-27: the word engine `go` / `wstep` / `worbit`
                          (Dossier7RawTM.lean / Dossier27RawTM.lean)

Every function is a transcription of the Lean definition it names; the
Lean theorems (`meta_transport`, `wstep_faithful`, `safe*_nonhalting`)
are what make the empirical replay below meaningful.
"""
from collections import deque

from .rawtm import parse_tm


# =====================================================================
# dossier-2 / dossier-3 : five-integer meta-orbit
# =====================================================================
def d2_meta_step(s):
    """Dossier2RawTM.metaStep (verbatim)."""
    three, l, h1, h2, r = s
    if three:
        if l <= h1 and h1 + 4 <= h2 and h2 + 6 <= r and \
                (r - h2) % 2 == 0 and (h2 - h1) % 2 == 0:
            return (False, l, h1 + 6, h2 + 4, r + 1)
        if l <= h1 and h2 == h1 + 2 and h2 + 7 <= r and (r - h2) % 2 == 0:
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


def d3_meta_step(s):
    """Dossier3RawTM.metaStep (verbatim, the mirror)."""
    three, l, h1, h2, r = s
    if three:
        if h1 <= l and h2 <= h1 - 4 and r <= h2 - 6 and \
                (h2 - r) % 2 == 0 and (h1 - h2) % 2 == 0:
            return (False, l, h1 - 6, h2 - 4, r - 1)
        if h1 <= l and h2 == h1 - 2 and r <= h2 - 7 and (h2 - r) % 2 == 0:
            return (False, l, h1 - 9, r - 1, r - 2)
        return None
    if h2 == r + 1:
        if h1 <= l and r + 4 <= h1:
            return (False, l, h1, r + 2, r - 1)
        return None
    if h2 == r + 3:
        if (h1 - r) % 2 == 1:
            if h1 <= l and r <= h1 - 7:
                return (False, l, h1 - 6, r - 1, r - 2)
            return None
        if (l - h1) % 2 == 1:
            if h1 <= l - 3 and r <= h1 - 6:
                return (False, l + 1, l - 5, h1 - 4, r - 1)
            return None
        if h1 <= l - 5 and r <= h1 - 6:
            return (False, l + 3, l - 6, h1 - 4, r - 1)
        return None
    if h1 <= l and h2 <= h1 - 1 and r + 4 <= h2:
        return (True, l, h1, h2, r - 1)
    return None


def _hole_tape_ones(lo, hi, holes):
    """holeTape lo hi a b c d as the set of cells reading 1."""
    return {q for q in range(lo, hi + 1) if q not in holes}


def d2_entry_ones(s):
    """Dossier2RawTM.entryTape as a set of 1-cells."""
    three, l, h1, h2, r = s
    if three:
        return _hole_tape_ones(l, r - 1, {h1, h2, r - 3})
    return _hole_tape_ones(l, r - 1, {h1, h2})


def d3_entry_ones(s):
    """Dossier3RawTM.entryTape (mirror) as a set of 1-cells."""
    three, l, h1, h2, r = s
    if three:
        return _hole_tape_ones(r + 1, l, {h1, h2, r + 3})
    return _hole_tape_ones(r + 1, l, {h1, h2})


class MetaOrbit:
    """Realizes-checker for the D2/D3 meta orbit on a raw trace."""
    SPECS = {
        'd2': dict(step=d2_meta_step, entry=d2_entry_ones, s0=(False, -8, -2, 12, 13),
                   state='D', anchor_step=235),
        'd3': dict(step=d3_meta_step, entry=d3_entry_ones, s0=(False, 17, 11, -39, -40),
                   state='E', anchor_step=2044),
    }

    def __init__(self, key):
        spec = self.SPECS[key]
        self.step = spec['step']
        self.entry = spec['entry']
        self.state = spec['state']
        self.anchor_step = spec['anchor_step']
        self.cur = spec['s0']
        self.cur_ones = self.entry(self.cur)
        self.n_realized = 0
        self.realized_at = []     # raw step of each realization
        self.dead = False

    def realizes(self, sim):
        return (sim.state == self.state and sim.head == self.cur[4]
                and sim.ones() == self.cur_ones)

    def observe(self, sim):
        """Call once per raw step BEFORE stepping (sim.t = current time)."""
        if self.dead or sim.state != self.state or sim.head != self.cur[4]:
            return
        if sim.ones() != self.cur_ones:
            return
        self.n_realized += 1
        self.realized_at.append(sim.t)
        nxt = self.step(self.cur)
        if nxt is None:
            self.dead = True
            return
        self.cur = nxt
        self.cur_ones = self.entry(nxt)


# =====================================================================
# dossier-7 / dossier-27 : the single-raw-step word engine
# =====================================================================
class WordEngine:
    """`go` / `wstep` / `worbit` for the left-growing machines.  em[0] is
    the cell just below the head (nearest first), rest[0] the head cell;
    push = right move; arrival = pop below the base (fresh left extreme).
    `probe_fatal(st, r, em)` encodes the machine's fail-closed probe."""
    SPECS = {
        'd7': dict(code='1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA',
                   # fatal C-probe: C reads 0 with no 1 guard on its left
                   probe=lambda st, r, em: st == 'C' and r == 0 and not (em and em[0] == 1),
                   raw_probe=('C', 0, 1)),   # state C reading 0 => left neighbour must be 1
        'd27': dict(code='1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA',
                    probe=lambda st, r, em: False,   # only the E1 halt itself
                    raw_probe=('E', 1, None)),        # state E must never read 1
    }

    def __init__(self, key):
        spec = self.SPECS[key]
        self.tbl = parse_tm(spec['code'])
        self.probe = spec['probe']
        self.raw_probe = spec['raw_probe']

    def micro(self, st, em, rest):
        r = rest[0] if rest else 0
        tr = self.tbl[(st, r)]
        if tr is None:
            return None
        if self.probe(st, r, em):
            return None
        wv, d, ns = tr
        if rest:
            rest.popleft()
        if d == 'R':
            em.appendleft(wv)
            return ('cont', ns)
        if em:
            rest.appendleft(wv)
            rest.appendleft(em.popleft())
            return ('cont', ns)
        rest.appendleft(wv)
        rest.appendleft(0)
        return ('arrival', ns, list(rest))

    @staticmethod
    def wfuel(w):
        return 64 * (len(w) + 64) * (len(w) + 64)

    def wstep(self, st, w):
        fuel = self.wfuel(w)
        em, rest = deque(), deque(w)
        dt = 0
        while fuel > 0:
            fuel -= 1
            out = self.micro(st, em, rest)
            if out is None:
                return None
            dt += 1
            if out[0] == 'arrival':
                return (out[1], tuple(out[2]), dt)
            st = out[1]
        return None


def eqw(u, v):
    n = max(len(u), len(v))
    return all((u[i] if i < len(u) else 0) == (v[i] if i < len(v) else 0)
               for i in range(n))


class WordOrbit:
    """Replays `worbit` against the raw fresh-left-extreme records."""

    def __init__(self, key):
        self.eng = WordEngine(key)
        self.st, self.w = 'A', ()
        self.t_pred = 0          # cumulative predicted raw step of next record
        self.lo = 0
        self.n_records = 0
        self.dead = False
        self.mismatch = None
        self.max_gap = 0
        self.max_word = 0

    def observe(self, sim):
        if self.dead or self.mismatch:
            return
        if sim.head >= self.lo:
            return
        self.lo = sim.head
        out = self.eng.wstep(self.st, self.w)
        if out is None:
            self.dead = True
            return
        st, w, dt = out
        self.t_pred += dt
        rw = tuple(sim.tape.get(x, 0) for x in range(sim.head, max(sim.tape) + 1))
        if self.t_pred != sim.t or st != sim.state or not eqw(w, rw):
            self.mismatch = (self.n_records + 1, sim.t, self.t_pred, st, sim.state)
            return
        self.st, self.w = st, w
        self.n_records += 1
        self.max_gap = max(self.max_gap, dt)
        self.max_word = max(self.max_word, len(w))
