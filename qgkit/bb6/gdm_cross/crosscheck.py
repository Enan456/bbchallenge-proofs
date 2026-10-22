"""One raw run, two abstract replays.

For a machine key in {d2, d3, d7, d27}:

  * `GdmOrbit`  replays Google DeepMind's `start / encode / next`: every
    time the raw configuration equals `encode(expected)` the expected
    state advances by `next`.  Checks: the first hit is `start` at the
    documented raw step; every subsequent expected configuration is hit
    (ReachesPlus); `next = none` never fires before the raw machine
    halts; and, as a stricter *first-hit* diagnostic, no configuration
    decoding to a different family member is met before the expected
    one.
  * `MetaOrbit` / `WordOrbit` replay this repository's Lean orbit
    (`metaOrbit` for d2/d3, `worbit` for d7/d27) against the same trace.

Both replays are fail-closed: an orbit that returns `none` is reported
as *dead* (which, by the respective theorems, would mean a halt).
"""
import time

from .gdm_rules import MACHINES
from .our_rules import MetaOrbit, WordOrbit
from .rawtm import RawSim


class GdmOrbit:
    def __init__(self, M):
        self.M = M
        self.expect = M.start
        self.exp = M.encode(M.start)
        self.hits = []
        self.started_at = None
        self.dead_at = None          # raw step at which next() returned none
        self.skipped = 0             # canonical configs met before the expected one
        self.skipped_example = None
        self.max_gap = 0
        self._window = self._mk_window(self.exp)

    @staticmethod
    def _mk_window(enc):
        _, left, right = enc
        def cell(side, i):
            return side[i] if i < len(side) else 0
        return (cell(right, 0), cell(left, 0), cell(right, 1), cell(left, 1), cell(right, 2))

    def _window_ok(self, sim):
        t, h = sim.tape, sim.head
        w = self._window
        return (t.get(h, 0) == w[0] and t.get(h - 1, 0) == w[1] and
                t.get(h + 1, 0) == w[2] and t.get(h - 2, 0) == w[3] and
                t.get(h + 2, 0) == w[4])

    def observe(self, sim):
        if self.dead_at is not None:
            return
        st, left, right = self.exp
        if sim.state != st or not self._window_ok(sim):
            return
        rl = sim.left_nearest_first()
        if rl != left:
            self._first_hit_check(sim, rl, None)
            return
        rr = sim.right_head_first()
        if rr != right:
            self._first_hit_check(sim, rl, rr)
            return
        # hit
        if self.hits:
            self.max_gap = max(self.max_gap, sim.t - self.hits[-1])
        self.hits.append(sim.t)
        if self.started_at is None:
            self.started_at = sim.t
        nxt = self.M.next(self.expect)
        if nxt is None:
            self.dead_at = sim.t
            return
        self.expect = nxt
        self.exp = self.M.encode(nxt)
        self._window = self._mk_window(self.exp)

    def _first_hit_check(self, sim, rl, rr):
        """Diagnostic only: Google's `next` may compose several raw sweeps
        into one abstract step (IsValidAcceleration needs ReachesPlus,
        not first-hit), so the trace can pass through other members of
        the canonical family first.  We count them."""
        if self.started_at is None:
            return
        if rr is None:
            rr = sim.right_head_first()
        d = self.M.decode(sim.state, rl, rr)
        if d is None:
            return
        if self.M.canon(d) != self.M.canon(self.expect):
            self.skipped += 1
            if self.skipped_example is None:
                self.skipped_example = (sim.t, d, self.expect)


def make_ours(key):
    return MetaOrbit(key) if key in ('d2', 'd3') else WordOrbit(key)


def run(key, horizon, progress=None):
    M = MACHINES[key]
    sim = RawSim(M.CODE)
    g = GdmOrbit(M)
    o = make_ours(key)
    t0 = time.time()
    halted_at = None
    for t in range(horizon):
        g.observe(sim)
        o.observe(sim)
        if not sim.step():
            halted_at = t
            break
        if progress and t % progress == 0 and t:
            print(f'  [{key}] t={t:,} gdm_hits={len(g.hits):,} ours={_ours_count(o):,}',
                  flush=True)
    secs = time.time() - t0
    return summarize(key, M, sim, g, o, horizon, halted_at, secs)


def _ours_count(o):
    return o.n_realized if isinstance(o, MetaOrbit) else o.n_records


def summarize(key, M, sim, g, o, horizon, halted_at, secs):
    ours = {}
    if isinstance(o, MetaOrbit):
        ours = dict(kind='metaOrbit', realized=o.n_realized,
                    anchor_expected=o.anchor_step,
                    anchor_observed=o.realized_at[0] if o.realized_at else None,
                    last_realized_at=o.realized_at[-1] if o.realized_at else None,
                    max_gap=max((b - a for a, b in zip(o.realized_at, o.realized_at[1:])), default=0),
                    dead=o.dead, final_state=list(o.cur))
    else:
        ours = dict(kind='worbit', records=o.n_records, dead=o.dead,
                    mismatch=o.mismatch, max_gap=o.max_gap, max_word=o.max_word)
    return dict(
        machine=key, code=M.CODE, horizon=horizon, raw_steps=sim.t,
        halted_at=halted_at, seconds=round(secs, 1),
        gdm=dict(start=list(M.start), start_step_documented=M.START_STEP,
                 start_step_docstring=getattr(M, 'DOCSTRING_START_STEP', M.START_STEP),
                 start_step_observed=g.started_at, hits=len(g.hits),
                 last_hit_at=g.hits[-1] if g.hits else None,
                 dead_at=g.dead_at, max_gap=g.max_gap,
                 skipped_intermediate=g.skipped, skipped_example=g.skipped_example,
                 final_expected=list(g.expect)),
        ours=ours,
    )


def verdict(r):
    """Hard pass/fail conditions."""
    g, o = r['gdm'], r['ours']
    problems = []
    if g['start_step_observed'] != g['start_step_documented']:
        problems.append(f"gdm start at {g['start_step_observed']} != documented {g['start_step_documented']}")
    if g['hits'] < 2:
        problems.append('gdm: fewer than 2 canonical hits')
    if g['dead_at'] is not None and r['halted_at'] is None:
        problems.append(f"gdm next=none at t={g['dead_at']} but raw did not halt")
    if g['last_hit_at'] is not None:
        idle = r['raw_steps'] - g['last_hit_at']
        if idle > max(200_000, 20 * g['max_gap']):
            problems.append(f"gdm stalled: no hit for {idle:,} raw steps (max gap {g['max_gap']:,})")
    if o['kind'] == 'metaOrbit':
        if o['anchor_observed'] != o['anchor_expected']:
            problems.append(f"ours anchor at {o['anchor_observed']} != Lean anchor_run {o['anchor_expected']}")
        if o['dead']:
            problems.append('ours: metaOrbit died')
        if o['realized'] < 2:
            problems.append('ours: fewer than 2 realizations')
        elif r['raw_steps'] - o['last_realized_at'] > max(200_000, 20 * o['max_gap']):
            problems.append('ours: metaOrbit stalled')
    else:
        if o['dead']:
            problems.append('ours: worbit died')
        if o['mismatch']:
            problems.append(f"ours: record mismatch {o['mismatch']}")
        if o['records'] < 2:
            problems.append('ours: fewer than 2 records')
    if r['halted_at'] is not None:
        problems.append(f"RAW MACHINE HALTED at {r['halted_at']}")
    return problems


NAMES = {'d2': 'dossier-2', 'd3': 'dossier-3', 'd7': 'dossier-7', 'd27': 'dossier-27'}
OUR_THM = {
    'd2': '`dossier2_nonhalting_of_safeMetaOrbit : SafeMetaOrbit → ¬ RawHalts blankStart`',
    'd3': '`dossier3_nonhalting_of_safeMetaOrbit : SafeMetaOrbit → ¬ RawHalts blankStart`',
    'd7': '`safeD7Orbit_nonhalting : SafeD7Orbit → ¬ RawHalts blankStart`',
    'd27': '`safeD27Orbit_nonhalting : SafeD27Orbit → ¬ RawHalts blankStart`',
}
GDM_THM = '`isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start` (+ `is_closed_pattern_set`, `has_collatz_reduction`, `is_valid_acceleration`)'


def markdown(r):
    g, o = r['gdm'], r['ours']
    probs = verdict(r)
    lines = [f"### {NAMES[r['machine']]}  `{r['code']}`", '']
    lines.append(f"**Verdict:** {'PASS' if not probs else 'FAIL: ' + '; '.join(probs)}")
    lines.append('')
    lines.append(f"Raw horizon: {r['raw_steps']:,} steps ({r['seconds']}s); raw machine halted: "
                 f"{'no' if r['halted_at'] is None else 'YES at ' + str(r['halted_at'])}.")
    lines.append('')
    lines.append('| side | theorem replayed | abstract steps hit | first hit (raw step) | last hit (raw step) | fail-closed death |')
    lines.append('|---|---|---|---|---|---|')
    doc = (f"(docstring says {g['start_step_docstring']}; Lean proof carries no count)"
           if g['start_step_docstring'] != g['start_step_documented']
           else f"(documented {g['start_step_documented']})")
    lines.append(f"| Google DeepMind | {GDM_THM} | {g['hits']:,} | {g['start_step_observed']} "
                 f"{doc} | {g['last_hit_at']:,} | "
                 f"{'none' if g['dead_at'] is None else g['dead_at']} |")
    if o['kind'] == 'metaOrbit':
        lines.append(f"| this repo | {OUR_THM[r['machine']]} | {o['realized']:,} | {o['anchor_observed']} "
                     f"(Lean `anchor_run` {o['anchor_expected']}) | {o['last_realized_at']:,} | "
                     f"{'none' if not o['dead'] else 'DIED'} |")
    else:
        lines.append(f"| this repo | {OUR_THM[r['machine']]} | {o['records']:,} records | 0 (anchor `(A, [])`) | "
                     f"— | {'none' if not o['dead'] else 'DIED'} |")
    lines.append('')
    extra = []
    if o['kind'] == 'worbit':
        extra.append(f"word orbit: max record gap {o['max_gap']:,} raw steps, max word length {o['max_word']:,}")
    extra.append(f"Google `next` granularity: {g['skipped_intermediate']:,} intermediate canonical "
                 f"configurations were passed through before the expected one (multi-sweep acceleration; "
                 f"allowed by `IsValidAcceleration`), first example {g['skipped_example']}; "
                 f"max raw gap between hits {g['max_gap']:,}")
    extra.append(f"Google final expected state: `{g['final_expected']}`")
    if o['kind'] == 'metaOrbit':
        extra.append(f"this repo final meta state `(three, l, h1, h2, r)`: `{o['final_state']}`")
    for e in extra:
        lines.append(f'- {e}')
    lines.append('')
    return '\n'.join(lines)
