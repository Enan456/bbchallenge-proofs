"""Cross-verification of Google DeepMind's `cryptids` BB(6) accelerations
against this repository's Lean orbits on the four shared machines
(see qgkit/bb6/gdm_cross/).  Short horizons here; the 20M-step runs are
produced by `python -m qgkit.bb6.gdm_cross --md ...`."""
import os
import random
import sys

import pytest

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from qgkit.bb6.gdm_cross.gdm_rules import D2, D3, D7, D27, MACHINES  # noqa: E402
from qgkit.bb6.gdm_cross.crosscheck import run, verdict  # noqa: E402
from qgkit.bb6.gdm_cross.our_rules import d2_meta_step  # noqa: E402
from qgkit.bb6.gdm_cross.rawtm import RawSim  # noqa: E402

HORIZON = int(os.environ.get('GDM_CROSS_HORIZON', '400000'))


# ------------------------------------------------------------ Google ports
def test_d2_next_matches_docstring():
    # C_1(2,2,0): b+1, c=0  ->  C_0(a+2, 0, b)
    assert D2.next(('C1', 2, 2, 0)) == ('C0', 4, 0, 1)
    assert D2.next(('C0', 4, 0, 1)) == ('C1', 2, 2, 5)
    assert D2.next(('C0', 7, 0, 0)) is None
    assert D2.next(('C1', 0, 0, 5)) == ('C1', 2, 3, 3)


def test_d3_next_matches_docstring():
    # docstring: C(2k, 2k, f) -> C(2, 2, f+6k-6) ; Lean (k+1,m+1,f) with k=m -> C 0 0 (f+6(k+1))
    assert D3.next(('C', 2, 2, 7)) == ('C', 0, 0, 7 + 12)
    assert D3.next(('C', 0, 0, 3)) is None
    assert D3.next(('C', 0, 1, 3)) is None
    assert D3.next(('C', 0, 2, 4)) == ('C', 5, 2, 4)
    assert D3.next(('C', 0, 2, 5)) == ('C', 7, 0, 1)


def test_d7_next_matches_docstring():
    assert D7.next(('C3', 4, 0, 0)) == ('C3', 2, 3, 0)
    assert D7.next(('C3', 0, 3, 0)) == ('M3', False, 3, 0)
    assert D7.next(('M3', False, 3, 0)) == ('L3', False, 3)
    assert D7.next(('L3', False, 3)) is None        # L(0, 2k, 3) -> Halt? b odd & a=0 -> none
    assert D7.next(('L3', False, 4)) == ('C3', 0, 0, 5)
    assert D7.next(('L6', True, 0)) == ('C3', 6, 0, 3)


def test_d27_next_small_cases():
    assert D27.next(('R1', 0)) == ('R1', 4)
    assert D27.next(('R1', 1)) == ('R1', 6)
    assert D27.next(('R1', 9)) == ('R1', 14)
    assert D27.next(('R2', 0)) == ('R1', 4)
    assert D27.next(('S6', 0)) == ('R1', 9)
    assert D27.next(('S6', 1)) == D27.next_HubTail('r_3', 0, 2) == ('R2', 23)
    # HubTail unrolling: w = 7 -> a += 31, remainder 2
    assert D27.next_HubTail('r_R2', 0, 7) == ('Q', 31 + 19)


@pytest.mark.parametrize('key', list(MACHINES))
def test_decode_inverts_encode(key):
    M = MACHINES[key]
    rng = random.Random(1)
    for _ in range(300):
        if key == 'd2':
            s = (rng.choice(['C0', 'C1']), rng.randrange(8), rng.randrange(8), rng.randrange(8))
        elif key == 'd3':
            s = ('C', rng.randrange(8), rng.randrange(8), rng.randrange(8))
        elif key == 'd7':
            kind = rng.choice(['C3', 'C6', 'M3', 'M6', 'L3', 'L6'])
            if kind in ('C3', 'C6'):
                s = (kind, rng.randrange(8), rng.randrange(8), rng.randrange(6))
            elif kind in ('M3', 'M6'):
                s = (kind, rng.choice([False, True]), rng.randrange(8), rng.randrange(6))
            else:
                s = (kind, rng.choice([False, True]), rng.randrange(8))
        else:
            s = (rng.choice(list(D27.SUFFIX)), rng.randrange(8))
        st, left, right = M.encode(s)
        d = M.decode(st, left, right)
        assert d is not None, (s, st, left, right)
        assert M.canon(d) == M.canon(s), (s, d)


def test_d2_meta_step_agrees_with_existing_port():
    """Independent port in qgkit/bb6/halting_game23.py (2026-08)."""
    from qgkit.bb6.halting_game23 import meta_step
    rng = random.Random(7)
    for _ in range(5000):
        l = rng.randrange(-30, 0)
        h1 = l + rng.randrange(0, 12)
        h2 = h1 + rng.randrange(0, 12)
        r = h2 + rng.randrange(0, 12)
        s = (rng.random() < 0.5, l, h1, h2, r)
        assert d2_meta_step(s) == meta_step(*s)


# ------------------------------------------------------------ raw sim sanity
def test_rawsim_canonical_form():
    sim = RawSim(D2.CODE)
    for _ in range(100):
        sim.step()
    tape = sim.tape
    left = sim.left_nearest_first()
    right = sim.right_head_first()
    for i, v in enumerate(left):
        assert tape.get(sim.head - 1 - i, 0) == v
    for i, v in enumerate(right):
        assert tape.get(sim.head + i, 0) == v
    assert not left or left[-1] == 1
    assert not right or right[-1] == 1


# ------------------------------------------------------------ the cross-check
@pytest.mark.parametrize('key', list(MACHINES))
def test_cross_verification(key):
    r = run(key, HORIZON)
    assert verdict(r) == [], r
    # d27's R2 rule triples the block count per abstract step, so hits are
    # sparse (3 in the first 400k raw steps); the others hit hundreds of times.
    assert r['gdm']['hits'] >= (3 if key == 'd27' else 20), r['gdm']
    o = r['ours']
    assert (o['realized'] if o['kind'] == 'metaOrbit' else o['records']) >= 20, o
