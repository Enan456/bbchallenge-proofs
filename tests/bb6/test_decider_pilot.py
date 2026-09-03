"""Soundness tests for the decider-pilot invariant searchers: known
invariants must be found, known non-invariants must be rejected."""

from __future__ import annotations

from fractions import Fraction

from qgkit.bb6.decider_pilot import (
    GuardedBranch, search_congruence, search_monotone, spec_replay)


def _br(n_in, n_out, sig, maps, cost=None):
    rule = {"maps": [tuple(Fraction(c) for c in m) for m in maps],
            "cost": tuple(Fraction(c) for c in (cost or (0,) * (n_in + 1)))}
    return GuardedBranch((n_in, n_out, tuple(sig)), rule)


def test_totality_hit_when_growth_keeps_coordinates_large():
    # x >= 3 -> x + 2: never leaves the covered region, m = 1 suffices
    branches = [_br(1, 1, (3,), [(1, 2)])]
    hit, _ = search_congruence(branches, [(5,)])
    assert hit is not None and hit["kind"] == "total" and hit["m"] == 1


def test_congruence_hit_requires_residue_refinement():
    # x >= 3 -> x - 2 can reach small values; only even orbits stay
    # inside {2} u {even large}, and x = 2 -> 6 recovers. Odd seeds
    # would reach 1, which no guard covers: m = 2 separates them.
    branches = [_br(1, 1, (3,), [(1, -2)]),
                _br(1, 1, (2,), [(0, 6)])]
    hit, _ = search_congruence(branches, [(4,)])
    assert hit is not None and hit["kind"] == "congruence" and hit["m"] == 2


def test_uncovered_orbit_rejected_at_every_modulus():
    # x >= 3 -> x - 2 with no rule at x = 1 or x = 2: every modulus
    # must fail (residues cannot exclude the reachable small values,
    # since both parities of large values occur from the odd seed).
    branches = [_br(1, 1, (3,), [(1, -2)])]
    hit, failures = search_congruence(branches, [(5,)])
    assert hit is None
    assert all(reason in ("uncovered", "breakdown")
               for reason, _ in failures.values())


def test_fractional_coefficients_disqualify_sharing_moduli():
    # x >= 3 -> x/2 + 9/2: the residue of the image mod 2 is not a
    # function of the residue of the input mod 2; the searcher must
    # reject m = 2 as unusable rather than guess.
    branches = [_br(1, 1, (3,), [(Fraction(1, 2), Fraction(9, 2))])]
    hit, failures = search_congruence(branches, [(3,)], moduli=(2,))
    assert hit is None and failures[2][0] == "modulus"


def test_monotone_hit_with_exclusion_link():
    # coordinate 0 grows under every applicable branch, and every
    # signature with x0 >= 3 is covered: fatal states need x0 < 3.
    branches = [_br(2, 2, (3, 3), [(1, 0, 1), (0, 1, 0)]),
                _br(2, 2, (3, 1), [(1, 0, 2), (0, 0, 5)]),
                _br(2, 2, (3, 2), [(2, 0, 0), (0, 1, 1)])]
    hits, reason = search_monotone(branches, [(4, 7)])
    assert reason is None
    assert any(h["coordinate"] == 0 for h in hits)


def test_monotone_rejects_rotation():
    branches = [_br(2, 2, (3, 3), [(0, 1, 0), (1, 0, 0)]),
                _br(2, 2, (3, 1), [(0, 0, 4), (1, 0, 0)]),
                _br(2, 2, (3, 2), [(0, 0, 4), (1, 0, 0)])]
    hits, reason = search_monotone(branches, [(4, 7)])
    assert hits == []


def test_monotone_requires_seed_floor():
    branches = [_br(1, 1, (3,), [(1, 1)]),
                _br(1, 1, (1,), [(0, 4)]),
                _br(1, 1, (2,), [(0, 4)])]
    hits, _ = search_monotone(branches, [(2,)])
    assert hits == []          # seed below the floor: no exclusion claim


def test_replay_reports_the_off_spec_witness():
    branches = [_br(1, 1, (3,), [(1, -2)])]
    outcome, iters, witness = spec_replay(branches, (9,))
    assert outcome == "uncovered" and witness in ((1,), (2,))
