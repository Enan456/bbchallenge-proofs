from __future__ import annotations

import math

import pytest

from qgkit.bb6.geometry.charts import h2_chart, log_chart, simplex_chart
from qgkit.bb6.geometry.events import antihydra_events, record_events

ANTIHYDRA = "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"


def test_antihydra_event_zero_matches_lean_eorbit():
    """Event 0 must be the Lean `eorbit 0 = some ⟨2, 1, 11⟩` with b = 12."""
    ev = next(antihydra_events(1))
    assert (ev["b"], ev["heads"]) == (12, 2)
    assert (ev["a"], ev["m"], ev["c"]) == (2, 1, 11)
    assert ev["rule"] == "merge"


def test_antihydra_hydra_recurrence():
    """b follows H(b) = b + b//2 and heads follows +2/-1 by parity."""
    evs = list(antihydra_events(9))
    bs = [e["b"] for e in evs]
    assert bs == [12, 18, 27, 40, 60, 90, 135, 202, 303]
    for prev, cur in zip(evs, evs[1:]):
        assert cur["b"] == prev["b"] + prev["b"] // 2
        expected = prev["heads"] + (2 if prev["b"] % 2 == 0 else -1)
        assert cur["heads"] == expected


def test_antihydra_boundary_triple_consistency():
    """Reconstructed (m, c) always satisfies the boundary invariants proved
    in Lean: m ∈ {1, 2} and c ≡ 2 (mod 3), with b = m + 2*(c-2)//3 + 5."""
    for ev in antihydra_events(500):
        assert ev["m"] in (1, 2)
        assert ev["c"] % 3 == 2
        assert ev["b"] == ev["m"] + 2 * ((ev["c"] - 2) // 3) + 5


def test_antihydra_acceleration_is_real():
    """The certified event-skip covers many raw steps per event and the
    cumulative raw cost grows superlinearly in events."""
    evs = list(antihydra_events(200))
    assert all(e["raw_steps"] > 0 for e in evs)
    assert evs[-1]["raw_steps"] > evs[0]["raw_steps"] * 100


def test_record_events_antihydra_smoke():
    halted, stop_step, events, n_records = record_events(
        ANTIHYDRA, steps=50_000, cap=500)
    assert not halted
    assert n_records > 0
    assert events, "Antihydra records should show near-collapse events"
    assert all(ev["type"] for ev in events)


def test_charts_basic():
    assert log_chart([0, 1]) == [0.0, math.log(2)]
    assert simplex_chart([1, 1, 2]) == [0.25, 0.25, 0.5]
    assert simplex_chart([0, 0, 0]) is None
    x, y = h2_chart([3, 1, 1])
    assert x == pytest.approx(2 / 5)
    assert y == pytest.approx(math.log1p(5))
