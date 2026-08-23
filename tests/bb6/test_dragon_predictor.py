"""Differential validation of the predictive orbit emulator: every
predicted record (raw step index, head position, block layout) must match
the actual raw machine exactly."""

from __future__ import annotations

import pytest

from qgkit.bb6.dragon.predictor import ANTIHYDRA, OrbitPredictor


def raw_sim(code: str, steps: int):
    """Minimal raw stepper; yields (step, state, head) and keeps the tape."""
    table = {}
    for i, group in enumerate(code.split("_")):
        st = "ABCDEF"[i]
        for sym in (0, 1):
            e = group[3 * sym: 3 * sym + 3]
            table[(st, sym)] = None if e == "---" else (
                int(e[0]), 1 if e[1] == "R" else -1, e[2])
    tape: dict[int, int] = {}
    head, state = 0, "A"
    snap = {}
    for n in range(steps + 1):
        snap[n] = (state, head)
        entry = table[(state, tape.get(head, 0))]
        if entry is None:
            break
        w, mv, nxt = entry
        tape[head] = w
        head += mv
        state = nxt
    return snap, tape


N_RECORDS = 60          # deep enough to cross many drops and merges
pred = OrbitPredictor()
records = [pred.record(r) for r in range(N_RECORDS)]
MAX_STEP = records[-1]["raw_step"]


@pytest.fixture(scope="module")
def sim():
    return raw_sim(ANTIHYDRA, MAX_STEP)


def test_predicted_records_match_machine(sim):
    snap, _ = sim
    for rec in records:
        state, head = snap[rec["raw_step"]]
        assert (state, head) == (rec["state"], rec["head"]), (
            f"record {rec['record']}: predicted ({rec['state']},"
            f" {rec['head']}) at step {rec['raw_step']}, machine at"
            f" ({state}, {head})")


def test_predicted_block_layout(sim):
    """At the final tested record the tape must spell the Realizes grammar:
    counter block, gap, m block, gap, c block, blanks beyond."""
    _, tape = sim
    rec = records[-1]
    p, a, m, c = rec["anchor"], rec["a"], rec["m"], rec["c"]
    for i in range(a):
        assert tape.get(p - i, 0) == 1, f"counter cell {p - i}"
    assert tape.get(p + 1, 0) == 0
    for i in range(m):
        assert tape.get(p + 2 + i, 0) == 1, f"m cell {p + 2 + i}"
    assert tape.get(p + 2 + m, 0) == 0
    for i in range(c):
        assert tape.get(p + 3 + m + i, 0) == 1, f"c cell {p + 3 + m + i}"
    assert tape.get(p - a, 0) == 0 and tape.get(p + 3 + m + c, 0) == 0


def test_record_at_step_brackets(sim):
    target = records[30]["raw_step"] + 1
    rec = pred.record_at_step(target)
    assert rec["raw_step"] <= target < rec["next_record_step"]


def test_safe_horizon_positive():
    assert all(r["safe_horizon_events"] >= 1 for r in records)
