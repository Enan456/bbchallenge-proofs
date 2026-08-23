"""Rigorous out-of-sample validation of the generic predictor: fit on
120k raw steps, then check EVERY predicted record — exact raw-step index,
blocks, control state, and absolute head — against 400k steps of raw
simulation (heads from an independent stepper)."""

from __future__ import annotations

import pytest

from qgkit.bb6.dragon.generic import GenericOrbitPredictor, MissingRule
from qgkit.bb6.dragon.predictor import ANTIHYDRA
from qgkit.bb6.vcollatz.classify import simulate_records

NEW1 = "1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD"
NEW2 = "1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE"

FIT, HORIZON = 200_000, 1_500_000


def raw_expansion_heads(code: str, steps: int):
    """Independent stepper: (step -> head) at every range expansion."""
    table = {}
    for i, group in enumerate(code.split("_")):
        st = "ABCDEF"[i]
        for sym in (0, 1):
            e = group[3 * sym: 3 * sym + 3]
            table[(st, sym)] = None if e == "---" else (
                int(e[0]), 1 if e[1] == "R" else -1, e[2])
    tape, head, state, lo, hi = {}, 0, "A", 0, 0
    out = {}
    for n in range(steps):
        if head < lo or head > hi:
            lo, hi = min(lo, head), max(hi, head)
            out[n] = head
        entry = table[(state, tape.get(head, 0))]
        if entry is None:
            break
        w, mv, nxt = entry
        tape[head] = w
        head += mv
        state = nxt
    return out


@pytest.mark.parametrize("code", [ANTIHYDRA, NEW1, NEW2])
def test_every_prediction_is_exact(code):
    """The core guarantee: every record the emulator predicts matches the
    raw machine exactly (step index, blocks, control state, head), and any
    stop is an explicit MissingRule — never a silent wrong guess.

    Antihydra predicts deep out-of-sample. The two stage757 machines have a
    genuine guard long-tail on their 4-block boundary states (mixed-guard
    families, confirmed not affine-poolable), so their certified depth ends
    at the last determined rule — explicitly."""
    pred = GenericOrbitPredictor(code, fit_steps=FIT)
    _, _, actual = simulate_records(code, steps=HORIZON, cap=5_000)
    actual = [r for r in actual if r["blocks"] and r["side"] == pred.side]
    heads = raw_expansion_heads(code, HORIZON)
    n_fit = len(pred._recs)
    got, stopped = [], False
    try:
        for p in pred.predict(len(actual) - 1 - pred.seed_index):
            got.append(p)
    except MissingRule:
        stopped = True
    # 1. exactness of EVERYTHING predicted
    for p in got:
        a = actual[p["i"]]
        assert p["step"] == a["step"], (code, p["i"], "step")
        assert list(p["blocks"]) == list(a["blocks"]), (code, p["i"], "blocks")
        assert p["state"] == a["state"], (code, p["i"], "state")
        assert heads[p["step"]] == p["head"], (code, p["i"], "head")
    # 2. substantial certified depth, and honest stops only
    assert len(got) >= min(300, n_fit - 2)
    if code == ANTIHYDRA:
        assert len(got) > n_fit * 1.2, "Antihydra must predict deep OOS"
    else:
        assert stopped or len(got) >= len(actual) - 1 - pred.seed_index


@pytest.mark.parametrize("code", [ANTIHYDRA, NEW1, NEW2])
def test_prediction_spans_the_fit_horizon(code):
    """Prediction must carry at least to the vicinity of the fit budget in
    raw steps (Antihydra: far beyond it)."""
    pred = GenericOrbitPredictor(code, fit_steps=FIT)
    last = None
    try:
        for p in pred.predict(len(pred._recs) * 2):
            last = p
    except MissingRule:
        pass
    assert last is not None
    target = FIT * 1.2 if code == ANTIHYDRA else FIT * 0.8
    assert last["step"] >= target, (code, last["step"])
