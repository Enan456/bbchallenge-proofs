"""Differential parity test: Lean's proved `step` semantics vs an independent
Python reference simulator (plan 1, task 2).

The Lean side is `packages/dossier1`'s `trace` executable, which iterates
the *proved* `step` function from `blankStart` and prints one line per step:
``index state head window`` with ``window`` = the 33 cells [head-16, head+16].

The Python side re-implements standard-format TM semantics from scratch in
~30 lines (deliberately independent of both the Lean code and qgkit), parses
the same machine codes, and emits the identical format.  Byte-equality of
the traces is the test.

Run: python3 -m pytest tests/lean_parity/ -v
The test skips (does not fail) if the Lean executable has not been built:
    cd packages/dossier1 && lake build trace
"""

from __future__ import annotations

import pathlib
import subprocess

import pytest

REPO = pathlib.Path(__file__).resolve().parents[2]
TRACE_BIN = REPO / "packages" / "dossier1" / ".lake" / "build" / "bin" / "trace"

MACHINES = {
    "antihydra": "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA",
    "dossier1": "1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB",
}

STEPS = 2000


def parse(code: str):
    """Standard format -> {(state, sym): (write, move, next) | None}."""
    table = {}
    for i, group in enumerate(code.split("_")):
        state = "ABCDEF"[i]
        for sym in (0, 1):
            entry = group[3 * sym : 3 * sym + 3]
            if entry == "---":
                table[(state, sym)] = None
            else:
                write = int(entry[0])
                move = 1 if entry[1] == "R" else -1
                table[(state, sym)] = (write, move, entry[2])
    return table


def reference_trace(code: str, steps: int):
    """Yield lines in the trace executable's exact format."""
    table = parse(code)
    tape: dict[int, int] = {}
    head = 0
    state = "A"
    for i in range(steps):
        window = "".join(str(tape.get(head - 16 + k, 0)) for k in range(33))
        yield f"{i} {state} {head} {window}"
        entry = table[(state, tape.get(head, 0))]
        if entry is None:
            yield f"{i + 1} HALT"
            return
        write, move, nxt = entry
        tape[head] = write
        head += move
        state = nxt


@pytest.fixture(scope="module")
def trace_bin():
    if not TRACE_BIN.exists():
        pytest.skip(
            "Lean trace executable not built "
            "(cd packages/dossier1 && lake build trace)"
        )
    return TRACE_BIN


@pytest.mark.parametrize("machine", sorted(MACHINES))
def test_trace_parity(trace_bin, machine):
    lean = subprocess.run(
        [str(trace_bin), machine, str(STEPS)],
        capture_output=True,
        text=True,
        check=True,
        timeout=600,
    )
    lean_lines = lean.stdout.strip().splitlines()
    ref_lines = list(reference_trace(MACHINES[machine], STEPS))
    assert len(lean_lines) == len(ref_lines) == STEPS  # neither halted
    for i, (a, b) in enumerate(zip(lean_lines, ref_lines)):
        assert a == b, f"{machine} diverges at step {i}:\n  lean: {a}\n  ref:  {b}"


def test_reference_detects_halter():
    """Control: the reference stepper sees BB(2)'s halt at the right step."""
    lines = list(reference_trace("1RB1LB_1LA---", 100))
    assert lines[-1].endswith("HALT")
    assert lines[-1].startswith("6 ")  # BB(2) halts on its 6th step


def test_startup_anchors():
    """The Lean-proved startup records appear at the right steps."""
    anti = list(reference_trace(MACHINES["antihydra"], 70))
    # startup_run: stepN 62 blankStart = some ⟨State.B, 6, startTape⟩
    assert anti[62].startswith("62 B 6 ")
    doss = list(reference_trace(MACHINES["dossier1"], 40))
    # step35: the dossier-1 35-step startup ends in state E at head 5
    assert doss[35].startswith("35 E 5 ")
