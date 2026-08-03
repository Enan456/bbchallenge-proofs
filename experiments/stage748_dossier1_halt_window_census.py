"""Stage 748 -- bounded halt-window census for dossier-1 BB(6).

The census is empirical: it records every observed C0 -> F entry within the
chosen budget, but makes no unreachability claim beyond that bounded run.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
from collections import Counter
from pathlib import Path

from tqdm import tqdm

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))


CODE = "1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB"
OUT = Path(__file__).resolve().parent / "outputs" / "stage748"
STORED_EVENT_CAP = 200_000
EXACT_DIMENSION_EVENTS = 500_000
SAMPLED_DIMENSION_STRIDE = 100  # after the exact prefix: bounded RLE work
TOKEN = re.compile(r"^(---|[01][LR][A-F])$")


def parse(code: str) -> dict[tuple[int, int], tuple[int, int, int]]:
    """Parse the compact BB(6) code into the classify.py transition shape."""
    rows = code.split("_")
    if len(rows) != 6:
        raise ValueError(f"expected 6 rows, got {len(rows)}")
    tab: dict[tuple[int, int], tuple[int, int, int]] = {}
    for state, row in enumerate(rows):
        if len(row) != 6:
            raise ValueError(f"row {state} is not two three-character tokens: {row!r}")
        for sym, token in enumerate((row[:3], row[3:])):
            if not TOKEN.fullmatch(token):
                raise ValueError(f"invalid token {token!r}")
            if token == "---":
                continue
            write = int(token[0])
            direction = 1 if token[1] == "R" else -1
            next_state = ord(token[2]) - ord("A")
            tab[state, sym] = next_state, write, direction
    return tab


def one_runs(tape: dict[int, int], lo: int, hi: int) -> list[tuple[int, int]]:
    """Return inclusive intervals of maximal interior 1-runs."""
    runs: list[tuple[int, int]] = []
    pos = lo
    while pos <= hi:
        if not tape.get(pos, 0):
            pos += 1
            continue
        start = pos
        while pos <= hi and tape.get(pos, 0):
            pos += 1
        runs.append((start, pos - 1))
    return runs


def window9(tape: dict[int, int], head: int) -> str:
    return "".join(str(tape.get(pos, 0)) for pos in range(head - 4, head + 5))


def right_run_index(tape: dict[int, int], head: int, hi: int) -> int | None:
    """Index of the head-adjacent run counted from the right, without full RLE."""
    n_right_runs = 0
    in_run = False
    for pos in range(hi, head, -1):
        bit = bool(tape.get(pos, 0))
        if bit and not in_run:
            n_right_runs += 1
        in_run = bit
    if tape.get(head + 1, 0):
        return n_right_runs - 1
    if tape.get(head - 1, 0):
        return n_right_runs
    return None


def histogram_json(counter: Counter[int]) -> dict[str, int]:
    return {str(key): counter[key] for key in sorted(counter)}


def compact_histogram(counter: Counter[int], edge: int = 8) -> str:
    """A console-sized view; the JSON retains every histogram bin."""
    items = sorted(counter.items())
    shown = items if len(items) <= edge * 2 else items[:edge] + items[-edge:]
    body = ", ".join(f"{key}:{value}" for key, value in shown)
    middle = "" if len(items) <= edge * 2 else ", ..."
    return f"{len(items)} bins {{{body}{middle}}}"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--budget", type=int, default=100_000_000)
    args = ap.parse_args()
    if args.budget < 1:
        raise ValueError("--budget must be positive")

    tab = parse(CODE)
    # Dossier-1 verification: F is entered exclusively through C reading 0.
    f_entries = [(state, sym) for (state, sym), (ns, _, _) in tab.items() if ns == 5]
    assert f_entries == [(2, 0)], f"unexpected F-entry transitions: {f_entries}"
    assert tab[2, 0] == (5, 0, 1), f"C0 is not 0RF: {tab[2, 0]}"
    assert (5, 0) not in tab and tab[5, 1] == (1, 0, 1), "F row is not ---0RB"

    tape: dict[int, int] = {}
    head = 0
    state = 0
    lo = hi = 0
    raw_events: list[dict] = []
    window_counts: Counter[str] = Counter()
    window_right_run_counts: Counter[tuple[str, int | None]] = Counter()
    right_distances: Counter[int] = Counter()
    exact_dimension_counts: Counter[int] = Counter()
    sampled_dimension_counts: Counter[int] = Counter()
    total_f_entries = 0
    dimension_samples = 0
    assertion_held = True
    assertion_failure: dict | None = None
    halted = False
    stop_step = args.budget

    # This follows classify.simulate_records: read, lookup, write, advance state
    # and head, then update touched extents.  The C0 observation is necessarily
    # made immediately after the read and before applying that transition.
    for step in tqdm(range(args.budget), desc="stage748 BB(6) census", mininterval=5):
        sym = tape.get(head, 0)
        if state == 2 and sym == 0:
            total_f_entries += 1
            win = window9(tape, head)
            right_symbol = tape.get(head + 1, 0)
            try:
                assert right_symbol == 1, "C0 would enter F with F-read symbol 0"
            except AssertionError as exc:
                assertion_held = False
                assertion_failure = {"step": step, "head": head, "window": win,
                                     "head_plus_1": right_symbol, "reason": str(exc)}
                stop_step = step
                break

            right_distance = hi - head
            nearest_from_right = right_run_index(tape, head, hi)
            window_counts[win] += 1
            window_right_run_counts[win, nearest_from_right] += 1
            right_distances[right_distance] += 1

            exact = total_f_entries <= EXACT_DIMENSION_EVENTS
            sampled = (not exact and total_f_entries % SAMPLED_DIMENSION_STRIDE == 0)
            runs: list[tuple[int, int]] | None = None
            if exact or sampled or len(raw_events) < STORED_EVENT_CAP:
                runs = one_runs(tape, lo, hi)
            if exact:
                exact_dimension_counts[len(runs or [])] += 1
            elif sampled:
                sampled_dimension_counts[len(runs or [])] += 1
                dimension_samples += 1
            if len(raw_events) < STORED_EVENT_CAP:
                assert runs is not None
                adjacent = None
                for index, (start, end) in enumerate(runs):
                    if end == head - 1 or start == head + 1:
                        adjacent = index
                        break
                raw_events.append({
                    "step": step, "head": head, "window": win,
                    "head_plus_1": right_symbol, "distance_to_extents": [head - lo, hi - head],
                    "interior_one_run_lengths": [end - start + 1 for start, end in runs],
                    "adjacent_run_index_from_left": adjacent,
                    "nearest_run_index_from_right": nearest_from_right,
                })

        tr = tab.get((state, sym))
        if tr is None:
            halted = True
            stop_step = step
            break
        ns, nw, direction = tr
        if nw:
            tape[head] = 1
        else:
            tape.pop(head, None)
        state = ns
        head += direction
        if head < lo:
            lo = head
        elif head > hi:
            hi = head

    dimension_mode = ("exact through F-entry 500000; then every 100th F-entry sampled"
                      if total_f_entries > EXACT_DIMENSION_EVENTS else "exact")
    small_window_set = len(window_counts) < 10
    central_question_text = (
        "Do F-entries confine to a small finite set of 9-cell windows (fewer than 10), "
        "and does F always read 1 at head+1 across the whole bounded run? "
        f"Answer: {'yes' if small_window_set else 'no'} for the fewer-than-10 threshold "
        f"({len(window_counts)} distinct windows), and {'yes' if assertion_held else 'no'} "
        "for F reading 1."
    )
    question_answer = {
        "small_finite_window_set_under_10": small_window_set,
        "distinct_windows": len(window_counts),
        "f_always_reads_1_at_head_plus_1": assertion_held,
        "scope": "within the bounded run only",
    }
    output = {
        "code": CODE,
        "budget": args.budget,
        "steps_executed": stop_step if (halted or not assertion_held) else args.budget,
        "halted": halted,
        "honest_scope": "bounded census; no unreachability claim",
        "parse_verification": {"rows": ["A", "B", "C", "D", "E", "F"],
                               "F_entered_only_via": "C0 = 0RF",
                               "F0": "---", "F1": "0RB"},
        "total_f_entries": total_f_entries,
        "stored_raw_events": len(raw_events),
        "first_50_raw_events": raw_events[:50],
        "window_census": {key: window_counts[key] for key in sorted(window_counts)},
        "window_nearest_run_index_from_right_census": {
            f"{win}|{idx if idx is not None else 'None'}": count
            for (win, idx), count in sorted(window_right_run_counts.items(), key=lambda x: (x[0][0], str(x[0][1])))
        },
        "right_edge_distance_hi_minus_head": {
            "min": min(right_distances) if right_distances else None,
            "max": max(right_distances) if right_distances else None,
            "histogram": histogram_json(right_distances),
        },
        "events_by_dimension": {
            "mode": dimension_mode,
            "exact_events_covered": min(total_f_entries, EXACT_DIMENSION_EVENTS),
            "exact_counts": histogram_json(exact_dimension_counts),
            "sample_stride_after_exact_prefix": SAMPLED_DIMENSION_STRIDE if total_f_entries > EXACT_DIMENSION_EVENTS else None,
            "sampled_events": dimension_samples,
            "sampled_counts": histogram_json(sampled_dimension_counts),
        },
        "f_always_reads_1_assertion": {"held": assertion_held, "failure": assertion_failure},
        "central_question": question_answer,
        "central_question_text": central_question_text,
    }
    OUT.mkdir(parents=True, exist_ok=True)
    path = OUT / "census.json"
    path.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")

    print(f"F-entries: {total_f_entries}; distinct 9-cell windows: {len(window_counts)} "
          f"({'small (<10)' if small_window_set else 'not small (<10)'})")
    print(central_question_text)
    print(f"F always reads 1 at head+1: {assertion_held}")
    if assertion_failure:
        print(f"Assertion failure: {assertion_failure}")
    print(f"right-edge distance hi-head: min={output['right_edge_distance_hi_minus_head']['min']}, "
          f"max={output['right_edge_distance_hi_minus_head']['max']}, "
          f"histogram={compact_histogram(right_distances)}")
    print(f"events-by-dimension ({dimension_mode}): exact={histogram_json(exact_dimension_counts)}, "
          f"sampled={histogram_json(sampled_dimension_counts)}")
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
