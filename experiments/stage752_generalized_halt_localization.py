"""Stage 752 -- bounded generalized halt-window localization for BB(6).

For every syntactically undefined transition in a two-symbol standard-format
machine, census every transition that enters its state.  The observation is
made before the entering move, so the stored nine-cell window has precisely
the stage748 convention.  Macro alignment is a bounded empirical aid only.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from bisect import bisect_right
from collections import Counter, defaultdict
from pathlib import Path

from tqdm import tqdm


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from qgkit.bb6.vcollatz.classify import _one_blocks, _parse
from qgkit.bb6.vcollatz import macro


OUT = HERE / "outputs" / "stage752"
FIT_STEPS = 20_000_000
RECORD_CAP = 100_000


def state_name(state: int) -> str:
    return chr(ord("A") + state)


def pair_label(state: int, symbol: int) -> str:
    return f"({state_name(state)},{symbol})"


def entry_label(entry: tuple[int, int, int, int, int]) -> str:
    state, symbol, _write, _direction, next_state = entry
    return f"{pair_label(state, symbol)}->{state_name(next_state)}"


def tag_label(entry: tuple[int, int, int, int, int], undefined: tuple[int, int]) -> str:
    return f"{entry_label(entry)}; {pair_label(*undefined)}"


def window9(tape: dict[int, int], head: int) -> str:
    """Stage748's nine-cell window, centered on the pre-move head."""
    return "".join(str(tape.get(pos, 0)) for pos in range(head - 4, head + 5))


def describe_entry(entry: tuple[int, int, int, int, int]) -> dict:
    state, symbol, write, direction, next_state = entry
    return {
        "from_state": state_name(state),
        "read_symbol": symbol,
        "write_symbol": write,
        "direction": "R" if direction == 1 else "L",
        "to_state": state_name(next_state),
        "label": entry_label(entry),
    }


def describe_undefined(pair: tuple[int, int]) -> dict:
    state, symbol = pair
    return {"state": state_name(state), "symbol": symbol,
            "label": pair_label(state, symbol)}


def selected_rule_label(state: tuple, actual: tuple, rules: dict) -> str | None:
    """Return stage749's literal/parity/non-parity rule label when it fires."""
    if macro.predict_next(state, rules) != actual:
        return None
    group_rules = rules["group_rules"]
    literal_rules = rules["literal_rules"]
    if state in literal_rules:
        return "LITERAL:" + repr(state)
    for parity in (True, False):
        key = macro.group_key(state, parity=parity)
        if key in group_rules:
            return repr(key)
    return None


def macro_alignment(records: list[dict]) -> tuple[str, dict, list[str]]:
    """Fit through FIT_STEPS and exact-replay every later captured record."""
    fit_end = bisect_right([record["step"] for record in records], FIT_STEPS)
    fit_records = records[:fit_end]
    details = {
        "fit_steps": FIT_STEPS,
        "startup_prefix": 8,
        "fit_records": len(fit_records),
        "replay_records": len(records) - fit_end,
        "record_cap": RECORD_CAP,
    }
    if len(fit_records) < 2:
        details["reason"] = "fewer than two frontier records within fit horizon"
        return "insufficient_records", details, []

    rules = macro.fit_macro_rules(fit_records)
    details.update({
        "group_rules": len(rules["group_rules"]),
        "literal_rules": len(rules["literal_rules"]),
        "n_conflicts": rules["n_conflicts"],
    })
    if rules["n_conflicts"]:
        return "conflict", details, []
    # Include the boundary transition from the final fitted record to the
    # first replay record; this is the first transition not used in fitting.
    replay_start = max(fit_end - 1, 0)
    replay = macro.replay_records(records, replay_start, rules)
    details["replay"] = replay
    if not replay["exact"]:
        return "replay_mismatch", details, []

    interval_labels: list[str] = []
    for index, (left, right) in enumerate(zip(records, records[1:])):
        if index < 8:
            interval_labels.append("STARTUP")
            continue
        label = selected_rule_label(macro.astate(left), macro.astate(right), rules)
        # Exact replay, plus fit verification by the macro fitter, means that
        # this fallback is only defensive; do not invent a rule name.
        interval_labels.append(label if label is not None else "UNMATCHED")
    return "exact", details, interval_labels


def analyze(code: str, steps: int) -> dict:
    """Run one bounded raw-machine census and align it to frontier macros."""
    tab = _parse(code)
    n_states = len(code.split("_"))
    undefined_pairs = [(state, symbol) for state in range(n_states)
                       for symbol in (0, 1) if (state, symbol) not in tab]
    undefined_by_state: dict[int, list[tuple[int, int]]] = defaultdict(list)
    for pair in undefined_pairs:
        undefined_by_state[pair[0]].append(pair)
    entries = sorted((state, symbol, write, direction, next_state)
                     for (state, symbol), (next_state, write, direction) in tab.items()
                     if next_state in undefined_by_state)

    tags = [tag_label(entry, undefined)
            for entry in entries for undefined in undefined_by_state[entry[4]]]
    event_counts: Counter[str] = Counter()
    landing_histograms: dict[str, Counter[int]] = defaultdict(Counter)
    window_counts: dict[str, Counter[str]] = defaultdict(Counter)
    # The stage748 census can contain millions of events.  Retain exact
    # alignment information compactly as (left-record interval, tag, window)
    # counts rather than an unbounded list of event dictionaries.
    interval_event_counts: Counter[tuple[int, str, str]] = Counter()
    halt_candidate_steps: set[int] = set()
    tape: dict[int, int] = {}
    head = state = 0
    lo = hi = 0
    records: list[dict] = []
    halted = False
    halt_step: int | None = None

    for step in tqdm(range(steps), desc="stage752 halt localization", mininterval=5.0):
        symbol = tape.get(head, 0)
        transition = tab.get((state, symbol))
        if transition is None:
            halted = True
            halt_step = step
            break
        next_state, write, direction = transition
        entry = (state, symbol, write, direction, next_state)
        if next_state in undefined_by_state:
            win = window9(tape, head)
            landing_symbol = tape.get(head + direction, 0)
            for undefined in undefined_by_state[next_state]:
                tag = tag_label(entry, undefined)
                event_counts[tag] += 1
                landing_histograms[tag][landing_symbol] += 1
                window_counts[tag][win] += 1
                interval_event_counts[len(records) - 1, tag, win] += 1
                if landing_symbol == undefined[1]:
                    halt_candidate_steps.add(step)

        if write:
            tape[head] = 1
        else:
            tape.pop(head, None)
        state = next_state
        head += direction
        expanded = False
        if head < lo:
            lo = head
            expanded = True
        elif head > hi:
            hi = head
            expanded = True
        if expanded and len(records) < RECORD_CAP:
            blocks = _one_blocks(tape, lo, hi)
            records.append({
                "step": step + 1,
                "side": "L" if head == lo else "R",
                "state": state,
                "width": hi - lo + 1,
                "ones": sum(blocks),
                "blocks": blocks,
            })

    macro_status, macro_details, interval_labels = macro_alignment(records)
    rule_windows: dict[str, Counter[str]] = defaultdict(Counter)
    unassigned_events = 0
    if macro_status == "exact":
        for (interval, _tag, window), count in interval_event_counts.items():
            if interval < 0 or interval >= len(interval_labels):
                unassigned_events += count
                continue
            rule = interval_labels[interval]
            if rule in {"STARTUP", "UNMATCHED"}:
                unassigned_events += count
                continue
            rule_windows[rule][window] += count
    macro_details["unassigned_events"] = unassigned_events

    obligations = [
        {"rule": rule, "window": window, "count": count}
        for rule in sorted(rule_windows)
        for window, count in sorted(rule_windows[rule].items())
    ]
    output = {
        "code": code,
        "steps_budget": steps,
        "steps_executed": halt_step if halted else steps,
        "undefined_pairs": [describe_undefined(pair) for pair in undefined_pairs],
        "entry_transitions": [describe_entry(entry) for entry in entries],
        "halted": halted,
        "halt_step": halt_step,
        "n_events": {tag: event_counts[tag] for tag in tags},
        "distinct_windows": {tag: dict(sorted(window_counts[tag].items())) for tag in tags},
        "landing_symbol_histogram": {
            tag: {str(symbol): landing_histograms[tag][symbol]
                  for symbol in sorted(landing_histograms[tag])}
            for tag in tags
        },
        "halt_event_verification": {
            "n_events_landing_on_undefined_symbol": {
                tag: landing_histograms[tag][undefined[1]]
                for entry in entries for undefined in undefined_by_state[entry[4]]
                for tag in [tag_label(entry, undefined)]
            },
            "actual_halt_consistent_with_event": (
                not halted or halt_step - 1 in halt_candidate_steps
            ),
        },
        "macro_status": macro_status,
        "macro_details": macro_details,
        "rule_to_window_census": {rule: dict(sorted(windows.items()))
                                  for rule, windows in sorted(rule_windows.items())},
        "per_rule_window_counts": {rule: len(windows) for rule, windows in sorted(rule_windows.items())},
        "obligations": obligations,
        "n_obligations": len(obligations),
        "honest_scope": "bounded census+alignment; no unreachability claim",
    }
    return output


def read_codes(args: argparse.Namespace) -> list[str]:
    if bool(args.code) == bool(args.input):
        raise ValueError("provide exactly one of --code or --input")
    if args.code:
        return [args.code.strip()]
    return [line.strip() for line in Path(args.input).read_text().splitlines()
            if line.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--code", help="one BB(6) standard-format machine")
    source.add_argument("--input", help="newline-delimited BB(6) standard-format codes")
    parser.add_argument("--steps", type=int, default=100_000_000)
    args = parser.parse_args()
    if args.steps < 1:
        raise ValueError("--steps must be positive")

    codes = read_codes(args)
    OUT.mkdir(parents=True, exist_ok=True)
    for code in tqdm(codes, desc="stage752 machines"):
        path = OUT / f"{hashlib.sha1(code.encode()).hexdigest()[:12]}.json"
        if path.exists():
            print(f"skip existing {path}")
            continue
        output = analyze(code, args.steps)
        path.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
        print(f"wrote {path}; macro_status={output['macro_status']}; "
              f"n_obligations={output['n_obligations']}")


if __name__ == "__main__":
    main()
