"""Stage 749 -- align dossier-1 C0/F-entry windows to fitted macro rules.

This is a bounded alignment census.  The rule fitter and lookup semantics are
imported from stage747; C0 observation and the 9-cell window are imported from
stage748.  It does not make an unreachability claim.
"""
from __future__ import annotations

import importlib.util
import json
import sys
from bisect import bisect_right
from collections import Counter, defaultdict
from pathlib import Path

from tqdm import tqdm


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

CODE = "1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB"
OUT = HERE / "outputs" / "stage749"
RAW_STEPS = 100_000_000
RECORD_CAP = 100_000


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


stage747 = load_module("stage747_dossier1_macro_system", HERE / "stage747_dossier1_macro_system.py")
stage748 = load_module("stage748_dossier1_halt_window_census", HERE / "stage748_dossier1_halt_window_census.py")

# Required stage747 machinery: do not duplicate the macro fitter or lookup.
simulate_records = stage747.simulate_records
group_key = stage747.group_key
build_rules = stage747.build_rules
predict = stage747.predict
astate = stage747.astate


def fit_rule_table() -> tuple[dict, dict, list[dict]]:
    """Fit precisely on stage747's 20M-step, post-startup transition set."""
    halted, _stop, records = simulate_records(
        CODE, steps=stage747.FIT_STEPS, cap=stage747.FIT_RECORDS
    )
    assert not halted, "machine halted during stage747 fit horizon"
    transitions = [
        (astate(a), astate(b))
        for a, b in zip(records[stage747.STARTUP_PREFIX:], records[stage747.STARTUP_PREFIX + 1:])
    ]
    group_rules, literal_rules = build_rules(transitions)
    return group_rules, literal_rules, records


def label_rule(state: tuple, actual: tuple, group_rules: dict, literal_rules: dict) -> str | None:
    """Return the rule selected in stage747's literal, parity, non-parity order."""
    expected = predict(state, group_rules, literal_rules)
    if expected != actual:
        return None
    if state in literal_rules:
        return "LITERAL:" + repr(state)
    for parity in (True, False):
        key = group_key(state, parity=parity)
        rule = group_rules.get(key)
        if rule is None:
            continue
        # predict() returns None immediately if this selected affine guard abstains.
        # expected == actual above establishes that this is the rule that fired.
        return repr(key)
    return None


def raw_run() -> tuple[list[dict], list[dict], dict]:
    """One 100M-step instrumented run using the stage748 C0/window timing."""
    tab = stage748.parse(CODE)
    assert [(s, b) for (s, b), (ns, _, _) in tab.items() if ns == 5] == [(2, 0)]
    tape: dict[int, int] = {}
    head = state = 0
    lo = hi = 0
    records: list[dict] = []
    f_events: list[dict] = []
    halted = False
    stop_step = RAW_STEPS

    # This block extractor is the exact one used by simulate_records.
    from qgkit.bb6.vcollatz.classify import _one_blocks

    for step in tqdm(range(RAW_STEPS), desc="stage749 instrumented 100M raw run", mininterval=5.0):
        sym = tape.get(head, 0)
        if state == 2 and sym == 0:  # stage748's F-entry event: C0 = 0RF
            assert tape.get(head + 1, 0) == 1, "C0 would enter F with F-read symbol 0"
            f_events.append({"step": step, "window": stage748.window9(tape, head)})

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

    return records, f_events, {"halted": halted, "steps_executed": stop_step if halted else RAW_STEPS}


def main() -> None:
    group_rules, literal_rules, fit_records = fit_rule_table()
    records, f_events, run = raw_run()
    assert records, "raw run produced no frontier-expansion records"
    assert len(records) <= RECORD_CAP, "frontier-record cap was exceeded"
    assert all(a["step"] < b["step"] for a, b in zip(records, records[1:])), "record steps not strictly increasing"

    interval_labels: list[str] = []
    interval_f_counts: list[int] = [0] * (len(records) - 1)
    for index, (left, right) in enumerate(zip(records, records[1:])):
        state, actual = astate(left), astate(right)
        if index < stage747.STARTUP_PREFIX:
            interval_labels.append("STARTUP")
        else:
            label = label_rule(state, actual, group_rules, literal_rules)
            interval_labels.append(label if label is not None else "UNMATCHED")

    steps = [record["step"] for record in records]
    startup_events = 0
    unmatched = 0
    out_of_interval = 0
    labelled_events: list[tuple[int, str, str]] = []
    for event in f_events:
        interval = bisect_right(steps, event["step"]) - 1
        if interval < 0 or interval >= len(interval_labels):
            out_of_interval += 1
            continue
        label = interval_labels[interval]
        interval_f_counts[interval] += 1
        if label == "STARTUP":
            startup_events += 1
        elif label == "UNMATCHED":
            unmatched += 1
        else:
            labelled_events.append((interval, label, event["window"]))

    # All macro firings are retained in each rule's histogram, including zero-F
    # intervals; this makes n_intervals and per-firing multiplicities auditable.
    by_rule: dict[str, dict] = {}
    interval_indices: dict[str, list[int]] = defaultdict(list)
    for index, label in enumerate(interval_labels):
        if label not in {"STARTUP", "UNMATCHED"}:
            interval_indices[label].append(index)
    windows_by_rule: dict[str, Counter[str]] = defaultdict(Counter)
    for _index, label, window in labelled_events:
        windows_by_rule[label][window] += 1
    for label, indices in interval_indices.items():
        hist = Counter(interval_f_counts[index] for index in indices)
        by_rule[label] = {
            "windows": dict(sorted(windows_by_rule[label].items())),
            "n_intervals": len(indices),
            "n_f_entries": sum(interval_f_counts[index] for index in indices),
            "f_entries_per_interval_histogram": {str(k): hist[k] for k in sorted(hist)},
        }

    f_rule_items = [(key, val) for key, val in by_rule.items() if val["n_f_entries"]]
    multiple = [
        {"rule": key, "windows": sorted(val["windows"])}
        for key, val in f_rule_items if len(val["windows"]) > 1
    ]
    exactly_one = sum(len(val["windows"]) == 1 for _key, val in f_rule_items)
    assigned = sum(val["n_f_entries"] for _key, val in f_rule_items) + startup_events + unmatched + out_of_interval
    assert assigned == len(f_events), "F-entry accounting does not close"
    assert out_of_interval == 0, "an F-entry lies outside record intervals"

    output = {
        "code": CODE,
        "honest_scope": "bounded alignment census; no unreachability claim",
        "fit": {"steps": stage747.FIT_STEPS, "startup_prefix": stage747.STARTUP_PREFIX,
                "fit_records": len(fit_records), "group_rules": len(group_rules),
                "literal_rules": len(literal_rules)},
        "run": {**run, "record_cap": RECORD_CAP, "records_captured": len(records),
                "total_f_entries": len(f_events)},
        "rule_to_f_window_census": dict(sorted(by_rule.items())),
        "n_rules_with_f_entries": len(f_rule_items),
        "n_rules_with_exactly_one_window": exactly_one,
        "n_rules_with_multiple_windows": multiple,
        "n_unmatched": unmatched,
        "n_startup_events": startup_events,
        "n_out_of_interval_events": out_of_interval,
        "one_window_per_rule": not multiple,
        "verification": {
            "f_entry_accounting": {"total": len(f_events), "assigned": assigned},
            "record_steps_strictly_increasing": True,
            "record_interval_count": len(interval_labels),
            "record_intervals_have_no_internal_gaps": True,
            "intervals_cover_record_span": [records[0]["step"], records[-1]["step"]],
            "all_f_entries_within_record_interval_span": out_of_interval == 0,
        },
    }
    OUT.mkdir(parents=True, exist_ok=True)
    path = OUT / "alignment.json"
    path.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")

    print("rule | F entries | distinct windows | intervals | F-per-interval histogram")
    for key, val in sorted(f_rule_items, key=lambda item: (-item[1]["n_f_entries"], item[0])):
        print(f"{key} | {val['n_f_entries']} | {len(val['windows'])} | {val['n_intervals']} | "
              f"{val['f_entries_per_interval_histogram']}")
    print(f"F entries total={len(f_events)}; startup={startup_events}; unmatched={unmatched}; "
          f"out_of_interval={out_of_interval}")
    print(f"one_window_per_rule={output['one_window_per_rule']}; "
          f"rules_with_F={output['n_rules_with_f_entries']}; exactly_one={exactly_one}; "
          f"multiple={len(multiple)}")
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
