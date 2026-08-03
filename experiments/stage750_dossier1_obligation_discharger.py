"""Stage 750 -- discharge local C0/F obligations for dossier-1.

Machine: ``1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB``.

This is a bounded, mechanical induction-premise audit.  It imports the fitted
macro-rule machinery from stage747 (rather than reimplementing the fitter),
and takes the stage749 ``(rule, 9-cell-window)`` pairs as its obligations.

At every frontier record we retain both the stage747 macro state and the full
interior RLE, written as ``(one_run, zero_gap, one_run, ..., one_run)``.  The
macro blocks alone intentionally do *not* encode the zero gaps.

Relative-site convention (used uniformly for every C0/F entry): C0 is known
to have a 1 immediately to its right.  Its site is therefore
``left_of_1run_from_right:k``, where ``k`` is the zero-based index, counted
from the right, of that adjacent 1-run in the *current tape at the event*.
This is insensitive to changes made earlier in the macro interval and does
not attempt to project the event onto a stale input gap.

``DISCHARGED_UNIFORM`` is evidence only: all observed firings have the same
value-independent event structure (with any multiplicity exactly affine in
the VAR input components), and fresh-value literal replays agree.  It is not
a proof of the unbounded induction premise.
"""
from __future__ import annotations

import importlib.util
import json
import sys
from bisect import bisect_right
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
from pathlib import Path

from tqdm import tqdm


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))  # stage745-style bootstrap for qgkit imports

CODE = "1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB"
OUT = HERE / "outputs" / "stage750"
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

# Explicitly reuse stage747's fitted-rule API and stage748's parse/window timing.
simulate_records = stage747.simulate_records
astate = stage747.astate
build_rules = stage747.build_rules
group_key = stage747.group_key
predict = stage747.predict


def fit_rule_table() -> tuple[dict, dict, list[dict]]:
    halted, _stop, records = simulate_records(
        CODE, steps=stage747.FIT_STEPS, cap=stage747.FIT_RECORDS
    )
    assert not halted, "machine halted during stage747 fit horizon"
    transitions = [
        (astate(a), astate(b))
        for a, b in zip(records[stage747.STARTUP_PREFIX:], records[stage747.STARTUP_PREFIX + 1:])
    ]
    groups, literals = build_rules(transitions)
    return groups, literals, records


def label_rule(state: tuple, actual: tuple, groups: dict, literals: dict) -> str | None:
    """Stage747's literal, parity-refined, then ordinary prediction order."""
    if predict(state, groups, literals) != actual:
        return None
    if state in literals:
        return "LITERAL:" + repr(state)
    for parity in (True, False):
        key = group_key(state, parity=parity)
        if key in groups:
            return repr(key)
    return None


def interior_rle(tape: dict[int, int], lo: int, hi: int) -> tuple[int, ...]:
    """Alternating 1-runs and strictly interior 0-gaps, endpoint-to-endpoint."""
    ones: list[tuple[int, int]] = []
    pos = lo
    while pos <= hi:
        if not tape.get(pos, 0):
            pos += 1
            continue
        start = pos
        while pos <= hi and tape.get(pos, 0):
            pos += 1
        ones.append((start, pos - 1))
    if not ones:
        return ()
    out: list[int] = []
    for i, (start, end) in enumerate(ones):
        out.append(end - start + 1)
        if i + 1 < len(ones):
            out.append(ones[i + 1][0] - end - 1)
    return tuple(out)


def rle_blocks(rle: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(rle[::2])


def abstract_rle(rle: tuple[int, ...]) -> tuple[object, ...]:
    """Only 1-runs above four become VAR; every observed zero gap stays literal."""
    return tuple((n if n <= 4 else "VAR") if i % 2 == 0 else n
                 for i, n in enumerate(rle))


def site_from_right(tape: dict[int, int], head: int, hi: int) -> str:
    """Current-tape site convention documented in this module's docstring."""
    assert tape.get(head + 1, 0) == 1
    k = 0
    in_run = False
    for pos in range(hi, head, -1):
        bit = bool(tape.get(pos, 0))
        if bit and not in_run:
            k += 1
        in_run = bit
    # The adjacent run itself is included in k, so its right-index is k - 1.
    return f"left_of_1run_from_right:{k - 1}"


def raw_run() -> tuple[list[dict], list[dict], dict]:
    """100M raw steps with full RLE records and C0/F observations."""
    tab = stage748.parse(CODE)
    assert [(s, b) for (s, b), (ns, _, _) in tab.items() if ns == 5] == [(2, 0)]
    tape: dict[int, int] = {}
    head = state = 0
    lo = hi = 0
    records: list[dict] = []
    events: list[dict] = []
    halted = False
    stop = RAW_STEPS
    for step in tqdm(range(RAW_STEPS), desc="stage750 instrumented 100M raw run", mininterval=5.0):
        sym = tape.get(head, 0)
        if state == 2 and sym == 0:
            assert tape.get(head + 1, 0) == 1, "C0 would enter F with F-read 0"
            events.append({"step": step, "window": stage748.window9(tape, head),
                           "relative_site": site_from_right(tape, head, hi),
                           "f_reads_1": True})
        tr = tab.get((state, sym))
        if tr is None:
            halted = True
            stop = step
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
        if expanded:
            if len(records) >= RECORD_CAP:
                raise RuntimeError(f"frontier-record cap {RECORD_CAP} exceeded")
            rle = interior_rle(tape, lo, hi)
            records.append({"step": step + 1, "state": state,
                            "side": "L" if head == lo else "R",
                            "blocks": list(rle_blocks(rle)),
                            "full_interior_rle": list(rle)})
    return records, events, {"halted": halted, "steps_executed": stop if halted else RAW_STEPS}


def affine_count_fit(xs: list[tuple[int, ...]], ys: list[int], var_indices: list[int]) -> dict:
    """Exact count = alpha dot VARs + beta, refusing non-affine observations."""
    if len(set(ys)) == 1:
        return {"kind": "constant", "value": ys[0], "exact": True}
    rows = [tuple(Fraction(x[i]) for i in var_indices) + (Fraction(1),) for x in xs]
    n = len(var_indices) + 1
    aug = [list(row) + [Fraction(y)] for row, y in zip(rows, ys)]
    pivots: list[int] = []
    r = 0
    for c in range(n):
        pivot = next((i for i in range(r, len(aug)) if aug[i][c] != 0), None)
        if pivot is None:
            continue
        aug[r], aug[pivot] = aug[pivot], aug[r]
        aug[r] = [v / aug[r][c] for v in aug[r]]
        for i in range(len(aug)):
            if i != r and aug[i][c] != 0:
                aug[i] = [a - aug[i][c] * b for a, b in zip(aug[i], aug[r])]
        pivots.append(c)
        r += 1
    if any(all(v == 0 for v in row[:-1]) and row[-1] != 0 for row in aug) or r < n:
        return {"kind": "no_exact_determined_affine_fit", "exact": False,
                "observed_counts": ys, "var_indices": var_indices}
    coeff = [Fraction(0)] * n
    for row, col in enumerate(pivots):
        coeff[col] = aug[row][-1]
    predicted = [sum(a * b for a, b in zip(row, coeff)) for row in rows]
    if any(v.denominator != 1 or int(v) != y for v, y in zip(predicted, ys)):
        return {"kind": "no_exact_affine_fit", "exact": False, "observed_counts": ys}
    return {"kind": "affine", "var_indices": var_indices,
            "coefficients": [str(v) for v in coeff[:-1]], "intercept": str(coeff[-1]),
            "exact": True}


def count_from_fit(fit: dict, blocks: tuple[int, ...]) -> int | None:
    if fit["kind"] == "constant":
        return fit["value"]
    if fit["kind"] != "affine":
        return None
    value = Fraction(fit["intercept"])
    for i, coefficient in zip(fit["var_indices"], fit["coefficients"]):
        value += Fraction(coefficient) * blocks[i]
    return int(value) if value.denominator == 1 else None


def build_tape_from_rle(rle: tuple[int, ...], side: str) -> tuple[dict[int, int], int, int, int]:
    """Literal record reconstruction: current frontier cell is the side blank."""
    tape: dict[int, int] = {}
    # Place the interior from position 1; a leading (L) or trailing (R) blank
    # becomes the frontier head.  Translation does not alter the machine.
    pos = 1
    for i, length in enumerate(rle):
        if i % 2 == 0:
            for cell in range(pos, pos + length):
                tape[cell] = 1
        pos += length
    if side == "L":
        return tape, 0, pos - 1, 0
    # Shift so that the right boundary is the blank at zero.
    shift = -pos
    shifted = {cell + shift: bit for cell, bit in tape.items()}
    return shifted, -pos + 1, 0, 0


def run_one_firing(rle: tuple[int, ...], state: int, side: str) -> dict:
    """Raw replay from a literal frontier record through its next expansion."""
    tab = stage748.parse(CODE)
    tape, lo, hi, head = build_tape_from_rle(rle, side)
    events: list[dict] = []
    steps = 0
    while True:
        sym = tape.get(head, 0)
        if state == 2 and sym == 0:
            f1 = tape.get(head + 1, 0) == 1
            events.append({"window": stage748.window9(tape, head),
                           "relative_site": site_from_right(tape, head, hi) if f1 else "F_READ_0",
                           "f_reads_1": f1})
        tr = tab.get((state, sym))
        if tr is None:
            return {"halted": True, "steps": steps, "events": events}
        ns, nw, direction = tr
        if nw:
            tape[head] = 1
        else:
            tape.pop(head, None)
        state = ns
        head += direction
        steps += 1
        if head < lo or head > hi:
            if head < lo:
                lo = head
            else:
                hi = head
            rle_out = interior_rle(tape, lo, hi)
            return {"halted": False, "steps": steps, "events": events,
                    "output": (state, "L" if head == lo else "R", rle_blocks(rle_out))}


def expected_obligations() -> list[tuple[str, str]]:
    alignment = json.loads((HERE / "outputs" / "stage749" / "alignment.json").read_text())
    return sorted((rule, window)
                  for rule, payload in alignment["rule_to_f_window_census"].items()
                  for window in payload["windows"])


def synthetic_inputs(label: str, firings: list[dict], literals: dict,
                     var_indices: list[int] | None = None) -> tuple[list[dict], list[dict]]:
    """Return guard-compatible fresh inputs and any explicitly logged substitutions."""
    first = firings[0]
    base = tuple(first["rle"])
    blocks = tuple(first["blocks"])
    if var_indices is None:
        var_indices = [i for i, n in enumerate(blocks) if n > 4]
    notes: list[dict] = []
    if label.startswith("LITERAL:"):
        notes.append({"reason": "literal rule accepts only its exact input; fresh VAR values rejected",
                      "substitution": "replayed the literal observed block values"})
        return [{"name": "literal_guard_compatible", "rle": base, "blocks": blocks}], notes
    observed_max = {i: max(f["blocks"][i] for f in firings) for i in var_indices}
    if not var_indices:
        return [{"name": "no_VAR_components", "rle": base, "blocks": blocks}], notes
    out = []
    for ordinal, offset in enumerate((13, 26), 1):
        requested = list(blocks)
        for i in var_indices:
            # Both offsets provide opposite parities.  All nonliteral group-key
            # caps accept >=4; a parity-refined key is checked below.
            requested[i] = max(5, observed_max[i] + offset)
        candidate = None
        # Affine rules can impose parity/integrality guards.  Search every
        # nearby parity combination and retain only the exact same selected
        # stage747 rule, never a merely predictable neighbouring rule.
        for corrections in product(range(4), repeat=len(var_indices)):
            trial = list(requested)
            for i, correction in zip(var_indices, corrections):
                trial[i] += correction
            trial_state = (first["state"], first["side"], tuple(trial))
            trial_pred = predict(trial_state, GROUPS, LITERALS)
            if trial_pred is not None and label_rule(trial_state, trial_pred, GROUPS, LITERALS) == label:
                candidate = tuple(trial)
                break
        if candidate is None:
            # A one-sample affine rule can have every block folded into an
            # exact guard.  Fresh values are then mathematically impossible;
            # replay the guard-compatible literal input once below.
            notes.append({"reason": "no guard-compatible fresh candidate after parity search",
                          "requested_offset": offset, "requested": requested})
            continue
        if list(candidate) != requested:
            notes.append({"reason": "initial fresh candidate rejected by stage747 guard",
                          "requested_offset": offset, "substitution": list(candidate)})
        rle = list(base)
        for j, val in enumerate(candidate):
            rle[2 * j] = val
        out.append({"name": f"fresh_offset_{offset}", "rle": tuple(rle), "blocks": candidate})
    if not out:
        matching = next((rule for key, rule in GROUPS.items() if repr(key) == label), None)
        guard = (matching or {}).get("guard", {})
        guarded = list(blocks)
        for index, value in guard.items():
            guarded[int(index)] = int(value)
        guarded_blocks = tuple(guarded)
        guarded_state = (first["state"], first["side"], guarded_blocks)
        guarded_pred = predict(guarded_state, GROUPS, LITERALS)
        if guarded_pred is not None and label_rule(guarded_state, guarded_pred, GROUPS, LITERALS) == label:
            guarded_rle = list(base)
            for j, value in enumerate(guarded_blocks):
                guarded_rle[2 * j] = value
            notes.append({"reason": "fresh values prohibited by exact stage747 affine guard",
                          "substitution": list(guarded_blocks)})
            out.append({"name": "exact_guard_compatible", "rle": tuple(guarded_rle),
                        "blocks": guarded_blocks})
    return out, notes


def main() -> None:
    global GROUPS, LITERALS
    OUT.mkdir(parents=True, exist_ok=True)
    obligations = expected_obligations()
    GROUPS, LITERALS, fit_records = fit_rule_table()
    records, events, run = raw_run()
    assert records and len(records) < RECORD_CAP
    steps = [r["step"] for r in records]

    firing_by_rule: dict[str, list[dict]] = defaultdict(list)
    labels: list[str] = []
    for i, (left, right) in enumerate(zip(records, records[1:])):
        label = "STARTUP" if i < stage747.STARTUP_PREFIX else label_rule(astate(left), astate(right), GROUPS, LITERALS)
        labels.append(label or "UNMATCHED")
        if label not in {None, "STARTUP"}:
            firing_by_rule[label].append({"record_index": i, "rle": tuple(left["full_interior_rle"]),
                                          "blocks": tuple(left["blocks"]), "state": left["state"],
                                          "side": left["side"], "events": []})
    by_index = {f["record_index"]: f for fs in firing_by_rule.values() for f in fs}
    for event in events:
        i = bisect_right(steps, event["step"]) - 1
        if 0 <= i < len(labels) and i in by_index:
            by_index[i]["events"].append(event)

    # Analyze each selected macro rule once; every obligation gets its relevant
    # window slice of this same audited event class and replay set.
    analyses: dict[str, dict] = {}
    for label, fs in firing_by_rule.items():
        # Position-wise template across ALL firings: an entry is the literal
        # value iff it is constant over every firing, else VAR. Template
        # uniformity then only requires equal RLE lengths; value-cutoff
        # artifacts (a run straddling 4 across firings) cannot occur.
        lengths = {len(f["rle"]) for f in fs}
        template_ok = len(lengths) == 1
        if template_ok:
            width = next(iter(lengths))
            canonical = tuple(
                fs[0]["rle"][p] if len({f["rle"][p] for f in fs}) == 1 else "VAR"
                for p in range(width)
            )
        else:
            canonical = ()
        pairs = sorted({(e["window"], e["relative_site"]) for f in fs for e in f["events"]})
        var_indices = [i for i in range(len(fs[0]["blocks"]))
                       if canonical and canonical[2 * i] == "VAR"]
        pair_fits: dict[tuple[str, str], dict] = {}
        for pair in pairs:
            counts = [sum((e["window"], e["relative_site"]) == pair for e in f["events"]) for f in fs]
            pair_fits[pair] = affine_count_fit([f["blocks"] for f in fs], counts, var_indices)
        uniform_ok = template_ok and all(v["exact"] for v in pair_fits.values())
        first = None
        if not template_ok:
            baseline = len(fs[0]["rle"])
            mismatch_index = next(j for j, f in enumerate(fs)
                                  if len(f["rle"]) != baseline)
            first = {"kind": "rle_length_mismatch",
                     "firing_index": mismatch_index,
                     "record_index": fs[mismatch_index]["record_index"],
                     "expected_length": baseline,
                     "actual_length": len(fs[mismatch_index]["rle"])}
        else:
            bad = next(((pair, fit) for pair, fit in pair_fits.items() if not fit["exact"]), None)
            if bad:
                first = {"kind": "non_affine_event_count", "pair": list(bad[0]), "fit": bad[1]}
        synth, guard_notes = synthetic_inputs(label, fs, LITERALS,
                                              var_indices=var_indices)
        replay_results = []
        for instance in synth:
            expected = predict((fs[0]["state"], fs[0]["side"], instance["blocks"]), GROUPS, LITERALS)
            replay = run_one_firing(instance["rle"], fs[0]["state"], fs[0]["side"])
            actual = replay.get("output")
            event_counts = Counter((e["window"], e["relative_site"]) for e in replay["events"])
            expected_counts = {pair: count_from_fit(fit, instance["blocks"])
                               for pair, fit in pair_fits.items()}
            event_ok = (all(e["f_reads_1"] for e in replay["events"])
                        and all(event_counts.get(pair, 0) == count for pair, count in expected_counts.items())
                        and all(pair in expected_counts for pair in event_counts))
            macro_ok = not replay["halted"] and expected == actual
            result = {"name": instance["name"], "blocks": list(instance["blocks"]),
                      "steps": replay["steps"], "macro_expected": repr(expected),
                      "macro_actual": repr(actual), "macro_ok": macro_ok,
                      "event_expected_counts": {f"{a}|{b}": c for (a, b), c in expected_counts.items()},
                      "event_actual_counts": {f"{a}|{b}": c for (a, b), c in event_counts.items()},
                      "f_always_reads_1": all(e["f_reads_1"] for e in replay["events"]),
                      "event_structure_ok": event_ok, "passed": macro_ok and event_ok}
            replay_results.append(result)
            if first is None and not result["passed"]:
                first = {"kind": "synthetic_replay_mismatch", **result}
        analyses[label] = {"n_firings": len(fs), "abstract_input_rle": list(canonical),
                           "var_block_indices": var_indices, "template_uniform": template_ok,
                           "pair_count_fits": {f"{a}|{b}": fit for (a, b), fit in pair_fits.items()},
                           "uniformity_ok": uniform_ok, "synthetic_replays": replay_results,
                           "guard_rejections_or_substitutions": guard_notes,
                           "first_counterexample": first}

    rows = []
    for label, window in obligations:
        analysis = analyses.get(label)
        if analysis is None:
            rows.append({"rule": label, "window": window, "verdict": "FAILED",
                         "first_counterexample": {"kind": "rule_not_seen_in_stage750_run"}})
            continue
        relevant = [(key, fit) for key, fit in analysis["pair_count_fits"].items() if key.startswith(window + "|")]
        has_window = bool(relevant)
        passed = (has_window and analysis["uniformity_ok"]
                  and all(r["passed"] for r in analysis["synthetic_replays"]))
        counter = analysis["first_counterexample"]
        if not has_window:
            counter = {"kind": "expected_window_absent", "expected_window": window,
                       "actual_pairs": list(analysis["pair_count_fits"])}
        rows.append({"rule": label, "window": window,
                     "relative_site_count_fits": dict(relevant),
                     "n_firings": analysis["n_firings"],
                     "abstract_input_rle": analysis["abstract_input_rle"],
                     "var_block_indices": analysis["var_block_indices"],
                     "uniformity_ok": analysis["uniformity_ok"],
                     "synthetic_replays": analysis["synthetic_replays"],
                     "guard_rejections_or_substitutions": analysis["guard_rejections_or_substitutions"],
                     "verdict": "DISCHARGED_UNIFORM" if passed else "FAILED",
                     "first_counterexample": None if passed else counter})

    n_failed = sum(r["verdict"] == "FAILED" for r in rows)
    summary = {"n_obligations": len(rows), "n_discharged": len(rows) - n_failed,
               "n_failed": n_failed,
               "status": "ALL_DISCHARGED_UNIFORM" if n_failed == 0 else "FAILED",
               "honest_scope": "uniformity + fresh-value replay evidence for the induction premise; not itself a proof"}
    output = {"code": CODE, "fit": {"steps": stage747.FIT_STEPS, "records": len(fit_records),
                                       "group_rules": len(GROUPS), "literal_rules": len(LITERALS)},
              "run": {**run, "records_captured": len(records), "f_entries": len(events),
                      "relative_site_definition": "left_of_1run_from_right:k on current tape"},
              "obligations": rows, "summary": summary}
    path = OUT / "obligations.json"
    path.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    print("rule | window | firings | verdict")
    for row in rows:
        print(f"{row['rule']} | {row['window']} | {row.get('n_firings', 0)} | {row['verdict']}")
    print(json.dumps(summary, sort_keys=True))
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
