"""Stage 753 -- generalized (rule, window) obligation discharger for BB(6).

Machine-agnostic port of the stage750 dossier-1 discharger onto the
generalized ``qgkit.bb6.vcollatz.macro`` fitter.  For any two-symbol
standard-format machine with exactly one undefined transition (Hstate, hsym):

1. run an instrumented raw simulation retaining, at every frontier record,
   the full interior RLE ``(one_run, zero_gap, ..., one_run)`` alongside the
   macro blocks, and at every transition that enters Hstate the stage748
   nine-cell pre-move window plus a frontier-relative site;
2. fit the macro-rule table on the fit horizon and label every record
   interval with the exact rule that fired (exact replay is a precondition);
3. for every (rule, window) obligation observed: check firing-template
   uniformity (position-wise literal/VAR RLE template; per-(window, site)
   event counts constant or exactly affine in the VAR blocks) and replay the
   rule from synthetic fresh-value inputs, requiring the same macro output
   and the same event structure with every landing symbol != hsym.

``DISCHARGED_UNIFORM`` is evidence for the induction premise, not a proof.
The frontier-relative site convention generalizes stage750: at a safe entry
event the landing cell ``head + direction`` holds a non-hsym symbol; for
``hsym == 0`` its 1-run is indexed from the frontier on the landing side
(``from_right`` when the move is R, ``from_left`` when the move is L).
Machines with ``hsym == 1`` fall back to the coarse site ``ZERO_LANDING``.

v2 (after the first Antihydra run): a frontier record's head is NOT always
adjacent to the nearest interior 1-run -- the head-side zero offset
(``head_gap``) is part of the configuration and is now (a) captured per
record, (b) reproduced by the tape reconstruction, (c) checked by a literal
self-replay of each rule's first observed firing, and (d) admitted as a
template/regressor dimension, with a blocks-mod-2 parity partition as the
fallback when a raw affine count fit fails.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from bisect import bisect_right
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from tqdm import tqdm

from qgkit.bb6.vcollatz.classify import _parse
from qgkit.bb6.vcollatz import macro

OUT = HERE / "outputs" / "stage753"
FIT_STEPS = 20_000_000
RECORD_CAP = 100_000
STARTUP_PREFIX = 8


def state_name(state: int) -> str:
    return chr(ord("A") + state)


def window9(tape: dict[int, int], head: int) -> str:
    return "".join(str(tape.get(pos, 0)) for pos in range(head - 4, head + 5))


def interior_rle(tape: dict[int, int], lo: int, hi: int) -> tuple[int, ...]:
    """Alternating 1-runs and strictly interior 0-gaps (stage750 convention)."""
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


def head_side_gap(tape: dict[int, int], lo: int, hi: int, head: int) -> int:
    """Zero cells strictly between the frontier head and the nearest 1-run."""
    if head == lo:
        pos = next((p for p in range(lo, hi + 1) if tape.get(p, 0)), None)
        return 0 if pos is None else pos - head - 1
    pos = next((p for p in range(hi, lo - 1, -1) if tape.get(p, 0)), None)
    return 0 if pos is None else head - pos - 1


def relative_site(tape: dict[int, int], head: int, lo: int, hi: int,
                  direction: int, hsym: int) -> str:
    """Frontier-relative location of the landing cell of a safe entry event."""
    landing = head + direction
    if tape.get(landing, 0) == hsym:
        return "UNSAFE_LANDING"
    if hsym != 0:
        return "ZERO_LANDING"
    # The landing cell is inside a 1-run; index that run from the frontier on
    # the landing side (value-independent under uniform block growth).
    k = 0
    in_run = False
    if direction == 1:
        span = range(hi, landing - 1, -1)
        tag = "1run_from_right"
    else:
        span = range(lo, landing + 1)
        tag = "1run_from_left"
    for pos in span:
        bit = bool(tape.get(pos, 0))
        if bit and not in_run:
            k += 1
        in_run = bit
    return f"{tag}:{k - 1}"


def machine_shape(code: str) -> tuple[dict, tuple[int, int], list[tuple]]:
    tab = _parse(code)
    n_states = len(code.split("_"))
    undefined = [(s, b) for s in range(n_states) for b in (0, 1)
                 if (s, b) not in tab]
    if len(undefined) != 1:
        raise ValueError(f"expected exactly one undefined pair, got {undefined}")
    hstate, _hsym = undefined[0]
    entries = sorted((s, b) for (s, b), (ns, _w, _d) in tab.items() if ns == hstate)
    return tab, undefined[0], entries


def raw_run(code: str, steps: int) -> tuple[list[dict], list[dict], dict]:
    """Instrumented raw run: full-RLE frontier records + Hstate entry events."""
    tab, (hstate, hsym), _entries = machine_shape(code)
    tape: dict[int, int] = {}
    head = state = 0
    lo = hi = 0
    records: list[dict] = []
    events: list[dict] = []
    halted = False
    stop = steps
    for step in tqdm(range(steps), desc=f"stage753 raw run {code[:12]}...",
                     mininterval=5.0):
        sym = tape.get(head, 0)
        tr = tab.get((state, sym))
        if tr is None:
            halted = True
            stop = step
            break
        ns, nw, direction = tr
        if ns == hstate:
            safe = tape.get(head + direction, 0) != hsym
            events.append({
                "step": step,
                "window": window9(tape, head),
                "relative_site": relative_site(tape, head, lo, hi, direction, hsym),
                "safe": safe,
            })
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
            head_gap = head_side_gap(tape, lo, hi, head)
            records.append({"step": step + 1, "state": state,
                            "side": "L" if head == lo else "R",
                            "blocks": list(rle_blocks(rle)),
                            "full_interior_rle": list(rle),
                            "head_gap": head_gap,
                            # Far-side zero margin: visited-but-zero cells
                            # between the last 1-run and the opposite
                            # frontier.  Blank-equivalent for the dynamics
                            # but load-bearing for record timing.
                            "far_gap": (hi - lo + 1) - 1 - head_gap - sum(rle)})
    return records, events, {"halted": halted,
                             "steps_executed": stop if halted else steps}


def label_rule(state: tuple, actual: tuple, rules: dict) -> str | None:
    """The exact rule the macro table selects for this transition, or None."""
    if macro.predict_next(state, rules) != actual:
        return None
    if state in rules["literal_rules"]:
        return "LITERAL:" + repr(state)
    for parity in (True, False):
        key = macro.group_key(state, parity=parity)
        if key in rules["group_rules"]:
            return repr(key)
    return None


def affine_count_fit(xs: list[tuple[int, ...]], ys: list[int],
                     var_indices: list[int]) -> dict:
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
            "coefficients": [str(v) for v in coeff[:-1]],
            "intercept": str(coeff[-1]), "exact": True}


def count_fit_with_fallback(xs: list[tuple[int, ...]], ys: list[int],
                            var_indices: list[int]) -> dict:
    """Affine fit over the VAR inputs; on failure retry per mod-k residue
    class of the VAR inputs, k in 2..4 (stage747-style modular refinement).
    Class sizes are reported so singleton classes are visible as weak."""
    fit = affine_count_fit(xs, ys, var_indices)
    if fit["exact"] or not var_indices:
        return fit
    for modulus in (2, 3, 4):
        classes: dict[tuple[int, ...], tuple[list, list]] = defaultdict(lambda: ([], []))
        for x, y in zip(xs, ys):
            sig = tuple(x[i] % modulus for i in var_indices)
            classes[sig][0].append(x)
            classes[sig][1].append(y)
        if len(classes) < 2:
            continue
        sub = {sig: affine_count_fit(cx, cy, var_indices)
               for sig, (cx, cy) in classes.items()}
        if all(f["exact"] for f in sub.values()):
            return {"kind": "modular_piecewise", "exact": True,
                    "modulus": modulus, "var_indices": var_indices,
                    "class_sizes": {repr(sig): len(cy) for sig, (_cx, cy)
                                    in classes.items()},
                    "classes": {repr(sig): f for sig, f in sub.items()}}
    # Boundary split: a VAR input pinned at its minimum observed value is an
    # exactly-guarded subfamily (e.g. a block at the group-cap boundary, the
    # final sweep step before a merge).  Same idea as solve_affine's constant
    # -column folding, applied to event counts.
    for i in var_indices:
        values = {x[i] for x in xs}
        if len(values) < 2:
            continue
        boundary = min(values)
        at_b = [j for j, x in enumerate(xs) if x[i] == boundary]
        above = [j for j, x in enumerate(xs) if x[i] != boundary]
        fit_at = affine_count_fit([xs[j] for j in at_b], [ys[j] for j in at_b],
                                  var_indices)
        fit_above = affine_count_fit([xs[j] for j in above],
                                     [ys[j] for j in above], var_indices)
        if fit_at["exact"] and fit_above["exact"]:
            return {"kind": "boundary_piecewise", "exact": True,
                    "index": i, "boundary": boundary,
                    "var_indices": var_indices,
                    "class_sizes": {"at_boundary": len(at_b),
                                    "above": len(above)},
                    "at_boundary": fit_at, "above": fit_above}
    return fit


def count_from_fit(fit: dict, xvec: tuple[int, ...]) -> int | None:
    if fit["kind"] == "constant":
        return fit["value"]
    if fit["kind"] == "modular_piecewise":
        sig = tuple(xvec[i] % fit["modulus"] for i in fit["var_indices"])
        sub = fit["classes"].get(repr(sig))
        return None if sub is None else count_from_fit(sub, xvec)
    if fit["kind"] == "boundary_piecewise":
        branch = ("at_boundary" if xvec[fit["index"]] == fit["boundary"]
                  else "above")
        return count_from_fit(fit[branch], xvec)
    if fit["kind"] != "affine":
        return None
    value = Fraction(fit["intercept"])
    for i, coefficient in zip(fit["var_indices"], fit["coefficients"]):
        value += Fraction(coefficient) * xvec[i]
    return int(value) if value.denominator == 1 else None


def build_tape_from_rle(rle: tuple[int, ...], side: str, head_gap: int = 0,
                        far_gap: int = 0) -> tuple[dict[int, int], int, int, int]:
    """Faithful record reconstruction: the frontier head sits ``head_gap``
    zero cells beyond the nearest interior 1-run, and the opposite frontier
    extends ``far_gap`` visited-but-zero cells beyond the far 1-run (v2 fix;
    stage750 assumed both margins are zero, true for dossier-1 only).
    Both margins are blank as tape content, but the frontier bounds -- and
    therefore the timing of the next record -- depend on them."""
    interior_len = sum(rle)
    if side == "L":
        head = lo = 0
        start = 1 + head_gap
        hi = head_gap + interior_len + far_gap
    else:
        lo = 0
        start = far_gap
        head = hi = far_gap + interior_len + head_gap
    tape: dict[int, int] = {}
    pos = start
    for i, length in enumerate(rle):
        if i % 2 == 0:
            for cell in range(pos, pos + length):
                tape[cell] = 1
        pos += length
    return tape, lo, hi, head


def run_one_firing(code: str, rle: tuple[int, ...], state: int, side: str,
                   head_gap: int = 0, far_gap: int = 0) -> dict:
    """Raw replay from a literal frontier record through its next expansion."""
    tab, (hstate, hsym), _entries = machine_shape(code)
    tape, lo, hi, head = build_tape_from_rle(rle, side, head_gap, far_gap)
    events: list[dict] = []
    steps = 0
    while True:
        sym = tape.get(head, 0)
        tr = tab.get((state, sym))
        if tr is None:
            return {"halted": True, "steps": steps, "events": events}
        ns, nw, direction = tr
        if ns == hstate:
            safe = tape.get(head + direction, 0) != hsym
            events.append({
                "window": window9(tape, head),
                "relative_site": relative_site(tape, head, lo, hi, direction, hsym),
                "safe": safe,
            })
        if nw:
            tape[head] = 1
        else:
            tape.pop(head, None)
        state = ns
        head += direction
        steps += 1
        if steps > 200_000_000:
            return {"halted": False, "steps": steps, "events": events,
                    "output": None, "error": "firing exceeded step guard"}
        if head < lo or head > hi:
            if head < lo:
                lo = head
            else:
                hi = head
            rle_out = interior_rle(tape, lo, hi)
            return {"halted": False, "steps": steps, "events": events,
                    "output": (state, "L" if head == lo else "R",
                               rle_blocks(rle_out))}


def _search_candidate(first: dict, requested: list[int], rules: dict,
                      label: str, search_indices: list[int]) -> tuple | None:
    """Nearest guard-compatible input for which the macro table selects the
    exact same rule (never a merely predictable neighbouring rule)."""
    for corrections in product(range(4), repeat=len(search_indices)):
        trial = list(requested)
        for i, correction in zip(search_indices, corrections):
            trial[i] += correction
        trial_state = (first["state"], first["side"], tuple(trial))
        trial_pred = macro.predict_next(trial_state, rules)
        if trial_pred is not None and label_rule(trial_state, trial_pred, rules) == label:
            return tuple(trial)
    return None


def synthetic_inputs(label: str, firings: list[dict], rules: dict,
                     var_indices: list[int],
                     boundary_pins: set[tuple[int, int]] = frozenset()
                     ) -> tuple[list[dict], list[dict]]:
    """Guard-compatible fresh inputs plus explicitly logged substitutions.

    ``boundary_pins`` are (block index, value) pairs from boundary_piecewise
    count fits: each gets an extra instance with that block pinned and the
    remaining VAR blocks fresh, so the guarded subfamily is replay-covered.
    """
    first = firings[0]
    base = tuple(first["rle"])
    blocks = tuple(first["blocks"])
    notes: list[dict] = []
    if label.startswith("LITERAL:"):
        notes.append({"reason": "literal rule accepts only its exact input; "
                                "fresh VAR values rejected",
                      "substitution": "replayed the literal observed block values"})
        return [{"name": "literal_guard_compatible", "rle": base,
                 "blocks": blocks}], notes
    if not var_indices:
        return [{"name": "no_VAR_components", "rle": base, "blocks": blocks}], notes
    observed_max = {i: max(f["blocks"][i] for f in firings) for i in var_indices}
    plans = [(f"fresh_offset_{offset}", None, offset) for offset in (13, 26)]
    plans += [(f"boundary_pin_{i}_{value}", (i, value), 13)
              for i, value in sorted(boundary_pins) if i in var_indices]
    out = []
    for name, pin, offset in plans:
        requested = list(blocks)
        search_indices = list(var_indices)
        for i in var_indices:
            requested[i] = max(macro.CAP_SMALL + 1, observed_max[i] + offset)
        if pin is not None:
            requested[pin[0]] = pin[1]
            search_indices = [i for i in var_indices if i != pin[0]]
        candidate = _search_candidate(first, requested, rules, label,
                                      search_indices)
        if candidate is None:
            notes.append({"reason": "no guard-compatible fresh candidate after parity search",
                          "instance": name, "requested": requested})
            continue
        if list(candidate) != requested:
            notes.append({"reason": "initial fresh candidate rejected by rule guard",
                          "instance": name, "substitution": list(candidate)})
        rle = list(base)
        for j, val in enumerate(candidate):
            rle[2 * j] = val
        out.append({"name": name, "rle": tuple(rle), "blocks": candidate})
    if not out:
        matching = next((rule for key, rule in rules["group_rules"].items()
                         if repr(key) == label), None)
        guard = (matching or {}).get("guard", {})
        guarded = list(blocks)
        for index, value in guard.items():
            guarded[int(index)] = int(value)
        guarded_blocks = tuple(guarded)
        guarded_state = (first["state"], first["side"], guarded_blocks)
        guarded_pred = macro.predict_next(guarded_state, rules)
        if guarded_pred is not None and label_rule(guarded_state, guarded_pred, rules) == label:
            guarded_rle = list(base)
            for j, value in enumerate(guarded_blocks):
                guarded_rle[2 * j] = value
            notes.append({"reason": "fresh values prohibited by exact affine guard",
                          "substitution": list(guarded_blocks)})
            out.append({"name": "exact_guard_compatible", "rle": tuple(guarded_rle),
                        "blocks": guarded_blocks})
    return out, notes


def discharge(code: str, steps: int) -> dict:
    tab, (hstate, hsym), entries = machine_shape(code)
    records, events, run = raw_run(code, steps)
    result_base = {
        "code": code,
        "undefined": {"state": state_name(hstate), "symbol": hsym},
        "entry_transitions": [f"{state_name(s)}{b}" for s, b in entries],
        "run": {**run, "records_captured": len(records),
                "entry_events": len(events),
                "n_unsafe_events": sum(not e["safe"] for e in events)},
        "honest_scope": ("uniformity + fresh-value replay evidence for the "
                         "induction premise; not itself a proof"),
    }
    if run["halted"]:
        return {**result_base, "status": "HALTED"}
    if len(records) < STARTUP_PREFIX + 2:
        return {**result_base, "status": "INSUFFICIENT_RECORDS"}

    steps_index = [r["step"] for r in records]
    fit_end = bisect_right(steps_index, FIT_STEPS)
    fit_records = records[:fit_end]
    rules = macro.fit_macro_rules(fit_records, startup_prefix=STARTUP_PREFIX)
    replay = macro.replay_records(records, max(fit_end - 1, 0), rules)
    result_base["fit"] = {"fit_steps": FIT_STEPS, "fit_records": len(fit_records),
                          "group_rules": len(rules["group_rules"]),
                          "literal_rules": len(rules["literal_rules"]),
                          "n_conflicts": rules["n_conflicts"], "replay": replay}
    if rules["n_conflicts"] or not replay["exact"]:
        return {**result_base, "status": "MACRO_NOT_EXACT"}

    firing_by_rule: dict[str, list[dict]] = defaultdict(list)
    labels: list[str] = []
    for i, (left, right) in enumerate(zip(records, records[1:])):
        label = ("STARTUP" if i < STARTUP_PREFIX
                 else label_rule(macro.astate(left), macro.astate(right), rules))
        labels.append(label or "UNMATCHED")
        if label not in {None, "STARTUP"}:
            firing_by_rule[label].append({
                "record_index": i, "rle": tuple(left["full_interior_rle"]),
                "blocks": tuple(left["blocks"]), "state": left["state"],
                "side": left["side"], "head_gap": left["head_gap"],
                "far_gap": left["far_gap"],
                "next_astate": macro.astate(right), "events": []})
    by_index = {f["record_index"]: f
                for fs in firing_by_rule.values() for f in fs}
    unassigned_events = 0
    for event in events:
        i = bisect_right(steps_index, event["step"]) - 1
        if 0 <= i < len(labels) and i in by_index:
            by_index[i]["events"].append(event)
        else:
            unassigned_events += 1
    result_base["run"]["unassigned_events"] = unassigned_events

    analyses: dict[str, dict] = {}
    for label, fs in tqdm(firing_by_rule.items(), desc="stage753 rule analyses"):
        # Extended input vector: full interior RLE plus both edge margins.
        xvecs = [f["rle"] + (f["head_gap"], f["far_gap"]) for f in fs]
        lengths = {len(x) for x in xvecs}
        template_ok = len(lengths) == 1
        if template_ok:
            width = next(iter(lengths))
            canonical = tuple(
                xvecs[0][p] if len({x[p] for x in xvecs}) == 1 else "VAR"
                for p in range(width))
        else:
            canonical = ()
        pairs = sorted({(e["window"], e["relative_site"])
                        for f in fs for e in f["events"]})
        var_indices = [i for i in range(len(fs[0]["blocks"]))
                       if canonical and canonical[2 * i] == "VAR"]
        head_gap_var = bool(canonical) and canonical[-2] == "VAR"
        far_gap_var = bool(canonical) and canonical[-1] == "VAR"
        # Count-fit regressors: VAR blocks, plus either margin when it varies.
        n_blocks = len(fs[0]["blocks"])
        fit_vecs = [f["blocks"] + (f["head_gap"], f["far_gap"]) for f in fs]
        fit_var = (var_indices + ([n_blocks] if head_gap_var else [])
                   + ([n_blocks + 1] if far_gap_var else []))
        pair_fits: dict[tuple[str, str], dict] = {}
        for pair in pairs:
            counts = [sum((e["window"], e["relative_site"]) == pair
                          for e in f["events"]) for f in fs]
            pair_fits[pair] = count_fit_with_fallback(fit_vecs, counts, fit_var)
        # Literal self-check: replaying the first observed firing exactly must
        # reproduce the observed macro transition and its event multiset.
        self_first = fs[0]
        self_replay = run_one_firing(code, self_first["rle"], self_first["state"],
                                     self_first["side"], self_first["head_gap"],
                                     self_first["far_gap"])
        self_events = Counter((e["window"], e["relative_site"])
                              for e in self_replay["events"])
        observed_events = Counter((e["window"], e["relative_site"])
                                  for e in self_first["events"])
        self_check_ok = (not self_replay["halted"]
                         and self_replay.get("output") == self_first["next_astate"]
                         and self_events == observed_events)
        uniform_ok = (template_ok and self_check_ok
                      and all(v["exact"] for v in pair_fits.values()))
        first = None
        if not template_ok:
            baseline = len(xvecs[0])
            mismatch = next(j for j, x in enumerate(xvecs) if len(x) != baseline)
            first = {"kind": "rle_length_mismatch", "firing_index": mismatch,
                     "record_index": fs[mismatch]["record_index"],
                     "expected_length": baseline,
                     "actual_length": len(xvecs[mismatch])}
        elif not self_check_ok:
            first = {"kind": "literal_self_check_failed",
                     "record_index": self_first["record_index"],
                     "expected": repr(self_first["next_astate"]),
                     "actual": repr(self_replay.get("output")),
                     "halted": self_replay["halted"],
                     "event_diff": {f"{a}|{b}": [observed_events.get((a, b), 0),
                                                 self_events.get((a, b), 0)]
                                    for (a, b) in set(observed_events) | set(self_events)
                                    if observed_events.get((a, b), 0)
                                    != self_events.get((a, b), 0)}}
        else:
            bad = next(((pair, fit) for pair, fit in pair_fits.items()
                        if not fit["exact"]), None)
            if bad:
                first = {"kind": "non_affine_event_count",
                         "pair": list(bad[0]), "fit": bad[1]}
        # Fresh margins: constant across firings, or exactly derived from the
        # VAR blocks; otherwise the first firing's value with an explicit note.
        margin_fits = {name: count_fit_with_fallback(
                           [f["blocks"] for f in fs], [f[name] for f in fs],
                           var_indices)
                       for name in ("head_gap", "far_gap")}
        boundary_pins = {(fit["index"], fit["boundary"])
                         for fit in pair_fits.values()
                         if fit["kind"] == "boundary_piecewise"
                         and fit["index"] < n_blocks}
        synth, guard_notes = synthetic_inputs(label, fs, rules, var_indices,
                                              boundary_pins)
        replay_results = []
        for instance in synth:
            margins = {}
            for name, mfit in margin_fits.items():
                value = (count_from_fit(mfit, instance["blocks"])
                         if mfit["exact"] else None)
                if value is None or value < 0:
                    value = self_first[name]
                    if (head_gap_var if name == "head_gap" else far_gap_var):
                        guard_notes.append({"reason": f"{name} not exactly "
                                                      "derivable from VAR blocks; "
                                                      "used first firing's value",
                                            "instance": instance["name"]})
                margins[name] = value
            expected = macro.predict_next(
                (fs[0]["state"], fs[0]["side"], instance["blocks"]), rules)
            firing = run_one_firing(code, instance["rle"], fs[0]["state"],
                                    fs[0]["side"], margins["head_gap"],
                                    margins["far_gap"])
            actual = firing.get("output")
            event_counts = Counter((e["window"], e["relative_site"])
                                   for e in firing["events"])
            instance_vec = (tuple(instance["blocks"])
                            + (margins["head_gap"], margins["far_gap"]))
            expected_counts = {pair: count_from_fit(fit, instance_vec)
                               for pair, fit in pair_fits.items()}
            event_ok = (all(e["safe"] for e in firing["events"])
                        and all(event_counts.get(pair, 0) == count
                                for pair, count in expected_counts.items())
                        and all(pair in expected_counts for pair in event_counts))
            macro_ok = not firing["halted"] and expected == actual
            result = {"name": instance["name"], "blocks": list(instance["blocks"]),
                      "steps": firing["steps"], "macro_expected": repr(expected),
                      "macro_actual": repr(actual), "macro_ok": macro_ok,
                      "event_expected_counts": {f"{a}|{b}": c for (a, b), c
                                                in expected_counts.items()},
                      "event_actual_counts": {f"{a}|{b}": c for (a, b), c
                                              in event_counts.items()},
                      "all_landings_safe": all(e["safe"] for e in firing["events"]),
                      "event_structure_ok": event_ok,
                      "passed": macro_ok and event_ok}
            replay_results.append(result)
            if first is None and not result["passed"]:
                first = {"kind": "synthetic_replay_mismatch", **result}
        analyses[label] = {"n_firings": len(fs),
                           "abstract_input_rle": list(canonical),
                           "var_block_indices": var_indices,
                           "head_gap_var": head_gap_var,
                           "far_gap_var": far_gap_var,
                           "template_uniform": template_ok,
                           "literal_self_check_ok": self_check_ok,
                           "pair_count_fits": {f"{a}|{b}": fit for (a, b), fit
                                               in pair_fits.items()},
                           "uniformity_ok": uniform_ok,
                           "synthetic_replays": replay_results,
                           "guard_rejections_or_substitutions": guard_notes,
                           "first_counterexample": first}

    obligations = sorted({(label, e["window"])
                          for label, fs in firing_by_rule.items()
                          for f in fs for e in f["events"]})
    rows = []
    for label, window in obligations:
        analysis = analyses[label]
        relevant = {key: fit for key, fit in analysis["pair_count_fits"].items()
                    if key.startswith(window + "|")}
        passed = (bool(relevant) and analysis["uniformity_ok"]
                  and all(r["passed"] for r in analysis["synthetic_replays"]))
        rows.append({"rule": label, "window": window,
                     "relative_site_count_fits": relevant,
                     "n_firings": analysis["n_firings"],
                     "abstract_input_rle": analysis["abstract_input_rle"],
                     "var_block_indices": analysis["var_block_indices"],
                     "uniformity_ok": analysis["uniformity_ok"],
                     "synthetic_replays": analysis["synthetic_replays"],
                     "guard_rejections_or_substitutions":
                         analysis["guard_rejections_or_substitutions"],
                     "verdict": "DISCHARGED_UNIFORM" if passed else "FAILED",
                     "first_counterexample":
                         None if passed else analysis["first_counterexample"]})

    n_failed = sum(r["verdict"] == "FAILED" for r in rows)
    n_unsafe = result_base["run"]["n_unsafe_events"]
    status = ("ALL_DISCHARGED_UNIFORM"
              if n_failed == 0 and n_unsafe == 0 else "FAILED")
    return {**result_base, "status": status, "obligations": rows,
            "summary": {"n_obligations": len(rows),
                        "n_discharged": len(rows) - n_failed,
                        "n_failed": n_failed, "n_unsafe_events": n_unsafe,
                        "status": status}}


def main() -> None:
    parser = argparse.ArgumentParser()
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--code")
    source.add_argument("--input")
    parser.add_argument("--steps", type=int, default=100_000_000)
    args = parser.parse_args()
    if args.steps < 1:
        raise ValueError("--steps must be positive")
    codes = ([args.code.strip()] if args.code else
             [line.strip() for line in Path(args.input).read_text().splitlines()
              if line.strip()])
    OUT.mkdir(parents=True, exist_ok=True)
    for code in codes:
        path = OUT / f"{hashlib.sha1(code.encode()).hexdigest()[:12]}.json"
        if path.exists():
            print(f"skip existing {path}")
            continue
        output = discharge(code, args.steps)
        path.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
        summary = output.get("summary", {})
        print(f"{code}: status={output['status']} "
              f"obligations={summary.get('n_obligations')} "
              f"discharged={summary.get('n_discharged')}")


if __name__ == "__main__":
    main()
