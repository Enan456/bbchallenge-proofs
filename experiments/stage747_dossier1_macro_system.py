"""Stage 747 -- Exact macro system for the dossier-1 cryptid candidate.

Machine: 1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB (halts iff state F reads 0).

Derives a deterministic macro system over the augmented frontier-record state
(machine_state, side, blocks) and verifies it fail-closed:

* FIT: group transitions by an input-derivable key (state, side, dim,
  per-component small-caps); explain each group with the simplest exact rule
  that fits ALL its members -- constant-delta, else exact rational affine
  (solved over Fractions, verified on every pair), else parity-refined, else a
  flagged literal. Generalized rules only outside the startup prefix.
* REPLAY (in-sample): the rule table must reproduce every post-startup
  transition of the fit run exactly -- (state, side, blocks) all three.
* OUT-OF-SAMPLE: the frozen table must reproduce every transition of a longer
  run beyond the fit horizon exactly; unseen group keys count as failures.
* CHECKPOINT LAW: consecutive full-collapse (dim-1) pairs are split into
  SINGLE_CYCLE (intervening dim <= 3) and MULTI_LEVEL; the law
  n -> (3n+7)/2 is verified on every non-startup single-cycle pair.
* HALT LOCALIZATION (bounded): count state-F appearances at records.

Everything here is bounded empirical evidence; PASS_EXACT_MACRO_SYSTEM means
the macro system reproduced every observed transition exactly, not that the
machine is decided.

Run:
    python3 experiments/stage747_dossier1_macro_system.py
"""
from __future__ import annotations

import json
import sys
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from tqdm import tqdm

from qgkit.bb6.vcollatz.classify import simulate_records

CODE = "1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB"
OUT = Path(__file__).resolve().parent / "outputs" / "stage747"
STARTUP_PREFIX = 8
CAP_SMALL = 4
FIT_STEPS = 20_000_000
FIT_RECORDS = 20_000
VERIFY_STEPS = 100_000_000
VERIFY_RECORDS = 100_000


def astate(rec: dict) -> tuple:
    return (rec["state"], rec["side"], tuple(rec["blocks"]))


def group_key(state: tuple, parity: bool = False) -> tuple:
    st, side, blocks = state
    caps = tuple(min(c, CAP_SMALL) for c in blocks)
    key = (st, side, len(blocks), caps)
    if parity:
        key += (tuple(c % 2 for c in blocks),)
    return key


def solve_affine(pairs: list[tuple[tuple, tuple]]):
    """Fit out[j] = sum_i A[j][i]*in[i] + c[j] exactly over Fractions.

    Input columns that are constant across all pairs are folded into the
    constant term (their coefficient is set to 0) and recorded as an exact
    guard {col: value}; at apply time the guard must match or the rule
    abstains. Returns (coeffs, guard) iff one affine map reproduces every
    pair exactly; None otherwise.
    """
    d_in = len(pairs[0][0])
    d_out = len(pairs[0][1])
    if any(len(a) != d_in or len(b) != d_out for a, b in pairs):
        return None
    const_cols = {i: pairs[0][0][i] for i in range(d_in)
                  if all(a[i] == pairs[0][0][i] for a, _ in pairs)}
    var_cols = [i for i in range(d_in) if i not in const_cols]
    n_unknown = len(var_cols) + 1
    rows = [tuple(Fraction(a[i]) for i in var_cols) + (Fraction(1),)
            for a, _ in pairs]
    coeffs: list[list[Fraction]] = []
    for j in range(d_out):
        rhs = [Fraction(b[j]) for _, b in pairs]
        aug = [list(row) + [r] for row, r in zip(rows, rhs)]
        piv_cols: list[int] = []
        r = 0
        for c in range(n_unknown):
            piv = next((i for i in range(r, len(aug)) if aug[i][c] != 0), None)
            if piv is None:
                continue
            aug[r], aug[piv] = aug[piv], aug[r]
            aug[r] = [x / aug[r][c] for x in aug[r]]
            for i in range(len(aug)):
                if i != r and aug[i][c] != 0:
                    aug[i] = [x - aug[i][c] * y for x, y in zip(aug[i], aug[r])]
            piv_cols.append(c)
            r += 1
        if r < n_unknown:
            return None  # underdetermined: refuse to guess free parameters
        if any(all(x == 0 for x in row[:-1]) and row[-1] != 0 for row in aug):
            return None  # inconsistent
        sol = [Fraction(0)] * n_unknown
        for i, c in enumerate(piv_cols):
            sol[c] = aug[i][-1]
        # reassemble full-width row: 0 for constant cols, folded constant term
        full = [Fraction(0)] * (d_in + 1)
        for k, col in enumerate(var_cols):
            full[col] = sol[k]
        full[d_in] = sol[-1]
        coeffs.append(full)
    for a, b in pairs:  # exact re-verification on every pair (fail-closed)
        for j in range(d_out):
            val = sum(coeffs[j][i] * a[i] for i in range(d_in)) + coeffs[j][-1]
            if val != b[j]:
                return None
    guard = {str(col): val for col, val in const_cols.items()}
    return [[str(x) for x in row] for row in coeffs], guard


def apply_affine(coeffs: list, guard: dict, vec: tuple) -> tuple | None:
    for col, val in guard.items():
        if vec[int(col)] != val:
            return None  # guard on folded constant column failed: abstain
    out = []
    for row in coeffs:
        val = sum(Fraction(row[i]) * vec[i] for i in range(len(vec))) + Fraction(row[-1])
        if val.denominator != 1:
            return None
        out.append(int(val))
    return tuple(out)


def fit_group(members: list[tuple[tuple, tuple]]) -> dict | None:
    """Explain one group's (in_state -> out_state) members with a single rule."""
    outs = {(o[0], o[1]) for _, o in members}
    if len(outs) != 1:
        return None
    out_st, out_side = next(iter(outs))
    pairs = [(i[2], o[2]) for i, o in members]
    dims_out = {len(b) for _, b in pairs}
    if len(dims_out) != 1:
        return None
    deltas = {tuple(y - x for x, y in zip(a, b)) for a, b in pairs
              if len(a) == len(b)}
    if len(deltas) == 1 and len(pairs[0][0]) == len(pairs[0][1]):
        return {"kind": "delta", "delta": list(next(iter(deltas))),
                "out_state": out_st, "out_side": out_side,
                "support": len(members)}
    solved = solve_affine(pairs)
    if solved is not None:
        coeffs, guard = solved
        return {"kind": "affine", "coeffs": coeffs, "guard": guard,
                "out_state": out_st, "out_side": out_side,
                "support": len(members)}
    return None


def build_rules(transitions: list[tuple[tuple, tuple]]) -> tuple[dict, dict]:
    """Return (group_rules, literal_rules). Fail-closed; literals flagged."""
    groups: dict = defaultdict(list)
    for a, b in transitions:
        groups[group_key(a)].append((a, b))
    group_rules: dict = {}
    literal_rules: dict = {}
    for key, members in groups.items():
        rule = fit_group(members)
        if rule is not None:
            group_rules[key] = rule
            continue
        sub: dict = defaultdict(list)  # refine by parity
        for a, b in members:
            sub[group_key(a, parity=True)].append((a, b))
        fitted = {k: fit_group(m) for k, m in sub.items()}
        if len(sub) > 1 and all(v is not None for v in fitted.values()):
            group_rules.update(fitted)
            continue
        for a, b in members:  # literal fallback, flagged
            literal_rules[a] = {"kind": "literal",
                                "out": [b[0], b[1], list(b[2])],
                                "support": 1}
    return group_rules, literal_rules


def predict(state: tuple, group_rules: dict, literal_rules: dict):
    if state in literal_rules:
        o = literal_rules[state]["out"]
        return (o[0], o[1], tuple(o[2]))
    for parity in (True, False):
        rule = group_rules.get(group_key(state, parity=parity))
        if rule is None:
            continue
        blocks = state[2]
        if rule["kind"] == "delta":
            nb = tuple(x + d for x, d in zip(blocks, rule["delta"]))
        else:
            nb = apply_affine(rule["coeffs"], rule.get("guard", {}), blocks)
            if nb is None:
                return None
        return (rule["out_state"], rule["out_side"], nb)
    return None


def replay(records: list[dict], start: int, group_rules: dict,
           literal_rules: dict, label: str) -> dict:
    n_checked = 0
    n_mismatch = 0
    n_uncovered = 0
    first: list[dict] = []
    for i in tqdm(range(start, len(records) - 1), desc=f"replay {label}",
                  mininterval=5.0):
        a, b = astate(records[i]), astate(records[i + 1])
        pred = predict(a, group_rules, literal_rules)
        n_checked += 1
        if pred != b:
            n_mismatch += 1
            if pred is None:
                n_uncovered += 1
            if len(first) < 3:
                first.append({"index": i, "input": repr(a),
                              "predicted": repr(pred), "actual": repr(b)})
    return {"exact": n_mismatch == 0, "n_transitions_checked": n_checked,
            "n_mismatches": n_mismatch, "n_uncovered": n_uncovered,
            "first_mismatches": first, "label": label}


def checkpoint_analysis(records: list[dict]) -> dict:
    blocks = [tuple(r["blocks"]) for r in records]
    cps = [(i, b[0]) for i, b in enumerate(blocks) if len(b) == 1]
    pairs = []
    for (i1, n1), (i2, n2) in zip(cps, cps[1:]):
        md = max(len(b) for b in blocks[i1:i2 + 1])
        pairs.append({"n": n1, "next": n2, "max_dim_between": md,
                      "class": "SINGLE_CYCLE" if md <= 3 else "MULTI_LEVEL"})
    law_ok, law_bad = [], []
    for p in pairs:
        if p["class"] != "SINGLE_CYCLE" or p["n"] <= 1:
            continue
        if p["n"] % 2 == 1 and (3 * p["n"] + 7) % 2 == 0 \
                and (3 * p["n"] + 7) // 2 == p["next"]:
            law_ok.append(p)
        else:
            law_bad.append(p)
    return {
        "collapse_values": [v for _, v in cps],
        "pairs": pairs,
        "single_cycle_law": "n odd -> n' = (3n+7)/2",
        "n_single_cycle_verified": len(law_ok),
        "n_single_cycle_failures": len(law_bad),
        "single_cycle_failures": law_bad,
        "multi_level_pairs": [p for p in pairs if p["class"] == "MULTI_LEVEL"],
        "exact_on_single_cycle": not law_bad,
    }


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)

    halted, _stop, fit_recs = simulate_records(CODE, steps=FIT_STEPS,
                                               cap=FIT_RECORDS)
    assert not halted
    transitions = [(astate(a), astate(b))
                   for a, b in zip(fit_recs[STARTUP_PREFIX:],
                                   fit_recs[STARTUP_PREFIX + 1:])]
    succ = defaultdict(set)
    for a, b in transitions:
        succ[a].add(b)
    n_conf = sum(1 for v in succ.values() if len(v) > 1)

    group_rules, literal_rules = build_rules(transitions)

    in_sample = replay(fit_recs, STARTUP_PREFIX, group_rules, literal_rules,
                       "in-sample")

    halted2, _stop2, ver_recs = simulate_records(CODE, steps=VERIFY_STEPS,
                                                 cap=VERIFY_RECORDS)
    assert not halted2
    oos_start = len(fit_recs)  # transitions beyond the fit horizon only
    out_sample = replay(ver_recs, oos_start, group_rules, literal_rules,
                        "out-of-sample")

    ckpt = checkpoint_analysis(ver_recs)
    f_at_records = sum(1 for r in ver_recs if r["state"] == 5)
    state_counts = Counter(r["state"] for r in ver_recs)

    status = ("PASS_EXACT_MACRO_SYSTEM"
              if in_sample["exact"] and out_sample["exact"]
              and n_conf == 0 else "PARTIAL")

    rules_out = {
        "code": CODE,
        "macro_state": "(machine_state, side, blocks)",
        "group_rules": [
            {"key": repr(k), **v} for k, v in sorted(
                group_rules.items(), key=lambda kv: -kv[1]["support"])
        ],
        "literal_rules": [
            {"input": repr(k), **v} for k, v in literal_rules.items()
        ],
        "n_group_rules": len(group_rules),
        "n_literal_rules": len(literal_rules),
    }
    verify_out = {
        "code": CODE,
        "determinism_conflicts_augmented_state": n_conf,
        "in_sample": in_sample,
        "out_of_sample": out_sample,
        "checkpoint_law": ckpt,
        "halt_localization": {
            "halts_iff": "state F reads 0",
            "state_F_at_records": f_at_records,
            "state_counts_at_records": dict(state_counts),
            "raw_no_halt_steps": VERIFY_STEPS,
        },
    }
    summary = {
        "code": CODE,
        "status": status,
        "fit": {"steps": FIT_STEPS, "records": len(fit_recs),
                "transitions": len(transitions),
                "determinism_conflicts": n_conf},
        "rules": {"group": len(group_rules), "literal": len(literal_rules)},
        "in_sample_exact": in_sample["exact"],
        "out_of_sample_exact": out_sample["exact"],
        "out_of_sample_transitions": out_sample["n_transitions_checked"],
        "checkpoint_single_cycle_verified": ckpt["n_single_cycle_verified"],
        "checkpoint_single_cycle_failures": ckpt["n_single_cycle_failures"],
        "multi_level_pairs": len(ckpt["multi_level_pairs"]),
        "state_F_at_records": f_at_records,
    }
    (OUT / "rules.json").write_text(json.dumps(rules_out, indent=2) + "\n")
    (OUT / "verify.json").write_text(json.dumps(verify_out, indent=2) + "\n")
    (OUT / "summary.json").write_text(json.dumps(summary, indent=2,
                                                 sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
