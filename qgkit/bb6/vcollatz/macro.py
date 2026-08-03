"""Fail-closed fitting of frontier-record macro systems.

This is the reusable form of the verified stage747 fitter.  Its claims are
strictly bounded: rules are accepted only after exact rational verification
on the supplied records, and prediction abstains when no guarded rule applies.
"""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction

CAP_SMALL = 4


def astate(rec: dict) -> tuple:
    """Return the augmented macro state carried by a frontier record."""
    return (rec["state"], rec["side"], tuple(rec["blocks"]))


def group_key(state: tuple, parity: bool = False) -> tuple:
    st, side, blocks = state
    caps = tuple(min(c, CAP_SMALL) for c in blocks)
    key = (st, side, len(blocks), caps)
    if parity:
        key += (tuple(c % 2 for c in blocks),)
    return key


def solve_affine(pairs: list[tuple[tuple, tuple]]):
    """Fit an exact guarded affine map, using stage747's fail-closed solver."""
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
            return None
        if any(all(x == 0 for x in row[:-1]) and row[-1] != 0 for row in aug):
            return None
        sol = [Fraction(0)] * n_unknown
        for i, c in enumerate(piv_cols):
            sol[c] = aug[i][-1]
        full = [Fraction(0)] * (d_in + 1)
        for k, col in enumerate(var_cols):
            full[col] = sol[k]
        full[d_in] = sol[-1]
        coeffs.append(full)
    for a, b in pairs:
        for j in range(d_out):
            val = sum(coeffs[j][i] * a[i] for i in range(d_in)) + coeffs[j][-1]
            if val != b[j]:
                return None
    guard = {str(col): val for col, val in const_cols.items()}
    return [[str(x) for x in row] for row in coeffs], guard


def _apply_affine(coeffs: list, guard: dict, vec: tuple) -> tuple | None:
    for col, val in guard.items():
        if vec[int(col)] != val:
            return None
    out = []
    for row in coeffs:
        val = sum(Fraction(row[i]) * vec[i] for i in range(len(vec))) + Fraction(row[-1])
        if val.denominator != 1:
            return None
        out.append(int(val))
    return tuple(out)


def fit_group(members: list[tuple[tuple, tuple]]) -> dict | None:
    outs = {(o[0], o[1]) for _, o in members}
    if len(outs) != 1:
        return None
    out_st, out_side = next(iter(outs))
    pairs = [(i[2], o[2]) for i, o in members]
    if len({len(b) for _, b in pairs}) != 1:
        return None
    deltas = {tuple(y - x for x, y in zip(a, b)) for a, b in pairs
              if len(a) == len(b)}
    if len(deltas) == 1 and len(pairs[0][0]) == len(pairs[0][1]):
        return {"kind": "delta", "delta": list(next(iter(deltas))),
                "out_state": out_st, "out_side": out_side, "support": len(members)}
    solved = solve_affine(pairs)
    if solved is None:
        return None
    coeffs, guard = solved
    return {"kind": "affine", "coeffs": coeffs, "guard": guard,
            "out_state": out_st, "out_side": out_side, "support": len(members)}


def build_rules(transitions: list[tuple[tuple, tuple]]) -> tuple[dict, dict]:
    """Return generalized group rules and explicitly flagged literal rules."""
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
        sub: dict = defaultdict(list)
        for a, b in members:
            sub[group_key(a, parity=True)].append((a, b))
        fitted = {k: fit_group(m) for k, m in sub.items()}
        if len(sub) > 1 and all(v is not None for v in fitted.values()):
            group_rules.update(fitted)
            continue
        for a, b in members:
            literal_rules[a] = {"kind": "literal", "out": [b[0], b[1], list(b[2])],
                                "support": 1}
    return group_rules, literal_rules


def fit_macro_rules(records: list[dict], startup_prefix: int = 8) -> dict:
    """Fit a frozen macro table after the non-generalized startup prefix."""
    transitions = [(astate(a), astate(b))
                   for a, b in zip(records[startup_prefix:], records[startup_prefix + 1:])]
    successors: dict = defaultdict(set)
    for a, b in transitions:
        successors[a].add(b)
    group_rules, literal_rules = build_rules(transitions)
    return {"group_rules": group_rules, "literal_rules": literal_rules,
            "n_conflicts": sum(len(v) > 1 for v in successors.values())}


def predict_next(state: tuple, rules: dict) -> tuple | None:
    """Predict one macro transition, or abstain for an unseen/guarded state."""
    group_rules, literal_rules = rules["group_rules"], rules["literal_rules"]
    if state in literal_rules:
        out = literal_rules[state]["out"]
        return (out[0], out[1], tuple(out[2]))
    for parity in (True, False):
        rule = group_rules.get(group_key(state, parity=parity))
        if rule is None:
            continue
        if rule["kind"] == "delta":
            blocks = tuple(x + d for x, d in zip(state[2], rule["delta"]))
        else:
            blocks = _apply_affine(rule["coeffs"], rule.get("guard", {}), state[2])
            if blocks is None:
                return None
        return (rule["out_state"], rule["out_side"], blocks)
    return None


def replay_records(records: list[dict], start: int, rules: dict) -> dict:
    """Replay record transitions exactly, reporting coverage separately."""
    n_checked = n_mismatches = n_uncovered = 0
    for i in range(start, len(records) - 1):
        pred = predict_next(astate(records[i]), rules)
        actual = astate(records[i + 1])
        n_checked += 1
        if pred != actual:
            n_mismatches += 1
            n_uncovered += pred is None
    return {"exact": n_mismatches == 0, "n_transitions_checked": n_checked,
            "n_mismatches": n_mismatches, "n_uncovered": n_uncovered}
