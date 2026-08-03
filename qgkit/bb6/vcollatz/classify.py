"""Collatz-lens characterization of BB(6) holdouts.

Combines bounded frontier-record simulation (ported from the stage655 miner),
compact-growth cryptid scoring, and a stage652-style abstraction-class
heuristic. Everything here is bounded empirical evidence: no function in this
module proves halting or non-halting, and vector-map results are block-length
projections only (``EXTRACT_HALT_FAITHFUL`` is ``False``).
"""

from __future__ import annotations

import itertools
import math
from collections import Counter

# Exact codes visible on BusyBeaverWiki's Cryptids page as of 2026-07-27
# (same set as experiments/stage655_new_cryptid_miner.py).
KNOWN_WIKI_CRYPTIDS = frozenset({
    "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA",  # Antihydra
    "1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD",  # Space Needle
    "1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA",
    "1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC",
    "1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---",
    "1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB",
    "1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC",
    "1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF",
    "1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB",
    "1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA",
    "1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE",
    "1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA",
    "1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE",
    "1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE",
    "1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC",
    "1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE",
    "1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB",
})

# Local Dvisetu candidate (stage655 top hit; deep-dived in stages 656-744).
DVISETU_CODE = "1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB"


def _parse(code: str):
    tab = {}
    n = len(code.split("_"))
    for state, group in enumerate(code.split("_")):
        for sym in (0, 1):
            tok = group[3 * sym:3 * sym + 3]
            if tok == "---" or tok[2] == "-":
                continue
            ns = ord(tok[2]) - ord("A")
            if ns < n:
                tab[(state, sym)] = (ns, int(tok[0]), 1 if tok[1] == "R" else -1)
    return tab


def _one_blocks(tape: dict[int, int], lo: int, hi: int) -> tuple[int, ...]:
    cells = (tape.get(pos, 0) for pos in range(lo, hi + 1))
    return tuple(sum(1 for _ in grp) for bit, grp in itertools.groupby(cells) if bit == 1)


def simulate_records(code: str, steps: int = 700_000, cap: int = 350):
    """Bounded raw simulation collecting tape-frontier expansion records.

    Returns ``(halted, stop_step, records)``. ``halted`` is definite within the
    budget; a ``False`` value is only "did not halt in ``steps`` steps".
    """
    tab = _parse(code)
    tape: dict[int, int] = {}
    head = 0
    state = 0
    lo = hi = 0
    records: list[dict] = []
    for step in range(steps):
        sym = tape.get(head, 0)
        tr = tab.get((state, sym))
        if tr is None:
            return True, step, records
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
            blocks = _one_blocks(tape, lo, hi)
            records.append({
                "step": step + 1,
                "side": "L" if head == lo else "R",
                "state": state,
                "width": hi - lo + 1,
                "ones": sum(blocks),
                "blocks": blocks,
            })
            if len(records) >= cap:
                break
    return False, steps, records


def _best_period(seq: list, max_period: int = 12):
    if len(seq) < 24:
        return None, 0.0
    tail = seq[len(seq) // 3:]
    best = (None, 0.0)
    for period in range(1, min(max_period, len(tail) // 2) + 1):
        matches = 0
        total = 0
        for i in range(period, len(tail)):
            total += 1
            if tail[i] == tail[i - period]:
                matches += 1
        frac = matches / total if total else 0.0
        if frac > best[1]:
            best = (period, frac)
    return best


def _delta_signature(records):
    sigs = []
    for a, b in zip(records, records[1:]):
        ba = a["blocks"]
        bb = b["blocks"]
        if len(ba) != len(bb):
            continue
        delta = tuple(y - x for x, y in zip(ba, bb))
        if max((abs(x) for x in delta), default=0) <= 12:
            sigs.append(delta)
    if not sigs:
        return None, 0, []
    common, count = Counter(sigs).most_common(1)[0]
    return common, count, sigs


def compact_growth_features(records: list[dict]) -> dict | None:
    """Score how cryptid-like (compact, structured, growing) a record set is.

    Returns ``None`` when there are fewer than 40 records. The score is the
    stage655 heuristic; it ranks candidates for human reverse-engineering and
    proves nothing.
    """
    if len(records) < 40:
        return None
    dims = [len(r["blocks"]) for r in records]
    widths = [r["width"] for r in records]
    ones = [r["ones"] for r in records]
    dmax = max(dims)
    growth = max(widths[-1] / max(widths[0], 1), ones[-1] / max(ones[0], 1))
    d_period, d_match = _best_period(dims)
    side_period, side_match = _best_period([r["side"] for r in records], 8)
    delta, delta_count, deltas = _delta_signature(records)
    delta_frac = delta_count / len(deltas) if deltas else 0.0
    dim_entropy = len(set(dims)) / max(len(dims), 1)
    score = (
        20.0 * min(math.log(max(growth, 1.0000001), 2), 12)
        + 35.0 * d_match
        + 15.0 * side_match
        + 35.0 * delta_frac
        + max(0, 20.0 * (1.0 - dim_entropy * 5.0))
        - 1.5 * dmax
    )
    return {
        "score": round(float(score), 3),
        "dmax": dmax,
        "growth": round(float(growth), 3),
        "d_period": d_period,
        "d_period_match": round(d_match, 3),
        "side_period": side_period,
        "side_period_match": round(side_match, 3),
        "dominant_delta": list(delta) if delta is not None else None,
        "dominant_delta_frac": round(delta_frac, 3),
        "dims_tail": dims[-36:],
    }


def abstraction_class(dims: list[int], d_cap: int = 12) -> str:
    """Stage652-style abstraction class from the block-dimension trajectory.

    Heuristic only (Dcap matches stage652's Dcap=12):
    ``SHORT_UNDECIDED`` for <20 dims, ``GROWING_DIM`` when the tail exceeds
    ``d_cap``, ``FIXED_DIM_CARRY`` when the tail is constant, otherwise
    ``BOUNDED_VARYING``.
    """
    if len(dims) < 20:
        return "SHORT_UNDECIDED"
    tail = dims[len(dims) // 3:]
    if max(tail) > d_cap:
        return "GROWING_DIM"
    if len(set(tail)) == 1:
        return "FIXED_DIM_CARRY"
    return "BOUNDED_VARYING"


CRYPTID_SCORE_THRESHOLD = 200.0


def characterize_holdout(
    code: str,
    *,
    decider_budget: int = 100_000,
    backward_depth: int = 800,
    ctl_radius: int = 7,
    far_dfa_states: int = 10,
    sim_steps: int = 700_000,
    extract_steps: int = 1_000_000,
    extract_max_dim: int = 8,
    run_decider: bool = True,
) -> dict:
    """Characterize one holdout through the Collatz lens.

    Order: sound decider chain (certified verdicts only) -> exact vector-map
    projection extraction -> compact-growth cryptid scoring -> abstraction
    class. Only the decider chain produces certainty; every other label is
    bounded empirical structure, and ``VCOLLATZ_EXACT_PROJECTION`` never
    implies machine-level non-halting.
    """
    from qgkit.bb6.bbchallenge import parse_bbchallenge
    from qgkit.bb6.toc import classify as toc_classify
    from qgkit.bb6.types import ConfidenceTier, Outcome
    from qgkit.bb6.vcollatz.extract import extract_vector_map

    decider_row = None
    if run_decider:
        verdict = toc_classify(
            parse_bbchallenge(code),
            budget=decider_budget,
            backward_depth=backward_depth,
            ctl_radius=ctl_radius,
            far_dfa_states=far_dfa_states,
        )
        decider_row = {
            "outcome": verdict.outcome.name,
            "toc_class": verdict.toc_class,
            "tier": verdict.tier.name,
            "decider": (verdict.evidence or {}).get("decider"),
        }
        if (verdict.tier is ConfidenceTier.CERTIFIED
                and verdict.toc_class == "bouncer"):
            # stage647 / 2026-07-18 falsified this step-4 induction on BB(6).
            decider_row["demoted"] = "unsound_bouncer_certificate_2026-07-18"
        elif verdict.tier is ConfidenceTier.CERTIFIED:
            if verdict.outcome is Outcome.HALTS:
                label = "DECIDED_HALTS"
            else:
                label = f"DECIDED_NONHALT:{verdict.toc_class}"
            return {
                "code": code,
                "label": label,
                "decided": True,
                "decider": decider_row,
                "features": None,
                "vmap": None,
                "abstraction_class": None,
                "novel": False,
            }

    halted, _stop, records = simulate_records(code, steps=sim_steps)
    features = None if halted else compact_growth_features(records)
    dims = [len(r["blocks"]) for r in records]
    a_class = abstraction_class(dims)

    vmap_row = None
    vgc = None
    if not halted:
        try:
            vgc = extract_vector_map(code, max_steps=extract_steps,
                                     max_dim=extract_max_dim)
        except Exception:
            vgc = None
    if vgc is not None:
        vmap_row = {
            "d": int(vgc.d),
            "mod_vec": list(vgc.mod_vec),
            "n_branches": len(vgc.branches),
            "halt_faithful": False,
        }

    if vmap_row is not None:
        label = "VCOLLATZ_EXACT_PROJECTION"
    elif features is not None and features["score"] >= CRYPTID_SCORE_THRESHOLD:
        label = "CRYPTID_COMPACT_GROWTH"
    else:
        label = a_class

    return {
        "code": code,
        "label": label,
        "decided": False,
        "decider": decider_row,
        "features": features,
        "vmap": vmap_row,
        "abstraction_class": a_class,
        "novel": code not in KNOWN_WIKI_CRYPTIDS and code != DVISETU_CODE,
    }
