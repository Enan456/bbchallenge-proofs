# Collatz-Lens Mass Classification Sweep + Next-Cryptid Discovery Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking. **Per user preference, code implementation is routed through the Codex rescue agent (`codex:codex-rescue`), not general-purpose subagents.**

**Goal:** Mass-classify all 1094 BB(6) holdouts through the vector-Collatz emulation lens into one honest taxonomy, and produce deep-characterization dossiers for the top novel cryptid candidates beyond Dvisetu.

**Architecture:** Reusable per-machine characterization lives in a new `qgkit/bb6/vcollatz/classify.py` module (decider chain → exact vector-map extraction → compact-growth cryptid scoring → abstraction-class fallback). Two thin experiment drivers consume it: `stage745` (resumable full sweep over the 1094 holdouts, JSONL + summary + markdown) and `stage746` (long-run dossiers for the top-K novel candidates). This mirrors the repo's existing pattern: logic in `qgkit/bb6/`, stage scripts in `experiments/`.

**Tech Stack:** Python 3 stdlib + `tqdm` (matching existing `qgkit/bb6/vcollatz/` modules). Existing building blocks: `qgkit.bb6.toc.classify` (sound decider chain), `qgkit.bb6.bbchallenge.parse_bbchallenge`, `qgkit.bb6.vcollatz.extract.extract_vector_map`, stage655 compact-growth scoring (ported into the module), stage652 abstraction classes (`Dcap=12`).

> **Execution deviation (2026-07-28):** during the first sweep run, `toc.classify`'s step-4 `certify_bouncer` re-issued CERTIFIED verdicts on frontier machines whose certificates were falsified on 2026-07-18 (stage647: 135/137 are non-uniform carry-counters). `characterize_holdout` now demotes `toc_class == "bouncer"` certifications to undecided (`decider.demoted = "unsound_bouncer_certificate_2026-07-18"`) and falls through to structural characterization; `bouncer_sound` remains trusted. 42 tainted rows were purged from `rows.jsonl` and re-swept. Commit `eaeb139a`.

## Global Constraints

- **Honest labeling (project-wide rule):** `extract_vector_map` returns a block-length PROJECTION with `EXTRACT_HALT_FAITHFUL = False`; a projection-level result is NEVER labeled as machine-level non-halting. No `candidate_nonhalting` call at machine level (that path caused the killed false solve — see vcollatz memory). Labels use "candidate"/"projection" wording throughout.
- **tqdm on every long-running loop** (user requirement).
- **Resumability:** the mass sweep must skip codes already present in its JSONL output so multi-hour runs survive interruption.
- Stage numbering: new scripts are `stage745` and `stage746` (last used: 744).
- Input file: `experiments/outputs/BB6_holdouts_1094.txt` (1094 lines, std format codes).
- Known wiki cryptids: the 17-code set currently in `experiments/stage655_new_cryptid_miner.py:36-54` (`KNOWN_WIKI_CRYPTIDS`), plus the Dvisetu candidate `1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB`, are excluded from "novel" ranking.
- Commit prefix convention: `feat(bb6): ...`, `docs(bb6): ...`; commits end with `Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>`.

---

### Task 1: Compact-growth features + abstraction class in `qgkit/bb6/vcollatz/classify.py`

Port the stage655 scoring logic into the package (stage655 stays as-is; new consumers import from the module) and add the stage652-style abstraction-class heuristic.

**Files:**
- Create: `qgkit/bb6/vcollatz/classify.py`
- Test: `tests/bb6/test_vcollatz_classify.py`

**Interfaces:**
- Consumes: nothing from other tasks (self-contained simulation, same tape convention as `experiments/stage655_new_cryptid_miner.py:76-116`).
- Produces (used by Tasks 2, 3, 5):
  - `KNOWN_WIKI_CRYPTIDS: frozenset[str]` (17 codes), `DVISETU_CODE: str`
  - `simulate_records(code: str, steps: int = 700_000, cap: int = 350) -> tuple[bool, int, list[dict]]` — `(halted, stop_step, records)`; each record has keys `step, side, state, width, ones, blocks`.
  - `compact_growth_features(records: list[dict]) -> dict | None` — `None` when `len(records) < 40`; otherwise dict with keys `score, dmax, growth, d_period, d_period_match, side_period, side_period_match, dominant_delta, dominant_delta_frac, dims_tail`.
  - `abstraction_class(dims: list[int], d_cap: int = 12) -> str` — one of `"SHORT_UNDECIDED" | "GROWING_DIM" | "FIXED_DIM_CARRY" | "BOUNDED_VARYING"`.

- [ ] **Step 1: Write the failing tests**

```python
# tests/bb6/test_vcollatz_classify.py
from __future__ import annotations

from qgkit.bb6.vcollatz.classify import (
    KNOWN_WIKI_CRYPTIDS,
    abstraction_class,
    compact_growth_features,
    simulate_records,
)

ANTIHYDRA = "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"
BB2_HALTER = "1RB1LB_1LA---"


def test_simulate_records_detects_halt():
    halted, stop_step, _records = simulate_records(BB2_HALTER, steps=1_000)
    assert halted
    assert stop_step < 10


def test_simulate_records_antihydra_produces_frontier_records():
    halted, _stop_step, records = simulate_records(ANTIHYDRA, steps=200_000, cap=200)
    assert not halted
    assert len(records) >= 40
    assert {"step", "side", "state", "width", "ones", "blocks"} <= set(records[0])


def test_compact_growth_features_short_input_is_none():
    assert compact_growth_features([]) is None


def test_compact_growth_features_antihydra_has_score():
    _halted, _stop, records = simulate_records(ANTIHYDRA, steps=200_000, cap=200)
    features = compact_growth_features(records)
    # Antihydra grows and keeps compact block structure; features must exist.
    assert features is not None
    assert isinstance(features["score"], float)
    assert features["dmax"] >= 1


def test_abstraction_class_labels():
    assert abstraction_class([2] * 10) == "SHORT_UNDECIDED"
    assert abstraction_class(list(range(1, 40))) == "GROWING_DIM"
    assert abstraction_class([3] * 60) == "FIXED_DIM_CARRY"
    assert abstraction_class([2, 3, 4, 3, 2, 3, 4, 3] * 10) == "BOUNDED_VARYING"


def test_known_wiki_cryptids_set_size():
    assert len(KNOWN_WIKI_CRYPTIDS) == 17
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `python3 -m pytest tests/bb6/test_vcollatz_classify.py -v`
Expected: FAIL with `ModuleNotFoundError: No module named 'qgkit.bb6.vcollatz.classify'`

- [ ] **Step 3: Write the implementation**

```python
# qgkit/bb6/vcollatz/classify.py
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
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `python3 -m pytest tests/bb6/test_vcollatz_classify.py -v`
Expected: 6 PASS

- [ ] **Step 5: Commit**

```bash
git add qgkit/bb6/vcollatz/classify.py tests/bb6/test_vcollatz_classify.py
git commit -m "feat(bb6): add collatz-lens compact-growth features + abstraction classes

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>"
```

---

### Task 2: `characterize_holdout` orchestrator

**Files:**
- Modify: `qgkit/bb6/vcollatz/classify.py` (append)
- Test: `tests/bb6/test_vcollatz_classify.py` (append)

**Interfaces:**
- Consumes: Task 1 functions; `qgkit.bb6.toc.classify(tm, budget=..., backward_depth=..., ctl_radius=..., far_dfa_states=...) -> Verdict` (fields `outcome: Outcome`, `toc_class: str`, `tier: ConfidenceTier`, `evidence: dict`); `qgkit.bb6.bbchallenge.parse_bbchallenge(code) -> TMSpec`; `qgkit.bb6.vcollatz.extract.extract_vector_map(code, max_steps, max_dim) -> Optional[VGCMap]` (fields `d, mod_vec, branches, halt_vec`).
- Produces (used by Tasks 3 and 5):
  - `characterize_holdout(code: str, *, decider_budget: int = 100_000, backward_depth: int = 800, ctl_radius: int = 7, far_dfa_states: int = 10, sim_steps: int = 700_000, extract_steps: int = 1_000_000, extract_max_dim: int = 8, run_decider: bool = True) -> dict` with keys `code, label, decided, decider, features, vmap, abstraction_class, novel`.
  - Label values: `"DECIDED_HALTS"`, `"DECIDED_NONHALT:<toc_class>"`, `"VCOLLATZ_EXACT_PROJECTION"`, `"CRYPTID_COMPACT_GROWTH"`, or one of the four abstraction classes.

- [ ] **Step 1: Write the failing tests (append to test file)**

```python
from qgkit.bb6.vcollatz.classify import characterize_holdout

TRANSLATED_CYCLER = "1RB---_1RA---"


def test_characterize_decides_translated_cycler():
    row = characterize_holdout(TRANSLATED_CYCLER, decider_budget=5_000,
                               sim_steps=5_000, extract_steps=5_000)
    assert row["decided"] is True
    assert row["label"].startswith("DECIDED_NONHALT")


def test_characterize_decides_halter():
    row = characterize_holdout(BB2_HALTER, decider_budget=5_000,
                               sim_steps=5_000, extract_steps=5_000)
    assert row["label"] == "DECIDED_HALTS"


def test_characterize_antihydra_undecided_with_features():
    row = characterize_holdout(ANTIHYDRA, decider_budget=2_000,
                               backward_depth=50, ctl_radius=2,
                               far_dfa_states=4,
                               sim_steps=200_000, extract_steps=50_000)
    assert row["decided"] is False
    assert row["features"] is not None
    assert row["label"] in {
        "VCOLLATZ_EXACT_PROJECTION", "CRYPTID_COMPACT_GROWTH",
        "GROWING_DIM", "FIXED_DIM_CARRY", "BOUNDED_VARYING", "SHORT_UNDECIDED",
    }
    assert row["novel"] is False  # Antihydra is a known wiki cryptid


def test_characterize_skip_decider():
    row = characterize_holdout(ANTIHYDRA, run_decider=False,
                               sim_steps=100_000, extract_steps=20_000)
    assert row["decided"] is False
    assert row["decider"] is None
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `python3 -m pytest tests/bb6/test_vcollatz_classify.py -v -k characterize`
Expected: FAIL with `ImportError: cannot import name 'characterize_holdout'`

- [ ] **Step 3: Write the implementation (append to classify.py)**

```python
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
        if verdict.tier is ConfidenceTier.CERTIFIED:
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
```

- [ ] **Step 4: Run the full test file**

Run: `python3 -m pytest tests/bb6/test_vcollatz_classify.py -v`
Expected: 10 PASS

- [ ] **Step 5: Run the existing vcollatz suite to check for regressions**

Run: `python3 -m pytest tests/bb6/test_vcollatz_extract.py tests/bb6/test_vcollatz_reduce.py tests/bb6/test_toc.py -q`
Expected: all PASS

- [ ] **Step 6: Commit**

```bash
git add qgkit/bb6/vcollatz/classify.py tests/bb6/test_vcollatz_classify.py
git commit -m "feat(bb6): add characterize_holdout collatz-lens orchestrator

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>"
```

---

### Task 3: `stage745` resumable mass-sweep driver

**Files:**
- Create: `experiments/stage745_collatz_mass_sweep.py`

**Interfaces:**
- Consumes: `characterize_holdout` (Task 2 signature), `experiments/outputs/BB6_holdouts_1094.txt`.
- Produces: `experiments/outputs/stage745/rows.jsonl` (one dict per machine, Task 2 schema plus `"error"` key on crash), `experiments/outputs/stage745/summary.json`, `experiments/outputs/stage745/classification.md`. Consumed by Task 5.

- [ ] **Step 1: Write the driver**

```python
# experiments/stage745_collatz_mass_sweep.py
"""Stage 745 -- Collatz-lens mass classification of all BB(6) holdouts.

Runs characterize_holdout over every machine in BB6_holdouts_1094.txt and
writes a per-machine JSONL plus an aggregate summary and markdown table.
Resumable: codes already present in rows.jsonl are skipped, so the sweep can
be interrupted and relaunched.

Only decider-chain rows are certainties; all other labels are bounded
empirical structure and prove nothing.

Run:
    python3 experiments/stage745_collatz_mass_sweep.py [--profile fast|deep]
        [--limit N] [--input PATH]
"""
from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

from tqdm import tqdm

from qgkit.bb6.vcollatz.classify import characterize_holdout

OUT = Path(__file__).resolve().parent / "outputs" / "stage745"
DEFAULT_INPUT = Path(__file__).resolve().parent / "outputs" / "BB6_holdouts_1094.txt"

PROFILES = {
    # Holdouts already survived huge decider budgets; "fast" keeps the chain
    # cheap and spends time on structure instead.
    "fast": dict(decider_budget=20_000, backward_depth=200, ctl_radius=4,
                 far_dfa_states=6, sim_steps=700_000, extract_steps=1_000_000),
    "deep": dict(decider_budget=200_000, backward_depth=800, ctl_radius=7,
                 far_dfa_states=10, sim_steps=2_000_000, extract_steps=3_000_000),
}


def load_done(path: Path) -> set[str]:
    done: set[str] = set()
    if path.exists():
        for line in path.read_text().splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                done.add(json.loads(line)["code"])
            except (json.JSONDecodeError, KeyError):
                continue
    return done


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--profile", choices=sorted(PROFILES), default="fast")
    ap.add_argument("--limit", type=int, default=0, help="stop after N new rows (0 = all)")
    ap.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    args = ap.parse_args()

    OUT.mkdir(parents=True, exist_ok=True)
    rows_path = OUT / "rows.jsonl"
    codes = [ln.strip() for ln in args.input.read_text().splitlines() if ln.strip()]
    done = load_done(rows_path)
    todo = [c for c in codes if c not in done]
    if args.limit:
        todo = todo[: args.limit]

    kwargs = PROFILES[args.profile]
    with rows_path.open("a") as fh:
        for code in tqdm(todo, desc=f"stage745 sweep ({args.profile})"):
            try:
                row = characterize_holdout(code, **kwargs)
            except Exception as exc:  # keep the sweep alive; record the crash
                row = {"code": code, "label": "ERROR", "decided": False,
                       "error": repr(exc)}
            fh.write(json.dumps(row, sort_keys=True) + "\n")
            fh.flush()

    all_rows = [json.loads(ln) for ln in rows_path.read_text().splitlines() if ln.strip()]
    label_counts = Counter(r["label"] for r in all_rows)
    scored = [r for r in all_rows
              if r.get("features") and not r["decided"] and r.get("novel")]
    scored.sort(key=lambda r: r["features"]["score"], reverse=True)
    summary = {
        "profile": args.profile,
        "n_input": len(codes),
        "n_classified": len(all_rows),
        "label_counts": dict(label_counts),
        "n_novel_scored": len(scored),
        "top_novel": [
            {"code": r["code"], "label": r["label"],
             "score": r["features"]["score"], "dmax": r["features"]["dmax"],
             "dominant_delta": r["features"]["dominant_delta"],
             "dominant_delta_frac": r["features"]["dominant_delta_frac"]}
            for r in scored[:25]
        ],
    }
    (OUT / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")

    lines = ["# Stage 745 -- Collatz-lens mass classification", "",
             f"Input machines: {len(codes)}  |  classified: {len(all_rows)}", "",
             "| label | count |", "|---|---|"]
    for label, count in label_counts.most_common():
        lines.append(f"| {label} | {count} |")
    lines += ["", "## Top novel compact-growth candidates", "",
              "| score | dmax | dominant delta | frac | code |", "|---|---|---|---|---|"]
    for r in summary["top_novel"]:
        lines.append(f"| {r['score']} | {r['dmax']} | {r['dominant_delta']} "
                     f"| {r['dominant_delta_frac']} | `{r['code']}` |")
    (OUT / "classification.md").write_text("\n".join(lines) + "\n")

    print(json.dumps({k: v for k, v in summary.items() if k != "top_novel"}, indent=2))
    print(f"wrote {OUT / 'summary.json'}")


if __name__ == "__main__":
    main()
```

- [ ] **Step 2: Smoke-test on 5 machines**

Run: `python3 experiments/stage745_collatz_mass_sweep.py --limit 5`
Expected: tqdm bar over 5 machines; `experiments/outputs/stage745/rows.jsonl` has 5 lines; summary printed with `label_counts`.

- [ ] **Step 3: Verify resumability**

Run: `python3 experiments/stage745_collatz_mass_sweep.py --limit 5`
Expected: bar shows 5 *new* machines (total rows now 10) — previously classified codes skipped.

- [ ] **Step 4: Commit**

```bash
git add experiments/stage745_collatz_mass_sweep.py
git commit -m "feat(bb6): add stage745 collatz-lens mass classification sweep

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>"
```

---

### Task 4: Run the full sweep and record results

**Files:**
- Create: `docs/results/2026-07-28-bb6-collatz-mass-classification.md`
- Output: `experiments/outputs/stage745/` (rows.jsonl, summary.json, classification.md)

- [ ] **Step 1: Launch the full sweep in the background**

Run: `python3 experiments/stage745_collatz_mass_sweep.py --profile fast` (background; expect roughly 1–3 s/machine → 20–60 min for 1094)

- [ ] **Step 2: On completion, sanity-check the output**

Run: `python3 -c "import json;d=json.load(open('experiments/outputs/stage745/summary.json'));print(d['n_classified'],d['label_counts'])"`
Expected: `n_classified == 1094`; label counts roughly consistent with stage652 (GROWING_DIM the largest bucket; DECIDED_* small or zero since these survived big budgets already).

- [ ] **Step 3: Write the results doc**

Create `docs/results/2026-07-28-bb6-collatz-mass-classification.md` with: date, script, profile, the label-count table (copy from `classification.md`), the top-10 novel candidate table, an honest-scope paragraph (bounded evidence only; projections ≠ machine-level proofs; any DECIDED rows should be cross-checked before claiming coverage progress), and next-step pointer to stage746 dossiers.

- [ ] **Step 4: Commit**

```bash
git add experiments/outputs/stage745 docs/results/2026-07-28-bb6-collatz-mass-classification.md
git commit -m "docs(bb6): record stage745 collatz-lens mass classification results

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>"
```

---

### Task 5: `stage746` next-cryptid dossiers

Deep characterization of the top-K novel candidates from stage745, in the style of the Dvisetu focused check (one-block checkpoints + dominant transfer rule + high-budget projection extraction).

**Files:**
- Create: `experiments/stage746_next_cryptid_dossiers.py`

**Interfaces:**
- Consumes: `experiments/outputs/stage745/summary.json` (`top_novel` list), `simulate_records`, `compact_growth_features`, `KNOWN_WIKI_CRYPTIDS`, `DVISETU_CODE` from `qgkit.bb6.vcollatz.classify`; `extract_vector_map` from `qgkit.bb6.vcollatz.extract`.
- Produces: `experiments/outputs/stage746/dossier_<idx>.json` per candidate and `experiments/outputs/stage746/dossiers.md`.

- [ ] **Step 1: Write the driver**

```python
# experiments/stage746_next_cryptid_dossiers.py
"""Stage 746 -- Deep dossiers for the top novel cryptid candidates.

For each top-scoring novel machine from the stage745 sweep, run a long
focused simulation collecting one-block checkpoint values (the tape moments
where exactly one 1-run exists), measure the dominant two-block transfer
rule at frontier records, and attempt a high-budget exact vector-map
projection. Bounded evidence only; nothing here decides any machine.

Run:
    python3 experiments/stage746_next_cryptid_dossiers.py [--top K]
        [--steps N] [--checkpoint-cap M]
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

from tqdm import tqdm

from qgkit.bb6.vcollatz.classify import (
    DVISETU_CODE, KNOWN_WIKI_CRYPTIDS, _parse, compact_growth_features,
    simulate_records,
)
from qgkit.bb6.vcollatz.extract import extract_vector_map

OUT = Path(__file__).resolve().parent / "outputs" / "stage746"
SUMMARY_745 = Path(__file__).resolve().parent / "outputs" / "stage745" / "summary.json"


def focused_run(code: str, steps: int, checkpoint_cap: int = 4_000):
    """Long raw run: halt check + one-block checkpoint series.

    A checkpoint is recorded whenever the tape holds exactly one 1-run;
    consecutive duplicates are collapsed. tqdm-wrapped because this is the
    long loop (up to hundreds of millions of steps).
    """
    tab = _parse(code)
    tape: dict[int, int] = {}
    head = 0
    state = 0
    lo = hi = 0
    checkpoints: list[int] = []
    ones = 0
    run_breaks = 0  # number of 0-gaps inside [min_one, max_one]
    min_one = None
    max_one = None

    def snapshot_one_block() -> int | None:
        cells = (tape.get(p, 0) for p in range(lo, hi + 1))
        runs = [sum(1 for _ in g) for b, g in itertools.groupby(cells) if b == 1]
        return runs[0] if len(runs) == 1 else None

    check_every = 64
    for step in tqdm(range(steps), desc=f"focused {code[:12]}", mininterval=5.0):
        sym = tape.get(head, 0)
        tr = tab.get((state, sym))
        if tr is None:
            return {"halted": True, "halt_step": step, "checkpoints": checkpoints}
        ns, nw, direction = tr
        if nw:
            tape[head] = 1
        else:
            tape.pop(head, None)
        state = ns
        head += direction
        lo = min(lo, head)
        hi = max(hi, head)
        if step % check_every == 0 and len(checkpoints) < checkpoint_cap:
            value = snapshot_one_block()
            if value is not None and (not checkpoints or checkpoints[-1] != value):
                checkpoints.append(value)
    return {"halted": False, "halt_step": None, "checkpoints": checkpoints}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--top", type=int, default=8)
    ap.add_argument("--steps", type=int, default=50_000_000)
    ap.add_argument("--checkpoint-cap", type=int, default=4_000)
    args = ap.parse_args()

    OUT.mkdir(parents=True, exist_ok=True)
    summary = json.loads(SUMMARY_745.read_text())
    candidates = [r for r in summary["top_novel"]
                  if r["code"] not in KNOWN_WIKI_CRYPTIDS
                  and r["code"] != DVISETU_CODE][: args.top]

    md = ["# Stage 746 -- next-cryptid candidate dossiers", ""]
    for idx, cand in enumerate(candidates):
        code = cand["code"]
        run = focused_run(code, steps=args.steps,
                          checkpoint_cap=args.checkpoint_cap)
        _h, _s, records = simulate_records(code, steps=3_000_000, cap=600)
        features = compact_growth_features(records)
        try:
            vgc = extract_vector_map(code, max_steps=3_000_000, max_dim=6)
        except Exception:
            vgc = None
        dossier = {
            "code": code,
            "stage745_score": cand["score"],
            "halted_in_focused_run": run["halted"],
            "halt_step": run["halt_step"],
            "focused_steps": args.steps,
            "one_block_checkpoints_head": run["checkpoints"][:80],
            "n_checkpoints": len(run["checkpoints"]),
            "features_3m": features,
            "vmap": None if vgc is None else {
                "d": int(vgc.d), "mod_vec": list(vgc.mod_vec),
                "n_branches": len(vgc.branches), "halt_faithful": False,
            },
        }
        path = OUT / f"dossier_{idx:02d}.json"
        path.write_text(json.dumps(dossier, indent=2, sort_keys=True) + "\n")
        md += [f"## {idx}: `{code}`", "",
               f"- stage745 score: {cand['score']}",
               f"- focused run: {'HALTED at ' + str(run['halt_step']) if run['halted'] else f'no halt in {args.steps:,} steps'}",
               f"- one-block checkpoints observed: {len(run['checkpoints'])}",
               f"- checkpoint head: {run['checkpoints'][:24]}",
               f"- dominant delta (3M-step records): {features['dominant_delta'] if features else None} "
               f"@ {features['dominant_delta_frac'] if features else None}",
               f"- exact projection map: {dossier['vmap']}", ""]
    (OUT / "dossiers.md").write_text("\n".join(md) + "\n")
    print(f"wrote {len(candidates)} dossiers to {OUT}")


if __name__ == "__main__":
    main()
```

- [ ] **Step 2: Smoke-test with tiny budgets**

Run: `python3 experiments/stage746_next_cryptid_dossiers.py --top 1 --steps 200000 --checkpoint-cap 50`
Expected: one `dossier_00.json` + `dossiers.md`; no crash.

- [ ] **Step 3: Full run in background**

Run: `python3 experiments/stage746_next_cryptid_dossiers.py --top 8 --steps 50000000` (background; ~minutes per candidate at CPython speed — budget ≥1 h total)

- [ ] **Step 4: Commit code + outputs**

```bash
git add experiments/stage746_next_cryptid_dossiers.py experiments/outputs/stage746
git commit -m "feat(bb6): add stage746 next-cryptid dossier generator + dossiers

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>"
```

---

### Task 6: Results doc + memory update

**Files:**
- Modify: `docs/results/2026-07-28-bb6-collatz-mass-classification.md` (append dossier section)
- Memory: new file in the project memory directory + MEMORY.md index line

- [ ] **Step 1:** Append a "Next-cryptid dossiers" section to the results doc: per-candidate one-line summary (halted?, checkpoint structure, dominant rule, projection map), which candidates merit a Dvisetu-style deep dive next, honest-scope statement.
- [ ] **Step 2:** Write memory `bb6-collatz-mass-classification.md` (type: project) recording: the taxonomy counts over 1094, top novel candidates, and where the artifacts live; link `[[vcollatz-emulator]]`, `[[bb6-untested-frontier-taxonomy]]`.
- [ ] **Step 3: Commit**

```bash
git add docs/results/2026-07-28-bb6-collatz-mass-classification.md
git commit -m "docs(bb6): finalize collatz mass-classification + dossier results

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>"
```

---

## Self-Review

- **Spec coverage:** "proceed on quantum emulation of collatz style behaviour to discover more cryptids" → Tasks 1–2 (lens + orchestrator) and Task 5 (dossiers for the next candidates after Dvisetu); "plan for a full sweep that would provide a mass classification" → Tasks 3–4 (resumable 1094-machine sweep + results doc). Covered.
- **Placeholder scan:** all code steps carry complete code; doc steps enumerate their required content. No TBDs.
- **Type consistency:** `characterize_holdout` keys (`code/label/decided/decider/features/vmap/abstraction_class/novel`) match what stage745 reads; stage746 reads `summary.json["top_novel"]` entries with `code/score/dmax/dominant_delta/dominant_delta_frac`, which stage745 writes. `simulate_records` return triple consistent across Tasks 1, 2, 5.
