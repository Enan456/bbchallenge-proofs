#!/usr/bin/env python3
"""stage756: the incision atlas (plan 3, task 4).

For the stage753 obligation-queue machines, extract incision events and plot
them in the non-Euclidean charts of ``qgkit.bb6.geometry``:

* **Antihydra** additionally runs in *exact mode*: the certified event
  process (Lean ``eorbit`` / ``hydraOrbit``, proved equivalent to the full
  abstract orbit by ``eventSafe_iff_safeOrbitA`` /
  ``hydraSafe_iff_safeOrbitA`` in ``packages/bbchallenge``), including the
  exact raw-step cost per event — the measured speedup of boundary-only
  checking.
* every machine runs in *record mode*: the heuristic near-collapse /
  dimension-change proxy (`record_events`), bounded and uncertified.

Outputs (``experiments/outputs/stage756/``): per-machine event JSONL
(resumable: existing files are skipped), ``metrics.json``, ``atlas.md``, and
PNG figures when matplotlib is available.

Honest scope: every number and figure here is bounded empirical structure.
Nothing in this stage proves halting or non-halting for any machine.

Run from repo root:  python experiments/stage756_incision_atlas.py
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import pathlib
import sys

REPO = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))

# exact-mode raw-step counts are astronomically large integers (b ~ 1.5^k)
sys.set_int_max_str_digits(2_000_000)

from tqdm import tqdm  # noqa: E402

from qgkit.bb6.geometry.charts import h2_chart, simplex_chart  # noqa: E402
from qgkit.bb6.geometry.events import antihydra_events, record_events  # noqa: E402

ANTIHYDRA = "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"

try:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    HAVE_MPL = True
except ImportError:  # pragma: no cover
    HAVE_MPL = False


def mid(code: str) -> str:
    return hashlib.sha256(code.encode()).hexdigest()[:12]


def int_log10(n: int) -> float:
    """log10 for integers far beyond float range."""
    if n <= 0:
        return float("-inf")
    s = str(n)
    return len(s) - 1 + math.log10(int(s[:15]) / 10 ** 14)


def run_exact_antihydra(outdir: pathlib.Path, n_events: int) -> dict:
    path = outdir / "events" / f"exact_{mid(ANTIHYDRA)}.jsonl"
    if not path.exists():
        tmp = path.with_suffix(".jsonl.tmp")
        with tmp.open("w") as fh:
            for ev in tqdm(antihydra_events(n_events),
                           total=n_events, desc="antihydra exact"):
                fh.write(json.dumps(ev) + "\n")
        tmp.rename(path)
    events = [json.loads(line) for line in path.open()]

    drops = [e for e in events if e["rule"] == "drop"]
    merges = [e for e in events if e["rule"] == "merge"]
    heads = [e["heads"] for e in events]
    margins = [e["death_margin"] for e in drops]
    cum_raw = 0
    events_in_1e8 = None
    for e in events:
        cum_raw += e["raw_steps"]
        if events_in_1e8 is None and cum_raw > 10 ** 8:
            events_in_1e8 = e["k"]
    metrics = {
        "mode": "exact-certified",
        "machine": "antihydra",
        "n_events": len(events),
        "n_merge": len(merges),
        "n_drop": len(drops),
        "heads_min": min(heads),
        "heads_final": heads[-1],
        "min_death_margin": min(margins) if margins else None,
        "events_within_1e8_raw_steps": events_in_1e8,
        "log10_total_raw_steps": round(int_log10(cum_raw), 2),
        "raw_steps_first_event": events[0]["raw_steps"],
    }

    if HAVE_MPL:
        fig, axes = plt.subplots(1, 3, figsize=(15, 4.5))
        ks = [e["k"] for e in events]
        axes[0].plot(ks, heads, lw=0.7)
        axes[0].set_title("Antihydra heads counter (a) per event")
        axes[0].set_xlabel("event k")
        # simplex chart of (a, m, c): x = barycentric projection
        pts = [simplex_chart([e["a"], e["m"], e["c"]]) for e in events]
        xs = [p[0] + 0.5 * p[1] for p in pts]
        ys = [p[1] * math.sqrt(3) / 2 for p in pts]
        cols = ["tab:red" if e["rule"] == "drop" else "tab:blue"
                for e in events]
        axes[1].scatter(xs, ys, s=3, c=cols, alpha=0.5)
        axes[1].set_title("incisions on the (a, m, c) simplex\n"
                          "(red = drop, blue = merge; death face = m-vertex)")
        h2 = [h2_chart([e["a"], e["m"], e["c"]]) for e in events]
        axes[2].plot([p[0] for p in h2], [p[1] for p in h2], lw=0.5)
        axes[2].set_title("upper-half-plane surrogate (x = imbalance, y = log scale)")
        fig.tight_layout()
        fig.savefig(outdir / "antihydra_exact.png", dpi=130)
        plt.close(fig)
    return metrics


def run_record_machine(code: str, outdir: pathlib.Path, steps: int,
                       cap: int) -> dict:
    path = outdir / "events" / f"records_{mid(code)}.jsonl"
    if path.exists():
        payload = json.loads(path.open().readline())
    else:
        halted, stop_step, events, n_records = record_events(
            code, steps=steps, cap=cap)
        payload = {
            "code": code,
            "halted": halted,
            "stop_step": stop_step,
            "n_records": n_records,
            "events": events,
        }
        with path.open("w") as fh:
            fh.write(json.dumps(payload) + "\n")
    events = payload["events"]
    dims = [e["dims"] for e in events]
    metrics = {
        "mode": "record-heuristic",
        "machine": code,
        "halted": payload["halted"],
        "n_records": payload["n_records"],
        "n_events": len(events),
        "n_near_collapse": sum(1 for e in events if "near_collapse" in e["type"]),
        "n_dim_change": sum(1 for e in events if "dim_change" in e["type"]),
        "dims_min": min(dims) if dims else None,
        "dims_max": max(dims) if dims else None,
        "dims_tail_mean": (round(sum(dims[-max(1, len(dims) // 4):]) /
                                 max(1, len(dims[-max(1, len(dims) // 4):])), 2)
                           if dims else None),
    }

    if HAVE_MPL and events:
        fig, axes = plt.subplots(1, 2, figsize=(11, 4.5))
        triples = [[e["blocks"][0], e["min_block"], e["blocks"][-1]]
                   for e in events if e["blocks"]]
        pts = [simplex_chart(t) for t in triples if sum(t) > 0]
        axes[0].scatter([p[0] + 0.5 * p[1] for p in pts],
                        [p[1] * math.sqrt(3) / 2 for p in pts], s=4, alpha=0.5)
        axes[0].set_title("incision proxies on (first, min, last)-block simplex")
        h2 = [h2_chart(e["blocks"]) for e in events if e["blocks"]]
        axes[1].plot([p[0] for p in h2], [p[1] for p in h2], lw=0.5)
        axes[1].set_title("upper-half-plane surrogate")
        fig.suptitle(code, fontsize=8)
        fig.tight_layout()
        fig.savefig(outdir / f"records_{mid(code)}.png", dpi=130)
        plt.close(fig)
    return metrics


def write_atlas(outdir: pathlib.Path, exact: dict, rows: list[dict],
                steps: int) -> None:
    lines = [
        "# stage756 — incision atlas",
        "",
        "**Honest scope:** every number and figure here is bounded empirical",
        "structure over finite budgets; nothing proves halting or",
        "non-halting for any machine.  Exact mode mirrors the Lean-certified",
        "event process (`packages/bbchallenge`); record mode is a heuristic",
        "proxy.",
        "",
        "## Antihydra — exact certified event process",
        "",
        "| metric | value |",
        "|---|---|",
    ]
    for k, v in exact.items():
        lines.append(f"| {k} | {v} |")
    lines += [
        "",
        f"The `events_within_1e8_raw_steps` row is the measured acceleration",
        f"of boundary-only checking: that many incision events carry the same",
        f"information as 10^8 raw steps (cross-check: stage753 observed",
        f"14,109 E-entry events in its 10^8-step replay).",
        "",
        f"## Record-mode machines (sim budget {steps:,} steps)",
        "",
        "| machine | halted | records | events | near-collapse | dim-change |"
        " dims min/max | dims tail mean |",
        "|---|---|---|---|---|---|---|---|",
    ]
    for r in rows:
        lines.append(
            f"| `{r['machine']}` | {r['halted']} | {r['n_records']} |"
            f" {r['n_events']} | {r['n_near_collapse']} | {r['n_dim_change']} |"
            f" {r['dims_min']}/{r['dims_max']} | {r['dims_tail_mean']} |")
    lines += [
        "",
        "Figures: `antihydra_exact.png`, `records_<id>.png` (when matplotlib",
        "is available).  Event data: `events/*.jsonl` (resumable).",
        "",
    ]
    (outdir / "atlas.md").write_text("\n".join(lines))


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--events", type=int, default=20_000,
                    help="exact-mode Antihydra events (default 20000)")
    ap.add_argument("--steps", type=int, default=200_000,
                    help="record-mode raw steps per machine (default 200000)")
    ap.add_argument("--cap", type=int, default=2_000,
                    help="record cap per machine (default 2000)")
    ap.add_argument("--machines", type=pathlib.Path,
                    default=REPO / "experiments" / "outputs" / "stage753_queue.txt")
    ap.add_argument("--outdir", type=pathlib.Path,
                    default=REPO / "experiments" / "outputs" / "stage756")
    args = ap.parse_args()

    outdir = args.outdir
    (outdir / "events").mkdir(parents=True, exist_ok=True)

    codes = [line.strip() for line in args.machines.open()
             if line.strip() and not line.startswith("#")]

    exact = run_exact_antihydra(outdir, args.events)
    rows = []
    for code in tqdm(codes, desc="record mode"):
        rows.append(run_record_machine(code, outdir, args.steps, args.cap))

    metrics = {"exact_antihydra": exact, "record_machines": rows,
               "have_matplotlib": HAVE_MPL}
    (outdir / "metrics.json").write_text(json.dumps(metrics, indent=2))
    write_atlas(outdir, exact, rows, args.steps)
    print(f"wrote {outdir}/metrics.json and atlas.md "
          f"({len(rows)} record machines; matplotlib={HAVE_MPL})")


if __name__ == "__main__":
    main()
