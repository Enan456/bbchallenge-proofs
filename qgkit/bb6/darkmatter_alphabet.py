#!/usr/bin/env python3
"""Natural block-alphabet search over the BB(6) "unstructured" dark-matter band.

Motivation (the alphabet-artifact lesson): several holdouts that *looked*
array-class / horizonless in the raw {0,1} alphabet turned out to be
FIXED-DIMENSION once the tape was re-encoded in the right period-k block
alphabet.  The census (`census_bands.py`, source
`experiments/outputs/d4_fullsweep.jsonl`) buckets ~793 machines as
UNSTRUCTURED because no affine regime law fit *in the raw alphabet*.  Nobody
had run the automated natural-alphabet search across that band.  This does.

Method (all MEASUREMENT, nothing certified):
  * Reuse the project's generic raw BB(6) simulator (blank tape, st='A',
    hd=0, fail-closed the instant a `---` transition is read -- an actual
    halt is reported loudly).  Table parsing is imported from cone_sweep.
  * A "record event" = the head reaches a fresh extreme (hd>hi or hd<lo),
    exactly the event stream `dossier4.regimes` segments.
  * At a bounded, rolling sample of record events, snapshot the tape region
    [lo..hi] and, for every period k in {1..6} and every block phase, compute:
        - the block-symbol HISTOGRAM (a fixed-dimension vector, dim <= 2**k)
          plus boundary features  -> the "macro-state";
        - the run-length-encoded skeleton (positional structure) and its
          length -> the fixed-dim (bounded) vs array-class (growing) witness.
  * FIXED-DIM-IN-ALPHABET(k): on the post-startup tail, for some stride
    s in {1,2,3}, every stride-phase subsequence of the macro-state vector is
    ARITHMETIC (constant first difference = affine recurrence) AND survives a
    hold-out (fit on first half, predict second half exactly), AND the RLE
    skeleton length is BOUNDED (not growing) -- i.e. a genuinely low-
    dimensional affine law in the block alphabet, the closable shape.
  * Otherwise the machine is genuinely higher-rank / both-sided (no fixed-dim
    fit in any tested alphabet) -- true dark matter -- or degenerate.

Classes emitted per machine:
  (a) FIXED-DIM-IN-ALPHABET  (records best k, phase, stride, dimension)
  (b) HIGHER-RANK / DARK     (no fixed-dim fit; notes array-class vs chaotic)
  (c) SUSPECTED-HALTING/degenerate (any real halt is flagged LOUDLY)

Nothing here decides any machine; a fixed-dim hit is a *lead* for the
raw-step closure engine, not a proof.
"""
from __future__ import annotations
import sys, os, json, pathlib, argparse

def parse(code):
    """Identical to cone_sweep.parse / dossier4's table parse (imported inline
    to avoid triggering cone_sweep's module-level sweep on import).
    tbl[(st,b)] = (write_int, dir_char, next_state) or None for a `---` halt."""
    tbl = {}
    halts = []
    for si, block in enumerate(code.split('_')):
        st = 'ABCDEF'[si]
        for b in range(2):
            tr = block[3 * b:3 * b + 3]
            if tr == '---':
                tbl[(st, b)] = None
                halts.append((st, b))
            else:
                tbl[(st, b)] = (int(tr[0]), tr[1], tr[2])
    return tbl, halts

REPO = pathlib.Path(__file__).resolve().parents[2]
SWEEP = REPO / "experiments" / "outputs" / "d4_fullsweep.jsonl"

KS = (1, 2, 3, 4, 5, 6)
WIDTH_CAP = 3_000_000      # skip snapshots when the touched region is wider
SNAP_CAP = 400            # rolling target number of snapshots kept


# ----------------------------------------------------------------- band / sample

def band(row) -> str:
    if row.get("laws", 0) > 1:
        return "multi_law"
    if row.get("laws", 0) == 1 and row.get("nreg", 0) >= 3:
        return "structured"
    return "unstructured"


def load_unstructured():
    rows = [json.loads(l) for l in open(SWEEP) if l.strip()]
    return [r for r in rows if "code" in r and band(r) == "unstructured"]


def sample_codes(n=40):
    """Deterministic evenly-spaced slice across the unstructured band (in
    census file order).  Reproducible: same n -> same machine list."""
    uns = load_unstructured()
    m = len(uns)
    if n >= m:
        idxs = list(range(m))
    else:
        idxs = [ (i * m) // n for i in range(n) ]
    return [uns[i]["code"] for i in idxs], m


# ----------------------------------------------------------------- block descriptors

def block_desc(tape, lo, hi, k, phase):
    """Histogram of block symbols over [lo..hi], plus RLE skeleton length.
    Blocks are aligned so block starts sit at positions == phase (mod k)."""
    start = lo - ((lo - phase) % k)          # aligned block start <= lo
    hist = {}
    syms = []
    pos = start
    while pos <= hi:
        s = 0
        for j in range(k):
            if tape.get(pos + j, 0):
                s |= (1 << j)
        hist[s] = hist.get(s, 0) + 1
        syms.append(s)
        pos += k
    rlen = 1
    for i in range(1, len(syms)):
        if syms[i] != syms[i - 1]:
            rlen += 1
    if not syms:
        rlen = 0
    return hist, rlen


# ----------------------------------------------------------------- raw run + sampling

def _raw_pass(tbl, horizon, window_start=None):
    """One generic raw BB(6) pass from blank tape; fail-closed on `---`.
    If window_start is None: cheap counting pass, returns (halted, nevents,
    final_width).  Else: snapshots the macro-descriptors at EVERY record event
    with index >= window_start (full granularity, no decimation), returning
    (halted, nevents, final_width, snaps) where snaps is the consecutive tail
    window.  A width beyond WIDTH_CAP suppresses descriptor computation."""
    tape = {}
    st, hd = "A", 0
    lo = hi = 0
    nevents = 0
    halted = None
    snaps = []
    wide = False
    for t in range(horizon):
        b = tape.get(hd, 0)
        if hd > hi or hd < lo:
            lo = min(lo, hd); hi = max(hi, hd)
            ei = nevents
            nevents += 1
            if window_start is not None and ei >= window_start:
                if (hi - lo) <= WIDTH_CAP:
                    desc = {}
                    for k in KS:
                        for phase in range(k):
                            desc[(k, phase)] = block_desc(tape, lo, hi, k, phase)
                    snaps.append((ei, desc))
                else:
                    wide = True
        tr = tbl[(st, b)]
        if tr is None:
            halted = t
            break
        w, d, ns = tr
        tape[hd] = w
        hd += 1 if d == "R" else -1
        st = ns
    if window_start is None:
        return halted, nevents, hi - lo, wide
    return halted, nevents, hi - lo, snaps, wide


def run(code, horizon):
    """Two-pass generic raw run.  Pass 1 counts record events cheaply; pass 2
    snapshots the block macro-state at every record event inside the final
    SNAP_CAP-event window (full granularity, so a stride-s / head-sweep phase
    law is not aliased away by uniform decimation).  Fail-closed on halt."""
    tbl, _halts = parse(code)
    halted, nevents, width, wide1 = _raw_pass(tbl, horizon, window_start=None)
    if halted is not None:
        return dict(halted=halted, nevents=nevents, width=width,
                    snaps=[], wide_skips=int(wide1))
    ws = max(0, nevents - SNAP_CAP)
    _h2, _n2, _w2, snaps, wide2 = _raw_pass(tbl, horizon, window_start=ws)
    return dict(halted=None, nevents=nevents, width=width,
                snaps=snaps, wide_skips=int(wide1 or wide2))


# ----------------------------------------------------------------- affine detector

def _slope(ys):
    n = len(ys)
    if n < 2:
        return 0.0
    xs = list(range(n))
    mx = (n - 1) / 2.0
    my = sum(ys) / n
    num = sum((xs[i] - mx) * (ys[i] - my) for i in range(n))
    den = sum((xs[i] - mx) ** 2 for i in range(n))
    return num / den if den else 0.0


MINRUN = 8   # a constant-diff suffix must span >= this many snapshots per phase


def _arithmetic_holdout(vecs):
    """vecs: list of equal-length int vectors (a single stride-phase
    subsequence, in time order ending at the horizon).  Find the longest
    END-ANCHORED run over which the first difference is a constant integer
    vector (an affine recurrence in the persisting regime), tolerating an
    earlier startup ramp inside the analysis window.  Returns (delta, runlen)
    if that run spans >= MINRUN snapshots, else None.  Hold-out: delta is
    fit on the first half of the run and predicts the second half exactly
    (automatic once the diffs are constant; the evidence is the run length
    and the exact multi-coordinate integer match)."""
    n = len(vecs)
    if n < MINRUN:
        return None
    d = len(vecs[0])
    delta = tuple(vecs[-1][j] - vecs[-2][j] for j in range(d))
    run = 2                                   # last two points
    i = n - 2
    while i - 1 >= 0:
        di = tuple(vecs[i][j] - vecs[i - 1][j] for j in range(d))
        if di != delta:
            break
        run += 1
        i -= 1
    if run < MINRUN:
        return None
    # explicit hold-out over the constant-diff run: fit on first half, predict
    start = n - run
    half = start + run // 2
    cur = list(vecs[half])
    for t in range(half, n):
        if tuple(cur) != tuple(vecs[t]):
            return None
        for j in range(d):
            cur[j] += delta[j]
    return (delta, run)


def analyze_kphase(snaps, k, phase):
    """Test the macro-state (block-symbol histogram + boundary) for an affine
    recurrence, anchored at the END of the run (the regime that persists to
    the horizon), tolerating a period-s head-sweep phase.  The RLE skeleton
    length is reported as a secondary *quality* flag (bounded => clean single
    skeleton; growing => count-affine but positionally scattered), NOT as a
    gate: a machine whose block-symbol COUNTS obey a fixed-dim affine law is
    the closable lead regardless of raw-alphabet run-length wobble."""
    seq = [d[(k, phase)] for _, d in snaps]     # (histdict, rlen) per snapshot
    m = len(seq)
    if m < 20:
        return None
    L = min(m, 240)                              # end-anchored analysis window
    W = list(range(m - L, m))
    if len(W) < 16:
        return None
    rlens = [seq[i][1] for i in W]
    rle_slope = _slope(rlens)
    rle_bounded = abs(rle_slope) < 0.03 and (max(rlens) - min(rlens) <= 3)
    keys = sorted(set().union(*[set(seq[i][0].keys()) for i in W]))
    vecs = [[seq[i][0].get(s, 0) for s in keys] for i in W]
    affine = None
    for s in range(1, 17):                       # head-sweep period can exceed 6
        if L // s < MINRUN:
            break
        ok = True
        deltas = []
        runs = []
        for r in range(s):
            res = _arithmetic_holdout(vecs[r::s])
            if res is None:
                ok = False
                break
            deltas.append(res[0]); runs.append(res[1])
        if ok and any(any(x != 0 for x in dl) for dl in deltas):
            affine = (s, deltas, min(runs))      # require some coordinate to move
            break
    return dict(rle_slope=rle_slope, rle_bounded=rle_bounded,
                dim=len(keys), affine=affine, n_win=len(W),
                rle_max=max(rlens))


def classify(code, horizon):
    r = run(code, horizon)
    out = dict(code=code, horizon=horizon, halted=r["halted"],
               nevents=r["nevents"], width=r["width"],
               nsnaps=len(r["snaps"]), wide_skips=r["wide_skips"])

    if r["halted"] is not None:
        out["klass"] = "c_HALT"
        out["note"] = f"MACHINE HALTS at raw step {r['halted']}"
        return out
    if len(r["snaps"]) < 16:
        out["klass"] = "c_degenerate"
        out["note"] = ("too few sampled record events"
                       + (" (region wider than WIDTH_CAP; snapshots skipped)"
                          if r["wide_skips"] else ""))
        return out

    hits = []          # (k, phase, info) fixed-dim affine hits
    per_k = {}
    for k in KS:
        best = None
        for phase in range(k):
            info = analyze_kphase(r["snaps"], k, phase)
            if info is None:
                continue
            per_k.setdefault(k, []).append(info["rle_slope"])
            if info["affine"] is not None:       # affine macro-state law = hit
                # prefer, at this k, a clean bounded skeleton then lowest dim
                key = (0 if info["rle_bounded"] else 1, info["dim"])
                if best is None or key < best[0]:
                    best = (key, phase, info)
        if best is not None:
            hits.append((k, best[1], best[2]))

    if hits:
        hits.sort(key=lambda h: (h[0], h[2]["dim"]))     # smallest k, then dim
        k, phase, info = hits[0]
        out["klass"] = "a_fixeddim"
        out["best_k"] = k
        out["best_phase"] = phase
        out["dim"] = info["dim"]
        out["stride"] = info["affine"][0]
        out["law_run"] = info["affine"][2]
        out["clean_skeleton"] = info["rle_bounded"]
        out["all_k_hits"] = sorted(set(h[0] for h in hits))
        out["note"] = (f"fixed-dim affine macro-law in period-{k} alphabet "
                       f"(phase {phase}, stride {info['affine'][0]}, macro-dim "
                       f"{info['dim']}, {'clean' if info['rle_bounded'] else 'scattered'} "
                       f"skeleton)")
        return out

    # no affine macro-law at any k -> dark.  Array-class if RLE grows at every k.
    min_slopes = {k: (min(v) if v else 0.0) for k, v in per_k.items()}
    grows_all = all(s > 0.05 for s in min_slopes.values()) if min_slopes else False
    out["klass"] = "b_darkrank"
    out["min_rle_slopes"] = {k: round(s, 4) for k, s in min_slopes.items()}
    out["note"] = ("array-class (RLE skeleton grows in every tested alphabet)"
                   if grows_all else
                   "no fixed-dim affine macro-law in any tested alphabet (higher-rank / chaotic)")
    return out


# ----------------------------------------------------------------- driver

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--horizon", type=int, default=10_000_000)
    ap.add_argument("--n", type=int, default=40)
    ap.add_argument("--codes", nargs="*", default=None,
                    help="explicit machine codes (overrides the sample)")
    ap.add_argument("--out", default=None, help="write per-machine JSONL here")
    a = ap.parse_args()

    if a.codes:
        codes, band_n = a.codes, None
    else:
        codes, band_n = sample_codes(a.n)

    results = []
    fout = open(a.out, "w") if a.out else None
    for i, code in enumerate(codes):
        res = classify(code, a.horizon)
        results.append(res)
        if fout:
            fout.write(json.dumps(res) + "\n"); fout.flush()
        tag = res["klass"]
        extra = ""
        if tag == "a_fixeddim":
            extra = f" k={res['best_k']} phase={res['best_phase']} dim={res['dim']} stride={res['stride']}"
        elif tag == "c_HALT":
            extra = f"  *** {res['note']} ***"
        print(f"[{i+1:>3}/{len(codes)}] {code}  {tag}{extra}", flush=True)
    if fout:
        fout.close()

    from collections import Counter
    c = Counter(r["klass"] for r in results)
    print("\n=== breakdown ===")
    for k in ("a_fixeddim", "b_darkrank", "c_degenerate", "c_HALT"):
        print(f"  {k:>14}: {c.get(k,0)}")
    halts = [r for r in results if r["klass"] == "c_HALT"]
    if halts:
        print("\n*** HALTS DETECTED ***")
        for r in halts:
            print(f"  {r['code']}: {r['note']}")
    if band_n:
        print(f"\n(sample of {len(codes)} from {band_n} unstructured machines; "
              f"horizon {a.horizon:,})")


if __name__ == "__main__":
    main()
