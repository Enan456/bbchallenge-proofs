"""Decider pilot: sound invariant search over learned macro laws.

Two searchers run over every learned law the program holds:

  A. Congruence invariants. A machine whose OrbitFinder spec is a
     finite set of guarded affine branches on block tuples is
     abstracted onto a finite domain: each coordinate is either an
     exact small value (below the guard cap) or the pair
     (large, residue mod m). Guards of the spec (capped signatures)
     are represented exactly in this domain, so branch applicability
     is decided, not approximated. The searcher computes the forward
     closure of the observed seed states; a hit is a closure in which
     every state is covered by at least one branch guard. States with
     no covering guard are the fatal proxy: there the learned law has
     no continuation and non-halting cannot be argued from it.

  B. Monotone coordinate invariants. For single-arity specs, find a
     coordinate j such that every branch applicable at states with
     x_j >= cap preserves arity and strictly increases x_j (verified
     symbolically over the guard box in exact rational arithmetic),
     every capped signature with x_j >= cap is covered by some
     branch, and every seed has x_j >= cap. Then the orbit can never
     reach a fatal (guard-uncovered) state, because every uncovered
     state requires x_j < cap.

Both searchers are fail-closed: any modulus obstruction, state-space
explosion, contradiction, or budget overrun rejects the machine at
that setting. A returned invariant is verified, never fitted.

Honest scope. Every invariant here is an invariant OF THE LEARNED
LAW. The conditional hypothesis per machine is: from the seed record
onward, all frontier records stay on the seed side and every
consecutive record pair follows some branch of the spec exactly.
An invariant on a learned law is decision-grade only after the law
itself is Lean-certified (episode obligations kernel-checked); until
then the result is a closure certificate over an empirical law.

Small-value floor: raw records come from ``_one_blocks``, which emits
only positive block lengths, so the abstract domain excludes 0. This
is a property of the record encoding, not of the learned law.

Reuse: the sibling package ``qgkit.bb6.decider.invariants`` provides
guard-free searchers. Its ``monotone_search`` (constant-difference
functionals) is sound and is reused for the one-dimensional regime
laws of population 2. Its ``congruence_search`` applies affine maps
to residue representatives, which does not commute with reduction
mod m when coefficients are fractional, so this module carries its
own congruence engine for OrbitFinder specs (fractional coefficients
are routine there) and represents the finder's guards exactly.
"""

from __future__ import annotations

import itertools
import json
import math
import sys
from fractions import Fraction

from qgkit.bb6.dragon.finder import CAP, OrbitFinder
from qgkit.bb6.vcollatz.classify import _parse

SMALL = tuple(range(1, CAP))          # exact small block values: 1, 2
MODULI = (1,) + tuple(range(2, 65))   # m = 1 is the pure interval check
MAX_STATES = 50_000
MAX_BRANCH_PRODUCT = 256
MAX_TOTAL_WORK = 2_000_000            # visited states across all moduli
MAX_ARITY = 24                        # searcher bound: larger tuples are
                                      # declined fail-closed (cost grows
                                      # with arity^2 per state and such
                                      # specs are memorized tables)


class ModulusUnusable(Exception):
    """Branch denominators share a factor with m: residues of images
    are not determined by residues of inputs at this modulus."""


class Breakdown(Exception):
    """A branch image provably cannot be a valid block value: the
    law contradicts the record encoding at this abstract state."""


class Explosion(Exception):
    """Closure exceeded the state or successor budget."""


# ---------------------------------------------------------------------------
# Branch model: OrbitFinder rules as guarded affine branches
# ---------------------------------------------------------------------------

class GuardedBranch:
    """One OrbitFinder rule. Guard: x has arity n_in and for each i,
    sig[i] < CAP means x_i == sig[i] exactly, sig[i] == CAP means
    x_i >= CAP. maps[t] is the affine row (c_1..c_n, const) for output
    coordinate t; cost is the step-count row."""

    __slots__ = ("n_in", "n_out", "sig", "maps", "cost", "support")

    def __init__(self, key, rule):
        self.n_in, self.n_out, self.sig = key[0], key[1], tuple(key[2])
        self.maps = tuple(tuple(Fraction(c) for c in m) for m in rule["maps"])
        self.cost = tuple(Fraction(c) for c in rule["cost"])
        self.support = rule.get("support", 0)

    def image(self, x):
        """Exact concrete image, or None if any coordinate is not a
        positive integer (law contradicts the record encoding)."""
        out = []
        for row in self.maps:
            v = sum(c * xi for c, xi in zip(row[: self.n_in], x)) + row[-1]
            if v.denominator != 1 or v < 1:
                return None
            out.append(int(v))
        return tuple(out)

    def step_cost(self, x):
        return sum(c * xi for c, xi in zip(self.cost[: self.n_in], x)) \
            + self.cost[-1]


def spec_branches(spec) -> list:
    return [GuardedBranch(key, rule) for key, rule in spec["rules"].items()]


def branch_index(branches) -> dict:
    """Guard lookup table: capped signature -> branches. Signature
    matching is exact, so this is the complete applicability relation."""
    idx = {}
    for br in branches:
        idx.setdefault(br.sig, []).append(br)
    return idx


def concrete_sig(x):
    return tuple(min(v, CAP) for v in x)


# ---------------------------------------------------------------------------
# Searcher A: congruence closure on the exact-small / residue domain
# ---------------------------------------------------------------------------

def abstract_state(x, m):
    """Coordinate v < CAP stays exact; v >= CAP becomes ('b', v % m)."""
    return tuple(v if v < CAP else ("b", v % m) for v in x)


def abstract_sig(a):
    return tuple(CAP if isinstance(v, tuple) else v for v in a)


def _coordinate_possibilities(row, a, m):
    """Sound possibility set for one output coordinate of a branch
    applied to abstract state a. Uses exact residues (via the lcm of
    denominators, invertible mod m or the modulus is rejected) and
    one-sided interval bounds from coefficient signs over the guard
    box (pinned coordinates exact, free coordinates >= CAP)."""
    const = row[-1]
    free = []
    for i, ai in enumerate(a):
        if isinstance(ai, tuple):
            if row[i] != 0:
                free.append((row[i], ai[1]))
        else:
            const += row[i] * ai
    lb, ub = const, const
    lb_fin = ub_fin = True
    for c, _ in free:
        if c > 0:
            lb += CAP * c
            ub_fin = False
        else:
            ub += CAP * c
            lb_fin = False
    lcm_d = const.denominator
    for c, _ in free:
        d = c.denominator
        lcm_d = lcm_d * d // math.gcd(lcm_d, d)
    if math.gcd(lcm_d, m) != 1:
        raise ModulusUnusable(f"denominator lcm {lcm_d} shares a factor "
                              f"with m={m}")
    acc = int(const * lcm_d)
    for c, r in free:
        acc += int(c * lcm_d) * r
    res = (pow(lcm_d, -1, m) * acc) % m
    poss = []
    for v in SMALL:
        if v % m == res and (not lb_fin or v >= lb) and \
                (not ub_fin or v <= ub):
            poss.append(v)
    if not ub_fin or ub >= CAP:
        poss.append(("b", res))
    if not poss:
        raise Breakdown("no positive block value consistent with "
                        "residue and bounds")
    return poss


def branch_abstract_successors(br: GuardedBranch, a, m):
    per_coord = [_coordinate_possibilities(row, a, m) for row in br.maps]
    total = 1
    for p in per_coord:
        total *= len(p)
    if total > MAX_BRANCH_PRODUCT:
        raise Explosion(f"successor product {total} at one state")
    return [tuple(c) for c in itertools.product(*per_coord)]


def congruence_closure(idx, seeds, m, max_states=MAX_STATES):
    """Forward closure of the abstract seed set under every applicable
    branch. Success: closure terminates with every state covered by at
    least one guard. Returns (True, S, None) or (False, reason, w)."""
    S = set()
    frontier = []
    for x in seeds:
        a = abstract_state(x, m)
        if a not in S:
            S.add(a)
            frontier.append(a)
    while frontier:
        a = frontier.pop()
        matching = idx.get(abstract_sig(a))
        if not matching:
            return False, "uncovered", a
        for br in matching:
            try:
                succs = branch_abstract_successors(br, a, m)
            except ModulusUnusable as e:
                return False, "modulus", str(e)
            except Breakdown as e:
                return False, "breakdown", (a, str(e))
            except Explosion as e:
                return False, "explosion", str(e)
            for s in succs:
                if s not in S:
                    if len(S) >= max_states:
                        return False, "explosion", f"> {max_states} states"
                    S.add(s)
                    frontier.append(s)
    return True, S, None


def search_congruence(branches, seeds, moduli=MODULI):
    """First hit wins. Returns (hit, failures): hit is None or a dict
    with m, the closure S and its size, and kind 'total' (m == 1: the
    guards cover the whole reachable box, no residue refinement
    needed) or 'congruence'. failures maps each tried m to its
    rejection; a global work budget stops long failure streaks."""
    idx = branch_index(branches)
    failures = {}
    work = 0
    for m in moduli:
        ok, payload, witness = congruence_closure(idx, seeds, m)
        if ok:
            return {"m": m, "size": len(payload),
                    "kind": "total" if m == 1 else "congruence",
                    "S": payload}, failures
        failures[m] = (payload, witness)
        work += MAX_STATES if payload == "explosion" else 1000
        if work > MAX_TOTAL_WORK:
            failures["stopped_early_after"] = (f"m={m}", None)
            break
    return None, failures


# ---------------------------------------------------------------------------
# Searcher B: monotone coordinate with a fatal-exclusion link
# ---------------------------------------------------------------------------

def _growth_ok(br: GuardedBranch, j) -> bool:
    """Verify symbolically that out_j >= x_j + 1 over the branch guard
    box. The minimum of an affine form over the box (pinned exact,
    free >= CAP) is finite only when every free coefficient of the
    difference is nonnegative."""
    row = br.maps[j]
    const = row[-1] - 1
    for i, s in enumerate(br.sig):
        c = row[i] - (1 if i == j else 0)
        if s < CAP:
            const += c * s
        else:
            if c < 0:
                return False
            const += CAP * c
    return const >= 0


def search_monotone(branches, seeds):
    """Returns (hits, skip_reason). A hit names coordinate j with:
    every branch applicable where x_j >= CAP preserves arity and
    strictly increases x_j (symbolic, exact); every capped signature
    with sig[j] == CAP is present among the branch guards (so no
    state with x_j >= CAP is fatal); every seed has x_j >= CAP.
    Fatal states then require x_j < CAP and are never reached."""
    arities = {br.n_in for br in branches} | {br.n_out for br in branches}
    if len(arities) != 1:
        return [], f"mixed arities {sorted(arities)}"
    n = arities.pop()
    if n > 13:
        return [], f"arity {n} too large for signature enumeration"
    if not all(len(x) == n for x in seeds):
        return [], "seed arity differs from spec arity"
    sigs = {br.sig for br in branches}
    hits = []
    for j in range(n):
        applicable = [br for br in branches if br.sig[j] == CAP]
        if not applicable:
            continue
        if not all(_growth_ok(br, j) for br in applicable):
            continue
        others = [SMALL + (CAP,)] * n
        others[j] = (CAP,)
        if not all(p in sigs for p in itertools.product(*others)):
            continue
        if not all(x[j] >= CAP for x in seeds):
            continue
        hits.append({"coordinate": j,
                     "claim": f"x[{j}] >= {CAP} at the seed, grows by "
                              f">= 1 under every applicable branch, and "
                              f"every fatal state requires x[{j}] < {CAP}"})
    return hits, None


# ---------------------------------------------------------------------------
# Concrete spec replay: provable-failure detection
# ---------------------------------------------------------------------------

def spec_replay(branches, start, max_iters=20_000, value_cap=10 ** 60):
    """Iterate the exact law forward from a concrete state. Outcomes:
    ('uncovered', k, x)  the law itself predicts leaving the law: no
                         covering invariant of this family can exist
                         for the machine's future orbit, conditional
                         on the law (the provable-failure witness);
    ('ambiguous', k, x)  two branches match with different images;
    ('breakdown', k, x)  a matching branch maps outside positive ints;
    ('ok', k, x)         budget exhausted with the law total so far."""
    idx = branch_index(branches)
    x = tuple(start)
    for k in range(max_iters):
        matching = idx.get(concrete_sig(x))
        if not matching:
            return "uncovered", k, x
        images = set()
        for br in matching:
            y = br.image(x)
            if y is None:
                return "breakdown", k, x
            images.add(y)
        if len(images) > 1:
            return "ambiguous", k, x
        x = images.pop()
        if sum(x) > value_cap:
            return "ok", k + 1, ("value cap",)
    return "ok", max_iters, x


# ---------------------------------------------------------------------------
# Raw simulation (fast) and the stress harness
# ---------------------------------------------------------------------------

def raw_records_fast(code, steps, max_records=500_000):
    """List-tape port of classify.simulate_records: same record
    stream (step, side, state, blocks) at a fraction of the cost."""
    tab = _parse(code)
    left, right = [], [0]      # position p: right[p] if p >= 0, left[-1-p]
    head, state = 0, 0
    lo = hi = 0
    records = []
    for step in range(steps):
        sym = right[head] if head >= 0 else left[-1 - head]
        tr = tab.get((state, sym))
        if tr is None:
            return True, step, records
        ns, nw, d = tr
        if head >= 0:
            right[head] = nw
        else:
            left[-1 - head] = nw
        state = ns
        head += d
        if head < lo:
            left.append(0)
            lo = head
        elif head > hi:
            right.append(0)
            hi = head
        else:
            continue
        cells = itertools.chain(reversed(left), right)
        blocks = tuple(sum(1 for _ in g)
                       for b, g in itertools.groupby(cells) if b)
        records.append({"step": step + 1,
                        "side": "L" if head == lo else "R",
                        "state": state, "blocks": blocks})
        if len(records) >= max_records:
            break
    return False, steps, records


def tail_records(records):
    """The maximal single-side suffix of the nonempty-block record
    stream: the observed orbit the invariants are seeded from."""
    recs = [r for r in records if r["blocks"]]
    if not recs:
        return []
    side = recs[-1]["side"]
    tail = []
    for r in reversed(recs):
        if r["side"] != side:
            break
        tail.append(r)
    tail.reverse()
    return tail


def _pair_follows_spec(idx, x, y, dstep):
    for br in idx.get(concrete_sig(x), ()):
        if br.image(x) == y and br.step_cost(x) == dstep:
            return True
    return False


def stress_candidate(code, branches, candidate, tail_start_step,
                     steps=10_000_000):
    """Searcher C. Rerun the raw machine much further and check the
    candidate on every observed abstract state at or after the seed
    window, and that every consecutive window pair still follows the
    spec exactly. Any violation kills the candidate. The single-side
    hypothesis is also enforced: a record on the other side, or with
    empty blocks, after the seed window is a violation."""
    halted, _, records = raw_records_fast(code, steps)
    if halted:
        return False, "machine halted in stress budget"
    window = [r for r in records if r["step"] >= tail_start_step]
    if not window:
        return False, "seed window not reached in stress run"
    if any(not r["blocks"] for r in window):
        return False, "empty-block record after seed window"
    if len({r["side"] for r in window}) > 1:
        return False, "side switch after seed window"
    if candidate["searcher"] == "A":
        m, S = candidate["m"], candidate["S"]
        for r in window:
            if abstract_state(r["blocks"], m) not in S:
                return False, f"state outside S at step {r['step']}"
    else:
        j = candidate["coordinate"]
        for r in window:
            if len(r["blocks"]) <= j or r["blocks"][j] < CAP:
                return False, f"coordinate floor broken at step {r['step']}"
        for r1, r2 in zip(window, window[1:]):
            if r2["blocks"][j] < r1["blocks"][j] + 1:
                return False, f"growth broken at step {r2['step']}"
    idx = branch_index(branches)
    for r1, r2 in zip(window, window[1:]):
        if not _pair_follows_spec(idx, tuple(r1["blocks"]),
                                  tuple(r2["blocks"]),
                                  r2["step"] - r1["step"]):
            return False, f"law violated at step {r2['step']}"
    return True, f"{len(window)} states checked to raw step {steps}"


# ---------------------------------------------------------------------------
# Population 1 driver: sweep251 EXACT machines
# ---------------------------------------------------------------------------

def analyze_exact_machine(code, steps=1_500_000, cap=20_000,
                          seed_window=200, stress_steps=10_000_000):
    import time
    t0 = time.time()
    out = {"code": code}
    spec = OrbitFinder(code, steps=steps, cap=cap).fit()
    out["t_fit"] = round(time.time() - t0, 1)
    if spec is None:
        out["status"] = "refit-failed"
        return out
    branches = spec_branches(spec)
    out["n_rules"] = spec["n_rules"]
    out["n_transitions"] = spec["n_transitions"]
    out["max_arity"] = max(max(br.n_in, br.n_out) for br in branches)
    halted, _, records = raw_records_fast(code, steps, max_records=cap)
    tail = tail_records(records)
    if halted or len(tail) < 2:
        out["status"] = "halted-or-no-tail"
        return out
    window = tail[-seed_window:]
    seeds = [tuple(r["blocks"]) for r in window]
    tail_start_step = window[0]["step"]
    out["tail_len"] = len(tail)
    out["seed_arities"] = sorted({len(s) for s in seeds})
    t1 = time.time()
    replay = spec_replay(branches, seeds[-1])
    out["replay"] = {"outcome": replay[0], "iters": replay[1],
                     "witness": None if replay[0] == "ok"
                     else _short(replay[2])}
    if out["max_arity"] > MAX_ARITY:
        out["congruence"] = {"hit": None,
                             "failures": {"reasons": {
                                 "arity-bound-declined": ["all"]},
                                 "uncovered_witness": None}}
        hit_a = None
    else:
        hit_a, failures = search_congruence(branches, seeds)
        out["congruence"] = {
            "hit": None if hit_a is None else
            {"m": hit_a["m"], "kind": hit_a["kind"], "size": hit_a["size"]},
            "failures": _summarize_failures(failures)}
    hits_b, reason_b = search_monotone(branches, seeds)
    out["monotone"] = {"hits": hits_b, "skip_reason": reason_b}
    out["t_search"] = round(time.time() - t1, 1)
    candidates = []
    if hit_a is not None:
        candidates.append({"searcher": "A", "m": hit_a["m"],
                           "kind": hit_a["kind"], "S": hit_a["S"]})
    for h in hits_b:
        candidates.append({"searcher": "B",
                           "coordinate": h["coordinate"]})
    out["stress"] = []
    for cand in candidates:
        ok, detail = stress_candidate(code, branches, cand,
                                      tail_start_step, steps=stress_steps)
        out["stress"].append(
            {"searcher": cand["searcher"],
             "what": (f"m={cand['m']} ({cand['kind']})"
                      if cand["searcher"] == "A"
                      else f"coordinate {cand['coordinate']}"),
             "ok": ok, "detail": detail})
    out["status"] = "done"
    return out


def _short(x, limit=240):
    s = repr(x)
    return s if len(s) <= limit else s[:limit] + "..."


def _summarize_failures(failures):
    """Compress the per-modulus failure map: reason -> moduli, with
    one witness for the uncovered case."""
    by_reason, witness = {}, None
    for m, (reason, w) in failures.items():
        by_reason.setdefault(str(reason), []).append(str(m))
        if reason == "uncovered" and witness is None:
            witness = _short(w)
    return {"reasons": by_reason, "uncovered_witness": witness}


# ---------------------------------------------------------------------------
# Population 2 driver: dossier-4 single-law regime machines
# ---------------------------------------------------------------------------

def regime_refit(code, steps=250_000):
    """Port of the dossier-4 regime segmenter (qgkit/bb6/dossier4.py):
    frontier-expansion event times, segmented into maximal runs of
    constant second difference on stride subsequences. Returns
    (regs, halted_step); regs entries are (start_event, length,
    second_difference, stride, first_gap)."""
    tab = _parse(code)
    left, right = [], [0]
    head, state = 0, 0
    lo = hi = 0
    events = []
    for t in range(steps):
        if head > hi or head < lo:
            events.append(t)
            if head < lo:
                left.append(0)
                lo = head
            else:
                right.append(0)
                hi = head
        sym = right[head] if head >= 0 else left[-1 - head]
        tr = tab.get((state, sym))
        if tr is None:
            return None, t
        ns, nw, d = tr
        if head >= 0:
            right[head] = nw
        else:
            left[-1 - head] = nw
        state = ns
        head += d
    best = ([], 1, 0.0)
    for stride in (1, 2, 3, 4):
        cov, regs = 0, []
        for ph in range(stride):
            sub = events[ph::stride]
            dts = [sub[i + 1] - sub[i] for i in range(len(sub) - 1)]
            sd = [dts[i + 1] - dts[i] for i in range(len(dts) - 1)]
            i = 0
            while i < len(sd):
                j = i
                while j < len(sd) and sd[j] == sd[i]:
                    j += 1
                if j - i >= 3:
                    regs.append((ph + i * stride, (j - i) * stride,
                                 sd[i], stride, dts[i]))
                    cov += (j - i) * stride
                i = max(j, i + 1)
        frac = cov / max(len(events), 1)
        if frac > best[2]:
            best = (regs, stride, frac)
    regs, stride, frac = best
    regs.sort()
    return regs, None


def analyze_regime_machine(code, steps=250_000):
    """The regime law is one-dimensional (gap -> gap + sd), with
    integer coefficients and no guards, so the sibling searchers of
    qgkit.bb6.decider.invariants apply soundly and are reused. No
    fatal model exists for this abstraction (the law says nothing
    about halt corridors), so the congruence searcher is not decisive
    here by construction; the monotone searcher can verify growth of
    the event gap but that growth excludes no fatal set."""
    from qgkit.bb6.decider.invariants import (AffineSystem, Branch,
                                              congruence_search,
                                              monotone_search)
    out = {"code": code}
    regs, halted = regime_refit(code, steps)
    if halted is not None:
        out["status"] = "halted"
        return out
    if not regs:
        out["status"] = "no-regimes"
        return out
    sds = sorted({r[2] for r in regs})
    out["nreg"] = len(regs)
    out["laws"] = len(sds)
    out["stride"] = regs[0][3]
    if len(sds) != 1:
        out["status"] = "not-single-law"
        return out
    c = sds[0]
    out["sd"] = c
    system = AffineSystem(branches=[Branch(matrix=((1,),), offset=(c,),
                                           name=f"gap+{c}")],
                          dim=1, seed=(regs[-1][4],))
    mono = monotone_search(system)
    cong = congruence_search(system)     # no fatal model: never decisive
    out["gap_growth_verified"] = any(cf == (1,) for cf, _ in mono)
    out["monotone_functionals"] = len(mono)
    out["congruence_hits"] = len(cong)
    out["decision_grade_hits"] = 0
    out["status"] = "done"
    return out


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _load_pop1(path):
    codes = []
    with open(path) as fh:
        for line in fh:
            row = json.loads(line)
            if row.get("verdict") == "EXACT":
                codes.append(row["code"])
    return codes


def _load_pop2(path):
    rows = []
    with open(path) as fh:
        for line in fh:
            row = json.loads(line)
            if row.get("laws") == 1 and row.get("nreg", 0) >= 3 \
                    and row.get("halted") is None:
                rows.append(row)
    return rows


def main(argv):
    which = argv[0]
    args = dict(a.split("=", 1) for a in argv[1:])
    shard = int(args.get("shard", 0))
    nshards = int(args.get("nshards", 1))
    out_path = args["out"]
    root = args.get("root", ".")
    results = []
    if args.get("resume") == "1":
        try:
            with open(out_path) as fh:
                results = [json.loads(l) for l in fh]
        except FileNotFoundError:
            pass
    have = {r["code"] for r in results}
    if which == "pop1":
        codes = _load_pop1(
            f"{root}/experiments/outputs/sweep251_results.jsonl")
        for i, code in enumerate(codes):
            if i % nshards != shard or code in have:
                continue
            try:
                results.append(analyze_exact_machine(code))
            except Exception as e:                  # fail-closed, keep going
                results.append({"code": code, "status": "error",
                                "detail": _short(e)})
            _flush(out_path, results)
    elif which == "pop2":
        rows = _load_pop2(f"{root}/experiments/outputs/d4_fullsweep.jsonl")
        for i, row in enumerate(rows):
            if i % nshards != shard or row["code"] in have:
                continue
            try:
                results.append(analyze_regime_machine(row["code"]))
            except Exception as e:
                results.append({"code": row["code"], "status": "error",
                                "detail": _short(e)})
            if len(results) % 20 == 0:
                _flush(out_path, results)
        _flush(out_path, results)
    else:
        raise SystemExit(f"unknown mode {which}")


def _flush(path, results):
    with open(path, "w") as fh:
        for r in results:
            fh.write(json.dumps(r) + "\n")


if __name__ == "__main__":
    main(sys.argv[1:])
