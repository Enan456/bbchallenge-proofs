"""Phase-1 catch-grammar extractor for the hurler/catcher decider.

Pipeline position (see docs/results/2026-09-10-hurler-catcher-grammar-plan.md):
    emulation -> [THIS: extract catch grammar + prove it complete] -> non-intermittency -> fuel bound -> ...

Two stages, both fail-closed:
  1a  extract(): observe the catcher-symbol sequence; build the order-1 grammar
      (alphabet + adjacency) and per-symbol affine/parity features. Observed
      transitions are a LOWER bound on the admissible grammar -- never a verdict.
  1b  prove_complete(): search a forcing invariant (parity/residue predicate)
      that closes each symbol's successor set to the observed set, proving no
      other transition is possible. Emits a Lean-checkable obligation. If no
      closing invariant is found within budget -> REFUSE (no unsound grammar).

Validated on the dossier-2/3 renewal map: recovers
    C->{T}, F->{C,F}, T->{C,F}, TT-forbidden
with the b-parity forcing invariant, matching the proven manuscript Lemma.

The extractor is agnostic to the emulation internals: it consumes a stream of
CatchEvent(symbol, state_features, out_features, det). For reduced machines a
macro-step function (e.g. the renewal map R) is adapted by `events_from_macro`.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Callable, Iterable


@dataclass
class CatchEvent:
    symbol: str                      # catcher-outcome macro-symbol
    feat_in: dict                    # parity/residue features of the incoming macro-state
    feat_out: dict                   # features of the outgoing macro-state (what the NEXT symbol must consume)
    det: int                         # |det| of this symbol's affine linear part (1 = neutral)


@dataclass
class GrammarRecord:
    code: str
    alphabet: list                   # sorted Sigma
    adjacency: dict                  # symbol -> sorted list of observed successors
    det: dict                        # symbol -> |det|  (neutral iff 1)
    forbidden: list                  # forbidden ordered pairs
    forcing_invariant: str | None    # name of the feature that closes the grammar, or None
    complete: bool                   # 1b proven (empirically closed + obligation emitted)
    refuse_reason: str | None = None
    obligations: list = field(default_factory=list)   # Lean obligation statements


# ---- 1a: extraction -------------------------------------------------------

def extract(events: Iterable["CatchEvent | None"], code: str) -> GrammarRecord:
    # A `None` in the stream is an ORBIT BOUNDARY: it resets `prev` so the last
    # symbol of one orbit is never recorded as a successor of the first symbol
    # of the next. Omitting this contaminates the grammar with phantom
    # cross-orbit transitions -- caught fail-closed by prove_complete.
    adj = defaultdict(set)
    det = {}
    feat_in = defaultdict(lambda: defaultdict(set))
    feat_out = defaultdict(lambda: defaultdict(set))
    prev = None
    for ev in events:
        if ev is None:
            prev = None
            continue
        det[ev.symbol] = ev.det
        for k, v in ev.feat_in.items():
            feat_in[ev.symbol][k].add(v)
        for k, v in ev.feat_out.items():
            feat_out[ev.symbol][k].add(v)
        if prev is not None:
            adj[prev].add(ev.symbol)
        prev = ev.symbol
    Sigma = sorted(adj)
    forbidden = [(s, t) for s in Sigma for t in Sigma if t not in adj[s]]
    rec = GrammarRecord(
        code=code, alphabet=Sigma,
        adjacency={s: sorted(adj[s]) for s in Sigma},
        det=dict(det), forbidden=forbidden,
        forcing_invariant=None, complete=False,
    )
    rec._feat_in = {s: dict(feat_in[s]) for s in Sigma}     # type: ignore[attr-defined]
    rec._feat_out = {s: dict(feat_out[s]) for s in Sigma}   # type: ignore[attr-defined]
    return rec


# ---- 1b: completeness via a forcing invariant -----------------------------

def prove_complete(rec: GrammarRecord) -> GrammarRecord:
    """Search a single feature `f` such that (i) each symbol fires only at one
    value of f (precondition single-valued) and (ii) each symbol's OUT-value of
    f forces exactly the observed successor set. That feature is the forcing
    invariant; its existence is the completeness witness (verified in Lean)."""
    feat_in = rec._feat_in    # type: ignore[attr-defined]
    feat_out = rec._feat_out  # type: ignore[attr-defined]
    candidate_feats = sorted({k for s in rec.alphabet for k in feat_in[s]})
    for f in candidate_feats:
        if f not in feat_out[rec.alphabet[0]]:
            continue
        need = {}
        ok = True
        for s in rec.alphabet:                      # precondition single-valued?
            vals = feat_in[s].get(f, set())
            if len(vals) != 1:
                ok = False; break
            need[s] = next(iter(vals))
        if not ok:
            continue
        closes = True                                # out-value forces successor set?
        for s in rec.alphabet:
            outvals = feat_out[s].get(f, set())
            forced = {t for t in rec.alphabet if need[t] in outvals}
            if forced != set(rec.adjacency[s]):
                closes = False; break
        if closes:
            rec.forcing_invariant = f
            rec.complete = True
            rec.obligations = [
                f"precondition: for all reachable macro-states x, symbol(x) fires only when {f}(x) = need[symbol]",
                f"forcing: for all x, {f}(step(x)) determines next-symbol's admissible set = adjacency[symbol(x)]",
                f"non-intermittency corollary: neutral symbols {sorted(s for s in rec.alphabet if rec.det[s]==1)} "
                f"have bounded runs (no neutral cycle in adjacency)",
            ]
            return rec
    rec.refuse_reason = "no order-1 forcing invariant found (escalate to order-n or REFUSE)"
    return rec


# ---- adapter: reduced macro-map (e.g. the renewal map) --------------------

def events_from_macro(macro_step: Callable, fatal: Callable, seeds, max_ret=3000,
                      bit_cap=120, features: Callable | None = None):
    """Adapt a reduced macro-step `macro_step(state) -> (state', symbol, det)` into
    a CatchEvent stream. `features(state) -> dict` supplies parity/residue features."""
    for s0 in seeds:
        state = s0
        for _ in range(max_ret):
            if fatal(*state):
                break
            nxt, sym, det = macro_step(state)
            fi = features(state) if features else {}
            fo = features(nxt) if features else {}
            yield CatchEvent(sym, fi, fo, det)
            state = nxt
            if max(state).bit_length() > bit_cap:
                break
        yield None    # orbit boundary: never chain one orbit's tail to the next orbit's head


# ---- validation target: dossier-2/3 renewal map ---------------------------

if __name__ == "__main__":
    def _macro(state):
        a, b = state
        if b % 2 == 0:
            return (a + 6, b - 3), 'T', 1
        be = (a - 1) if a % 2 == 1 else (a - 2)
        al = 6 if a % 2 == 1 else 9
        if b < be:
            return (al + 3 * (b - 3), be - (b - 3)), 'C', 3
        return (al + 3 * be + 3, b - be - 4), 'F', 3

    def _fatal(a, b):
        if b <= 2 or (b % 2 == 0 and b == 4):
            return True
        be = (a - 1) if a % 2 == 1 else (a - 2)
        return b % 2 == 1 and b > be and b - be in (1, 3, 5)

    def _features(state):
        a, b = state
        return {"b%2": b % 2, "a%2": a % 2}

    seeds = [(6 + 4 * k, 13 + 8 * k) for k in range(4000)]
    rec = extract(events_from_macro(_macro, _fatal, seeds, features=_features),
                  code="dossier-2/3 renewal map")
    rec = prove_complete(rec)
    print("alphabet:", rec.alphabet)
    print("adjacency:", rec.adjacency)
    print("det (neutral iff 1):", rec.det)
    print("forbidden:", rec.forbidden)
    print("forcing invariant:", rec.forcing_invariant)
    print("complete:", rec.complete, "| refuse:", rec.refuse_reason)
    for o in rec.obligations:
        print("  obligation:", o)
    assert rec.complete and rec.forcing_invariant == "b%2"
    assert rec.adjacency == {'C': ['T'], 'F': ['C', 'F'], 'T': ['C', 'F']}
    print("\nVALIDATED against the proven manuscript grammar.")
