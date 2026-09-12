# Phase 1 spec: the catch-grammar extractor

**Date:** 2026-09-12. Implements Phase 1 of the hurler/catcher grammar plan
(`docs/results/2026-09-10-hurler-catcher-grammar-plan.md`). Module:
`qgkit/bb6/decider/grammar_extract.py` (runnable; validated on dossier-2/3).
Goal: turn a machine's observed catcher behaviour into a **proven-complete
symbolic grammar** that downstream stages (non-intermittency, fuel bound) can
stand on. Fail-closed throughout: the extractor emits a grammar only with a
completeness witness, else it `REFUSE`s.

## Interfaces

```
CatchEvent(symbol, feat_in, feat_out, det)    # one catcher outcome
  symbol   : str   macro-symbol from the catch-alphabet
  feat_in  : dict  parity/residue features of the incoming macro-state
  feat_out : dict  features of the outgoing state (what the NEXT symbol must consume)
  det      : int   |det| of this symbol's affine linear part (1 = neutral)

extract(events, code) -> GrammarRecord         # 1a: alphabet + adjacency + features
prove_complete(rec)   -> GrammarRecord         # 1b: forcing-invariant search / REFUSE
events_from_macro(macro_step, fatal, seeds, features)   # adapter for reduced maps
```

`GrammarRecord` carries: `alphabet`, `adjacency` (symbol -> successors), `det`
(neutral iff 1), `forbidden` pairs, `forcing_invariant`, `complete`,
`refuse_reason`, and the Lean `obligations`.

The extractor is **agnostic to the emulation internals** — it consumes a
`CatchEvent` stream. The hurler/catcher emulation (the user's Lean layer)
supplies that stream; reduced machines are adapted from a macro-step function.

## 1a — extraction (observed lower bound)

Walk the event stream; build the order-1 grammar (alphabet + adjacency matrix)
and, per symbol, the sets of observed incoming/outgoing feature values and the
`|det|`. Observed transitions are a **lower bound** on the admissible grammar
and are *never* used for a verdict on their own.

**Orbit-boundary discipline (learned the hard way).** The event stream must emit
a `None` sentinel between orbits so `extract` resets its `prev` pointer. Without
it the tail of one orbit chains to the head of the next, injecting phantom
transitions. In first testing this produced a spurious `C->F`; `prove_complete`
then correctly **refused** (the contaminated grammar is not closed by
b-parity). The fail-closed check caught the bug before it could become an
unsound grammar — which is exactly its job, and a good omen for the discipline.

## 1b — completeness via a forcing invariant (the soundness crux)

Observed != admissible. The decider needs an **upper** bound: that no other
transition is possible. The method searches for a single feature `f` (a
parity/residue predicate) that is *forcing*:

1. **precondition single-valued:** each symbol fires at exactly one value of
   `f` on its incoming state (e.g. `T` only when `b` is even);
2. **successor-closing:** each symbol's *outgoing* `f`-value determines exactly
   the observed successor set (e.g. `T` outputs `b` odd, and the symbols
   admitting odd `b` are exactly `{C,F}`).

If such an `f` exists, the grammar is complete: no unobserved transition can
occur, because it would violate the forced `f`-value. The extractor emits the
two statements plus the non-intermittency corollary as Lean obligations; the
kernel verifies them against the raw transition table. If no order-1 `f` closes
the grammar, escalate to order-`n` context (features of the last `n` symbols);
if that also fails within budget, `REFUSE` — never emit an unsound grammar.

## Validation (known-answer test)

On the dossier-2/3 renewal map the module recovers, exactly:

```
alphabet    : C, F, T
adjacency   : C -> {T},  F -> {C,F},  T -> {C,F}      (TT forbidden)
det         : C,F expanding (3);  T neutral (1)
forcing inv : b%2     complete: True
```

matching the proven manuscript Lemma (the parity grammar) and its corollary
that the parabolic symbol `T` is never iterated. The neutral-symbol set `{T}`
with no neutral cycle in the adjacency is precisely the Phase-2
non-intermittency input.

## Lean obligation shape (fed to Phase 2-4)

```
theorem grammar_complete (x : MacroState) :
    nextSymbol (catchStep x) ∈ adjacency (symbolClass x)
```
proved from: `symbolClass x` fixes `f(x)` (precondition), `f(catchStep x)` is
determined, and the finite table of which symbols admit each `f`-value. Kept at
axioms `{propext, Quot.sound}`, no `sorry`, matching the `*RawTM.lean` style.

## Module layout and tests
- `qgkit/bb6/decider/grammar_extract.py` — this module (extract / prove_complete /
  adapter / dossier-2/3 self-test in `__main__`).
- `tests/bb6/test_grammar_extract.py` (to add) — the dossier-2/3 known-answer
  assertion, plus a fail-closed test that a contaminated stream (no boundary
  sentinel) is refused, not passed.
- Next: wire the real hurler/catcher emulation's event stream into
  `CatchEvent`, and run the extractor across the ~122 cohort, reporting
  `complete` / `REFUSE(reason)` per machine with no silent drops.
