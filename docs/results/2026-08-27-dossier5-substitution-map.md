# Dossier-5 step 2 (opened): the substitution map and the death tree

**Date:** 2026-08-27 · **Machine:**
`1RB1RD_1LC0LC_0RD0LB_1RF0LE_0RD---_0RA1RC` · builds on
`2026-08-27-dossier5-trisection-calculus.md`

## The abstract map: a rigid cycle grammar

Lifting the validated calculus to block level, one sweep parses into
**cycles** with a rigid internal order. Classifying every interior
unit as `c` (B-copy), `a` (B-absorb), `x` (3-crossing `B0`),
`i` (D-insert), `r` (D-regroup/cascade), `d` (C1-dance):

```
sweep  =  r* a? ( c* x i r* a )* c* [boundary]
```

**767 / 785 sweeps over 8M raw steps parse exactly**; the 18
exceptions are the gap-relic sweeps whose block classification needs
the relic dictionary (they are the same boundary-window events
quantified in the step-1 document). The parse shows the sweep's
conserved combinatorics, confirmed independently by counting: per
sweep, #crossings = #inserts = #absorbs (±1) — every 3-crossing fires
exactly one insert, and every D-run ends in exactly one absorb.
The mode-switch laws, read off the learned decision table:

- B-phase: copy 1-blocks; a (1,3) pair is absorbed (`(1,3) → 1`);
  meeting a bare 3-block flips to D (the crossing `x`, which always
  emits one 1-block and triggers the one insert `1 → (1,3)`).
- D-phase: persists exactly while the lookahead is `1,1` material
  (regroup family `1,1,(3,1)^k,1 → (1,3)^{k+1}`); flips back to B by
  absorbing when a 3-block is adjacent, or at the input end.

Semantics: the 3s are carries organized into traveling `(3,1)*` wave
trains (visible as `1010…` in the digit picture); a sweep destroys
one 3 and creates one 3 per cycle plus one net 3 per regroup event;
the wave trains drift and multiply through the regroup family. A
plain positional binary reading of the word is **not** invariant
(tested: value differences are unstructured), so the odometer runs in
a numeral system tied to the cycle structure, not to position — its
exact invariant is the next question of step 2.

## The death tree, raw level

The machine halts only at `E` reading 1, and `E` is entered only via
`D1 → 0LE`: death = a D1-event whose left neighbor holds 1. In the
calculus every `D1` maximum is followed by an `E0` minimum — the left
neighbor is always 0 on the certified orbit; that is the safety
invariant the eventual `SafeWordOrbit` must carry.

Backward constraint-pattern BFS from `E reads 1` (the D3 method)
gives family counts by depth:

```
1 1 1 1 1 3 4 5 10 11 13 23 26 34 56 65 92 140 167 247 355 441
651 900 1153 1686 2281 3006 4332 5807 7804
```

- Growth ratio ≈ 1.36 per step (tail ratios 1.32–1.44) —
  **a different constant from dossier-3's φ ≈ 1.618**, consistent
  with the per-machine-Pisot prediction; no exact integer linear
  recurrence of order ≤ 6 fits depths 8–30 at the raw level. For
  dossier-3 too, the clean recurrence (Fibonacci) lived at the
  *abstract* level only; the abstract death tree here (preimage
  families of the fatal pattern under the sweep map) is the object
  the prediction is about, and the cycle grammar above is exactly
  the inverse-parse grammar needed to build it (transfer-matrix
  branching = parse ambiguity per symbol).
- The fatal patterns at depth 5–12 all require compound motifs —
  a double-0 gap followed by adjacent 1s (`…0011…`, `…0010011…`)
  in the region the pass is about to enter. Single-cell mutations of
  a real 648-cell orbit word were tested exhaustively: **0 of 646
  mutations halt** (300k-step horizon each) — the fatal set is not
  reachable by one-bit noise, mirroring the narrow-danger-band
  structure of dossiers 2/3.

## The exact inverse-branching law (2026-08-29)

The cycle grammar inverts in closed form. A cycle emits
`1^{m} (1,3)^{1+R} 1` where the `(1,3)`-train of length $t$ can be
produced by the single insert plus **any ordered composition** of
$R = t-1$ into regroup events ($r_k$ emits $(1,3)^{k+1}$; verified:
$r_1$'s emission equals $r_0 r_0$'s exactly, from different inputs).
The 1-run split (absorb · copies · crossing) is unique. Hence the
number of one-sweep preimages of an interior word is exactly

$$\prod_{\text{trains}} 2^{\max(0,\, t_i - 2)}$$

— the abstract death tree branches **2-adically in wave-train
lengths**. This sharpens the Pisot prediction for this machine: where
dossier-3's tree branches at $\varphi$ (from the no-TT constraint),
the rank-1 tree's generation growth is a power of 2 whose exponent is
the total train-length excess of the cone's words; the algebraic
constant, if one emerges, comes from the backward dynamics of train
profiles, now an explicit combinatorial question.

## Status

Step 2 opened: forward abstract map = cycle grammar (verified
767/785), death tree raw counts + fatal motifs mapped, robustness
measured. Next: the cycle-level invariant (what the odometer counts),
the abstract preimage tree via the inverse parse with its
transfer-matrix constant, and the relic dictionary that closes the
18 boundary sweeps.
