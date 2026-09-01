# Candidate machine parametrics: tail families close the held-out gap

**Date:** 2026-08-31 · **Machine:** `1RB0LF_1RC---_1LD0RF_1RA0LE_0LD1LD_0RD0RB`
(right-growing, no mirror) · **Code:** `qgkit/bb6/d5_candidate_parametrics.py`
(builds on the generic ladder in `qgkit/bb6/d5_generic.py`, MINI_DEPTH=8)

## Summary

The generic literal ladder left this machine at 82.42% held-out exact
(74,443/90,318) with 616 literal tail rules and 308 learning
conflicts. Dumping the learned tables shows that the literal tail set
collapses into two parametric families plus one bounded literal, and
that every one of the 308 conflicts is the same single key aliasing
on the next-arrival kind alone. Replacing the literal tails with the
families and deriving the kind from a word law takes held-out
validation to 100.00% (90,318/90,318) with zero conflicts, and the
result holds unchanged when validation is extended to the 8M-step
horizon (271,344/271,344). This replicates the move that closed the
rank-1 machine in `d5_calculus2.py`.

| calculus | tails | conflicts | held-out exact (2M-4M) | held-out exact (2M-8M) |
|---|---|---|---|---|
| literal (baseline) | 616 | 308 | 74,443/90,318 (82.42%) | not run |
| parametric | 1 | 0 | 90,318/90,318 (100.00%) | 271,344/271,344 (100.00%) |

Both rows use the identical protocol: learn on segments starting
before step 2,000,000, validate every later tiled segment exactly
(output word, step count, head offset, next arrival state and kind),
fail closed on anything unmatched.

## Anatomy of the dynamics

Segment tiling at MINI_DEPTH=8 gives 180,159 segments in 4M steps
(99.75% tiled), average length about 22 steps. Every tiled segment is
head plus a single tail rule with no interior events (the ctx table
holds one rule, used only by the rare full C0 segment). Every arrival
is (C, 0). The dominant motion is a `..####` cursor marching left
through the word: each mini segment consumes the cursor at the floor,
rewrites a short window just right of it, and carries the entire
remaining suffix unchanged. The generic extractor keys the tail on
that whole suffix, which is why the literal tail set was unbounded:
the suffix `(##.)^k#` reaches k in the hundreds and every k is a new
literal key. The dip depths 9, 15, 21 (families 3+6k and 5+6k from
the ladder document, shifted by the 6-cell head) show up directly as
the leading run lengths of the tail patterns below.

## The parametric families

Words over {`#`, `.`}. In each family the consumed pattern starts
with an odd run of marks, `#`^(2m+1), followed by `.`, and then
either nothing or `#.` and an arbitrary carried suffix S. The suffix
is copied verbatim; only the window left of it changes.

D1 tail (after the mini head `D1`: `..####` -> `####`, 5 steps):

```
#^(2m+1) .        ->  ##. (#.)^m #
#^(2m+1) . #. S   ->  ##. (#.)^m ##. S
```

cost 5 steps, offset rel 2, next arrival (C, 0). Observed m: 1, 4, 7
(leading runs 3, 9, 15). The m=1 second form is the workhorse
(179,702 of 179,709 instances); in run-length terms it is
[3,1,2,...] -> [2,1,2,2,...], the insertion of one `##.` block.

A1 tail (after the full head `A1`: `.#` -> `.`, 1 step):

```
#^(2m+1) .        ->  (#.)^(m+1) #
#^(2m+1) . #. S   ->  (#.)^(m+1) ##. S
```

cost 3 steps, offset rel 1, next arrival (C, 0). Observed m: 0, 5, 8
(leading runs 1, 11, 17).

C0 tail (after the full head `C0`: `..#.#` -> `####`, 6 steps, and
the growth unit `''` -> `###`, 11 steps): `''` -> `#####.`, cost 15,
rel 5, next arrival (C, 0). This is a single bounded rule and stays
literal.

Both families share one shape and differ only in the emitted units
and the cost constant; the implementation is one matcher with two
parameter sets.

Verification: on the full 4M-step run the families reproduce every
observed tail instance exactly (179,709 D1, 5 A1, 1 C0; emit, cost,
offset, and next arrival all checked; zero exceptions).

## The word laws that resolve the conflicts

All 308 baseline conflicts sit on the single tail key
`('HEAD:D1', '###.#.##.#')`: emit, cost, offset, and arrival agree on
every occurrence, and only the recorded next-arrival kind flips
between full and mini. The kind is not a function of the tail window;
it depends on whether a cursor survives anywhere in the output word.
This is distance-to-end aliasing in the same sense as the rank-1
machine's saturated decision windows, and it is resolved the same
way: by a law evaluated on the whole output rather than a wider
literal key.

Floor law: the mini floor is the rightmost j < poff with
`cells[j:j+6] == '..####'` and poff - j >= 8.

Kind law: the next arrival is mini exactly when the floor law finds a
site in the output word below the output head offset, and full
otherwise.

Both laws hold on every one of the 179,715 tiled segments of the
4M-step run, with zero exceptions, and the learner rechecks them on
every training segment (a violation would count as a conflict; none
occurred through 8M steps). The 125 baseline mismatch failures were
exactly the conflicted key predicting the wrong kind; the 15,750
baseline no-rule failures were unseen suffix lengths in the D1
family.

## Honest scope

1. The claim is empirical and horizon-limited: exact reproduction of
   all 271,344 held-out tiled segments between steps 2M and 8M. It is
   a learned calculus validated fail-closed, not a proof.
2. Tiling covers 99.75% of segments at 4M (99.83% at 8M). The
   untiled remainder (444 segments in 4M steps) is the once-per-cycle
   rebuild sweep: its duration grows linearly across the run (about
   75 steps early, about 2,600 near 4M) and its density decays
   correspondingly. The segment extractor does not tile these long
   sweeps, so the calculus says nothing about them. Closing them
   needs a segmenter change, not a new tail family.
3. The validation protocol, identical to the baseline, supplies the
   mini floor to `step` from the extraction. The floor law above
   removes the need for this in principle and was verified on every
   tiled segment, but the reported percentages use the same protocol
   as the baseline for comparability.
4. The observed parameter values are sparse (m in {1, 4, 7} and
   {0, 5, 8}). The families are stated for all m; members outside the
   observed values are extrapolation and would be caught fail-closed
   if wrong, since the learner checks every instance.

## Files

- `qgkit/bb6/d5_candidate_parametrics.py`: families, laws, learner,
  ladder driver.
- Baseline: `qgkit/bb6/d5_generic.py` (unchanged).
- Prior context: `docs/results/2026-08-27-d5-certification-ladder.md`,
  `docs/results/2026-08-30-arrayclass-verification.md`.
