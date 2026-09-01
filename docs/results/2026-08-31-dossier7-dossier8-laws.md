# Dossier-7 and dossier-8 opened: two ladder machines, two complete conditional laws

**Date:** 2026-08-31 · **Machines:**
dossier-7 `1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA` (finder: 70
rules, top support 334) and dossier-8
`1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE` (finder: 75 rules, top
support 268), the two remaining PASS machines of the 2026-08-31 deep
finder sweep. Extraction and fail-closed validation:
`qgkit/bb6/d78_laws.py`.

## Growth direction and the record family

Both machines grow left. Over 2M steps, dossier-7 posts 1,169
fresh-left-extreme records against 11 fresh-right startup events;
dossier-8 posts 1,330 against 13. Records are taken at every fresh
left extreme; the tape support at a record is encoded as the tuple of
1-block lengths, and every interior 0-run is a singleton at every
record of both machines through 20M steps (0 violations in 5,252 and
3,880 records).

The standard family, head at the left end:

```
dossier-7:  1^a 0 1 0 1^b 0 (1 0)^k 1^4 0 1^2      state A, k odd
            1^a 0 1 0 1^b 0 1^2                     terminal form
dossier-8:  1^a 0 1 0 1^b 0 (1 0)^k (1^4 0)^g 1^2   state E, k even
```

At 2M steps the family covers 1,115 of 1,158 dossier-7 records and
1,290 of 1,320 dossier-8 records (the rest are renewal-funnel
checkpoints, states D and A respectively, all matched by the law
below); at 20M the ratios are 5,174 of 5,252 and 3,847 of 3,880.

## The gate verdicts fall; the macro dimension survives

The sweep doc's fixed-shape gates (bounded hole count and RLE
dimension at 1M steps) are horizon artifacts for both machines: the
ladder `(1 0)^k` reaches k = 1,137 on dossier-7 at 6.2M steps, an RLE
dimension over 2,280, and k jumps without bound at every grand
renewal. These are not five-integer fixed-dimension machines in the
dossier-1..4 sense. They still compress exactly: the ladder is a
unary-coded counter, so the macro state is the fixed integer vector
(a, b, k) for dossier-7 and (a, b, k, g) for dossier-8, and the
record-to-record law closes over that vector.

## The dossier-7 law (13 rules, fail-closed at 20M)

All 5,251 consecutive record transitions (t > 200) are reproduced
exactly; zero exceptions, zero ambiguous rule matches. Support per
rule at the 20M horizon in parentheses. R denotes the untouched rest
of the tuple.

- **Drift** (5,144): A `(a,1,b)+R -> (a-2,1,b+3)+R` for a >= 3.
- **Merge** (15), a = 2: A `(2,1,b)+R -> (1,b+3)+R`.
- **Odd bottom**, a = 1: A `(1,1,B)+R -> ` D `(4,B)+R` (14); D
  `(4,B)+R -> ` A `(5,B)+R` (14); then
  - k >= 3 (11): A `(5,B,1^k,4,2) -> (B+1,1,7,1^(k-2),4,2)`;
  - k = 1 (2): `-> (B+1,1,10,2)`, entering the terminal form;
  - terminal, B even (1): `(5,B,2) -> ` D `(1,1,1,4,1^m,4,2)` with
    m = (B-6)/2, then D `-> (1,4,4,1^m,4,2)` (1), then
    `-> ` A `(6,1,7,1^(m-2),4,2)` (1): the odd-side grand renewal.
- **Even bottom**, post-merge: A `(1,B)+R -> ` D `(3,B)+R` (16); D
  `(3,B)+R -> ` A `(4,B)+R` (16); then
  - k >= 3 (14): A `(4,B,1^k,4,2) -> (B,1,7,1^(k-2),4,2)`;
  - terminal, B odd (2): `(4,B,2) -> (2,1^((B+1)/2),4,2)`, the
    even-side grand renewal, which re-enters the standard family
    through merge and the k >= 3 branch with B = 4.

Every minor cycle multiplies a by about 3/2 (a -> (3a+13)/2 for odd
a, (3a+14)/2 for even a) and drops k by 2; a grand renewal converts
the accumulated b into a fresh ladder of roughly 3a/4 rungs. Three
grand renewals in 20M steps: the startup event (B = 13, t = 210), B =
49 at t = 2,290, and B = 2,284 at t = 6,210,622, which loaded
k = 1,137. At 13.9M steps the ladder stands at k = 1,113 with minor
cycles growing by 3/2 each; the fourth grand renewal is beyond any
direct horizon.

## The dossier-8 law (12 rules, fail-closed at 20M)

All 3,879 consecutive record transitions (t > 200) are reproduced
exactly; zero exceptions, zero ambiguous rule matches.

- **Drift** (3,821): E `(a,1,b)+R -> (a-2,1,b+3)+R` for a >= 3.
- **Merge** (10), a = 2: E `(2,1,b)+R -> (1,b+3)+R`.
- **Odd bottom**, a = 1: E `(1,1,B)+R -> ` A `(4,B)+R` (12); then
  - k >= 2 (10): A `(4,B,1^k,4^g,2) -> ` E `(B,1,7,1^(k-2),4^g,2)`;
  - k = 1, g = 1 (1, startup): `-> ` E `(B,1,10,2)`.
- **Even bottom**, post-merge: E `(1,B)+R -> ` A `(3,B)+R` (10); then
  - k >= 2 (8): A `(3,B,1^k,4^g,2) -> ` E `(B-1,1,7,1^(k-2),4^g,2)`;
  - k = 0, g >= 1, B even (1): `-> ` A `(1,4,1^((B-4)/2),4^(g+1),2)`,
    the grand renewal: the epoch counter g increments, the tail gains
    a 1^4 block;
  - k = 0, g = 0, B odd (1, startup): `-> ` E `(1^((B+3)/2),4,2)`.
- **Grand funnel** (2 each): A `(1,4,1^m,4^g,2) -> (7,1^m,4^g,2)`,
  then A `-> ` E `(5,1,4,1^(m-2),4^g,2)`.
- **Startup singleton** (1): A `(4,1^k,4,2) -> ` E
  `(2,1,4,1^(k-2),4,2)`, the B = 1 degenerate of the odd-bottom
  branch, seen once at t = 797.

Same anatomy as dossier-7 with opposite k parity (k even) and one
extra integer: g counts grand epochs in the tail. Two grand renewals
in 20M steps, both epoch transitions: g 0 -> 1 at t = 623 (B = 25)
and g 1 -> 2 at t = 17,603 (B = 124, loading a 60-rung ladder through
the funnel, k = 58 at the first standard record).
At 9.19M steps the ladder stands at k = 32 with minor-cycle times
growing by about 2.2 each; the g = 2 -> 3 renewal projects to roughly
3 x 10^12 raw steps.

## Halt anatomy

Both machines halt only in state F reading 0, and both enter F only
from C reading 0 (`C0 -> 1LF`), so the halt funnel is the `C0 -> F0`
corridor: C must read a 0 whose left neighbor is also 0. C is entered
from B0 and D1 on dossier-7, from B0 and A1 on dossier-8; F reading 1
escapes (0LA and 0LE respectively). At every record snapshot through
20M steps all interior holes are isolated singletons, so a 00 window
exists only at the left frontier, where the entry state is always A
(dossier-7) or E (dossier-8), never C, across all 5,252 and 3,880
records. Neither machine halts through 20M raw steps. Whether a C0
frontier read is reachable inside the excursions between records is
the danger-band question, not settled here.

## Why the finder's 70/75-rule specs broke

The finder demands one affine map per shape key, and every ladder
length k is a distinct shape key, so the single drift rule shattered
into one fragment per k (70 and 75 fragments at the 1.5M fitting
horizon, growing without bound). The conditional laws above, 13 and
12 rules with parity guards over a fixed integer vector, are the
replacement.

## Honest scope

Both laws are exact on every observed record transition at 20M raw
steps with zero exceptions. Branches never exercised at that horizon
carry no rule and would fail closed: for dossier-7, the even-side
last-rung minor renewal (`(4,B,1,4,2)`) and the grand renewals from
the complementary parities (terminal bottoms with B odd on the odd
side or B even on the even side, reachable only from terminal entries
a = 3 or 0 mod 4; the observed entries were a = 1517 and 26, residues
1 and 2 mod 4). For dossier-8, the odd-bottom ladder exhaustion
(`(4,B,4^g,2)`), grand renewal with B odd, and every g >= 2 grand
renewal (first event projected near 3 x 10^12 steps). The startup
rules rest on one observation each. Nothing here is proven; the
family, the vector (a, b, k, g), and the branch structure are the
empirical substrate a Lean layer would certify, and the halting-game
slots in as with dossier-6: law = drift/minor/grand, seed = the
startup record, terminal = raw execution.
