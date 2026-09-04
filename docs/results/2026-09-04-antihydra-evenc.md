# Antihydra: the even-c case of the dying family (1, 2, c)

**Date:** 2026-09-04 · **Code:** `qgkit/bb6/antihydra_evenc.py`
· **Sources:** `busy-beaver-core/BusyBeaverCore/AntihydraRawTM.lean`
(the abstract map `astep`, death set, and `Realizes` grammar)
· **Cross-reference:** `docs/results/2026-08-31-antihydra-parity.md`
(odd formula, even gap flagged open) and
`docs/results/2026-09-03-lethality-and-cones.md` (first statement of the
even-c re-entry). This note is an **independent reproduction** of both,
plus a closed analytic derivation of both parity branches.

## Honesty note (scope)

Everything below is **measurement and analysis of the abstract/raw map**.
It does **not** resolve, or bear on the truth of, the Antihydra
non-halting conjecture (`SafeOrbitA` in the Lean file). On the contrary,
the even-c result *reduces* to that same open conjecture on derived
seeds. No claim here is a proof of non-halting, and every halt reported is
a real, fail-closed raw halt reached by direct simulation.

## The object

The Lean file reduces raw non-halting from the blank tape to `SafeOrbitA`:
the abstract orbit of

```
astep(a,m,c) = (a, m-2, c+3)      if m >= 3            [hydra]
             = (a-1, c+3, 2)      if m = 2 and a >= 2  [drop]
             = none               if m = 2 and a  < 2  [DEATH]
             = (a+2, c+2, 2)      if m = 1             [merge]
             = none               if m = 0             [DEATH]
```

never reaches `none`. The death set is `D = {(a,2,c): a<=1} ∪ {(a,0,c)}`.
The `Realizes` grammar demands `a,m,c >= 1`, so the **only death states
with a tape realization are the family `(1, 2, c)`** (confirmed by scan,
step [0] of the script: among `a,m<4`, the realizable death states are
exactly `(1,2,1)` and `(1,2,2)`). Abstract death is *loss of grammar
certification*, not in itself a raw halt. The question this note answers
is the actual raw fate of the materialized tape `1^1 0 1^2 0 1^c` (state B,
head on the fresh frontier) as a function of `c`.

The transition table parsed from the machine string is checked entry by
entry against the Lean `instr` table before any run (script asserts this at
import).

## 1. Odd c: confirmed, and now derived in closed form

**Confirmation.** Direct raw simulation of `materialize(1,2,c)` to the
undefined transition `F0`, for **every odd c from 1 to 499** (250 values),
gives the exact halt time `(3c^2 + 44c + 125)/4` with **zero mismatches**;
spot checks at c = 999, 2001, 4999 also match exactly (e.g. c = 4999 halts
at 18,797,521 raw steps). This reproduces the parity note's formula
(verified there to c = 79 / spot c = 999) and the 2026-09-03 extension to
c = 9,999.

**Derivation (new).** The quadratic is not a fit; it decomposes exactly.
The raw machine on `(1,2,c)` performs the *extended abstract descent* of
section 2, and the per-rule raw cost model closes it in three pieces:

| piece | event | raw cost |
|---|---|---|
| drop | `(1,2,c) -> (0,c+3,2)` (counter falls to 0) | `2c + 16` |
| ladder | `J = (c+1)/2` hydra steps down the m-ladder; step j costs `6j+15` | `3J^2 + 12J` |
| tail | terminal death from `(0,2,cfinal)`, `cfinal = (3c+7)/2` | `cfinal + 5` |

Summing: `(2c+16) + (3J^2+12J) + (cfinal+5) = (3c^2+44c+125)/4` identically
for odd c. The script recomputes this decomposition and checks
`predicted == raw simulation` for all odd c in 1..499 (0 mismatches);
worked examples c = 1 (18+15+10 = 43), c = 3 (22+36+13 = 71),
c = 99 (214+8100+157 = 8471). The second difference `f(c+2)-f(c) = 3c+25`
is the fixed slope of this quadratic.

## 2. Why parity decides everything: the extended descent

Allow the counter to reach `a = 0` (physically, the one-cell counter block
just vanishes) and continue the abstract map. From `(1,2,c)`:

```
(1,2,c) --drop--> (0, c+3, 2) --hydra*--> m-ladder descends by 2, c grows by 3
```

The ladder starts at `m = c+3` and steps down by 2. Where it lands is
fixed by the **parity of c+3**:

- **c odd  => c+3 even:** the ladder lands on `m = 2` with `a = 0`. That is
  `astep = none` — genuine terminal **DEATH**. The raw machine halts. This
  is section 1.
- **c even => c+3 odd:** the ladder lands on `m = 1`, which is a **MERGE**:
  `(0,1,cfinal) -> (2, cfinal+2, 2)`. The counter is resurrected to `a = 2`,
  a survivor-eligible value. **No death.**

Step [2] of the script prints this ladder-landing for c = 1..12; step [3]
reads the resulting live record back off the raw tape.

## 3. Even c: re-entry into a LIVE seed, raw-verified

For even c the descent's merge lands the machine on a live grammar record.
Working the arithmetic, the merge target is

```
cfinal = 2 + 3*(c+2)/2 = (3c+10)/2,   re-entry = (2, cfinal+2, 2) = (2, (3c+14)/2, 2).
```

**Raw verification.** Running the raw machine from `materialize(1,2,c)` and
reading the first live state-B record off the tape via the `Realizes`
grammar gives, for **every even c from 2 to 40**, exactly
`(2, (3c+14)/2, 2)` — 20/20 matches:

| c | first re-entry (raw) | raw step | formula (2,(3c+14)/2,2) |
|---|---|---|---|
| 2 | (2, 10, 2) | 94 | (2, 10, 2) |
| 4 | (2, 13, 2) | 131 | (2, 13, 2) |
| 10 | (2, 22, 2) | 278 | (2, 22, 2) |
| 40 | (2, 67, 2) | 1823 | (2, 67, 2) |

So `(1, 2, even)` is **not a realization of a dying state at all**. The
"abstract death" `astep(1,2,even) = none` is an artifact of the grammar's
`a >= 2` floor at the drop; the raw machine folds the counter and re-enters
ordinary Antihydra dynamics.

## 4. The true even-c fate, and the population split

From the re-entry, the raw orbit is an ordinary Antihydra orbit on the
derived seed `(2, (3c+14)/2, 2)`. It genuinely halts **only if that orbit
later reaches a boundary `(1,2,c')` with c' ODD** — the only genuinely
halting boundary. Every `(1,2,even)` boundary it crosses is itself another
re-entry. Folding those re-entries (astep with odd-boundary = halt,
even-boundary = re-enter) gives the true fate; it is validated against
direct raw runs wherever they terminate within reach:

| even c | folded fate | direct raw check |
|---|---|---|
| 2 | halt: reaches odd (1,2,101) after 1 re-entry | raw halt at 15,536 ✓ |
| 14 | halt: reaches odd (1,2,65) | raw halt at 6,657 ✓ |
| 16 | halt: reaches odd (1,2,3071) | raw halt at 12,785,384 ✓ |
| 6, 8, 12 | halt at an odd terminal ~10^4 (raw time far beyond 2·10^7) | (beyond tested raw horizon) |
| 4, 10, 18, 20, 50, 100, 1000 | **survives** (no death in 2·10^7 abstract steps; counters grow into the millions) | (no raw halt observed) |

The split is exactly the one reported on 2026-09-03, reproduced here with
an independent simulator. Even c is therefore **not a uniform escape**: it
splits into two populations, both governed by `SafeOrbitA` on the derived
seed — those whose derived orbit eventually reaches an odd boundary (halt,
some far beyond any tested horizon, which is why the parity note read them
as escapes) and those whose derived orbit survives forever (conjecturally
non-halting). Survivors show the counter drifting up (a in the tens) and
m, c into the tens of millions, the signature of a genuine Antihydra
survivor.

## 5. Verdict: unified or separate?

**Separate regimes; the odd-c formula does not extend to even c.**

- **odd c:** a genuine raw halt with the closed-form time
  `(3c^2+44c+125)/4`, derived exactly in section 1. The counter dies.
- **even c:** *no closed-form halt time exists.* The counter is
  resurrected (`a: 1 -> 0 -> 2`) and the machine re-enters the live seed
  `(2, (3c+14)/2, 2)`. Its raw fate is precisely the Antihydra fate of that
  seed — a shifted instance of the same open conjecture, splitting into a
  halting and a surviving population with no polynomial law.

The single quadratic and the re-entry are two outcomes of **one**
mechanism — the extended descent — selected by the parity of `c+3`. That
is the honest sense in which the picture is unified: one descent, two
landing rows of the map (`m = 2, a = 0` vs `m = 1`). But there is **no
single lethality/timing formula covering both parities**: even c has no
finite death time in general.

## 6. What remains open for even c

- Whether a given even-c derived orbit `(2, (3c+14)/2, 2)` ever reaches an
  odd boundary (halt) or survives forever is **an instance of `SafeOrbitA`
  itself** — undecidable by any formula here. The surviving cases (c = 4,
  10, 18, 20, 50, 100, 1000, ...) are conjectural non-halters, exactly as
  the certified seed (2,7,2) is.
- The parity map `c -> (2, (3c+14)/2, 2)` is verified against the raw
  machine only to c = 40 (re-entry read-back) and for the halting cases
  c = 2, 14, 16 (full raw halt). Beyond that, the fold is exact abstract
  iteration, certified as the raw fate by the Lean transport theorems, not
  by execution.
- The odd-c formula is confirmed by direct raw simulation to c = 499
  exhaustively (spot to 4999 here, to 9,999 in the 2026-09-03 C run) and
  derived in closed form; a Lean proof (induction in steps of 2, the
  `3c+25` increment) is sketched in the 2026-09-03 note but not carried.

## Reproduce

```
python3 qgkit/bb6/antihydra_evenc.py
```

Prints: the death-set scan; odd-c formula check + decomposition (0
mismatches to c = 499, spot to 4999); the extended-descent ladder landing
by parity; the even-c re-entry read-back (c = 2..40, 20/20); fold-vs-raw
for c = 2, 14, 16; and the population split for c up to 1000. Runtime ~30s.
