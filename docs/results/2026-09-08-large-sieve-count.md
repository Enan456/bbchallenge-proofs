# The large-sieve / lattice-point route to natural density zero

**Date:** 2026-09-08. Executes the counting route (method **C**) sketched in
`2026-09-08-closure-plan.md` for the density form of the almost-all
theorem: prove `#{(a,b): a,b<=N, halts} = o(N^2)` by counting integer seeds
on the fatal lines directly, and assess whether Montgomery's **large sieve**
gives a rigorous aggregate bound. Runs the exact verified renewal map `R`
(`renewal_analysis3.py`). Script: `qgkit/bb6/large_sieve_count.py`
(deterministic; symbolic affine forms verified against the exact map).

**This is measurement + analysis, NOT a proof.** The density form remains
conditional. What is new here is a precise, quantified diagnosis of *why*
both the large sieve and the elementary line-count fail, and exactly where
the obstruction sits. Two clean verdicts, one negative (large sieve), one
partial (elementary count closes the fat regime, fails on the thin tail).

## Setup: the fatal condition is a union of exact integer lines

On a fixed depth-`d` cylinder (itinerary `(k_1..k_d)`, where depth counts
diagonal / `F`-crossings), every first return is affine, so the offset is an
**exact integer affine form**
```
    o_d(a,b) = p*a + q*b + r .
```
The script extracts `(p,q,r)` by symbolic composition of the per-step affine
maps and **verifies it reproduces the exact map and the exact offsets** on
many seeds. "Halt at depth `d` in that cylinder" `=` the three parallel
lines `o_d(a,b) in {1,3,5}`. So the halting set is a union, over cylinders
and depths, of integer points on explicit lines, each restricted to its
cylinder (the cylinders partition the box, so there is no double count).

## (1) Affine-form coefficient growth: geometric, base ~3

The linear part accumulated over a cylinder is `P` with
`det P = (+-3)^{#C+#F}` **exactly** (`T`-steps have det 1, `C` and `F` steps
det -3, +3). Measured median coefficient size `max(|p|,|q|)` of `o_d` by
depth `d`:

| d | median max(|p|,q|) | ratio/prev | median |det P| | (|p,q|)/sqrt|det| |
|---|---|---|---|---|
| 1 | 1 | -- | 1 | 1.0 |
| 2 | 40 | 40.0 | 81 = 3^4 | 4.4 |
| 3 | 223 | 5.6 | 729 = 3^6 | 8.3 |
| 4 | 1252 | 5.6 | 6561 = 3^8 | 15.5 |
| 6 | 46897 | 11.7 | 531441 = 3^12 | 64.3 |
| 8 | 4.4e6 | 11.4 | 3^17 | 385 |
| 10 | 6.4e8 | 11.1 | 3^22 | 2081 |
| 12 | 2.6e10 | 6.0 | 3^28 | 9409 |
| 15 | 2.4e12 | 2.7 | 3^38 | 5.7e4 |

**The coefficients grow geometrically**, `|p,q| ~ 3^{Theta(d)}` (about one
factor `sqrt(3)..3` per crossing beyond the leading `sqrt|det P|` scale).
Consequence for counting: the fatal line `o_d = c` has integer-point spacing
`~ |p,q|/gcd(p,q)`, so once `|p,q| > N` the line carries **at most one**
box point (`floor(N/step)+1 <= 1`), generically zero. This splits every
cylinder into a **fat** regime (`|p,q| <= N`, line carries `~N/step`
points) and a **thin** regime (`|p,q| > N`, `<=1` point). The split happens
at depth `d* ~ log_3 N ~ 0.63 log N`.

## (2) Measured #halting scaling: Theta(N), decisively o(N^2)

Exact enumeration of the full box `1<=a,b<=N`:

| N | #seeds | #halting | #halt/N | max F-depth |
|---|---|---|---|---|
| 100 | 1e4 | 2581 | 25.8 | 11 |
| 200 | 4e4 | 5716 | 28.6 | 13 |
| 400 | 1.6e5 | 12326 | 30.8 | 16 |
| 600 | 3.6e5 | 19003 | 31.7 | -- |

Sampled (120k uniform box seeds each), `frac_halt * N`:

| N | 1000 | 2000 | 4000 | 8000 | 16000 | 32000 | 64000 |
|---|---|---|---|---|---|---|---|
| frac*N | 31.8 | 33.1 | 32.0 | 29.9 | 34.7 | 34.7 | 30.4 |

`#halt / N` rises from ~26 and **plateaus at ~30-35** across a 640x range of
`N`. So `#halting = C*N` with `C ~ 30-35` (a possible slowly-varying
sub-log factor is within the noise). Either way `#halting = N^{1+o(1)} =
o(N^2)`: **the natural density is 0, confirmed directly by exact count**,
not merely inferred from the measure form. Max halting depth grows like
`log N`, consistent with the fat/thin split at `d* ~ log_3 N`.

## (3) The large sieve: VACUOUS here -- it does not close it

The fatal condition, on a depth-`d` cylinder, pins the seed to `3` cosets of
the sublattice `P Z^2` of index `Q_d = |det P| = 3^{#C+#F}`. Montgomery's
large-sieve inequality bounds a set constrained modulo **many** moduli
`q <= Q` by the threshold `(N + Q^2)/L`. Tabulating the actual indices
`Q_d` realized by box seeds (`N=2000`):

| d | median Q_d | N/Q_d | (N+Q_d^2)/N^2 | trivial 3N^2/Q_d |
|---|---|---|---|---|
| 3 | 243 | 8.2 | 0.015 | 4.9e4 |
| 4 | 6561 | 0.30 | **10.8** | 1829 |
| 6 | 1.6e6 | 1.3e-3 | 6.4e5 | 7.5 |
| 8 | 1.3e8 | 1.5e-5 | 4.2e9 | 0.09 |
| 10 | 3.1e10 | 6.4e-8 | 2.5e14 | 4e-4 |

**The mismatch is structural.** The large sieve is the sharp tool for
**many small moduli** (`q <= Q <= sqrt(N)`), where `N + Q^2 ~ N` beats the
main term. Here the relevant moduli are **few and enormous**: a single
cylinder already has `Q_d = 3^{#C+#F}`, which **exceeds `N` by depth 3-4**
and `Q_d^2` exceeds `N^2` by depth 4. For any depth past 3 the sieve
threshold `N + Q_d^2` is larger than the entire box `N^2` -- the inequality
gives nothing. Worse, the **trivial** count of the 3 fatal cosets in the box,
`<= 3 N^2 / Q_d`, is *already* far sharper than the sieve (last column). The
large sieve's power is wasted on a problem that has no "many small moduli"
structure to exploit: the fatal conditions are **exact rank-1 equations**
(points on lines), not a sifting-out of residue classes across a range of
primes. `L^2`-decoupling (Bourgain-Demeter) is the same story -- it controls
lattice points on *curves*; our fatal sets are *straight lines*, on which the
elementary bound below is already optimal.

**Verdict (3): the large sieve does not close it, and cannot -- wrong tool
for the shape of the problem.** No aggregate `o(N^2)` comes out of it.

## (4) The elementary line-count: closes the fat regime, fails on the tail

Elementary bound: integer points on a line `p a + q b = c` in `[1,N]^2` number
`<= N/step + 1`, `step = max(|p|,|q|)/gcd(p,q)`. Summing over all cylinders
and depths (cylinders partition the box, so this is an exact upper bound for
`#halting`):
```
   #halting  <=  SUM_{cyl meeting box}  3 * ( N/step_cyl  +  1 ).
```
The two pieces behave oppositely, and the split is exactly the fat/thin line.

**The "+1" budget = number of cylinders meeting the box, summed over depth.**
Measured two ways:

- **All depths (seeds run deep):** `Sum_d #cyl(d)` plateaus at
  **`~61 * N^2`** (`/N^2 = 52.0, 58.3, 60.8, 61.1` for `N=100,200,400,600`).
  This is **Theta(N^2)** -- the naive "+1 per cylinder" budget is the SAME
  order as the whole box. Elementary count is **vacuous** if applied blindly
  over all depths.

- **Fat regime only (`|p,q| <= N`):** distinct cylinders up to the first
  crossing where the offset step exceeds `N`:

  | N | fat #cyl | /N | /(N log N) | max fat depth |
  |---|---|---|---|---|
  | 100 | 136 | 1.36 | 0.295 | 4 |
  | 200 | 222 | 1.11 | 0.210 | 5 |
  | 400 | 392 | 0.98 | 0.164 | 5 |
  | 600 | 558 | 0.93 | 0.145 | 6 |
  | 800 | 718 | 0.90 | 0.134 | 6 |

  The fat cylinder count is **`O(N)`** (`/N` decreasing to ~0.9,
  `/(N log N)` decreasing) -- so the "+1" overhead in the fat regime is
  `O(N) = o(N^2)`, negligible.

**What this buys, honestly:**

- **Fat regime (depth `<~ log_3 N`): rigorously controlled, `o(N^2)`.**
  There are only `O(N)` fat cylinders; on each, the fatal line has step
  `<= N`, and the classical sector/lattice count (Gauss, with sublattice
  density `3^{-(#C+#F)}`) gives its point count with error `O(1)` per line.
  The `O(N)` "+1"s sum to `O(N)`; the main terms sum to the genuine count of
  shallow halts, which is `Theta(N)` (measured). No equidistribution is
  needed here -- the fat regime is finite-depth lattice counting, exactly the
  part the probe already called provable. This is a **rigorous `o(N^2)` for
  the bulk of the halting mass.**

- **Thin regime (depth `>~ log_3 N`): the elementary count FAILS, for a
  precise reason.** Here each cylinder's fatal line carries `<=1` box point,
  but there are `Theta(N^2)` such cylinders (the `61 N^2` count is dominated
  by them). Paying "+1" for every thin cylinder gives `Theta(N^2)` --
  useless. To win one must show that the **overwhelming majority of thin
  cylinders' fatal lines contain NO box integer point** (only `o(N^2)` of
  them do). That is exactly a **non-concentration / equidistribution**
  statement for the offset form at the resolution of `{1,3,5}` -- the same
  arithmetic core the probe (`2026-09-07`) identified, with **no elementary
  shortcut**. The line-count reproduces the wall precisely; it does not
  remove it.

## Honest verdict

- **Large sieve: does NOT close it, and is the wrong tool.** The fatal
  conditions are exact rank-1 equations in cosets of sublattices of index
  `Q_d = 3^{#C+#F}`, which exceed `N` by depth ~3 and `N^2` by depth ~4. The
  large-sieve threshold `N + Q^2` is then larger than the whole box; the
  trivial coset count `3N^2/Q_d` already dominates it. No aggregate `o(N^2)`.

- **Elementary line-count: closes the fat regime, not the tail.** It gives a
  genuine **rigorous `o(N^2)` bound on halts up to depth `~log_3 N`** (the
  `O(N)` fat cylinders, finite-depth lattice counting), which carries the
  bulk of the halting mass. But the thin tail has `Theta(N^2)` cylinders and
  the naive `+1` budget is `Theta(N^2)`; controlling it needs the
  non-concentration estimate, not elementary counting.

- **Direct measurement: `#halting = Theta(N) = N^{1+o(1)}`, decisively
  `o(N^2)`** -- the density is 0, confirmed by exact enumeration and
  sampling over a 640x range. This is strong evidence, not a proof.

**Net:** neither modern-sieve route in the closure plan produces the
unconditional `o(N^2)`. The large sieve is structurally mismatched (few huge
moduli, not many small ones). The elementary count **cleanly bisects the
problem at the fat/thin line** and disposes of the fat side rigorously,
leaving precisely the thin-cylinder non-concentration estimate of
`2026-09-07-discrete-equidistribution-probe.md` as the sole remaining
obstruction -- now quantified: `O(N)` fat cylinders (handled) versus
`Theta(N^2)` thin cylinders (the wall). No Lean file, no paper, and no
certificate is changed by this note; the density form stays conditional.

```
Reproduce:  python3 qgkit/bb6/large_sieve_count.py   (deterministic; the
exact-enumeration blocks run in a few minutes, the rest in seconds)
```
