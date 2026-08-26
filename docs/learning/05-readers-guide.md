# A reader's guide to "Orbital Dragons to Hunt Cryptids"

**Audience.** A mathematically literate reader who knows the busy
beaver subfield and Collatz-like problems, and wants to follow the
paper's motivations, definitions, and proof architecture without
reading 15,000 lines of Lean.

---

## 1. Motivation: BB(6) machines are hailstone problems

The busy beaver value $BB(n)$ is the longest halting runtime of any
$n$-state, 2-symbol Turing machine started on a blank tape. Computing
$BB(n)$ means *deciding every $n$-state machine*: proving each one
either halts (run it) or runs forever (prove it).

$BB(5)$ was settled in 2024. At $n = 6$ the obstruction changes
character. After all standard deciders run, a residual set of machines
("cryptids") remains, and the reason they resist is that **their tape
dynamics simulate iterated arithmetic maps of hailstone type**. The
flagship example, Antihydra, halts if and only if a certain orbit of
$b \mapsto b + \lfloor b/2 \rfloor = \lfloor 3b/2 \rfloor$ (started at
8, with a side-counter fed by the parities encountered) ever reaches a
dead state. That is structurally the Collatz situation: a deterministic
integer map whose orbit must avoid a sparse "bad set" forever, with
parities driving the branching. Tao's 2019 theorem — almost all Collatz
orbits attain almost bounded values — is the strongest known result for
such maps, and it is *measure-theoretic*; busy beaver questions need
*pointwise* control of one specific orbit. This is why cryptids are
believed hard, and why anything that changes the *type* of the question
is progress.

**The paper's claim, in one sentence:** for two of the BB(6) holdout
machines (a mirror pair we call dossier-2 and dossier-3), we prove —
machine-checked end to end — that the entire halting question is
equivalent-in-the-useful-direction to a single conjecture about a
deterministic affine map on five integers; and we prove the reduction
is *sharp*, in that the parameter region the conjecture excludes
provably triggers halting.

## 2. The machine model (what the Lean actually talks about)

All definitions live in core Lean 4 with axioms only
$\{\mathrm{propext}, \mathrm{Quot.sound}\}$ (no classical choice; the
proofs are effectively constructive).

- **Configuration.** $\mathsf{Config} = (\text{state},\ \text{head} \in
  \mathbb{Z},\ \text{tape} : \mathbb{Z} \to \{0,1\})$. The tape is a
  total function; the only mutation is pointwise override
  ($\mathsf{writeAt}$).
- **Step.** $\mathsf{step} : \mathsf{Config} \to
  \mathsf{Option\ Config}$ applies the transition table; the table has
  exactly one undefined entry, and reaching it is the *only* way to
  halt. $\mathsf{stepN}\ n$ iterates. For dossier-2 the table is
  `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD` (undefined: state $E$
  reading $0$); dossier-3 is its dynamical mirror.
- **Halting.** $\Halts \equiv \exists n,\ \mathsf{stepN}\ n\
  \mathsf{blankStart} = \mathsf{none}$.
- **Probe safety.** Halt localization theorems show any halting run
  must pass through a *probe event*: the danger state (C for dossier-2)
  reading a $0$ whose critical neighbour is also $0$. Define
  $\mathsf{CProbeSafe}$: every reachable danger-read-of-$0$ has a $1$
  on the critical side. Theorem: $\mathsf{CProbeSafe} \Rightarrow
  \lnot \Halts$. Everything else in the paper is about establishing
  probe safety forever.

## 3. The shape: what the tape always looks like

After a short startup, at every "spawn entry" (a canonical recurring
instant), the tape is exactly a **holeTape**:

$$\mathsf{holeTape}(l, r, \text{holes}) (q) \;=\;
\begin{cases} 0 & q \in \text{holes} \\ 1 & l \le q \le r \\ 0 &
\text{otherwise,} \end{cases}$$

i.e., a solid field of 1s on $[l, r]$ with **two mobile holes** $h_1 <
h_2$ (sometimes a third, freshly dug at a fixed offset). The abstract
state is therefore five numbers: a tag (2-hole or 3-hole family) and
$(l, h_1, h_2, r)$. Convenient derived coordinates:
$$a = h_1 - l, \qquad b = h_2 - h_1, \qquad c = r - h_2 .$$

## 4. The interaction calculus: what the machine does, forever

Between spawn entries the machine performs one of **seven episodes**,
each certified as a theorem with exact step count, exact output shape,
and probe safety:

1. **Spawn** (7 steps): at the right edge, extend the field by one and
   dig a fresh "carried" hole at $r - 2$ — which is *precisely* the
   entry pattern of the crawl.
2. **Caterpillar crawl** ($10$ steps per cycle, $2$ cells of travel):
   the machine's gait. Certified by an $n$-fold induction
   (`cat_run`) with a closed-form tape image; the cycle carries its
   own moving hole at offset 3 and consumes two 1s per cycle.
3. **Cross** ($+4$): when the crawl meets a static hole at *even*
   arrival parity, the march extends and the hole is absorbed — and
   re-appears 4 cells to the right (the cat's own trail hole becomes
   static). Parity flips.
4. **Terminate** ($+6$): at *odd* arrival parity, the danger state
   reads the hole's $0$ — these are the **only probe events in the
   machine's entire eternity**, and each is proven safe — and a
   fill-chain plants the hole 6 cells right, then pivots into the
   return sweep.
5. **Fuse** ($+9$): adjacent holes ($b = 1$) trigger a triple
   fill-chain; the fused hole lands 9 right of the lower one, and the
   parity-shifted sweep exits leaving a fresh hole at $r+1$.
6. **Edge businesses** (odd/even $a$): the crawl runs off the left end
   of the field, extends it by 1 or 3, and plants the new first hole —
   the *renewal* moves.
7. **Return sweep** ($2$ cells per pair): the D–F gait home. The sweep
   lemma requires 1s only on the D-parity cells; F preserves anything —
   which is *why* holes cross for free and why every shift constant is
   what it is: $+4$, $+6$, $+9$ all preserve F-parity of every hole.

The calculus was validated **fail-closed** against $10^9$ raw steps per
machine: every episode must be predicted exactly (position, full
shape); one unexplained event aborts the pipeline. There were none.

## 5. The five-integer orbit and the conjecture

$\mathsf{metaStep}$ is the episode dispatcher as a pure function on
abstract states — a case split whose guards you can read as the
machine's "phase":

- 3-hole, $b \ge 3$: **generic traversal**
  $(l, h_1, h_2, r) \mapsto (l,\ h_1{+}6,\ h_2{+}4,\ r{+}1)$, so in
  derived coordinates $(a, b, c) \mapsto (a{+}6,\ b{-}2,\ c{-}2)$.
- 3-hole, $b = 1$: **fuse** $\mapsto (l,\ h_1{+}9,\ r{+}1,\ r{+}2)$.
- 2-hole, $h_2 = r-1$: **spawn-variant** (post-fuse bookkeeping).
- 2-hole, $h_2 = r-3$, $r - h_1$ odd: **carried terminate**.
- 2-hole, $h_2 = r-3$, $r - h_1$ even: **deep renewal**, odd/even $a$
  variants $\mapsto (l{-}1,\ l{+}5,\ h_1{+}4,\ r{+}1)$ /
  $(l{-}3,\ l{+}6,\ h_1{+}4,\ r{+}1)$ — note these *swap the roles of
  $a$ and $b$* and reset $a$ to $6$ or $9$.
- otherwise, 2-hole interior: **spawn**.
- **No guard satisfied: $\mathsf{none}$.** This is the fail-closed
  boundary.

$$\Safe \;\equiv\; \forall k,\ \mathsf{metaOrbit}(k) \neq \mathsf{none},$$

where $\mathsf{metaOrbit}$ iterates $\mathsf{metaStep}$ from the
startup's landing state $s_0$.

**Why the conjecture is sharp.** Within a run of generic traversals,
$\gamma = c - b$ is *conserved* while $a$ grows by 6 per loop; the loop
exits either by $b$ exhausting (fuse path, requires $\gamma \ge 7$
effectively) or $c$ exhausting (deep path, $\gamma \le -1$). Renewals
then re-seed $(a,b,c)$ subtractively — a **Euclid–Collatz hybrid**:
Euclid-like because renewals subtract and swap the counters, Collatz-like
because parities select the branch. The bands
$\gamma \in \{1, 3, 5\}$ (and $b_C \le 2$ at carried entries) are
**lethal**: constructing those configurations and running the raw
machine produces the probe violation — the halting transition — within
about 50 steps. So $\Safe$ is not a convenience of our proof; its
failure *is* halting. The conjecture holds empirically for $10^8$
abstract episodes ($\approx 10^{15}$ raw steps).

## 6. The theorem chain (how the pieces snap together)

$$\underbrace{\mathsf{anchor}}_{\text{235 / 2044 concrete steps}}
\;\longrightarrow\;
\underbrace{\mathsf{meta\_transport}}_{\text{episodes realize } \mathsf{metaStep}}
\;\longrightarrow\;
\underbrace{\text{keystone}}_{\text{induction over segments}}
\;\longrightarrow\;
\mathsf{CProbeSafe}
\;\longrightarrow\;
\lnot \Halts$$

- **Anchor**: a fully concrete certified run from the blank tape to
  $s_0$'s configuration — including each machine's one *degenerate*
  episode (a startup-scale corner where the generic guards fail). No
  conjecture touches the startup.
- **Transport**: if $\mathsf{metaStep}(s) = \mathsf{some}\ s'$, then
  from any configuration realizing $s$ the machine runs a positive,
  probe-safe number of steps to a configuration realizing $s'$. Proven
  by dispatching to the seven episode theorems; the Nat-typed cycle
  counts double as parity certificates.
- **Keystone**: safety in pieces is safety forever — an invariant
  maintained by positive safe segments yields $\mathsf{CProbeSafe}$ for
  the infinite run (strong induction on step count).
- **Conclusion**: $\Safe \rightarrow \lnot\Halts(\mathsf{blankStart})$,
  at axioms $\{\mathrm{propext}, \mathrm{Quot.sound}\}$.

## 7. The charts (why "non-Euclidean," and what they're for)

The charts are *discovery* instruments — no theorem depends on them:

- **Log chart** $x \mapsto \log(1+x)$: the Maslov–Viro tropical limit;
  affine record dynamics become straight lines, corners mark renewals.
- **Simplex chart** $(a,b,c)/(a{+}b{+}c)$: quotient out scale
  (Perron–Frobenius style); only *shape* dynamics remain, and the
  lethal configurations sit at literal corners.
- **Hyperbolic chart** (shape vs.\ log-scale): renewal orbits are
  hierarchies, and hierarchies embed naturally in negative curvature
  (the Poincaré-embedding insight); the eternal orbit is an ascending
  zig-zag.

Their role in the pipeline: they made the piecewise-affine,
renewal-structured nature of the dynamics *visible*, which told us what
to certify.

## 8. What is and is not claimed

- **Claimed**: the conditional theorems, the sharpness of the
  conjecture (lethality of the excluded bands), the validation record,
  and the reduction in the *type* of the open problem — from a Turing
  machine to a five-integer recurrence.
- **Not claimed**: unconditional non-halting of any open machine; any
  progress on the arithmetic of the recurrence itself; any endorsement
  by the authors whose methods we build on.

*Prepared 2026-08-26; companion to
`docs/submissions/deepmath2026/deepmath2026.pdf` and the Palomar
entries `dossier2cryptid` / `dossier3cryptid`.*
