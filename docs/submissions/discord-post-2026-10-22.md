# Discord post draft — bbchallenge server (2026-10-22)

Two versions. The first is the one to post: every sentence is checkable
from the repo, and the comparison does the talking. The second is the
same content with the edge the author wants; it is kept here so the
choice is deliberate. Either way, post to the BB(6) / cryptids channel,
one message, repo link at the top, and be ready to answer "can I rebuild
it" with the two commands at the bottom.

---

## Version A (recommended)

**Independent Lean closures for 115 BB(6) holdouts, incl. 3 of DeepMind's 11 "novel" cryptids — now public, with a cross-check of both formalizations**

Repo: https://github.com/Enan456/bbchallenge-proofs

Short version: between late July and early September I built, solo, a Lean 4
pipeline that reduces the non-halting of BB(6) holdouts to explicit, executable
orbit conjectures, and I kept it private while I tried to close the arithmetic.
Then DeepMind's cryptids paper landed (arXiv:2610.22603). Seven of their 53
machines are ones I had already closed conditionally, and three of them are in
the eleven the paper calls novel:

- `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD` (my dossier-2, closed 2026-08-25)
- `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE` (dossier-3, its mirror, 2026-08-25)
- `1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA` (dossier-7, 2026-09-03)

plus `1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA` (dossier-27, 2026-09-04),
which they added to the repo on Oct 20. Commit dates are in the git history;
nobody saw anybody's work, so this is a genuine independent reproduction, not
a priority claim.

What's in the repo, all kernel-checked (`lake build`, axioms propext/Quot.sound
only, no sorry, no Mathlib):

- 115 theorems of the form `Safe_X → ¬RawHalts blankStart`, one per holdout,
  where `Safe_X` is a fail-closed executable orbit (five integers for the
  dossier-2/3 pair, `(state, word)` records for the left-growing machines).
  Halt localization, every episode transition for all block values, and the
  abstract-to-raw transport are proven; the only thing assumed is that the
  orbit never leaves its guarded region.
- Parser-parity theorems against the standard machine format and a
  bisimulation with the Rocq-style zipper tape, so the formal object is
  provably the community's machine.
- For Antihydra, a proof that my orbit conjecture is equivalent to the wiki's
  1-D hydra statement.

Cross-verification (today): I ported DeepMind's `start/encode/next` for the
four shared machines literally from their Lean and replayed both their
acceleration and my orbit against one raw simulation, 2×10⁷ steps each. All
four agree with the machine and with each other; neither fail-closed system
dies. Details, per-machine reports and the harness are in
`docs/results/2026-10-22-gdm-cross-verification.md`. Two things worth knowing
if you read their files:

1. Their dossier-27 docstring says the start configuration is reached in 66
   steps; it's 169 (66 is one of their turnaround lemmas). Proof unaffected,
   just a docstring slip.
2. Their `next` is not a first-return map. On dossier-3 the trace passes
   through 2,317 other members of their own canonical family before hitting
   the stated successor. Fine under `IsValidAcceleration`, but don't read it
   as "the next time the pattern recurs".

Where they're ahead: their statement is an `iff` (`IsHalt ↔ CollatzHalts`),
mine is one-directional with the converse only empirical. Where I'm ahead:
coverage (115 vs 53 machines), halt localization, format parity. Neither of us
decided anything; the dossier-2/3 question provably has no congruence
invariant to modulus 384 and no rotation rigidity, which is why it's still
open.

Happy to walk anyone through a file. Reproduce:

```
git clone https://github.com/Enan456/bbchallenge-proofs && cd bbchallenge-proofs
cd busy-beaver-core && lake build            # ~119 jobs, prints axioms per closure
cd .. && python -m qgkit.bb6.gdm_cross d2 d3 d7 d27 --horizon 20000000 --md out.md
```

---

## Version B (the author's edge, same facts)

Same post with a different opening paragraph. Everything after "What's in the
repo" is identical.

**One person, no compute budget, same machines, two months earlier**

Repo: https://github.com/Enan456/bbchallenge-proofs

DeepMind's cryptids paper (arXiv:2610.22603) presents eleven BB(6) machines as
novel discoveries of a Gemini pipeline. Three of them, plus one they added to
the repo last Monday, are machines I had already closed conditionally in Lean
in August and early September, working alone on a laptop, along with 111
others they don't have. Dates are in the git log. I'm publishing today, and I
spent the afternoon reproducing their four reductions against mine so this is
a cross-check and not just a complaint. They hold up, with one docstring error
and one thing their `next` map doesn't do that a reader would assume it does.
Details below. The point isn't who was first; it's that this frontier is
reachable without a lab, and the math — not the model — is what's hard.

[continue from "What's in the repo" in Version A]

---

## Notes on tone (for the author, not for posting)

- The bbchallenge Discord is small and technical; Shawn Ligocki, mxdys,
  savask, Racheline and the DeepMind authors' collaborators read it. A post
  that is precise and checkable will be reproduced within a day; one that
  reads as a grievance will be politely ignored. Version A gets you the
  reproduction, the wiki credit on dossier-2/3/7/27, and probably a reply from
  the DeepMind authors. Version B gets you the same facts read less charitably.
- Do not say "scooped": they published first and the repo was private. "Independent
  reproduction" is both accurate and, in this community, the higher-status
  claim.
- The docstring error and the granularity observation are the strongest cards
  because they show you actually read their Lean. Lead with substance, let
  people draw the "one person vs. a lab" conclusion themselves; they will.
- If asked about the 97 generated closures: say plainly they are template
  instances from `rawstep_generator.py`, each with its own differential test,
  and that the 18 named ones are hand-built. Don't let anyone discover that
  distinction for you.
