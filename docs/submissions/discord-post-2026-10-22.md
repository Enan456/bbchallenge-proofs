# Discord post draft — bbchallenge server (2026-10-22)

Post to the BB(6) / cryptids channel. Discord's limit is 2,000 characters
per message for non-Nitro accounts, so send the first block as the message
and the rest as thread replies. Repo link at the top. Be ready to answer
"can I rebuild it" with the two commands at the bottom.

---

**Lean closures for 115 BB(6) holdouts, held back for explainability reasons, published now because they overlap DeepMind's cryptids repo and might be useful**

Repo: https://github.com/Enan456/bbchallenge-proofs

Hi all. Some context first, because it affects how you should read this. I
started on BB(6) in July as a way to get reacquainted with mathematics and to
try some less conventional approaches on a hard problem. Everything in the repo
builds on this community's work: mxdys's 1,094-machine holdout snapshot, the
wiki's machine format and Antihydra statement, Coq-BB5's zipper tape, and the
BusyLean and busycoq idea of formalizing a reduction even when the conjecture
stays open. Thank you for all of that.

I chose not to publish over the summer. The reason is that the method is close
to what DeepMind's pipeline does, in that an automated layer finds the rules and
the Lean layer certifies them, and I was not comfortable with the distance
between "kernel-checked" and "I can explain to you why this machine behaves this
way". I still think there is a lot of explanation owed on these machines, mine
included, and if anything the bar for that should go up rather than down as more
of us automate the certification step. I'm dropping this now because the overlap
with DeepMind's repo makes the artifacts useful as an independent check, and
holding them back no longer serves anyone.

What's in the repo, all kernel-checked (`lake build`, axioms propext and
Quot.sound only, no sorry, no Mathlib):

- 115 theorems of the form `Safe_X → ¬RawHalts blankStart`, one per holdout,
  where `Safe_X` is an explicit, executable, fail-closed abstract orbit (five
  integers for one mirror pair, `(state, word)` records for the left-growing
  machines). Halt localization, the episode transitions for all block values,
  and the transport from abstract orbit to raw tape are proven. The only thing
  assumed is that the orbit never leaves its guarded region, and that
  assumption is the open problem.
- Parser-parity theorems against the standard machine format and a
  bisimulation with the zipper tape, so the formal object is provably the
  community's machine and not my transcription of it.
- For Antihydra, a proof that my orbit conjecture is equivalent to the wiki's
  1-D hydra statement, so nobody has to trust that the two coincide.

The reason I'm posting now: DeepMind's cryptids repo (arXiv:2610.22603) turned
out to contain seven machines I'd also closed conditionally, four of them with
no wiki page:

- `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD` and its mirror
  `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE`
- `1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA`
- `1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA`

Neither side saw the other's work (mine was private), so I think the useful
thing to do with that coincidence is treat it as an independent reproduction.
Today I ported their `start/encode/next` for those four machines literally
from their Lean and replayed both their acceleration and my orbit against one
raw simulation per machine, 2×10⁷ steps each (10⁸ for the fourth). All four
agree with the machine and with each other, and neither fail-closed system
dies. Their reductions hold up. Harness and per-machine reports are in
`docs/results/2026-10-22-gdm-cross-verification.md`.

Two small things I noticed while reading their files, offered in case they
save someone else time:

1. The docstring of their fourth machine says the start configuration is
   reached in 66 steps; the trace reaches it at 169 (66 is the step count of
   one of their turnaround lemmas). The proof is a `ReachesStar` statement
   with no count, so nothing is affected. I'll open a PR.
2. Their `next` composes whole sweep cascades, so it isn't a first-return
   map. On the mirror pair's second machine the trace passes through 2,317
   other members of their own canonical family before reaching the stated
   successor. That's fine under `IsValidAcceleration`, just worth knowing when
   you read the rule tables.

Where their work is stronger than mine: their statement is an `iff`
(`IsHalt ↔ CollatzHalts`), and mine is one-directional with the converse only
tested empirically. Upgrading my four to an `iff` against their predicates is
the obvious next step and I'd welcome help or criticism on it. What I can add
to theirs is coverage (111 machines they don't have, including the Antihydra
bridge) and the format-parity layer.

Nothing here decides a machine. The mirror pair's conjecture provably has no
congruence invariant to modulus 384 and no rotation rigidity, which is as far
as I got on the arithmetic. More formal reductions of the same open question,
from any pipeline, don't move it on their own. What moves it is someone
understanding why these particular counter maps avoid their fatal set, and
that is the part I haven't managed and would like to learn from people here.
Treat the repo as raw material for that, not as a result. Corrections very
welcome, and I'm happy to walk anyone through a file.

Reproduce:

```
git clone https://github.com/Enan456/bbchallenge-proofs && cd bbchallenge-proofs
cd busy-beaver-core && lake build            # ~119 jobs, prints axioms per closure
cd .. && python -m qgkit.bb6.gdm_cross d2 d3 d7 d27 --horizon 20000000 --md out.md
```

---

## Notes for the author (not for posting)

- Credit names if you know who did what on the pieces you used: mxdys
  (holdout list, busycoq), Shawn Ligocki, savask, Racheline, int-y1
  (BusyLean), Tristan Stérin and the Coq-BB5 team. Naming people is cheap and
  it is how this community keeps score.
- If the DeepMind authors reply, thank them for publishing the Lean; your
  cross-check only exists because their proofs were readable.
- If asked about the 97 generated closures: they are template instances from
  `rawstep_generator.py`, each with its own differential test; the 18 named
  ones are hand-built. Say so before anyone has to ask.
