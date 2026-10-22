# Discord post draft — bbchallenge server (2026-10-22, rev 3)

Context that shaped this revision (from the #bb6 thread, 2026-10-19..22):
Shawn Ligocki added wiki pages for all 11 DeepMind machines on 10-21 and
invited people to study their dynamics; Tom Zahavy (DeepMind) is in the
channel and posted a dossier-27 observation on 10-22; Shawn said the
community lacks a word for "characterized into a set of dynamic equations
(regardless of difficulty)"; Andrew Ducharme is pushing back on loose use of
"cryptid"; Dennis and slugbird end posts with AI-assistance disclosures.

Post the first block as the message in #bb6, the second as a reply in Tom's
thread, the third as a thread reply under your own message. 2,000-char limit
per message.

---

## Message 1 (main post)

**Re: the 11 DeepMind machines — independent Lean characterizations of 3 of them (+1 from their 10-20 batch), and a replay of their accelerations**

Repo: https://github.com/Enan456/bbchallenge-proofs

Shawn's invitation yesterday to dig into the 11 new machines is a good
moment to put this out. Since July I've been reducing BB(6) holdouts to
explicit, executable orbit conjectures in Lean 4, as a way of relearning
mathematics on a hard problem. I kept it private on purpose. The bar I
held myself to is the one in cosmo's 2022 deciders' validation process
(discuss.bbchallenge.org/t/85): decide at least 10% of the remaining
undecided machines, be reproduced independently, and carry a proof of
correctness that someone else validates. My 115 closures are 10.5% of the
1,094 snapshot, but they decide nothing, and the proof-of-correctness
clause only means something if a second person can follow *why* the
machine behaves that way. Being honest, I can explain to another person
roughly a third of what the pipeline found, and that is a generous count.
I think that gap is the real state of the art for every automated
characterization right now, including the ones in the paper, and that the
bar should go up as the certification step gets cheaper. So read what
follows as a reference artifact and a cross-check, not as understanding.
Three of the 11 are machines I'd already characterized:

- `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD` and its mirror
  `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE` (closed 2026-08-25)
- `1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA` (2026-09-03)
- plus `1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA` from their 10-20 batch
  (2026-09-04)

In Shawn's words these are machines "characterized into a set of dynamic
equations", not claims of hardness. In the repo each is a theorem
`Safe_X → ¬RawHalts blankStart` where `Safe_X` is a fail-closed executable
orbit (five integers for the mirror pair, `(state, word)` records for the
left-growers); halt localization, every episode transition for all block
values, and the transport to the raw tape are proven, and the assumption is
the open problem. Same shape for 111 other holdouts from mxdys's 1,094 list,
all building `lake build` with axioms propext/Quot.sound, no sorry, no
Mathlib. Parser parity against the standard format and a bisimulation with
the Coq-BB5 zipper tape are included so the formal object is provably the
community's machine. Nothing is decided.

Cross-check: I ported DeepMind's `start/encode/next` for those four
literally from their Lean and replayed both their acceleration and my orbit
against one raw simulation per machine (2×10⁷ steps each, 10⁸ for the
fourth). All four agree with the machine and with each other; neither
fail-closed system dies. Their reductions hold up. Report and harness:
`docs/results/2026-10-22-gdm-cross-verification.md`. Two things I'd flag
for @Marco / @tomzahavy: (1) the fourth machine's docstring says `S6 1` is
reached in 66 steps; it's 169 (66 is your `step_drain_odd_end` lemma), proof
unaffected; (2) `next` isn't a first-return map — on the mirror's second
machine the trace passes 2,317 other canonical configurations before the
stated successor. Fine under `IsValidAcceleration`, just worth a note in the
rule tables.

I'll add a "formalization" section to each of the three wiki pages this week
unless someone objects. Their `IsHalt ↔ CollatzHalts` is stronger than my
one-directional statement; a Lean bridge from my orbit conjecture to their
`CollatzHalts` is in progress. What I'd most like from this channel is the
part neither pipeline produced: someone who can see why these counter maps
avoid their fatal set. The mirror pair's map provably has no congruence
invariant to modulus 384 and no rotation rigidity, which is as far as I
got, and I'd rather hear that explained than add another certified
reduction to the pile.

AI assistance disclosure: the Lean proofs, the harness and this post were
produced with Claude (Anthropic) and Codex (OpenAI); I ran every build and
check myself and the mathematical framing is mine, including its gaps.

---

## Message 2 (reply in Tom's thread about `1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA`)

Some data on this one from my side. My record orbit for it (arrivals at
fresh left extremes, each certified as one `wstep` of a word engine in
Lean) runs 16,613 exact record transitions over 10⁸ raw steps with no
fail-closed exit, max word length 16,656, max record gap 120,867 raw steps.
Your `R2` rule triples the `U4` stack per abstract step, so only six of your
abstract steps land in that horizon (the sixth at raw step 38,979,318,
`R2 2196`, next expected `Q 6808`). I haven't tested for the translated
cycler sink you mention; if you can say what the cycle looks like on the
tape I can check whether the record orbit enters it, since the arrival
words are all logged.

---

## Message 3 (thread reply under message 1, for anyone who wants to rebuild)

```
git clone https://github.com/Enan456/bbchallenge-proofs && cd bbchallenge-proofs
cd busy-beaver-core && lake build      # 119 jobs, prints axioms per closure (also builds on 4.35.0-rc4)
cd .. && python -m qgkit.bb6.gdm_cross d2 d3 d7 d27 --horizon 20000000 --md out.md
```

The 18 named closures are hand-built (`docs/submissions/cryptid-names.md`);
the other 97 are instances of one certified template generated by
`qgkit/bb6/rawstep_generator.py`, each with its own differential test. The
census of what did and didn't fit is `docs/results/2026-09-03-state-and-gaps.md`.

---

## Notes for the author (not for posting)

- Edit the disclosure line to whatever is exactly true for you. Precision
  there is the whole point of the line.
- Follow through on the wiki sections within the week you promised, or
  don't promise. Shawn reads those pages.
- If Tom answers message 2 with a cycle description, that check is a small
  Python job against the logged arrival words; do it the same day.
- Do not reply to Andrew's "white flag on cryptid" question. The post
  already sidesteps the word.
- The Big_numbers/Dennis/hipparcos exchange is the house style: post rules,
  get checked, fix within hours. Expect the same for your files and welcome
  it.
