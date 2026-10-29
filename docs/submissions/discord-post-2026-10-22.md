# Discord post draft — bbchallenge server (2026-10-22, rev 3)

Context that shaped this revision (from the #bb6 thread, 2026-10-19..22):
Shawn Ligocki added wiki pages for all 11 DeepMind machines on 10-21 and
invited people to study their dynamics; Tom Zahavy (DeepMind) is in the
channel and posted a dossier-27 observation on 10-22; Shawn said the
community lacks a word for "characterized into a set of dynamic equations
(regardless of difficulty)"; Andrew Ducharme is pushing back on loose use of
"cryptid"; Dennis and slugbird end posts with AI-assistance disclosures.

Message 1 is now ~4,500 chars: send it as three consecutive messages split
at the paragraph breaks before "Here's why I care" and before "Three of the 11". Message 2 goes as a reply in Tom's thread, message 3 as a
thread reply under your own first message. 2,000-char limit per message.

---

## Message 1 (main post)

**I characterized 3 of the 11 DeepMind machines in Lean back in August. Repo is public now. Here's what it is and what it isn't.**

https://github.com/Enan456/bbchallenge-proofs

Shawn asked yesterday for people to dig into the 11 new machines, so this is
the moment. I started on BB(6) in July to get back into math and try some
odd approaches on a hard problem. Since then I've been reducing holdouts to
explicit executable orbit conjectures in Lean 4. 115 of them from mxdys's
1,094 list. I sat on it.

Why I sat on it. The bar I held myself to is cosmo's 2022 validation process
for deciders (discuss.bbchallenge.org/t/85): decide 10% of what's left, get
reproduced by someone else, carry a proof someone else validates. 115/1094
is 10.5%, so I clear the number. But these decide nothing. And "proof of
correctness" only means something if another person can follow *why* the
machine does what it does. Straight up: I can explain about a third of what
my pipeline found, and that's me being generous with myself. I think that's
the honest state of every automated characterization right now, the paper's
included. The bar should go up as the certification step gets cheaper, not
down.

Here's why I care about that here specifically. BB is popular because it's
the cheapest place where a concrete finite object hits undecidability, and
deciders are how this community actually moved on it. A decider is an
argument: a class of machines, a reason they can't halt, a proof the reason
is sound, a person who can check it. That's what the 2022 rules are asking
for. A pipeline-found reduction is a different thing. It says: the machine
followed these rules as long as we watched, and the kernel agrees the rules
match the transition table. The rules can be exactly right and still carry
zero reason the orbit avoids the fatal set, which is the only question that
matters. Without that reason it's symbolic induction with a type checker
bolted on. The pattern held, so we certified the pattern. My mirror pair is
the clean example: 10^9 raw steps, 10^6 renewals, margin of 4 from death
the whole way, every rule proven for all block values, and not one sentence
that says why the margin never closes. I automated that step too, I'm not
knocking it. I'm saying the value is moving to the explanation and the
standards should follow it.

So treat what follows as a reference artifact and a cross-check. Not
understanding.

Three of the 11 are machines I already had:
- `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD` and its mirror
  `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE` (closed 2026-08-25)
- `1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA` (2026-09-03)
- and `1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA` from their Oct 20 batch
  (2026-09-04)

Shawn's phrase is the right one: "characterized into a set of dynamic
equations." Not cryptids, not hardness claims. Each is a theorem
`Safe_X → ¬RawHalts blankStart`. `Safe_X` is a fail-closed executable orbit
(five integers for the mirror pair, `(state, word)` records for the
left-growers). Halt localization, every episode transition for all block
values, and the transport to the raw tape are proven. The assumption is the
open problem. All 115 build with `lake build`, axioms propext/Quot.sound, no
sorry, no Mathlib. Parser parity against the standard format and a
bisimulation with the Coq-BB5 zipper tape are in there so the formal object
is provably your machine and not my transcription of it. Nothing is decided.

Cross-check, done today: I ported DeepMind's `start/encode/next` for those
four straight from their Lean and replayed their acceleration and my orbit
against one raw simulation per machine, 2×10^7 steps each, 10^8 for the
fourth. All four agree with the machine and with each other. Neither
fail-closed system dies. Their reductions hold. Report and harness:
`docs/results/2026-10-22-gdm-cross-verification.md`.

On validation horizons, since the Lean on both sides is horizon-free and
the horizon only matters for the conjecture: the paper's rules come from a
5×10^6-step detection pass and 128k-step checks per synthetic transition,
and it reports no longer run. The mirror pair's orbit conjecture here was
validated against 10^9 raw steps per machine and 10^8 iterations of the
renewal map (about 10^15 raw steps equivalent), minimum margin 4 from the
fatal set throughout; the left-growers against 2×10^7 raw steps with every
record transition exact. That's more validation behind the same open
conjecture, not more understanding of it, and mxdys's 10^13 sweep of every
holdout is the real yardstick for both of us. Two things for
@Marco / @tomzahavy: (1) the fourth machine's docstring says `S6 1` at step
66. It's 169. 66 is your `step_drain_odd_end` lemma. Proof unaffected.
(2) `next` isn't a first-return map. On the mirror's second machine the
trace passes 2,317 other canonical configs before the stated successor.
Fine under `IsValidAcceleration`, but say so in the rule tables.

I'll add a formalization section to each of the three wiki pages this week
unless someone objects. Your `IsHalt ↔ CollatzHalts` is stronger than my
one-way statement; a Lean bridge from my orbit conjecture to your
`CollatzHalts` is in progress. What I actually want from this channel is the
part neither pipeline produced: someone who can see why these counter maps
avoid their fatal set. The mirror pair's map has no congruence invariant to
mod 384 and no rotation rigidity, proven. That's as far as I got. I'd rather
hear that explained than stack another certified reduction on the pile.

AI assistance disclosure: the Lean proofs, the harness and this post were
produced with Claude (Anthropic) and Codex (OpenAI). I ran every build and
check myself. The framing is mine, including its gaps.

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
