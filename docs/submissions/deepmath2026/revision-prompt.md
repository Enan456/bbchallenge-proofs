# Revision prompt: DeepMath 2026 submission, v9 style pass

Constructed from the version history (v1 draft; v4 "academic voice";
v5 "way more grounded, simple to mathematicians outside this space,
match the organizers' register"; v7 "more lower-level concepts";
v8 census and classifications) and the standing author directives:
written academically, no em dashes, no filler text.

## Voice

- First-person plural, declarative. We state what we did, what we
  proved, and what we measured, in that order of strength.
- Every claim is tagged by its evidence class in the sentence itself:
  "checked by the Lean kernel", "verified against N raw steps",
  "measured over horizon H", "conjectured". No claim floats free.
- The reader is a working mathematician outside the busy beaver
  subfield. Every term is defined before use; no term is defined
  twice.

## Tone

- Grounded and non-promotional. No hype adjectives (striking,
  beautiful, remarkable, powerful), no editorial asides, no
  rhetorical questions.
- Negative and limiting results are stated with the same directness
  as positive ones.
- Honest-scope statements are content, not disclaimers; they stay.

## Syntax

- No em dashes. Restructure each occurrence into a period, colon,
  comma, parenthesis, or a new sentence. (LaTeX "---" in machine
  transition codes is data, not punctuation; untouched.)
- One idea per sentence; target under 30 words; split rather than
  subordinate twice.
- No filler: banned phrases include "it is useful to", "worth
  recording", "in its own right", "of course", "clearly", "note
  that", "interestingly", sentence-initial "So," and "Now,".
- Numbers carry their horizon or unit at first mention.
- Parallel structure in lists and tables; tables for enumerable
  facts, prose for mechanisms.

## Structure (unchanged from v8)

Problem from zero; method (watch, compress, certify); result;
census and classifications; verification spectrum; relevance.
The title, author, theorems, numbers, figures, and citations are
fixed content. This is a style pass: rewrite sentences, do not
change claims, and do not add or remove evidence.
