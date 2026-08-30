# Pre-submission audit, v10 (simulated reviewers and organizers)

## Reviewer 1 (dynamics / number theory)

- Theorem-versus-computation separation: clean. The one theorem is
  stated with its axioms; everything empirical carries a horizon.
- The renewal map display omitted the case $b = \beta$. FIXED: a
  caveat now states the case never occurs on the verified orbit,
  against which the map is checked transition by transition.
- Factor-complexity and residue-search claims name their bounds
  (modulus 384, $1.6^n$ versus $n+1$); acceptable as computational
  evidence, correctly not claimed as theorems.
- The horoball restatement cites Series; a specialist may want the
  explicit matrix moves. Judged acceptable for an extended abstract.

## Reviewer 2 (mathematics of deep learning)

- The representation-learning kinship is stated as a method
  parallel, not an application claim; correct register for this
  venue.
- "Fail-closed" is defined at first use (Certify paragraph).
- Figures: raw versus transformed views support the coordinate-choice
  argument; captions are self-contained.
- The abstract is one long paragraph, at the upper end of length but
  within norms for extended abstracts.

## Reviewer 3 (formal verification)

- Axiom footprint is stated three times consistently
  ({propext, Quot.sound}); the AI-assistance disclosure is explicit
  in the acknowledgments; the trust surface (kernel plus two axioms,
  generators excluded) is stated.
- External checkability: the Palomar entry gives a pinned-commit
  channel; the bibliography annotation says so.

## Organizers (format and policy)

- No em dashes; no filler phrases; claims hedged only where
  empirical. Verified by mechanical sweep.
- Direct quotes in the bibliography are verbatim from retrieved
  sources; two entries (Kůrka, Series) carry no quote because the
  publisher pages are access-controlled, and nothing was fabricated.
- Title's "Solve" is aspirational; the form-fields note offers an
  alternate title if the chairs prefer.
- AI-assistance disclosure present; email-sharing and data-release
  checkboxes prepared in form-fields.md.

## Verdict

Ready to submit as v10. Remaining risks are judgment calls, not
defects: the aspirational title, the single-paragraph abstract, and
the unusual (but attributed) annotated bibliography.
