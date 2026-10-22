"""Cross-verification of the Google DeepMind `cryptids` BB(6) reductions
(arXiv:2610.22603, github.com/google-deepmind/cryptids) against this
repository's Lean conditional closures, on the four machines both sides
formalized independently:

    dossier-2   1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD
    dossier-3   1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE
    dossier-7   1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA
    dossier-27  1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA

Both abstract systems are replayed against ONE raw simulation of the
machine from the blank tape.  See `crosscheck.py`.
"""
