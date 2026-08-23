# stage757 — orbit-finder sweep (stage753 queue)

4/9 machines admit a fail-closed exact orbit spec at 150k-step budget.
EXACT machines are OrbitPredictor-ready and candidates for flying-dragon
localization proofs; REJECTED means no exact affine record spec at this
budget/signature (not a negative result about the machine).

- EXACT    `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA` trans=539 rules=16 top=495
- EXACT    `1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB` trans=296 rules=30 top=184
- EXACT    `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD` trans=379 rules=17 top=156
- EXACT    `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE` trans=366 rules=15 top=151
- REJECTED `1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA` trans=375
- REJECTED `1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA` trans=54
- REJECTED `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE` trans=249
- REJECTED `1RB1RA_1RC1LB_0LD0RA_1RA1LE_---1LF_1LC0LF` trans=53
- REJECTED `1RB1RA_1RC1LE_1RD1LC_0LB0RA_---1LF_1LD0LF` trans=75

Honest scope: bounded empirical structure over observed records; only the Lean layer turns specs into theorems.
