# BB(6) new cryptid-candidate mining pass

**Date:** 2026-07-27  
**Script:** `experiments/stage655_new_cryptid_miner.py`  
**Input:** `experiments/outputs/BB6_holdouts_1094.txt`

## Result

The miner scanned all 1094 available BB(6) holdouts and produced 145 compact-growth
candidates. After excluding exact machine codes already visible on the BusyBeaverWiki
Cryptids registry, the strongest new candidate was:

```text
1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB
```

Exact-code web/wiki searches for this machine and distinctive substrings returned no
indexed BusyBeaverWiki hit on 2026-07-27. This is therefore a **new candidate found by
the local miner**, not a confirmed new named cryptid.

## Evidence

Bounded simulation:

- No halt through 200,000,000 raw simulation steps in the focused check.
- The machine repeatedly collapses to a one-block checkpoint.
- After startup, frontier records stabilize to two `1`-blocks.
- Dominant two-block transfer rule observed at frontier records:

```text
(a, b) -> (a + 4, b - 3)
```

with support `294/312 = 0.942` in the initial mining pass.

Single-block checkpoint values observed through the 200M-step focused run:

```text
1, 1, 3, 4, 7, 8, 13, 14, 21, 22, 31, 32, 45, 46,
63, 64, 87, 88, 119, 120, 136, 137, 185, 186, 210, 211,
283, 284, 381, 382, 511, 512, 685, 686, 917, 918, 934, 935,
1249, 1250, 1669, 1670, 2229, 2230, 2975, 2976, 3310, 3311,
4417, 4418, 5893, 5894, 7861, 7862
```

The adjacent-pair pattern `n, n+1` plus irregular jumps is consistent with a
generalized-Collatz style map, but the exact macro-rule has not yet been proven.

Local decider chain check:

```text
classify(... budget=200000, cycle=200000, backward_depth=800,
         bouncer_steps=200000, ctl_radius=7, far_dfa_states=10)
-> UNDECIDED / cryptid_candidate / none_fired
```

## Honest scope

This does **not** decide the machine and does **not** prove it is a cryptid. The next
step is to derive a configuration-level macro system for the one-block checkpoint
map and verify whether the halting condition corresponds to a hard avoid-set, as in
Space Needle.

