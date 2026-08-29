"""Re-probe the 14 top-25 rejects with 10x OrbitFinder budget
(1.5M steps, cap 20k) -- were the rejections budget-limited?"""
import sys
sys.path.insert(0, '/Users/enan/Documents/bbchallenge-proofs')
from qgkit.bb6.dragon.finder import OrbitFinder

REJECTS = [
 '1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---',
 '1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---',
 '1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---',
 '1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD',
 '1RB0RC_1LC1LA_1RD0LB_1RE1RC_1RA0RF_1RC---',
 '1RB0LE_1RC1RA_1RD0RF_1RE0RA_1LA1LD_1RA---',
 '1RB0RF_1RC0RD_1LD1LB_1RE0LC_1RA1RD_1RD---',
 '1RB1RE_1LC0RA_1LD1LB_1LE0LF_1LA0LB_1LB---',
 '1RB1RF_1RC1RB_1LD0RA_1LA1LE_---0LF_0LC1LF',
 '1RB1RF_1RC0RB_0RD1LF_1LE1RE_1LA---_1RA0LC',
 '1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC---',
 '1RB1LB_1RC---_1LD1LF_1LE0LD_0LA1RF_1LC0RE',
 '1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF',
 '1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB',
]
for code in REJECTS:
    try:
        spec = OrbitFinder(code, steps=1_500_000, cap=20_000).fit()
    except Exception as e:
        print(f"ERROR     {code}  {type(e).__name__}: {str(e)[:80]}",
              flush=True)
        continue
    if spec is None:
        print(f"REJECTED  {code}", flush=True)
    else:
        sup = max(r['support'] for r in spec['rules'].values())
        print(f"EXACT     {code}  rules={spec['n_rules']} "
              f"transitions={spec['n_transitions']} top_support={sup}",
              flush=True)
