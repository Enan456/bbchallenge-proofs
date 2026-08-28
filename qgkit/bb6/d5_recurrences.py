"""Dossier-5 opener: the golden-ratio generalization.

Fit small integer linear recurrences to each machine's backward-cone
counts L(k). Dossier-3's tree satisfies L(k)=L(k-1)+L(k-2) (phi).
Question: does each machine own an algebraic constant?"""
import sys, json
sys.path.insert(0, '.')
from cone_sweep import parse, cone
from itertools import product


def fit_recurrence(seq, max_order=4, max_coef=2, skip=4):
    """Find smallest integer recurrence L(k)=sum c_i L(k-i) matching
    seq[skip:] exactly."""
    s = seq[skip:]
    for order in range(2, max_order + 1):
        if len(s) < order + 4:
            break
        for coefs in product(range(-max_coef, max_coef + 1),
                             repeat=order):
            if coefs[-1] == 0:
                continue
            ok = all(
                s[i] == sum(coefs[j] * s[i - 1 - j]
                            for j in range(order))
                for i in range(order, len(s)))
            if ok:
                return order, coefs
    return None, None


def char_root(coefs):
    """Largest real root of x^n = c1 x^{n-1} + ... + cn."""
    n = len(coefs)
    lo_, hi_ = 0.0, 4.0
    f = lambda x: x ** n - sum(coefs[j] * x ** (n - 1 - j)
                               for j in range(n))
    for _ in range(200):
        mid = (lo_ + hi_) / 2
        if f(mid) > 0:
            hi_ = mid
        else:
            lo_ = mid
    return (lo_ + hi_) / 2


NAMED = {1.6180: 'GOLDEN RATIO phi', 1.4656: 'supergolden (x^3=x^2+1)',
         1.3247: 'plastic number', 1.4142: 'sqrt(2)',
         1.8393: 'tribonacci', 1.7549: 'x^3=x^2+x-... ',
         2.0000: '2'}


def near(x):
    for v, n in NAMED.items():
        if abs(x - v) < 0.004:
            return n
    return ''


MACHS = json.load(open('/tmp/cert_exact.json')) + [
    '1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE',   # dossier-3
    '1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD',   # dossier-2
    '1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA',   # antihydra
    '1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB',   # dossier-1
]
print(f"{'machine':<44} {'recurrence':<22} {'root':>7}  named")
for code in MACHS:
    tbl, halts = parse(code)
    counts, _ = cone(tbl, halts, 26)
    order, coefs = fit_recurrence(counts, skip=6)
    if coefs:
        rec = "L=" + "+".join(f"{c}L{-i-1}" for i, c in
                              enumerate(coefs) if c) \
            .replace("+-", "-").replace("1L", "L")
        root = char_root(coefs)
        print(f"{code:<44} {rec:<22} {root:>7.4f}  {near(root)}")
    else:
        # report empirical ratio instead
        r = (counts[-1] / counts[-6]) ** 0.2 if counts[-6] else 0
        print(f"{code:<44} {'(no exact recurrence)':<22} "
              f"{r:>7.4f}  {near(r)}")
