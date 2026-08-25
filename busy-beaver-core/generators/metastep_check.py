"""Exact python mirror of the Lean metaStep; validated against vpredict
from s0 for 2M episodes (which itself matched 1B raw steps)."""
import sys
sys.path.insert(0, '.')
from vpredict import predict


def meta_step(three, l, h1, h2, r):
    if three:
        if l <= h1 and h1 + 4 <= h2 and h2 + 6 <= r and \
                (r - h2) % 2 == 0 and (h2 - h1) % 2 == 0:
            return (False, l, h1 + 6, h2 + 4, r + 1)
        if l <= h1 and h2 == h1 + 2 and h2 + 7 <= r and \
                (r - h2) % 2 == 0:
            return (False, l, h1 + 9, r + 1, r + 2)
        return None
    if h2 == r - 1:
        if l <= h1 and h1 <= r - 4:
            return (False, l, h1, r - 2, r + 1)
        return None
    if h2 == r - 3:
        if (r - h1) % 2 == 1:
            if l <= h1 and h1 + 7 <= r:
                return (False, l, h1 + 6, r + 1, r + 2)
            return None
        if (h1 - l) % 2 == 1:
            if l + 3 <= h1 and h1 + 6 <= r:
                return (False, l - 1, l + 5, h1 + 4, r + 1)
            return None
        if l + 5 <= h1 and h1 + 6 <= r:
            return (False, l - 3, l + 6, h1 + 4, r + 1)
        return None
    if l <= h1 and h1 + 1 <= h2 and h2 <= r - 4:
        return (True, l, h1, h2, r + 1)
    return None


def to_shape(ms):
    three, l, h1, h2, r = ms
    if three:
        return (l, (h1, h2, r - 3), r)
    return (l, (h1, h2), r)


ms = (False, -8, -2, 12, 13)
vs = (-8, (-2, 12), 13)
for i in range(2_000_000):
    assert to_shape(ms) == vs, (i, ms, vs)
    nxt = meta_step(*ms)
    if nxt is None:
        print("META DIED at", i, ms)
        sys.exit(1)
    vout, rule = predict(vs)
    if vout is None:
        print("VPREDICT DIED at", i, vs, rule)
        sys.exit(1)
    assert to_shape(nxt) == vout, (i, ms, nxt, vout, rule)
    ms, vs = nxt, vout
print("metaStep == vpredict for 2,000,000 episodes; orbit alive; "
      f"final r-l = {ms[4] - ms[2] + (ms[2]-ms[1]) + (ms[1]-ms[2]) }")
print("final state:", ms[0], "l,h1,h2,r deltas ok")
