"""The local interaction calculus as an abstract predictor, validated
fail-closed against raw emulation for both machines (mirror-normalized).

Episode from spawn-entry shape (l, holes, r):
- 2-hole, h2 <= r-4          : SPAWN         -> (h1, h2, r-2), r+1     [7 steps]
- 2-hole, h2 == r-1          : SPAWN-VARIANT -> (h1, r-2), r+1         [7 steps]
- h_top == r-3 (carried)     : TRAVERSE — walk statics top-down with
    crossings := 0; at static q (next lower static q' or edge):
      * if q - q' == 2 (adjacent pair): FUSE -> holes below q' kept,
        hole at q'+9? (observed h1+9 for pair (h1,h1+2)); return with
        right-end +2 and hole at r+1. terminal.
      * elif (r - q + crossings) odd: TERMINATE -> hole q+6; crossed
        holes already shifted; return; right-end +1. terminal.
      * else: CROSS -> hole q+4, crossings += 1, continue to next.
    If no statics left: EDGE business at l: a := (lowest crossed
    original q) - l  ... use a = h1 - l of the LAST crossed hole:
      * a odd:  l' = l-1, plant l'+6   * a even: l' = l-3, plant l'+9
    return; right-end +1."""
import sys
def predict(shape):
    l, hs, r = shape
    hs = list(hs)
    if hs and hs[-1] != r - 3:
        h2 = hs[-1]
        if h2 <= r - 4:
            return (l, tuple(hs + [r - 2]), r + 1), 'spawn'
        if h2 == r - 1 and (len(hs) < 2 or hs[-2] <= r - 4):
            return (l, tuple(hs[:-1] + [r - 2]), r + 1), 'spawn-variant'
        return None, f'degenerate(hs={hs},r={r})'
    if not hs:
        return None, 'no-holes'

    def exit_(out, plant, tag):
        if (r - plant) % 2 == 0:
            return (l2, tuple(sorted(out)), r + 1), tag
        return (l2, tuple(sorted(out + [r + 1])), r + 2), tag + '+hole'

    statics = hs[:-1][::-1]
    out = []
    crossings = 0
    l2 = l
    i = 0
    while i < len(statics):
        q = statics[i]
        qnext = statics[i + 1] if i + 1 < len(statics) else None
        if qnext is not None and q - qnext == 2:
            out += statics[i + 2:]
            return exit_(out + [qnext + 9], qnext + 9, 'fuse')
        if (r - q + crossings) % 2 == 1:
            out += statics[i + 1:]
            return exit_(out + [q + 6], q + 6, 'terminate')
        out.append(q + 4)
        crossings += 1
        i += 1
    lastq = statics[-1] if statics else None
    a = (lastq - l) if lastq is not None else 0
    if a % 2 == 1:
        l2 = l - 1
        return exit_(out + [l2 + 6], l2 + 6, 'edge-odd')
    l2 = l - 3
    return exit_(out + [l2 + 9], l2 + 9, 'edge-even')

