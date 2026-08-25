"""Mirror plans_d2 into D3 plans: flip position arithmetic, reverse
inequalities, swap holeTape range sides, reverse atomgen cell orders."""
import re


def flip_expr(e):
    """Swap + and - in a position expression."""
    return e.replace('+', '\x01').replace('-', '+').replace('\x01', '-')


def flip_guard(g):
    if '≤' in g:
        a, b = g.split('≤')
        return f"{flip_expr(b).strip()} ≤ {flip_expr(a).strip()}"
    if '=' in g:
        a, b = g.split('=', 1)
        return f"{flip_expr(a).strip()} = {flip_expr(b).strip()}"
    raise ValueError(g)


def mirror_shape(shape):
    low, high, holes = shape
    # D2: (l-side low, r-side high). D3: low = spawn side, high = far l.
    return (flip_expr(high), flip_expr(low),
            [flip_expr(h) for h in holes])


def mirror_seg(seg, atom_reverse):
    m = dict(seg)
    k = seg['kind']
    if k == 'catrun':
        m['front'] = flip_expr(seg['front'])
        m['out_holes'] = [flip_expr(h) for h in seg['out_holes']]
        if 'out_r' in m:
            # D2 catrun extended the HIGH side (r-1 -> r); mirror: LOW
            m['out_low'] = flip_expr(m.pop('out_r'))
    elif k == 'atom':
        m['out_holes'] = [flip_expr(h) for h in seg['out_holes']]
        m['writes'] = [(flip_expr(p), v) for p, v in seg['writes']]
        m['write_fates'] = {flip_expr(p): f
                            for p, f in seg['write_fates'].items()}
        m['end_head'] = flip_expr(seg['end_head'])
        if seg.get('end_state') == 'D':
            m['end_state'] = 'E'
        if seg.get('end_off_raw'):
            m['end_off_raw'] = flip_expr(seg['end_off_raw'])
        if seg['name'] != 'spawn_step' and atom_reverse:
            m['cells'] = list(reversed(seg['cells']))
        if 'out_r' in m:
            m['out_low'] = flip_expr(m.pop('out_r'))
        if 'out_l' in m:
            m['out_high'] = flip_expr(m.pop('out_l'))
    elif k == 'fstep':
        m['end_head'] = flip_expr(seg['end_head'])
    elif k == 'sweep':
        m['end_head'] = flip_expr(seg['end_head'])
    return m


def mirror_plan(pl):
    return dict(
        name=pl['name'],
        doc=pl['doc'] + "  (Mirror.)",
        guards=[(n, flip_guard(g)) for n, g in pl['guards']],
        in_shape=mirror_shape(pl['in_shape']),
        segments=[mirror_seg(s, True) for s in pl['segments']],
        out_head=flip_expr(pl['out_head']),
        steps=pl['steps'],
        out_shape=mirror_shape(pl['out_shape']),
        nat_vars=pl['nat_vars'])
