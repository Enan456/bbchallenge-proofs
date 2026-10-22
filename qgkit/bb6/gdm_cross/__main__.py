"""CLI:  python -m qgkit.bb6.gdm_cross [d2 d3 d7 d27] [--horizon N] [--json out.json] [--md out.md]"""
import argparse
import json
import sys

from .crosscheck import markdown, run, verdict


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument('machines', nargs='*', default=['d2', 'd3', 'd7', 'd27'])
    ap.add_argument('--horizon', type=int, default=20_000_000)
    ap.add_argument('--json')
    ap.add_argument('--md')
    ap.add_argument('--progress', type=int, default=2_000_000)
    a = ap.parse_args(argv)
    results = []
    for key in a.machines:
        print(f'== {key}: horizon {a.horizon:,}', flush=True)
        r = run(key, a.horizon, progress=a.progress)
        results.append(r)
        probs = verdict(r)
        print(f'   {"PASS" if not probs else "FAIL " + str(probs)}  '
              f'gdm hits={r["gdm"]["hits"]:,} ours={r["ours"]}', flush=True)
    if a.json:
        with open(a.json, 'w') as f:
            json.dump(results, f, indent=1)
    if a.md:
        with open(a.md, 'w') as f:
            f.write('\n'.join(markdown(r) for r in results))
    return 0 if all(not verdict(r) for r in results) else 1


if __name__ == '__main__':
    sys.exit(main())
