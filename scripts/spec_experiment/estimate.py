#!/usr/bin/env python3
"""Estimate the routed-line saving of each arm from the measured sample.

Saving of a declaration under an arm: original normalized lines minus the arm's, if the arm's
last record compiles and passes the heartbeat gate (heartbeats <= 1.5x the original's, or
lines <= 0.6x and heartbeats <= 5x); otherwise the arm falls back (B to the better of A and O,
A to O), saving 0 in the worst case.

Estimator: within each mid-length stratum, a ratio (sum of savings / sum of census lines of the
sampled declarations) times the stratum's census lines; the long stratum the same with
Horvitz-Thompson weights; short proofs (<= 5 lines) count as no saving. The result is a share of
the frame's census lines (and of all routed lines, counting unsampled routes as no saving).
Confidence intervals: stratified bootstrap (resampling declarations within strata), paired
across arms.

Usage: estimate.py [--sample pilot.csv,main.csv] [--arms A,B] [--library-lines N]
"""
import argparse, collections, csv, json, os, random

HERE = os.path.dirname(os.path.abspath(__file__))
FAM = {'upper': 'upper', 'relational': 'relational', 'necessary': 'necessary',
       'possible': 'necessary', 'handler': 'handler', 'queryBound': 'queryBound',
       'lowerUpper': 'lowerUpper', 'upToBad': 'lowerUpper', 'lower': 'lowerUpper',
       'core:lower': 'lowerUpper'}
ROUTED_LINES = 30000  # census: all routed declarations (incl. program algebra, Foxglove)

def bucket(n):
    return 'short' if n <= 5 else ('long' if n > 60 else 'mid')

def frame_totals(census):
    tot = collections.Counter()
    for r in csv.DictReader(open(census)):
        if r['route'] in FAM and not r['module'].startswith(('Foxglove', 'VCVioFoxglove')):
            b = bucket(int(r['lines']))
            key = 'long' if b == 'long' else f"{FAM[r['route']]}/{b}"
            tot[key] += int(r['lines'])
    return tot

def gate(o, x):
    if not x or not x['ok'] or x['heartbeats'] is None or o['heartbeats'] is None:
        return False
    hb, ln = x['heartbeats'], x['lines']
    return hb <= 1.5 * max(o['heartbeats'], 1) or (ln <= 0.6 * o['lines'] and
                                                   hb <= 5 * max(o['heartbeats'], 1))

def savings(recs, arms):
    """id -> {arm: saved lines} (with fallbacks)."""
    out = {}
    for i, by in recs.items():
        o = by.get('O')
        if not o or not o['ok']:
            continue
        s = {'O': 0}
        for arm in arms:
            x = by.get(arm)
            v = o['lines'] - x['lines'] if gate(o, x) else None
            fallback = max([s[a] for a in s if a != arm] + [0]) if arm != 'A' else 0
            s[arm] = max(v, fallback) if v is not None else fallback
        out[i] = s
    return out

def estimate(rows, sav, tot, arm):
    by = collections.defaultdict(list)
    for r in rows:
        if r['id'] in sav:
            by[r['stratum']].append(r)
    saved = 0.0
    for st, rs in by.items():
        if st == 'long':
            num = sum(sav[r['id']][arm] / float(r['incl']) for r in rs)
            den = sum(int(r['lines']) / float(r['incl']) for r in rs)
        else:
            num = sum(sav[r['id']][arm] for r in rs)
            den = sum(int(r['lines']) for r in rs)
        saved += (num / den) * tot[st] if den else 0
    return saved

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--sample', default=os.path.join(HERE, 'pilot.csv'))
    ap.add_argument('--arms', default='A,B')
    ap.add_argument('--census', default='.lake/route-census.csv')
    ap.add_argument('--library-lines', type=int, default=0)
    ap.add_argument('--reps', type=int, default=10000)
    ap.add_argument('--results', default=os.path.join(HERE, 'results.jsonl'))
    a = ap.parse_args()
    arms = a.arms.split(',')
    rows = [r for f in a.sample.split(',') for r in csv.DictReader(open(f))]
    recs = collections.defaultdict(dict)
    for l in open(a.results):
        x = json.loads(l)
        recs[x['id']][x['arm']] = x  # last record wins
    tot = frame_totals(a.census)
    frame = sum(tot.values())
    sav = savings(recs, arms)
    measured = [r for r in rows if r['id'] in sav and all(arm in recs[r['id']] for arm in arms)]
    print(f'frame {frame} census lines; {len(measured)}/{len(rows)} sampled declarations '
          f'measured in all arms {arms}')
    print(f"{'id':9} {'stratum':16} {'O':>5} " + ' '.join(f'{arm:>9}' for arm in arms))
    for r in measured:
        o = recs[r['id']]['O']
        cells = []
        for arm in arms:
            x = recs[r['id']].get(arm)
            mark = '' if gate(o, x) else '*'
            cells.append(f"{x['lines'] if x else '-':>4}/{sav[r['id']][arm]:<3}{mark}")
        print(f"{r['id']:9} {r['stratum']:16} {o['lines']:>5} " + ' '.join(f'{c:>9}' for c in cells))
    point = {arm: estimate(measured, sav, tot, arm) for arm in arms}
    rng = random.Random(1)
    strata = collections.defaultdict(list)
    for r in measured:
        strata[r['stratum']].append(r)
    boots = {arm: [] for arm in arms}
    delta = []
    for _ in range(a.reps):
        res = [rng.choice(rs) for rs in strata.values() for _ in rs]
        e = {arm: estimate(res, sav, tot, arm) for arm in arms}
        for arm in arms:
            boots[arm].append(e[arm])
        if len(arms) > 1:
            delta.append(e[arms[-1]] - e[arms[0]])
    def ci(xs):
        xs = sorted(xs)
        return xs[int(0.05 * len(xs))], xs[int(0.95 * len(xs)) - 1]
    for arm in arms:
        lo, hi = ci(boots[arm])
        print(f'arm {arm}: saved {point[arm]:.0f} lines = {100 * point[arm] / frame:.1f}% of frame '
              f'(90% CI {100 * lo / frame:.1f}-{100 * hi / frame:.1f}); '
              f'{100 * point[arm] / ROUTED_LINES:.1f}% of all routed lines')
    if len(arms) > 1:
        lo, hi = ci(delta)
        d = point[arms[-1]] - point[arms[0]]
        print(f'increment {arms[-1]}-{arms[0]}: {100 * d / frame:+.1f} pts of frame '
              f'(90% CI {100 * lo / frame:+.1f} to {100 * hi / frame:+.1f})')
    if a.library_lines:
        last = arms[-1]
        net = point[last] - a.library_lines
        lo, _ = ci(boots[last])
        print(f'net of {a.library_lines} library lines: {100 * net / frame:.1f}% of frame '
              f'(90% lower bound {100 * (lo - a.library_lines) / frame:.1f}%)')
    per = collections.defaultdict(lambda: collections.Counter())
    for r in measured:
        for arm in arms:
            per[r['family']][arm] += sav[r['id']][arm]
        per[r['family']]['C'] += int(r['lines'])
    print('per family (sampled lines saved / census lines): ' + '; '.join(
        f"{f} " + ' '.join(f"{arm} {100 * c[arm] / c['C']:.0f}%" for arm in arms)
        for f, c in sorted(per.items())))

if __name__ == '__main__':
    main()
