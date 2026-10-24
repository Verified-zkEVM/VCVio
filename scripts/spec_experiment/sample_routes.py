#!/usr/bin/env python3
"""Seeded stratified sample of routed declarations for the spec-library experiment.

Frame: rows of `.lake/route-census.csv` whose route is a program-logic family, outside the
Foxglove modules (program algebra and Foxglove's own logic are not sampled and count as zero
saving). Strata: family x length bucket. Mid-length (6-60 lines) strata are sampled without
replacement, with a fixed allocation; the long stratum (> 60 lines) is sampled with probability
proportional to size (systematic PPS over a seeded random order), with first-order inclusion
probabilities for Horvitz-Thompson weights; short proofs (<= 5 lines, about 1% of lines) are not
sampled.

Usage: sample_routes.py SEED OUT.csv [--exclude prior.csv ...] [--mid fam=n ...] [--long n]
"""
import csv, random, sys, re, os, argparse

FAM = {'upper': 'upper', 'relational': 'relational', 'necessary': 'necessary',
       'possible': 'necessary', 'handler': 'handler', 'queryBound': 'queryBound',
       'lowerUpper': 'lowerUpper', 'upToBad': 'lowerUpper', 'lower': 'lowerUpper',
       'core:lower': 'lowerUpper'}

def bucket(n):
    return 'short' if n <= 5 else ('long' if n > 60 else 'mid')

def locate(module, decl):
    """File and 1-based line of the declaration's header."""
    path = module.replace('.', '/') + '.lean'
    short = decl.split('.')[-1]
    if not os.path.exists(path):
        return path, None
    pat = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable )*'
                     r'(?:theorem|lemma)\s+(?:[\w.]*\.)?' + re.escape(short) + r'\b')
    for i, line in enumerate(open(path, encoding='utf-8'), 1):
        if pat.match(line):
            return path, i
    return path, None

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('seed', type=int)
    ap.add_argument('out')
    ap.add_argument('--census', default='.lake/route-census.csv')
    ap.add_argument('--exclude', nargs='*', default=[])
    ap.add_argument('--mid', nargs='*', default=['necessary=3', 'relational=3', 'queryBound=2',
                                                  'handler=2', 'lowerUpper=2', 'upper=2'])
    ap.add_argument('--long', type=int, default=6)
    a = ap.parse_args()
    rows = list(csv.DictReader(open(a.census)))
    excluded = set()
    for f in a.exclude:
        excluded |= {r['decl'] for r in csv.DictReader(open(f))}
    frame = [r for r in rows if r['route'] in FAM
             and not r['module'].startswith(('Foxglove', 'VCVioFoxglove'))]
    for r in frame:
        r['family'] = FAM[r['route']]
        r['bucket'] = bucket(int(r['lines']))
    rng = random.Random(a.seed)
    out = []
    # stratum totals over the whole frame (for weights), before exclusions
    tot = {}
    for r in frame:
        k = (r['family'], r['bucket'])
        d, l = tot.get(k, (0, 0))
        tot[k] = (d + 1, l + int(r['lines']))
    avail = [r for r in frame if r['decl'] not in excluded]
    for spec in a.mid:
        fam, n = spec.split('=')
        pool = sorted([r for r in avail if r['family'] == fam and r['bucket'] == 'mid'],
                      key=lambda r: r['decl'])
        pick = rng.sample(pool, min(int(n), len(pool)))
        for r in pick:
            out.append(dict(r, stratum=f'{fam}/mid', weight=len(pool) / len(pick),
                            incl=len(pick) / len(pool)))
    longpool = sorted([r for r in avail if r['bucket'] == 'long'], key=lambda r: r['decl'])
    rng.shuffle(longpool)
    L = sum(int(r['lines']) for r in longpool)
    n = a.long
    step = L / n
    start = rng.uniform(0, step)
    marks = [start + i * step for i in range(n)]
    acc, j, picked = 0, 0, []
    for r in longpool:
        lo, acc = acc, acc + int(r['lines'])
        while j < n and lo <= marks[j] < acc:
            if r not in picked:
                picked.append(r)
            j += 1
    for r in picked:
        incl = min(1.0, n * int(r['lines']) / L)
        out.append(dict(r, stratum='long', weight=1 / incl, incl=incl))
    with open(a.out, 'w', newline='') as f:
        cols = ['id', 'decl', 'module', 'file', 'line', 'route', 'family', 'stratum', 'lines',
                'incl', 'weight']
        w = csv.DictWriter(f, fieldnames=cols)
        w.writeheader()
        for i, r in enumerate(out):
            path, line = locate(r['module'], r['decl'])
            w.writerow({'id': f'S{a.seed % 1000:03d}_{i:02d}', 'decl': r['decl'], 'module': r['module'],
                        'file': path, 'line': line, 'route': r['route'], 'family': r['family'],
                        'stratum': r['stratum'], 'lines': r['lines'], 'incl': f"{r['incl']:.4f}",
                        'weight': f"{r['weight']:.3f}"})
    print(f'{len(out)} draws -> {a.out}')

if __name__ == '__main__':
    main()
