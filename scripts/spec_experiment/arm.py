#!/usr/bin/env python3
"""Measure one arm of one sampled declaration, in place.

An arm is a re-proof of a sampled declaration. It lives in `arms/<ID>/<ARM>.lean`:
an optional first line `-- imports: Mod.A Mod.B` (extra imports), then any helper declarations
written for this proof, then the main declaration, starting at the same header line as the
original (`theorem name ...`). Arm `O` is the original and needs no file.

The arm is spliced into a copy of the original source file in place of the original declaration
(so private helpers, section variables and notation are in scope), with `count_heartbeats in`
before the main declaration and a usage report after it, and compiled with `lake env lean`.

Checks: the main statement (text up to the proof's `:=`) is the original's, up to whitespace.
Counts: non-blank, non-comment lines and tokens of helpers plus main declaration (the docstring
and attributes of the original are kept and not counted).

Usage: arm.py ID ARM [--sample pilot.csv] [--keep]   (run from the repository root)
Appends a JSON record to scripts/spec_experiment/results.jsonl and prints it.
"""
import argparse, csv, json, os, re, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
SCRATCH = os.environ.get('SPEC_EXP_BUILD', os.path.join(HERE, '..', '..', '.lake', 'spec-exp'))
LIB_PREFIX = 'VCVio.ProgramLogic.Library'

HEADER = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable )*'
                    r'(?:theorem|lemma)\s+(?:[\w.]*\.)?(?P<name>[^\s({\[:]+)')

def strip_comments(text):
    """Remove block comments (nested, incl. docstrings) and line comments."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth and text.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth:
            if text[i] == '\n':
                out.append('\n')
            i += 1; continue
        if text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
            continue
        out.append(text[i]); i += 1
    return ''.join(out)

def measure(text):
    body = strip_comments(text)
    lines = [l for l in body.split('\n') if l.strip()]
    toks = re.findall(r"[\w'.₀-₉ᵢ]+|[^\s\w]", body)
    return len(lines), len(toks)

def decl_span(src, header_line):
    """(preamble_start, header, end) as 0-based line indices; end is exclusive."""
    h = header_line - 1
    p = h
    while p > 0:
        prev = src[p - 1]
        if prev.startswith('@['):
            p -= 1; continue
        if prev.rstrip().endswith('-/'):
            q = p - 1
            while q >= 0 and not src[q].lstrip().startswith('/--'):
                q -= 1
            if q >= 0:
                p = q; continue
        break
    e = h + 1
    while e < len(src):
        l = src[e]
        if l and not l[0].isspace() and not l.startswith(('|', ')', ']', '}', '⟩')):
            break
        e += 1
    while e > h + 1 and not src[e - 1].strip():
        e -= 1
    return p, h, e

def statement(text):
    """Header text up to the proof's top-level `:=`, whitespace-normalized."""
    s = strip_comments(text)
    depth, i = 0, 0
    while i < len(s):
        c = s[i]
        if c in '([{⟨⦃':
            depth += 1
        elif c in ')]}⟩⦄':
            depth -= 1
        elif depth == 0 and s.startswith(':=', i):
            return ' '.join(s[:i].split())
        i += 1
    return ' '.join(s.split())

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('id'); ap.add_argument('arm')
    ap.add_argument('--sample', default=os.path.join(HERE, 'pilot.csv'))
    ap.add_argument('--keep', action='store_true')
    ap.add_argument('--timeout', type=int, default=1800)
    a = ap.parse_args()
    row = next((r for f in a.sample.split(',') for r in csv.DictReader(open(f))
                if r['id'] == a.id), None)
    if row is None:
        sys.exit(f'unknown id {a.id}')
    src = open(row['file'], encoding='utf-8').read().split('\n')
    p, h, e = decl_span(src, int(row['line']))
    orig_main = '\n'.join(src[h:e])
    short = HEADER.match(src[h]).group('name').split('.')[-1]
    imports, inlines = [], []
    if a.arm == 'O':
        helpers, main_text = '', orig_main
    else:
        path = os.path.join(HERE, 'arms', a.id, a.arm + '.lean')
        lines = open(path, encoding='utf-8').read().rstrip('\n').split('\n')
        while lines and lines[0].startswith(('-- imports:', '-- inline:')):
            key, val = lines[0].split(':', 1)
            if key == '-- imports':
                imports += val.split()
            else:
                inlines += val.split()
            lines = lines[1:]
        k = next((i for i, l in enumerate(lines)
                  if (m := HEADER.match(l)) and m.group('name').split('.')[-1] == short), None)
        if k is None:
            sys.exit(f'{path}: no main declaration `{short}`')
        helpers, main_text = '\n'.join(lines[:k]), '\n'.join(lines[k:])
        if statement(main_text) != statement(orig_main):
            sys.exit(f'{path}: statement differs from the original\n  orig: '
                     f'{statement(orig_main)}\n  arm:  {statement(main_text)}')
    n_lines, n_toks = measure(helpers + '\n' + main_text)
    # usage report: library constants reachable from the main declaration through helpers
    report = f'''
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let n ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent `{short})
  let mut seen : NameSet := {{}}
  let mut todo := #[n]
  let mut lib : Array Name := #[]
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let mod := (env.getModuleIdxFor? c).map (env.header.moduleNames[·]!)
    if mod.any (fun m => (`{LIB_PREFIX}).isPrefixOf m) then
      lib := lib.push c
    else if mod.isNone then
      for d in ci.getUsedConstantsAsSet do todo := todo.push d
  logInfo m!"@usage {{lib.qsort Name.lt}}"
'''
    out = src[:p]
    n_inl = 0
    for f in inlines:
        # library text (not counted): a library module's body after its imports, as a section
        body = open(f, encoding='utf-8').read().split('\n')
        k = max(i for i, l in enumerate(body) if re.match(r'^(public )?(meta )?import ', l))
        body = [l for l in body[k + 1:] if l.strip() not in ('public section', '@[expose] public section')]
        out += ['section'] + body + ['end']
        n_inl += len(body) + 2
    if helpers:
        out += helpers.split('\n')
    out += ['#count_heartbeats in'] + src[p:h] + main_text.split('\n') + report.split('\n') + src[e:]
    # imports: after the last import line; add the meta import the report needs
    last = max(i for i, l in enumerate(out[:p + 50]) if re.match(r'^(public )?(meta )?import ', l))
    extra = [f'public import {m}' for m in imports] + ['import Mathlib.Util.CountHeartbeats',
                                                       'meta import Lean.Elab.Command']
    out = out[:last + 1] + extra + out[last + 1:]
    os.makedirs(SCRATCH, exist_ok=True)
    lo = p + len(extra) + 1 + n_inl
    hi = lo + len(helpers.split('\n')) * bool(helpers) + 1 + (h - p) + len(main_text.split('\n'))
    copy = os.path.join(SCRATCH, f'{a.id}_{a.arm}.lean')
    open(copy, 'w', encoding='utf-8').write('\n'.join(out))
    t0 = time.time()
    try:
        r = subprocess.run(['lake', 'env', 'lean', copy], capture_output=True, text=True,
                           timeout=a.timeout)
        log = r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        log = 'error: timeout'
    dt = time.time() - t0
    errs = [l for l in log.split('\n') if ': error' in l or l.startswith('error')]
    def in_region(l):
        m = re.search(r'\.lean:(\d+):', l)
        return m is not None and lo <= int(m.group(1)) <= hi
    warns = [l for l in log.split('\n') if ': warning' in l and in_region(l)]
    hb = re.search(r'Used (\d+) heartbeats', log)
    usage = re.search(r'@usage #\[(.*?)\]', log, re.S)
    rec = {'id': a.id, 'arm': a.arm, 'ok': not errs, 'errors': len(errs), 'warnings': len(warns),
           'heartbeats': int(hb.group(1)) if hb else None, 'lines': n_lines, 'tokens': n_toks,
           'census_lines': int(row['lines']), 'stratum': row['stratum'], 'family': row['family'],
           'seconds': round(dt, 1),
           'library': [s.strip() for s in usage.group(1).split(',') if s.strip()] if usage else [],
           'imports': imports, 'inlines': inlines}
    if errs:
        rec['first_errors'] = errs[:5]
    if warns:
        rec['first_warnings'] = warns[:5]
    with open(os.path.join(HERE, 'results.jsonl'), 'a') as f:
        f.write(json.dumps(rec) + '\n')
    print(json.dumps(rec, indent=1))
    if not a.keep and not errs:
        os.remove(copy)

if __name__ == '__main__':
    main()
