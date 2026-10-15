#!/usr/bin/env python3
"""Check the optional model CLI, and optionally both pinned Cryptol evaluators."""

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent.parent
REPO = ROOT.parents[1]
CLI = REPO / ".lake/build/bin/cryptol-interop"
CRYPTOL_REVISION = "61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b"

# Cryptol 3.6.0 Reference.lhs uses quot/rem for these Integer operations,
# whereas its normal evaluator rounds down. Keep the discrepancy executable;
# the model's specification target is the reference evaluator.
NORMAL_DIFFERENCES = {"negative_quotient": -3, "negative_remainder": 2}


def run(args, *, env=None, timeout=30):
    if args[0] == str(CLI):
        args = [args[0], "model", *args[1:]]
    return subprocess.run(args, text=True, capture_output=True, env=env,
                          timeout=timeout, cwd=ROOT, check=False)


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def word_value(op, n, k, x):
    mask = (1 << n) - 1
    if op == "left":
        return (x << k) & mask
    if op == "right":
        return x >> k
    if op in ("rotl", "rotr"):
        if not n:
            return 0
        k %= n
        if op == "rotr":
            k = (-k) % n
        return ((x << k) | (x >> (n - k))) & mask
    return {"not": lambda: (~x) & mask, "xor": lambda: x ^ (k & mask),
            "and": lambda: x & (k & mask), "or": lambda: x | (k & mask),
            "sub": lambda: (x - k) & mask, "mul": lambda: (x * k) & mask,
            "neg": lambda: (-x) & mask, "add": lambda: (x + k) & mask}[op]()


def check_words():
    """Exercise independent arithmetic expectations and demand-sensitive observations."""
    fixtures = []
    for n in (0, 1, 2, 3, 8, 32, 64):
        mask = (1 << n) - 1
        patterns = sorted({0, mask, (1 << (n - 1)) if n else 0,
                           int("10" * ((n + 1) // 2), 2) & mask if n else 0})
        if n <= 3:
            patterns = list(range(1 << n))
        cases = [(op, k, x) for op in ("left", "right", "rotl", "rotr")
                 for k in sorted({0, max(0, n - 1), n, n + 1}) for x in patterns]
        cases += [(op, k, x) for op in ("xor", "and", "or", "add", "sub", "mul")
                  for k in (range(1 << n) if n <= 3 else [mask]) for x in patterns]
        cases += [(op, 0, x) for op in ("not", "neg") for x in patterns]
        cases += [(op, k, x) for op in ("rotl", "rotr")
                  for k in (-1, -n - 1) for x in patterns]
        for op, k, x in cases:
            label = f"word {op} {n} {k} {x}"
            result = run([str(CLI), *label.split(), "1000000"], timeout=60)
            require(result.returncode == 0, label + result.stderr)
            report = json.loads(result.stdout)
            value = word_value(op, n, k, x)
            bits = [{"status": "value", "value": bool(value & (1 << i))}
                    for i in reversed(range(n))]
            require(report["outer"] == {"status": "value"} and report["bits"] == bits,
                    label + ": machine disagrees with independent word calculation")
            native = f"({x} : [{n}])"
            if op in ("not", "neg"):
                native = f"complement {native}" if op == "not" else f"negate {native}"
            else:
                operator = {"left": "<<", "right": ">>", "rotl": "<<<", "rotr": ">>>",
                            "xor": "^", "and": "&&", "or": "||",
                            "add": "+", "sub": "-", "mul": "*"}[op]
                rhs = f"({k} : Integer)" if op in ("left", "right", "rotl", "rotr") else \
                    f"({k & mask} : [{n}])"
                native = f"{native} {operator} {rhs}"
            fixtures.append((label, report["source"], native, value))
    for op in ("rotl", "rotr"):
        for input_, status in (("error", "error"), ("diverge", "cutoff")):
            report = json.loads(run([str(CLI), "word", op, "0", "1", input_, "100"]).stdout)
            require(report["outer"]["status"] == status and report["bits"] == [],
                    "zero-width rotation must preserve the input's outer result")
        report = json.loads(run([str(CLI), "word", op, "8", "1", "partial", "1000"]).stdout)
        defined = 7 if op == "rotl" else 1
        require(report["bits"][defined] == {"status": "value", "value": True} and
                all(b["status"] == "error" for i, b in enumerate(report["bits"]) if i != defined),
                "rotation forced or lost a suspended partial bit")
    print(f"Word boundaries: {len(fixtures)} total cases and six demand-sensitive cases passed")
    return fixtures


def check_external_words(cryptol, fixtures):
    executable = str(Path(shutil.which(cryptol)).resolve())
    env = dict(os.environ)
    env["PATH"] = str(Path(executable).parent) + os.pathsep + env.get("PATH", "")
    # Small batches keep failures localized to a manageable set of source expressions.
    batches, batch, size, offset = [], [], 0, 0
    for fixture in fixtures:
        if batch and (len(batch) == 4 or size + len(fixture[1]) > 80000):
            batches.append((offset, batch))
            offset += len(batch)
            batch, size = [], 0
        batch.append(fixture)
        size += len(fixture[1])
    if batch:
        batches.append((offset, batch))
    with tempfile.TemporaryDirectory(prefix="polyfun-word-") as temporary:
        source = Path(temporary) / "PolyFunWords.cry"
        for offset, batch in batches:
            expressions = [f"toInteger ({expr})" for _, core, native, _ in batch
                           for expr in (core, native)]
            source.write_text("module PolyFunWords where\nresults : [" + str(len(expressions)) +
                              "]Integer\nresults = [" + ",\n".join(expressions) + "]\n")
            for mode in ("results", ":eval results"):
                try:
                    result = run([executable, "--ignore-cryptolrc", "--color=none", "-e",
                                  "-c", f":load {source}", "-c", ":set base=10", "-c", mode],
                                 env=env, timeout=60)
                except subprocess.TimeoutExpired as exc:
                    raise AssertionError(f"word batch {offset} ({mode}) timed out; "
                                         f"first case: {batch[0][0]}") from exc
                output = result.stdout + result.stderr
                matches = re.findall(r"\[[\d,\s]+\]", result.stdout)
                require(result.returncode == 0 and len(matches) == 1,
                        f"word batch {offset} ({mode}): {output}")
                require(json.loads(matches[0]) == [value for *_, value in batch for _ in range(2)],
                        f"word batch {offset} ({mode}): native/source discrepancy")
        # These distinguish outer failure from an empty but successfully returned word.
        for op in ("<<<", ">>>"):
            for mode in ("", ":eval "):
                result = run([executable, "--ignore-cryptolrc", "--color=none", "-e", "-c",
                              mode + f'((error "empty" : [0]) {op} (1 : Integer))'], env=env)
                require(re.search(r"^Run-time error: empty$", result.stdout + result.stderr,
                                  re.MULTILINE), "native zero-width rotation lost its outer error")
        for op, index in (("<<<", 7), (">>>", 1)):
            for mode in ("", ":eval "):
                partial = ('[if i == 0 then True else error "partial bit" | '
                           'i <- [0 .. 7] : [8]Integer] : [8]')
                expression = f'(({partial}) {op} (1 : Integer)) @ {index}'
                result = run([executable, "--ignore-cryptolrc", "--color=none", "-e",
                              "-c", mode + expression], env=env)
                require(result.returncode == 0 and re.search(r"^True$", result.stdout, re.MULTILINE),
                        "native rotation demanded an unrelated erroneous bit: " +
                        result.stdout + result.stderr)
        # Normal evaluation forces this erroneous word tail even when indexing
        # the defined prefix. Reference evaluation preserves the suspended tail.
        prefix = '([True] # (error "tail" : [7]))'
        for expression in (prefix + " @ 0", f"({prefix} <<< (1 : Integer)) @ 7",
                           f"({prefix} >>> (1 : Integer)) @ 1"):
            for mode in ("", ":eval "):
                result = run([executable, "--ignore-cryptolrc", "--color=none", "-e",
                              "-c", mode + expression], env=env)
                output = result.stdout + result.stderr
                wanted = r"^True$" if mode else r"^Run-time error: tail$"
                require(result.returncode == (0 if mode else 1) and
                        re.search(wanted, output, re.MULTILINE),
                        "documented partial-word evaluator difference changed: " + output)
    print(f"Native word primitives and compact source exports: {4 * len(fixtures) + 14} comparisons passed "
          "(three documented normal/reference partial-word differences)")


def check_arx():
    fixtures = []
    for n in (32, 64):
        for depth in (1, 2, 4, 8):
            label = f"arx-native {n} {depth}"
            result = run([str(CLI), *label.split()])
            require(result.returncode == 0, label + result.stderr)
            report = json.loads(result.stdout)
            expected = 305419896 & ((1 << n) - 1)
            for _ in range(depth):
                expected ^= word_value("rotr", n, 7, (expected * 2) & ((1 << n) - 1))
            require(report["native"] == expected, label + ": native ARX disagreement")
            require(report["sourceNodes"] <= 20 * depth + 1 and
                    report["source"].count(" where ") == depth,
                    label + ": source sharing was expanded")
            fixtures.append((label, report["source"], f"({expected} : [{n}])", expected))
            print(f"{label}: {report['sourceNodes']} nodes, {len(report['source'])} bytes, "
                  f"{report['nativeNanos']} native ns")
    # Bounded core observations are recorded separately; cutoff remains a cutoff.
    for depth in (1, 2, 4, 8):
        result = run([str(CLI), "arx", "8", str(depth), "2000"], timeout=60)
        require(result.returncode == 0, result.stderr)
        report = json.loads(result.stdout)
        require(report["outer"]["status"] in ("value", "cutoff") and
                all(bit["status"] in ("value", "cutoff") for bit in report["bits"]),
                "bounded ARX observation failed")
    return fixtures


def check_reference_demand(cryptol):
    executable = str(Path(shutil.which(cryptol)).resolve())
    env = dict(os.environ)
    env["PATH"] = str(Path(executable).parent) + os.pathsep + env.get("PATH", "")
    cases = [
        ('(((\\x -> error "left-result") + (error "right-function")) '
         ': Integer -> Integer) 0', "error:left-result", "error:right-function"),
        ('(((\\x -> error "left-result") ^ (error "right-function")) '
         ': Integer -> Bit) 0', "error:right-function", "error:right-function"),
        ('([x + y | x <- [0, 1], y <- [x, x + 10]] : [4]Integer) @ 1', "10", "10"),
        ('([x + y | x <- [0, 1], y <- [x, x + 10]] : [4]Integer) @ 2', "2", "2"),
        ('([x + y | x <- [0, 1] | y <- [10, 11, error "tail"]] : [2]Integer) @ 1',
         "12", "12"),
        ('([23 | x <- (error "left" : [2]Integer) | '
         'y <- (error "right" : [inf]Integer)] : [2]Integer) @ 1', "23", "error:right"),
        ('([23 | x <- (error "left" : [2]Integer) | '
         'y <- (error "right" : [3]Integer)] : [2]Integer) @ 1', "23", "23"),
        ('([False, error "late"] : [2]) == [True, False]', "False", "error:late"),
        ('update ([False, True] : [2]) (-1 : Integer) True', "1", "invalid"),
        ('toInteger ((0x9 : [4]) <<< (-1 : Integer))', "12", "12"),
        ('((error "source" : [4]) << (4 : Integer)) @ 0', "False", "error:source"),
        ('(update (error "source" : [2]) (0 : Integer) True) @ 0', "True", "error:source"),
        ('foldl (error "function" : Integer -> Integer -> Integer) (7 : Integer) '
         '(error "sequence" : [0]Integer)', "7", "error:sequence"),
        ('foldl (\\a b -> 7 : Integer) (error "initial" : Integer) '
         '(error "sequence" : [3]Integer)', "7", "error:sequence"),
        ('(error "left" : Integer) <= (error "right" : Integer)', "error:left", "error:left"),
        ('(error "left" : [0][8]) + ([] : [0][8])', "error:left", "error:left"),
        ('([] : [0][8]) + (error "right" : [0][8])', "error:right", "error:right"),
        ('(zero : Integer -> Bit) (error "argument" : Integer)', "False", "False"),
        ('(zero : [inf]Integer) @ (100000 : Integer)', "0", "0"),
        ('map (\\x -> 7 : Integer) (error "generator" : [3]Integer)', "[7, 7, 7]", "[7, 7, 7]"),
    ]
    observations = []
    for expression, reference, normal in cases:
        if expression.startswith("update "):
            expression = "toInteger (" + expression + ")"
        for prefix, expected in ((":eval ", reference), ("", normal)):
            result = run([executable, "--ignore-cryptolrc", "--color=none", "-e", "-c",
                          ":set base=10", "-c", prefix + expression], env=env)
            output = result.stdout + result.stderr
            if expected.startswith("error:"):
                pattern = r"^Run-time error: " + re.escape(expected[6:]) + r"$"
            elif expected == "invalid":
                pattern = r"^invalid sequence index: -1$"
            else:
                pattern = "^" + re.escape(expected) + "$"
            error_expected = expected.startswith("error:") or expected == "invalid"
            require(result.returncode == (1 if error_expected and not prefix else 0) and
                    re.search(pattern, output, re.MULTILINE) and
                    not re.search(r"parse error|type error|\[error\]", output, re.IGNORECASE),
                    "Cryptol 3.6.0 reference-demand behavior changed: " + expression + "\n" + output)
            observations.append({"expression": expression,
                                 "mode": "reference" if prefix else "normal", "result": expected})
    print(f"Versioned demand checks: {2 * len(cases)} normal/reference observations passed")
    return observations


def check_polymorphic(cryptol):
    """Versioned observations of the finite Lean examples' handwritten source counterparts."""
    executable = str(Path(shutil.which(cryptol)).resolve())
    env = dict(os.environ)
    env["PATH"] = str(Path(executable).parent) + os.pathsep + env.get("PATH", "")
    source = """module OrderedPolymorphic where
polyMap : {n, a, b} (a -> b) -> [n]a -> [n]b
polyMap f xs = [ f x | x <- xs ]
polyXor : {n} (fin n) => ([n], [n]) -> [n]
polyXor (x, y) = x ^ y
different : {n : #} Bit
different = constant`{n = n + 1}
constant : {n : #} Bit
constant = True
twoUses : (Bit, Integer)
twoUses = (identity True, identity (3 : Integer))
  where
    identity : {a} a -> a
    identity x = x
"""
    cases = [
        ('polyMap (\\x -> 7 : Integer) (error "unused" : [3]Integer)',
         "[7, 7, 7]", "[7, 7, 7]"),
        ('polyMap (error "function" : Integer -> Integer) ([] : [0]Integer)', "0", "[]"),
        ('(polyMap (\\x -> 7 : Integer) (error "source" : [inf]Integer)) @ 1000',
         "7", "error:source"),
        ('(polyMap (\\x -> x) (error "source" : [3]Integer)) @ 1',
         "error:source", "error:source"),
        ('toInteger (polyXor ((error "left" : [0]), ([] : [0])))',
         "error:left", "error:left"),
        ('twoUses', "(True, 3)", "(True, 3)"),
    ]
    for width in (0, 1, 2, 3, 8, 32, 64):
        left = (1 << width) - 1
        right = left // 3
        expression = f"toInteger (polyXor (({left} : [{width}]), ({right} : [{width}])))"
        cases.append((expression, str(left ^ right), str(left ^ right)))
    for number in ("0", "1", "31", "inf"):
        cases.append((f"different`{{n={number}}}", "True", "True"))
    with tempfile.TemporaryDirectory(prefix="cryptol-ordered-") as directory:
        fixture = Path(directory) / "OrderedPolymorphic.cry"
        fixture.write_text(source)
        for expression, reference, normal in cases:
            for prefix, expected in ((":eval ", reference), ("", normal)):
                result = run([executable, "--ignore-cryptolrc", "--color=none", "-e",
                              "-c", f":load {fixture}", "-c", ":set base=10",
                              "-c", prefix + expression], env=env)
                output = result.stdout + result.stderr
                error = expected.startswith("error:")
                pattern = (r"^Run-time error: " + re.escape(expected[6:]) + r"$" if error
                           else "^" + re.escape(expected) + "$")
                require(result.returncode == (1 if error and not prefix else 0) and
                        re.search(pattern, output, re.MULTILINE) and
                        not re.search(r"parse error|type error|\[error\]", output, re.IGNORECASE),
                        "Ordered polymorphic observation changed: " + expression + "\n" + output)
    print(f"Ordered polymorphism: {2 * len(cases)} normal/reference observations passed")


def check_cryptol(cryptol, fixtures):
    executable = shutil.which(cryptol)
    require(executable is not None, f"Cryptol executable not found: {cryptol}")
    executable = str(Path(executable).resolve())
    env = dict(os.environ)
    env["PATH"] = str(Path(executable).parent) + os.pathsep + env.get("PATH", "")
    version = run([executable, "--version"], env=env)
    require(version.returncode == 0 and re.search(r"\b3\.6\.0\b", version.stdout) and
            f"Git commit {CRYPTOL_REVISION}" in version.stdout,
            f"Expected Cryptol 3.6.0: {version.stdout}{version.stderr}")
    tested = 0
    with tempfile.TemporaryDirectory(prefix="polyfun-cryptol-") as temporary:
        source = Path(temporary) / "PolyFunExport.cry"
        for fixture in fixtures:
            expected = fixture["expected"]
            # A finite cutoff is tested in Lean. A wall-clock timeout would not
            # provide evidence of semantic divergence in the external engine.
            if expected["status"] == "cutoff":
                continue
            source.write_text(fixture["source"])
            for mode, expression in (("normal", "result"), ("reference", ":eval result")):
                label = f"{fixture['name']} ({mode})"
                try:
                    result = run([executable, "--ignore-cryptolrc", "--color=none", "-e",
                                  "-c", f":load {source}", "-c", ":set base=10",
                                  "-c", expression], env=env)
                except subprocess.TimeoutExpired as exc:
                    raise AssertionError(f"{label}: external evaluation timed out") from exc
                output = result.stdout + result.stderr
                if expected["status"] == "value":
                    values = re.findall(r"^\s*(-?\d+)\s*$", result.stdout, re.MULTILINE)
                    wanted = (NORMAL_DIFFERENCES.get(fixture["name"], expected["value"])
                              if mode == "normal" else expected["value"])
                    require(result.returncode == 0 and values == [str(wanted)],
                            f"{label}: expected {wanted}, got:\n{output}")
                else:
                    error = expected["error"]
                    pattern = {
                        "invalidIndex": r"^invalid sequence index: " +
                            str(error.get("index", "")) + r"$",
                        "divideByZero": r"^division by 0$",
                        "user": r"^Run-time error: " +
                            re.escape(error.get("message", "")) + r"$",
                    }[error["kind"]]
                    # The reference REPL prints errors but exits successfully;
                    # normal evaluation exits with status 1. Match the actual
                    # diagnostic line, never a message quoted in rejected source.
                    require(result.returncode == (1 if mode == "normal" else 0) and
                            re.search(pattern, output, re.MULTILINE),
                            f"{label}: expected {error}, got:\n{output}")
                    require(not re.search(r"parse error|type error|\[error\]", output, re.IGNORECASE),
                            f"{label}: source rejected:\n{output}")
                tested += 1
    print(f"Cryptol 3.6.0: {tested} comparisons passed across both evaluators "
          f"({len(NORMAL_DIFFERENCES)} documented normal/reference differences)")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cryptol", help="Also run the pinned Cryptol 3.6.0 executable")
    args = parser.parse_args()
    result = run([str(CLI), "report"], timeout=60)
    require(result.returncode == 0, result.stderr)
    fixtures = json.loads(result.stdout)
    require(len({f["name"] for f in fixtures}) == len(fixtures), "Duplicate fixture names")
    require(len(fixtures) >= 20, "Regression corpus unexpectedly empty or truncated")
    for fixture in fixtures:
        require(fixture["actual"] == fixture["expected"],
                f"Lean fixture {fixture['name']}: {fixture['actual']} != {fixture['expected']}")
    bad = run([str(CLI), "emit", "does-not-exist"])
    require(bad.returncode != 0 and not bad.stdout, "Unknown fixture should fail without output")
    usage = run([str(CLI)])
    require(usage.returncode != 0 and "Usage:" in usage.stderr, "Missing CLI usage error")
    sample = fixtures[0]
    emitted = run([str(CLI), "emit", sample["name"]])
    require(emitted.returncode == 0 and emitted.stdout == sample["source"], "emit/report mismatch")
    print(f"Lean machine and CLI: {len(fixtures)} fixtures passed")
    words = check_words() + check_arx()
    if args.cryptol:
        check_cryptol(args.cryptol, fixtures)
        check_external_words(args.cryptol, words)
        check_reference_demand(args.cryptol)
        check_polymorphic(args.cryptol)


if __name__ == "__main__":
    main()
