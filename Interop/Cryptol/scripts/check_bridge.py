#!/usr/bin/env python3
"""Reproduce the narrow source bridge and its bounded interoperability probes."""

import argparse
from collections import Counter
import json
import os
import random
import re
import subprocess
import tempfile
import time
from pathlib import Path

import extract_foundation as extract
import coverage_catalogue

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
CLI = REPO / ".lake/build/bin/cryptol-interop"
COMPRESSION = extract.COMPRESSION


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def cli(*args):
    return subprocess.check_output([str(CLI), "foundation", *args], text=True, cwd=REPO, timeout=60)


def rejection_tests():
    count = 0

    def rejected(action):
        nonlocal count
        count += 1
        try:
            action()
        except extract.Unsupported:
            return
        raise AssertionError("unsupported artifact accepted")

    for text in ("", "[(", "[)]", "[] trailing"):
        rejected(lambda: extract.parse_dump(text))
    duplicate = '[(NonRecursive (Decl (1,"x") DPrim)), (NonRecursive (Decl (1,"y") DPrim))]'
    rejected(lambda: extract.Decoder(extract.parse_dump(duplicate)))
    for decl in ('(NonRecursive (Decl (1,"unknown") DPrim))',
                 '(NonRecursive (Decl (1,"foreign") (DForeign (EVar (2,"x")))))',
                 '(Recursive [(Decl (1,"loop") (DExpr (EVar (1,"loop"))))])'):
        rejected(lambda: extract.Decoder(extract.parse_dump("[" + decl + "]")).global_value(1))
    decoder = extract.Decoder(extract.parse_dump("[]"))
    rejected(lambda: decoder.global_value(42))
    rejected(lambda: extract.type_value(extract.parse_dump("(TVar { tpUnique = 42 })"), {}))
    rejected(lambda: decoder.primitive(extract.Primitive((1, "number"), (256, ("word", 8)))))
    rejected(lambda: decoder.primitive(extract.Primitive((1, "^"), (("word", 8),),
             (extract.Symbol(("word", 8), "var", (0,)), extract.Symbol("bit", "var", (0,))))))
    rejected(lambda: extract.lean_term(extract.Symbol(("word", 8), "var", (1,))))
    rejected(lambda: decoder.expr(extract.parse_dump("(EComp [])"), {}, {}))
    rejected(lambda: decoder.expr(extract.parse_dump(
        '(EWhere (EVar (0,"x")) [(Recursive [])])'), {}, {}))
    table = ("seq", 64, ("word", 32))
    at = extract.Symbol("integer", "capture", ("t",))
    rejected(lambda: decoder.primitive(extract.Primitive((1, "@"),
        (64, ("word", 32), "integer"), (extract.Symbol(table, "capture", ("unknown",)), at))))
    rejected(lambda: decoder.primitive(extract.Primitive((1, "@"),
        (63, ("word", 32), "integer"), (extract.Symbol(table, "capture", ("K",)), at))))
    rejected(lambda: decoder.expr(extract.parse_dump('(ESel (EVar (0,"x")) (ListSel 64))'),
        {}, {0: extract.Symbol(table, "var", ("input",))}))
    rejected(lambda: extract.round_root(decoder))
    rejected(lambda: decoder.expr(extract.parse_dump('(ETuple [])'), {}, {}))
    from source_reifier import SourceDecoder, source_term
    source = SourceDecoder(extract.parse_dump("[]"))
    rejected(lambda: source.expr(extract.parse_dump(
        '(EWhere (EVar (1,"x")) [(Recursive [(Decl (1,"x") (DExpr (EVar (1,"x"))))])])'), {}, {}))
    rejected(lambda: source.expr(extract.parse_dump(
        '(EWhere (EVar (1,"x")) [(Recursive [(Decl (1,"x") (DExpr (EVar (2,"y")))), '
        '(Decl (2,"y") (DExpr (EVar (1,"x"))))])])'), {}, {}))
    rejected(lambda: source.quote(extract.Symbol("bit", "literal", (True,)), "integer"))
    rejected(lambda: source_term(extract.Symbol("integer", "foreign", ())))
    rejected(lambda: source_term(extract.Symbol("integer", "var", ("absent",))))
    return count


def integers(output):
    matches = re.findall(r"\[[\d,\s]+\]", output)
    require(len(matches) == 1, "expected one integer list, got: " + output)
    return json.loads(matches[0])


def census(raw):
    """Syntactic dependency closure, without attempting unsupported lowering."""
    tree = extract.parse_dump(raw[raw.index("[ (NonRecursive"):].strip())
    decoder = extract.Decoder(tree)
    roots = [uid for uid, (identity, _, _) in decoder.decls.items() if identity[1] == "result"]
    require(len(roots) == 1, "compression root is ambiguous")
    pending, seen, constructors, primitives, recursive = roots[:], set(), Counter(), set(), []
    local_recursive = set()

    def walk(node):
        if not isinstance(node, extract.Group):
            return
        xs = node.items
        if xs and isinstance(xs[0], str) and re.fullmatch(r"[A-Z][A-Za-z]+", xs[0]):
            constructors[xs[0]] += 1
        if xs and xs[0] == "EVar":
            uid, _ = extract.name(xs[1])
            if uid in decoder.decls and uid not in seen:
                pending.append(uid)
        if xs and xs[0] == "Recursive":
            for decl in extract.entries(xs[1]):
                data = extract.fields(extract.unwrap(decl))
                if data and data[0] == "Decl":
                    local_recursive.add(extract.name(data[1])[1])
        for child in xs:
            walk(child)

    while pending:
        uid = pending.pop()
        if uid in seen:
            continue
        seen.add(uid)
        identity, body, is_recursive = decoder.decls[uid]
        if is_recursive:
            recursive.append(identity[1])
        if body == "DPrim":
            primitives.add(identity[1])
        else:
            walk(body)
    return {"declarations": len(seen), "constructors": dict(sorted(constructors.items())),
            "primitives": sorted(primitives), "recursive_global_declarations": sorted(recursive),
            "recursive_local_declarations": sorted(local_recursive),
            "unsupported_expression_constructors": sorted(k for k in constructors
                if k.startswith("E") and k not in {"EVar", "EAbs", "ETAbs", "EApp", "ETApp", "ETyp",
                    "EList", "ESel", "ETuple", "EWhere"}),
            "unsupported_primitives": sorted(primitives - extract.Decoder.ARITIES.keys())}


def check_rounds(cryptol, foundation, temporary, rng):
    cases = [[0] * 10, [2**32 - 1] * 10, [1 << i for i in range(10)],
             *[[rng.randrange(2**32) for _ in range(10)] for _ in range(5)]]
    exported = temporary / "PolyFunExport.cry"
    exported.write_text(cli("emit-round"))
    sizes, nodes = [], set()
    for values in cases:
        row = json.loads(cli("round", *map(str, values)))
        require(row["source"] == row["vcvio"], "native round disagreement")
        nodes.add(row["nodes"])
        state, kt, wt = values[:8], values[8], values[9]
        state_text = "[" + ",".join(map(str, state)) + "]"
        wrapper = temporary / "PolyFunCompression.cry"
        # A legal Klen=1 instantiation reaches the actual local step3 once.
        # Subtract the feed-forward state to observe its output directly.
        source = COMPRESSION.replace("type Klen = 64", "type Klen = 1").replace(
            "K = K_256", f"K = [{kt}]")
        source = source[:source.index("result :")] + (
            f"result = Core::step ({state_text} : [8][32]) "
            f"([{wt}] # zero : [16][32]) - ({state_text} : [8][32])\n")
        wrapper.write_text(source)
        paths = [([f":load {wrapper}"], "result"),
                 ([f":load {exported}"], f"result ({state_text}, ({kt}, {wt}))")]
        for commands, expression in paths:
            for mode in ("", ":eval "):
                output = extract.run(cryptol, foundation,
                    commands + [":set base=10", mode + expression])
                require(integers(output) == row["vcvio"], "actual local/exported round mismatch")
        sizes.append(exported.stat().st_size)
    return {"cases": len(cases), "external_paths": 4,
            "source_bytes": sorted(set(sizes)), "source_nodes": sorted(nodes),
            "actual_local_round": "Main Klen=1, subtract feed-forward; K/W lookups specialize to words"}


def check_functions(cryptol, foundation, rng):
    triples = [(0, 0, 0), (2**32 - 1, 0, 2**32 - 1),
               *[tuple(rng.randrange(2**32) for _ in range(3)) for _ in range(8)]]
    expressions, wanted = [], []
    for x, y, z in triples:
        row = json.loads(cli("sample-all", str(x), str(y), str(z)))
        require(row["source"] == row["vcvio"], "six-function native mismatch")
        wanted.extend(row["vcvio"])
        expressions.extend([f"toInteger ({name} ({x} : [32]))" for name in
                            ("SIGMA_256_0", "SIGMA_256_1", "sigma_256_0", "sigma_256_1")])
        expressions.extend([f"toInteger ({name} ({x}, {y}, {z}) : [32])" for name in ("Ch", "Maj")])
    for mode in ("", ":eval "):
        output = extract.run(cryptol, foundation, [":load algorithms/SHA2/Functions.cry",
            ":set base=10", mode + "[" + ",".join(expressions) + "]"])
        require(integers(output) == wanted, "six-function Foundation mismatch")
    return {"triples": len(triples), "functions": 6, "evaluators": 2}


def check_compression(cryptol, foundation, temporary, rng):
    source = temporary / "PolyFunExport.cry"
    compiled_text = cli("emit-compression")
    preserved_text = cli("emit-compression-source")
    cases = []
    for offset, state, block in [(0, [0] * 8, [0] * 64),
            (1, [2**32-1] * 8, [255] * 64),
            (3, [1 << i for i in range(8)], list(range(64))),
            *[(offset, [rng.randrange(2**32) for _ in range(8)],
               [rng.randrange(256) for _ in range(64)]) for offset in (0, 2, 17)]]:
        data = [rng.randrange(256) for _ in range(offset)] + block + [25, 99, 150]
        row = json.loads(cli("compress", str(offset), json.dumps(state), json.dumps(data)))
        require(row["compiled"] == row["vcvio"], "full compression native mismatch")
        # The prefix and suffix are outside the stated window.
        changed = [b ^ 255 if i < offset or i >= offset + 64 else b
                   for i, b in enumerate(data)]
        outside = json.loads(cli("compress", str(offset), json.dumps(state), json.dumps(changed)))
        require(outside["vcvio"] == row["vcvio"], "outside-window bytes were observed")
        words = [int.from_bytes(bytes(block[i:i+4]), "big") for i in range(0, 64, 4)]
        cases.append((state, words, row))
    paths = (("Foundation", COMPRESSION, True),
                               ("preserved", preserved_text, True),
                               ("compiled", compiled_text, False)) if cryptol else ()
    for label, text, curried in paths:
        path = temporary / ("PolyFunCompression.cry" if label == "Foundation" else "PolyFunExport.cry")
        path.write_text(text)
        for mode in ("", ":eval "):
            expressions = []
            for state, words, _ in cases:
                st, block = json.dumps(state), json.dumps(words)
                expressions.append(f"result {st} {block}" if curried else f"result ({st}, {block})")
            expression = "join [" + ",".join(expressions) + "]"
            output = extract.run(cryptol, foundation,
                [f":load {path}", ":set base=10", mode + expression])
            require(integers(output) == [word for _, _, row in cases for word in row["vcvio"]],
                    f"full compression {label} {mode} disagreement")
    invalid = [(0, [0] * 7, [0] * 64), (1, [0] * 8, [0] * 64),
               (0, [2**32] * 8, [0] * 64), (0, [0] * 8, [256] * 64)]
    for base, st, data in invalid:
        result = subprocess.run([str(CLI), "foundation", "compress", str(base), json.dumps(st), json.dumps(data)],
                                text=True, capture_output=True, timeout=10)
        require(result.returncode == 1, "invalid compression boundary accepted")
    return {"cases": len(cases), "external_paths": len(paths) * 2, "invalid_boundaries": len(invalid),
            "preserved_bytes": len(preserved_text.encode()), "compiled_bytes": len(compiled_text.encode()),
            "source_nodes": cases[0][2]["sourceNodes"], "compiled_nodes": cases[0][2]["compiledNodes"],
            "compiled_milliseconds": [row["compiledMilliseconds"] for _, _, row in cases],
            "scaling": json.loads(cli("compression-sizes"))}


def check_boundaries():
    subprocess.run(["bash", "scripts/check-interop-isolation.sh"], cwd=REPO, check=True)


def certificate_rejection(temporary):
    probe = temporary / "BadCertificate.lean"
    probe.write_text("""import Interop.Cryptol.Translation.Certified
open Interop.Cryptol Interop.Cryptol.Finite
noncomputable def bad : CertifiedFunction (.word 8) (.word 8) where
  source := .lam (.var .zero)
  implementation := .lam (.word 0)
  correct := by intro x; rfl
""")
    command = ["lake"]
    if os.environ.get("POLYFUN_PATH"):
        command.extend(["-R", "-K", "polyfunPath=" + os.environ["POLYFUN_PATH"]])
    result = subprocess.run([*command, "env", "lean", str(probe)], cwd=REPO,
                            text=True, capture_output=True, timeout=30)
    require(result.returncode != 0 and "rfl" in result.stdout and
            "Tactic" in result.stdout, "wrong certificate was not rejected at its proof")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cryptol", type=Path)
    parser.add_argument("--foundation", type=Path)
    parser.add_argument("--local-only", action="store_true")
    parser.add_argument("--report", type=Path, help="Write diagnostic evidence outside the source tree")
    args = parser.parse_args()
    check_boundaries()
    if args.local_only:
        with tempfile.TemporaryDirectory(prefix="vcvio-cryptol-") as temporary:
            report = {"coverage": coverage_catalogue.check(),
                      "rejections": rejection_tests(), "compression": check_compression(
                None, None, Path(temporary), random.Random(0xC0DEC))}
            certificate_rejection(Path(temporary))
            report["wrong_certificate_rejected"] = True
        if args.report:
            args.report.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(report, indent=2))
        return
    if not args.cryptol or not args.foundation:
        parser.error("external checks require --cryptol and --foundation")
    cryptol, foundation = args.cryptol.resolve(), args.foundation.resolve()
    for path, expected in extract.extract(cryptol, foundation).items():
        require((ROOT / path).read_text() == expected, "stale extraction artifact: " + path)
    report = {"coverage": coverage_catalogue.check(cryptol, foundation),
              "rejections": rejection_tests()}
    # Constraint erasure is addressed by checking concrete roots with Cryptol first.
    try:
        extract.run(cryptol, foundation, [":load algorithms/SHA2/Notation.cry",
                    ":type (ROTRIsRightCircularShift`{32,32} : [32] -> Bit)"])
    except extract.Unsupported:
        report["invalid_rotation_constraint_rejected"] = True
    else:
        raise AssertionError("Cryptol accepted the invalid n < w root")
    rng = random.Random(0xC0DEC)
    samples = sorted({0, 1, 2**31, 2**32 - 1, 0xAAAAAAAA, 0x55555555,
                      *(1 << i for i in range(32)), *(rng.randrange(2**32) for _ in range(16))})
    report["functions"] = check_functions(cryptol, foundation, rng)
    lean = [json.loads(cli("sample", str(x))) for x in samples]
    for row in lean:
        require(row["source"] == row["vcvio"] and row["machine"] ==
                {"status": "value", "value": row["vcvio"]}, "Lean comparison failed")
    report["samples"] = len(samples)
    report["core_steps"] = sorted({x["steps"] for x in lean})
    report["core_nodes"] = sorted({x["nodes"] for x in lean})
    inputs = "[" + ",".join(map(str, samples)) + "]"
    wanted = [row["vcvio"] for row in lean]
    with tempfile.TemporaryDirectory(prefix="vcvio-cryptol-") as temporary:
        temporary = Path(temporary)
        report["round"] = check_rounds(cryptol, foundation, temporary, rng)
        sigma = temporary / "PolyFunExport.cry"
        sigma.write_text(cli("emit-sigma"))
        report["sigma_source_bytes"] = sigma.stat().st_size
        expressions = [([":load algorithms/SHA2/Functions.cry"],
                        f"[toInteger (SIGMA_256_0 x) | x <- ({inputs} : [{len(samples)}][32])]"),
                       ([f":load {sigma}"],
                        f"[toInteger (result x) | x <- ({inputs} : [{len(samples)}][32])]")]
        for commands, expression in expressions:
            for mode in ("", ":eval "):
                values = integers(extract.run(cryptol, foundation,
                    commands + [":set base=10", mode + expression]))
                require(values == wanted, "Foundation/exported-core comparison failed")
        sigma.write_text(cli("emit-property"))
        report["property_source_bytes"] = sigma.stat().st_size
        start = time.monotonic()
        proof = extract.run(cryptol, foundation, [f":load {sigma}", ":prove result"])
        require("Q.E.D." in proof, "external property proof failed: " + proof)
        report["property_solver_seconds"] = time.monotonic() - start
        report["external_linearity"] = "Q.E.D.; independent solver evidence, not a Lean certificate"
        report["compression"] = check_compression(cryptol, foundation, temporary, rng)
        for mode in ("", ":eval "):
            output = extract.run(cryptol, foundation, [":load algorithms/Keccak/Main.cry",
                ":set base=10", mode + "h2bTest", mode + "bitReorderingInfIssue",
                mode + "[toInteger (take`{12} (bitReordering (0x123 # zero : [inf]))), "
                "toInteger (bitReordering 0x123)]"])
            require(len(re.findall(r"^True$", output, re.MULTILINE)) == 2 and
                    integers(output) == [0x480, 0x483], "Keccak bit-order probe failed: " + output)
        report["keccak_finite_infinite_prefix"] = [0x480, 0x483]
        report["saw_statement"] = "h2bTest transcribed and proved in Lean; no SAW certificate imported"
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Foundation bridge: {len(samples)} inputs, four external paths, artifact reproduction, "
          f"{report['rejections']} rejection tests, six functions, eight local rounds, "
          "property, compression and Keccak passed")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
