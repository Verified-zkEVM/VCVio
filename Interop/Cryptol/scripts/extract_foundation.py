#!/usr/bin/env python3
"""Regenerate the checked Foundation word descriptions from Cryptol's typed AST.

Uses Cryptol 3.6.0's existing Haskell :extract-coq exporter, not a source parser.
That exporter erases proof applications and some type annotations. Cryptol
checks each concrete root first; the accepted monomorphic descriptions are
checked again by Lean. Raw reification remains trusted. Recurrence compilation is certified in Lean.
"""

import argparse
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import textwrap


FOUNDATION = "7d0528bd998682788f4e23661f2829298f9e47db"
CRYPTOL = "61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b"
ROOT = Path(__file__).resolve().parents[1]

COMPRESSION = """module PolyFunCompression where
import algorithms::SHA2::Preprocessing (H0_256)
import algorithms::SHA2::Functions
import algorithms::SHA2::Main as Core where
  type d = 256
  type w = 32
  type Klen = 64
  H0 = H0_256
  K = K_256
  SIGMA_0 = SIGMA_256_0
  SIGMA_1 = SIGMA_256_1
  sigma_0 = sigma_256_0
  sigma_1 = sigma_256_1
result : [8][32] -> [16][32] -> [8][32]
result = Core::step
"""


class Unsupported(ValueError):
    """An artifact outside the explicitly supported subset."""


@dataclass
class Group:
    bracket: str
    items: list

    def text(self):
        close = {"(": ")", "[": "]", "{": "}"}[self.bracket]
        return self.bracket + " ".join(
            x.text() if isinstance(x, Group) else x for x in self.items) + close


def parse_dump(text):
    """Decode only the balanced constructor format emitted by :extract-coq."""
    tokens = re.findall(r'"(?:\\.|[^"\\])*"|[()\[\]{},=]|[^\s()\[\]{},=]+', text)
    if not tokens:
        raise Unsupported("empty constructor dump")
    position = 0

    def group():
        nonlocal position
        opener = tokens[position]
        if opener not in ("(", "[", "{"):
            raise Unsupported("expected constructor group")
        position += 1
        items = []
        close = {"(": ")", "[": "]", "{": "}"}[opener]
        while position < len(tokens) and tokens[position] != close:
            token = tokens[position]
            if token in ("(", "[", "{"):
                items.append(group())
            elif token in (")", "]", "}"):
                raise Unsupported("unbalanced constructor dump")
            else:
                items.append(token)
                position += 1
        if position == len(tokens):
            raise Unsupported("truncated constructor dump")
        position += 1
        return Group(opener, items)

    result = group()
    if position != len(tokens):
        raise Unsupported("trailing data after constructor dump")
    return result


def fields(node):
    if not isinstance(node, Group):
        raise Unsupported("expected constructor, got " + repr(node)[:240])
    return node.items


def name(node):
    xs = fields(node)
    if len(xs) != 3 or xs[1] != ",":
        raise Unsupported("invalid resolved name")
    return int(xs[0]), json.loads(xs[2])


def entries(node):
    result, current = [], []
    for x in fields(node):
        if x == ",":
            result.append(Group("(", current))
            current = []
        else:
            current.append(x)
    if current:
        result.append(Group("(", current))
    return result


def unwrap(node):
    while isinstance(node, Group) and len(node.items) == 1 and isinstance(node.items[0], Group):
        node = node.items[0]
    return node


def type_value(node, env):
    node = unwrap(node)
    xs = fields(node)
    if xs[0] == "ETyp":
        return type_value(xs[1], env)
    if xs[0] == "TUser":
        return type_value(xs[-1], env)
    if xs[0] == "TVar":
        match = re.search(r"tpUnique\s*=\s*(\d+)", node.text())
        if not match or int(match[1]) not in env:
            raise Unsupported("unresolved type variable")
        return env[int(match[1])]
    if xs[0] != "TCon" or len(xs) != 3:
        raise Unsupported("unsupported numeric/type expression: " + node.text()[:120])
    con = fields(xs[1])
    args = [type_value(x, env) for x in entries(xs[2])]
    tag = con[1]
    if isinstance(tag, Group) and fields(tag)[0] == "TCNum":
        return int(fields(tag)[1])
    if tag == "TCBit":
        return "bit"
    if tag == "TCInteger":
        return "integer"
    if tag == "TCSeq" and len(args) == 2 and isinstance(args[0], int):
        return ("word", args[0]) if args[1] == "bit" else ("seq", args[0], args[1])
    if tag in ("TCAdd", "TCSub", "TCMul") and len(args) == 2 and all(
            isinstance(x, int) for x in args):
        a, b = args
        result = {"TCAdd": lambda: a + b, "TCSub": lambda: a - b,
                  "TCMul": lambda: a * b}[tag]()
        if result < 0:
            raise Unsupported("negative numeric result")
        return result
    raise Unsupported("unsupported type constructor: " + node.text()[:120])


@dataclass
class Symbol:
    ty: object
    op: str
    args: tuple


@dataclass
class Closure:
    type_binder: bool
    binder: int
    body: Group
    types: dict
    values: dict


@dataclass
class Primitive:
    identity: tuple
    types: tuple = ()
    values: tuple = ()


class Decoder:
    """Specialize and beta-reduce a finite, nonrecursive dependency closure."""

    ARITIES = {"number": (2, 0), "^": (1, 2), "&&": (1, 2), "||": (1, 2),
               "complement": (1, 1), "==": (1, 2), "<<": (3, 2), ">>": (3, 2),
               "<<<": (3, 2), ">>>": (3, 2), "+": (1, 2), "-": (1, 2),
               "*": (1, 2), "@": (3, 2)}

    def __init__(self, tree):
        self.decls = {}
        self.used = set()
        self.steps = 0
        self.bindings = []
        self.overrides = {}
        self.lookups = set()
        for entry in entries(tree):
            xs = fields(unwrap(entry))
            if xs[0] == "NonRecursive":
                ds = [xs[1]]
            elif xs[0] == "Recursive":
                ds = [unwrap(x) for x in entries(xs[1])]
            else:
                raise Unsupported("unknown declaration group")
            for decl in ds:
                data = fields(decl)
                if data[0] != "Decl":
                    raise Unsupported("expected declaration")
                identity = name(data[1])
                if identity[0] in self.decls:
                    raise Unsupported("duplicate declaration identity")
                self.decls[identity[0]] = (identity, data[2], xs[0] == "Recursive")

    def global_value(self, uid):
        if uid in self.overrides:
            return self.overrides[uid]
        if uid not in self.decls:
            raise Unsupported("unbound resolved identity: " + str(uid))
        self.used.add(uid)
        identity, body, recursive = self.decls[uid]
        if recursive:
            raise Unsupported("recursive dependency: " + identity[1])
        if body == "DPrim":
            if identity[1] not in self.ARITIES:
                raise Unsupported("unsupported primitive: " + identity[1])
            return Primitive(identity)
        xs = fields(body)
        if xs[0] != "DExpr":
            raise Unsupported("foreign or unsupported declaration: " + identity[1])
        return self.expr(xs[1], {}, {})

    def expr(self, node, types, values):
        self.steps += 1
        if self.steps > 10000:
            raise Unsupported("specialization budget exhausted")
        xs = fields(node)
        tag = xs[0]
        if tag == "EVar":
            uid, _ = name(xs[1])
            return values[uid] if uid in values else self.global_value(uid)
        if tag in ("ETAbs", "EAbs"):
            return Closure(tag == "ETAbs", name(xs[1])[0], xs[2], dict(types), dict(values))
        if tag == "ETApp":
            return self.apply(self.expr(xs[1], types, values), type_value(xs[2], types), True)
        if tag == "EApp":
            return self.apply(self.expr(xs[1], types, values), self.expr(xs[2], types, values), False)
        if tag in ("ETuple", "EList"):
            items = tuple(self.expr(unwrap(x), types, values) for x in entries(xs[1]))
            if not items or any(not isinstance(x, Symbol) for x in items):
                raise Unsupported("empty or non-data aggregate")
            if tag == "ETuple":
                return Symbol(("tuple", *(x.ty for x in items)), "tuple", items)
            if any(x.ty != items[0].ty for x in items):
                raise Unsupported("heterogeneous sequence")
            return Symbol(("seq", len(items), items[0].ty), "sequence", items)
        if tag == "ESel":
            value = self.expr(xs[1], types, values)
            selector = fields(xs[2])
            if selector[0] == "TupleSel":
                index = int(selector[1])
                if value.ty[0] != "tuple" or not 0 <= index < len(value.ty) - 1:
                    raise Unsupported("tuple projection out of range")
                if value.op == "tuple":
                    return value.args[index]
                return Symbol(value.ty[index + 1], "projection", (index, value))
            if selector[0] == "ListSel":
                index = int(selector[1])
                if value.ty[0] != "seq" or not 0 <= index < value.ty[1]:
                    raise Unsupported("list projection out of range")
                return Symbol(value.ty[2], "index", (value, index))
            raise Unsupported("unsupported selector")
        if tag == "EWhere":
            local = dict(values)
            for entry in entries(xs[2]):
                group = fields(unwrap(entry))
                if group[0] != "NonRecursive":
                    raise Unsupported("recursive local dependency")
                decl = fields(group[1])
                uid, identifier = name(decl[1])
                body = fields(decl[2])
                if body[0] != "DExpr":
                    raise Unsupported("non-expression local declaration")
                value = self.expr(body[1], types, local)
                if not isinstance(value, Symbol):
                    raise Unsupported("higher-order local binding")
                key = "local" + str(len(self.bindings))
                self.bindings.append((key, identifier, value))
                local[uid] = Symbol(value.ty, "var", (key,))
            return self.expr(xs[1], types, local)
        raise Unsupported("unsupported expression constructor: " + str(tag))

    def apply(self, f, x, is_type):
        if isinstance(f, Closure):
            if f.type_binder != is_type:
                raise Unsupported("type/term application mismatch")
            types, values = dict(f.types), dict(f.values)
            (types if is_type else values)[f.binder] = x
            return self.expr(f.body, types, values)
        if not isinstance(f, Primitive):
            raise Unsupported("application of nonfunction")
        f = Primitive(f.identity, f.types + ((x,) if is_type else ()),
                      f.values + (() if is_type else (x,)))
        nt, nv = self.ARITIES[f.identity[1]]
        if len(f.types) > nt or len(f.values) > nv:
            raise Unsupported("primitive arity mismatch")
        if len(f.types) == nt and len(f.values) == nv:
            return self.primitive(f)
        return f

    def primitive(self, f):
        op, ts, vs = f.identity[1], f.types, f.values
        if op == "number":
            n, ty = ts
            if not isinstance(n, int) or n < 0 or not (ty == "integer" or
                    isinstance(ty, tuple) and ty[0] == "word"):
                raise Unsupported("unsupported literal")
            if ty != "integer" and n >= 2 ** ty[1]:
                raise Unsupported("literal does not fit instantiated width")
            return Symbol(ty, "literal", (n,))
        if any(not isinstance(v, Symbol) for v in vs):
            raise Unsupported("non-base primitive argument")
        if op in ("<<", ">>", "<<<", ">>>"):
            n, index, element = ts
            if not isinstance(n, int) or index != "integer" or element != "bit" or \
                    vs[0].ty != ("word", n) or vs[1].ty != "integer" or \
                    vs[1].op != "literal":
                raise Unsupported("only constant natural word shifts/rotations are supported")
            return Symbol(("word", n), {"<<": "shiftLeft", ">>": "shiftRight",
                          "<<<": "rotateLeft", ">>>": "rotateRight"}[op],
                          (vs[1].args[0], vs[0]))
        if op == "@":
            n, element, index = ts
            array, at = vs
            if index != "integer" or array.ty != ("seq", n, element) or at.ty != index:
                raise Unsupported("lookup type mismatch")
            if array.op != "capture" or array.args[0] not in ("K", "W") or \
                    at.op != "capture" or at.args != ("t",):
                raise Unsupported("lookup is not an identified captured K/W at t")
            self.lookups.add(array.args[0])
            return Symbol(element, "var", (array.args[0].lower() + "t",))
        ty = ts[0]
        if not (ty == "bit" or isinstance(ty, tuple) and ty[0] == "word") or \
                any(v.ty != ty for v in vs):
            raise Unsupported("primitive operand type mismatch")
        if op in ("+", "-", "*"):
            if not isinstance(ty, tuple) or ty[0] != "word":
                raise Unsupported("only word arithmetic is accepted")
            return Symbol(ty, "arithmetic", ({"+": "add", "-": "sub", "*": "mul"}[op], *vs))
        if op == "==":
            if ty == "bit":
                raise Unsupported("Boolean equality is outside this decoder")
            return Symbol("bit", "wordEq", vs)
        if op == "complement":
            return Symbol(ty, "bitNot" if ty == "bit" else "wordNot", vs)
        return Symbol(ty, "bitOp" if ty == "bit" else "wordOp",
                      ({"^": "xor", "&&": "and", "||": "or"}[op], *vs))

    def root(self, identifier, parameters, argument):
        self.bindings = []
        matches = [uid for uid, (identity, _, _) in self.decls.items() if identity[1] == identifier]
        if len(matches) != 1:
            raise Unsupported("root name is missing or ambiguous")
        value = self.global_value(matches[0])
        for parameter in parameters:
            value = self.apply(value, parameter, True)
        return self.apply(value, Symbol(argument, "var", ("input",)), False)


def lean_var(index):
    result = ".zero"
    for _ in range(index):
        result = ".succ (" + result + ")"
    return result


def lean_term(value, context=("input",)):
    op, args = value.op, value.args
    go = lambda x: lean_term(x, context)
    if op == "var":
        if args[0] not in context:
            raise Unsupported("unbound symbolic variable")
        return ".var (" + lean_var(context.index(args[0])) + ")"
    if op == "literal":
        if not isinstance(value.ty, tuple):
            raise Unsupported("integer escaped a static parameter")
        return f".word (BitVec.ofNat {value.ty[1]} {args[0]})"
    if op in ("wordOp", "bitOp", "arithmetic"):
        return f".{op} .{args[0]} ({go(args[1])}) ({go(args[2])})"
    if op in ("shiftLeft", "shiftRight", "rotateLeft", "rotateRight"):
        return f".{op} {args[0]} ({go(args[1])})"
    if op == "sequence":
        return ".sequence " + str(len(args)) + " ![" + ", ".join(go(x) for x in args) + "]"
    if op == "index":
        return f".index ({go(args[0])}) ⟨{args[1]}, by decide⟩"
    if op == "projection":
        index, value = args
        result = go(value)
        for _ in range(index):
            result = ".snd (" + result + ")"
        if index < len(value.ty) - 2:
            result = ".fst (" + result + ")"
        return result
    if op == "tuple":
        result = go(args[-1])
        for x in reversed(args[:-1]):
            result = ".pair (" + go(x) + ") (" + result + ")"
        return result
    return f".{op} " + " ".join(f"({go(x)})" for x in args)


def shared_term(value, bindings, context=("input",)):
    if not bindings:
        return lean_term(value, context)
    key, _, bound = bindings[0]
    return ".letE (" + lean_term(bound, context) + ")\n    (" + shared_term(
        value, bindings[1:], (key, *context)) + ")"


def native_term(value):
    op, args = value.op, value.args
    go = native_term
    if op == "var":
        return args[0]
    if op == "literal":
        return f"({args[0]}#{value.ty[1]})"
    if op in ("wordOp", "bitOp", "arithmetic"):
        operator = {"xor": "^^^", "and": "&&&", "or": "|||", "add": "+",
                    "sub": "-", "mul": "*"}[args[0]]
        return f"({go(args[1])} {operator} {go(args[2])})"
    if op in ("shiftLeft", "shiftRight", "rotateLeft", "rotateRight"):
        operation = "ushiftRight" if op == "shiftRight" else op
        return f"({go(args[1])}).{operation} {args[0]}"
    if op == "wordNot":
        return "(~~~" + go(args[0]) + ")"
    if op == "sequence":
        return "![" + ", ".join(go(x) for x in args) + "]"
    if op == "index":
        return f"({go(args[0])} {args[1]})"
    if op == "projection":
        index, value = args
        result = "(" + go(value) + ")" + ".2" * index
        return result + (".1" if index < len(value.ty) - 2 else "")
    raise Unsupported("unsupported native equation node: " + op)


def lean_type(ty):
    if ty == "bit":
        return ".bit"
    if ty[0] == "word":
        return f"(.word {ty[1]})"
    if ty[0] == "seq":
        return f"(.seq {ty[1]} {lean_type(ty[2])})"
    if ty[0] == "tuple":
        result = lean_type(ty[-1])
        for t in reversed(ty[1:-1]):
            result = f"(.prod {lean_type(t)} {result})"
        return result
    raise Unsupported("unsupported Lean type")


def find_declarations(node, identifier):
    if not isinstance(node, Group):
        return []
    xs = node.items
    if xs and xs[0] == "Decl" and name(xs[1])[1] == identifier:
        return [node]
    return [d for x in xs for d in find_declarations(x, identifier)]


def round_root(decoder):
    # Select the concretely instantiated step, not the parametrized module.
    candidates = [(uid, body) for uid, (identity, body, _) in decoder.decls.items()
                  if identity[1] == "step" and "TVar" not in body.text()]
    if len(candidates) != 1:
        raise Unsupported("instantiated compression step is missing or ambiguous")
    uid, step = candidates[0]
    local = find_declarations(step, "step3")
    schedule = find_declarations(step, "W")
    if len(local) != 1 or len(schedule) != 1:
        raise Unsupported("round/schedule local identity is missing or ambiguous")
    # The round captures W; its recursive definition is recorded, never decoded.
    k_ids = [i for i, (identity, body, _) in decoder.decls.items()
             if identity[1] == "K" and body != "DPrim" and
             re.search(r"EVar \(" + str(i) + r" , \"K\"\)", local[0].text())]
    if len(k_ids) != 1:
        raise Unsupported("instantiated K identity is ambiguous")
    table_ty = ("seq", 64, ("word", 32))
    decoder.overrides[k_ids[0]] = Symbol(table_ty, "capture", ("K",))
    w_id = name(fields(schedule[0])[1])[0]
    local_value = decoder.expr(fields(fields(local[0])[2])[1], {},
                               {w_id: Symbol(table_ty, "capture", ("W",))})
    decoder.bindings = []
    state = ("seq", 8, ("word", 32))
    body = decoder.apply(local_value, Symbol(state, "var", ("state",)), False)
    body = decoder.apply(body, Symbol("integer", "capture", ("t",)), False)
    if body.ty != state or decoder.lookups != {"K", "W"}:
        raise Unsupported("round result or captured lookups mismatch")
    provenance = {"step_identity": uid, "round_identity": name(fields(local[0])[1]),
                  "K_identity": k_ids[0], "W_identity": w_id,
                  "round_ast_sha256": digest(local[0].text()),
                  "W_ast_sha256": digest(schedule[0].text()),
                  "captured_lookups": ["K @ t -> kt", "W @ t -> wt"],
                  "retained_let_bindings": [name for _, name, _ in decoder.bindings]}
    # A single product argument makes arbitrary round contracts straightforward.
    inp = Symbol(("tuple", state, ("word", 32), ("word", 32)), "var", ("input",))
    initial = [("state", "state", Symbol(state, "projection", (0, inp))),
               ("kt", "kt", Symbol(("word", 32), "projection", (1, inp))),
               ("wt", "wt", Symbol(("word", 32), "projection", (2, inp)))]
    return body, initial + decoder.bindings, inp.ty, provenance


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def run(cryptol, foundation, commands):
    env = dict(os.environ)
    env["PATH"] = str(cryptol.parent) + os.pathsep + env.get("PATH", "")
    result = subprocess.run([str(cryptol), "--ignore-cryptolrc", "--color=none", "-e",
                             *[arg for c in commands for arg in ("-c", c)]],
                            cwd=foundation, env=env, text=True, capture_output=True, timeout=60)
    if result.returncode or re.search(r"\[error\]|Parse error|Type error", result.stdout + result.stderr):
        raise Unsupported(result.stdout + result.stderr)
    return result.stdout


def extract(cryptol, foundation):
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=foundation, text=True).strip()
    if revision != FOUNDATION or subprocess.check_output(
            ["git", "status", "--porcelain"], cwd=foundation, text=True).strip():
        raise Unsupported("Foundation must be the clean pinned revision")
    version = subprocess.check_output([str(cryptol), "--version"], text=True)
    if not re.search(r"\b3\.6\.0\b", version) or f"Git commit {CRYPTOL}" not in version:
        raise Unsupported("expected Cryptol 3.6.0 at the pinned source revision")
    word = ("word", 32)
    triple = ("tuple", word, word, word)
    requests = [("sigma256Zero", "SIGMA_256_0", [32], word, word),
                ("sigma256One", "SIGMA_256_1", [32], word, word),
                ("smallSigma256Zero", "sigma_256_0", [32], word, word),
                ("smallSigma256One", "sigma_256_1", [32], word, word),
                ("choose256", "Ch", [word], triple, word),
                ("majority256", "Maj", [word], triple, word),
                *[(f"rotateLaw{k}", "ROTRIsRightCircularShift", [k, 32], word, "bit")
                  for k in (2, 13, 22)]]
    checks = [":type (" + identifier + " : " +
              ("([32], [32], [32])" if argument == triple else "[32]") +
              " -> [32])" for _, identifier, _, argument, result in requests if result != "bit"]
    checks += [":module algorithms::SHA2::Notation", *[
        ":type (ROTRIsRightCircularShift`{" + str(k) + ",32} : [32] -> Bit)" for k in (2, 13, 22)]]
    commands = [":load algorithms/SHA2/Functions.cry"]
    checked = run(cryptol, foundation, commands + checks)
    output = run(cryptol, foundation, commands + [":extract-coq"])
    raw = output[output.index("[ (NonRecursive"):].strip() + "\n"
    normalize = lambda x: x.replace(str(foundation.resolve()), "$FOUNDATION").replace(
        str(cryptol.parent.parent.resolve()), "$CRYPTOL")
    raw = normalize(raw)
    decoder = Decoder(parse_dump(raw))
    definitions = []
    for lean_name, identifier, parameters, argument, result in requests:
        term = decoder.root(identifier, parameters, argument)
        if not isinstance(term, Symbol) or term.ty != result:
            raise Unsupported("root result type mismatch")
        definitions.append(f"/-- Extracted `{identifier}` at {parameters}. -/\n"
                           f"@[expose] def {lean_name}In {{Γ : List Finite.Ty}} : Term Γ (.arrow {lean_type(argument)} "
                           f"{lean_type(result)}) :=\n"
                           "  .lam (" + shared_term(term, decoder.bindings).replace(") (", ")\n    (") + ")\n")
    for lean_name, _, _, argument, result in requests:
        definitions.append(f"/-- Closed entry point for `{lean_name}In`. -/\n"
            f"@[expose] def {lean_name} : Term [] (.arrow {lean_type(argument)} "
            f"{lean_type(result)}) := {lean_name}In\n")
    # Use the actual module instantiation to reach its local round.
    with tempfile.TemporaryDirectory(prefix="foundation-extract-") as tmp:
        wrapper = Path(tmp) / "PolyFunCompression.cry"
        wrapper.write_text(COMPRESSION)
        output = run(cryptol, foundation, [f":load {wrapper}", ":extract-coq"])
        round_raw = normalize(output[output.index("[ (NonRecursive"):].strip() + "\n").replace(
            str(Path(tmp).resolve()), "$WRAPPER").replace(str(Path(tmp)), "$WRAPPER")
    round_decoder = Decoder(parse_dump(round_raw))
    body, bindings, argument, round_info = round_root(round_decoder)
    definitions.append("/-- Actual local `step3`, with captured lookups specialized to `kt`/`wt`. -/\n"
                       "@[expose] def round256In {Γ : List Finite.Ty} : Term Γ (.arrow " + lean_type(argument) + " " +
                       lean_type(body.ty) + ") :=\n  .lam (" + shared_term(body, bindings) + ")\n")
    definitions.append("/-- Closed entry point for `round256In`. -/\n"
        "@[expose] def round256 : Term [] (.arrow " + lean_type(argument) + " " +
        lean_type(body.ty) + ") := round256In\n")
    native_body = "\n".join("  let " + key + " := " + native_term(value)
                            for key, _, value in bindings)
    definitions.append("/-- Native equation generated from the same checked round description. -/\n"
        "@[expose] def round256Native (input : (Fin 8 → BitVec 32) × BitVec 32 × BitVec 32) :\n"
        "    Fin 8 → BitVec 32 :=\n" + native_body + "\n  " + native_term(body) + "\n\n"
        "/-- The generated native equation follows from the public constructor equations. -/\n"
        "theorem round256In_denote {Γ : List Finite.Ty} (ρ : Env Γ)\n"
        "    (input : (Fin 8 → BitVec 32) × BitVec 32 × BitVec 32) :\n"
        "    round256In.denote ρ input = round256Native input := by\n"
        "  funext i\n  fin_cases i <;>\n"
        "    simp [round256In, round256Native, ArithOp.eval, wordOp]\n\n"
        "/-- The closed entry point computes the native round. -/\n"
        "theorem round256_denote (input : (Fin 8 → BitVec 32) × BitVec 32 × BitVec 32) :\n"
        "    round256.denote Env.empty input = round256Native input :=\n"
        "  round256In_denote Env.empty input\n")
    constants_decoder = Decoder(parse_dump(round_raw))
    constants_value = constants_decoder.global_value(round_info["K_identity"])
    if constants_value.ty != ("seq", 64, word) or constants_value.op != "sequence" or any(
            x.op != "literal" for x in constants_value.args):
        raise Unsupported("expected 64 literal round constants")
    definitions.append("/-- Constants reached through the concrete compression module. -/\n"
        "@[expose] def constants256 : Fin 64 → BitVec 32 :=\n  " +
        native_term(constants_value) + "\n")
    source = """/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Translation.FiniteSource
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Extracted Foundation descriptions

Generated by `Interop/Cryptol/scripts/extract_foundation.py` from the pinned typed AST.
The declarations are checked finite descriptions, not manually copied algorithms.
The artifact manifest records the trusted frontend and specialization boundary.
-/

public section

namespace Interop.Cryptol.Bridge.Foundation

open Interop.Cryptol.Finite

""" + "\n".join(definitions) + "\nend Interop.Cryptol.Bridge.Foundation\n"
    source = "\n".join(textwrap.fill(line, width=96, subsequent_indent="    ",
        break_long_words=False, break_on_hyphens=False) if len(line) > 96 else line
        for line in source.splitlines()) + "\n"
    # The preserved source is reified separately from the finite word decoder.
    from source_reifier import SourceDecoder, source_declarations
    source_decoder = SourceDecoder(parse_dump(round_raw))
    step_ids = [uid for uid, (identity, body, _) in source_decoder.decls.items()
                if identity[1] == "step" and "TVar" not in body.text()]
    if len(step_ids) != 1:
        raise Unsupported("source compression root is ambiguous")
    state, block = ("seq", 8, word), ("seq", 16, word)
    source_value = source_decoder.quote(source_decoder.global_value(step_ids[0]),
                                        ("arrow", state, ("arrow", block, state)))
    source_helpers, source_code = source_declarations(source_value)
    source_header = source[:source.index("namespace Interop.Cryptol.Bridge.Foundation")]
    source_header = source_header.replace("Interop.Cryptol.Translation.FiniteSource", "Interop.Cryptol.Model.ResolvedLaws")
    source_header = source_header.replace("# Extracted Foundation descriptions", "# Preserved Foundation compression source")
    source_header = source_header.replace(
        "The declarations are checked finite descriptions, not manually copied algorithms.",
        "Recursion, folds, integer indices, branches, and lexical bindings remain in the source.")
    resolved_source = source_header + """namespace Interop.Cryptol.Bridge.Foundation

open Interop.Cryptol Interop.Cryptol.Resolved

""" + source_helpers + """
/-- Concrete `Main::step`, reified before recurrence or fold compilation. -/
@[expose] def compressionSource : Term []
    (.arrow (.seq (.finite 8) (wordTy 32))
      (.arrow (.seq (.finite 16) (wordTy 32)) (.seq (.finite 8) (wordTy 32)))) :=
  """ + source_code + "\n\nend Interop.Cryptol.Bridge.Foundation\n"
    resolved_source = "\n".join(textwrap.fill(line, width=96, subsequent_indent="    ",
        break_long_words=False, break_on_hyphens=False) if len(line) > 96 else line
        for line in resolved_source.splitlines()) + "\n"
    source_files = ["algorithms/SHA2/Functions.cry", "algorithms/SHA2/Notation.cry",
                    "algorithms/SHA2/Main.cry", "algorithms/SHA2/Preprocessing.cry", "NOTICE.md", "LICENSE"]
    manifest = {"foundation_revision": FOUNDATION, "cryptol_revision": CRYPTOL,
                "cryptol_version": "3.6.0", "export": ":extract-coq", "roots": requests,
                "source_sha256": {p: digest((foundation / p).read_text()) for p in source_files},
                "normalized_ast_sha256": digest(raw), "lean_sha256": digest(source),
                "round_normalized_ast_sha256": digest(round_raw), "round": round_info,
                "compression_source_sha256": digest(resolved_source),
                "recursive_arrays": source_decoder.recursive_arrays,
                "source_dependencies": [source_decoder.decls[uid][0]
                                        for uid in sorted(source_decoder.used)],
                "round_dependencies": [round_decoder.decls[uid][0]
                                       for uid in sorted(round_decoder.used)],
                "dependencies": [decoder.decls[uid][0] for uid in sorted(decoder.used)],
                "trusted": ["Cryptol 3.6.0 frontend, type checking and erased constraints",
                            "typed AST exporter and constructor decoder",
                            "monomorphic structural reification, comprehension translation and lambda lifting"],
                "checked": ["Lean typing and partial source/core preservation",
                            "preserved recursive schedule and lazy fold normalization",
                            "strict-prefix recurrence compilation, all 64 rounds and feed-forward",
                            "arbitrary-state/block byte-array VCVio compression equality",
                            "bidirectional total contracts and adaptive response/state replacement"],
                "tested": ["source printer against both pinned Cryptol evaluators",
                           "raw Foundation, preserved source and finite compiled compression"]}
    return {"artifacts/typed-ast.txt": raw, "artifacts/round-typed-ast.txt": round_raw, "artifacts/types.txt": checked,
            "artifacts/foundation-notice.txt": (foundation / "NOTICE.md").read_text(),
            "artifacts/manifest.json": json.dumps(manifest, indent=2) + "\n",
            "Bridge/Foundation.lean": source,
            "Bridge/SourceFoundation.lean": resolved_source}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cryptol", type=Path, required=True)
    parser.add_argument("--foundation", type=Path, required=True)
    parser.add_argument("--check", action="store_true", help="Check committed artifacts without rewriting")
    args = parser.parse_args()
    artifacts = extract(args.cryptol.resolve(), args.foundation.resolve())
    for name_, content in artifacts.items():
        path = ROOT / name_
        if args.check:
            if not path.exists() or path.read_text() != content:
                raise Unsupported("artifact differs: " + name_)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print("Foundation: nine scalar/property roots, the local round and preserved full compression " + ("reproduced" if args.check else "extracted"))


if __name__ == "__main__":
    import sys
    sys.modules.setdefault("extract_foundation", sys.modules[__name__])
    main()
