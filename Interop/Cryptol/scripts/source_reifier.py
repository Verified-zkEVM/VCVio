"""Scoped reification of the monomorphic SHA-256 source dependency closure.

This is part of the trusted frontend boundary. It retains integer indices,
conditionals, recursive arrays, finite folds, and lexical bindings. It never
unrolls recursion or discharges a source-to-implementation certificate.
"""
from dataclasses import dataclass
from extract_foundation import (Decoder, Closure, Primitive, Symbol, Unsupported,
                                fields, entries, unwrap, name, type_value, lean_var)


@dataclass
class Scope:
    key: str
    value: Symbol
    body: object
    application: bool = False


class SourceDecoder(Decoder):
    ARITIES = {**Decoder.ARITIES, "<=": (1, 2), "foldl": (3, 3),
               "fromToLessThan": (3, 0), "zero": (1, 0)}

    def __init__(self, tree):
        super().__init__(tree)
        self.serial = 0
        self.recursive_arrays = []

    def fresh(self):
        self.serial += 1
        return "v" + str(self.serial)

    def scope(self, key, value, body, application=False):
        if not isinstance(body, Symbol):
            return Scope(key, value, body, application)
        if application:
            fn = Symbol(("arrow", value.ty, body.ty), "lam", (key, body))
            return Symbol(body.ty, "app", (fn, value))
        return Symbol(body.ty, "let", (key, value, body))

    def apply(self, f, x, is_type):
        if isinstance(f, Scope):
            if is_type:
                raise Unsupported("local polymorphic function")
            return self.scope(f.key, f.value, self.apply(f.body, x, False), f.application)
        if isinstance(f, Closure):
            if f.type_binder != is_type:
                raise Unsupported("type/term application mismatch")
            types, values = dict(f.types), dict(f.values)
            if is_type:
                types[f.binder] = x
                return self.expr(f.body, types, values)
            if not isinstance(x, Symbol):
                # The only source higher-order parameter here is generate's function.
                # Quote the function using the concrete type arguments of generate.
                if len(types) != 3:
                    raise Unsupported("unannotated higher-order application")
                n, a, ix = tuple(types.values())
                if not isinstance(n, int) or ix != "integer":
                    raise Unsupported("unsupported generator instantiation")
                x = self.quote(x, ("arrow", ix, a))
            key = self.fresh()
            values[f.binder] = Symbol(x.ty, "var", (key,))
            return self.scope(key, x, self.expr(f.body, types, values), True)
        if isinstance(f, Symbol):
            if is_type or not isinstance(f.ty, tuple) or f.ty[0] != "arrow":
                raise Unsupported("application of nonfunction")
            x = self.quote(x, f.ty[1])
            return Symbol(f.ty[2], "app", (f, x))
        return super().apply(f, x, is_type)

    def quote(self, value, ty):
        if isinstance(value, Symbol):
            if value.ty != ty:
                raise Unsupported(f"source type mismatch: {value.ty!r}, expected {ty!r}")
            return value
        if not isinstance(ty, tuple) or ty[0] != "arrow":
            raise Unsupported("non-data expression at a data type")
        key = self.fresh()
        body = self.quote(self.apply(value, Symbol(ty[1], "var", (key,)), False), ty[2])
        return Symbol(ty, "lam", (key, body))

    def expr(self, node, types, values):
        xs = fields(node)
        if xs[0] == "EIf":
            p, x, y = (self.expr(e, types, values) for e in xs[1:])
            if not all(isinstance(v, Symbol) for v in (p, x, y)) or p.ty != "bit" or x.ty != y.ty:
                raise Unsupported("unsupported conditional type")
            return Symbol(x.ty, "ite", (p, x, y))
        if xs[0] == "EWhere":
            local, bindings = dict(values), []
            for group in entries(xs[2]):
                data = fields(unwrap(group))
                if data[0] == "Recursive":
                    decls = [fields(unwrap(d)) for d in entries(data[1])]
                    if len(decls) != 1:
                        raise Unsupported("mutually recursive local group")
                    decl = decls[0]
                    uid, identifier = name(decl[1])
                    body = fields(decl[2])
                    if body[0] != "DExpr":
                        raise Unsupported("recursive foreign declaration")
                    # The admitted recursive shape is a finite generate application.
                    head = fields(body[1])
                    if head[0] != "EApp":
                        raise Unsupported("recursive binding must generate an array")
                    params = []
                    fn = head[1]
                    while fields(fn)[0] == "ETApp":
                        params.insert(0, type_value(fields(fn)[2], types))
                        fn = fields(fn)[1]
                    if fields(fn)[0] != "EVar" or name(fields(fn)[1])[1] != "generate" or \
                            len(params) != 3 or not isinstance(params[0], int) or params[2] != "integer":
                        raise Unsupported("unsupported recursive array type")
                    ty = ("seq", params[0], params[1])
                    key = self.fresh()
                    recursive = dict(local)
                    recursive[uid] = Symbol(ty, "var", (key,))
                    value = self.quote(self.expr(body[1], types, recursive), ty)
                    value = Symbol(ty, "fix", (key, value))
                    self.recursive_arrays.append((uid, identifier, ty))
                elif data[0] == "NonRecursive":
                    decl = fields(data[1])
                    uid, identifier = name(decl[1])
                    body = fields(decl[2])
                    if body[0] != "DExpr":
                        raise Unsupported("non-expression local declaration")
                    value = self.expr(body[1], types, local)
                else:
                    raise Unsupported("unknown local group")
                if isinstance(value, Symbol):
                    key = self.fresh()
                    bindings.append((key, value))
                    local[uid] = Symbol(value.ty, "var", (key,))
                else:
                    local[uid] = value
            result = self.expr(xs[1], types, local)
            for key, value in reversed(bindings):
                result = self.scope(key, value, result)
            return result
        if xs[0] == "EComp":
            branches = entries(xs[2])
            if len(branches) != 1:
                raise Unsupported("only single-generator comprehensions are reified")
            matches = entries(unwrap(branches[0]))
            if len(matches) != 1:
                raise Unsupported("only single-generator comprehensions are reified")
            match = fields(unwrap(matches[0]))
            if match[0] != "From":
                raise Unsupported("unsupported comprehension match")
            seq = self.expr(match[2], types, values)
            if not isinstance(seq, Symbol) or not isinstance(seq.ty, tuple) or seq.ty[0] != "seq":
                raise Unsupported("finite data generator required")
            key = self.fresh()
            local = dict(values)
            local[name(match[1])[0]] = Symbol(seq.ty[2], "var", (key,))
            body = self.expr(xs[1], types, local)
            if not isinstance(body, Symbol):
                raise Unsupported("comprehension function element")
            return Symbol(("seq", seq.ty[1], body.ty), "comp", (key, seq, body))
        return super().expr(node, types, values)

    def primitive(self, f):
        op, ts, vs = f.identity[1], f.types, f.values
        if op == "foldl":
            n, a, b = ts
            fn = self.quote(vs[0], ("arrow", a, ("arrow", b, a)))
            seed = self.quote(vs[1], a)
            seq = self.quote(vs[2], ("seq", n, b))
            return Symbol(a, "foldl", (n, a, b, fn, seed, seq))
        if op == "fromToLessThan":
            start, stop, ty = ts
            if ty != "integer" or not all(isinstance(k, int) for k in (start, stop)) or stop < start:
                raise Unsupported("unsupported finite enumeration")
            return Symbol(("seq", stop - start, "integer"), "range", (start, stop))
        if op == "zero":
            return Symbol(ts[0], "zero", ())
        if op == "@":
            n, elem, ix = ts
            array = self.quote(vs[0], ("seq", n, elem))
            at = self.quote(vs[1], ix)
            if ix != "integer":
                raise Unsupported("source lookup requires integer index")
            return Symbol(elem, "lookup", (array, at))
        if op in ("+", "-", "*", "<=") and ts[0] == "integer":
            x, y = (self.quote(v, "integer") for v in vs)
            return Symbol("bit" if op == "<=" else "integer",
                          "intLe" if op == "<=" else "intOp", ((x, y) if op == "<=" else
                          ({"+": "add", "-": "sub", "*": "mul"}[op], x, y)))
        if op in ("+", "-", "*") and isinstance(ts[0], tuple) and ts[0][0] == "seq":
            ty = ts[0]
            if not isinstance(ty[2], tuple) or ty[2][0] != "word":
                raise Unsupported("only arrays of words have aggregate arithmetic here")
            x, y = (self.quote(v, ty) for v in vs)
            return Symbol(ty, "arrayArithmetic", ({"+": "add", "-": "sub", "*": "mul"}[op], x, y))
        return super().primitive(f)


def source_type(ty):
    if ty in ("bit", "integer"):
        return "." + ty
    if ty[0] == "word":
        return f"(wordTy {ty[1]})"
    if ty[0] == "seq":
        return f"(.seq (.finite {ty[1]}) {source_type(ty[2])})"
    if ty[0] == "arrow":
        return f"(.arrow {source_type(ty[1])} {source_type(ty[2])})"
    if ty[0] == "tuple":
        result = source_type(ty[-1])
        for t in reversed(ty[1:-1]):
            result = f"(.prod {source_type(t)} {result})"
        return result
    raise Unsupported("unsupported source type")


def source_term(value, context=(), replacements=None):
    replacements = replacements or {}
    if id(value) in replacements:
        helper, free = replacements[id(value)]
        term = helper
        for v in free:
            term = f".app ({term}) ({source_term(v, context)})"
        return term
    op, args = value.op, value.args
    go = lambda x: source_term(x, context, replacements)
    if op == "var":
        if args[0] not in context:
            raise Unsupported("unbound source variable")
        return ".var (" + lean_var(context.index(args[0])) + ")"
    if op == "literal":
        return f".integer {args[0]}" if value.ty == "integer" else \
            f".word (BitVec.ofNat {value.ty[1]} {args[0]})"
    if op in ("lam", "fix"):
        return f".{op} ({source_term(args[1], (args[0], *context), replacements)})"
    if op == "let":
        return f".letE ({go(args[1])})\n    ({source_term(args[2], (args[0], *context), replacements)})"
    if op in ("wordOp", "arithmetic", "intOp", "bitOp"):
        ctor = {"wordOp": "wordLogic", "arithmetic": "wordArithmetic"}.get(op, op)
        return f".{ctor} .{args[0]} ({go(args[1])}) ({go(args[2])})"
    if op == "arrayArithmetic":
        return f".app (.app (.primitive (.wordArrayArithmetic {value.ty[1]} {value.ty[2][1]} " + \
            f".{args[0]})) ({go(args[1])})) ({go(args[2])})"
    if op == "intLe":
        return f".app (.app (.primitive .intLe) ({go(args[0])})) ({go(args[1])})"
    if op in ("shiftLeft", "shiftRight", "rotateLeft", "rotateRight"):
        movement = {"shiftLeft": "left", "shiftRight": "right", "rotateLeft": "rotateLeft",
                    "rotateRight": "rotateRight"}[op]
        # Keep the native dynamic operator and its literal integer argument.
        return f".shift .{movement} ({go(args[1])}) (.integer {args[0]})"
    if op == "wordNot":
        return f".app (.primitive (.wordNot {value.ty[1]})) ({go(args[0])})"
    if op == "sequence":
        return f".sequence {len(args)} ![" + ", ".join(go(x) for x in args) + "]"
    if op == "range":
        return f".sequence {args[1] - args[0]} (fun i => .integer ({args[0]} + (i.val : Int)))"
    if op == "comp":
        key, seq, body = args
        # The generator is bound before the index; the selected element remains suspended.
        index_key, seq_key = "index" + key, "seq" + key
        inner = source_term(body, (key, index_key, seq_key, *context), replacements)
        return f".letE ({go(seq)}) (.generate (.finite {seq.ty[1]}) " + \
            f"(.letE (.index (.var (.succ .zero)) (.var .zero)) ({inner})))"
    if op == "foldl":
        n, a, b, fn, seed, seq = args
        return f".app (.app (.app (.primitive (.foldl {n} {source_type(a)} {source_type(b)})) " + \
            f"({go(fn)})) ({go(seed)})) ({go(seq)})"
    if op in ("index", "lookup"):
        at = f".integer {args[1]}" if op == "index" else go(args[1])
        return f".index ({go(args[0])}) ({at})"
    if op == "zero":
        return f".primitive (.zero {source_type(value.ty)})"
    if op == "projection":
        index, val = args
        result = go(val)
        for _ in range(index):
            result = ".snd (" + result + ")"
        if index < len(val.ty) - 2:
            result = ".fst (" + result + ")"
        return result
    if op == "tuple":
        result = go(args[-1])
        for x in reversed(args[:-1]):
            result = ".pair (" + go(x) + ") (" + result + ")"
        return result
    if op not in ("app", "ite", "bitNot"):
        raise Unsupported("unsupported source printing operation: " + op)
    return f".{op} " + " ".join(f"({go(x)})" for x in args)


def walk_symbols(value):
    if not isinstance(value, Symbol):
        return
    yield value
    for arg in value.args:
        yield from walk_symbols(arg)


def free_variables(value, bound=()):
    if not isinstance(value, Symbol):
        return {}
    if value.op == "var":
        return {} if value.args[0] in bound else {value.args[0]: value}
    if value.op in ("lam", "fix"):
        return free_variables(value.args[1], (value.args[0], *bound))
    if value.op in ("let", "comp"):
        key, val, body = value.args
        return free_variables(val, bound) | free_variables(body, (key, *bound))
    result = {}
    for arg in value.args:
        result.update(free_variables(arg, bound))
    return result


def source_declarations(value):
    """Lift the schedule and round into named source functions without compiling them.

    The inserted applications are ordinary source beta-redexes, checked again
    by the source equation. Naming closed scalar units and loop bodies keeps consumer proof terms small.
    """
    nodes = list(walk_symbols(value))
    fixes = [v for v in nodes if v.op == "fix"]
    folds = [v for v in nodes if v.op == "foldl"]
    if len(fixes) != 1 or len(folds) != 1:
        raise Unsupported("expected one recursive schedule and one round fold")
    helpers, replacements = [], {}

    def lift(helper, node):
        free = list(free_variables(node).values())
        abstract = node
        for var in reversed(free):
            abstract = Symbol(("arrow", var.ty, abstract.ty), "lam", (var.args[0], abstract))
        helpers.append(f"/-- Preserved source unit `{helper}`, with its captured input explicit. -/\n"
            f"@[expose] def {helper} {{Γ : List ClosedTy}} : Term Γ {source_type(abstract.ty)} :=\n  " +
            source_term(abstract, replacements=replacements) + "\n")
        replacements[id(node)] = (helper, free)

    # Closed scalar functions and literal tables are named separately so their
    # semantic equations are checked once, rather than expanded under every binder.
    word_units, tables = 0, {}
    for node in nodes:
        if free_variables(node):
            continue
        if node.op == "lam" and node.ty[-1] == ("word", 32) and \
                len(list(walk_symbols(node))) > 5:
            lift(f"wordSource{word_units}In", node)
            word_units += 1
        elif node.op in ("range", "sequence"):
            key = source_term(node)
            if key in tables:
                replacements[id(node)] = (tables[key], [])
            else:
                helper = f"tableSource{len(tables)}In"
                tables[key] = helper
                lift(helper, node)
    for helper, node in (("scheduleSourceIn", fixes[0]), ("roundSourceIn", folds[0].args[3])):
        lift(helper, node)
    return "\n".join(helpers), source_term(value, replacements=replacements)
