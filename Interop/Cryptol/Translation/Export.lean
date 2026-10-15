/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Resolved

/-!
# Export finite descriptions to Cryptol

The printer emits fully annotated expressions with fresh names for de Bruijn
binders. Recursion and infinite sequences remain finite source descriptions.
Schema applications are instantiated before printing. Native primitive heads
and let bindings remain compact. Source lowering is verified in Lean; parsing
and behavior of printed text are checked by the external differential driver.
-/

public section

namespace Interop.Cryptol.Export

/-- Render a closed numeric argument. -/
@[expose] def length : Length → String
  | .finite n => toString n
  | .infinite => "inf"

/-- Render a closed type with explicit grouping. -/
@[expose] def type : ClosedTy → String
  | .var e => e.elim
  | .bit => "Bit"
  | .integer => "Integer"
  | .unit => "()"
  | .seq n a => "[" ++ length n ++ "]" ++ type a
  | .prod a b => "(" ++ type a ++ ", " ++ type b ++ ")"
  | .arrow a b => "(" ++ type a ++ " -> " ++ type b ++ ")"

/-- Generated binder names depend on lexical depth, never on user text. -/
@[expose] def binder (depth : Nat) : String := "x" ++ toString depth

/-- Escape user error messages as Cryptol string literals. -/
@[expose] def stringLiteral (s : String) : String :=
  "\"" ++ String.ofList (s.toList.flatMap fun c => match c with
    | '\\' => ['\\', '\\']
    | '"' => ['\\', '"']
    | '\n' => ['\\', 'n']
    | '\r' => ['\\', 'r']
    | '\t' => ['\\', 't']
    | c => [c]) ++ "\""

/-- A literal error uses the corresponding Cryptol error expression. -/
@[expose] def error : EvalError → String
  | .user s => "error " ++ stringLiteral s
  | .invalidIndex i => "if (([] : [0]Bit) @ (" ++ toString i ++
      " : Integer)) then error \"unreachable\" else error \"unreachable\""
  | .divideByZero => "if ((1 : Integer) / 0 == 0) then error \"unreachable\" " ++
      "else error \"unreachable\""

/-- Concrete integer operator tokens. -/
@[expose] def intOp : IntOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"

/-- Concrete strict bit operator tokens. -/
@[expose] def bitOp : BitOp → String
  | .and => "&&" | .or => "||" | .xor => "^"

/-- Finite or infinite integer enumeration used by a sequence generator. -/
@[expose] def indices : Length → String
  | .finite 0 => "([] : [0]Integer)"
  | .finite (n + 1) => "([0 .. " ++ toString n ++ "] : [" ++ toString (n + 1) ++ "]Integer)"
  | .infinite => "([0 ...] : [inf]Integer)"

/-- The concrete spelling of a retained native primitive constant. -/
@[expose] def primitive : {a : ClosedTy} → Primitive a → String
  | _, .logic _ op => "(" ++ bitOp op ++ ")"
  | _, .complement _ => "complement"
  | _, .ring _ op => "(" ++ intOp op.integer ++ ")"
  | _, .intLe => "(<=)"
  | _, .wordArrayArithmetic _ _ op => "(" ++ intOp op ++ ")"
  | _, .word x => toString x.toNat
  | _, .wordNot _ => "complement"
  | _, .wordLogic _ op => "(" ++ bitOp op ++ ")"
  | _, .wordArithmetic _ op => "(" ++ intOp op ++ ")"
  | _, .wordEq _ => "(==)"
  | _, .wordCompare _ op => match op with
      | .eq => "(==)" | .ne => "(!=)" | .lt => "(<)"
      | .le => "(<=)" | .gt => "(>)" | .ge => "(>=)"
  | _, .toInteger _ => "toInteger"
  | _, .fromInteger _ => "fromInteger"
  | _, .shift _ op => match op with
      | .left => "(<<)" | .right => "(>>)"
      | .rotateLeft => "(<<<)" | .rotateRight => "(>>>)"
  | _, .shiftFixed _ op k =>
      "(\\p0 -> p0 " ++ (match op with
        | .left => "<<" | .right => ">>" | .rotateLeft => "<<<" | .rotateRight => ">>>") ++
        " (" ++ toString k ++ " : Integer))"
  | _, .append _ _ _ => "(#)"
  | _, .take front back _ => "take`{front=" ++ length front ++ ",back=" ++ length back ++ "}"
  | _, .drop front back _ => "drop`{front=" ++ toString front ++ ",back=" ++ length back ++ "}"
  | _, .reverse _ _ => "reverse"
  | _, .join parts each _ => "join`{parts=" ++ length parts ++ ",each=" ++ toString each ++ "}"
  | _, .split parts each _ => "split`{parts=" ++ length parts ++ ",each=" ++ toString each ++ "}"
  | _, .transpose rows cols _ =>
      "transpose`{rows=" ++ length rows ++ ",cols=" ++ length cols ++ "}"
  | _, .update _ _ => "update"
  | _, .updateEnd _ _ => "updateEnd"
  | _, .indexEnd _ _ => "(!)"
  | _, .foldl _ _ _ => "foldl"
  | _, .zero a => "(zero : " ++ type a ++ ")"

/-- Render a head using already annotated children. -/
@[expose] def headText (Γ : List ClosedTy) {a : ClosedTy} (head : Resolved.Op a)
    (child : Fin head.arity → String) : String :=
  match head with
  | .sequence n => "[" ++ String.intercalate ", " ((List.finRange n).map child) ++ "]"
  | .primitive p => primitive p
  | .bit b => if b then "True" else "False"
  | .integer n => if n < 0 then "-" ++ toString n.natAbs else toString n
  | .unit => "()"
  | .error e => error e
  | @Resolved.Op.lam arg _ =>
      "\\(" ++ binder Γ.length ++ " : " ++ type arg ++ ") -> " ++ child 0
  | .app => child 0 ++ " " ++ child 1
  | .letE => child 1 ++ " where " ++ binder Γ.length ++ " = " ++ child 0
  | .pair => "(" ++ child 0 ++ ", " ++ child 1 ++ ")"
  | .fst => child 0 ++ ".0"
  | .snd => child 0 ++ ".1"
  | .generate n => "[ " ++ child 0 ++ " | " ++ binder Γ.length ++ " <- " ++ indices n ++ " ]"
  | .index => child 0 ++ " @ " ++ child 1
  | .ite => "if " ++ child 0 ++ " then " ++ child 1 ++ " else " ++ child 2
  | .fix => binder Γ.length ++ " where " ++ binder Γ.length ++ " = " ++ child 0
  | .bitNot => "~" ++ child 0
  | .bitOp op => child 0 ++ " " ++ bitOp op ++ " " ++ child 1
  | .intOp op => child 0 ++ " " ++ intOp op ++ " " ++ child 1
  | .intEq => child 0 ++ " == " ++ child 1
  | .intLt => child 0 ++ " < " ++ child 1

/-- Print source syntax without expanding native primitives or substituting let bindings. -/
@[expose] def expression : {s : Resolved.Scope} →
    IPFunctor.IFreeM Resolved.signature (fun j => Var j.1 j.2) s → String
  | s, .pure v => "((" ++ binder (s.1.length - 1 - Var.index v) ++ ") : " ++ type s.2 ++ ")"
  | s, .liftBind head next =>
      "((" ++ headText s.1 head (fun i => expression (next i)) ++ ") : " ++ type s.2 ++ ")"

/-- Print a standalone module with fixed, safe declaration and module names. -/
@[expose] def moduleText {a : ClosedTy} (e : Resolved.Term [] a) : String :=
  "module PolyFunExport where\n\nresult : " ++ type a ++ "\nresult = " ++ expression e ++ "\n"

/-- Bare core export is explicitly fallible when its forcing behavior has no source spelling. -/
@[expose] def coreExpression? {Γ : List ClosedTy} {a : ClosedTy} (e : Expr Γ a) :
    Except String String := match Resolved.ofCore? e with
  | .ok term => .ok (expression term)
  | .error e => .error e

/-- Fallible standalone export for core terms with source-level constructors only. -/
@[expose] def coreModuleText? {a : ClosedTy} (e : Expr [] a) : Except String String :=
  match Resolved.ofCore? e with
  | .ok term => .ok (moduleText term)
  | .error e => .error e

end Interop.Cryptol.Export
