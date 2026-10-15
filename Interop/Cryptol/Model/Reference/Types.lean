/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Reference.Kinds

/-!
# Closed reference types and constraint interpretation

Record labels and tuple arities survive specialization. Numeric functions use
the partial `InfNat` equations; failed arithmetic is never replaced by zero.
Class membership follows the structural instances in Cryptol 3.6.0's
`TypeCheck.Solver.Class`, restricted to Bit, Integer, sequences, functions,
tuples, and records. These are explicit checks, separate from expression typing.
-/

public section

namespace Interop.Cryptol.Reference

/-- Closed value types with source aggregate shapes. -/
inductive ValueType where
  | bit | integer
  | seq (length : Length) (element : ValueType)
  | function (argument result : ValueType)
  | tuple (fields : List ValueType)
  | record (fields : List (String × ValueType))
  deriving Repr, BEq, Inhabited

/-- The structural classes supported by the reference fragment. -/
inductive ValueClass where
  | zero | logic | ring | integral | eq | cmp | signedCmp
  deriving Repr, DecidableEq

/-- Distinguish packed words from general structural sequences. -/
@[expose] def ValueType.isBit : ValueType → Bool
  | .bit => true
  | _ => false

/-- Structural instance resolution, including finite-word special cases. -/
@[expose] def ValueType.supports (c : ValueClass) (t : ValueType) : Bool :=
  match t with
  | .bit => c == .zero || c == .logic || c == .eq || c == .cmp
  | .integer => c == .zero || c == .ring || c == .integral || c == .eq || c == .cmp
  | .seq n a =>
      if c == .integral then
        match n, a with | .finite _, .bit => true | _, _ => false
      else if c == .ring && a.isBit then
        match n with | .finite _ => true | .infinite => false
      else if c == .signedCmp && a.isBit then
        match n with | .finite n => n > 0 | .infinite => false
      else if (c == .eq || c == .cmp || c == .signedCmp) &&
          (match n with | .infinite => true | .finite _ => false) then false
      else a.supports c
  | .function _ b =>
      (c == .zero || c == .logic || c == .ring) && b.supports c
  | .tuple fields => c != .integral && fields.attach.all (fun field =>
      have _h := List.sizeOf_lt_of_mem field.property
      field.val.supports c)
  | .record fields => c != .integral && fields.attach.all (fun field =>
      have _h := List.sizeOf_lt_of_mem field.property
      have _h' : sizeOf field.val = 1 + sizeOf field.val.1 + sizeOf field.val.2 := rfl
      field.val.2.supports c)
termination_by sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Closed literal constraints, distinguishing exact values and exclusive bounds. -/
@[expose] def ValueType.literal (exclusive : Bool) (n : Length) : ValueType → Bool
  | .bit => match n with
      | .finite n => n ≤ if exclusive then 2 else 1
      | .infinite => false
  | .integer => exclusive || match n with
      | .finite _ => true
      | .infinite => false
  | .seq (.finite w) .bit => match n with
      | .finite n =>
          match (if exclusive then NumericUnary.lg2 else .width).eval (.finite n) with
          | .finite needed => needed ≤ w
          | .infinite => false
      | .infinite => false
  | _ => false

/-- Numeric comparison includes infinity as the greatest length. -/
@[expose] def lengthGe : Length → Length → Bool
  | .infinite, _ => true
  | .finite _, .infinite => false
  | .finite a, .finite b => b ≤ a

/-- A closed argument of any supported kind. -/
inductive TypeValue where
  | number (length : Length)
  | value (type : ValueType)
  | proposition (holds : Bool)
  deriving Repr, BEq

/-- The kind of a closed argument. -/
@[expose] def TypeValue.kind : TypeValue → Kind
  | .number _ => .number
  | .value _ => .value
  | .proposition _ => .proposition

/-- Resolve a closed numeric argument without coercions or defaults. -/
@[expose] def TypeValue.number? : TypeValue → Except String Length
  | .number n => .ok n
  | _ => .error "expected a numeric argument"

/-- Resolve a closed value-type argument without coercions or defaults. -/
@[expose] def TypeValue.value? : TypeValue → Except String ValueType
  | .value t => .ok t
  | _ => .error "expected a value-type argument"

/-- Resolve a closed constraint without coercions or defaults. -/
@[expose] def TypeValue.proposition? : TypeValue → Except String Bool
  | .proposition p => .ok p
  | _ => .error "expected a constraint"

/-- Identity-indexed instantiations preserve the kind of each source parameter. -/
abbrev TypeEnvironment := List (Nat × TypeValue)

/-- Decode a binary numeric constructor at the pinned frontend version. -/
@[expose] def numericBinary? : String → Option NumericBinary
  | "TF TCAdd" => some .add
  | "TF TCSub" => some .sub
  | "TF TCMul" => some .mul
  | "TF TCDiv" => some .div
  | "TF TCMod" => some .mod
  | "TF TCExp" => some .exp
  | "TF TCMin" => some .min
  | "TF TCMax" => some .max
  | "TF TCCeilDiv" => some .ceilDiv
  | "TF TCCeilMod" => some .ceilMod
  | _ => none

/-- Decode a structural class constructor. -/
@[expose] def valueClass? : String → Option ValueClass
  | "PC PZero" => some .zero
  | "PC PLogic" => some .logic
  | "PC PRing" => some .ring
  | "PC PIntegral" => some .integral
  | "PC PEq" => some .eq
  | "PC PCmp" => some .cmp
  | "PC PSignedCmp" => some .signedCmp
  | _ => none

/-- Evaluate a fully applied constructor, rejecting kind and arithmetic failures. -/
@[expose] def evaluateConstructor (name : String) (args : List TypeValue) :
    Except String TypeValue := do
  match name, args with
  | "TC TCBit", [] => return .value .bit
  | "TC TCInteger", [] => return .value .integer
  | "TC TCInf", [] => return .number .infinite
  | "TC TCSeq", [.number n, .value t] => return .value (.seq n t)
  | "TC TCFun", [.value a, .value b] => return .value (.function a b)
  | "TF TCWidth", [.number n] => return .number (NumericUnary.width.eval n)
  | "TF TCLenFromThenTo", [.number a, .number b, .number c] =>
      match numericRangeLength a b c with
      | some n => return .number n
      | none => throw "undefined enumeration length"
  | "PC PEqual", [.number a, .number b] => return .proposition (a == b)
  | "PC PNeq", [.number a, .number b] => return .proposition (a != b)
  | "PC PGeq", [.number a, .number b] => return .proposition (lengthGe a b)
  | "PC PFin", [.number n] =>
      return .proposition (match n with | .finite _ => true | .infinite => false)
  | "PC PTrue", [] => return .proposition true
  | "PC PAnd", [.proposition a, .proposition b] => return .proposition (a && b)
  | "PC PLiteral", [.number n, .value t] => return .proposition (t.literal false n)
  | "PC PLiteralLessThan", [.number n, .value t] => return .proposition (t.literal true n)
  | _, [.number a, .number b] =>
      match numericBinary? name with
      | some op => match op.eval a b with
          | some n => return .number n
          | none => throw s!"undefined numeric operation {name}"
      | none => throw s!"unsupported numeric constructor {name}"
  | _, [.value t] =>
      match valueClass? name with
      | some c => return .proposition (t.supports c)
      | none => throw s!"unsupported class {name}"
  | _, _ => throw s!"unsupported constructor or argument kinds: {name}"

/-- Type-directed selection also checks the frontend's optional shape annotation. -/
@[expose] def ValueType.select (s : Selector) : ValueType → Except String ValueType
  | .tuple fields => match s with
      | .tuple i size => do
          unless size.isNone || size == some fields.length do throw "tuple shape mismatch"
          match fields[i]? with
          | some t => return t
          | none => throw "tuple selector out of bounds"
      | _ => .error "selector does not match tuple"
  | .record fields => match s with
      | .record label names => do
          unless names.isNone || names == some (fields.map Prod.fst) do
            throw "record shape mismatch"
          match fields.find? (fun f => f.1 == label) with
          | some (_, t) => return t
          | none => throw "unknown record field"
      | _ => .error "selector does not match record"
  | .seq n t => match s with
      | .list i size => do
          unless size.isNone || n == .finite (size.getD 0) do throw "list shape mismatch"
          unless lengthGe n (.finite (i + 1)) do throw "list selector out of bounds"
          return t
      | _ => .error "selector does not match sequence"
  | _ => .error "selector requires an aggregate"

/-- Interpret closed type syntax under an explicit parameter assignment. -/
def TypeExpr.evaluate : Nat → TypeEnvironment → TypeExpr → Except String TypeValue
  | 0, _, _ => .error "type evaluation budget exhausted"
  | fuel + 1, env, e => do
      let child := TypeExpr.evaluate fuel env
      match e with
      | .var p =>
          match env.find? (fun x => x.1 == p.id) with
          | some (_, v) =>
              unless v.kind == p.kind do throw "parameter kind mismatch"
              return v
          | none => throw s!"uninstantiated type parameter {p.id}"
      | .number n => return .number (.finite n)
      | .constructor name args => evaluateConstructor name (← args.mapM child)
      | .tuple size fields =>
          unless size == fields.length do throw "tuple shape mismatch"
          return .value (.tuple (← fields.mapM (fun t => child t >>= TypeValue.value?)))
      | .record fields =>
          unless (fields.map Prod.fst).Nodup do throw "duplicate record label"
          return .value (.record (← fields.mapM fun (label, t) => do
            return (label, ← child t >>= TypeValue.value?)))
      | .synonym _ _ body => child body
      | .has s args =>
          match ← args.mapM child with
          | [.value aggregate, .value field] =>
              return .proposition ((← aggregate.select s) == field)
          | _ => throw "malformed selector constraint"

/-- A checked instantiation includes all source obligations and the resulting type. -/
def Schema.instantiate (fuel : Nat) (ambient : TypeEnvironment) (schema : Schema)
    (arguments : List TypeValue) : Except String (TypeEnvironment × ValueType) := do
  unless schema.parameters.length == arguments.length do throw "wrong type-argument count"
  let mut env := ambient
  for (p, a) in schema.parameters.zip arguments do
    unless p.kind == a.kind do throw "wrong type-argument kind"
    env := (p.id, a) :: env
  for c in schema.constraints do
    unless (← c.evaluate fuel env >>= TypeValue.proposition?) do
      throw "unsatisfied source constraint"
  return (env, ← schema.body.evaluate fuel env >>= TypeValue.value?)

end Interop.Cryptol.Reference
