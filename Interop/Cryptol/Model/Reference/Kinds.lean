/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Reference.Syntax

/-! # Kind checking of the accepted Cryptol reference types -/

public section

namespace Interop.Cryptol.Reference

/-- Kinds of each argument and of the result of a fully applied constructor. -/
@[expose] def constructorKinds : String → Option (List Kind × Kind)
  | "TC TCInf" => some ([], .number)
  | "TC TCBit" | "TC TCInteger" => some ([], .value)
  | "TC TCSeq" => some ([.number, .value], .value)
  | "TC TCFun" => some ([.value, .value], .value)
  | "TF TCWidth" => some ([.number], .number)
  | "TF TCAdd" | "TF TCSub" | "TF TCMul" | "TF TCDiv" | "TF TCMod" |
    "TF TCExp" | "TF TCMin" | "TF TCMax" | "TF TCCeilDiv" | "TF TCCeilMod" =>
      some ([.number, .number], .number)
  | "TF TCLenFromThenTo" => some ([.number, .number, .number], .number)
  | "PC PEqual" | "PC PNeq" | "PC PGeq" => some ([.number, .number], .proposition)
  | "PC PFin" | "PC PPrime" | "PC PNotPrime" => some ([.number], .proposition)
  | "PC PZero" | "PC PLogic" | "PC PRing" | "PC PIntegral" | "PC PEq" |
    "PC PCmp" | "PC PSignedCmp" => some ([.value], .proposition)
  | "PC PLiteral" | "PC PLiteralLessThan" => some ([.number, .value], .proposition)
  | "PC PTrue" => some ([], .proposition)
  | "PC PAnd" => some ([.proposition, .proposition], .proposition)
  | _ => none

/-- Infer a type expression's kind while checking parameter identities and arities. -/
def TypeExpr.kind? : Nat → List Parameter → TypeExpr → Except String Kind
  | 0, _, _ => .error "type-kind nesting budget exhausted"
  | fuel + 1, params, expression => do
      let child := TypeExpr.kind? fuel params
      match expression with
      | .var p =>
          match params.find? (fun q => q.id == p.id) with
          | some q =>
              if q.kind = p.kind then return p.kind
              else throw s!"parameter {p.id} has an inconsistent kind"
          | none => throw s!"unbound type parameter {p.id}"
      | .number _ => return .number
      | .constructor name args =>
          match constructorKinds name with
          | none => throw s!"unsupported type constructor {name}"
          | some (expected, result) =>
              let actual ← args.mapM child
              unless actual = expected do throw s!"kind or arity mismatch for {name}"
              return result
      | .tuple size fields =>
          unless size = fields.length do throw "tuple shape annotation mismatch"
          for field in fields do
            unless (← child field) = .value do throw "tuple field is not a value type"
          return .value
      | .record fields =>
          let names := fields.map Prod.fst
          unless names.Nodup do throw "duplicate record field"
          for (_, field) in fields do
            unless (← child field) = .value do throw "record field is not a value type"
          return .value
      | .synonym _ arguments body =>
          for argument in arguments do let _ ← child argument
          child body
      | .has _ arguments =>
          unless (← arguments.mapM child) = [.value, .value] do
            throw "selector constraint requires an aggregate and a field type"
          return .proposition

/-- Check one type expression against a required kind. -/
def TypeExpr.checkKind (fuel : Nat) (params : List Parameter) (kind : Kind)
    (expression : TypeExpr) : Except String Unit := do
  unless (← expression.kind? fuel params) = kind do throw "unexpected type-expression kind"

/-- Check a scheme under its ambient numeric and type parameters. -/
def Schema.checkKinds (fuel : Nat) (ambient : List Parameter) (schema : Schema) :
    Except String Unit := do
  let params := schema.parameters ++ ambient
  unless (params.map Parameter.id).Nodup do throw "duplicate type-parameter identity"
  unless schema.parameters.all (fun p => p.kind != .proposition) do
    throw "proposition parameters must be represented by proof abstraction"
  for c in schema.constraints do c.checkKind fuel params .proposition
  schema.body.checkKind fuel params .value

end Interop.Cryptol.Reference
