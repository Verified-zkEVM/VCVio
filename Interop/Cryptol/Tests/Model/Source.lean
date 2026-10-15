/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Translation.Quote
import Interop.Cryptol.Translation.Contracts
import Interop.Cryptol.Translation.Export
import Interop.Cryptol.Model.Inspect

/-!
# Ordinary-import source API canaries

Named quotation, lexical shadowing, products, arrays and specification transfer
are usable without opening implementation bodies.
-/

public section

open Interop.Cryptol Interop.Cryptol.Finite

/-- A shared ARX quotation with lexical shadowing. -/
@[expose] def quoted : Finite.Term [] (.arrow (.word 32) (.word 32)) :=
  [cryptol| fun x => let y := rotr x 7; let x := y + 1; x ^ y]

example (x : BitVec 32) : quoted.denote Env.empty x =
    (x.rotateRight 7 + 1) ^^^ x.rotateRight 7 := rfl

example : Resolved.nodeCount quoted.source = 16 := rfl

/-- error: unbound quoted variable -/
#guard_msgs in
example : Finite.Term [] (.word 32) := [cryptol| missing]

example : Export.coreExpression? (Expr.force (.integer 0) (.integer 1) : ClosedExpr [] .integer) =
    .error "The internal force constructor has no Cryptol source operator" := rfl

example {Γ : List ClosedTy} {a : ClosedTy} (e : Resolved.Term Γ a) (η : Environment Γ) :
    (Resolved.lower e).denote η = Resolved.denote e η :=
  congrArg (fun f => f η) (Resolved.lower_correct e)

example (pre : BitVec 8 × BitVec 8 → Prop) (post : (BitVec 8 × BitVec 8) → BitVec 8 → Prop) :
    DataContract (.prod (.word 8) (.word 8))
      (Finite.Term.lam (.arithmetic .add (.fst (.var .zero)) (.snd (.var .zero))) :
        Finite.Term [] (.arrow (.prod (.word 8) (.word 8)) (.word 8))).lower
      pre post ↔ ∀ x, pre x → post x (x.1 + x.2) := by
  apply Term.dataContract_iff (.prod (.word 8) (.word 8)) (.word 8)
  intro x
  rfl

example (xs : Fin 3 → BitVec 8) :
    DomainResult.applyContinuous
      ((Finite.Term.lam (.index (.var .zero) (1 : Fin 3)) :
        Finite.Term [] (.arrow (.seq 3 (.word 8)) (.word 8))).lower.denote Environment.empty)
      (encodeData (.seq 3 (.word 8)) xs) = .value (wordValue (xs 1)) :=
  Term.denote_apply_data (.seq 3 (.word 8)) (.word 8) _ xs
