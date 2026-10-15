/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.SequenceOps
public import Interop.Cryptol.Model.SequenceLaws

/-!
# Sequential and parallel comprehension lowering

Sequential generators enumerate each inner row before advancing the outer
generator. An infinite inner row therefore never advances past the first outer
element. Empty dimensions annihilate infinity. Parallel branches stop at their
shortest length and suspend each branch independently. Local declarations use
the core's lazy `letE` constructor.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol

/-- Sequential generators with finite or infinite inner rows. -/
@[expose] def Expr.flatMap {Γ : List ClosedTy} {a b : ClosedTy} {outer : Length}
    (inner : Length) (f : Expr Γ (.arrow a (.seq inner b)))
    (xs : Expr Γ (.seq outer a)) : Expr Γ (.seq (outer.mul inner) b) :=
  match inner with
  | .finite each => .generate (outer.mul (.finite each))
      (.index (.app f.weaken
        (.index xs.weaken (.intOp .div (.var .zero) (.integer each))))
        (.intOp .mod (.var .zero) (.integer each)))
  | .infinite => .generate (outer.mul .infinite)
      (.index (.app f.weaken (.index xs.weaken (.integer 0))) (.var .zero))

/-- Parallel branch environments retain independently suspended components. -/
@[expose] def Expr.zip {Γ : List ClosedTy} {a b : ClosedTy} {left right : Length}
    (xs : Expr Γ (.seq left a)) (ys : Expr Γ (.seq right b)) :
    Expr Γ (.seq (left.min right) (.prod a b)) :=
  .generate (left.min right)
    (.pair (.index xs.weaken (.var .zero)) (.index ys.weaken (.var .zero)))

/-- Direct reference semantics of sequential generators. -/
@[expose] noncomputable def Semantics.flatMap {a b : ClosedTy} (outer inner : Length) :
    Computation (.arrow a (.seq inner b)) →𝒄 (Computation (.seq outer a) →𝒄
      Computation (.seq (outer.mul inner) b)) :=
  match inner with
  | .finite each => .ofFun (fun f => .ofFun (fun xs => DomainResult.valueContinuous
      (fun i => indexAt
        (DomainResult.applyContinuous f (indexAt xs ((Length.indexNat i : Int).tdiv each)))
        ((Length.indexNat i : Int).tmod each))))
  | .infinite => .ofFun (fun f => .ofFun (fun xs => DomainResult.valueContinuous
      (fun i => indexAt (DomainResult.applyContinuous f (indexAt xs 0)) (Length.indexNat i))))

/-- Direct reference semantics of parallel branch environments. -/
@[expose] noncomputable def Semantics.zip {a b : ClosedTy} (left right : Length) :
    Computation (.seq left a) →𝒄 (Computation (.seq right b) →𝒄
      Computation (.seq (left.min right) (.prod a b))) :=
  .ofFun (fun xs => .ofFun (fun ys => DomainResult.valueContinuous
    (fun i => DomainResult.valueContinuous
      (indexAt xs (Length.indexNat i), indexAt ys (Length.indexNat i)))))

/-- Parallel lowering preserves independent branch demands. -/
theorem Expr.denote_zip {Γ : List ClosedTy} {a b : ClosedTy} {left right : Length}
    (xs : Expr Γ (.seq left a)) (ys : Expr Γ (.seq right b)) (ρ : Environment Γ) :
    (zip xs ys).denote ρ = Semantics.zip left right (xs.denote ρ) (ys.denote ρ) := by
  simp only [zip, denote_generate, denote_pair, denote_index, denote_weaken, denote_var]
  rfl

/-- Sequential lowering preserves finite, empty, and infinite row semantics. -/
theorem Expr.denote_flatMap {Γ : List ClosedTy} {a b : ClosedTy} {outer : Length}
    (inner : Length) (f : Expr Γ (.arrow a (.seq inner b)))
    (xs : Expr Γ (.seq outer a)) (ρ : Environment Γ) :
    (flatMap inner f xs).denote ρ =
      Semantics.flatMap outer inner (f.denote ρ) (xs.denote ρ) := by
  cases inner with
  | infinite =>
      simp only [flatMap, denote_generate, denote_index, denote_app, denote_weaken,
        denote_integer, denote_var]
      rfl
  | finite each =>
      rw [flatMap, denote_generate]
      apply congrArg DomainResult.value
      funext i
      have hn := Length.each_pos_of_index outer each i
      have hi : (each : Int) ≠ 0 := by omega
      simp only [denote_index, denote_app, denote_weaken, denote_intOp, denote_var,
        denote_integer, Environment.extend_zero]
      change Semantics.index
        (DomainResult.applyContinuous (f.denote ρ) (Semantics.index (xs.denote ρ)
          (ofExcept (IntOp.div.eval (Length.indexNat i) each))))
        (ofExcept (IntOp.mod.eval (Length.indexNat i) each)) = _
      simp only [IntOp.eval, hi, ↓reduceIte, ofExcept]
      rfl

end Interop.Cryptol
