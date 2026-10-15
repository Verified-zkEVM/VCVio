/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.WordShift
public import Interop.Cryptol.Model.WordCompare
public import Interop.Cryptol.Model.Fold
public import Interop.Cryptol.Model.Aggregate
public import Interop.Cryptol.Model.Zero
public import Interop.Cryptol.Model.StructuralLogic
public import Interop.Cryptol.Model.StructuralRing

/-!
# Instantiated Cryptol primitive heads

Primitive constants retain their native operator identity at the source
boundary. Their direct continuous meanings are independent of core lowering.
The preservation theorem covers partial inputs, including errors and bottom.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol

/-- Primitive signatures after numeric and type arguments have been instantiated. -/
inductive Primitive : ClosedTy → Type where
  | zero (a : ClosedTy) : Primitive a
  | logic {a : ClosedTy} (shape : LogicType a) (op : BitOp) :
      Primitive (.arrow a (.arrow a a))
  | complement {a : ClosedTy} (shape : LogicType a) : Primitive (.arrow a a)
  | ring {a : ClosedTy} (shape : RingType a) (op : RingOp) :
      Primitive (.arrow a (.arrow a a))
  | intLe : Primitive (.arrow .integer (.arrow .integer .bit))
  | wordArrayArithmetic (count width : Nat) (op : IntOp) :
      Primitive (.arrow (.seq (.finite count) (wordTy width))
        (.arrow (.seq (.finite count) (wordTy width)) (.seq (.finite count) (wordTy width))))
  | word {n : Nat} (x : BitVec n) : Primitive (wordTy n)
  | wordNot (n : Nat) : Primitive (.arrow (wordTy n) (wordTy n))
  | wordLogic (n : Nat) (op : BitOp) :
      Primitive (.arrow (wordTy n) (.arrow (wordTy n) (wordTy n)))
  | wordArithmetic (n : Nat) (op : IntOp) :
      Primitive (.arrow (wordTy n) (.arrow (wordTy n) (wordTy n)))
  | wordEq (n : Nat) : Primitive (.arrow (wordTy n) (.arrow (wordTy n) .bit))
  | wordCompare (n : Nat) (op : CompareOp) :
      Primitive (.arrow (wordTy n) (.arrow (wordTy n) .bit))
  | toInteger (n : Nat) : Primitive (.arrow (wordTy n) .integer)
  | fromInteger (n : Nat) : Primitive (.arrow .integer (wordTy n))
  | shift (n : Nat) (op : ShiftOp) :
      Primitive (.arrow (wordTy n) (.arrow .integer (wordTy n)))
  | shiftFixed (n : Nat) (op : ShiftOp) (amount : Nat) :
      Primitive (.arrow (wordTy n) (wordTy n))
  | append (front : Nat) (back : Length) (a : ClosedTy) :
      Primitive (.arrow (.seq (.finite front) a)
        (.arrow (.seq back a) (.seq ((Length.finite front).add back) a)))
  | take (front back : Length) (a : ClosedTy) :
      Primitive (.arrow (.seq (front.add back) a) (.seq front a))
  | drop (front : Nat) (back : Length) (a : ClosedTy) :
      Primitive (.arrow (.seq ((Length.finite front).add back) a) (.seq back a))
  | reverse (n : Nat) (a : ClosedTy) :
      Primitive (.arrow (.seq (.finite n) a) (.seq (.finite n) a))
  | join (parts : Length) (each : Nat) (a : ClosedTy) :
      Primitive (.arrow (.seq parts (.seq (.finite each) a))
        (.seq (parts.mul (.finite each)) a))
  | split (parts : Length) (each : Nat) (a : ClosedTy) :
      Primitive (.arrow (.seq (parts.mul (.finite each)) a)
        (.seq parts (.seq (.finite each) a)))
  | transpose (rows cols : Length) (a : ClosedTy) :
      Primitive (.arrow (.seq rows (.seq cols a)) (.seq cols (.seq rows a)))
  | update (l : Length) (a : ClosedTy) :
      Primitive (.arrow (.seq l a) (.arrow .integer (.arrow a (.seq l a))))
  | updateEnd (n : Nat) (a : ClosedTy) :
      Primitive (.arrow (.seq (.finite n) a)
        (.arrow .integer (.arrow a (.seq (.finite n) a))))
  | indexEnd (n : Nat) (a : ClosedTy) :
      Primitive (.arrow (.seq (.finite n) a) (.arrow .integer a))
  | foldl (n : Nat) (a b : ClosedTy) :
      Primitive (.arrow (.arrow a (.arrow b a))
        (.arrow a (.arrow (.seq (.finite n) b) a)))

/-- Lift a curried semantic operation to a curried language function. -/
@[expose] noncomputable def Semantics.function₂ {a b c : ClosedTy}
    (f : Computation a →𝒄 (Computation b →𝒄 Computation c)) :
    Computation (.arrow a (.arrow b c)) :=
  .value (.ofFun (fun x => DomainResult.valueContinuous (f x)))

/-- A third argument remains suspended under the two preceding lambdas. -/
@[expose] noncomputable def Semantics.function₃ {a b c d : ClosedTy}
    (f : Computation a →𝒄 (Computation b →𝒄 (Computation c →𝒄 Computation d))) :
    Computation (.arrow a (.arrow b (.arrow c d))) :=
  .value (.ofFun (fun x => DomainResult.valueContinuous
    (.ofFun (fun y => DomainResult.valueContinuous (f x y)))))

/-- Applying a lifted binary operation demands its operands according to that operation. -/
@[simp] theorem Semantics.apply_function₂ {a b c : ClosedTy}
    (f : Computation a →𝒄 (Computation b →𝒄 Computation c))
    (x : Computation a) (y : Computation b) :
    DomainResult.applyContinuous (DomainResult.applyContinuous (function₂ f) x) y = f x y := rfl

/-- Applying a lifted ternary operation leaves all operand demands to its direct meaning. -/
@[simp] theorem Semantics.apply_function₃ {a b c d : ClosedTy}
    (f : Computation a →𝒄 (Computation b →𝒄 (Computation c →𝒄 Computation d)))
    (x : Computation a) (y : Computation b) (z : Computation c) :
    DomainResult.applyContinuous
      (DomainResult.applyContinuous (DomainResult.applyContinuous (function₃ f) x) y) z =
      f x y z := rfl

/-- Direct reference meanings of the instantiated primitive constants. -/
@[expose] noncomputable def Primitive.denote : {a : ClosedTy} → Primitive a → Computation a
  | _, .zero a => Semantics.zero a
  | _, .logic h op => Semantics.function₂ (h.binarySem op)
  | _, .complement h => .value h.complementSem
  | _, .ring h op => Semantics.function₂ (h.binarySem op)
  | _, .intLe => Semantics.function₂ Semantics.intLe
  | _, .wordArrayArithmetic n w op => Semantics.function₂ (Semantics.wordArrayArithmetic n w op)
  | _, .word x => .value (wordValue x)
  | _, .wordNot n => .value (Semantics.wordNot n)
  | _, .wordLogic n op => Semantics.function₂ (Semantics.wordLogic n op)
  | _, .wordArithmetic n op => Semantics.function₂ (Semantics.wordArithmetic n op)
  | _, .wordEq n => Semantics.function₂ (Semantics.wordEq n)
  | _, .wordCompare n op => Semantics.function₂ (Semantics.wordCompare op n)
  | _, .toInteger n => .value (Semantics.toInteger n)
  | _, .fromInteger n => .value (Semantics.fromInteger n)
  | _, .shift n op => Semantics.function₂ (Semantics.shift op n)
  | _, .shiftFixed n op k => .value (Semantics.shiftFixed op n k)
  | _, .append front back _ => Semantics.function₂ (Semantics.append front back)
  | _, .take front back _ => .value (Semantics.take front back)
  | _, .drop front back _ => .value (Semantics.drop front back)
  | _, .reverse n _ => .value (Semantics.reverse n)
  | _, .join parts each _ => .value (Semantics.join parts each)
  | _, .split parts each _ => .value (Semantics.split parts each)
  | _, .transpose rows cols _ => .value (Semantics.transpose rows cols)
  | _, .update l _ => Semantics.function₃ (Semantics.update l)
  | _, .updateEnd n _ => Semantics.function₃ (Semantics.update (.finite n) true)
  | _, .indexEnd n _ => Semantics.function₂ (Semantics.indexEnd n)
  | _, .foldl n _ _ => Semantics.function₃ (Semantics.foldlPrefix n n)

/-- Lower primitive constants to small kernel expressions with explicit demands. -/
@[expose] def Primitive.lower {Γ : List ClosedTy} : {a : ClosedTy} → Primitive a → Expr Γ a
  | _, .zero a => .zero a
  | _, .logic h op => .lam (.lam (h.binary op (.var (.succ .zero)) (.var .zero)))
  | _, .complement h => .lam (h.complement (.var .zero))
  | _, .ring h op => .lam (.lam (h.binary op (.var (.succ .zero)) (.var .zero)))
  | _, .intLe => .lam (.lam (.intLe (.var (.succ .zero)) (.var .zero)))
  | _, .wordArrayArithmetic _ _ op =>
      .lam (.lam (.wordArrayArithmetic op (.var (.succ .zero)) (.var .zero)))
  | _, .word x => .word x
  | _, .wordNot _ => .lam (.wordNot (.var .zero))
  | _, .wordLogic _ op => .lam (.lam (.wordBitOp op (.var (.succ .zero)) (.var .zero)))
  | _, .wordArithmetic _ op => .lam (.lam (.wordOp op (.var (.succ .zero)) (.var .zero)))
  | _, .wordEq _ => .lam (.lam (.wordEq (.var (.succ .zero)) (.var .zero)))
  | _, .wordCompare _ op => .lam (.lam (.wordCompare op (.var (.succ .zero)) (.var .zero)))
  | _, .toInteger _ => .lam (.wordToInteger (.var .zero))
  | _, .fromInteger n => .lam (.integerToWord n (.var .zero))
  | _, .shift _ op => .lam (.lam (.shift op (.var (.succ .zero)) (.var .zero)))
  | _, .shiftFixed _ op k => .lam (.shiftFixed op k (.var .zero))
  | _, .append _ _ _ => .lam (.lam (.append (.var (.succ .zero)) (.var .zero)))
  | _, .take front back _ => .lam (.take front back (.var .zero))
  | _, .drop front back _ => .lam (.drop front back (.var .zero))
  | _, .reverse _ _ => .lam (.reverse (.var .zero))
  | _, .join parts each _ => .lam (.join parts each (.var .zero))
  | _, .split parts each _ => .lam (.split parts each (.var .zero))
  | _, .transpose rows cols _ => .lam (.transpose rows cols (.var .zero))
  | _, .update _ _ => .lam (.lam (.lam (.update (.var (.succ (.succ .zero)))
      (.var (.succ .zero)) (.var .zero))))
  | _, .updateEnd _ _ => .lam (.lam (.lam (.updateEnd (.var (.succ (.succ .zero)))
      (.var (.succ .zero)) (.var .zero))))
  | _, .indexEnd _ _ => .lam (.lam (.indexEnd (.var (.succ .zero)) (.var .zero)))
  | _, .foldl n _ _ => .lam (.lam (.lam (.foldlPrefix
      (.var (.succ (.succ .zero))) (.var (.succ .zero)) (.var .zero) n)))

/-- Every primitive lowering preserves its meaning on arbitrary partial arguments. -/
theorem Primitive.lower_correct {Γ : List ClosedTy} {a : ClosedTy} (p : Primitive a)
    (η : Environment Γ) : p.lower.denote η = p.denote := by
  cases p with
  | zero a => exact Expr.denote_zero a η
  | logic h op =>
      apply Expr.denote_lam_eq
      intro x
      apply Expr.denote_lam_eq
      intro y
      exact h.denote_binary op _ _ _
  | complement h =>
      apply Expr.denote_lam_eq
      intro x
      exact h.denote_complement _ _
  | ring h op =>
      apply Expr.denote_lam_eq
      intro x
      apply Expr.denote_lam_eq
      intro y
      exact h.denote_binary op _ _ _
  | intLe =>
      apply Expr.denote_lam_eq
      intro x
      apply Expr.denote_lam_eq
      intro y
      exact Expr.denote_intLe _ _ _
  | wordArrayArithmetic n w op =>
      apply Expr.denote_lam_eq
      intro x
      apply Expr.denote_lam_eq
      intro y
      exact Expr.denote_wordArrayArithmetic _ _ _ _
  | word x => exact Expr.denote_word x η
  | wordNot n =>
      apply Expr.denote_lam_eq
      intro x
      exact Expr.denote_wordNot_sem _ _
  | wordLogic n op =>
      apply Expr.denote_lam_eq
      intro x
      apply Expr.denote_lam_eq
      intro y
      exact Expr.denote_wordLogic_sem _ _ _ _
  | wordArithmetic n op =>
      apply Expr.denote_lam_eq
      intro x
      apply Expr.denote_lam_eq
      intro y
      exact Expr.denote_wordArithmetic_sem _ _ _ _
  | wordEq n =>
      apply Expr.denote_lam_eq
      intro x
      apply Expr.denote_lam_eq
      intro y
      exact Expr.denote_wordEq_sem _ _ _
  | wordCompare n op =>
      apply Expr.denote_lam_eq
      intro x
      apply Expr.denote_lam_eq
      intro y
      exact Expr.denote_wordCompare _ _ _ _
  | toInteger n =>
      apply Expr.denote_lam_eq
      intro x
      exact Expr.denote_toInteger_sem _ _
  | fromInteger n =>
      apply Expr.denote_lam_eq
      intro x
      exact Expr.denote_fromInteger_sem _ _ _
  | shift n op =>
      apply Expr.denote_lam_eq
      intro x
      apply Expr.denote_lam_eq
      intro k
      exact Expr.denote_shift _ _ _ _
  | shiftFixed n op k =>
      apply Expr.denote_lam_eq
      intro x
      exact Expr.denote_shiftFixed _ _ _ _
  | append front back a =>
      apply Expr.denote_lam_eq
      intro x
      apply Expr.denote_lam_eq
      intro y
      exact Expr.denote_append _ _ _
  | take front back a =>
      apply Expr.denote_lam_eq
      intro x
      exact Expr.denote_take _ _ _ _
  | drop front back a =>
      apply Expr.denote_lam_eq
      intro x
      exact Expr.denote_drop _ _ _ _
  | reverse n a =>
      apply Expr.denote_lam_eq
      intro x
      exact Expr.denote_reverse _ _
  | join parts each a =>
      apply Expr.denote_lam_eq
      intro x
      exact Expr.denote_join _ _ _ _
  | split parts each a =>
      apply Expr.denote_lam_eq
      intro x
      exact Expr.denote_split _ _ _ _
  | transpose rows cols a =>
      apply Expr.denote_lam_eq
      intro x
      exact Expr.denote_transpose _ _ _ _
  | update l a =>
      apply Expr.denote_lam_eq
      intro x
      apply Expr.denote_lam_eq
      intro i
      apply Expr.denote_lam_eq
      intro value
      exact Expr.denote_update _ _ _ _
  | updateEnd n a =>
      apply Expr.denote_lam_eq
      intro x
      apply Expr.denote_lam_eq
      intro i
      apply Expr.denote_lam_eq
      intro value
      exact Expr.denote_updateEnd _ _ _ _
  | indexEnd n a =>
      apply Expr.denote_lam_eq
      intro x
      apply Expr.denote_lam_eq
      intro i
      exact Expr.denote_indexEnd _ _ _
  | foldl n a b =>
      apply Expr.denote_lam_eq
      intro f
      apply Expr.denote_lam_eq
      intro z
      apply Expr.denote_lam_eq
      intro xs
      exact Expr.denote_foldlPrefix _ _ _ _ _

end Interop.Cryptol
