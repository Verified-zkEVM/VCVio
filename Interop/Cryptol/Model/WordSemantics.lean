/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.WordArithmetic
public import Interop.Cryptol.Model.SequenceOps

/-!
# Reference word operations on partial values

These continuous operations are defined directly on semantic computations.
The lowering equations hold for arbitrary environments and partial operands;
the native BitVec theorems separately require fully represented operands.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol

/-- A finite word type, with most-significant-bit-first sequence positions. -/
abbrev wordTy (n : Nat) : ClosedTy := .seq (.finite n) .bit

namespace Semantics

/-- Strict complement on a single bit. -/
@[expose] noncomputable def bitNot : Computation .bit →𝒄 Computation .bit :=
  DomainResult.bind (DiscreteOrder.continuousMap fun b : Bool => .value ⟨!b⟩)

/-- Complement demands the word constructor, then computes each bit on demand. -/
@[expose] noncomputable def wordNot (n : Nat) : Computation (wordTy n) →𝒄
    Computation (wordTy n) :=
  .ofFun (fun x => DomainResult.force x (DomainResult.valueContinuous
    (fun i : Fin n => bitNot (indexAt x i.val))))

/-- Logic demands both outer words before exposing a sequence of lazy bit operations. -/
@[expose] noncomputable def wordLogic (n : Nat) (op : BitOp) :
    Computation (wordTy n) →𝒄 (Computation (wordTy n) →𝒄 Computation (wordTy n)) :=
  .ofFun (fun x => .ofFun (fun y => DomainResult.force x (DomainResult.force y
    (DomainResult.valueContinuous (fun i : Fin n =>
      binary (fun a b => .ok (op.eval a b)) (indexAt x i.val) (indexAt y i.val))))))

/-- Left-to-right equality tests, stopping at the first unequal bit. -/
@[expose] noncomputable def wordEqualBits (n : Nat) : List (Fin n) →
    Computation (wordTy n) →𝒄 (Computation (wordTy n) →𝒄 Computation .bit)
  | [] => .const (.const (.value ⟨true⟩))
  | i :: is => .ofFun (fun x => .ofFun (fun y =>
      conditional (wordEqualBits n is x y, .value ⟨false⟩)
        (bitNot (binary (fun a b => .ok (BitOp.xor.eval a b))
          (indexAt x i.val) (indexAt y i.val)))))

/-- Word equality preserves the reference's outer strictness and prefix demand. -/
@[expose] noncomputable def wordEq (n : Nat) :
    Computation (wordTy n) →𝒄 (Computation (wordTy n) →𝒄 Computation .bit) :=
  .ofFun (fun x => .ofFun (fun y => DomainResult.force x (DomainResult.force y
    (wordEqualBits n (List.finRange n) x y))))

/-- Unsigned accumulation of a prefix in most-significant-bit order. -/
@[expose] noncomputable def wordPrefix (n : Nat) : Nat →
    Computation (wordTy n) →𝒄 Computation .integer
  | 0 => .const (.value ⟨0⟩)
  | k + 1 => .ofFun (fun x => binary IntOp.add.eval
      (binary IntOp.mul.eval (wordPrefix n k x) (.value ⟨2⟩))
      (conditional (a := .integer) (.value ⟨1⟩, .value ⟨0⟩) (indexAt x k)))

/-- Even an empty word must expose its outer constructor during conversion. -/
@[expose] noncomputable def toInteger (n : Nat) :
    Computation (wordTy n) →𝒄 Computation .integer :=
  .ofFun (fun x => DomainResult.force x (wordPrefix n n x))

/-- Integer conversion demands its argument before exposing any output word. -/
@[expose] noncomputable def fromInteger (n : Nat) :
    Computation .integer →𝒄 Computation (wordTy n) :=
  DomainResult.bind (DiscreteOrder.continuousMap fun x : Int =>
    DomainResult.value (wordValue (BitVec.ofInt n x)))

/-- Whole-word arithmetic demands left and right unsigned values, then wraps the result. -/
@[expose] noncomputable def wordArithmetic (n : Nat) (op : IntOp) :
    Computation (wordTy n) →𝒄 (Computation (wordTy n) →𝒄 Computation (wordTy n)) :=
  .ofFun (fun x => .ofFun (fun y =>
    fromInteger n (binary op.eval (toInteger n x) (toInteger n y))))

end Semantics

namespace Expr

variable {Γ : List ClosedTy} {n : Nat}

theorem denote_wordNot_sem (x : Expr Γ (wordTy n)) (η : Environment Γ) :
    x.wordNot.denote η = Semantics.wordNot n (x.denote η) := by
  change DomainResult.force (x.denote η) _ = DomainResult.force (x.denote η) _
  congr 1
  apply congrArg DomainResult.value
  funext i
  change Semantics.bitNot ((Expr.index x.weaken (.var .zero)).denote
    (η.extend (.value ⟨(i.val : Int)⟩))) = _
  rw [denote_index, denote_weaken]
  rfl

theorem denote_wordLogic_sem (op : BitOp) (x y : Expr Γ (wordTy n)) (η : Environment Γ) :
    (wordBitOp op x y).denote η = Semantics.wordLogic n op (x.denote η) (y.denote η) := by
  change DomainResult.force (x.denote η) (DomainResult.force (y.denote η) _) =
    DomainResult.force (x.denote η) (DomainResult.force (y.denote η) _)
  congr 1
  congr 1
  apply congrArg DomainResult.value
  funext i
  change Semantics.binary _
    ((Expr.index x.weaken (.var .zero)).denote (η.extend (.value ⟨(i.val : Int)⟩)))
    ((Expr.index y.weaken (.var .zero)).denote (η.extend (.value ⟨(i.val : Int)⟩))) = _
  simp only [denote_index, denote_weaken]
  rfl

theorem denote_wordEqualBits_sem (x y : Expr Γ (wordTy n)) (η : Environment Γ)
    (is : List (Fin n)) :
    (allBits (fun i : Fin n => .bitNot (.bitOp .xor
      (.index x (.integer i.val)) (.index y (.integer i.val)))) is).denote η =
        Semantics.wordEqualBits n is (x.denote η) (y.denote η) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      change Semantics.conditional (a := .bit) (_, .value ⟨false⟩) _ = _
      rw [ih]
      rfl

theorem denote_wordEq_sem (x y : Expr Γ (wordTy n)) (η : Environment Γ) :
    (wordEq x y).denote η = Semantics.wordEq n (x.denote η) (y.denote η) := by
  change DomainResult.force (x.denote η) (DomainResult.force (y.denote η) _) = _
  rw [denote_wordEqualBits_sem]
  rfl

theorem denote_wordPrefix_sem (x : Expr Γ (wordTy n)) (η : Environment Γ) (k : Nat) :
    (x.wordPrefix k).denote η = Semantics.wordPrefix n k (x.denote η) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change Semantics.binary IntOp.add.eval
        (Semantics.binary IntOp.mul.eval ((x.wordPrefix k).denote η) (.value ⟨2⟩)) _ = _
      rw [ih]
      rfl

theorem denote_toInteger_sem (x : Expr Γ (wordTy n)) (η : Environment Γ) :
    x.wordToInteger.denote η = Semantics.toInteger n (x.denote η) := by
  simp only [wordToInteger, denote_force, denote_letE, denote_wordPrefix_sem, denote_var]
  rfl

theorem denote_fromInteger_sem (x : Expr Γ .integer) (η : Environment Γ) (n : Nat) :
    (integerToWord n x).denote η = Semantics.fromInteger n (x.denote η) := by
  generalize hx : x.denote η = d
  induction d using WithBot.recBotCoe with
  | bot =>
      change DomainResult.force (x.denote η) _ = _
      rw [hx]
      rfl
  | coe v =>
      cases v with
      | inl err =>
          change DomainResult.force (x.denote η) _ = _
          rw [hx]
          rfl
      | inr v => exact denote_integerToWord x η v.value hx n

theorem denote_wordArithmetic_sem (op : IntOp) (x y : Expr Γ (wordTy n))
    (η : Environment Γ) : (wordOp op x y).denote η =
      Semantics.wordArithmetic n op (x.denote η) (y.denote η) := by
  rw [wordOp, denote_fromInteger_sem, denote_intOp, denote_toInteger_sem, denote_toInteger_sem]
  rfl

end Expr

end Interop.Cryptol
