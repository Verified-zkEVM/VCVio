/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.WordSemantics

/-!
# Dynamic word shifts and rotations

The amount is an integer computation, demanded before the sequence is
exposed. Word-valued amounts compose with unsigned conversion. Negative
shifts retain the reference evaluator's index checks; rotations use Euclidean
remainder. No normalization of negative shifts to the opposite direction is
assumed.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol

/-- The four unsigned sequence movement operations. -/
inductive ShiftOp where
  | left | right | rotateLeft | rotateRight
  deriving DecidableEq, Repr

/-- Rotation of an empty sequence returns the source after demanding the amount. -/
@[expose] def ShiftOp.preservesEmpty : ShiftOp → Bool
  | .left | .right => false
  | .rotateLeft | .rotateRight => true

/-- An output position selects a source index, or a zero-filled bit. -/
@[expose] def ShiftOp.position (op : ShiftOp) (n : Nat) (i amount : Int) : Option Int :=
  match op with
  | .left => if i + amount < n then some (i + amount) else none
  | .right => if i < amount then none else some (i - amount)
  | .rotateLeft => some ((i + amount) % n)
  | .rotateRight => some ((i - amount) % n)

namespace Expr

/-- One selected bit of a dynamic shift or rotation. -/
@[expose] def shiftBody {Γ : List ClosedTy} {n : Nat} (op : ShiftOp)
    (xs : Expr Γ (wordTy n)) (amount i : Expr Γ .integer) : Expr Γ .bit :=
  match op with
  | .left => .ite (.intLt (.intOp .add i amount) (.integer n))
      (.index xs (.intOp .add i amount)) (.bit false)
  | .right => .ite (.intLt i amount) (.bit false)
      (.index xs (.intOp .sub i amount))
  | .rotateLeft => .index xs (euclideanMod n (.intOp .add i amount))
  | .rotateRight => .index xs (euclideanMod n (.intOp .sub i amount))

/-- A dynamic movement operation, strict in the amount and lazy in source bits. -/
@[expose] def shift {Γ : List ClosedTy} {n : Nat} (op : ShiftOp)
    (xs : Expr Γ (wordTy n)) (amount : Expr Γ .integer) : Expr Γ (wordTy n) :=
  .force amount (if n = 0 ∧ op.preservesEmpty = true then xs else
    .generate (.finite n) (shiftBody op xs.weaken amount.weaken (.var .zero)))

end Expr

namespace Semantics

/-- Sequence construction once the shift amount is known. -/
@[expose] noncomputable def shiftedWord (op : ShiftOp) (n : Nat) (k : Int) :
    Computation (wordTy n) →𝒄 Computation (wordTy n) :=
  if n = 0 ∧ op.preservesEmpty = true then .id else
    .ofFun (fun xs => DomainResult.valueContinuous (fun i : Fin n =>
      match op.position n i.val k with
      | none => .value ⟨false⟩
      | some j => indexAt xs j)) (by
      apply DomainResult.valueContinuous.ωScottContinuous.comp
      apply ωScottContinuous.of_apply₂
      intro i
      cases op.position n i.val k <;> fun_prop)

/-- Direct reference semantics, with an integer amount and suspended source. -/
@[expose] noncomputable def shift (op : ShiftOp) (n : Nat) :
    Computation (wordTy n) →𝒄 (Computation .integer →𝒄 Computation (wordTy n)) :=
  .ofFun (fun xs => DomainResult.bind
    (DiscreteOrder.continuousMap fun k : Int => shiftedWord op n k xs))

theorem shift_value (op : ShiftOp) (n : Nat) (xs : Computation (wordTy n)) (k : Int) :
    shift op n xs (.value ⟨k⟩) = shiftedWord op n k xs := rfl

/-- A fixed nonnegative left rotation, using the unsigned index formula. -/
@[expose] noncomputable def rotateLeftFixed (n amount : Nat) :
    Computation (wordTy n) →𝒄 Computation (wordTy n) :=
  if n = 0 then .id else .ofFun (fun xs => DomainResult.valueContinuous
    (fun i : Fin n => indexAt xs (((i.val : Int) + amount).tmod n)))

/-- Direct semantics of nonnegative, statically instantiated movement operations. -/
@[expose] noncomputable def shiftFixed (op : ShiftOp) (n amount : Nat) :
    Computation (wordTy n) →𝒄 Computation (wordTy n) :=
  match op with
  | .left => .ofFun (fun xs => DomainResult.valueContinuous (fun i : Fin n =>
      if (i.val : Int) + amount < n then indexAt xs ((i.val : Int) + amount)
      else .value ⟨false⟩))
  | .right => .ofFun (fun xs => DomainResult.valueContinuous (fun i : Fin n =>
      if (i.val : Int) < amount then .value ⟨false⟩
      else indexAt xs ((i.val : Int) - amount)))
  | .rotateLeft => rotateLeftFixed n amount
  | .rotateRight => rotateLeftFixed n (n - amount % n)

/-- Fixed nonnegative movements agree with the dynamic reference operation on partial inputs. -/
theorem shiftFixed_eq_shift (op : ShiftOp) (n amount : Nat) (xs : Computation (wordTy n)) :
    shiftFixed op n amount xs = shift op n xs (.value ⟨(amount : Int)⟩) := by
  rw [shift_value]
  cases op with
  | left =>
      simp only [shiftFixed, shiftedWord, ShiftOp.preservesEmpty, Bool.false_eq_true,
        and_false, ite_false]
      apply congrArg DomainResult.value
      funext i
      change (if _ then _ else _) = (match ShiftOp.left.position _ _ _ with
        | none => _ | some _ => _)
      unfold ShiftOp.position
      split <;> rfl
  | right =>
      simp only [shiftFixed, shiftedWord, ShiftOp.preservesEmpty, Bool.false_eq_true,
        and_false, ite_false]
      apply congrArg DomainResult.value
      funext i
      change (if _ then _ else _) = (match ShiftOp.right.position _ _ _ with
        | none => _ | some _ => _)
      unfold ShiftOp.position
      split <;> rfl
  | rotateLeft =>
      cases n with
      | zero => rfl
      | succ n =>
          change DomainResult.value (fun i : Fin (n + 1) =>
            indexAt xs (((i.val : Int) + amount).tmod (n + 1))) =
            DomainResult.value (fun i : Fin (n + 1) =>
              indexAt xs (((i.val : Int) + amount) % (n + 1)))
          apply congrArg DomainResult.value
          funext i
          rw [Int.tmod_eq_emod_of_nonneg (by omega)]
  | rotateRight =>
      cases n with
      | zero => rfl
      | succ n =>
          change DomainResult.value (fun i : Fin (n + 1) =>
            indexAt xs (((i.val : Int) + (n + 1 - amount % (n + 1) : Nat)).tmod (n + 1))) =
            DomainResult.value (fun i : Fin (n + 1) =>
              indexAt xs (((i.val : Int) - amount) % (n + 1)))
          apply congrArg DomainResult.value
          funext i
          rw [Int.tmod_eq_emod_of_nonneg (by omega)]
          rw [Int.ofNat_sub (Nat.le_of_lt (Nat.mod_lt _ (Nat.succ_pos n)))]
          simp only [Int.natCast_succ, Int.natCast_emod, ← Int.add_sub_assoc, Int.sub_emod,
            Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]

end Semantics

namespace Expr

/-- Static movement operations preserve native operator identity at the source boundary. -/
@[expose] def shiftFixed {Γ : List ClosedTy} {n : Nat} (op : ShiftOp) (amount : Nat)
    (xs : Expr Γ (wordTy n)) : Expr Γ (wordTy n) :=
  match op with
  | .left => xs.shiftLeft amount
  | .right => xs.shiftRight amount
  | .rotateLeft => xs.rotateLeft amount
  | .rotateRight => xs.rotateRight amount

theorem denote_rotateLeftFixed {Γ : List ClosedTy} {n : Nat} (amount : Nat)
    (xs : Expr Γ (wordTy n)) (η : Environment Γ) :
    (xs.rotateLeft amount).denote η = Semantics.rotateLeftFixed n amount (xs.denote η) := by
  by_cases hn : n = 0
  · simp only [rotateLeft, Semantics.rotateLeftFixed, hn, ↓reduceIte]; rfl
  · simp only [rotateLeft, Semantics.rotateLeftFixed, hn, ↓reduceIte]
    apply congrArg DomainResult.value
    funext i
    simp only [Environment.extendContinuous_apply, denote_index, denote_weaken, denote_intOp,
      denote_var, denote_integer]
    change Semantics.index (xs.denote η)
      (ofExcept (IntOp.mod.eval ((i.val : Int) + amount) n)) = _
    have hn' : (n : Int) ≠ 0 := by omega
    simp only [IntOp.eval, hn', ↓reduceIte, ofExcept]
    rfl

/-- The static lowering preserves partial source words at every width. -/
theorem denote_shiftFixed {Γ : List ClosedTy} {n : Nat} (op : ShiftOp) (amount : Nat)
    (xs : Expr Γ (wordTy n)) (η : Environment Γ) :
    (shiftFixed op amount xs).denote η = Semantics.shiftFixed op n amount (xs.denote η) := by
  cases op with
  | left =>
      apply congrArg DomainResult.value
      funext i
      simp only [Environment.extendContinuous_apply, denote_ite, denote_index, denote_weaken,
        denote_intOp, denote_intLt, denote_var, denote_integer]
      change Semantics.conditional _ (.value ⟨decide ((i.val : Int) + amount < n)⟩) = _
      rw [Semantics.conditional_value]
      simp only [decide_eq_true_eq]
      split <;> rfl
  | right =>
      apply congrArg DomainResult.value
      funext i
      simp only [Environment.extendContinuous_apply, denote_ite, denote_index, denote_weaken,
        denote_intOp, denote_intLt, denote_var, denote_integer]
      change Semantics.conditional _ (.value ⟨decide ((i.val : Int) < amount)⟩) = _
      rw [Semantics.conditional_value]
      simp only [decide_eq_true_eq]
      split <;> rfl
  | rotateLeft => exact denote_rotateLeftFixed _ _ _
  | rotateRight => exact denote_rotateLeftFixed _ _ _

theorem denote_shiftBody {Γ : List ClosedTy} {n : Nat} (op : ShiftOp)
    (xs : Expr Γ (wordTy n)) (amount idx : Expr Γ .integer) (η : Environment Γ)
    (k : Int) (i : Fin n) (hk : amount.denote η = .value ⟨k⟩)
    (hi : idx.denote η = .value ⟨(i.val : Int)⟩) :
    (shiftBody op xs amount idx).denote η =
      match op.position n i.val k with
      | none => .value ⟨false⟩
      | some j => Semantics.indexAt (xs.denote η) j := by
  cases op with
  | left =>
      simp only [shiftBody, denote_ite, denote_index, denote_intLt, denote_intOp,
        denote_integer, hi, hk]
      change Semantics.conditional _ (.value ⟨decide ((i.val : Int) + k < n)⟩) = _
      rw [Semantics.conditional_value]
      simp only [decide_eq_true_eq, ShiftOp.position]
      split <;> rfl
  | right =>
      simp only [shiftBody, denote_ite, denote_index, denote_intLt, denote_intOp, hi, hk]
      change Semantics.conditional _ (.value ⟨decide ((i.val : Int) < k)⟩) = _
      rw [Semantics.conditional_value]
      simp only [decide_eq_true_eq, ShiftOp.position]
      split <;> rfl
  | rotateLeft =>
      rw [shiftBody, denote_index, denote_euclideanMod _ η ((i.val : Int) + k)
        (by rw [denote_intOp, hi, hk]; rfl) n (by have := i.isLt; omega)]
      rfl
  | rotateRight =>
      rw [shiftBody, denote_index, denote_euclideanMod _ η ((i.val : Int) - k)
        (by rw [denote_intOp, hi, hk]; rfl) n (by have := i.isLt; omega)]
      rfl

/-- Lowering preserves arbitrary partial sources and amounts. -/
theorem denote_shift {Γ : List ClosedTy} {n : Nat} (op : ShiftOp)
    (xs : Expr Γ (wordTy n)) (amount : Expr Γ .integer) (η : Environment Γ) :
    (shift op xs amount).denote η =
      Semantics.shift op n (xs.denote η) (amount.denote η) := by
  generalize hk : amount.denote η = d
  induction d using DomainResult.inductionOn with
  | bot =>
      change DomainResult.force (amount.denote η) _ = _
      rw [hk]
      rfl
  | error err =>
      change DomainResult.force (amount.denote η) _ = _
      rw [hk]
      rfl
  | value k =>
      obtain ⟨k⟩ := k
      change DomainResult.force (amount.denote η) _ = _
      rw [hk]
      rw [DomainResult.force_value]
      rw [Semantics.shift_value, Semantics.shiftedWord]
      change (if n = 0 ∧ op.preservesEmpty = true then xs else _).denote η = _
      by_cases h : n = 0 ∧ op.preservesEmpty = true
      · simp only [h]; rfl
      · simp only [h, ↓reduceIte]
        apply congrArg DomainResult.value
        funext i
        simpa only [denote_weaken, Environment.extendContinuous_apply, Length.indexNat] using
          denote_shiftBody op xs.weaken amount.weaken (.var .zero)
            (η.extend (.value ⟨(i.val : Int)⟩)) k i
            (by simpa only [denote_weaken] using hk) rfl

end Expr

end Interop.Cryptol
