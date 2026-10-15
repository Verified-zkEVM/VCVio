/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.WordOps
public import Interop.Cryptol.Model.Laws

/-!
# Structural sequence operations

Lengths encode the primitive's actual Cryptol type, including empty and
infinite dimensions. Constructors suspend their source; observations demand
only the components selected by the reference evaluator.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol

namespace Expr

variable {Γ : List ClosedTy} {a : ClosedTy}

/-- A prefix whose length is checked by the source type. -/
@[expose] def take (front back : Length) (xs : Expr Γ (.seq (front.add back) a)) :
    Expr Γ (.seq front a) := .generate front (.index xs.weaken (.var .zero))

/-- Remove a finite prefix from a sequence or stream. -/
@[expose] def drop (front : Nat) (back : Length)
    (xs : Expr Γ (.seq ((Length.finite front).add back) a)) : Expr Γ (.seq back a) :=
  .generate back (.index xs.weaken (.intOp .add (.integer front) (.var .zero)))

/-- Reverse a finite sequence without demanding any elements in advance. -/
@[expose] def reverse {n : Nat} (xs : Expr Γ (.seq (.finite n) a)) :
    Expr Γ (.seq (.finite n) a) :=
  .generate (.finite n) (.index xs.weaken
    (.intOp .sub (.integer ((n : Int) - 1)) (.var .zero)))

/-- Flatten finitely sized rows from a finite or infinite sequence. -/
@[expose] def join (parts : Length) (each : Nat)
    (xs : Expr Γ (.seq parts (.seq (.finite each) a))) :
    Expr Γ (.seq (parts.mul (.finite each)) a) :=
  .generate (parts.mul (.finite each))
    (.index (.index xs.weaken (.intOp .div (.var .zero) (.integer each)))
      (.intOp .mod (.var .zero) (.integer each)))

/-- Split a sequence into lazily generated rows of a finite size. -/
@[expose] def split (parts : Length) (each : Nat)
    (xs : Expr Γ (.seq (parts.mul (.finite each)) a)) :
    Expr Γ (.seq parts (.seq (.finite each) a)) :=
  .generate parts (.generate (.finite each) (.index xs.weaken.weaken
    (.intOp .add (.intOp .mul (.var (.succ .zero)) (.integer each)) (.var .zero))))

/-- Transpose a rectangular sequence, including finite and infinite dimensions. -/
@[expose] def transpose (rows cols : Length) (xs : Expr Γ (.seq rows (.seq cols a))) :
    Expr Γ (.seq cols (.seq rows a)) :=
  .generate cols (.generate rows (.index (.index xs.weaken.weaken (.var .zero))
    (.var (.succ .zero))))

/-- A dynamic invalid-index error with the original index payload. -/
@[expose] def invalidIndex (i : Expr Γ .integer) : Expr Γ a :=
  .index (.generate (.finite 0) (.error (.user "unreachable"))) i

/-- Update's upper-bound test in Cryptol 3.6.0's reference evaluator.
Negative integer indices pass this test; no nonnegative position then matches. -/
@[expose] def updateInBounds (l : Length) (i : Expr Γ .integer) : Expr Γ .bit :=
  match l with
  | .finite n => .intLt i (.integer n)
  | .infinite => .bit true

/-- Replace one element, demanding the index before constructing the result. -/
@[expose] def update {l : Length} (xs : Expr Γ (.seq l a)) (i : Expr Γ .integer)
    (value : Expr Γ a) : Expr Γ (.seq l a) :=
  .force i (.ite (updateInBounds l i)
    (.generate l (.ite (.intEq (.var .zero) i.weaken) value.weaken
      (.index xs.weaken (.var .zero)))) (invalidIndex i))

/-- Index from the back, preserving the original invalid-index payload. -/
@[expose] def indexEnd {n : Nat} (xs : Expr Γ (.seq (.finite n) a))
    (i : Expr Γ .integer) : Expr Γ a :=
  .force xs (.force i (.ite (.intLt i (.integer 0)) (invalidIndex i)
    (.ite (.intLt i (.integer n))
      (.index xs (.intOp .sub (.integer ((n : Int) - 1)) i)) (invalidIndex i))))

/-- Replace a position counted from the end of a finite sequence. -/
@[expose] def updateEnd {n : Nat} (xs : Expr Γ (.seq (.finite n) a))
    (i : Expr Γ .integer) (value : Expr Γ a) : Expr Γ (.seq (.finite n) a) :=
  .force i (.ite (updateInBounds (.finite n) i)
    (.generate (.finite n) (.ite (.intEq (.var .zero)
      (.intOp .sub (.integer ((n : Int) - 1)) i.weaken)) value.weaken
      (.index xs.weaken (.var .zero)))) (invalidIndex i))

end Expr

namespace Semantics

/-- A known integer index, still checking the outer sequence and its bounds. -/
@[expose] noncomputable def indexAt {l : Length} {a : ClosedTy} (xs : Computation (.seq l a))
    (i : Int) : Computation a := index xs (.value ⟨i⟩)

@[fun_prop] theorem continuous_indexAt {l : Length} {a : ClosedTy} (i : Int) :
    ωScottContinuous (fun xs : Computation (.seq l a) => indexAt xs i) := by
  unfold indexAt
  fun_prop

/-- Concatenation chooses a suspended source only when an element is requested. -/
@[expose] noncomputable def append {a : ClosedTy} (front : Nat) (back : Length) :
    Computation (.seq (.finite front) a) →𝒄 (Computation (.seq back a) →𝒄
      Computation (.seq ((Length.finite front).add back) a)) :=
  .ofFun (fun xs => .ofFun (fun ys => DomainResult.valueContinuous
    (fun i => if Length.indexNat i < front then indexAt xs (Length.indexNat i)
      else indexAt ys ((Length.indexNat i : Int) - front))))

/-- Prefix selection is non-strict in its source until an element is selected. -/
@[expose] noncomputable def take {a : ClosedTy} (front back : Length) :
    Computation (.seq (front.add back) a) →𝒄 Computation (.seq front a) :=
  .ofFun (fun xs => DomainResult.valueContinuous
    (fun i : front.Index => indexAt xs (Length.indexNat i)))

/-- Suffix selection after a finite prefix. -/
@[expose] noncomputable def drop {a : ClosedTy} (front : Nat) (back : Length) :
    Computation (.seq ((Length.finite front).add back) a) →𝒄 Computation (.seq back a) :=
  .ofFun (fun xs => DomainResult.valueContinuous
    (fun i : back.Index => indexAt xs ((front : Int) + Length.indexNat i)))

/-- Reverse indexing into a suspended finite source. -/
@[expose] noncomputable def reverse {a : ClosedTy} (n : Nat) :
    Computation (.seq (.finite n) a) →𝒄 Computation (.seq (.finite n) a) :=
  .ofFun (fun xs => DomainResult.valueContinuous
    (fun i : Fin n => indexAt xs ((n : Int) - 1 - i.val)))

/-- Reference flattening by quotient and remainder of the requested index. -/
@[expose] noncomputable def join {a : ClosedTy} (parts : Length) (each : Nat) :
    Computation (.seq parts (.seq (.finite each) a)) →𝒄
      Computation (.seq (parts.mul (.finite each)) a) :=
  .ofFun (fun xs => DomainResult.valueContinuous (fun i =>
    indexAt (indexAt xs ((Length.indexNat i : Int).tdiv each))
      ((Length.indexNat i : Int).tmod each)))

/-- Each row is available before any source element is demanded. -/
@[expose] noncomputable def split {a : ClosedTy} (parts : Length) (each : Nat) :
    Computation (.seq (parts.mul (.finite each)) a) →𝒄
      Computation (.seq parts (.seq (.finite each) a)) :=
  .ofFun (fun xs => DomainResult.valueContinuous (fun i : parts.Index =>
    DomainResult.valueContinuous (fun j : Fin each =>
      indexAt xs ((Length.indexNat i : Int) * each + j.val))))

/-- Transposition demands only the selected source row and element. -/
@[expose] noncomputable def transpose {a : ClosedTy} (rows cols : Length) :
    Computation (.seq rows (.seq cols a)) →𝒄 Computation (.seq cols (.seq rows a)) :=
  .ofFun (fun xs => DomainResult.valueContinuous (fun c : cols.Index =>
    DomainResult.valueContinuous (fun r : rows.Index =>
      indexAt (indexAt xs (Length.indexNat r)) (Length.indexNat c))))

/-- Reference update checks the upper bound before returning a lazy sequence.
The negative-index behavior is the versioned reference rule. -/
@[expose] noncomputable def update {a : ClosedTy} (l : Length) (fromEnd : Bool := false) :
    Computation (.seq l a) →𝒄 (Computation .integer →𝒄
      (Computation a →𝒄 Computation (.seq l a))) :=
  .ofFun (fun xs => .ofFun (fun i => .ofFun (fun value =>
    DomainResult.bind (DiscreteOrder.continuousMap (fun j : Int =>
      if (match l with | .finite n => decide (j < n) | .infinite => true) then
        DomainResult.valueContinuous (fun k : l.Index =>
          if (Length.indexNat k : Int) =
              (match l, fromEnd with | .finite n, true => (n : Int) - 1 - j | _, _ => j)
          then value else indexAt xs (Length.indexNat k))
      else DomainResult.error (.invalidIndex j))) i)))

/-- A known update index exposes the upper-bound check and selected replacement. -/
theorem update_value {a : ClosedTy} (l : Length) (fromEnd : Bool)
    (xs : Computation (.seq l a)) (j : Int) (value : Computation a) :
    update l fromEnd xs (.value ⟨j⟩) value =
      if (match l with | .finite n => decide (j < n) | .infinite => true) then
        DomainResult.value (fun k : l.Index =>
          if (Length.indexNat k : Int) =
              (match l, fromEnd with | .finite n, true => (n : Int) - 1 - j | _, _ => j)
          then value else indexAt xs (Length.indexNat k))
      else DomainResult.error (.invalidIndex j) := rfl

/-- Reverse indexing first demands the outer source, then validates the original index. -/
@[expose] noncomputable def indexEnd {a : ClosedTy} (n : Nat) :
    Computation (.seq (.finite n) a) →𝒄 (Computation .integer →𝒄 Computation a) :=
  .ofFun (fun xs => .ofFun (fun i => DomainResult.force xs
    (DomainResult.bind (DiscreteOrder.continuousMap (fun j : Int =>
      if 0 ≤ j ∧ j < n then indexAt xs ((n : Int) - 1 - j)
      else DomainResult.error (.invalidIndex j))) i)))

end Semantics

namespace Expr

variable {Γ : List ClosedTy} {a : ClosedTy}

theorem denote_append {front : Nat} {back : Length}
    (xs : Expr Γ (.seq (.finite front) a)) (ys : Expr Γ (.seq back a))
    (η : Environment Γ) : (xs.append ys).denote η =
      Semantics.append front back (xs.denote η) (ys.denote η) := by
  apply congrArg DomainResult.value
  funext i
  simp only [Environment.extendContinuous_apply, denote_ite, denote_index, denote_weaken,
    denote_intOp, denote_integer, denote_var]
  change Semantics.conditional _
    (.value ⟨decide ((Length.indexNat i : Int) < front)⟩) = _
  rw [Semantics.conditional_value]
  simp only [Int.ofNat_lt, decide_eq_true_eq]
  split <;> rfl

/-- The empty sequence produces the original invalid-index payload at every integer. -/
theorem denote_invalidIndex (i : Expr Γ .integer) (η : Environment Γ) (j : Int)
    (hi : i.denote η = .value ⟨j⟩) :
    (invalidIndex (a := a) i).denote η = .error (.invalidIndex j) := by
  simp only [invalidIndex, denote_index, denote_generate, hi]
  rw [Semantics.index_values]
  simp [Length.checkIndex]

theorem denote_update {l : Length} (xs : Expr Γ (.seq l a)) (i : Expr Γ .integer)
    (value : Expr Γ a) (η : Environment Γ) : (xs.update i value).denote η =
      Semantics.update l false (xs.denote η) (i.denote η) (value.denote η) := by
  generalize hi : i.denote η = d
  induction d using DomainResult.inductionOn with
  | bot =>
      change DomainResult.force (i.denote η) _ = _
      rw [hi]
      rfl
  | error err =>
      change DomainResult.force (i.denote η) _ = _
      rw [hi]
      rfl
  | value j =>
      obtain ⟨j⟩ := j
      change DomainResult.force (i.denote η) _ = _
      rw [hi]
      rw [DomainResult.force_value]
      rw [denote_ite]
      rw [Semantics.update_value l false (xs.denote η) j]
      cases l with
      | finite n =>
          change Semantics.conditional _ (Semantics.binary
            (fun x y : Int => .ok (decide (x < y))) (i.denote η) (.value ⟨(n : Int)⟩)) = _
          rw [hi]
          change Semantics.conditional _ (.value ⟨decide (j < n)⟩) = _
          rw [Semantics.conditional_value]
          simp only [decide_eq_true_eq]
          by_cases hj : j < n
          · simp only [hj, ↓reduceIte]
            apply congrArg DomainResult.value
            funext k
            simp only [Environment.extendContinuous_apply, denote_ite, denote_intEq,
              denote_var, denote_weaken, denote_index, hi]
            change Semantics.conditional (value.denote η,
              Semantics.indexAt (xs.denote η) (Length.indexNat k))
                (.value ⟨(Length.indexNat k : Int) == j⟩) = _
            rw [Semantics.conditional_value]
            simp only [beq_iff_eq]
          · simp only [hj, ↓reduceIte]
            exact denote_invalidIndex i η j hi
      | infinite =>
          change Semantics.conditional _ (.value ⟨true⟩) = _
          rw [Semantics.conditional_value]
          apply congrArg DomainResult.value
          funext k
          simp only [Environment.extendContinuous_apply, denote_ite, denote_intEq,
            denote_var, denote_weaken, denote_index, hi]
          change Semantics.conditional (value.denote η,
            Semantics.indexAt (xs.denote η) (Length.indexNat k))
              (.value ⟨(Length.indexNat k : Int) == j⟩) = _
          rw [Semantics.conditional_value]
          simp only [beq_iff_eq]

theorem denote_updateEnd {n : Nat} (xs : Expr Γ (.seq (.finite n) a)) (i : Expr Γ .integer)
    (value : Expr Γ a) (η : Environment Γ) : (xs.updateEnd i value).denote η =
      Semantics.update (.finite n) true (xs.denote η) (i.denote η) (value.denote η) := by
  generalize hi : i.denote η = d
  induction d using DomainResult.inductionOn with
  | bot =>
      change DomainResult.force (i.denote η) _ = _
      rw [hi]
      rfl
  | error err =>
      change DomainResult.force (i.denote η) _ = _
      rw [hi]
      rfl
  | value j =>
      obtain ⟨j⟩ := j
      change DomainResult.force (i.denote η) _ = _
      rw [hi]
      rw [DomainResult.force_value]
      rw [denote_ite]
      rw [Semantics.update_value (.finite n) true (xs.denote η) j]
      change Semantics.conditional _ (Semantics.binary
        (fun x y : Int => .ok (decide (x < y))) (i.denote η) (.value ⟨(n : Int)⟩)) = _
      rw [hi]
      change Semantics.conditional _ (.value ⟨decide (j < n)⟩) = _
      rw [Semantics.conditional_value]
      simp only [decide_eq_true_eq]
      by_cases hj : j < n
      · simp only [hj, ↓reduceIte]
        apply congrArg DomainResult.value
        funext k
        simp only [Environment.extendContinuous_apply, denote_ite, denote_intEq,
          denote_var, denote_weaken, denote_index, denote_intOp, denote_integer, hi]
        change Semantics.conditional (value.denote η,
          Semantics.indexAt (xs.denote η) (Length.indexNat k))
            (.value ⟨(Length.indexNat k : Int) == (n : Int) - 1 - j⟩) = _
        rw [Semantics.conditional_value]
        simp only [beq_iff_eq]
      · simp only [hj, ↓reduceIte]
        exact denote_invalidIndex i η j hi

theorem denote_take (front back : Length) (xs : Expr Γ (.seq (front.add back) a))
    (η : Environment Γ) : (xs.take front back).denote η =
      Semantics.take front back (xs.denote η) := by
  apply congrArg DomainResult.value
  funext i
  simp only [Environment.extendContinuous_apply, denote_index, denote_weaken, denote_var]
  rfl

/-- Reverse indexing validates the original index after demanding the outer source. -/
theorem denote_indexEnd {n : Nat} (xs : Expr Γ (.seq (.finite n) a))
    (i : Expr Γ .integer) (η : Environment Γ) : (xs.indexEnd i).denote η =
      Semantics.indexEnd n (xs.denote η) (i.denote η) := by
  change DomainResult.force (xs.denote η) _ = DomainResult.force (xs.denote η) _
  apply congrArg (DomainResult.force (xs.denote η))
  generalize hi : i.denote η = d
  induction d using DomainResult.inductionOn with
  | bot =>
      change DomainResult.force (i.denote η) _ = _
      rw [hi]
      rfl
  | error err =>
      change DomainResult.force (i.denote η) _ = _
      rw [hi]
      rfl
  | value j =>
      obtain ⟨j⟩ := j
      change DomainResult.force (i.denote η) _ = _
      rw [hi, DomainResult.force_value]
      simp only [denote_ite, denote_intLt, denote_integer, hi]
      change Semantics.conditional _ (.value ⟨decide (j < 0)⟩) =
        if 0 ≤ j ∧ j < n then Semantics.indexAt (xs.denote η) ((n : Int) - 1 - j)
        else DomainResult.error (.invalidIndex j)
      rw [Semantics.conditional_value]
      by_cases hneg : j < 0
      · simp only [hneg, decide_true, ↓reduceIte,
          show ¬ (0 ≤ j ∧ j < n) by omega]
        exact denote_invalidIndex i η j hi
      · simp only [hneg, decide_false, Bool.false_eq_true, ↓reduceIte]
        change Semantics.conditional _ (.value ⟨decide (j < n)⟩) = _
        rw [Semantics.conditional_value]
        by_cases hj : j < n
        · simp only [hj, decide_true, ↓reduceIte,
            show 0 ≤ j ∧ j < n by omega]
          simp only [denote_index, denote_intOp, denote_integer, hi]
          rfl
        · simp only [hj, decide_false, Bool.false_eq_true, ↓reduceIte, and_false]
          exact denote_invalidIndex i η j hi

theorem denote_drop (front : Nat) (back : Length)
    (xs : Expr Γ (.seq ((Length.finite front).add back) a)) (η : Environment Γ) :
    (xs.drop front back).denote η = Semantics.drop front back (xs.denote η) := by
  apply congrArg DomainResult.value
  funext i
  simp only [Environment.extendContinuous_apply, denote_index, denote_weaken, denote_intOp,
    denote_integer, denote_var]
  rfl

theorem denote_reverse {n : Nat} (xs : Expr Γ (.seq (.finite n) a)) (η : Environment Γ) :
    xs.reverse.denote η = Semantics.reverse n (xs.denote η) := by
  apply congrArg DomainResult.value
  funext i
  simp only [Environment.extendContinuous_apply, denote_index, denote_weaken, denote_intOp,
    denote_integer, denote_var]
  rfl

theorem denote_split (parts : Length) (each : Nat)
    (xs : Expr Γ (.seq (parts.mul (.finite each)) a)) (η : Environment Γ) :
    (xs.split parts each).denote η = Semantics.split parts each (xs.denote η) := by
  apply congrArg DomainResult.value
  funext i
  apply congrArg DomainResult.value
  funext j
  simp only [Environment.extendContinuous_apply, denote_index, denote_weaken, denote_intOp,
    denote_integer, denote_var]
  rfl

theorem denote_join (parts : Length) (each : Nat)
    (xs : Expr Γ (.seq parts (.seq (.finite each) a))) (η : Environment Γ) :
    (xs.join parts each).denote η = Semantics.join parts each (xs.denote η) := by
  apply congrArg DomainResult.value
  funext i
  have hn : (each : Int) ≠ 0 := by
    have := Length.each_pos_of_index parts each i
    omega
  simp only [Environment.extendContinuous_apply, denote_index, denote_weaken,
    denote_intOp, denote_integer, denote_var]
  change Semantics.index (Semantics.index (xs.denote η)
    (ofExcept (IntOp.div.eval (Length.indexNat i) each)))
    (ofExcept (IntOp.mod.eval (Length.indexNat i) each)) = _
  simp only [IntOp.eval, hn, ↓reduceIte, ofExcept]
  rfl

theorem denote_transpose (rows cols : Length) (xs : Expr Γ (.seq rows (.seq cols a)))
    (η : Environment Γ) : (xs.transpose rows cols).denote η =
      Semantics.transpose rows cols (xs.denote η) := by
  apply congrArg DomainResult.value
  funext c
  apply congrArg DomainResult.value
  funext r
  simp only [Environment.extendContinuous_apply, denote_index, denote_weaken, denote_var]
  rfl

end Expr

end Interop.Cryptol
