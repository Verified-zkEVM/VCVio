/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Words

/-!
# Word operations and total representations

Word constructors preserve the lazy core's demand behavior. The representation
lemmas explicitly assume fully defined operands; they do not identify partial
words with bitvectors.
-/

public section

namespace Interop.Cryptol

namespace Expr

variable {Γ : List ClosedTy} {n : Nat}

/-- Pointwise logic demands both outer operands and leaves output elements lazy. -/
@[expose] def wordBitOp (op : BitOp) (x y : Expr Γ (.seq (.finite n) .bit)) :
    Expr Γ (.seq (.finite n) .bit) :=
  .force x (.force y (.generate (.finite n) (.bitOp op (.index x.weaken (.var .zero))
    (.index y.weaken (.var .zero)))))

/-- Pointwise complement, lazy in each output element. -/
@[expose] def wordNot (x : Expr Γ (.seq (.finite n) .bit)) :
    Expr Γ (.seq (.finite n) .bit) :=
  .force x (.generate (.finite n) (.bitNot (.index x.weaken (.var .zero))))

/-- Weakening ignores the fresh environment entry. -/
@[simp] theorem denote_weaken {a b : ClosedTy} (e : Expr Γ a) (η : Environment Γ)
    (x : Computation b) : e.weaken.denote (η.extend x) = e.denote η := by
  rw [weaken, denote_rename]
  rfl

/-- An in-range observation of a total word returns its represented bit. -/
theorem denote_index_word (e : Expr Γ (.seq (.finite n) .bit)) (η : Environment Γ)
    (x : BitVec n) (h : e.denote η = .value (wordValue x)) (j : Fin n)
    (i : Expr Γ .integer) (hi : i.denote η = .value ⟨(j.val : Int)⟩) :
    (Expr.index e i).denote η = .value ⟨x.getMsbD j.val⟩ := by
  change Semantics.index (e.denote η) (i.denote η) = _
  rw [h, hi, Semantics.index_values]
  simp [Length.checkIndex, j.isLt, wordValue]

/-- Bitwise logic agrees with the corresponding bitvector operation. -/
theorem denote_wordBitOp (op : BitOp) (e f : Expr Γ (.seq (.finite n) .bit))
    (η : Environment Γ) (x y : BitVec n)
    (he : e.denote η = .value (wordValue x))
    (hf : f.denote η = .value (wordValue y)) :
    (wordBitOp op e f).denote η = .value (wordValue (match op with
      | .and => x &&& y | .or => x ||| y | .xor => x ^^^ y)) := by
  change DomainResult.force (e.denote η) (DomainResult.force (f.denote η) _) = _
  rw [he, hf, DomainResult.force_value, DomainResult.force_value]
  apply congrArg DomainResult.value
  funext i
  change Semantics.binary (fun a b => .ok (op.eval a b))
    ((Expr.index e.weaken (.var .zero)).denote (η.extend (.value ⟨(i.val : Int)⟩)))
    ((Expr.index f.weaken (.var .zero)).denote (η.extend (.value ⟨(i.val : Int)⟩))) = _
  rw [show (Expr.index e.weaken (.var .zero)).denote
      (η.extend (.value ⟨(i.val : Int)⟩)) = .value ⟨x.getMsbD i.val⟩ from
    denote_index_word _ _ x (by simpa using he) i _ rfl]
  rw [show (Expr.index f.weaken (.var .zero)).denote
      (η.extend (.value ⟨(i.val : Int)⟩)) = .value ⟨y.getMsbD i.val⟩ from
    denote_index_word _ _ y (by simpa using hf) i _ rfl]
  change (DomainResult.value ⟨op.eval (x.getMsbD i.val) (y.getMsbD i.val)⟩ :
    Computation .bit) = _
  cases op <;> simp [BitOp.eval, wordValue]

/-- Complement agrees with bitvector complement on total inputs. -/
theorem denote_wordNot (e : Expr Γ (.seq (.finite n) .bit))
    (η : Environment Γ) (x : BitVec n) (he : e.denote η = .value (wordValue x)) :
    (wordNot e).denote η = .value (wordValue (~~~x)) := by
  change DomainResult.force (e.denote η) _ = _
  rw [he, DomainResult.force_value]
  apply congrArg DomainResult.value
  funext i
  change DomainResult.bind _ ((Expr.index e.weaken (.var .zero)).denote
    (η.extend (.value ⟨(i.val : Int)⟩))) = _
  rw [denote_index_word _ _ x (by simpa using he) i _ rfl]
  change (DomainResult.value ⟨!x.getMsbD i.val⟩ : Computation .bit) = _
  simp [wordValue, i.isLt]

/-- A zero-width rotation preserves even an erroneous or divergent input. -/
@[simp] theorem rotateLeft_zero (amount : Nat) (e : Expr Γ (.seq (.finite 0) .bit)) :
    rotateLeft amount e = e := by simp [rotateLeft]

/-- A zero-width right rotation preserves its input computation. -/
@[simp] theorem rotateRight_zero (amount : Nat) (e : Expr Γ (.seq (.finite 0) .bit)) :
    rotateRight amount e = e := by simp [rotateRight]

/-- Left rotation preserves the total bitvector representation at every width. -/
theorem denote_rotateLeft (amount : Nat) (e : Expr Γ (.seq (.finite n) .bit))
    (η : Environment Γ) (x : BitVec n) (he : e.denote η = .value (wordValue x)) :
    (rotateLeft amount e).denote η = .value (wordValue (x.rotateLeft amount)) := by
  by_cases hn : n = 0
  · subst n
    rw [rotateLeft_zero, he]
    congr 2
    exact Subsingleton.elim _ _
  · rw [rotateLeft, ite_eq_right hn]
    apply congrArg DomainResult.value
    funext i
    let j : Fin n := ⟨(i.val + amount) % n, Nat.mod_lt _ (by omega)⟩
    have hi : (Expr.intOp .mod (.intOp .add (.var .zero) (.integer amount))
        (.integer n) : Expr (.integer :: Γ) .integer).denote
        (η.extend (.value ⟨(i.val : Int)⟩)) = .value ⟨(j.val : Int)⟩ := by
      change ofExcept (IntOp.mod.eval ((i.val : Int) + amount) n) = _
      simp [IntOp.eval, hn, ofExcept, j,
        Int.tmod_eq_emod_of_nonneg (show 0 ≤ (i.val : Int) + amount by omega),
        Int.natCast_emod]
    change (Expr.index e.weaken (.intOp .mod
      (.intOp .add (.var .zero) (.integer amount)) (.integer n))).denote
      (η.extend (.value ⟨(i.val : Int)⟩)) = _
    rw [denote_index_word _ _ x (by simpa using he) j _ hi]
    simp [wordValue, BitVec.getMsbD_rotateLeft, i.isLt, j, Nat.add_comm]

/-- Right rotation is left rotation by the complementary residue. -/
theorem bitvec_rotateRight_eq (x : BitVec n) (amount : Nat) :
    x.rotateRight amount = x.rotateLeft (n - amount % n) := by
  apply BitVec.eq_of_getMsbD_eq
  intro i hi
  have hn : 0 < n := by omega
  have hm := Nat.mod_lt amount hn
  rw [BitVec.getMsbD_rotateRight, BitVec.getMsbD_rotateLeft]
  simp only [hi, decide_true, Bool.true_and]
  split
  · apply congrArg (fun j => x.getMsbD (j % n))
    omega
  · apply congrArg x.getMsbD
    have h : n - amount % n + i = n + (i - amount % n) := by omega
    calc
      i - amount % n = (i - amount % n) % n :=
        (Nat.mod_eq_of_lt (by omega : i - amount % n < n)).symm
      _ = (n - amount % n + i) % n := by rw [h, Nat.add_mod_left]

/-- Right rotation preserves the total bitvector representation. -/
theorem denote_rotateRight (amount : Nat) (e : Expr Γ (.seq (.finite n) .bit))
    (η : Environment Γ) (x : BitVec n) (he : e.denote η = .value (wordValue x)) :
    (rotateRight amount e).denote η = .value (wordValue (x.rotateRight amount)) := by
  rw [rotateRight, denote_rotateLeft _ _ _ _ he, bitvec_rotateRight_eq]

/-- Rotation distributes over pointwise exclusive-or. -/
theorem bitvec_rotateRight_xor (x y : BitVec n) (amount : Nat) :
    (x ^^^ y).rotateRight amount = x.rotateRight amount ^^^ y.rotateRight amount := by
  simp only [bitvec_rotateRight_eq]
  apply BitVec.eq_of_getMsbD_eq
  intro i hi
  simp [BitVec.getMsbD_rotateLeft, hi]

/-- Logical left shift fills out-of-range positions with zero. -/
theorem denote_shiftLeft (amount : Nat) (e : Expr Γ (.seq (.finite n) .bit))
    (η : Environment Γ) (x : BitVec n) (he : e.denote η = .value (wordValue x)) :
    (shiftLeft amount e).denote η = .value (wordValue (x <<< amount)) := by
  apply congrArg DomainResult.value
  funext i
  change Semantics.conditional _ (ofExcept (.ok (decide ((i.val : Int) + amount < n)))) = _
  by_cases h : i.val + amount < n
  · have ht : (i.val : Int) + amount < n := by omega
    simp only [ht, decide_true]
    change (Expr.index e.weaken (.intOp .add (.var .zero) (.integer amount))).denote
      (η.extend (.value ⟨(i.val : Int)⟩)) = _
    rw [denote_index_word _ _ x (by simpa using he) ⟨i.val + amount, h⟩ _
      (by change ofExcept (.ok ((i.val : Int) + amount)) = _; simp [ofExcept])]
    simp [wordValue]
  · have ht : ¬ (i.val : Int) + amount < n := by omega
    simp only [ht, decide_false]
    change (DomainResult.value ⟨false⟩ : Computation .bit) = _
    simp [wordValue, BitVec.getMsbD_of_ge, Nat.le_of_not_lt h]

/-- Logical right shift fills the leading positions with zero. -/
theorem denote_shiftRight (amount : Nat) (e : Expr Γ (.seq (.finite n) .bit))
    (η : Environment Γ) (x : BitVec n) (he : e.denote η = .value (wordValue x)) :
    (shiftRight amount e).denote η = .value (wordValue (x >>> amount)) := by
  apply congrArg DomainResult.value
  funext i
  change Semantics.conditional _ (ofExcept (.ok (decide ((i.val : Int) < amount)))) = _
  by_cases h : i.val < amount
  · have ht : (i.val : Int) < amount := by omega
    simp only [ht, decide_true]
    change (DomainResult.value ⟨false⟩ : Computation .bit) = _
    simp [wordValue, BitVec.getMsbD_ushiftRight, h, i.isLt]
  · have ht : ¬ (i.val : Int) < amount := by omega
    simp only [ht, decide_false]
    change (Expr.index e.weaken (.intOp .sub (.var .zero) (.integer amount))).denote
      (η.extend (.value ⟨(i.val : Int)⟩)) = _
    rw [denote_index_word _ _ x (by simpa using he) ⟨i.val - amount, by omega⟩ _
      (by change ofExcept (.ok ((i.val : Int) - amount)) = _
          simp [ofExcept, Int.natCast_sub (by omega : amount ≤ i.val)])]
    simp [wordValue, BitVec.getMsbD_ushiftRight, h, i.isLt]

/-- Left-to-right conjunction that stops at the first false bit. -/
@[expose] def allBits {α : Type} (p : α → Expr Γ .bit) : List α → Expr Γ .bit
  | [] => .bit true
  | x :: xs => .ite (p x) (allBits p xs) (.bit false)

/-- A finite conjunction preserves fully defined Boolean results. -/
theorem denote_allBits {α : Type} (p : α → Expr Γ .bit) (b : α → Bool)
    (xs : List α) (η : Environment Γ)
    (h : ∀ x ∈ xs, (p x).denote η = .value ⟨b x⟩) :
    (allBits p xs).denote η = .value ⟨xs.all b⟩ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change Semantics.conditional (((allBits p xs).denote η), .value ⟨false⟩)
        ((p x).denote η) = _
      rw [h x (by simp), ih (fun x hx => h x (by simp [hx]))]
      simp only [List.all_cons]
      cases b x <;> rfl

/-- Equality demands both outer words and stops at the first unequal bit. -/
@[expose] def wordEq (x y : Expr Γ (.seq (.finite n) .bit)) : Expr Γ .bit :=
  .force x (.force y (allBits (fun i : Fin n => .bitNot (.bitOp .xor
    (.index x (.integer i.val)) (.index y (.integer i.val)))) (List.finRange n)))

/-- Word equality agrees with bitvector equality for fully defined operands. -/
theorem denote_wordEq (e f : Expr Γ (.seq (.finite n) .bit))
    (η : Environment Γ) (x y : BitVec n)
    (he : e.denote η = .value (wordValue x))
    (hf : f.denote η = .value (wordValue y)) :
    (wordEq e f).denote η = .value ⟨x == y⟩ := by
  change DomainResult.force (e.denote η) (DomainResult.force (f.denote η) _) = _
  rw [he, hf, DomainResult.force_value, DomainResult.force_value]
  rw [denote_allBits _ (fun i => !(x.getMsbD i.val ^^ y.getMsbD i.val)) _ η (by
    intro i _
    change DomainResult.bind _ (Semantics.binary _
      ((Expr.index e (.integer i.val)).denote η)
      ((Expr.index f (.integer i.val)).denote η)) = _
    rw [denote_index_word _ _ _ he i _ rfl, denote_index_word _ _ _ hf i _ rfl]
    rfl)]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, beq_iff_eq]
  constructor
  · intro h
    apply BitVec.eq_of_getMsbD_eq
    intro i hi
    have hh := h ⟨i, hi⟩ (by simp)
    cases hx : x.getMsbD i <;> cases hy : y.getMsbD i <;> simp_all
  · intro h
    subst y
    simp

end Expr

end Interop.Cryptol
