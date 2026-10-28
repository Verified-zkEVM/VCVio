/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.FinEnum

/-!
 # Finite representations and discrete-log relations

Explicit coefficient witnesses transport along embeddings, arise from representation collisions,
and discharge against known logarithms. The statements follow the general algebra in ironwood's
`Zcash/Common/DiscreteLogRelation.lean`; no assumption about algebraic adversaries is needed.
-/

public section

namespace DiscreteLogRelation

variable {F G ι ι' : Type*}

/-- Evaluate coefficients against a finite family of group elements. -/
@[expose] def representationEval [Fintype ι] [Semiring F] [AddCommMonoid G] [Module F G]
    (basis : ι → G) (coeffs : ι → F) : G := ∑ i, coeffs i • basis i

/-- Subtraction of coefficients subtracts the represented group elements. -/
theorem representationEval_sub [Fintype ι] [Ring F] [AddCommGroup G] [Module F G]
    (basis : ι → G) (a b : ι → F) :
    representationEval basis (a - b) = representationEval basis a - representationEval basis b := by
  simp [representationEval, sub_smul, Finset.sum_sub_distrib]

/-- Evaluation on a disjoint union is the sum of the two evaluations. -/
theorem representationEval_sum [Fintype ι] [Fintype ι']
    [Semiring F] [AddCommMonoid G] [Module F G]
    (basis : ι → G) (basis' : ι' → G) (a : ι → F) (b : ι' → F) :
    representationEval (Sum.elim basis basis') (Sum.elim a b) =
      representationEval basis a + representationEval basis' b := by
  simp [representationEval, Fintype.sum_sum_type]

/-- Explicit nonzero coefficients evaluating to zero over a presented basis.
This is the general witness of ironwood `Zcash/Common/DiscreteLogRelation.lean`. -/
structure RelationWitness [Fintype ι] [Semiring F] [AddCommMonoid G] [Module F G]
    (basis : ι → G) where
  /-- The computed coefficient vector. -/
  coeffs : ι → F
  /-- At least one coefficient is nonzero. -/
  nonzero : coeffs ≠ 0
  /-- The linear combination vanishes. -/
  relation : representationEval basis coeffs = 0

/-- A relation has a nonzero coefficient at some slot. -/
theorem RelationWitness.exists_coeff_ne_zero [Fintype ι]
    [Semiring F] [AddCommMonoid G] [Module F G] {basis : ι → G}
    (r : RelationWitness (F := F) basis) : ∃ i, r.coeffs i ≠ 0 := by
  simpa only [Function.ne_iff, Pi.zero_apply] using r.nonzero

/-- Zero-extend coefficients along an injection, without choosing an inverse. -/
@[expose] def embedCoeffs [Fintype ι] [DecidableEq ι'] [AddCommMonoid F]
    (e : ι ↪ ι') (a : ι → F) : ι' → F := fun j => ∑ i, if e i = j then a i else 0

/-- Zero-extension preserves the coefficient at each embedded slot. -/
@[simp] theorem embedCoeffs_apply [Fintype ι] [DecidableEq ι'] [AddCommMonoid F]
    (e : ι ↪ ι') (a : ι → F) (i : ι) : embedCoeffs e a (e i) = a i := by
  classical
  simp [embedCoeffs, e.injective.eq_iff]

/-- Evaluation of zero-extended coefficients is evaluation on the embedded basis. -/
theorem representationEval_embedCoeffs [Fintype ι] [Fintype ι'] [DecidableEq ι']
    [Semiring F] [AddCommMonoid G] [Module F G]
    (e : ι ↪ ι') (basis : ι' → G) (a : ι → F) :
    representationEval basis (embedCoeffs e a) = representationEval (basis ∘ e) a := by
  classical
  simp only [representationEval, embedCoeffs, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp [ite_smul]

/-- Transport a relation into any larger compatible basis by zero-extension.
This is the embedding operation of ironwood `Zcash/Common/DiscreteLogRelation.lean`. -/
@[expose] def RelationWitness.embed [Fintype ι] [Fintype ι'] [DecidableEq ι']
    [Semiring F] [AddCommMonoid G] [Module F G] {basis : ι → G} {basis' : ι' → G}
    (r : RelationWitness (F := F) basis) (e : ι ↪ ι')
    (h : ∀ i, basis' (e i) = basis i) : RelationWitness (F := F) basis' where
  coeffs := embedCoeffs e r.coeffs
  nonzero := by
    intro hz
    apply r.nonzero
    funext i
    simpa using congrFun hz (e i)
  relation := by
    rw [representationEval_embedCoeffs, show basis' ∘ e = basis from funext h]
    exact r.relation

/-- Assemble a relation from two disjoint coefficient families whose evaluations cancel.
This generalizes `NontrivialRelation.ofParts` in ironwood
`Zcash/Common/DiscreteLogRelation.lean`. -/
@[expose] def RelationWitness.ofParts [Fintype ι] [Fintype ι']
    [Semiring F] [AddCommMonoid G] [Module F G]
    (basis : ι → G) (basis' : ι' → G) (a : ι → F) (b : ι' → F)
    (hn : a ≠ 0 ∨ b ≠ 0)
    (h : representationEval basis a + representationEval basis' b = 0) :
    RelationWitness (F := F) (Sum.elim basis basis') where
  coeffs := Sum.elim a b
  nonzero := by
    intro hz
    rcases hn with ha | hb
    · exact ha (funext fun i => congrFun hz (.inl i))
    · exact hb (funext fun i => congrFun hz (.inr i))
  relation := (representationEval_sum basis basis' a b).trans h

/-- Unequal representations of one element give a relation by subtraction.
This generalizes the collision constructors in ironwood `Zcash/Common/DiscreteLogRelation.lean`. -/
@[expose] def RelationWitness.ofCollision [Fintype ι]
    [Ring F] [AddCommGroup G] [Module F G] (basis : ι → G) (a b : ι → F)
    (hne : a ≠ b) (h : representationEval basis a = representationEval basis b) :
    RelationWitness (F := F) basis where
  coeffs := a - b
  nonzero := sub_ne_zero.mpr hne
  relation := by rw [representationEval_sub, h, sub_self]

/-- A computed scalar whose multiple of the base is the target. -/
structure DiscreteLogWitness [Semiring F] [AddCommMonoid G] [Module F G] (base target : G) where
  /-- The extracted logarithm. -/
  log : F
  /-- The extracted logarithm represents the target. -/
  smul_eq : log • base = target

/-- The scalar contribution of all slots other than one designated challenge.
This is `relationLogExcept` of ironwood `Zcash/Common/DiscreteLogRelation.lean`. -/
@[expose] def relationLogExcept [Fintype ι] [DecidableEq ι] [Semiring F]
    (logs coeffs : ι → F) (challenge : ι) : F :=
  ∑ i ∈ Finset.univ.erase challenge, coeffs i * logs i

/-- Split a representation into its challenge term and the known logarithmic contribution.
The statement follows ironwood `Zcash/Common/DiscreteLogRelation.lean`. -/
theorem representationEval_eq_challenge_add_known [Fintype ι] [DecidableEq ι]
    [Semiring F] [AddCommMonoid G] [Module F G]
    (base : G) (basis : ι → G) (logs coeffs : ι → F) (challenge : ι)
    (hknown : ∀ i, i ≠ challenge → basis i = logs i • base) :
    representationEval basis coeffs =
      coeffs challenge • basis challenge + relationLogExcept logs coeffs challenge • base := by
  rw [representationEval, ← Finset.add_sum_erase _ _ (Finset.mem_univ challenge)]
  congr 1
  simp only [relationLogExcept, Finset.sum_smul]
  exact Finset.sum_congr rfl fun i hi => by
    rw [hknown i (Finset.mem_erase.mp hi).1, smul_smul]

/-- A nonzero challenge coefficient extracts its logarithm from the known logs of other slots.
This is the basis-generic discharger in ironwood `Zcash/Common/DiscreteLogRelation.lean`. -/
@[expose] def RelationWitness.extractLog [Fintype ι] [DecidableEq ι]
    [Field F] [AddCommGroup G] [Module F G]
    {basis : ι → G} (r : RelationWitness (F := F) basis)
    (base : G) (logs : ι → F) (challenge : ι)
    (hknown : ∀ i, i ≠ challenge → basis i = logs i • base)
    (hc : r.coeffs challenge ≠ 0) : DiscreteLogWitness (F := F) base (basis challenge) where
  log := -(relationLogExcept logs r.coeffs challenge) / r.coeffs challenge
  smul_eq := by
    have h := r.relation
    rw [representationEval_eq_challenge_add_known base basis logs _ challenge hknown] at h
    have he := congrArg (fun z : G => (r.coeffs challenge)⁻¹ • z)
      (eq_neg_of_add_eq_zero_left h)
    simpa [smul_smul, hc, div_eq_mul_inv, mul_comm, neg_smul] using he.symm

/-- Delete a zero-coefficient slot, retaining a nontrivial relation on the remaining slots. -/
@[expose] def RelationWitness.erase [Fintype ι] [DecidableEq ι]
    [Semiring F] [AddCommMonoid G] [Module F G]
    {basis : ι → G} (r : RelationWitness (F := F) basis) (challenge : ι)
    (hc : r.coeffs challenge = 0) :
    RelationWitness (F := F) (fun i : {i // i ≠ challenge} => basis i) where
  coeffs := fun i => r.coeffs i
  nonzero := by
    intro hz
    apply r.nonzero
    funext i
    by_cases hi : i = challenge
    · simpa [hi] using hc
    · exact congrFun hz ⟨i, hi⟩
  relation := by
    rw [representationEval, ← Finset.sum_subtype (Finset.univ.erase challenge)
      (by simp) (fun i => r.coeffs i • basis i)]
    have h := r.relation
    rw [representationEval, ← Finset.add_sum_erase _ _ (Finset.mem_univ challenge), hc,
      zero_smul, zero_add] at h
    exact h

/-- A relation either deletes the challenge slot or computes its discrete logarithm.
The branch retains the returned relation's coefficients; it does not choose a new relation. -/
@[expose] def RelationWitness.discharge [Fintype ι] [DecidableEq ι] [DecidableEq F]
    [Field F] [AddCommGroup G] [Module F G]
    {basis : ι → G} (r : RelationWitness (F := F) basis)
    (base : G) (logs : ι → F) (challenge : ι)
    (hknown : ∀ i, i ≠ challenge → basis i = logs i • base) :
    RelationWitness (F := F) (fun i : {i // i ≠ challenge} => basis i) ⊕
      DiscreteLogWitness (F := F) base (basis challenge) :=
  if hc : r.coeffs challenge = 0 then .inl (r.erase challenge hc)
  else .inr (r.extractLog base logs challenge hknown hc)

end DiscreteLogRelation
