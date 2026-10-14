/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Pure.Norm
public import VCVio.Quantum.Pure.State

/-!
# Subinstruments on pure substates

Subinstruments built from Kraus operators send pure substates to pure substates, so their outcome
measures and post-branch substates can be computed with vectors.

A contraction `K` gives the one-outcome subinstrument `Quantum.SubInstrument.ofContraction K`,
which sends the pure substate of `ψ` to that of `K •ᵥ ψ`; it is lossless when `K` is an isometry,
and sequencing two of them multiplies the operators. A unitary on a fixed register is the special
case `Quantum.SubInstrument.ofUnitary`. For a measurement `Quantum.SubInstrument.ofKraus K`, the
Born rule `Quantum.SubInstrument.outcomeMeasure_ofKraus_ofVector` gives outcome `a` the weight
`‖K a •ᵥ ψ‖ ^ 2` and the post-branch substate of `K a •ᵥ ψ`. Combined with the norm estimates for
vectors, the outcome weights of two input vectors differ on every event by at most
`(‖ψ‖ + ‖φ‖) * ‖ψ - φ‖` (`Quantum.SubInstrument.abs_outcomeMeasure_real_ofKraus_ofVector_sub_le`).

## Main definitions

* `Quantum.SubInstrument.ofContraction K hK`: the subinstrument `ρ ↦ K * ρ * Kᴴ` of a contraction.
* `Quantum.SubInstrument.ofProjective P hP hsum`: the measurement with a complete family of star
  projections.
* `Quantum.SubInstrument.ofUnitary U`: the subinstrument applying a unitary to a register.
-/

public section

open MeasureTheory
open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator
open Matrix

universe u v w

namespace Quantum

namespace SubInstrument

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] {α β : Type*}

/-! ## A single map followed by a continuation -/

/-- On the zero substate every outcome has weight zero. -/
theorem outcomeMeasure_eq_zero_of_matrix_eq_zero [MeasurableSpace α] (p : SubInstrument A B α)
    {ρ : SubState A} (hρ : ρ.matrix = 0) : p.outcomeMeasure ρ = 0 := by
  ext s hs
  simp [outcomeMeasure_apply _ _ hs, hρ]

/-- Each branch of a composite that starts with a single map is the branch of the continuation
after that map. -/
theorem branch_ofMap_bind_apply (Φ : MatrixMap A B) (hcp : Φ.IsCP) (htni : Φ.IsTNI)
    (k : PUnit → SubInstrument B C β) (b : β) :
    ((ofMap Φ hcp htni).bind k).branch b = (k PUnit.unit).branch b ∘ₗ Φ := by
  rw [branch_bind_apply_univ, Fintype.sum_unique]
  rfl

/-- After the unique outcome of a single map, the substate is the image under the map. -/
theorem matrix_post_ofMap (Φ : MatrixMap A B) (hcp : Φ.IsCP) (htni : Φ.IsTNI) (ρ : SubState A)
    (u : PUnit) : ((ofMap Φ hcp htni).post ρ u).matrix = Φ ρ.matrix := by
  rw [matrix_post, branch_ofMap]

/-- The post-branch substates of a composite that starts with a single map are those of the
continuation on the image of the substate. -/
theorem post_ofMap_bind (Φ : MatrixMap A B) (hcp : Φ.IsCP) (htni : Φ.IsTNI)
    (k : PUnit.{v + 1} → SubInstrument B C β) (ρ : SubState A) (b : β) :
    ((ofMap Φ hcp htni).bind k).post ρ b =
      (k PUnit.unit).post ((ofMap Φ hcp htni).post ρ PUnit.unit.{v + 1}) b :=
  SubState.ext <| by
    rw [matrix_post, branch_ofMap_bind_apply, matrix_post, matrix_post_ofMap,
      LinearMap.comp_apply]

/-- The outcome measure of a composite that starts with a single map is the outcome measure of
the continuation on the image of the substate. -/
theorem outcomeMeasure_ofMap_bind [MeasurableSpace β] (Φ : MatrixMap A B) (hcp : Φ.IsCP)
    (htni : Φ.IsTNI) (k : PUnit.{v + 1} → SubInstrument B C β) (ρ : SubState A) :
    ((ofMap Φ hcp htni).bind k).outcomeMeasure ρ =
      (k PUnit.unit).outcomeMeasure ((ofMap Φ hcp htni).post ρ PUnit.unit.{v + 1}) := by
  ext s hs
  rw [outcomeMeasure_apply _ _ hs, outcomeMeasure_apply _ _ hs]
  simp only [branch_ofMap_bind_apply, matrix_post_ofMap, LinearMap.comp_apply]

/-! ## Contractions -/

section ofContraction

variable [DecidableEq A]

/-- The subinstrument with one outcome that applies the Kraus map `ρ ↦ K * ρ * Kᴴ` of a
contraction `K`. On vectors it is the map `ψ ↦ K •ᵥ ψ`; the decrease in squared norm is the
failure weight this step adds. -/
@[expose]
noncomputable def ofContraction (K : Matrix B A ℂ) (hK : ‖K‖ ≤ 1) : SubInstrument A B PUnit :=
  ofMap (MatrixMap.conj K) (MatrixMap.isCP_conj K)
    (MatrixMap.isTNI_conj ((posSemidef_one_sub_conjTranspose_mul_self_iff K).mpr hK))

/-- The branch family of the subinstrument of a contraction is its Kraus map at the unique
outcome. -/
@[simp]
theorem branch_ofContraction (K : Matrix B A ℂ) (hK : ‖K‖ ≤ 1) :
    (ofContraction K hK).branch = fun _ ↦ MatrixMap.conj K :=
  rfl

/-- The total map of the subinstrument of a contraction is its Kraus map. -/
@[simp]
theorem total_ofContraction (K : Matrix B A ℂ) (hK : ‖K‖ ≤ 1) :
    (ofContraction K hK).total = MatrixMap.conj K :=
  total_ofMap ..

/-- The subinstrument of an isometry is lossless. -/
theorem lossless_ofContraction {K : Matrix B A ℂ} (hK : ‖K‖ ≤ 1) (h : Kᴴ * K = 1) :
    (ofContraction K hK).Lossless :=
  lossless_ofMap _ (MatrixMap.isTP_conj h)

/-- The subinstrument of the identity operator returns the unique outcome and leaves the state
unchanged. -/
theorem ofContraction_one (h : ‖(1 : Matrix A A ℂ)‖ ≤ 1) :
    ofContraction (1 : Matrix A A ℂ) h = SubInstrument.pure PUnit.unit :=
  SubInstrument.ext <| funext fun u ↦ by
    cases u
    rw [branch_ofContraction, MatrixMap.conj_one, branch_pure_self]

/-- Each branch of a composite that starts with a contraction is the branch of the continuation
after the Kraus map of the contraction. -/
theorem branch_ofContraction_bind_apply (K : Matrix B A ℂ) (hK : ‖K‖ ≤ 1)
    (k : PUnit → SubInstrument B C β) (b : β) :
    ((ofContraction K hK).bind k).branch b = (k PUnit.unit).branch b ∘ₗ MatrixMap.conj K :=
  branch_ofMap_bind_apply ..

/-- Sequencing the subinstruments of two contractions gives the subinstrument of their
product. -/
theorem ofContraction_bind_ofContraction [DecidableEq B] (K : Matrix B A ℂ) (hK : ‖K‖ ≤ 1)
    (L : Matrix C B ℂ) (hL : ‖L‖ ≤ 1) :
    ((ofContraction K hK).bind fun _ ↦ ofContraction L hL) =
      ofContraction (L * K) (l2_opNorm_mul_le_one hL hK) :=
  SubInstrument.ext <| funext fun u ↦ by
    rw [branch_ofContraction_bind_apply, branch_ofContraction, branch_ofContraction,
      MatrixMap.conj_mul]

/-- The subinstrument of a contraction `K` sends the pure substate of `ψ` to the pure substate
of `K •ᵥ ψ`. -/
theorem post_ofContraction_ofVector (K : Matrix B A ℂ) (hK : ‖K‖ ≤ 1) (ψ : EuclideanSpace ℂ A)
    (hψ : ‖ψ‖ ≤ 1) (u : PUnit) :
    (ofContraction K hK).post (.ofVector ψ hψ) u =
      .ofVector (K •ᵥ ψ) (norm_applyVec_le_one hK hψ) :=
  SubState.ext <| by
    rw [ofContraction, matrix_post_ofMap]
    exact conj_ketBra_self K ψ

/-- On the pure substate of `ψ`, the subinstrument of a contraction `K` reports its unique
outcome with weight `‖K •ᵥ ψ‖ ^ 2`. -/
theorem outcomeMeasure_ofContraction_ofVector (K : Matrix B A ℂ) (hK : ‖K‖ ≤ 1)
    (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) :
    (ofContraction K hK).outcomeMeasure (.ofVector ψ hψ) =
      ENNReal.ofReal (‖K •ᵥ ψ‖ ^ 2) • Measure.dirac PUnit.unit := by
  rw [outcomeMeasure_eq_sum_univ, Fintype.sum_unique, PUnit.default_eq_unit, branch_ofContraction,
    SubState.matrix_ofVector, conj_ketBra_self, trace_re_ketBra_self]

/-- Vector form of the chain rule for a contraction: the outcome measure of a composite that
starts with the contraction `K`, on the pure substate of `ψ`, is the outcome measure of the
continuation on the pure substate of `K •ᵥ ψ`. -/
theorem outcomeMeasure_ofContraction_bind_ofVector [MeasurableSpace β] (K : Matrix B A ℂ)
    (hK : ‖K‖ ≤ 1) (k : PUnit → SubInstrument B C β) (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) :
    ((ofContraction K hK).bind k).outcomeMeasure (.ofVector ψ hψ) =
      (k PUnit.unit).outcomeMeasure (.ofVector (K •ᵥ ψ) (norm_applyVec_le_one hK hψ)) :=
  (outcomeMeasure_ofMap_bind ..).trans <|
    congrArg _ (post_ofContraction_ofVector K hK ψ hψ PUnit.unit)

/-- Vector form of the post-branch substates of a composite that starts with a contraction. -/
theorem post_ofContraction_bind_ofVector (K : Matrix B A ℂ) (hK : ‖K‖ ≤ 1)
    (k : PUnit → SubInstrument B C β) (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (b : β) :
    ((ofContraction K hK).bind k).post (.ofVector ψ hψ) b =
      (k PUnit.unit).post (.ofVector (K •ᵥ ψ) (norm_applyVec_le_one hK hψ)) b :=
  (post_ofMap_bind ..).trans <|
    congrArg (fun ρ ↦ (k PUnit.unit).post ρ b)
      (post_ofContraction_ofVector K hK ψ hψ PUnit.unit)

end ofContraction

/-! ## The Born rule for Kraus measurements -/

section ofKraus

variable [Fintype α] [DecidableEq A]

/-- After a Kraus measurement reports `a` on the pure substate of `ψ`, the substate is the pure
substate of `K a •ᵥ ψ`. -/
theorem post_ofKraus_ofVector (K : α → Matrix B A ℂ) (hK : ∑ a, (K a)ᴴ * K a = 1)
    (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (a : α) :
    (ofKraus K hK).post (.ofVector ψ hψ) a =
      .ofVector (K a •ᵥ ψ) ((norm_applyVec_le_of_sum_conjTranspose_mul_self hK a ψ).trans hψ) :=
  SubState.ext <| conj_ketBra_self (K a) ψ

/-- Vector form of the chain rule for a Kraus measurement: the outcome measure of a composite
that starts with the measurement, on the pure substate of `ψ`, sums the outcome measures of the
continuations on the pure substates of the branches `K a •ᵥ ψ`. -/
theorem outcomeMeasure_ofKraus_bind_ofVector {β : Type*} [MeasurableSpace β]
    (K : α → Matrix B A ℂ) (hK : ∑ a, (K a)ᴴ * K a = 1) (k : α → SubInstrument B C β)
    (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) :
    ((ofKraus K hK).bind k).outcomeMeasure (.ofVector ψ hψ) =
      ∑ a, (k a).outcomeMeasure (.ofVector (K a •ᵥ ψ)
        ((norm_applyVec_le_of_sum_conjTranspose_mul_self hK a ψ).trans hψ)) := by
  rw [outcomeMeasure_bind, Measure.sum_fintype]
  simp_rw [post_ofKraus_ofVector K hK ψ hψ]

variable [MeasurableSpace α]

/-- Born rule: on the pure substate of `ψ`, a Kraus measurement reports outcome `a` with weight
`‖K a •ᵥ ψ‖ ^ 2`. -/
theorem outcomeMeasure_ofKraus_ofVector (K : α → Matrix B A ℂ) (hK : ∑ a, (K a)ᴴ * K a = 1)
    (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) :
    (ofKraus K hK).outcomeMeasure (.ofVector ψ hψ) =
      ∑ a, ENNReal.ofReal (‖K a •ᵥ ψ‖ ^ 2) • Measure.dirac a := by
  rw [outcomeMeasure_eq_sum_univ]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [branch_ofKraus_apply, SubState.matrix_ofVector, conj_ketBra_self, trace_re_ketBra_self]

variable [MeasurableSingletonClass α]

/-- Born rule for a single outcome. -/
theorem outcomeMeasure_ofKraus_ofVector_singleton (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (a : α) :
    (ofKraus K hK).outcomeMeasure (.ofVector ψ hψ) {a} = ENNReal.ofReal (‖K a •ᵥ ψ‖ ^ 2) := by
  rw [outcomeMeasure_apply_singleton, branch_ofKraus_apply, SubState.matrix_ofVector,
    conj_ketBra_self, trace_re_ketBra_self]

/-- Born rule for an event: its weight is the total squared norm of the branches of its
outcomes. -/
theorem outcomeMeasure_ofKraus_ofVector_apply (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (s : Set α)
    [DecidablePred (· ∈ s)] :
    (ofKraus K hK).outcomeMeasure (.ofVector ψ hψ) s =
      ENNReal.ofReal (∑ a with a ∈ s, ‖K a •ᵥ ψ‖ ^ 2) := by
  have hs : MeasurableSet s := s.toFinite.measurableSet
  rw [outcomeMeasure_ofKraus_ofVector, Measure.coe_finsetSum, Finset.sum_apply,
    ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ sq_nonneg _, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul, Set.indicator_apply]
  split_ifs <;> simp

/-- Born rule for an event, as a real number. -/
theorem outcomeMeasure_real_ofKraus_ofVector_apply (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (s : Set α)
    [DecidablePred (· ∈ s)] :
    ((ofKraus K hK).outcomeMeasure (.ofVector ψ hψ)).real s = ∑ a with a ∈ s, ‖K a •ᵥ ψ‖ ^ 2 := by
  rw [Measure.real, outcomeMeasure_ofKraus_ofVector_apply,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]

/-- The weights that a Kraus measurement gives an event on the pure substates of two vectors
differ by at most `(‖ψ‖ + ‖φ‖) * ‖ψ - φ‖`. -/
theorem abs_outcomeMeasure_real_ofKraus_ofVector_sub_le (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) (ψ φ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (hφ : ‖φ‖ ≤ 1)
    (s : Set α) :
    |((ofKraus K hK).outcomeMeasure (.ofVector ψ hψ)).real s -
      ((ofKraus K hK).outcomeMeasure (.ofVector φ hφ)).real s| ≤ (‖ψ‖ + ‖φ‖) * ‖ψ - φ‖ := by
  classical
  rw [outcomeMeasure_real_ofKraus_ofVector_apply, outcomeMeasure_real_ofKraus_ofVector_apply]
  exact abs_sum_norm_sq_applyVec_sub_sum_norm_sq_applyVec_le _ K
    (fun χ ↦ sum_norm_sq_applyVec_le hK _ χ) ψ φ

/-- The weights that a Kraus measurement gives an event on the pure substates of two vectors
differ by at most twice the distance between the vectors. -/
theorem abs_outcomeMeasure_real_ofKraus_ofVector_sub_le_two_mul (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) (ψ φ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (hφ : ‖φ‖ ≤ 1)
    (s : Set α) :
    |((ofKraus K hK).outcomeMeasure (.ofVector ψ hψ)).real s -
      ((ofKraus K hK).outcomeMeasure (.ofVector φ hφ)).real s| ≤ 2 * ‖ψ - φ‖ :=
  (abs_outcomeMeasure_real_ofKraus_ofVector_sub_le K hK ψ φ hψ hφ s).trans <|
    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

end ofKraus

/-! ## Projective measurements -/

section ofProjective

variable [Fintype α] [DecidableEq A]

/-- A family of star projections that sums to one satisfies the completeness relation of Kraus
operators. -/
theorem sum_conjTranspose_mul_self_of_isStarProjection {P : α → Matrix A A ℂ}
    (hP : ∀ a, IsStarProjection (P a)) (hsum : ∑ a, P a = 1) : ∑ a, (P a)ᴴ * P a = 1 := by
  rw [← hsum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← Matrix.star_eq_conjTranspose, (hP a).isSelfAdjoint.star_eq, (hP a).isIdempotentElem.eq]

/-- The projective measurement with a family of star projections `P a`, one per outcome, that
sums to one: the Kraus measurement with operators `P a`. -/
@[expose]
noncomputable def ofProjective (P : α → Matrix A A ℂ) (hP : ∀ a, IsStarProjection (P a))
    (hsum : ∑ a, P a = 1) : SubInstrument A A α :=
  ofKraus P (sum_conjTranspose_mul_self_of_isStarProjection hP hsum)

variable (P : α → Matrix A A ℂ) (hP : ∀ a, IsStarProjection (P a)) (hsum : ∑ a, P a = 1)

/-- A projective measurement is the Kraus measurement with its projections. -/
theorem ofProjective_eq_ofKraus :
    ofProjective P hP hsum = ofKraus P (sum_conjTranspose_mul_self_of_isStarProjection hP hsum) :=
  rfl

/-- The branch of a projective measurement at `a` is the Kraus map of `P a`. -/
@[simp]
theorem branch_ofProjective_apply (a : α) :
    (ofProjective P hP hsum).branch a = MatrixMap.conj (P a) :=
  rfl

/-- A projective measurement is lossless. -/
theorem lossless_ofProjective : (ofProjective P hP hsum).Lossless :=
  lossless_ofKraus _ _

/-- After a projective measurement reports `a` on the pure substate of `ψ`, the substate is the
pure substate of the projection `P a •ᵥ ψ`. -/
theorem post_ofProjective_ofVector (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (a : α) :
    (ofProjective P hP hsum).post (.ofVector ψ hψ) a =
      .ofVector (P a •ᵥ ψ) ((norm_applyVec_le_of_isStarProjection (hP a) ψ).trans hψ) :=
  SubState.ext <| conj_ketBra_self (P a) ψ

/-- Born rule for a projective measurement: on the pure substate of `ψ`, outcome `a` has weight
`‖P a •ᵥ ψ‖ ^ 2`. -/
theorem outcomeMeasure_ofProjective_ofVector_singleton [MeasurableSpace α]
    [MeasurableSingletonClass α] (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (a : α) :
    (ofProjective P hP hsum).outcomeMeasure (.ofVector ψ hψ) {a} =
      ENNReal.ofReal (‖P a •ᵥ ψ‖ ^ 2) :=
  outcomeMeasure_ofKraus_ofVector_singleton ..

/-- Born rule for a projective measurement, in expectation form: on the pure substate of `ψ`,
outcome `a` has weight `⟪ψ, P a •ᵥ ψ⟫`. -/
theorem outcomeMeasure_ofProjective_ofVector_singleton_eq_inner [MeasurableSpace α]
    [MeasurableSingletonClass α] (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) (a : α) :
    (ofProjective P hP hsum).outcomeMeasure (.ofVector ψ hψ) {a} =
      ENNReal.ofReal (⟪ψ, P a •ᵥ ψ⟫_ℂ).re := by
  rw [outcomeMeasure_ofProjective_ofVector_singleton, norm_sq_applyVec_of_isStarProjection (hP a)]

end ofProjective

end SubInstrument

/-! ## Unitaries on a fixed register -/

namespace SubInstrument

variable {M : Type u} [Fintype M] [DecidableEq M]

/-- The subinstrument that applies the unitary `U` to the register and returns the unique
value. -/
@[expose]
noncomputable def ofUnitary (U : Matrix.unitaryGroup M ℂ) : SubInstrument M M PUnit.{w + 1} :=
  SubInstrument.ofContraction (U : Matrix M M ℂ) (l2_opNorm_le_one_of_mem_unitaryGroup U.2)

/-- Applying a unitary is lossless. -/
theorem lossless_ofUnitary (U : Matrix.unitaryGroup M ℂ) :
    (ofUnitary.{u, w} U).Lossless :=
  SubInstrument.lossless_ofContraction _ (Matrix.mem_unitaryGroup_iff'.mp U.2)

/-- Applying the identity unitary is `pure`. -/
@[simp]
theorem ofUnitary_one : ofUnitary.{u, w} (1 : Matrix.unitaryGroup M ℂ) = pure PUnit.unit :=
  SubInstrument.ofContraction_one _

/-- Applying `U` and then `V` is applying the product `V * U`. -/
theorem ofUnitary_bind_ofUnitary (U V : Matrix.unitaryGroup M ℂ) :
    (ofUnitary.{u, w} U >>= fun _ ↦ ofUnitary.{u, w} V) = ofUnitary (V * U) :=
  SubInstrument.ofContraction_bind_ofContraction ..

/-- Applying a unitary `U` sends the pure substate of `ψ` to the pure substate of `U •ᵥ ψ`. -/
theorem post_ofUnitary_ofVector (U : Matrix.unitaryGroup M ℂ) (ψ : EuclideanSpace ℂ M)
    (hψ : ‖ψ‖ ≤ 1) (u : PUnit) :
    (ofUnitary.{u, w} U).post (.ofVector ψ hψ) u =
      .ofVector ((U : Matrix M M ℂ) •ᵥ ψ)
        ((norm_applyVec_of_mem_unitaryGroup U.2 ψ).le.trans hψ) :=
  SubInstrument.post_ofContraction_ofVector ..

/-- On the pure substate of `ψ`, applying a unitary returns its value with weight `‖ψ‖ ^ 2`. -/
theorem outcomeMeasure_ofUnitary_ofVector (U : Matrix.unitaryGroup M ℂ)
    (ψ : EuclideanSpace ℂ M) (hψ : ‖ψ‖ ≤ 1) :
    (ofUnitary.{u, w} U).outcomeMeasure (.ofVector ψ hψ) =
      ENNReal.ofReal (‖ψ‖ ^ 2) • Measure.dirac PUnit.unit := by
  rw [ofUnitary, SubInstrument.outcomeMeasure_ofContraction_ofVector,
    norm_applyVec_of_mem_unitaryGroup U.2]

/-- Vector form of the chain rule for a unitary step: the outcome measure of a computation that
starts by applying `U`, on the pure substate of `ψ`, is the outcome measure of the rest on the
pure substate of `U •ᵥ ψ`. -/
theorem outcomeMeasure_ofUnitary_bind_ofVector {β : Type w} [MeasurableSpace β]
    (U : Matrix.unitaryGroup M ℂ) (k : PUnit → SubInstrument M M β) (ψ : EuclideanSpace ℂ M)
    (hψ : ‖ψ‖ ≤ 1) :
    (ofUnitary.{u, w} U >>= k).outcomeMeasure (.ofVector ψ hψ) =
      (k PUnit.unit).outcomeMeasure (.ofVector ((U : Matrix M M ℂ) •ᵥ ψ)
        ((norm_applyVec_of_mem_unitaryGroup U.2 ψ).le.trans hψ)) :=
  SubInstrument.outcomeMeasure_ofContraction_bind_ofVector ..

end SubInstrument

end Quantum
