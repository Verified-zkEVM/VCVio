/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Compressed.Equivalence

/-!
# Measuring the database after a run

After a program has run against the compressed runtime (`Quantum.compressedRuntime`) and reached
a leaf, the database register can be measured in the computational basis
(`Quantum.measureDatabase`), which reports a database `D`. This is how the compressed oracle is
used to record queries (Zhandry, Crypto 2019; Chiesa, Di, Hu and Zheng, ePrint 2025/2166,
§4). The measurement does not disturb the leaf already reached, so the law of the leaf alone is
the law of the run against the compressed runtime, hence the law of the quantum random-oracle
model.

The joint law is defined for general programs (`Quantum.QuantumComp`), with the leaf observed
through any function: `Quantum.compressedJointLawWith`. For programs on a fixed final register,
`Quantum.compressedRunWithDatabase` is the run followed by the measurement, as a subinstrument on
`A × Database X Y`, and `Quantum.compressedJointLaw` is its outcome measure from the empty
database; it is the general joint law read through the value of each leaf
(`Quantum.compressedJointLaw_eq_compressedJointLawWith`).

The joint laws take the measurable structure on `Quantum.Database X Y` as an argument, so that no
instance on function types is fixed here.

## Main results

* `Quantum.map_fst_compressedJointLawWith_eq_qromLawWith`: the observed leaf has the law of the
  quantum random-oracle model.
* `Quantum.map_fst_compressedJointLaw_eq_qromLaw`: the same for fixed-register programs.
-/

public section

open MeasureTheory Matrix
open scoped Kronecker

universe u v w

namespace Quantum

/-! ## Marginals of outcome measures -/

namespace SubInstrument

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] {α β : Type*}

/-- Relabelling the outcomes of a subinstrument along a measurable map pushes its outcome
measure forward along the map. -/
theorem outcomeMeasure_map_eq_map [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) (p : SubInstrument A B α) (ρ : SubState A) :
    (p.map f).outcomeMeasure ρ = (p.outcomeMeasure ρ).map f := by
  rw [DSubInstrument.outcomeMeasure_map, DSubInstrument.outcomeMeasure_eq_sum,
    Measure.map_sum hf.aemeasurable]
  refine congrArg Measure.sum (funext fun a ↦ ?_)
  rw [Measure.map_smul, Measure.map_dirac' hf]
  exact hf.aemeasurable

/-- Tagging every outcome of a lossless subinstrument with `a` and forgetting the outcome leaves
the point mass at `a` with the weight of the input. -/
theorem map_fst_outcomeMeasure_map_prodMk [MeasurableSpace α] [MeasurableSpace β]
    {p : SubInstrument A B β} (hp : p.Lossless) (a : α) (ρ : SubState A) :
    ((p.map (Prod.mk a)).outcomeMeasure ρ).map Prod.fst =
      ENNReal.ofReal ρ.matrix.trace.re • Measure.dirac a := by
  rw [outcomeMeasure_map_eq_map measurable_prodMk_left,
    Measure.map_map measurable_fst measurable_prodMk_left,
    show (Prod.fst ∘ Prod.mk a : β → α) = fun _ ↦ a from rfl, Measure.map_const,
    hp.outcomeMeasure_apply_univ]

/-- If after each outcome `a` of `p` a lossless subinstrument `k a` is run and `a` is reported
together with its outcome, the first component of the joint outcome has the law of `p`. -/
theorem map_fst_outcomeMeasure_bind_map_prodMk [MeasurableSpace α] [MeasurableSpace β]
    (p : SubInstrument A B α) {k : α → SubInstrument B C β} (hk : ∀ a, (k a).Lossless)
    (ρ : SubState A) :
    ((p.bind fun a ↦ (k a).map (Prod.mk a)).outcomeMeasure ρ).map Prod.fst =
      p.outcomeMeasure ρ := by
  rw [DSubInstrument.outcomeMeasure_bind, Measure.map_sum measurable_fst.aemeasurable,
    DSubInstrument.outcomeMeasure_eq_sum]
  refine congrArg Measure.sum (funext fun a ↦ ?_)
  rw [map_fst_outcomeMeasure_map_prodMk (hk a), DSubInstrument.matrix_post]

end SubInstrument

/-! ## The database measurement -/

section measureDatabase

variable (M X Y : Type*) [Fintype M] [DecidableEq M] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]

/-- The projections `1 ⊗ |D⟩⟨D|` onto the basis states of the database register form a complete
family of Kraus operators. -/
theorem sum_one_kronecker_single_conjTranspose_mul_self :
    ∑ D : Database X Y, ((1 : Matrix M M ℂ) ⊗ₖ Matrix.single D D (1 : ℂ))ᴴ *
      ((1 : Matrix M M ℂ) ⊗ₖ Matrix.single D D (1 : ℂ)) = 1 := by
  have h (D : Database X Y) :
      ((1 : Matrix M M ℂ) ⊗ₖ Matrix.single D D (1 : ℂ))ᴴ *
        ((1 : Matrix M M ℂ) ⊗ₖ Matrix.single D D (1 : ℂ)) =
      (1 : Matrix M M ℂ) ⊗ₖ Matrix.single D D (1 : ℂ) := by
    rw [conjTranspose_kronecker, conjTranspose_one, Matrix.conjTranspose_single, star_one,
      ← mul_kronecker_mul, Matrix.one_mul, Matrix.single_mul_single_same, mul_one]
  rw [Finset.sum_congr rfl fun D _ ↦ h D]
  ext ⟨m, D⟩ ⟨m', D'⟩
  by_cases hm : m = m' <;>
    simp [Matrix.sum_apply, Matrix.one_apply, Matrix.single_apply, ite_and, hm]

/-- Measuring the database register of `M × Database X Y` in the computational basis, leaving
the register `M` untouched: the measurement with Kraus operators `1 ⊗ |D⟩⟨D|`, reporting `D`. -/
@[expose]
noncomputable def measureDatabase :
    SubInstrument (M × Database X Y) (M × Database X Y) (Database X Y) :=
  SubInstrument.ofKraus (fun D ↦ (1 : Matrix M M ℂ) ⊗ₖ Matrix.single D D (1 : ℂ))
    (sum_one_kronecker_single_conjTranspose_mul_self M X Y)

@[simp]
theorem branch_measureDatabase_apply (D : Database X Y) :
    (measureDatabase M X Y).branch D =
      MatrixMap.conj ((1 : Matrix M M ℂ) ⊗ₖ Matrix.single D D (1 : ℂ)) :=
  rfl

theorem lossless_measureDatabase : (measureDatabase M X Y).Lossless :=
  DSubInstrument.lossless_ofKraus _ (sum_one_kronecker_single_conjTranspose_mul_self M X Y)

end measureDatabase

/-! ## The joint law of the leaf and the database -/

section jointLaw

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [MeasurableSpace (Database X Y)] {L : LocalSig.{u, v}} {W : QReg → Type w} {A B : QReg}
  {α : Type w}

/-- The joint law of the observation `f` of the leaf reached by `x`, run against the compressed
runtime from `ρ` and the empty database, and of the database measured at that leaf: the leaf `p`
contributes the outcome measure of the database measurement on its joint post-state, with each
measured database tagged by `f p`. -/
@[expose]
noncomputable def compressedJointLawWith {γ : Type*} [MeasurableSpace γ] (I : L.Interp)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) (f : (Σ u, W u) → γ) :
    Measure (γ × Database X Y) :=
  Measure.sum fun p ↦ ((measureDatabase p.1 X Y).map (Prod.mk (f p))).outcomeMeasure
    ((compressedRuntime X Y).jointPost I x ρ p)

/-- Measuring the database at the leaf does not change the law of the observed leaf. -/
theorem map_fst_compressedJointLawWith {γ : Type*} [MeasurableSpace γ] (I : L.Interp)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) (f : (Σ u, W u) → γ) :
    (compressedJointLawWith I x ρ f).map Prod.fst =
      (compressedRuntime X Y).evalDistMap I x ρ f := by
  rw [compressedJointLawWith, Measure.map_sum measurable_fst.aemeasurable]
  refine congrArg Measure.sum (funext fun p ↦ ?_)
  exact SubInstrument.map_fst_outcomeMeasure_map_prodMk (lossless_measureDatabase _ X Y) _ _

/-- **The recorded queries do not disturb the law.** The observed leaf, marginal of the joint law
of the leaf and the measured database, has the law of the quantum random-oracle model. -/
theorem map_fst_compressedJointLawWith_eq_qromLawWith {γ : Type*}
    [MeasurableSpace γ] (I : L.Interp) (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A)
    (f : (Σ u, W u) → γ) :
    (compressedJointLawWith I x ρ f).map Prod.fst = qromEvalDistMap I x ρ fun _ ↦ f := by
  rw [map_fst_compressedJointLawWith, outcomeLawWith_compressedRuntime]

/-- The run of a fixed-register program `x` against the compressed runtime, followed by the
measurement of the database register, as a subinstrument on `A × Database X Y` reporting the
value of `x` and the measured database. It acts on any operator on `A × Database X Y`; the
initialization with the empty database happens in `Quantum.compressedJointLaw`. -/
@[expose]
noncomputable def compressedRunWithDatabase (I : L.Interp)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) :
    SubInstrument (A × Database X Y) (B × Database X Y) (α × Database X Y) :=
  ((compressedRuntime X Y).run₂ I x).bind fun a ↦ (measureDatabase B X Y).map (Prod.mk a)

/-- The joint law of the value of a fixed-register program `x`, run against the compressed
runtime from `ρ` and the empty database, and of the database measured afterwards. -/
@[expose]
noncomputable def compressedJointLaw [MeasurableSpace α] (I : L.Interp)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) : Measure (α × Database X Y) :=
  (compressedRunWithDatabase I x).outcomeMeasure (ρ.prod (SubState.basis Database.empty))

/-- The joint law of a fixed-register program is the general joint law, read through the value
of each leaf. -/
theorem compressedJointLaw_eq_compressedJointLawWith [MeasurableSpace α] (I : L.Interp)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) :
    compressedJointLaw I x ρ =
      compressedJointLawWith I x ρ (QuantumComp₂.leafEquiv B α).symm := by
  rw [compressedJointLaw, compressedRunWithDatabase, DSubInstrument.outcomeMeasure_bind]
  exact Measure.sum_comp_equiv (QuantumComp₂.leafEquiv B α) fun p ↦
    ((measureDatabase p.1 X Y).map (Prod.mk ((QuantumComp₂.leafEquiv B α).symm p))).outcomeMeasure
      ((compressedRuntime X Y).jointPost I x ρ p)

/-- Measuring the database after the run does not change the law of the value. -/
theorem map_fst_compressedJointLaw [MeasurableSpace α] (I : L.Interp)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) :
    (compressedJointLaw I x ρ).map Prod.fst = (compressedRuntime X Y).evalDist₂ I x ρ :=
  SubInstrument.map_fst_outcomeMeasure_bind_map_prodMk _
    (fun _ ↦ lossless_measureDatabase _ X Y) _

/-- The value marginal of the joint law of the value and the measured database is the law of the
quantum random-oracle model. -/
theorem map_fst_compressedJointLaw_eq_qromLaw [MeasurableSpace α]
    (I : L.Interp) (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) :
    (compressedJointLaw I x ρ).map Prod.fst = qromEvalDist₂ I x ρ := by
  rw [map_fst_compressedJointLaw, outcomeLaw₂_compressedRuntime]

end jointLaw

end Quantum
