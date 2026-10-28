/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.MasterBound
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Data.List.GetD

/-! # The decisional master theorem for discrete group models

Equally shaped symbolic tables with the same linear relations give identical exact runs.
The hidden-point runs differ by at most the sum of their two polynomial collision bounds,
jointly with the hidden point and the returned value.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace GroupModel

variable {F S ι : Type}

/-- Two symbolic tables have equal lengths and the same vanishing linear combinations
in every sort. -/
@[expose] def SameKernel [Field F] (T₀ T₁ : Tbl (fun _ : S => MvPolynomial ι F)) : Prop :=
  ∀ s, (T₀ s).length = (T₁ s).length ∧
    ∀ r : Repr F, evRepr (T₀ s) r = 0 ↔ evRepr (T₁ s) r = 0

/-- Equal relation kernels identify the same pairs of representations. -/
theorem SameKernel.eq_iff [Field F] {T₀ T₁ : Tbl (fun _ : S => MvPolynomial ι F)}
    (h : SameKernel T₀ T₁) (s : S) (r r' : Repr F) :
    evRepr (T₀ s) r = evRepr (T₀ s) r' ↔ evRepr (T₁ s) r = evRepr (T₁ s) r' := by
  simpa only [map_sub, sub_eq_zero] using (h s).2 (r - r')

private theorem evRepr_eq_zero_iff [Field F] {G : Type} [AddCommGroup G] [Module F G]
    (xs : List G) (h : LinearIndependent F xs.get) (r : Repr F) :
    evRepr xs r = 0 ↔ ∀ i < xs.length, r i = 0 := by
  rw [evRepr_apply, ← Fin.sum_univ_eq_sum_range]
  simp only [List.getD_eq_get]
  constructor
  · intro he i hi
    exact Fintype.linearIndependent_iff.mp h (fun j => r j) he ⟨i, hi⟩
  · intro he
    exact Finset.sum_eq_zero fun i _ => by rw [he i i.isLt, zero_smul]

/-- Equally long, linearly independent tables have the same relation kernel. -/
theorem sameKernel_of_linearIndependent [Field F]
    {T₀ T₁ : Tbl (fun _ : S => MvPolynomial ι F)}
    (hlen : ∀ s, (T₀ s).length = (T₁ s).length)
    (h₀ : ∀ s, LinearIndependent F (T₀ s).get)
    (h₁ : ∀ s, LinearIndependent F (T₁ s).get) : SameKernel T₀ T₁ := by
  intro s
  refine ⟨hlen s, fun r => ?_⟩
  rw [evRepr_eq_zero_iff _ (h₀ s), evRepr_eq_zero_iff _ (h₁ s), hlen s]

private theorem symbolic_discrete_eq [CommSemiring F] :
    symbolic F (discreteSig S) ι = Model.discrete (fun _ : S => MvPolynomial ι F) := by
  have hl : (symbolic F (discreteSig S) ι).lin =
      (Model.discrete (fun _ : S => MvPolynomial ι F)).lin := by
    funext o
    exact o.elim
  have hb : (symbolic F (discreteSig S) ι).bil =
      (Model.discrete (fun _ : S => MvPolynomial ι F)).bil := by
    funext o
    exact o.elim
  exact congrArg₂ Model.mk hl hb

private theorem mapTbl_units [Field F] (T : Tbl (fun _ : S => MvPolynomial ι F)) :
    mapTbl (fun s => evRepr (F := F) (T s))
      (fun s => List.ofFn (fun i : Fin (T s).length => Pi.single (i : Handle) 1)) = T := by
  funext s
  simp [mapTbl, List.map_ofFn, Function.comp_def, evRepr_single]

/-- Tables with the same shape and relation kernel give identical exact returned values.
T6 applies to evaluation morphisms out of the free discrete model on unit representations. -/
theorem SameKernel.runGen_fst_eq [Field F] [DecidableEq F] [DecidableEq ι] [DecidableEq S]
    {T₀ T₁ : Tbl (fun _ : S => MvPolynomial ι F)} (h : SameKernel T₀ T₁)
    {α : Type} (oa : OracleComp (genSpec F (discreteSig S)) α) :
    Prod.fst <$> runGen (symbolic F (discreteSig S) ι) (fun _ => id) oa T₀ =
      Prod.fst <$> runGen (symbolic F (discreteSig S) ι) (fun _ => id) oa T₁ := by
  let units : Tbl (fun _ : S => Repr F) :=
    fun s => List.ofFn (fun i : Fin (T₀ s).length => Pi.single (i : Handle) 1)
  have hu : units =
      (fun s => List.ofFn (fun i : Fin (T₁ s).length => Pi.single (i : Handle) 1)) := by
    funext s
    simp only [units, (h s).1, Fin.val_cast]
  have hev (T : Tbl (fun _ : S => MvPolynomial ι F)) :
      (fun s => ⇑((evHom.discrete T).toFun s)) = (fun s => ⇑(evRepr (F := F) (T s))) := by
    funext s r
    exact evHom.discrete_apply T s r
  have h₀ : mapTbl (fun s => (evHom.discrete T₀).toFun s) units = T₀ := by
    simpa only [hev, units] using mapTbl_units T₀
  have h₁ : mapTbl (fun s => (evHom.discrete T₁).toFun s) units = T₁ := by
    rw [hu]
    simpa only [hev] using mapTbl_units T₁
  have he := run_fst_eq_of_kernel_eq (evHom.discrete T₀) (evHom.discrete T₁)
    (fun s r r' => by simpa only [evHom.discrete_apply] using h.eq_iff s r r') oa units
  simpa only [h₀, h₁, symbolic_discrete_eq] using he

/-- The master bound also controls the joint hidden point and returned value, after discarding
both final tables. -/
theorem measureETVDist_runGen_symbolic_fst_le [Field F] [DecidableEq F] [DecidableEq ι]
    [Fintype S] [DecidableEq S] {α : Type} [MeasurableSpace ((ι → F) × α)]
    (xs : ProbComp (ι → F)) {d q : ℕ} {ε : ℝ≥0∞}
    (hε : ∀ f : MvPolynomial ι F, f ≠ 0 → f.totalDegree ≤ d →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε)
    (oa : OracleComp (genSpec F (discreteSig S)) α)
    (hq : IsQueryBoundP oa (fun i => isGroupOp i = true) q)
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (hd : DegreeLE d tbl) :
    measureETVDist
      (do let x ← xs
          let z ← runGen (symbolic F (discreteSig S) ι) (fun _ p => MvPolynomial.eval x p) oa tbl
          pure (x, z.1))
      (do let x ← xs
          let z ← runGen (symbolic F (discreteSig S) ι) (fun _ => id) oa tbl
          pure (x, z.1)) ≤
      (((∑ s, (tbl s).length) + q + 1).choose 2 : ℝ≥0∞) * ε := by
  let : MeasurableSpace ((ι → F) × (α × Tbl (fun _ : S => MvPolynomial ι F))) := ⊤
  have h := measureETVDist_runGen_symbolic_le xs hε oa hq tbl hd
  have hm := (measureETVDist_map_le (m := ProbComp) _ _ (fun z : (ι → F) ×
    (α × Tbl (fun _ : S => MvPolynomial ι F)) => (z.1, z.2.1)) Measurable.of_discrete).trans h
  simpa only [map_bind, map_pure] using hm

/-! ## Decisional bounds -/

/-- **T7, the decisional master theorem.** Equal shapes and relation kernels bound the
joint hidden-point/output distance by the sum of the two T3 collision terms. Each side
uses its own degree and root-probability bound. -/
theorem measureETVDist_runGen_sameKernel_le [Field F] [DecidableEq F]
    [Fintype S] [DecidableEq S] {α : Type} [MeasurableSpace ((ι → F) × α)]
    (xs : ProbComp (ι → F)) {d₀ d₁ q : ℕ} {ε₀ ε₁ : ℝ≥0∞}
    (hε₀ : ∀ f : MvPolynomial ι F, f ≠ 0 → f.totalDegree ≤ d₀ →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε₀)
    (hε₁ : ∀ f : MvPolynomial ι F, f ≠ 0 → f.totalDegree ≤ d₁ →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε₁)
    (oa : OracleComp (genSpec F (discreteSig S)) α)
    (hq : IsQueryBoundP oa (fun i => isGroupOp i = true) q)
    (T₀ T₁ : Tbl (fun _ : S => MvPolynomial ι F))
    (hd₀ : DegreeLE d₀ T₀) (hd₁ : DegreeLE d₁ T₁) (h : SameKernel T₀ T₁) :
    measureETVDist
      (do let x ← xs
          let z ← runGen (symbolic F (discreteSig S) ι) (fun _ p => MvPolynomial.eval x p) oa T₀
          pure (x, z.1))
      (do let x ← xs
          let z ← runGen (symbolic F (discreteSig S) ι) (fun _ p => MvPolynomial.eval x p) oa T₁
          pure (x, z.1)) ≤
      (((∑ s, (T₀ s).length) + q + 1).choose 2 : ℝ≥0∞) * ε₀ +
      (((∑ s, (T₁ s).length) + q + 1).choose 2 : ℝ≥0∞) * ε₁ := by
  classical
  let exactRun (T : Tbl (fun _ : S => MvPolynomial ι F)) : ProbComp ((ι → F) × α) := do
    let x ← xs
    let z ← runGen (symbolic F (discreteSig S) ι) (fun _ => id) oa T
    pure (x, z.1)
  -- T6 identifies the exact runs, including their joint outputs with the hidden point.
  have he : exactRun T₀ = exactRun T₁ := by
    simp only [exactRun, bind_pure_comp]
    congr 1
    funext x
    simpa only [Functor.map_map, Function.comp_def] using
      congrArg (fun c : ProbComp α => (fun a => (x, a)) <$> c) (h.runGen_fst_eq oa)
  -- Project T3 on each side and join the bounds through the common exact run.
  have h₀ := measureETVDist_runGen_symbolic_fst_le xs hε₀ oa hq T₀ hd₀
  have h₁ := measureETVDist_runGen_symbolic_fst_le xs hε₁ oa hq T₁ hd₁
  change measureETVDist _ (exactRun T₁) ≤ _ at h₁
  rw [← he, measureETVDist_comm] at h₁
  exact (measureETVDist_triangle _ (exactRun T₀) _).trans (add_le_add h₀ h₁)

/-- Every measurable event on the hidden point and returned value satisfies the decisional
bound in both directions. -/
theorem prEvent_runGen_sameKernel_le_add [Field F] [DecidableEq F]
    [Fintype S] [DecidableEq S] {α : Type} [MeasurableSpace ((ι → F) × α)]
    (xs : ProbComp (ι → F)) {d₀ d₁ q : ℕ} {ε₀ ε₁ : ℝ≥0∞}
    (hε₀ : ∀ f : MvPolynomial ι F, f ≠ 0 → f.totalDegree ≤ d₀ →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε₀)
    (hε₁ : ∀ f : MvPolynomial ι F, f ≠ 0 → f.totalDegree ≤ d₁ →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε₁)
    (oa : OracleComp (genSpec F (discreteSig S)) α)
    (hq : IsQueryBoundP oa (fun i => isGroupOp i = true) q)
    (T₀ T₁ : Tbl (fun _ : S => MvPolynomial ι F))
    (hd₀ : DegreeLE d₀ T₀) (hd₁ : DegreeLE d₁ T₁) (h : SameKernel T₀ T₁)
    (E : Set ((ι → F) × α)) (hE : MeasurableSet E) :
    (Pr{let x ← xs; let z ← (runGen (symbolic F (discreteSig S) ι)
        (fun _ p => MvPolynomial.eval x p) oa T₀)}[(x, z.1) ∈ E] ≤
      Pr{let x ← xs; let z ← (runGen (symbolic F (discreteSig S) ι)
        (fun _ p => MvPolynomial.eval x p) oa T₁)}[(x, z.1) ∈ E] +
      ((((∑ s, (T₀ s).length) + q + 1).choose 2 : ℝ≥0∞) * ε₀ +
      (((∑ s, (T₁ s).length) + q + 1).choose 2 : ℝ≥0∞) * ε₁)) ∧
    (Pr{let x ← xs; let z ← (runGen (symbolic F (discreteSig S) ι)
        (fun _ p => MvPolynomial.eval x p) oa T₁)}[(x, z.1) ∈ E] ≤
      Pr{let x ← xs; let z ← (runGen (symbolic F (discreteSig S) ι)
        (fun _ p => MvPolynomial.eval x p) oa T₀)}[(x, z.1) ∈ E] +
      ((((∑ s, (T₀ s).length) + q + 1).choose 2 : ℝ≥0∞) * ε₀ +
      (((∑ s, (T₁ s).length) + q + 1).choose 2 : ℝ≥0∞) * ε₁)) := by
  classical
  let left : ProbComp ((ι → F) × α) := do
    let x ← xs
    let z ← runGen (symbolic F (discreteSig S) ι) (fun _ p => MvPolynomial.eval x p) oa T₀
    pure (x, z.1)
  let right : ProbComp ((ι → F) × α) := do
    let x ← xs
    let z ← runGen (symbolic F (discreteSig S) ι) (fun _ p => MvPolynomial.eval x p) oa T₁
    pure (x, z.1)
  have hb : measureETVDist left right ≤ _ :=
    measureETVDist_runGen_sameKernel_le xs hε₀ hε₁ oa hq T₀ T₁ hd₀ hd₁ h
  have hl := (prEvent_le_prEvent_add_measureETVDist left right (· ∈ E) hE.mem).trans
    (add_le_add le_rfl hb)
  rw [measureETVDist_comm] at hb
  have hr := (prEvent_le_prEvent_add_measureETVDist right left (· ∈ E) hE.mem).trans
    (add_le_add le_rfl hb)
  simpa only [left, right, map_bind, map_pure, bind_pure_comp, Functor.map_map,
    Function.comp_def] using And.intro hl hr

/-- Uniform hidden points over a finite field give the two Schwartz–Zippel terms
`choose (initial size + q + 1) 2 * (degree / card F)` in the decisional bound. -/
theorem measureETVDist_runGen_sameKernel_uniform_le [Field F] [DecidableEq F]
    [Fintype F] [SampleableType (ι → F)]
    [Fintype S] [DecidableEq S] {α : Type} [MeasurableSpace ((ι → F) × α)]
    {d₀ d₁ q : ℕ} (oa : OracleComp (genSpec F (discreteSig S)) α)
    (hq : IsQueryBoundP oa (fun i => isGroupOp i = true) q)
    (T₀ T₁ : Tbl (fun _ : S => MvPolynomial ι F))
    (hd₀ : DegreeLE d₀ T₀) (hd₁ : DegreeLE d₁ T₁) (h : SameKernel T₀ T₁) :
    measureETVDist
      (do let x ← $ᵗ (ι → F)
          let z ← runGen (symbolic F (discreteSig S) ι) (fun _ p => MvPolynomial.eval x p) oa T₀
          pure (x, z.1))
      (do let x ← $ᵗ (ι → F)
          let z ← runGen (symbolic F (discreteSig S) ι) (fun _ p => MvPolynomial.eval x p) oa T₁
          pure (x, z.1)) ≤
      (((∑ s, (T₀ s).length) + q + 1).choose 2 : ℝ≥0∞) *
        ((d₀ : ℝ≥0∞) / Fintype.card F) +
      (((∑ s, (T₁ s).length) + q + 1).choose 2 : ℝ≥0∞) *
        ((d₁ : ℝ≥0∞) / Fintype.card F) := by
  classical
  have : Finite ι := Finite.of_injective (fun i : ι => Pi.single i (1 : F)) (by
    intro i j h
    by_contra hij
    have he := congrFun h i
    simp [hij] at he)
  apply measureETVDist_runGen_sameKernel_le ($ᵗ (ι → F)) _ _ oa hq T₀ T₁ hd₀ hd₁ h
  · intro f hf hdeg
    exact prob_eval_zero_univ_le_div f hf hdeg
  · intro f hf hdeg
    exact prob_eval_zero_univ_le_div f hf hdeg

end GroupModel
