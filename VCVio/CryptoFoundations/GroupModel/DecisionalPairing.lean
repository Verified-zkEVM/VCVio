/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Decisional
import all VCVio.CryptoFoundations.GroupModel.Instances
import Mathlib.Data.List.GetD

/-! # The decisional master theorem for Type 3 pairing groups

The accessible target span consists of the supplied target entries and all products of
supplied source entries. Equal relation kernels in these spans identify exact symbolic
runs; the two per-sort collision bounds then control the hidden-point runs.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace GroupModel

variable {F ι : Type}

/-- The polynomial pairing model maps to the symbolic model by the identity in every sort. -/
noncomputable def polynomialPairingToSymbolic [Field F] :
    (pairingReal (LinearMap.mul F (MvPolynomial ι F))).Hom (symbolic F pairingSig ι) where
  toFun
    | .g₁ => LinearMap.id
    | .g₂ => LinearMap.id
    | .gₜ => LinearMap.id
  map_lin o := o.elim
  map_bil o x y := by
    change Unit at o
    change MvPolynomial ι F at x y
    rfl

/-- The symbolic model maps to the polynomial pairing model by the identity in every sort. -/
noncomputable def symbolicToPolynomialPairing [Field F] :
    (symbolic F pairingSig ι).Hom (pairingReal (LinearMap.mul F (MvPolynomial ι F))) where
  toFun
    | .g₁ => LinearMap.id
    | .g₂ => LinearMap.id
    | .gₜ => LinearMap.id
  map_lin o := o.elim
  map_bil o x y := by
    change Unit at o
    rfl

/-- Evaluate free pairing representations on symbolic source and target tables. -/
@[expose] noncomputable def evHom.symbolicPairing [Field F]
    (T : Tbl (fun _ : PSort => MvPolynomial ι F)) :
    (free.pairing F).Hom (symbolic F pairingSig ι) where
  toFun
    | .g₁ => evRepr (T .g₁)
    | .g₂ => evRepr (T .g₂)
    | .gₜ => evReprT (LinearMap.mul F _) (T .g₁) (T .g₂) (T .gₜ)
  map_lin o := o.elim
  map_bil o r₁ r₂ := by
    change Unit at o
    change Repr F at r₁ r₂
    exact evReprT_outer (LinearMap.mul F _) (T .g₁) (T .g₂) (T .gₜ) r₁ r₂

/-- Equal shapes and equal kernels of free-model evaluation at the Type 3 signature.
The target kernel includes both supplied target entries and products of source entries. -/
@[expose] def SameKernel.pairing [Field F]
    (T₀ T₁ : Tbl (fun _ : PSort => MvPolynomial ι F)) : Prop :=
  (∀ s, (T₀ s).length = (T₁ s).length) ∧
    ∀ s (r : PFam (Repr F) (Repr F) (ReprT F) s),
      (evHom.symbolicPairing T₀).toFun s r = 0 ↔
        (evHom.symbolicPairing T₁).toFun s r = 0

/-- Equal Type 3 relation kernels identify the same pairs of free representations. -/
theorem SameKernel.pairing.eq_iff [Field F]
    {T₀ T₁ : Tbl (fun _ : PSort => MvPolynomial ι F)} (h : SameKernel.pairing T₀ T₁)
    (s : PSort) (r r' : PFam (Repr F) (Repr F) (ReprT F) s) :
    (evHom.symbolicPairing T₀).toFun s r = (evHom.symbolicPairing T₀).toFun s r' ↔
      (evHom.symbolicPairing T₁).toFun s r = (evHom.symbolicPairing T₁).toFun s r' := by
  cases s with
  | g₁ =>
    change Repr F at r r'
    have hr := h.2 .g₁ (r - r')
    change evRepr (T₀ .g₁) (r - r') = 0 ↔ evRepr (T₁ .g₁) (r - r') = 0 at hr
    change evRepr (T₀ .g₁) r = evRepr (T₀ .g₁) r' ↔ evRepr (T₁ .g₁) r = evRepr (T₁ .g₁) r'
    simpa only [map_sub, sub_eq_zero] using hr
  | g₂ =>
    change Repr F at r r'
    have hr := h.2 .g₂ (r - r')
    change evRepr (T₀ .g₂) (r - r') = 0 ↔ evRepr (T₁ .g₂) (r - r') = 0 at hr
    change evRepr (T₀ .g₂) r = evRepr (T₀ .g₂) r' ↔ evRepr (T₁ .g₂) r = evRepr (T₁ .g₂) r'
    simpa only [map_sub, sub_eq_zero] using hr
  | gₜ =>
    change ReprT F at r r'
    have hr := h.2 .gₜ (r - r')
    change evReprT (LinearMap.mul F _) (T₀ .g₁) (T₀ .g₂) (T₀ .gₜ) (r - r') = 0 ↔
      evReprT (LinearMap.mul F _) (T₁ .g₁) (T₁ .g₂) (T₁ .gₜ) (r - r') = 0 at hr
    change evReprT (LinearMap.mul F _) (T₀ .g₁) (T₀ .g₂) (T₀ .gₜ) r =
        evReprT (LinearMap.mul F _) (T₀ .g₁) (T₀ .g₂) (T₀ .gₜ) r' ↔
      evReprT (LinearMap.mul F _) (T₁ .g₁) (T₁ .g₂) (T₁ .gₜ) r =
        evReprT (LinearMap.mul F _) (T₁ .g₁) (T₁ .g₂) (T₁ .gₜ) r'
    simpa only [map_sub, sub_eq_zero] using hr

private noncomputable def pairingUnits [Field F] (n : PSort → ℕ) :
    Tbl (PFam (Repr F) (Repr F) (ReprT F))
  | .g₁ => List.ofFn (fun i : Fin (n .g₁) => Pi.single (i : Handle) 1)
  | .g₂ => List.ofFn (fun i : Fin (n .g₂) => Pi.single (i : Handle) 1)
  | .gₜ => List.ofFn (fun i : Fin (n .gₜ) => (Pi.single (i : Handle) 1, 0))

private theorem mapTbl_pairingUnits [Field F] (T : Tbl (fun _ : PSort => MvPolynomial ι F)) :
    mapTbl (fun s => (evHom.symbolicPairing T).toFun s)
      (pairingUnits (fun s => (T s).length)) = T := by
  funext s
  cases s with
  | g₁ =>
    change List.map (evRepr (T .g₁)) (List.ofFn _) = T .g₁
    simp [List.map_ofFn, Function.comp_def, evRepr_single]
  | g₂ =>
    change List.map (evRepr (T .g₂)) (List.ofFn _) = T .g₂
    simp [List.map_ofFn, Function.comp_def, evRepr_single]
  | gₜ =>
    change List.map (evReprT (LinearMap.mul F _) (T .g₁) (T .g₂) (T .gₜ))
      (List.ofFn _) = T .gₜ
    simp [List.map_ofFn, Function.comp_def, evReprT_apply, evRepr_single]

private theorem evReprT_eq_zero_iff [Field F]
    (xs ys zs : List (MvPolynomial ι F))
    (h : LinearIndependent F (Sum.elim zs.get
      (fun ij : Fin xs.length × Fin ys.length => xs.get ij.1 * ys.get ij.2)))
    (r : ReprT F) :
    evReprT (LinearMap.mul F _) xs ys zs r = 0 ↔
      (∀ k < zs.length, r.1 k = 0) ∧
        (∀ i < xs.length, ∀ j < ys.length, r.2 i j = 0) := by
  let c : Fin zs.length ⊕ (Fin xs.length × Fin ys.length) → F :=
    Sum.elim (fun k => r.1 k) (fun ij => r.2 ij.1 ij.2)
  have he : evReprT (LinearMap.mul F _) xs ys zs r =
      ∑ k, c k • Sum.elim zs.get
        (fun ij : Fin xs.length × Fin ys.length => xs.get ij.1 * ys.get ij.2) k := by
    simp only [evReprT_apply, evRepr_apply, LinearMap.mul_apply',
      Fintype.sum_sum_type, Fintype.sum_prod_type, c, Sum.elim_inl, Sum.elim_inr,
      ← Fin.sum_univ_eq_sum_range, List.getD_eq_get]
  rw [he]
  constructor
  · intro hz
    have hc := Fintype.linearIndependent_iff.mp h c hz
    exact ⟨fun k hk => hc (.inl ⟨k, hk⟩), fun i hi j hj => hc (.inr (⟨i, hi⟩, ⟨j, hj⟩))⟩
  · rintro ⟨hz, hp⟩
    apply Finset.sum_eq_zero
    intro k _
    cases k with
    | inl k => simp only [c, Sum.elim_inl, hz k k.isLt, zero_smul]
    | inr ij => simp only [c, Sum.elim_inr, hp ij.1 ij.1.isLt ij.2 ij.2.isLt, zero_smul]

/-- Equal shapes, independent source lists, and independent target entries together with
all source products suffice for equal Type 3 relation kernels. The sum index keeps the
given target entries distinct from the products, including when either list is empty. -/
theorem sameKernel_pairing_of_linearIndependent [Field F]
    {T₀ T₁ : Tbl (fun _ : PSort => MvPolynomial ι F)}
    (hlen : ∀ s, (T₀ s).length = (T₁ s).length)
    (h₀₁ : LinearIndependent F (T₀ .g₁).get)
    (h₀₂ : LinearIndependent F (T₀ .g₂).get)
    (h₀ₜ : LinearIndependent F (Sum.elim (T₀ .gₜ).get
      (fun ij : Fin (T₀ .g₁).length × Fin (T₀ .g₂).length =>
        (T₀ .g₁).get ij.1 * (T₀ .g₂).get ij.2)))
    (h₁₁ : LinearIndependent F (T₁ .g₁).get)
    (h₁₂ : LinearIndependent F (T₁ .g₂).get)
    (h₁ₜ : LinearIndependent F (Sum.elim (T₁ .gₜ).get
      (fun ij : Fin (T₁ .g₁).length × Fin (T₁ .g₂).length =>
        (T₁ .g₁).get ij.1 * (T₁ .g₂).get ij.2))) : SameKernel.pairing T₀ T₁ := by
  refine ⟨hlen, ?_⟩
  intro s r
  cases s with
  | g₁ =>
    change Repr F at r
    change evRepr (T₀ .g₁) r = 0 ↔ evRepr (T₁ .g₁) r = 0
    rw [evRepr_eq_zero_iff _ h₀₁, evRepr_eq_zero_iff _ h₁₁, hlen]
  | g₂ =>
    change Repr F at r
    change evRepr (T₀ .g₂) r = 0 ↔ evRepr (T₁ .g₂) r = 0
    rw [evRepr_eq_zero_iff _ h₀₂, evRepr_eq_zero_iff _ h₁₂, hlen]
  | gₜ =>
    change ReprT F at r
    change evReprT _ _ _ _ r = 0 ↔ evReprT _ _ _ _ r = 0
    rw [evReprT_eq_zero_iff _ _ _ h₀ₜ, evReprT_eq_zero_iff _ _ _ h₁ₜ,
      hlen .g₁, hlen .g₂, hlen .gₜ]

/-- Equal Type 3 relation kernels give identical exact symbolic returned values, by T6. -/
theorem SameKernel.pairing.runGen_fst_eq [Field F] [DecidableEq F] [DecidableEq ι]
    {T₀ T₁ : Tbl (fun _ : PSort => MvPolynomial ι F)} (h : SameKernel.pairing T₀ T₁)
    {α : Type} (oa : OracleComp (genSpec F pairingSig) α) :
    Prod.fst <$> runGen (symbolic F pairingSig ι) (fun _ => id) oa T₀ =
      Prod.fst <$> runGen (symbolic F pairingSig ι) (fun _ => id) oa T₁ := by
  have hu : (fun s => (T₀ s).length) = (fun s => (T₁ s).length) := funext h.1
  have he := run_fst_eq_of_kernel_eq (evHom.symbolicPairing T₀) (evHom.symbolicPairing T₁)
    h.eq_iff oa (pairingUnits (fun s => (T₀ s).length))
  rw [mapTbl_pairingUnits, hu, mapTbl_pairingUnits] at he
  exact he

/-- The master bound also controls the joint hidden point and returned value, after discarding
both final tables. -/
private theorem measureETVDist_pairing_symbolic_fst_le
    [Fintype PSort] [Field F] [DecidableEq F] [DecidableEq ι]
    {α : Type} [MeasurableSpace ((ι → F) × α)]
    (xs : ProbComp (ι → F)) {D : PSort → ℕ} {ε : PSort → ℝ≥0∞} {n : PSort → ℕ}
    (hD : pairingSig.DegreeClosed D)
    (hε : ∀ s (f : MvPolynomial ι F), f ≠ 0 → f.totalDegree ≤ D s →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε s)
    (oa : OracleComp (genSpec F pairingSig) α)
    (hn : ∀ s, IsQueryBoundP oa (appendsTo s) (n s))
    (tbl : Tbl (fun _ : PSort => MvPolynomial ι F)) (hd : DegreeLE D tbl) :
    measureETVDist
      (do let x ← xs
          let z ← runGen (symbolic F pairingSig ι) (fun _ p => MvPolynomial.eval x p) oa tbl
          pure (x, z.1))
      (do let x ← xs
          let z ← runGen (symbolic F pairingSig ι) (fun _ => id) oa tbl
          pure (x, z.1)) ≤
      ∑ s, (((tbl s).length + n s + 1).choose 2 : ℝ≥0∞) * ε s := by
  let : MeasurableSpace ((ι → F) × (α × Tbl (fun _ : PSort => MvPolynomial ι F))) := ⊤
  have h := measureETVDist_runGen_symbolic_le_of_target xs hD hε oa hn tbl hd
  have hm := (measureETVDist_map_le (m := ProbComp) _ _ (fun z : (ι → F) ×
    (α × Tbl (fun _ : PSort => MvPolynomial ι F)) => (z.1, z.2.1)) Measurable.of_discrete).trans h
  simpa only [map_bind, map_pure] using hm

/-! ## Decisional bounds -/

/-- **T7, the decisional master theorem.** Equal shapes and relation kernels bound the
joint hidden-point/output distance by the sum of the two T3 collision terms. Each side
uses its own degree and root-probability bound. -/
theorem measureETVDist_runGen_pairing_sameKernel_le [Fintype PSort] [Field F] [DecidableEq F]
    {α : Type} [MeasurableSpace ((ι → F) × α)]
    (xs : ProbComp (ι → F)) {D₀ D₁ n : PSort → ℕ} {ε₀ ε₁ : PSort → ℝ≥0∞}
    (hD₀ : pairingSig.DegreeClosed D₀) (hD₁ : pairingSig.DegreeClosed D₁)
    (hε₀ : ∀ s (f : MvPolynomial ι F), f ≠ 0 → f.totalDegree ≤ D₀ s →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε₀ s)
    (hε₁ : ∀ s (f : MvPolynomial ι F), f ≠ 0 → f.totalDegree ≤ D₁ s →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε₁ s)
    (oa : OracleComp (genSpec F pairingSig) α)
    (hn : ∀ s, IsQueryBoundP oa (appendsTo s) (n s))
    (T₀ T₁ : Tbl (fun _ : PSort => MvPolynomial ι F))
    (hd₀ : DegreeLE D₀ T₀) (hd₁ : DegreeLE D₁ T₁) (h : SameKernel.pairing T₀ T₁) :
    measureETVDist
      (do let x ← xs
          let z ← runGen (symbolic F pairingSig ι) (fun _ p => MvPolynomial.eval x p) oa T₀
          pure (x, z.1))
      (do let x ← xs
          let z ← runGen (symbolic F pairingSig ι) (fun _ p => MvPolynomial.eval x p) oa T₁
          pure (x, z.1)) ≤
      ∑ s, (((T₀ s).length + n s + 1).choose 2 : ℝ≥0∞) * (ε₀ s + ε₁ s) := by
  classical
  let exactRun (T : Tbl (fun _ : PSort => MvPolynomial ι F)) : ProbComp ((ι → F) × α) := do
    let x ← xs
    let z ← runGen (symbolic F pairingSig ι) (fun _ => id) oa T
    pure (x, z.1)
  -- T6 identifies the exact runs, including their joint outputs with the hidden point.
  have he : exactRun T₀ = exactRun T₁ := by
    simp only [exactRun, bind_pure_comp]
    congr 1
    funext x
    simpa only [Functor.map_map, Function.comp_def] using
      congrArg (fun c : ProbComp α => (fun a => (x, a)) <$> c) (h.runGen_fst_eq oa)
  -- Project T3 on each side and join the bounds through the common exact run.
  have h₀ := measureETVDist_pairing_symbolic_fst_le xs hD₀ hε₀ oa hn T₀ hd₀
  have h₁ := measureETVDist_pairing_symbolic_fst_le xs hD₁ hε₁ oa hn T₁ hd₁
  change measureETVDist _ (exactRun T₁) ≤ _ at h₁
  rw [← he, measureETVDist_comm] at h₁
  have hb := (measureETVDist_triangle _ (exactRun T₀) _).trans (add_le_add h₀ h₁)
  simpa only [← Finset.sum_add_distrib, ← mul_add, ← h.1] using hb

/-- Every measurable event on the hidden point and returned value satisfies the decisional
bound in both directions. -/
theorem prEvent_runGen_pairing_sameKernel_le_add [Fintype PSort] [Field F] [DecidableEq F]
    {α : Type} [MeasurableSpace ((ι → F) × α)]
    (xs : ProbComp (ι → F)) {D₀ D₁ n : PSort → ℕ} {ε₀ ε₁ : PSort → ℝ≥0∞}
    (hD₀ : pairingSig.DegreeClosed D₀) (hD₁ : pairingSig.DegreeClosed D₁)
    (hε₀ : ∀ s (f : MvPolynomial ι F), f ≠ 0 → f.totalDegree ≤ D₀ s →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε₀ s)
    (hε₁ : ∀ s (f : MvPolynomial ι F), f ≠ 0 → f.totalDegree ≤ D₁ s →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε₁ s)
    (oa : OracleComp (genSpec F pairingSig) α)
    (hn : ∀ s, IsQueryBoundP oa (appendsTo s) (n s))
    (T₀ T₁ : Tbl (fun _ : PSort => MvPolynomial ι F))
    (hd₀ : DegreeLE D₀ T₀) (hd₁ : DegreeLE D₁ T₁) (h : SameKernel.pairing T₀ T₁)
    (E : Set ((ι → F) × α)) (hE : MeasurableSet E) :
    (Pr{let x ← xs; let z ← (runGen (symbolic F pairingSig ι)
        (fun _ p => MvPolynomial.eval x p) oa T₀)}[(x, z.1) ∈ E] ≤
      Pr{let x ← xs; let z ← (runGen (symbolic F pairingSig ι)
        (fun _ p => MvPolynomial.eval x p) oa T₁)}[(x, z.1) ∈ E] +
      (∑ s, (((T₀ s).length + n s + 1).choose 2 : ℝ≥0∞) * (ε₀ s + ε₁ s))) ∧
    (Pr{let x ← xs; let z ← (runGen (symbolic F pairingSig ι)
        (fun _ p => MvPolynomial.eval x p) oa T₁)}[(x, z.1) ∈ E] ≤
      Pr{let x ← xs; let z ← (runGen (symbolic F pairingSig ι)
        (fun _ p => MvPolynomial.eval x p) oa T₀)}[(x, z.1) ∈ E] +
      (∑ s, (((T₀ s).length + n s + 1).choose 2 : ℝ≥0∞) * (ε₀ s + ε₁ s))) := by
  classical
  let left : ProbComp ((ι → F) × α) := do
    let x ← xs
    let z ← runGen (symbolic F pairingSig ι) (fun _ p => MvPolynomial.eval x p) oa T₀
    pure (x, z.1)
  let right : ProbComp ((ι → F) × α) := do
    let x ← xs
    let z ← runGen (symbolic F pairingSig ι) (fun _ p => MvPolynomial.eval x p) oa T₁
    pure (x, z.1)
  have hb : measureETVDist left right ≤ _ :=
    measureETVDist_runGen_pairing_sameKernel_le xs hD₀ hD₁ hε₀ hε₁ oa hn T₀ T₁ hd₀ hd₁ h
  have hl := (prEvent_le_prEvent_add_measureETVDist left right (· ∈ E) hE.mem).trans
    (add_le_add le_rfl hb)
  rw [measureETVDist_comm] at hb
  have hr := (prEvent_le_prEvent_add_measureETVDist right left (· ∈ E) hE.mem).trans
    (add_le_add le_rfl hb)
  simpa only [left, right, map_bind, map_pure, bind_pure_comp, Functor.map_map,
    Function.comp_def] using And.intro hl hr

/-- Uniform hidden points over a finite field give the two Schwartz–Zippel terms
`choose (initial size + q + 1) 2 * (degree / card F)` in the decisional bound. -/
theorem measureETVDist_runGen_pairing_sameKernel_uniform_le
    [Fintype PSort] [Field F] [DecidableEq F]
    [Fintype F] [SampleableType (ι → F)]
    {α : Type} [MeasurableSpace ((ι → F) × α)]
    {D₀ D₁ n : PSort → ℕ}
    (hD₀ : pairingSig.DegreeClosed D₀) (hD₁ : pairingSig.DegreeClosed D₁)
    (oa : OracleComp (genSpec F pairingSig) α)
    (hn : ∀ s, IsQueryBoundP oa (appendsTo s) (n s))
    (T₀ T₁ : Tbl (fun _ : PSort => MvPolynomial ι F))
    (hd₀ : DegreeLE D₀ T₀) (hd₁ : DegreeLE D₁ T₁) (h : SameKernel.pairing T₀ T₁) :
    measureETVDist
      (do let x ← $ᵗ (ι → F)
          let z ← runGen (symbolic F pairingSig ι) (fun _ p => MvPolynomial.eval x p) oa T₀
          pure (x, z.1))
      (do let x ← $ᵗ (ι → F)
          let z ← runGen (symbolic F pairingSig ι) (fun _ p => MvPolynomial.eval x p) oa T₁
          pure (x, z.1)) ≤
      ∑ s, (((T₀ s).length + n s + 1).choose 2 : ℝ≥0∞) *
        ((D₀ s : ℝ≥0∞) / Fintype.card F + (D₁ s : ℝ≥0∞) / Fintype.card F) := by
  classical
  have : Finite ι := Finite.of_injective (fun i : ι => Pi.single i (1 : F)) (by
    intro i j h
    by_contra hij
    have he := congrFun h i
    simp [hij] at he)
  apply measureETVDist_runGen_pairing_sameKernel_le ($ᵗ (ι → F)) hD₀ hD₁ _ _ oa hn T₀ T₁ hd₀ hd₁ h
  · intro s f hf hdeg
    exact prob_eval_zero_univ_le_div f hf hdeg
  · intro s f hf hdeg
    exact prob_eval_zero_univ_le_div f hf hdeg

end GroupModel
