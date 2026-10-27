/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.MatrixMap.BlockNorm
public import VCVio.Quantum.Oracle.Compressed.CommutatorSharp
public import VCVio.Quantum.Oracle.Compressed.Size
public import VCVio.Quantum.VC.CheckedRead
public import VCVio.Quantum.Oracle.Compressed.CheckedReadBound
public import VCVio.Quantum.VC.Conditions

/-!
# Commutation of compressed queries, checked reads, and extraction

Both clauses of P2 hold after arbitrary mixed prefixes with a total call budget `t`.
Every ordinary or checked query grows each database by at most one cell, while extraction
preserves its population. The final comparison therefore uses the instability cutoff `t + 1`.

For ordinary queries, the commutator splits into blocks indexed by the extraction tuple and
all databases other than the selected one. The purified-measurement commutator bound applies
on the population-supported state in each block.

For checked reads, fix the final address at each retained outcome and use the same block
indices. The checked-read defect bound sums all optional answers before bounding each block.
The block traces and then the retained-outcome traces sum to at most one. Thus neither the
answer alphabet nor the address space introduces a cardinality factor.

The common error is `24` times the supremum of online-label instability at `t + 1`.
`comBound_compressedVCOracle_eighty` also gives the constant `80` of Chiesa, Di, Hu and Zheng,
ePrint 2025/2166, Lemma 9.2, pp. 58–59.
-/

public section

open Matrix OracleSpec
open scoped Kronecker ENNReal ComplexOrder Matrix.Norms.L2Operator

universe u v w uL vL u₁ v₁

namespace Quantum

/-! ## Graded runtimes

A grading `g` of the runtime register that every step raises by at most one bounds the grade of
the support after a program with a query budget. -/

namespace QuerySupportedOn

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) (g : R.D → ℕ)

/-- **One call of a graded runtime.** If every step of `R` takes support on grades at most `t` to
support on grades at most `t + 1`, so does every call, with any remainder `E` carried along. -/
theorem queryStep_of_step
    (hR : ∀ i r t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + 1))
          ((R.step i).branch r σ))
    {A : QReg} {t : ℕ} (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E) (r : spec.Result i)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (h : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic t) ρ) :
    QuerySupportedOn (fun m : (spec.Out i × E) × R.D ↦ g m.2) (Set.Iic (t + 1))
      ((R.queryStep i E ℓ).branch r ρ) := by
  rw [QuantumRuntime.queryStep_branch_apply, DSubInstrument.branch_frame_apply]
  have h₁ := (h.branch_relabel (QuantumRuntime.queryEquivIn ℓ R.D)).imp
    (q' := fun m : (spec.In i × R.D) × E ↦ g m.1.2) (S' := Set.Iic t) fun m hm ↦ by
      obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ R.D).surjective m
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
  have h₂ := QuerySupportedOn.amplify_fst (q := fun m : spec.In i × R.D ↦ g m.2)
    (q' := fun m : spec.Out i × R.D ↦ g m.2) (fun σ hσ ↦ hR i r t σ hσ) h₁
  refine (h₂.branch_relabel (QuantumRuntime.queryEquivOut _ R.D E)).imp fun m hm ↦ ?_
  obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivOut _ R.D E).surjective m
  rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm

/-- Spending one call of a nonzero budget lowers its total by one. -/
theorem sum_update_sub_one_add_one {P : Type*} [Fintype P] [DecidableEq P] {b : P → ℕ} {i : P}
    (hb : 0 < b i) : ∑ j, Function.update b i (b i - 1) j + 1 = ∑ j, b j := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.compl_eq_univ_sdiff,
    Fintype.sum_eq_add_sum_compl i b]
  omega

variable {L : LocalSig.{uL, vL}} {W : QReg → Type w} {A : QReg}

/-- **The grade after a program.** If every step of `R` raises the grade of the support by at most
one, a program within the budget `b` takes support on grades at most `t` to support on grades at
most `t + ∑ i, b i` on every branch. -/
theorem run_of_step [Fintype spec.Port]
    (hR : ∀ i r t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + 1))
          ((R.step i).branch r σ))
    (I : L.Interp) {x : QuantumComp L spec W A} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    {t : ℕ} {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic t) ρ) (p : Σ u, W u) :
    QuerySupportedOn (fun m : p.1 × R.D ↦ g m.2) (Set.Iic (t + ∑ i, b i))
      ((R.run I x).branch p ρ) := by
  classical
  induction x using QuantumComp.inductionOn generalizing b t with
  | pure _ y =>
    rw [QuantumRuntime.run_pure]
    by_cases hp : p = ⟨_, y⟩
    · subst hp
      rw [DSubInstrument.branch_ret_self]
      exact hρ.mono (Set.Iic_subset_Iic.mpr (Nat.le_add_right t _))
    · rw [DSubInstrument.branch_ret_of_ne _ hp]
      exact querySupportedOn_zero _ _
  | primBind _ o k ih =>
    rw [QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply]
    exact QuerySupportedOn.tsum fun c ↦ ih c ((QuantumComp.isQueryBound_primBind_iff o k b).mp
      hx c) (QuerySupportedOn.amplify_snd (q := g) hρ _)
  | queryBind _ i E ℓ k ih =>
    obtain ⟨hq, hk⟩ := (QuantumComp.isQueryBound_queryBind_iff i E ℓ k b).mp hx
    rw [QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply]
    refine QuerySupportedOn.tsum fun r ↦ ?_
    have h := ih r (hk r) (queryStep_of_step R g hR i E ℓ r hρ)
    rwa [Nat.add_assoc, Nat.add_comm 1, sum_update_sub_one_add_one hq] at h

/-- A total call budget bounds the grade independently of the number of ports. -/
theorem run_of_total_step
    (hR : ∀ i r t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + 1))
          ((R.step i).branch r σ))
    (I : L.Interp) {x : QuantumComp L spec W A} {n : ℕ} (hx : x.IsTotalQueryBound n)
    {t : ℕ} {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic t) ρ) (p : Σ u, W u) :
    QuerySupportedOn (fun m : p.1 × R.D ↦ g m.2) (Set.Iic (t + n))
      ((R.run I x).branch p ρ) := by
  classical
  induction x using QuantumComp.inductionOn generalizing n t with
  | pure _ y =>
    rw [QuantumRuntime.run_pure]
    by_cases hp : p = ⟨_, y⟩
    · subst hp
      rw [DSubInstrument.branch_ret_self]
      exact hρ.mono (Set.Iic_subset_Iic.mpr (Nat.le_add_right t _))
    · rw [DSubInstrument.branch_ret_of_ne _ hp]
      exact querySupportedOn_zero _ _
  | primBind _ o k ih =>
    rw [QuantumComp.isTotalQueryBound_primBind_iff] at hx
    rw [QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply]
    exact QuerySupportedOn.tsum fun c ↦ ih c (hx c) (QuerySupportedOn.amplify_snd (q := g) hρ _)
  | queryBind _ i E ℓ k ih =>
    obtain ⟨hq, hk⟩ := (QuantumComp.isTotalQueryBound_queryBind_iff i E ℓ k n).mp hx
    rw [QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply]
    refine QuerySupportedOn.tsum fun r ↦ ?_
    have h := ih r (hk r) (queryStep_of_step R g hR i E ℓ r hρ)
    convert h using 1
    congr 1
    omega

end QuerySupportedOn

namespace EmulatedOracle

variable {P : Type u} {In : P → QReg} (F : EmulatedOracle P In) (g : F.S → ℕ)

/-- The steps of an emulated oracle whose unitaries raise the grade by at most one raise the grade
of the support by at most one. -/
theorem querySupportedOn_toRuntime_step
    (hF : ∀ i a a' d d', F.U i (a', d') (a, d) ≠ 0 → g d' ≤ g d + 1)
    (i : P) (r : Unit) (t : ℕ)
    (σ : Matrix (In i × F.S) (In i × F.S) ℂ)
    (hσ : QuerySupportedOn (fun m : In i × F.S ↦ g m.2) (Set.Iic t) σ) :
    QuerySupportedOn (fun m : In i × F.S ↦ g m.2) (Set.Iic (t + 1))
      ((F.toRuntime.step i).branch r σ) := by
  rw [toRuntime_step_branch]
  exact QuerySupportedOn.conj hσ fun m' m hK hm ↦
    (hF i m.1 m'.1 m.2 m'.2 hK).trans (Nat.add_le_add_right hm 1)

omit F g in
/-- The coherent unitary raises the grade by at most one when every port does. -/
theorem coherent_U_grade {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg}
    (F : EmulatedOracle P In) (g : F.S → ℕ)
    (hF : ∀ i a a' d d', F.U i (a', d') (a, d) ≠ 0 → g d' ≤ g d + 1) (i : Unit)
    (a a' : cohIn In) (d d' : F.S) (h : F.coherent.U i (a', d') (a, d) ≠ 0) :
    g d' ≤ g d + 1 := by
  obtain ⟨p', b'⟩ := a'
  obtain ⟨p, b⟩ := a
  by_cases hp : p' = p
  · subst hp
    rw [coherent_U_apply_self] at h
    exact hF p' b b' d d' h
  · exact absurd (coherent_U_apply_of_ne F hp b' b d' d) h

end EmulatedOracle

/-! ## The size invariant for the k compressed oracles with the extractor -/

section sizeInvariant

open EmulatedOracle (cohSpec)

variable {k : ℕ} {X Y Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  {Dm : Fin k → Type} (ME : MultiExtractor k Cm Dm (Fin k → Database X Y))
  (code : TpDCode k Dm Z)

/-- Every port of `EO^(Ext)` for the k compressed oracles changes the database `D_i` in at most
one cell: an oracle port `j ≠ i` leaves it alone, the port `i` is the compressed oracle on it,
and the extraction port does not change the private register. -/
theorem compressedVCOracle_withExtract_U_size_le (i : Fin k) (p : Fin k ⊕ Unit)
    (a a' : extIn k X Y Cm Z p) (d d' : Fin k → Database X Y)
    (h : ((compressedVCOracle k X Y).withExtract ME code).U p (a', d') (a, d) ≠ 0) :
    (d' i).size ≤ (d i).size + 1 := by
  rcases p with j | u
  · change onFactor (splitAt (X × Y) (Database X Y) j)
      (compressedOracle X Y) (a', d') (a, d) ≠ 0
      at h
    rw [onFactor_apply] at h
    split_ifs at h with hsplit
    · change (fun l : {l // l ≠ j} ↦ d' l.1) = fun l ↦ d l.1 at hsplit
      change compressedOracle X Y (a', d' j) (a, d j) ≠ 0 at h
      by_cases hij : i = j
      · subst hij
        exact size_le_of_compressedOracle_apply_ne_zero h
      · have hi : d' i = d i := congrFun hsplit ⟨i, hij⟩
        rw [hi]
        exact Nat.le_succ _
    · exact absurd rfl h
  · obtain ⟨tic', z'⟩ := a'
    obtain ⟨tic, z⟩ := a
    change extractUnitary ME code ((tic', z'), d') ((tic, z), d) ≠ 0 at h
    rw [extractUnitary_apply] at h
    split_ifs at h with hc
    · rw [hc.2.2]
      exact Nat.le_succ _
    · exact absurd rfl h

/-- **The size invariant for `EO^(Ext)`.** After a program that makes at most `t` calls to the
coherent port of `EO^(Ext)` for the k compressed oracles, the joint state at every outcome is
supported on tuples of databases whose `i`-th database has at most `t` nonempty cells. -/
theorem querySupportedOn_jointPost₂_compressedVCOracle_withExtract (i : Fin k) {A B : QReg}
    {α : Type w} (x : QuantumComp₂ LocalSig.instruments.{v} (cohSpec (extIn k X Y Cm Z)) A B α)
    {t : ℕ} (hx : x.IsQueryBound fun _ ↦ t) (ρ : SubState A) (a : α) :
    QuerySupportedOn (fun m : B × (Fin k → Database X Y) ↦ (m.2 i).size) (Set.Iic t)
      (((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime.jointPost₂
        .instruments x ρ a).matrix := by
  set F := ((compressedVCOracle k X Y).withExtract ME code)
  have hR := F.coherent.querySupportedOn_toRuntime_step
    (fun d : Fin k → Database X Y ↦ (d i).size)
    fun j b b' d d' h ↦ F.coherent_U_grade (fun d : Fin k → Database X Y ↦ (d i).size)
      (fun p b b' d d' h ↦ compressedVCOracle_withExtract_U_size_le ME code i p b b' d d' h)
      j b b' d d' h
  have h0 : QuerySupportedOn (fun m : A × (Fin k → Database X Y) ↦ (m.2 i).size) (Set.Iic 0)
      (ρ.matrix ⊗ₖ F.coherent.toRuntime.init.matrix) := by
    intro m m' hm
    change (ρ.matrix ⊗ₖ
      (SubState.basis fun _ : Fin k ↦ (Database.empty : Database X Y)).matrix)
      m m' ≠ 0 at hm
    rw [SubState.matrix_basis, kroneckerMap_apply] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · refine ⟨?_, ?_⟩
      · change (m.2 i).size ≤ 0
        rw [← he.1]
        simp
      · change (m'.2 i).size ≤ 0
        rw [← he.2]
        simp
    · exact absurd rfl h
  have h := QuerySupportedOn.run_of_step F.coherent.toRuntime
    (fun d : Fin k → Database X Y ↦ (d i).size) hR .instruments hx h0 ⟨B, rfl, a⟩
  rw [QuantumRuntime.matrix_jointPost₂, QuantumRuntime.branch_run₂]
  simp only [Finset.univ_unique, Finset.sum_singleton, zero_add] at h
  exact h

omit [AddCommGroup Y] in
/-- Flattening the family identifies each optional answer with a single-cell projector. -/
theorem compressedReadProjector_eq_checkedReadProjector (c : Fin k × X) (a : Option Y) :
    compressedReadProjector k X Y c a = (checkedReadProjector c a).submatrix
      (Equiv.curry (Fin k) X (Option Y)).symm
      (Equiv.curry (Fin k) X (Option Y)).symm := by
  have he : checkedReadProjector c a = compressAll (Fin k × X) Y *
      diagonal (fun D : Database (Fin k × X) Y ↦ if D c = a then 1 else 0) *
        compressAll (Fin k × X) Y := by
    ext D D'
    rw [checkedReadProjector_apply, Matrix.mul_apply]
    simp only [mul_diagonal]
    symm
    simpa only [compressAll, mul_left_comm, mul_assoc] using
      sum_mul_piKron_mul_piKron (fun _ : Fin k × X ↦ cellCompress Y)
        (fun _ : Fin k × X ↦ cellCompress Y) c (fun z ↦ if z = a then 1 else 0) D D'
  have hd : (diagonal (fun D : Fin k → Database X Y ↦ if D c.1 c.2 = a then 1 else 0) :
      Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ) =
      (diagonal (fun D : Database (Fin k × X) Y ↦ if D c = a then (1 : ℂ) else 0)).submatrix
        (Equiv.curry (Fin k) X (Option Y)).symm
        (Equiv.curry (Fin k) X (Option Y)).symm := by
    rw [submatrix_diagonal_equiv]
    rfl
  rw [compressedReadProjector, CompressedReplay.compressDatabases_eq_flat, hd, he,
    submatrix_mul_equiv, submatrix_mul_equiv]

/-- A read changes only its selected cell, so every database grows by at most one. -/
theorem compressedReadProjector_size_le (i : Fin k) (c : Fin k × X) (a : Option Y)
    (D D' : Fin k → Database X Y) (h : compressedReadProjector k X Y c a D' D ≠ 0) :
    (D' i).size ≤ (D i).size + 1 := by
  rcases c with ⟨j, y⟩
  rw [compressedReadProjector_eq_checkedReadProjector] at h
  have he := eq_update_of_checkedReadProjector_ne_zero (j, y) a h
  by_cases hi : i = j
  · subst i
    have hd : D' j = Function.update (D j) y (D' j y) := by
      funext x
      have hx := congrFun he (j, x)
      simpa only [Equiv.curry_symm_apply, Function.uncurry, Function.update_apply,
        Prod.mk.injEq, true_and] using hx
    rw [hd]
    exact Database.size_update_le _ _ _
  · have hd : D' i = D i := by
      funext x
      have hx := congrFun he (i, x)
      simpa [Equiv.curry_symm_apply, Function.uncurry, Function.update_apply, hi] using hx
    rw [hd]
    exact Nat.le_succ _

/-- Every mixed-runtime step raises the population of a selected database by at most one. -/
theorem compressedVCOracle_mixed_step_size (i : Fin k)
    (p : (mixedExtSpec k X Y Cm Z).Port) (r : (mixedExtSpec k X Y Cm Z).Result p)
    (t : ℕ) (σ : Matrix ((mixedExtSpec k X Y Cm Z).In p × (Fin k → Database X Y))
      ((mixedExtSpec k X Y Cm Z).In p × (Fin k → Database X Y)) ℂ)
    (hσ : QuerySupportedOn (fun m ↦ (m.2 i).size) (Set.Iic t) σ) :
    QuerySupportedOn (fun m ↦ (m.2 i).size) (Set.Iic (t + 1))
      (((compressedVCOracle k X Y).mixedExtractRuntime ME code).step p |>.branch r <| σ) := by
  cases p with
  | inl p =>
    exact ((compressedVCOracle k X Y).withExtract ME code).coherent.querySupportedOn_toRuntime_step
      (fun d ↦ (d i).size)
      (fun j b b' d d' h ↦ EmulatedOracle.coherent_U_grade _ (fun d ↦ (d i).size)
        (fun p b b' d d' h ↦ compressedVCOracle_withExtract_U_size_le ME code i p b b' d d' h)
        j b b' d d' h) p r t σ hσ
  | inr c =>
    change QuerySupportedOn _ _ (((compressedVCOracle k X Y).classicalRead.step c).branch r σ)
    erw [ProjectiveClassicalAnswers.step_branch]
    refine hσ.conj ?_
    intro m' m h hm
    exact (compressedReadProjector_size_le i c r m.2 m'.2
      (right_ne_zero_of_mul h)).trans (Nat.add_le_add_right hm 1)

/-- Mixed prefixes count every call toward one population bound. -/
theorem querySupportedOn_jointPost₂_compressedVCOracle_mixed (i : Fin k) {A B : QReg}
    {α : Type w} (x : QuantumComp₂ LocalSig.instruments.{v} (mixedExtSpec k X Y Cm Z) A B α)
    {t : ℕ} (hx : x.IsTotalQueryBound t) (ρ : SubState A) (a : α) :
    QuerySupportedOn (fun m : B × (Fin k → Database X Y) ↦ (m.2 i).size) (Set.Iic t)
      (((compressedVCOracle k X Y).mixedExtractRuntime ME code).jointPost₂
        .instruments x ρ a).matrix := by
  let R := (compressedVCOracle k X Y).mixedExtractRuntime ME code
  have h0 : QuerySupportedOn (fun m : A × (Fin k → Database X Y) ↦ (m.2 i).size) (Set.Iic 0)
      (ρ.matrix ⊗ₖ R.init.matrix) := by
    intro m m' hm
    change (ρ.matrix ⊗ₖ
      (SubState.basis fun _ : Fin k ↦ (Database.empty : Database X Y)).matrix)
      m m' ≠ 0 at hm
    rw [SubState.matrix_basis, kroneckerMap_apply] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · constructor
      · change (m.2 i).size ≤ 0
        rw [← he.1]
        simp
      · change (m'.2 i).size ≤ 0
        rw [← he.2]
        simp
    · exact absurd rfl h
  have h := QuerySupportedOn.run_of_total_step R (fun d ↦ (d i).size)
    (compressedVCOracle_mixed_step_size ME code i) .instruments hx h0 ⟨B, rfl, a⟩
  rw [QuantumRuntime.matrix_jointPost₂, QuantumRuntime.branch_run₂]
  simp only [zero_add] at h
  exact h

end sizeInvariant

/-! ## Block decomposition of the commutation defect -/

/-- A block-diagonal matrix has norm at most `r` when every block does. -/
theorem _root_.Matrix.l2_opNorm_blockDiagonal_le {o m : Type*} [Fintype o] [DecidableEq o]
    [Fintype m] [DecidableEq m] (F : o → Matrix m m ℂ) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ c, ‖F c‖ ≤ r) : ‖blockDiagonal F‖ ≤ r := by
  have he : blockDiagonal F = (∑ c, single c c (1 : ℂ) ⊗ₖ F c).submatrix
      (Equiv.prodComm m o) (Equiv.prodComm m o) := by
    ext ⟨a, c⟩ ⟨b, c'⟩
    rw [submatrix_apply, Equiv.prodComm_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
      Prod.swap_prod_mk, sum_single_kronecker_apply, blockDiagonal_apply]
  rw [he, l2_opNorm_submatrix_equiv, l2_opNorm_sum_single_kronecker]
  exact Real.iSup_le h hr

/-- **The trace bound through a block-diagonal operator on a projected state.** If `C Q` agrees
with `(⊕_c F c) Q` after reindexing by `e`, every block has `‖F c‖² ≤ r`, and the positive
semidefinite `σ` is fixed by conjugation with `Q`, then `tr(C σ C†) ≤ r tr σ`. -/
theorem re_trace_mul_mul_conjTranspose_le_of_blockDiagonal {N B o : Type*} [Fintype N]
    [Fintype B] [DecidableEq B] [Finite o] [DecidableEq o] (e : N ≃ B × o)
    (F : o → Matrix B B ℂ) {r : ℝ} (hr : 0 ≤ r) (hF : ∀ c, ‖F c‖ ^ 2 ≤ r)
    {C Q σ : Matrix N N ℂ} (hC : C * Q = (blockDiagonal F).submatrix e e * Q)
    (hσ : MatrixMap.conj Q σ = σ) (hpsd : σ.PosSemidef) :
    (C * σ * Cᴴ).trace.re ≤ r * σ.trace.re := by
  classical
  have := Fintype.ofFinite o
  have key : C * σ * Cᴴ = MatrixMap.conj ((blockDiagonal F).submatrix e e) σ := by
    calc _ = MatrixMap.conj C (MatrixMap.conj Q σ) := by rw [hσ]; rfl
      _ = MatrixMap.conj ((blockDiagonal F).submatrix e e * Q) σ := by
        rw [← hC, MatrixMap.conj_mul]; rfl
      _ = _ := by rw [MatrixMap.conj_mul, LinearMap.comp_apply, hσ]
  have hb : ∀ c, ‖F c‖ ≤ √r := fun c ↦ (le_abs_self _).trans (Real.abs_le_sqrt (hF c))
  have hn : ‖(blockDiagonal F).submatrix e e‖ ^ 2 ≤ r := by
    rw [l2_opNorm_submatrix_equiv]
    calc ‖blockDiagonal F‖ ^ 2 ≤ √r ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _)
            (l2_opNorm_blockDiagonal_le F (Real.sqrt_nonneg r) hb) 2
      _ = r := Real.sq_sqrt hr
  rw [key]
  exact (MatrixMap.re_trace_conj_le _ hpsd).trans
    (mul_le_mul_of_nonneg_right hn hpsd.trace_re_nonneg)

section blocks

variable {ι XY Tc Z Env DB : Type*} [DecidableEq ι]

/-- The regrouping of the output of a P2 adversary and the tuple of databases into a block
register and a block index: the block register holds the oracle query register, the database
`D_i`, the extraction output and the rest; the block index holds the tuple `tic` read by the
extractor and the other databases. -/
@[expose]
def comSplit (i : ι) :
    ((XY × (Tc × Z)) × Env) × (ι → DB) ≃
      ((XY × DB) × (Z × Env)) × (Tc × ({j // j ≠ i} → DB))
    where
  toFun a := (((a.1.1.1, a.2 i), (a.1.1.2.2, a.1.2)), (a.1.1.2.1, fun j ↦ a.2 j.1))
  invFun b := (((b.1.1.1, (b.2.1, b.1.2.1)), b.1.2.2),
    (Equiv.funSplitAt i DB).symm (b.1.1.2, b.2.2))
  left_inv a := Prod.ext rfl ((Equiv.funSplitAt i DB).symm_apply_apply a.2)
  right_inv b := by
    have h := (Equiv.funSplitAt i DB).apply_symm_apply (b.1.1.2, b.2.2)
    rw [Equiv.funSplitAt_apply, Prod.mk.injEq] at h
    exact Prod.ext (Prod.ext (Prod.ext rfl h.1) rfl) (Prod.ext rfl h.2)

/-- `comSplit i` on a basis state. -/
@[simp]
theorem comSplit_apply (i : ι) (xy : XY) (tc : Tc) (z : Z) (env : Env) (d : ι → DB) :
    comSplit i (((xy, (tc, z)), env), d) = (((xy, d i), (z, env)), (tc, fun j ↦ d j.1)) :=
  rfl

omit [DecidableEq ι] in
/-- A tuple is determined by its `i`-th entry and the other entries. -/
theorem eq_iff_apply_eq_and_restrict_eq (i : ι) {d d' : ι → DB} :
    d = d' ↔ d i = d' i ∧ (fun j : {j // j ≠ i} ↦ d j.1) = fun j ↦ d' j.1 := by
  classical
  rw [← (Equiv.funSplitAt i DB).injective.eq_iff, Equiv.funSplitAt_apply, Equiv.funSplitAt_apply,
    Prod.mk.injEq]

/-- Replacing the `i`-th entry of a tuple split at `i`. -/
theorem update_funSplitAt_symm (i : ι) (D D' : DB) (f : {j // j ≠ i} → DB) :
    Function.update ((Equiv.funSplitAt i DB).symm (D', f)) i D =
      (Equiv.funSplitAt i DB).symm (D, f) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

variable [DecidableEq XY] [DecidableEq Tc] [DecidableEq Z] [DecidableEq Env] [DecidableEq DB]
  [Fintype ι]

omit [DecidableEq XY] in
/-- **An operator on the query register and one table, placed on the output of a P2 adversary**,
is block diagonal for `comSplit i`, with the constant block `M ⊗ 1`. -/
theorem onFactor_slotFst₃_onFactor_splitAt (i : ι) (M : Matrix (XY × DB) (XY × DB) ℂ) :
    onFactor (slotFst₃ XY (Tc × Z) Env (ι → DB)) (onFactor (splitAt XY DB i) M) =
      (blockDiagonal fun _ : Tc × ({j // j ≠ i} → DB) ↦
        M ⊗ₖ (1 : Matrix (Z × Env) (Z × Env) ℂ)).submatrix (comSplit i) (comSplit i) := by
  ext ⟨⟨⟨xy, tc, z⟩, env⟩, d⟩ ⟨⟨⟨xy', tc', z'⟩, env'⟩, d'⟩
  simp only [onFactor_apply, slotFst₃, Equiv.coe_fn_mk, splitAt_apply, submatrix_apply,
    comSplit_apply, blockDiagonal_apply, kroneckerMap_apply, one_apply, Prod.mk.injEq]
  by_cases h₁ : tc = tc' <;> by_cases h₂ : z = z' <;> by_cases h₃ : env = env' <;>
    by_cases h₄ : (fun j : {j // j ≠ i} ↦ d j.1) = fun j ↦ d' j.1 <;>
      simp [h₁, h₂, h₃, h₄]

/-- **A diagonal operator on one table, on the output of a P2 adversary**, is block diagonal for
`comSplit i`. -/
theorem diagonal_apply_eq_blockDiagonal (i : ι) (p : DB → ℂ) :
    diagonal (fun m : ((XY × (Tc × Z)) × Env) × (ι → DB) ↦ p (m.2 i)) =
      (blockDiagonal fun _ : Tc × ({j // j ≠ i} → DB) ↦
        diagonal (fun a : XY × DB ↦ p a.2)
          ⊗ₖ (1 : Matrix (Z × Env) (Z × Env) ℂ)).submatrix
        (comSplit i) (comSplit i) := by
  ext ⟨⟨⟨xy, tc, z⟩, env⟩, d⟩ ⟨⟨⟨xy', tc', z'⟩, env'⟩, d'⟩
  simp only [diagonal_apply, submatrix_apply, comSplit_apply, blockDiagonal_apply,
    kroneckerMap_apply, one_apply, Prod.mk.injEq]
  simp only [eq_iff_apply_eq_and_restrict_eq i (d := d)]
  by_cases h₁ : tc = tc' <;> by_cases h₂ : z = z' <;> by_cases h₃ : env = env' <;>
    by_cases h₄ : (fun j : {j // j ≠ i} ↦ d j.1) = fun j ↦ d' j.1 <;>
    by_cases h₅ : xy = xy' <;> by_cases h₆ : d i = d' i <;>
      simp [h₁, h₂, h₃, h₄, h₅, h₆]

variable [AddGroup Z]

/-- **A controlled shift of the extraction register, on the output of a P2 adversary**, is block
diagonal for `comSplit i`: if `V |(tc, z), s⟩ = |(tc, z + f tc s), s⟩`, the block at
`(tc, (d_j)_{j ≠ i})` is the purified measurement of the label `D ↦ f tc d` of the table
`D = d_i`, with members `1 ⊗ xorShift ⊗ 1`. -/
theorem onFactor_slotSnd₃_eq_blockDiagonal (i : ι) (f : Tc → (ι → DB) → Z)
    {V : Matrix ((Tc × Z) × (ι → DB)) ((Tc × Z) × (ι → DB)) ℂ}
    (hV : ∀ tc tc' z z' s s', V ((tc, z), s) ((tc', z'), s') =
      if tc = tc' ∧ z = z' + f tc' s' ∧ s = s' then 1 else 0) :
    onFactor (slotSnd₃ XY (Tc × Z) Env (ι → DB)) V =
      (blockDiagonal fun c : Tc × ({j // j ≠ i} → DB) ↦
        labelControlled (fun a : (XY × DB) × (Z × Env) ↦
            f c.1 ((Equiv.funSplitAt i DB).symm (a.1.2, c.2)))
          fun l ↦ (1 : Matrix (XY × DB) (XY × DB) ℂ) ⊗ₖ
            (xorShift Z l ⊗ₖ (1 : Matrix Env Env ℂ))).submatrix
              (comSplit i) (comSplit i) := by
  ext ⟨⟨⟨xy, tc, z⟩, env⟩, d⟩ ⟨⟨⟨xy', tc', z'⟩, env'⟩, d'⟩
  simp only [onFactor_apply, slotSnd₃, Equiv.coe_fn_mk, hV, submatrix_apply,
    comSplit_apply, blockDiagonal_apply, labelControlled_apply, kroneckerMap_apply, one_apply,
    xorShift_apply, Prod.mk.injEq]
  have hd : (Equiv.funSplitAt i DB).symm (d i, fun j : {j // j ≠ i} ↦ d j.1) = d :=
    (Equiv.funSplitAt i DB).symm_apply_apply d
  rw [hd]
  by_cases hdd : d = d'
  · subst hdd
    by_cases h₁ : tc = tc' <;> by_cases h₃ : env = env' <;> by_cases h₅ : xy = xy' <;>
      simp [h₁, h₃, h₅]
  · have h := mt (eq_iff_apply_eq_and_restrict_eq i).mpr hdd
    by_cases h₄ : (fun j : {j // j ≠ i} ↦ d j.1) = fun j ↦ d' j.1 <;>
      by_cases h₆ : d i = d' i
    · exact absurd ⟨h₆, h₄⟩ h
    all_goals simp [hdd, h₄, h₆]

end blocks

/-! ## The commutator on one block -/

section blockAlgebra

variable {X Y W : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype W] [DecidableEq W]

/-- The compressed oracle raises the number of nonempty cells by at most one:
`cO P_size^(t) = P_size^(t+1) cO P_size^(t)`. -/
theorem compressedOracle_mul_sizeProjector (t : ℕ) :
    compressedOracle X Y * sizeProjector X Y t =
      sizeProjector X Y (t + 1) * compressedOracle X Y * sizeProjector X Y t := by
  ext a b
  simp only [sizeProjector, mul_diagonal, diagonal_mul]
  by_cases hb : b.2.size ≤ t
  · by_cases h : compressedOracle X Y a b = 0
    · simp [h]
    · have ha : a.2.size ≤ t + 1 :=
        (size_le_of_compressedOracle_apply_ne_zero h).trans (Nat.add_le_add_right hb 1)
      simp [ha, hb]
  · simp [hb]

omit [AddCommGroup Y] in
/-- `P_size^(t+1) P_size^(t) = P_size^(t)`. -/
theorem sizeProjector_succ_mul_sizeProjector (t : ℕ) :
    sizeProjector X Y (t + 1) * sizeProjector X Y t = sizeProjector X Y t := by
  rw [sizeProjector, sizeProjector, diagonal_mul_diagonal]
  congr 1
  funext m
  by_cases h : m.2.size ≤ t
  · simp [h, Nat.le_succ_of_le h]
  · simp [h]

omit [AddCommGroup Y] in
/-- A purified measurement of a label of the database commutes with `P_size^(s) ⊗ 1`. -/
theorem labelControlled_mul_sizeProjector_kronecker {ι : Type*} (π : Database X Y → ι)
    (U : ι → Matrix W W ℂ) (s : ℕ) :
    labelControlled (fun a : ((X × Y) × Database X Y) × W ↦ π a.1.2)
          (fun l ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ)
            ⊗ₖ U l) *
        (sizeProjector X Y s ⊗ₖ (1 : Matrix W W ℂ)) =
      (sizeProjector X Y s ⊗ₖ (1 : Matrix W W ℂ)) *
        labelControlled (fun a : ((X × Y) × Database X Y) × W ↦ π a.1.2)
          (fun l ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ)
            ⊗ₖ U l) := by
  have hP : sizeProjector X Y s ⊗ₖ (1 : Matrix W W ℂ) =
      diagonal fun a ↦ if a.1.2.size ≤ s then 1 else 0 := by
    ext ⟨a, w⟩ ⟨b, w'⟩
    by_cases hab : a = b <;> by_cases hw : w = w' <;> simp [sizeProjector, hab, hw]
  ext ⟨a, w⟩ ⟨b, w'⟩
  rw [hP, mul_diagonal, diagonal_mul, labelControlled_apply, kroneckerMap_apply, one_apply]
  by_cases hab : a = b
  · subst hab
    simp only [↓reduceIte]
    ring
  · simp [hab]

/-- **The truncation step on one block.** If `L` commutes with `P_size^(t) ⊗ 1`, then on the
range of `P_size^(t) ⊗ 1` the commutator of `L` with `cO ⊗ 1` is its commutator with
the truncated oracle `O^(t+1) ⊗ 1`. -/
theorem commutator_mul_sizeProjector_kronecker_eq (t : ℕ)
    (L : Matrix (((X × Y) × Database X Y) × W) (((X × Y) × Database X Y) × W) ℂ)
    (hL : L * (sizeProjector X Y t ⊗ₖ (1 : Matrix W W ℂ)) =
      (sizeProjector X Y t ⊗ₖ (1 : Matrix W W ℂ)) * L) :
    (L * (compressedOracle X Y ⊗ₖ (1 : Matrix W W ℂ)) -
        (compressedOracle X Y ⊗ₖ (1 : Matrix W W ℂ)) * L) *
        (sizeProjector X Y t ⊗ₖ (1 : Matrix W W ℂ)) =
      (L * (truncatedOracle X Y (t + 1) ⊗ₖ (1 : Matrix W W ℂ)) -
        (truncatedOracle X Y (t + 1) ⊗ₖ (1 : Matrix W W ℂ)) * L) *
        (sizeProjector X Y t ⊗ₖ (1 : Matrix W W ℂ)) := by
  have hT : (truncatedOracle X Y (t + 1) ⊗ₖ (1 : Matrix W W ℂ)) *
      (sizeProjector X Y t ⊗ₖ (1 : Matrix W W ℂ)) =
      (compressedOracle X Y ⊗ₖ (1 : Matrix W W ℂ)) *
        (sizeProjector X Y t ⊗ₖ (1 : Matrix W W ℂ)) := by
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, truncatedOracle, Matrix.mul_assoc _ _
      (sizeProjector X Y t), sizeProjector_succ_mul_sizeProjector,
      ← compressedOracle_mul_sizeProjector]
  have e : ∀ M, (L * M - M * L) * (sizeProjector X Y t ⊗ₖ (1 : Matrix W W ℂ)) =
      L * (M * (sizeProjector X Y t ⊗ₖ (1 : Matrix W W ℂ))) -
        M * (sizeProjector X Y t ⊗ₖ (1 : Matrix W W ℂ)) * L := fun M ↦ by
    rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc M, hL, ← Matrix.mul_assoc M]
  rw [e, e, hT]

end blockAlgebra

section defectBlocks

variable {X Y Tc Z Env ι : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [Fintype Tc] [DecidableEq Tc] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  [Fintype Env] [DecidableEq Env] [Fintype ι] [DecidableEq ι]

/-- **The commutation defect on the range of `|D_i| ≤ t` is block diagonal.** Let `V` add
`f tc s` to the extraction register, placed on the output of a P2 adversary as in
`Quantum.comDefect`, and let the compressed oracle act on the query register and the table `D_i`.
On the range of the projector onto `|D_i| ≤ t`, their commutator is the block-diagonal operator,
for `Quantum.comSplit i`, whose block at `c = (tc, (D_j)_{j ≠ i})` is the commutator of the
purified measurement of `D_i ↦ f tc D` with the truncated oracle `O^(t+1) ⊗ 1`. -/
theorem commutator_onFactor_mul_diagonal_eq (i : ι) (f : Tc → (ι → Database X Y) → Z)
    {V : Matrix ((Tc × Z) × (ι → Database X Y)) ((Tc × Z) × (ι → Database X Y)) ℂ}
    (hV : ∀ tc tc' z z' s s', V ((tc, z), s) ((tc', z'), s') =
      if tc = tc' ∧ z = z' + f tc' s' ∧ s = s' then 1 else 0) (t : ℕ) :
    (onFactor (slotSnd₃ (X × Y) (Tc × Z) Env (ι → Database X Y)) V *
          onFactor (slotFst₃ (X × Y) (Tc × Z) Env (ι → Database X Y))
            (onFactor (splitAt (X × Y) (Database X Y) i) (compressedOracle X Y)) -
        onFactor (slotFst₃ (X × Y) (Tc × Z) Env (ι → Database X Y))
            (onFactor (splitAt (X × Y) (Database X Y) i) (compressedOracle X Y)) *
          onFactor (slotSnd₃ (X × Y) (Tc × Z) Env (ι → Database X Y)) V) *
        diagonal (fun m : (((X × Y) × (Tc × Z)) × Env) × (ι → Database X Y) ↦
          if (m.2 i).size ≤ t then (1 : ℂ) else 0) =
      (blockDiagonal fun c : Tc × ({j // j ≠ i} → Database X Y) ↦
          labelControlled (fun a : ((X × Y) × Database X Y) × (Z × Env) ↦
              f c.1 ((Equiv.funSplitAt i (Database X Y)).symm (a.1.2, c.2)))
            (fun l ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ
              (xorShift Z l ⊗ₖ (1 : Matrix Env Env ℂ))) *
            (truncatedOracle X Y (t + 1) ⊗ₖ (1 : Matrix (Z × Env) (Z × Env) ℂ)) -
          (truncatedOracle X Y (t + 1) ⊗ₖ (1 : Matrix (Z × Env) (Z × Env) ℂ)) *
            labelControlled (fun a : ((X × Y) × Database X Y) × (Z × Env) ↦
              f c.1 ((Equiv.funSplitAt i (Database X Y)).symm (a.1.2, c.2)))
            (fun l ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ
              (xorShift Z l ⊗ₖ (1 : Matrix Env Env ℂ)))).submatrix (comSplit i) (comSplit i) *
        diagonal (fun m : (((X × Y) × (Tc × Z)) × Env) × (ι → Database X Y) ↦
          if (m.2 i).size ≤ t then (1 : ℂ) else 0) := by
  rw [onFactor_slotSnd₃_eq_blockDiagonal i f hV, onFactor_slotFst₃_onFactor_splitAt i,
    diagonal_apply_eq_blockDiagonal i fun D : Database X Y ↦ if D.size ≤ t then 1 else 0]
  rw [submatrix_mul_equiv, submatrix_mul_equiv, ← Pi.sub_apply, ← Pi.sub_apply,
    ← submatrix_sub, submatrix_mul_equiv, submatrix_mul_equiv,
    ← blockDiagonal_mul, ← blockDiagonal_mul, ← blockDiagonal_sub, ← blockDiagonal_mul,
    ← blockDiagonal_mul]
  refine congrArg (fun F ↦ (blockDiagonal F).submatrix _ _) (funext fun c ↦ ?_)
  have h := commutator_mul_sizeProjector_kronecker_eq t _
    (labelControlled_mul_sizeProjector_kronecker
      (fun D ↦ f c.1 ((Equiv.funSplitAt i (Database X Y)).symm (D, c.2)))
      (fun l ↦ xorShift Z l ⊗ₖ (1 : Matrix Env Env ℂ)) t)
  rw [sizeProjector] at h
  rw [Pi.sub_apply]
  exact h

end defectBlocks

/-! ## The error of Lemma 9.2 -/

section error

variable {k : ℕ} {X Y Cm Z : Type} [DecidableEq X] {Dm : Fin k → Type}
  (ME : MultiExtractor k Cm Dm (Fin k → Database X Y)) (code : TpDCode k Dm Z)
  [AnswerMeasure (X →ₒ Y)]

/-- **The error of Lemma 9.2 with the constant `24`** (ePrint 2025/2166, pp. 58–59): `24` times
the largest instability, at query bound `t + 1`, of the online partition of one extraction with
all databases but one fixed. -/
@[expose]
noncomputable def comBoundError (t : ℕ) : ℝ≥0∞ :=
  24 * ⨆ (j' : Fin k) (tic : TpIC k Cm) (Dfix : Fin k → Database X Y),
    Database.instability (onlineLabel ME ![tic] Dfix j') (t + 1)

/-- The label of the extraction on the block of `comSplit i` at `(tic, (D_j)_{j ≠ i})`, as a
function of `D_i`, coarsens an online partition of Theorem 8.4 (ePrint 2025/2166, p. 54), so
its instability is at most the largest instability of those. -/
theorem instability_extractLabel_le (i : Fin k) (c : TpIC k Cm × ({j // j ≠ i} → Database X Y))
    (s : ℕ) :
    Database.instability (fun D ↦ code.enc
        ⟨c.1.1, ME.extract c.1 ((Equiv.funSplitAt i (Database X Y)).symm (D, c.2))⟩) s ≤
      ⨆ (j' : Fin k) (tic : TpIC k Cm) (Dfix : Fin k → Database X Y),
        Database.instability (onlineLabel ME ![tic] Dfix j') s := by
  have h : (fun D ↦ code.enc
        ⟨c.1.1, ME.extract c.1 ((Equiv.funSplitAt i (Database X Y)).symm (D, c.2))⟩) =
      (fun l ↦ code.enc ⟨c.1.1, l 0⟩) ∘
        onlineLabel ME ![c.1] ((Equiv.funSplitAt i (Database X Y)).symm (Database.empty, c.2))
          i := by
    funext D
    simp only [Function.comp_apply, onlineLabel_apply, update_funSplitAt_symm]
    rfl
  rw [h]
  exact (Database.instability_comp_le _ _ s).trans
    (le_iSup_of_le i (le_iSup_of_le c.1 (le_iSup_of_le _ le_rfl)))

/-- The largest instability in `Quantum.comBoundError` is at most one, so finite. -/
theorem iSup_instability_onlineLabel_ne_top (s : ℕ) :
    ⨆ (j' : Fin k) (tic : TpIC k Cm) (Dfix : Fin k → Database X Y),
      Database.instability (onlineLabel ME ![tic] Dfix j') s ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (iSup_le fun _ ↦ iSup_le fun _ ↦ iSup_le fun _ ↦ Database.instability_le_one _ _)

/-- `Quantum.comBoundError` is at most `24`. -/
theorem comBoundError_le_twentyFour (t : ℕ) : comBoundError ME t ≤ 24 :=
  mul_le_of_le_one_right' (iSup_le fun _ ↦ iSup_le fun _ ↦ iSup_le fun _ ↦
    Database.instability_le_one _ _)

end error

section readBlocks

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

private theorem compressedReadProjector_apply_split (i : Fin k) (x : X) (a : Option Y)
    (D D' : Fin k → Database X Y) :
    compressedReadProjector k X Y (i, x) a D D' =
      if (fun j : {j // j ≠ i} ↦ D j.1) = fun j ↦ D' j.1 then
        checkedReadProjector x a (D i) (D' i) else 0 := by
  have hc (d d' : Database X Y) : checkedReadProjector x a d d' =
      ∑ z, (if z x = a then (1 : ℂ) else 0) *
        (compressAll X Y d z * compressAll X Y z d') := by
    rw [checkedReadProjector_apply]
    symm
    simpa only [compressAll, mul_left_comm, mul_assoc] using
      sum_mul_piKron_mul_piKron (fun _ : X ↦ cellCompress Y)
        (fun _ : X ↦ cellCompress Y) x (fun z ↦ if z = a then 1 else 0) d d'
  have he : compressedReadProjector k X Y (i, x) a D D' =
      ∏ j, ∑ z, (if j = i then (if z x = a then (1 : ℂ) else 0) else 1) *
        (compressAll X Y (D j) z * compressAll X Y z (D' j)) := by
    rw [compressedReadProjector, Matrix.mul_apply]
    simp only [mul_diagonal]
    simpa only [compressDatabases, mul_left_comm, mul_assoc] using
      sum_mul_piKron_mul_piKron (fun _ : Fin k ↦ compressAll X Y)
        (fun _ : Fin k ↦ compressAll X Y) i (fun z ↦ if z x = a then 1 else 0) D D'
  rw [he, Fintype.prod_eq_mul_prod_subtype_ne _ i]
  simp only [ite_true, ← hc]
  have hr : (∏ j : {j // j ≠ i}, ∑ z,
      (if j.1 = i then (if z x = a then (1 : ℂ) else 0) else 1) *
        (compressAll X Y (D j.1) z * compressAll X Y z (D' j.1))) =
      if (fun j : {j // j ≠ i} ↦ D j.1) = fun j ↦ D' j.1 then 1 else 0 := by
    have hs (j : {j // j ≠ i}) : (∑ z,
        (if j.1 = i then (if z x = a then (1 : ℂ) else 0) else 1) *
          (compressAll X Y (D j.1) z * compressAll X Y z (D' j.1))) =
        if D j.1 = D' j.1 then 1 else 0 := by
      simp only [j.2, ite_false, one_mul, ← Matrix.mul_apply,
        compressAll_mul_self, Matrix.one_apply]
    simp_rw [hs]
    simpa only [funext_iff] using
      (Fintype.prod_boole (p := fun j : {j // j ≠ i} ↦ D j.1 = D' j.1) (M₀ := ℂ))
  rw [hr]
  split_ifs <;> simp

private theorem sum_trace_fixedReadDefect_le [UniformAnswerMeasure (X →ₒ Y)]
    {ι E : Type*} [Fintype E] [DecidableEq E] (π : Database X Y → ι)
    (U : ι → Matrix E E ℂ) (hU : ∀ l, U l ∈ unitaryGroup E ℂ) (t : ℕ) (x : X)
    (σ : Matrix (Database X Y × E) (Database X Y × E) ℂ) (hσ : σ.PosSemidef)
    (hpop : QuerySupportedOn (fun i : Database X Y × E ↦ i.1.size) (Set.Iic t) σ) :
    let K : Option Y → Matrix (Database X Y × E) (Database X Y × E) ℂ :=
      fun a i j ↦
      checkedReadProjector x a i.1 j.1 * (U (π j.1) i.2 j.2 - U (π i.1) i.2 j.2)
    ∑ a, (K a * σ * (K a)ᴴ).trace.re ≤
      24 * (Database.instability π (t + 1)).toReal * σ.trace.re := by
  let K : Option Y → Matrix (Database X Y × E) (Database X Y × E) ℂ :=
    fun a i j ↦
    checkedReadProjector x a i.1 j.1 * (U (π j.1) i.2 j.2 - U (π i.1) i.2 j.2)
  let f : Database X Y × E → (X × Database X Y) × E := fun p ↦ ((x, p.1), p.2)
  let J := basisMatrix f
  have hJ : Jᴴ * J = 1 := conjTranspose_basisMatrix_mul_self (by
    intro a b h
    exact Prod.ext (congrArg (fun p : (X × Database X Y) × E ↦ p.1.2) h)
      (congrArg (fun p : (X × Database X Y) × E ↦ p.2) h))
  have hK (a : Option Y) : checkedReadDefect π U a * J = J * K a := by
    ext ⟨⟨y, d⟩, e⟩ ⟨d', e'⟩
    rw [mul_basisMatrix_apply]
    simp only [f, checkedReadDefect_apply, selectedCheckedReadProjector_apply]
    change _ = ∑ p, J ((y, d), e) p * K a p (d', e')
    by_cases hy : y = x
    · subst y
      simp [J, basisMatrix_apply, f, K, Fintype.sum_prod_type, ite_and]
    · simp [J, basisMatrix_apply, f, hy, K]
  have hp : QuerySupportedOn (fun i : (X × Database X Y) × E ↦ i.1.2.size)
      (Set.Iic t) (MatrixMap.conj J σ) := by
    refine hpop.conj ?_
    intro i j hij hj
    have he : i = f j := by
      simpa only [J, basisMatrix_apply, ne_eq, ite_eq_right_iff, one_ne_zero,
        imp_false, not_not] using hij
    simpa [he, f] using hj
  have h := sum_trace_checkedReadDefect_le π U hU t (MatrixMap.conj J σ)
    (hσ.mul_mul_conjTranspose_same J) hp
  have ht (ρ : Matrix (Database X Y × E) (Database X Y × E) ℂ) :
      (MatrixMap.conj J ρ).trace = ρ.trace := MatrixMap.isTP_conj hJ ρ
  have he (a : Option Y) : MatrixMap.conj (checkedReadDefect π U a) (MatrixMap.conj J σ) =
      MatrixMap.conj J (MatrixMap.conj (K a) σ) := by
    rw [← LinearMap.comp_apply, ← MatrixMap.conj_mul, hK, MatrixMap.conj_mul,
      LinearMap.comp_apply]
  change ∑ a, (MatrixMap.conj (K a) σ).trace.re ≤ _
  change ∑ a, (MatrixMap.conj (checkedReadDefect π U a) (MatrixMap.conj J σ)).trace.re
    ≤ _ at h
  simpa only [he, ht] using h

private theorem trace_conj_blockDiagonal {B C : Type*} [Fintype B] [Fintype C]
    [DecidableEq C] (K : C → Matrix B B ℂ) (σ : Matrix (B × C) (B × C) ℂ) :
    (MatrixMap.conj (blockDiagonal K) σ).trace =
      ∑ c, (MatrixMap.conj (K c) (σ.submatrix (fun b ↦ (b, c)) (fun b ↦ (b, c)))).trace := by
  simp only [MatrixMap.trace_conj_apply, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    blockDiagonal_apply, ite_mul, zero_mul, Matrix.submatrix_apply]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact Finset.sum_comm

private theorem trace_conj_submatrix_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (K : Matrix B B ℂ) (σ : Matrix A A ℂ) :
    (MatrixMap.conj (K.submatrix e e) σ).trace =
      (MatrixMap.conj K (σ.submatrix e.symm e.symm)).trace := by
  let τ := σ.submatrix e.symm e.symm
  have hτ : τ.submatrix e e = σ := by ext i j; simp [τ]
  change (MatrixMap.conj (K.submatrix e e) σ).trace = (MatrixMap.conj K τ).trace
  conv_lhs => rw [← hτ]
  rw [MatrixMap.conj_apply, conjTranspose_submatrix,
    submatrix_mul_equiv, submatrix_mul_equiv, MatrixMap.conj_apply]
  exact e.sum_comp (fun b ↦ (K * τ * Kᴴ) b b)

private def readSplit {ι Tc Z E DB : Type*} [DecidableEq ι] (i : ι) :
    ((Tc × Z) × E) × (ι → DB) ≃ (DB × (Z × E)) × (Tc × ({j // j ≠ i} → DB)) where
  toFun p := ((p.2 i, (p.1.1.2, p.1.2)), (p.1.1.1, fun j ↦ p.2 j.1))
  invFun p := (((p.2.1, p.1.2.1), p.1.2.2),
    (Equiv.funSplitAt i DB).symm (p.1.1, p.2.2))
  left_inv p := Prod.ext rfl ((Equiv.funSplitAt i DB).symm_apply_apply p.2)
  right_inv p := by
    have h := (Equiv.funSplitAt i DB).apply_symm_apply (p.1.1, p.2.2)
    rw [Equiv.funSplitAt_apply, Prod.mk.injEq] at h
    exact Prod.ext (Prod.ext h.1 rfl) (Prod.ext rfl h.2)

private theorem readSplit_read {Tc Z E : Type*} [DecidableEq Tc] [DecidableEq Z] [DecidableEq E]
    (i : Fin k) (x : X) (a : Option Y) :
    (1 : Matrix ((Tc × Z) × E) ((Tc × Z) × E) ℂ) ⊗ₖ
        compressedReadProjector k X Y (i, x) a =
      (blockDiagonal fun _ : Tc × ({j // j ≠ i} → Database X Y) ↦
        checkedReadProjector x a ⊗ₖ (1 : Matrix (Z × E) (Z × E) ℂ)).submatrix
          (readSplit i) (readSplit i) := by
  ext ⟨⟨⟨tc, z⟩, e⟩, D⟩ ⟨⟨⟨tc', z'⟩, e'⟩, D'⟩
  simp only [kroneckerMap_apply, Matrix.one_apply, compressedReadProjector_apply_split,
    Matrix.submatrix_apply, readSplit, Equiv.coe_fn_mk, blockDiagonal_apply, Prod.mk.injEq]
  by_cases htc : tc = tc' <;> by_cases hz : z = z' <;> by_cases he : e = e' <;>
    by_cases hd : (fun j : {j // j ≠ i} ↦ D j.1) = fun j ↦ D' j.1 <;> simp [htc, hz, he, hd]

omit [DecidableEq X] [Fintype Y] [AddCommGroup Y] in
private theorem readSplit_extract {Tc Z E : Type*}
    [DecidableEq Tc] [DecidableEq Z] [DecidableEq E] [AddGroup Z]
    (i : Fin k) (f : Tc → (Fin k → Database X Y) → Z)
    {V : Matrix ((Tc × Z) × (Fin k → Database X Y))
      ((Tc × Z) × (Fin k → Database X Y)) ℂ}
    (hV : ∀ tc tc' z z' d d', V ((tc, z), d) ((tc', z'), d') =
      if tc = tc' ∧ z = z' + f tc' d' ∧ d = d' then 1 else 0) :
    onFactor (slotFst (Tc × Z) E (Fin k → Database X Y)) V =
      (blockDiagonal fun c : Tc × ({j // j ≠ i} → Database X Y) ↦
        labelControlled (fun p : Database X Y × (Z × E) ↦
          f c.1 ((Equiv.funSplitAt i (Database X Y)).symm (p.1, c.2)))
          (fun l ↦ (1 : Matrix (Database X Y) (Database X Y) ℂ) ⊗ₖ
            (xorShift Z l ⊗ₖ (1 : Matrix E E ℂ)))).submatrix (readSplit i) (readSplit i) := by
  ext ⟨⟨⟨tc, z⟩, e⟩, D⟩ ⟨⟨⟨tc', z'⟩, e'⟩, D'⟩
  simp only [onFactor_apply, slotFst, Equiv.coe_fn_mk, hV, Matrix.submatrix_apply,
    readSplit, blockDiagonal_apply, labelControlled_apply, kroneckerMap_apply,
    Matrix.one_apply, xorShift_apply, Prod.mk.injEq]
  have hd : (Equiv.funSplitAt i (Database X Y)).symm
      (D i, fun j : {j // j ≠ i} ↦ D j.1) = D :=
    (Equiv.funSplitAt i (Database X Y)).symm_apply_apply D
  rw [hd]
  by_cases hdd : D = D'
  · subst D'
    by_cases htc : tc = tc' <;> by_cases he : e = e' <;> simp [htc, he]
  · have h := mt (eq_iff_apply_eq_and_restrict_eq i).mpr hdd
    by_cases hr : (fun j : {j // j ≠ i} ↦ D j.1) = fun j ↦ D' j.1 <;>
      by_cases hi : D i = D' i
    · exact absurd ⟨hi, hr⟩ h
    all_goals simp [hdd, hr, hi]

omit [AddCommGroup Y] in
private theorem controlled_read_defect_apply {ι E : Type*} [Fintype E] [DecidableEq E]
    (π : Database X Y → ι) (U : ι → Matrix E E ℂ) (x : X) (a : Option Y)
    (d d' : Database X Y) (e e' : E) :
    let T := labelControlled (fun p : Database X Y × E ↦ π p.1)
      (fun l ↦ (1 : Matrix (Database X Y) (Database X Y) ℂ) ⊗ₖ U l)
    ((checkedReadProjector x a ⊗ₖ (1 : Matrix E E ℂ)) * T -
      T * (checkedReadProjector x a ⊗ₖ (1 : Matrix E E ℂ))) (d, e) (d', e') =
      checkedReadProjector x a d d' * (U (π d') e e' - U (π d) e e') := by
  dsimp only
  simp [Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_prod_type, labelControlled_apply,
    kroneckerMap_apply, Matrix.one_apply, mul_comm, sub_mul]

end readBlocks

/-! ## Lemma 9.2 -/

section lemma92

open EmulatedOracle (cohSpec)

variable {k : ℕ} {X Y Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  {Dm : Fin k → Type} (ME : MultiExtractor k Cm Dm (Fin k → Database X Y))
  (code : TpDCode k Dm Z)

private theorem sum_trace_readComDefect_le [UniformAnswerMeasure (X →ₒ Y)]
    (t : ℕ) (i : Fin k) (x : X) (Env : QReg)
    (σ : Matrix (ReadComOut k Cm Z Env × (compressedVCOracle k X Y).S)
      (ReadComOut k Cm Z Env × (compressedVCOracle k X Y).S) ℂ) (hσ : σ.PosSemidef)
    (hpop : QuerySupportedOn (fun p ↦ (p.2 i).size) (Set.Iic t) σ) :
    ∑ a, (readComDefect (compressedVCOracle k X Y) ME code Env (i, x) a * σ *
      (readComDefect (compressedVCOracle k X Y) ME code Env (i, x) a)ᴴ).trace.re ≤
      (comBoundError ME t).toReal * σ.trace.re := by
  let S := ⨆ (j' : Fin k) (tic : TpIC k Cm) (Dfix : Fin k → Database X Y),
    Database.instability (onlineLabel ME ![tic] Dfix j') (t + 1)
  have hS : S ≠ ⊤ := iSup_instability_onlineLabel_ne_top ME (t + 1)
  let e := readSplit (Tc := TpIC k Cm) (Z := Z) (E := Env) (DB := Database X Y) i
  let f : TpIC k Cm → (Fin k → Database X Y) → Z :=
    fun tc d ↦ code.enc ⟨tc.1, ME.extract tc d⟩
  let lab := fun c : TpIC k Cm × ({j // j ≠ i} → Database X Y) ↦
    fun d ↦ f c.1 ((Equiv.funSplitAt i (Database X Y)).symm (d, c.2))
  let U := fun z ↦ xorShift Z z ⊗ₖ (1 : Matrix Env Env ℂ)
  let T := fun c ↦ labelControlled (fun p : Database X Y × (Z × Env) ↦ lab c p.1)
    (fun z ↦ (1 : Matrix (Database X Y) (Database X Y) ℂ) ⊗ₖ U z)
  let K := fun c a ↦
    (checkedReadProjector x a ⊗ₖ (1 : Matrix (Z × Env) (Z × Env) ℂ)) * T c -
    T c * (checkedReadProjector x a ⊗ₖ (1 : Matrix (Z × Env) (Z × Env) ℂ))
  have hC (a : Option Y) : readComDefect (compressedVCOracle k X Y) ME code Env (i, x) a =
      (blockDiagonal fun c ↦ K c a).submatrix e e := by
    unfold readComDefect
    change ((1 : Matrix ((TpIC k Cm × Z) × Env) ((TpIC k Cm × Z) × Env) ℂ) ⊗ₖ
        compressedReadProjector k X Y (i, x) a) *
        onFactor (slotFst (TpIC k Cm × Z) Env (Fin k → Database X Y)) (extractUnitary ME code) -
      onFactor (slotFst (TpIC k Cm × Z) Env (Fin k → Database X Y)) (extractUnitary ME code) *
        ((1 : Matrix ((TpIC k Cm × Z) × Env) ((TpIC k Cm × Z) × Env) ℂ) ⊗ₖ
          compressedReadProjector k X Y (i, x) a) = _
    rw [readSplit_read, readSplit_extract i f (extractUnitary_apply ME code),
      submatrix_mul_equiv, submatrix_mul_equiv,
      ← blockDiagonal_mul, ← blockDiagonal_mul]
    ext p q
    simp only [Matrix.sub_apply, Matrix.submatrix_apply, blockDiagonal_apply]
    split_ifs <;> simp_all only [e, K, T, lab, U, Matrix.sub_apply, sub_self]
  let τ := σ.submatrix e.symm e.symm
  let σb := fun c ↦ τ.submatrix (fun b ↦ (b, c)) (fun b ↦ (b, c))
  have hb (c) : ∑ a, (MatrixMap.conj (K c a) (σb c)).trace.re ≤
      24 * S.toReal * (σb c).trace.re := by
    have hpsd : (σb c).PosSemidef := (hσ.submatrix _).submatrix _
    have hp : QuerySupportedOn (fun p : Database X Y × (Z × Env) ↦ p.1.size)
        (Set.Iic t) (σb c) := by
      intro b b' h
      obtain ⟨hl, hr⟩ := hpop (e.symm (b, c)) (e.symm (b', c)) h
      simpa [e, readSplit] using And.intro hl hr
    have he (a : Option Y) : K c a = fun p q : Database X Y × (Z × Env) ↦
        checkedReadProjector x a p.1 q.1 * (U (lab c q.1) p.2 q.2 - U (lab c p.1) p.2 q.2) := by
      ext p q
      exact controlled_read_defect_apply (lab c) U x a p.1 q.1 p.2 q.2
    have h := sum_trace_fixedReadDefect_le (lab c) U
      (fun z ↦ kronecker_mem_unitary (xorShift_mem_unitaryGroup z) (one_mem _))
      t x (σb c) hpsd hp
    have hi := ENNReal.toReal_mono hS (instability_extractLabel_le ME code i c (t + 1))
    simp only [he]
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi (by norm_num))
      hpsd.trace_re_nonneg)
  have ht : ∑ c, (σb c).trace.re = σ.trace.re := by
    rw [← Complex.re_sum, ← MatrixMap.trace_eq_sum_trace_submatrix]
    exact congrArg Complex.re (e.symm.sum_comp (fun p ↦ σ p p))
  change ∑ a, (MatrixMap.conj (readComDefect (compressedVCOracle k X Y) ME code Env (i, x) a)
    σ).trace.re ≤ _
  have htrace (a : Option Y) :
      (MatrixMap.conj (readComDefect (compressedVCOracle k X Y) ME code Env (i, x) a) σ).trace =
        ∑ c, (MatrixMap.conj (K c a) (σb c)).trace := by
    rw [hC]
    exact (trace_conj_submatrix_equiv e _ σ).trans (trace_conj_blockDiagonal _ _)
  simp only [htrace, Complex.re_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ c, 24 * S.toReal * (σb c).trace.re := Finset.sum_le_sum fun c _ ↦ hb c
    _ = 24 * S.toReal * σ.trace.re := by rw [← Finset.mul_sum, ht]
    _ = _ := by simp [comBoundError, ENNReal.toReal_mul, S]

/-- Both P2 commutation bounds hold with `24` times the online-label instability at `t + 1`
after every mixed prefix of at most `t` calls. The read clause sums optional answers and
permits the retained classical outcome to select the final address. -/
theorem comBound_compressedVCOracle [UniformAnswerMeasure (X →ₒ Y)] :
    ComBound.{v, w} (compressedVCOracle k X Y) ME code (comBoundError ME) := by
  constructor
  · intro i t A Env α x ρ hx
    set S := ⨆ (j' : Fin k) (tic : TpIC k Cm) (Dfix : Fin k → Database X Y),
      Database.instability (onlineLabel ME ![tic] Dfix j') (t + 1) with hSdef
    have hS : S ≠ ⊤ := iSup_instability_onlineLabel_ne_top ME (t + 1)
    -- the blocks
    let f : TpIC k Cm → (Fin k → Database X Y) → Z :=
      fun tc s ↦ code.enc ⟨tc.1, ME.extract tc s⟩
    let lab : TpIC k Cm × ({j // j ≠ i} → Database X Y) → Database X Y → Z :=
      fun c D ↦ f c.1 ((Equiv.funSplitAt i (Database X Y)).symm (D, c.2))
    let Lb : TpIC k Cm × ({j // j ≠ i} → Database X Y) →
        Matrix (((X × Y) × Database X Y) × (Z × Env))
          (((X × Y) × Database X Y) × (Z × Env)) ℂ :=
      fun c ↦ labelControlled (fun a ↦ lab c a.1.2) fun l ↦
        (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ
          (xorShift Z l ⊗ₖ (1 : Matrix Env Env ℂ))
    let T := truncatedOracle X Y (t + 1) ⊗ₖ (1 : Matrix (Z × Env) (Z × Env) ℂ)
    let e := comSplit (XY := X × Y) (Tc := TpIC k Cm) (Z := Z) (Env := Env) (DB := Database X Y) i
    let Psz : Matrix (ComOut k X Y Cm Z Env × (compressedVCOracle k X Y).S)
        (ComOut k X Y Cm Z Env × (compressedVCOracle k X Y).S) ℂ :=
      diagonal fun m ↦ if (m.2 i).size ≤ t then 1 else 0
    -- on the range of `Psz`, the defect is block diagonal
    have hC : comDefect (compressedVCOracle k X Y) ME code Env i * Psz =
        ((blockDiagonal fun c ↦ Lb c * T - T * Lb c).submatrix e e :
          Matrix (ComOut k X Y Cm Z Env × (compressedVCOracle k X Y).S)
            (ComOut k X Y Cm Z Env × (compressedVCOracle k X Y).S) ℂ) * Psz :=
      commutator_onFactor_mul_diagonal_eq i f (extractUnitary_apply ME code) t
    -- each block, by Corollary 5.6 with the constant `24`
    have hb : ∀ c, ‖Lb c * T - T * Lb c‖ ^ 2 ≤ 24 * S.toReal := fun c ↦ by
      have h := l2_opNorm_commutator_purifiedMeasurement_sq_le_twentyFour_mul (lab c) (t + 1)
        (U := fun l ↦ xorShift Z l ⊗ₖ (1 : Matrix Env Env ℂ))
        fun l ↦ kronecker_mem_unitary (xorShift_mem_unitaryGroup l) (one_mem _)
      have h' := ENNReal.toReal_mono hS (instability_extractLabel_le ME code i c (t + 1))
      exact h.trans (by gcongr)
    -- one outcome
    let σf : α → Matrix (ComOut k X Y Cm Z Env × (compressedVCOracle k X Y).S)
        (ComOut k X Y Cm Z Env × (compressedVCOracle k X Y).S) ℂ := fun a ↦
      (((compressedVCOracle k X Y).mixedExtractRuntime ME code).jointPost₂
        .instruments x ρ a).matrix
    have hleaf : ∀ a, ENNReal.ofReal (comDefect (compressedVCOracle k X Y) ME code Env i *
        σf a * (comDefect (compressedVCOracle k X Y) ME code Env i)ᴴ).trace.re
        ≤ ENNReal.ofReal (24 * S.toReal) * ENNReal.ofReal (σf a).trace.re := fun a ↦ by
      have hsupp : QuerySupportedOn
          (fun m : ComOut k X Y Cm Z Env × (compressedVCOracle k X Y).S ↦ (m.2 i).size)
          (Set.Iic t) (σf a) :=
        querySupportedOn_jointPost₂_compressedVCOracle_mixed ME code i x hx ρ a
      have hσ : MatrixMap.conj Psz (σf a) = σf a :=
        QuerySupportedOn.conj_diagonal_eq_self (fun m hm ↦ by simp [Set.mem_Iic.mp hm]) hsupp
      have hpsd : (σf a).PosSemidef := SubState.posSemidef _
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal
        (re_trace_mul_mul_conjTranspose_le_of_blockDiagonal
          (N := ComOut k X Y Cm Z Env × (compressedVCOracle k X Y).S) e _ (by positivity) hb hC hσ
          hpsd)
    calc comError (compressedVCOracle k X Y) ME code i x ρ
        ≤ ∑' a, ENNReal.ofReal (24 * S.toReal) * ENNReal.ofReal (σf a).trace.re :=
          ENNReal.tsum_le_tsum hleaf
      _ = ENNReal.ofReal (24 * S.toReal) * ∑' a, ENNReal.ofReal (σf a).trace.re :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (24 * S.toReal) * 1 := by
          gcongr
          exact QuantumRuntime.tsum_jointPost₂_trace_le_one _ _ x ρ
      _ = comBoundError ME t := by
        rw [mul_one, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hS, comBoundError,
          ← hSdef]
        norm_num
  · intro t A Env α x ρ c hx
    let σf : α → Matrix (ReadComOut k Cm Z Env × (compressedVCOracle k X Y).S)
        (ReadComOut k Cm Z Env × (compressedVCOracle k X Y).S) ℂ := fun l ↦
      (((compressedVCOracle k X Y).mixedExtractRuntime ME code).jointPost₂
        .instruments x ρ l).matrix
    have hfinite : comBoundError ME t ≠ ⊤ :=
      ne_top_of_le_ne_top (by norm_num) (comBoundError_le_twentyFour ME t)
    have hleaf (l : α) :
        (∑ a, ENNReal.ofReal (readComDefect (compressedVCOracle k X Y) ME code Env (c l) a *
          (σf l) * (readComDefect (compressedVCOracle k X Y) ME code Env (c l) a)ᴴ).trace.re)
        ≤ comBoundError ME t * ENNReal.ofReal (σf l).trace.re := by
      have hpsd : (σf l).PosSemidef := SubState.posSemidef _
      have h := sum_trace_readComDefect_le ME code t (c l).1 (c l).2 Env (σf l) hpsd
        (querySupportedOn_jointPost₂_compressedVCOracle_mixed ME code (c l).1 x hx ρ l)
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦
        (hpsd.mul_mul_conjTranspose_same
          (readComDefect (compressedVCOracle k X Y) ME code Env (c l) a)).trace_re_nonneg)]
      calc
        _ ≤ ENNReal.ofReal ((comBoundError ME t).toReal * (σf l).trace.re) :=
          ENNReal.ofReal_le_ofReal h
        _ = _ := by rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hfinite]
    calc
      readComError (compressedVCOracle k X Y) ME code x ρ c
          ≤ ∑' l, comBoundError ME t * ENNReal.ofReal (σf l).trace.re :=
        ENNReal.tsum_le_tsum hleaf
      _ = comBoundError ME t * ∑' l, ENNReal.ofReal (σf l).trace.re :=
        ENNReal.tsum_mul_left
      _ ≤ comBoundError ME t * 1 := by
        gcongr
        exact QuantumRuntime.tsum_jointPost₂_trace_le_one _ _ x ρ
      _ = comBoundError ME t := mul_one _

/-- **Lemma 9.2 of ePrint 2025/2166 with the paper's constant `80`** (pp. 58–59): a corollary of
`Quantum.comBound_compressedVCOracle`. -/
theorem comBound_compressedVCOracle_eighty [UniformAnswerMeasure (X →ₒ Y)] :
    ComBound.{v, w} (compressedVCOracle k X Y) ME code fun t ↦
      80 * ⨆ (j' : Fin k) (tic : TpIC k Cm) (Dfix : Fin k → Database X Y),
        Database.instability (onlineLabel ME ![tic] Dfix j') (t + 1) :=
  (comBound_compressedVCOracle ME code).mono fun t ↦ by
    simp only [comBoundError]
    gcongr
    norm_num

end lemma92

end Quantum
