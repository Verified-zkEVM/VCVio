/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.CheckerComparison
public import VCVio.Quantum.Comp.Potential
public import VCVio.Quantum.VC.Proof.Offline
public import VCVio.CryptoFoundations.MerkleTree.Salted.Instability

/-!
# Concatenated extraction responses and the old-oracle error

`oldOfflineError` is the real-valued function `F` of the repair note FIX (35), with
`oldMerkleOfflineError` converting opened positions to `qs * (d + 1)` raw checks.
The leakage polynomial and invalid-sector term are those of FIX (26b).
Natural subtractions are truncated before casting, and division by six is real division.
Physical parameters have `N > 0` and nonnegative ordinary and extraction masses.

`databasePopulation_post_old` bounds total populated cells in every original post-adversary
branch of the old coherent ordinary/extraction runtime. It applies to any extractor and code,
and general local operations with register-changing leaves. Its proof lifts the one-cell growth
property structurally through the program; it does not require positivity of intermediate matrices.

`TpDCode.concat` encodes each decommitment in a separate additive coordinate, with a separate
length coordinate. Its coherent extraction matrix factors into commuting translations for any
partition of the response positions. For full Merkle tuples each part depends only on its
selected databases; duplicate-index tuples have database-independent parts. The generic
`checker_batches_factor` records the algebraic rearrangement of FIX (26b).

`filledCell_extraction_commutator_le` proves the local estimate in FIX (27), uniformly over
ancilla unitaries and every function of an extraction result, including component batches.
`invalidStack` represents the sum of invalid weights as a rectangular trace potential,
and `actual_sub_filled_potential_le` bounds the checker error by that potential on arbitrary
entangled mixed states. `rpow_inv_two_tsum_conj_unitary_le` supplies the direct-sum
triangle inequality without requiring the observables to sum to a projector.
The local commutator estimate uses the exact distance from the uniform projector to its
normalized restriction to unchanged labels. `databaseControl_sum_commutator_gram_le` lifts
the estimate over all cell contexts and sums occupancy to bound the squared commutator
by `4 * s * a` on the population-`s` subspace. Its hypothesis counts changing labels in
occupied-cell contexts; its invalid operators are identified with compressed empty-cell
projectors by `databaseInvalidCell_eq_compress`.

The leakage polynomial is the exact prefix sum in FIX (28). Its Cauchy--Schwarz estimate is
stated in `ℝ≥0∞`, including infinite masses. `old_run_invalid_le` bounds the original
post-adversary invalid norm by `2 √(e T(t) / N)`, where `e` is actual extraction mass.
This module does not assert `OfflineExtractable`: transfer to the actual challenger remains
necessary.
No assertion that arbitrary classical checks preserve population is used. The coefficients
four and eight in FIX (36) belong to the downstream reduction, not to this P4 error function.
-/

public section

open scoped ENNReal Kronecker Matrix.Norms.L2Operator ComplexOrder

open Matrix

universe u v w

namespace Quantum


namespace MatrixMap

/-- A unitary changes a family of observable seminorms by at most its commutator seminorm.
The family need not sum to a projector, and the positive input need not have trace one.
This is the direct-sum triangle step in FIX (27)–(28). -/
theorem rpow_inv_two_tsum_conj_unitary_le
    {C S : Type*} [Fintype S] [DecidableEq S] (R : C → Matrix S S ℂ)
    (U : Matrix S S ℂ) (hU : Uᴴ * U = 1) {ρ : Matrix S S ℂ} (hρ : ρ.PosSemidef) :
    (∑' c, ENNReal.ofReal (conj (R c) (conj U ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
      (∑' c, ENNReal.ofReal (conj (R c) ρ).trace.re) ^ (2⁻¹ : ℝ) +
      (∑' c, ENNReal.ofReal (conj (R c * U - U * R c) ρ).trace.re) ^ (2⁻¹ : ℝ) := by
  apply rpow_inv_two_tsum_le_of_le_add
  intro c
  have he : U * R c + (R c * U - U * R c) = R c * U := by abel
  have ht : (conj (U * R c) ρ).trace = (conj (R c) ρ).trace := by
    rw [trace_conj_apply, trace_conj_apply, conjTranspose_mul]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
  have hh := ofReal_trace_conj_add_rpow_le hρ (U * R c) (R c * U - U * R c)
  rw [he, ht, conj_mul, LinearMap.comp_apply] at hh
  exact hh

end MatrixMap

section counting
variable {C Y κ : Type*} [Fintype C] [DecidableEq C] [Fintype Y]

omit [Fintype C] [Fintype Y] in
/-- Restoring one split cell is the corresponding database update. -/
theorem splitAt_restore_update (D : Database C Y) (c : C) (y : Option Y) :
    (Equiv.funSplitAt c (Option Y)).symm (y, fun i ↦ D i.1) = Function.update D c y := by
  ext i
  by_cases h : i = c <;> simp [Equiv.funSplitAt_symm_apply, h]

omit [Fintype C] in
/-- The changing-label fraction can be counted by updates of any representative database. -/
theorem changingFraction_eq_update [DecidableEq κ] (β : Database C Y → κ)
    (D : Database C Y) (c : C) :
    changingFraction β c (fun i ↦ D i.1) =
      ((Finset.univ.filter fun y : Y ↦ β (Function.update D c (some y)) ≠
        β (Function.update D c none)).card : ℝ) / Fintype.card Y := by
  simp only [changingFraction, splitAt_restore_update]

omit [Fintype Y] in
/-- Erasing an occupied cell decreases population by exactly one. -/
theorem database_size_erase (D : Database C Y) (c : C) (hc : (D c).isSome) :
    Database.size (Function.update D c none) + 1 = D.size := by
  have he : (Finset.univ.filter fun i ↦ (Function.update D c none i).isSome) =
      (Finset.univ.filter fun i ↦ (D i).isSome).erase c := by
    ext i
    by_cases h : i = c <;> simp [Function.update_apply, h]
  simp only [Database.size, he]
  exact Finset.card_erase_add_one (by simpa using hc)

end counting
section family
variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]

omit [DecidableEq X] [Fintype Y] in
/-- Flattened population is the sum of the populations of the individual databases. -/
theorem database_size_curry (D : Database (Fin k × X) Y) :
    D.size = ∑ j : Fin k, Database.size (Function.curry D j) := by
  simp only [Database.size, Finset.card_filter]
  rw [Fintype.sum_prod_type]
  rfl

omit [Fintype X] [Fintype Y] in
/-- A flattened cell update changes just its indexed database and address. -/
theorem curry_update_cell (D : Database (Fin k × X) Y) (j : Fin k) (x : X) (y : Option Y) :
    Function.curry (Function.update D (j,x) y) =
      Function.update (Function.curry D) j (Function.update (Function.curry D j) x y) := by
  ext i z
  by_cases hi : i = j <;> by_cases hz : z = x <;>
    simp [Function.curry, hi, hz]

end family

section traceLeakage
variable {C Y Z κ : Type*} [Fintype C] [DecidableEq C] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z] [Nonempty Y] [DecidableEq κ]

/-- The summed squared invalid commutator on a positive population-supported state is
bounded by `4 * s * a` times its trace. All masses remain in `ℝ≥0∞`. -/
theorem databaseControl_leakage_trace_le
    (β : Database C Y → κ) (U : κ → Matrix Z Z ℂ)
    (hU : ∀ a, U a ∈ unitaryGroup Z ℂ) (s : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hβ : ∀ D : Database C Y, D.size ≤ s → ∀ c, (D c).isSome →
      changingFraction β c (fun i ↦ D i.1) ≤ a)
    {ρ : Matrix (Database C Y × Z) (Database C Y × Z) ℂ} (hρ : ρ.PosSemidef)
    (hpop : populationCut s * ρ = ρ) :
    let V := databaseControl β U
    let E := fun c ↦ V * databaseInvalidCell c - databaseInvalidCell c * V
    (∑' c, ENNReal.ofReal (MatrixMap.conj (E c) ρ).trace.re) ≤
      ENNReal.ofReal (4 * s * a) * ENNReal.ofReal ρ.trace.re := by
  dsimp only
  let K := populationCut (C := C) (Y := Y) (Z := Z) s
  let V := databaseControl β U
  let E := fun c ↦ V * databaseInvalidCell c - databaseInvalidCell c * V
  let B := ∑ c, (E c)ᴴ * E c
  change K * ρ = ρ at hpop
  have hK : Kᴴ = K := by simp [K, populationCut, diagonal_conjTranspose]
  have hright : ρ * K = ρ := by
    have hh := congrArg conjTranspose hpop
    simpa only [conjTranspose_mul, hρ.isHermitian.eq, hK] using hh
  have htrace : ((K * B * K) * ρ).trace = (B * ρ).trace := by
    rw [Matrix.mul_assoc, hpop, Matrix.mul_assoc, Matrix.trace_mul_comm K,
      Matrix.mul_assoc, hright]
  have hh := (databaseControl_sum_commutator_gram_le β U hU s ha hβ).trace_mul_re_nonneg hρ
  change 0 ≤ (((4 * s * a) • K - K * B * K) * ρ).trace.re at hh
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, Matrix.smul_mul,
    hpop, Matrix.trace_smul, htrace, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hh
  have hn (c : C) : 0 ≤ (MatrixMap.conj (E c) ρ).trace.re :=
    (hρ.mul_mul_conjTranspose_same (E c)).trace_re_nonneg
  change (∑' c, ENNReal.ofReal (MatrixMap.conj (E c) ρ).trace.re) ≤ _
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun c _ ↦ hn c)]
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have he : (∑ c, (MatrixMap.conj (E c) ρ).trace.re) = (B * ρ).trace.re := by
    simp only [B, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum, MatrixMap.trace_conj_apply]
  rw [he]
  linarith

end traceLeakage

section increment
variable {C Y Z κ : Type*} [Fintype C] [DecidableEq C] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

/-- Database-controlled ancilla unitaries form a unitary on the joint register. -/
theorem databaseControl_unitary (β : Database C Y → κ) (U : κ → Matrix Z Z ℂ)
    (hU : ∀ a, U a ∈ unitaryGroup Z ℂ) : databaseControl β U ∈ unitaryGroup _ ℂ := by
  apply labelControlled_mem_unitaryGroup
  · intro k a b h
    have hab : a.1 = b.1 := by
      by_contra hne
      simp [kroneckerMap_apply, one_apply_ne hne] at h
    rw [hab]
  · intro k
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_one,
      ← mul_kronecker_mul, Matrix.one_mul, ← star_eq_conjTranspose,
      mem_unitaryGroup_iff.mp (hU k), one_kronecker_one]

/-- A controlled extraction increases the direct-sum invalid seminorm by at most
`2 * sqrt (s * a)` on an arbitrary subnormalized state of population at most `s`.
The bound uses the original state’s population and retains the initial invalid norm. -/
theorem databaseControl_invalid_increment [Nonempty Y] [DecidableEq κ]
    (β : Database C Y → κ) (U : κ → Matrix Z Z ℂ)
    (hU : ∀ a, U a ∈ unitaryGroup Z ℂ) (s : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hβ : ∀ D : Database C Y, D.size ≤ s → ∀ c, (D c).isSome →
      changingFraction β c (fun i ↦ D i.1) ≤ a)
    {ρ : Matrix (Database C Y × Z) (Database C Y × Z) ℂ} (hρ : ρ.PosSemidef)
    (ht : ρ.trace.re ≤ 1) (hpop : populationCut s * ρ = ρ) :
    let V := databaseControl β U
    let R := fun c : C ↦ databaseInvalidCell (Y := Y) (Z := Z) c
    (∑' c, ENNReal.ofReal (MatrixMap.conj (R c) (MatrixMap.conj V ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
      (∑' c, ENNReal.ofReal (MatrixMap.conj (R c) ρ).trace.re) ^ (2⁻¹ : ℝ) +
        ENNReal.ofReal (2 * Real.sqrt (s * a)) := by
  dsimp only
  let V := databaseControl β U
  let R := fun c : C ↦ databaseInvalidCell (Y := Y) (Z := Z) c
  have hV : Vᴴ * V = 1 := mem_unitaryGroup_iff'.mp (databaseControl_unitary β U hU)
  have htriangle := MatrixMap.rpow_inv_two_tsum_conj_unitary_le R V hV hρ
  refine htriangle.trans (add_le_add le_rfl ?_)
  have he (c : C) : MatrixMap.conj (R c * V - V * R c) ρ =
      MatrixMap.conj (V * R c - R c * V) ρ := by
    have hneg : R c * V - V * R c = -(V * R c - R c * V) := by abel
    rw [hneg]
    simp only [MatrixMap.conj_apply, conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg,
      neg_neg]
  simp only [he]
  have hh := databaseControl_leakage_trace_le β U hU s ha hβ hρ hpop
  have hb : (∑' c, ENNReal.ofReal (MatrixMap.conj (V * R c - R c * V) ρ).trace.re) ≤
      ENNReal.ofReal (4 * s * a) := hh.trans (by
    exact mul_le_of_le_one_right (by positivity)
      (show ENNReal.ofReal ρ.trace.re ≤ 1 from ENNReal.ofReal_le_one.mpr ht))
  refine (ENNReal.rpow_le_rpow hb (by norm_num)).trans_eq ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    show (2⁻¹ : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  congr 1
  rw [show (4 : ℝ) * s * a = 4 * (s * a) by ring, Real.sqrt_mul (by norm_num)]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

end increment

namespace CompressedReplay

/-- The actual checker error is bounded by the rectangular invalid-sector potential on every
positive semidefinite joint input. Workspace entanglement and subnormalization are unrestricted.
This is the mixed-state, ancilla-preserving form of FIX (29). -/
theorem actual_sub_filled_potential_le
    {k : ℕ} {X Y A : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] [Fintype A]
    (io : List ((Fin k × X) × Y))
    {ρ : Matrix (A × (Fin k → Database X Y)) (A × (Fin k → Database X Y)) ℂ}
    (hρ : ρ.PosSemidef) :
    QuantumRuntime.potential (actualCheck io - filledCheck io) ρ ≤
      QuantumRuntime.potential (invalidStack (k := k) (X := X) (Y := Y)) ρ := by
  classical
  rw [QuantumRuntime.potential_eq, QuantumRuntime.potential_eq]
  apply ENNReal.ofReal_le_ofReal
  have hh := ((PosSemidef.one (n := A)).kronecker
    (actual_sub_filled_gram_le_invalidStack io)).trace_mul_re_nonneg hρ
  have he (M N : Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ) :
      (1 : Matrix A A ℂ) ⊗ₖ (M - N) = (1 ⊗ₖ M) - (1 ⊗ₖ N) := by
    ext a b
    simp only [kroneckerMap_apply, Matrix.sub_apply, mul_sub]
  rw [he, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at hh
  linarith

end CompressedReplay

namespace QuantumRuntime

/-- The potential of a summable family of positive operators is the sum of its potentials. -/
theorem potential_tsum {A D Z ι : Type*} [Fintype A] [Fintype D] [Fintype Z]
    (K : Matrix Z D ℂ) {f : ι → Matrix (A × D) (A × D) ℂ}
    (hf : Summable f) (hpos : ∀ b, (f b).PosSemidef) :
    potential K (∑' b, f b) = ∑' b, potential K (f b) := by
  classical
  simp only [potential, MatrixMap.map_tsum _ hf]
  apply ofReal_trace_re_tsum (MatrixMap.summable_comp _ hf)
  intro b
  rw [MatrixMap.amplifyLeft_conj]
  exact (hpos b).mul_mul_conjTranspose_same _

/-- Taking the input of a call preserves support of the private register. -/
theorem supported_callInput {A J E D : Type*} [Fintype A] [Fintype J] [Fintype E]
    [Fintype D] [DecidableEq A] [DecidableEq J] [DecidableEq E] [DecidableEq D]
    {C : Type*} (population : D → C) (S : Set C) (ℓ : A ≃ J × E)
    {ρ : Matrix (A × D) (A × D) ℂ}
    (hρ : QuerySupportedOn (fun a : A × D ↦ population a.2) S ρ) :
    QuerySupportedOn (fun a : J × D ↦ population a.2) S (callInput ℓ D ρ) := by
  intro a b hab
  simp only [callInput, LinearMap.comp_apply, MatrixMap.traceRight_apply,
    SubInstrument.relabel_branch_apply, submatrix_apply] at hab
  obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
  exact hρ _ _ he

end QuantumRuntime

namespace EmulatedOracle

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg}
  (E : EmulatedOracle P In) (population : E.S → ℕ)

/-- Coherent control preserves a portwise one-step population-growth bound. -/
theorem population_coherent_le
    (h : ∀ i a b, E.U i a b ≠ 0 → population a.2 ≤ population b.2 + 1)
    (a b : (Σ i, In i) × E.S) (hab : E.coherent.U () a b ≠ 0) :
    population a.2 ≤ population b.2 + 1 := by
  rcases a with ⟨⟨i, a⟩, d⟩
  rcases b with ⟨⟨j, b⟩, d'⟩
  by_cases hij : i = j
  · subst j
    rw [E.coherent_U_apply_self] at hab
    exact h i _ _ hab
  · exact (hab (E.coherent_U_apply_of_ne hij a b d d')).elim

/-- One coherent call increases the support population by at most one, with an arbitrary
entangled remainder register. This is an operator-support statement, with no normalization. -/
theorem population_queryStep
    (h : ∀ i a b, E.U i a b ≠ 0 → population a.2 ≤ population b.2 + 1)
    {A : QReg} {t : ℕ} (F : QReg) (ℓ : A ≃ (Σ i, In i) × F) (r : Unit)
    {ρ : Matrix (A × E.S) (A × E.S) ℂ}
    (hρ : QuerySupportedOn (fun a : A × E.S ↦ population a.2) (Set.Iic t) ρ) :
    QuerySupportedOn (fun a : ((Σ i, In i) × F) × E.S ↦ population a.2)
      (Set.Iic (t + 1)) ((E.coherent.toRuntime.queryStep () F ℓ).branch r ρ) := by
  rw [QuantumRuntime.queryStep_branch_apply, SubInstrument.branch_frame_apply,
    E.coherent.toRuntime_step_branch]
  have h₁ := (hρ.branch_relabel (QuantumRuntime.queryEquivIn ℓ E.S)).imp
    (q' := fun a : (((Σ i, In i) × E.S) × F) ↦ population a.1.2)
    (S' := Set.Iic t) fun a ha ↦ by
      obtain ⟨b, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ E.S).surjective a
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at ha
  have h₂ := QuerySupportedOn.amplify_fst
    (q := fun a : (Σ i, In i) × E.S ↦ population a.2)
    (q' := fun a : (Σ i, In i) × E.S ↦ population a.2)
    (S := Set.Iic t) (S' := Set.Iic (t + 1))
    (fun σ hσ ↦ QuerySupportedOn.conj hσ fun a b hab hb ↦
      (E.population_coherent_le population h a b hab).trans (Nat.add_le_add_right hb 1)) h₁
  refine (h₂.branch_relabel (QuantumRuntime.queryEquivOut _ E.S F)).imp fun a ha ↦ ?_
  obtain ⟨b, rfl⟩ := (QuantumRuntime.queryEquivOut _ E.S F).surjective a
  rwa [Function.comp_apply, Equiv.symm_apply_apply] at ha

/-- A portwise one-step population bound lifts through arbitrary local instruments and
register-changing leaves of a coherently controlled program. The input may be any joint matrix. -/
theorem population_run (h : ∀ i a b, E.U i a b ≠ 0 → population a.2 ≤ population b.2 + 1)
    {L : LocalSig.{u, v}} (I : L.Interp) {W : QReg → Type w} {A : QReg}
    {x : QuantumComp L (cohSpec In) W A} {q : ℕ} (hx : x.IsQueryBound fun _ ↦ q) {t : ℕ}
    {ρ : Matrix (A × E.S) (A × E.S) ℂ}
    (hρ : QuerySupportedOn (fun a : A × E.S ↦ population a.2) (Set.Iic t) ρ)
    (p : Σ B, W B) :
    QuerySupportedOn (fun a : p.1 × E.S ↦ population a.2) (Set.Iic (t + q))
      ((E.coherent.toRuntime.run I x).branch p ρ) := by
  induction x using QuantumComp.inductionOn generalizing q t with
  | pure _ y =>
    rw [QuantumRuntime.run_pure]
    by_cases hp : p = ⟨_, y⟩
    · subst hp
      rw [DSubInstrument.branch_ret_self]
      exact QuerySupportedOn.mono hρ (Set.Iic_subset_Iic.mpr (Nat.le_add_right t q))
    · rw [DSubInstrument.branch_ret_of_ne _ hp]
      exact querySupportedOn_zero _ _
  | primBind _ o k ih =>
    rw [QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply]
    exact QuerySupportedOn.tsum fun b ↦
      ih b (fun i ↦ hx i b) (QuerySupportedOn.amplify_snd hρ _)
  | queryBind _ i F ℓ k ih =>
    obtain ⟨hq, hk⟩ := (QuantumComp.isQueryBound_queryBind_iff i F ℓ k _).mp hx
    have hb : Function.update (fun _ : Unit ↦ q) i (q - 1) = fun _ ↦ q - 1 :=
      funext fun j ↦ by cases i; cases j; exact Function.update_self ..
    rw [hb] at hk
    rw [QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply]
    refine QuerySupportedOn.tsum fun r ↦ ?_
    rw [SubInstrument.branch_toD_apply]
    cases i
    have hh := ih r (hk r) (E.population_queryStep population h F ℓ r hρ)
    rwa [Nat.add_assoc, Nat.add_sub_cancel' hq] at hh

section potentialAccumulation
variable {L : LocalSig.{u, v}} (I : L.Interp) {W : QReg → Type w}
  {A : QReg} {Z : Type*} [Fintype Z]
open QuantumRuntime

/-- Square-root potential increments telescope along actual coherent-runtime prefixes.
The local hypothesis is required only at the current population cutoff. Arbitrary local
instruments, entangled substates, and register-changing leaves are covered. Costs and their
sums are extended nonnegative reals, so no finiteness or normalization of masses is needed. -/
theorem run_potential_rpow_le (K : Matrix Z E.S ℂ)
    (hg : ∀ i a b, E.U i a b ≠ 0 → population a.2 ≤ population b.2 + 1)
    (cost : ℕ → Matrix ((Σ i, In i) × E.S) ((Σ i, In i) × E.S) ℂ → ℝ≥0∞)
    (hstep : ∀ n σ, σ.PosSemidef →
      QuerySupportedOn (fun a : (Σ i, In i) × E.S ↦ population a.2) (Set.Iic n) σ →
      potential K (MatrixMap.conj (E.coherent.U ()) σ) ^ (2⁻¹ : ℝ) ≤
        potential K σ ^ (2⁻¹ : ℝ) + cost n σ ^ (2⁻¹ : ℝ))
    (x : QuantumComp L (cohSpec In) W A) (n : ℕ)
    {ρ : Matrix (A × E.S) (A × E.S) ℂ} (hρ : ρ.PosSemidef)
    (hpop : QuerySupportedOn (fun a : A × E.S ↦ population a.2) (Set.Iic n) ρ) :
    (∑' p, potential K ((E.coherent.toRuntime.run I x).branch p ρ)) ^ (2⁻¹ : ℝ) ≤
      potential K ρ ^ (2⁻¹ : ℝ) +
        ∑' j, E.coherent.toRuntime.queryWeight I (fun _ ↦ cost (n + j)) x ρ j ^ (2⁻¹ : ℝ) := by
  induction x using QuantumComp.inductionOn generalizing n with
  | pure B y =>
    rw [run_pure, tsum_eq_single (⟨_, y⟩ : Σ B, W B) fun p hp ↦ by
      simp [DSubInstrument.branch_ret_of_ne _ hp, potential]]
    simp only [DSubInstrument.branch_ret_self, LinearMap.id_apply]
    exact le_self_add
  | primBind B o k ih =>
    have hb := fun b ↦ ((I o).frame E.S).posSemidef_branch_apply b hρ
    have he : ∀ p, potential K ((E.coherent.toRuntime.run I
        (QuantumComp.primBind o k)).branch p ρ) =
        ∑' b, potential K ((E.coherent.toRuntime.run I (k b)).branch p
          (((I o).frame E.S).branch b ρ)) := fun p ↦ by
      rw [run_primBind, DSubInstrument.branch_bind_apply]
      exact potential_tsum K ((((I o).frame _).isCPTNIFamily.comp_eval
        (fun b ↦ (E.coherent.toRuntime.run I (k b)).isCPTNIFamily) p).summable_apply ρ)
        fun b ↦ (E.coherent.toRuntime.run I (k b)).posSemidef_branch_apply p (hb b)
    simp only [he, queryWeight_primBind]
    rw [ENNReal.tsum_comm]
    refine (rpow_inv_two_tsum_le_of_le_add_tsum fun b ↦
      ih b n (hb b) (QuerySupportedOn.amplify_snd hpop _)).trans ?_
    exact add_le_add (ENNReal.rpow_le_rpow (tsum_potential_frame_le K (I o) hρ)
      (by norm_num)) le_rfl
  | queryBind B i F ℓ k ih =>
    have hr := fun r ↦ (E.coherent.toRuntime.queryStep i F ℓ).posSemidef_branch_apply r hρ
    have he : ∀ p, potential K ((E.coherent.toRuntime.run I
        (QuantumComp.queryBind i F ℓ k)).branch p ρ) =
        ∑' r, potential K ((E.coherent.toRuntime.run I (k r)).branch p
          ((E.coherent.toRuntime.queryStep i F ℓ).branch r ρ)) := fun p ↦ by
      rw [run_queryBind, DSubInstrument.branch_bind_apply]
      exact potential_tsum K
        (((SubInstrument.toD (E.coherent.toRuntime.queryStep i F ℓ)).isCPTNIFamily.comp_eval
          (fun r ↦ (E.coherent.toRuntime.run I (k r)).isCPTNIFamily) p).summable_apply ρ)
        fun r ↦ (E.coherent.toRuntime.run I (k r)).posSemidef_branch_apply p (hr r)
    simp only [he]
    rw [ENNReal.tsum_comm]
    refine (rpow_inv_two_tsum_le_of_le_add_tsum fun r ↦
      ih r (n + 1) (hr r) (E.population_queryStep population hg F ℓ r hpop)).trans ?_
    conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable, queryWeight_queryBind_zero, ← add_assoc]
    simp only [queryWeight_queryBind_succ, Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]
    apply add_le_add _ le_rfl
    simp only [tsum_fintype, Finset.univ_unique, Finset.sum_singleton]
    rw [potential_queryStep E.coherent.toRuntime K i F ℓ default ρ,
      E.coherent.toRuntime_step_branch]
    have hh := hstep n _ (posSemidef_callInput ℓ hρ)
      (supported_callInput population _ ℓ hpop)
    rw [potential_callInput] at hh
    exact hh


end potentialAccumulation

end EmulatedOracle

/-- Total populated cells across all compressed databases; response registers are excluded. -/
@[expose]
noncomputable def databasePopulation {k : ℕ} {X Y : Type} [Fintype X]
    (D : Fin k → Database X Y) : ℕ := ∑ i, (D i).size

section population

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

/-- An ordinary port of the old oracle adds at most one populated cell across the whole family. -/
theorem databasePopulation_ordinary_le (i : Fin k)
    (a b : (X × Y) × (Fin k → Database X Y))
    (hab : (compressedVCOracle k X Y).U i a b ≠ 0) :
    databasePopulation a.2 ≤ databasePopulation b.2 + 1 := by
  rcases a with ⟨a, D⟩
  rcases b with ⟨b, D'⟩
  rw [compressedVCOracle_U, onFactor_apply, splitAt_apply, splitAt_apply] at hab
  split_ifs at hab with hs
  · have hsize := size_le_of_compressedOracle_apply_ne_zero hab
    change (D i).size ≤ (D' i).size + 1 at hsize
    have hother : ∀ j : {j // j ≠ i}, (D j).size = (D' j).size :=
      fun j ↦ congrArg Database.size (congrFun hs j)
    simp only [databasePopulation]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i, Fintype.sum_eq_add_sum_subtype_ne _ i]
    simp only [hother]
    omega
  · exact (hab rfl).elim

variable {Cm Z : Type} [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z]
  [AddGroup Z] {Dm : Fin k → Type}
  (ME : MultiExtractor k Cm Dm (Fin k → Database X Y)) (code : TpDCode k Dm Z)

/-- Extraction leaves every database entry unchanged, so the old extraction-extended oracle
still adds at most one populated cell in a call. This holds for any extractor and encoding. -/
theorem databasePopulation_withExtract_le (i : Fin k ⊕ Unit)
    (a b : extIn k X Y Cm Z i × (Fin k → Database X Y))
    (hab : ((compressedVCOracle k X Y).withExtract ME code).U i a b ≠ 0) :
    databasePopulation a.2 ≤ databasePopulation b.2 + 1 := by
  cases i with
  | inl i => exact databasePopulation_ordinary_le i a b hab
  | inr i =>
    rcases a with ⟨⟨t, z⟩, D⟩
    rcases b with ⟨⟨t', z'⟩, D'⟩
    change extractUnitary ME code ((t, z), D) ((t', z'), D') ≠ 0 at hab
    rw [extractUnitary_apply] at hab
    split_ifs at hab with hs
    · rw [hs.2.2]
      exact Nat.le_succ _
    · exact (hab rfl).elim

/-- The original post-adversary state of the old coherent ordinary/extraction runtime is
supported on databases with at most the total query budget of populated cells. Local instruments,
adaptivity, entangled workspace, register-changing leaves and subnormalized inputs are allowed.
This theorem concerns the adversary's output before any challenger check. -/
theorem databasePopulation_post_old {L : LocalSig.{u, v}} (I : L.Interp)
    {W : QReg → Type w} {A : QReg}
    {x : QuantumComp L (EmulatedOracle.cohSpec (extIn k X Y Cm Z)) W A}
    {q : ℕ} (hx : x.IsQueryBound fun _ ↦ q) (ρ : SubState A) (p : Σ B, W B) :
    QuerySupportedOn
      (fun a : p.1 × (Fin k → Database X Y) ↦ databasePopulation a.2) (Set.Iic q)
      ((((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime.jointPost
        I x ρ p).matrix) := by
  rw [QuantumRuntime.matrix_jointPost]
  have hρ : QuerySupportedOn
      (fun a : A × (Fin k → Database X Y) ↦ databasePopulation a.2) (Set.Iic 0)
      (ρ.matrix ⊗ₖ ((compressedVCOracle k X Y).withExtract ME code).init.matrix) := by
    change QuerySupportedOn _ _
      (ρ.matrix ⊗ₖ (SubState.basis (fun _ : Fin k ↦ (Database.empty : Database X Y))).matrix)
    rw [SubState.matrix_basis]
    intro a b hab
    rw [kroneckerMap_apply] at hab
    have hs := right_ne_zero_of_mul hab
    rw [Matrix.single_apply] at hs
    split_ifs at hs with he
    · simp [← he.1, ← he.2, databasePopulation, Database.size_empty]
    · exact (hs rfl).elim
  have hh := ((compressedVCOracle k X Y).withExtract ME code).population_run databasePopulation
    (databasePopulation_withExtract_le ME code) I hx hρ p
  rw [Nat.zero_add] at hh
  exact hh

end population

namespace TpDCode

variable {k : ℕ} {Dm : Fin k → Type} [∀ i, Fintype (Dm i)]

/-- A length register and one additive response register per decommitment position. The extra
value in each coordinate keeps the register nonempty even for an empty decommitment type. -/
abbrev ConcatReg (k : ℕ) (Dm : Fin k → Type) [∀ i, Fintype (Dm i)] :=
  ZMod (k + 1) × ∀ i, ZMod (Fintype.card (Dm i) + 1)

/-- Encode one decommitment in its own additive response register. -/
@[expose]
noncomputable def concatCell (i : Fin k) (a : Dm i) : ZMod (Fintype.card (Dm i) + 1) :=
  ((Fintype.equivFin (Dm i) a).val : ℕ)

/-- Each component encoding is injective. -/
theorem concatCell_injective (i : Fin k) : Function.Injective (concatCell (Dm := Dm) i) := by
  intro a b h
  apply (Fintype.equivFin (Dm i)).injective
  apply Fin.ext
  have hv := congrArg ZMod.val h
  simpa only [concatCell, ZMod.val_natCast_of_lt
    (Nat.lt_succ_of_lt (Fintype.equivFin (Dm i) a).isLt),
    ZMod.val_natCast_of_lt (Nat.lt_succ_of_lt (Fintype.equivFin (Dm i) b).isLt)] using hv

/-- Concatenate the encoded components, padding the unused positions with zero. -/
@[expose]
noncomputable def concatPayload (j : TupleLen k) (t : TpDLen k Dm j)
    (i : Fin k) : ZMod (Fintype.card (Dm i) + 1) :=
  if h : i.val < j.len then concatCell i (t ⟨i.val, h⟩) else 0

/-- Reading a used coordinate of a concatenated payload recovers its component encoding. -/
@[simp]
theorem concatPayload_castLE (j : TupleLen k) (t : TpDLen k Dm j) (i : Fin j.len) :
    concatPayload j t (Fin.castLE j.len_le i) =
      concatCell (Fin.castLE j.len_le i) (t i) := by
  simp [concatPayload, i.isLt]

/-- A concrete injective encoding that keeps the response coordinates separate. This is the
concatenated output convention used in the disjoint-database argument of FIX (26b). -/
@[expose]
noncomputable def concat : TpDCode k Dm (ConcatReg k Dm) where
  enc t := ((t.1.len : ZMod (k + 1)), concatPayload t.1 t.2)
  enc_injective := by
    rintro ⟨j, a⟩ ⟨j', b⟩ h
    have hj : j = j' := by
      apply Subtype.ext
      apply Fin.ext
      have hv := congrArg (fun z : ConcatReg k Dm ↦ z.1.val) h
      change (j.len : ZMod (k + 1)).val = (j'.len : ZMod (k + 1)).val at hv
      rw [ZMod.val_natCast_of_lt (show j.len < k + 1 from j.1.isLt),
        ZMod.val_natCast_of_lt (show j'.len < k + 1 from j'.1.isLt)] at hv
      exact hv
    subst j'
    congr 1
    funext i
    apply concatCell_injective (Fin.castLE j.len_le i)
    have hi := congrArg (fun z : ConcatReg k Dm ↦ z.2 (Fin.castLE j.len_le i)) h
    simpa only [concatPayload_castLE] using hi

/-- At full length the payload is precisely the family of component encodings. -/
@[simp]
theorem concat_full (hk : 1 ≤ k) (t : TpDLen k Dm (TupleLen.full hk)) :
    (concat (Dm := Dm)).enc ⟨TupleLen.full hk, t⟩ =
      ((k : ZMod (k + 1)), fun i : Fin k ↦ concatCell (Dm := Dm) i (t i)) := by
  refine Prod.ext ?_ ?_
  · rfl
  · funext i
    exact concatPayload_castLE (TupleLen.full hk) t i

variable {Cm S : Type}

/-- Add a tuple-dependent response while leaving the tuple and database unchanged. -/
@[expose]
noncomputable def responsePerm (f : TpIC k Cm → S → ConcatReg k Dm) :
    Equiv.Perm ((TpIC k Cm × ConcatReg k Dm) × S) where
  toFun a := ((a.1.1, a.1.2 + f a.1.1 a.2), a.2)
  invFun a := ((a.1.1, a.1.2 - f a.1.1 a.2), a.2)
  left_inv a := by simp
  right_inv a := by simp

/-- Composing response translations adds their offsets; all database registers are unchanged. -/
theorem responsePerm_add (f g : TpIC k Cm → S → ConcatReg k Dm) :
    responsePerm (fun t s ↦ f t s + g t s) = responsePerm f * responsePerm g := by
  apply Equiv.ext
  rintro ⟨⟨t, z⟩, s⟩
  change ((t, z + (f t s + g t s)), s) = ((t, (z + g t s) + f t s), s)
  congr 2
  abel

/-- Response translations commute, even when their offsets depend on the database. -/
theorem responsePerm_commute (f g : TpIC k Cm → S → ConcatReg k Dm) :
    Commute (responsePerm f) (responsePerm g) := by
  change responsePerm f * responsePerm g = responsePerm g * responsePerm f
  rw [← responsePerm_add, ← responsePerm_add]
  congr 1
  funext t s
  exact add_comm _ _

/-- The length part of a concatenated extraction response is independent of the database. -/
@[expose]
noncomputable def lengthResponse (t : TpIC k Cm) (_s : S) : ConcatReg k Dm :=
  ((t.1.len : ZMod (k + 1)), 0)

/-- The response on a selected set of positions; the length register is unchanged. -/
@[expose]
noncomputable def partResponse (ME : MultiExtractor k Cm Dm S) (B : Finset (Fin k))
    (t : TpIC k Cm) (s : S) : ConcatReg k Dm :=
  (0, fun i ↦ if i ∈ B then concatPayload t.1 (ME.extract t s) i else 0)

/-- Partitioning the response coordinates splits its payload additively. -/
theorem partResponse_union (ME : MultiExtractor k Cm Dm S) (B C : Finset (Fin k))
    (hBC : Disjoint B C) (t : TpIC k Cm) (s : S) :
    partResponse ME (B ∪ C) t s = partResponse ME B t s + partResponse ME C t s := by
  apply Prod.ext (by simp [partResponse])
  funext i
  have hi := Finset.disjoint_left.mp hBC
  by_cases hb : i ∈ B <;> by_cases hc : i ∈ C
  · exact (hi hb hc).elim
  all_goals simp [partResponse, hb, hc]

/-- The full concatenated encoding is its length and all payload coordinates. -/
theorem concat_response (ME : MultiExtractor k Cm Dm S) (t : TpIC k Cm) (s : S) :
    (concat (Dm := Dm)).enc ⟨t.1, ME.extract t s⟩ =
      lengthResponse t s + partResponse ME Finset.univ t s := by
  simp [concat, lengthResponse, partResponse]

/-- Factor extraction into length, before, after, and unchecked response translations.
The identity includes every tuple length and rejected duplicate-index tuples. No locality
property of the extractor is needed for this algebraic identity. -/
theorem extractPerm_concat_factor (ME : MultiExtractor k Cm Dm S)
    (B A C : Finset (Fin k)) (hBA : Disjoint B A) (hBC : Disjoint (B ∪ A) C)
    (hcover : B ∪ A ∪ C = Finset.univ) :
    extractPerm ME (concat (Dm := Dm)) =
      responsePerm lengthResponse * responsePerm (partResponse ME B) *
        responsePerm (partResponse ME A) * responsePerm (partResponse ME C) := by
  have heq : extractPerm ME (concat (Dm := Dm)) =
      responsePerm (fun t s ↦ lengthResponse t s +
        partResponse ME B t s + partResponse ME A t s + partResponse ME C t s) := by
    apply Equiv.ext
    rintro ⟨⟨t, z⟩, s⟩
    change ((t, z + (concat (Dm := Dm)).enc ⟨t.1, ME.extract t s⟩), s) =
      ((t, z + (lengthResponse t s + partResponse ME B t s +
        partResponse ME A t s + partResponse ME C t s)), s)
    congr 3
    rw [concat_response, ← hcover, partResponse_union ME _ _ hBC,
      partResponse_union ME _ _ hBA]
    abel
  rw [heq, responsePerm_add, responsePerm_add, responsePerm_add]

/-- The coherent extraction matrix has the same factorization as its basis permutation.
Thus the factorization holds on entangled states and superpositions of extraction tuples. -/
theorem extractUnitary_concat_factor [Fintype Cm] [DecidableEq Cm]
    [Fintype S] [DecidableEq S] (ME : MultiExtractor k Cm Dm S)
    (B A C : Finset (Fin k)) (hBA : Disjoint B A) (hBC : Disjoint (B ∪ A) C)
    (hcover : B ∪ A ∪ C = Finset.univ) :
    extractUnitary ME (concat (Dm := Dm)) =
      basisMatrix (responsePerm (lengthResponse (Dm := Dm) (Cm := Cm) (S := S))) *
        basisMatrix (responsePerm (partResponse ME B)) *
        basisMatrix (responsePerm (partResponse ME A)) *
        basisMatrix (responsePerm (partResponse ME C)) := by
  rw [extractUnitary, extractPerm_concat_factor ME B A C hBA hBC hcover]
  simp only [Equiv.Perm.coe_mul, basisMatrix_comp]

end TpDCode

section extraction
variable {k : ℕ} {X Y Cm : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Cm] [DecidableEq Cm] {Z : Type} [Fintype Z] [DecidableEq Z] [AddCommGroup Z]
  {Dm : Fin k → Type}

/-- Separate the extraction tuple from the flattened database and response register. -/
@[expose]
noncomputable def flatExtractSplit :
    ((TpIC k Cm × Z) × (Fin k → Database X Y)) ≃
      (Database (Fin k × X) Y × Z) × TpIC k Cm where
  toFun a := ((Function.uncurry a.2, a.1.2), a.1.1)
  invFun a := ((a.2, a.1.2), Function.curry a.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Cm]
  [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddCommGroup Z] in
/-- The extraction splitting keeps its tuple as the block index. -/
theorem flatExtractSplit_apply (a : (TpIC k Cm × Z) × (Fin k → Database X Y)) :
    flatExtractSplit a = ((Function.uncurry a.2, a.1.2), a.1.1) := rfl

omit [DecidableEq X] [Fintype Y] [Fintype Cm] [Fintype Z] in
/-- The actual coherent extraction unitary is block diagonal in its input tuple. -/
theorem extractUnitary_flat_blocks
    (ME : MultiExtractor k Cm Dm (Fin k → Database X Y)) (code : TpDCode k Dm Z) :
    extractUnitary ME code = liftBlocks flatExtractSplit
      (fun tic ↦ databaseControl
        (fun D ↦ code.enc ⟨tic.1, ME.extract tic (Function.curry D)⟩) (xorShift Z)) := by
  ext ⟨⟨t,z⟩,D⟩ ⟨⟨t',z'⟩,D'⟩
  simp only [extractUnitary_apply, liftBlocks, submatrix_apply, blockDiagonal_apply,
    flatExtractSplit_apply, databaseControl, labelControlled_apply,
    kroneckerMap_apply, one_apply, xorShift_apply]
  have he : Function.uncurry D = Function.uncurry D' ↔ D = D' :=
    (Equiv.curry (Fin k) X (Option Y)).symm.injective.eq_iff
  change (if t = t' ∧ z = z' + code.enc ⟨t'.1, ME.extract t' D'⟩ ∧ D = D'
    then 1 else 0) = _
  simp only [he]
  by_cases ht : t = t'
  · subst t'
    by_cases hD : D = D'
    · subst D'
      simp only [ite_true, one_mul, true_and, and_true]
      rfl
    · simp [hD]
  · simp [ht]

omit [Fintype Cm] [Fintype Z] [AddCommGroup Z] in
/-- Every invalid projector has the same flattened cell operator in each extraction-tuple block. -/
theorem invalid_flat_blocks [Nonempty Y] (c : Fin k × X) :
    (1 : Matrix (TpIC k Cm × Z) (TpIC k Cm × Z) ℂ) ⊗ₖ CompressedReplay.invalid c =
      liftBlocks (flatExtractSplit (Cm := Cm) (Z := Z))
        (fun _ ↦ databaseInvalidCell (Y := Y) (Z := Z) c) := by
  ext ⟨⟨t,z⟩,D⟩ ⟨⟨t',z'⟩,D'⟩
  have h := congrArg (fun A : Matrix ((Fin k → Database X Y) × Z) _ ℂ ↦ A (D,z) (D',z'))
    (CompressedReplay.databaseInvalidCell_flat (Z := Z) c)
  simp only [submatrix_apply, Equiv.prodCongr_apply, Equiv.curry_symm_apply, Equiv.refl_apply,
    kroneckerMap_apply, Prod.map_apply] at h
  simp only [liftBlocks, submatrix_apply, blockDiagonal_apply, flatExtractSplit_apply,
    h, kroneckerMap_apply, one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

omit [DecidableEq X] [Fintype Y] [Fintype Cm] [Fintype Z] [AddCommGroup Z] in
/-- The original population cutoff has the same flattened cutoff in every tuple block. -/
theorem population_flat_blocks (s : ℕ) :
    diagonal (fun a : (TpIC k Cm × Z) × (Fin k → Database X Y) ↦
      if databasePopulation a.2 ≤ s then (1 : ℂ) else 0) =
      liftBlocks (flatExtractSplit (Cm := Cm) (Z := Z))
        (fun _ ↦ populationCut (C := Fin k × X) (Y := Y) (Z := Z) s) := by
  rw [← liftBlocks_diagonal (flatExtractSplit (Cm := Cm) (Z := Z))]
  congr 1
  funext tic
  congr 1
  funext a
  change (if databasePopulation (Function.curry a.1) ≤ s then (1 : ℂ) else 0) =
    if a.1.size ≤ s then 1 else 0
  rw [database_size_curry]
  rfl

end extraction
namespace SaltedMerkle

section factorization

open _root_.SaltedMerkle

variable {X Y Msg Salt : Type} [LinearOrder Y] [Fintype Y]
  [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
  (enc : Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ)

/-- At full length, a component response depends only on its selected database. If the index
list has duplicates, all components are constant instead, so the same locality holds. -/
theorem partResponse_full_eq (hk : 1 ≤ k) (idx : Fin k → Fin k) (cm : Fin k → Y)
    (B : Finset (Fin k)) (D D' : Fin k → Database X Y)
    (hD : ∀ i ∈ B, D (idx i) = D' (idx i)) :
    TpDCode.partResponse (multiExtract enc d) B (TpIC.full hk idx cm) D =
      TpDCode.partResponse (multiExtract enc d) B (TpIC.full hk idx cm) D' := by
  refine Prod.ext rfl ?_
  funext i
  by_cases hi : i ∈ B
  · simp only [TpDCode.partResponse, hi, ite_true]
    simp only [TpDCode.concatPayload, dite_eq_left
      (show i.val < (TpIC.full hk idx cm).1.len from i.isLt)]
    congr 1
    simp only [multiExtract]
    split_ifs
    · change extract enc (d i) (cm i) (D (idx i)) =
        extract enc (d i) (cm i) (D' (idx i))
      rw [hD i hi]
    · rfl
  · simp [TpDCode.partResponse, hi]

/-- A rejected duplicate-index full tuple has a database-independent response on every subset
of positions, not only a database-independent complete response. -/
theorem partResponse_full_eq_of_not_injective (hk : 1 ≤ k) (idx : Fin k → Fin k)
    (cm : Fin k → Y) (B : Finset (Fin k)) (D D' : Fin k → Database X Y)
    (hidx : ¬ Function.Injective idx) :
    TpDCode.partResponse (multiExtract enc d) B (TpIC.full hk idx cm) D =
      TpDCode.partResponse (multiExtract enc d) B (TpIC.full hk idx cm) D' := by
  have h : ¬ Function.Injective (TpIC.full hk idx cm).idx := hidx
  simp only [TpDCode.partResponse, multiExtract, ite_eq_right h]

/-- Distinct tuple indices send disjoint position batches to disjoint database batches. -/
theorem disjoint_image_indices {idx : Fin k → Fin k} (hidx : Function.Injective idx)
    {B A : Finset (Fin k)} (hBA : Disjoint B A) :
    Disjoint (B.image idx) (A.image idx) := by
  apply Finset.disjoint_left.mpr
  intro j hj hj'
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hj'
  exact Finset.disjoint_left.mp hBA hb (hidx hab ▸ ha)

/-- The disjoint-batch identity in FIX (26b). Its right side applies the after-extraction
factor to the original state, so it does not assert that check projectors preserve population. -/
theorem checker_batches_factor {R : Type*} [Ring R] (Aa Ab Qa Qb Va Vb Vc : R)
    (hca : Commute Ab Vc) (hcq : Commute Qb Vc)
    (haa : Commute Ab Va) (hqa : Commute Qb Va)
    (hab : Commute Vb Aa) (hqb : Commute Vb Qa)
    (hA : Commute Ab Aa) (hQ : Commute Qb Qa) :
    Ab * (Vc * Va * Vb) * Aa - Qb * (Vc * Va * Vb) * Qa =
      Vc * Va * (Aa * Ab - Qa * Qb) * Vb := by
  have h (b a : R) (hc : Commute b Vc) (hv : Commute b Va)
      (hw : Commute Vb a) (hba : Commute b a) :
      b * (Vc * Va * Vb) * a = Vc * Va * (a * b) * Vb := by
    calc
      _ = (b * Vc) * Va * (Vb * a) := by simp only [mul_assoc]
      _ = (Vc * b) * Va * (a * Vb) := by rw [hc.eq, hw.eq]
      _ = Vc * (b * Va) * a * Vb := by simp only [mul_assoc]
      _ = Vc * (Va * b) * a * Vb := by rw [hv.eq]
      _ = Vc * Va * (b * a) * Vb := by simp only [mul_assoc]
      _ = _ := by rw [hba.eq]
  rw [h Ab Aa hca haa hab hA, h Qb Qa hcq hqa hqb hQ, mul_sub, sub_mul]

end factorization

/-- The leakage sum `T_u` of FIX (35), zero at zero and one total calls. -/
@[expose]
noncomputable def oldLeakagePolynomial (u : ℕ) : ℝ :=
  if 2 ≤ u then (u : ℝ) * (u - 1 : ℕ) * (4 * u - 5 : ℕ) / 6 else 0

/-- The capped fraction of changing labels `a_u` in FIX (35). -/
@[expose]
noncomputable def oldChangingFraction (N u : ℕ) : ℝ :=
  min 1 ((2 * u - 1 : ℕ) / (N : ℝ))

section localExtraction

variable {X Y Msg Salt : Type} [Fintype X] [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [Nonempty Y] [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]

/-- The filled-cell commutator estimate in FIX (27) for any function of a Merkle extraction
result, including a selected component batch. The tuple may contain repeated oracle indices.
The remaining database has fewer than `s` filled cells; all other databases and all ancilla
unitaries are arbitrary. -/
theorem filledCell_extraction_commutator_le
    (enc : _root_.SaltedMerkle.Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ)
    (tic : TpIC k Y) (Dfix : Fin k → Database X Y) (j : Fin k)
    (D : Database X Y) (x : X) (hx : D x = none) (s : ℕ) (hsize : D.size < s)
    {κ Z : Type*} [Fintype Z] [DecidableEq Z]
    (f : TpDLen k (DmOf (fun i ↦ 2 ^ d i) Msg
      (fun i ↦ _root_.SaltedMerkle.Td Y Salt (d i))) tic.1 → κ)
    (U : κ → Matrix Z Z ℂ) (hU : ∀ a, U a ∈ unitaryGroup Z ℂ) :
    let β := fun y ↦ f ((_root_.SaltedMerkle.multiExtract enc d).extract tic
      (Function.update Dfix j (Function.update D x (some y))))
    let V := labelControlled (fun a : Y × Z ↦ β a.1)
      (fun a ↦ (1 : Matrix Y Y ℂ) ⊗ₖ U a)
    ‖V * (uniformSubsetProjector Finset.univ ⊗ₖ (1 : Matrix Z Z ℂ)) -
      (uniformSubsetProjector Finset.univ ⊗ₖ (1 : Matrix Z Z ℂ)) * V‖ ≤
      2 * Real.sqrt (oldChangingFraction (Fintype.card Y) s) := by
  classical
  dsimp only
  let π := onlineLabel (_root_.SaltedMerkle.multiExtract enc d) ![tic] Dfix j
  let β := fun y ↦ f ((_root_.SaltedMerkle.multiExtract enc d).extract tic
    (Function.update Dfix j (Function.update D x (some y))))
  let base := f ((_root_.SaltedMerkle.multiExtract enc d).extract tic (Function.update Dfix j D))
  have hsub : (Finset.univ.filter fun y ↦ β y ≠ base) ⊆
      (Finset.univ.filter fun y ↦ π (Function.update D x (some y)) ≠ π D) := by
    intro y hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro heq
    exact (Finset.mem_filter.mp hy).2 (congrArg (fun z ↦ f (z 0)) heq)
  have hc : (Finset.univ.filter fun y ↦ β y ≠ base).card ≤ 2 * D.size + 1 :=
    (Finset.card_le_card hsub).trans
      (_root_.SaltedMerkle.card_onlineLabel_changes_le enc d tic Dfix j D x hx)
  have hfrac : ((Finset.univ.filter fun y ↦ β y ≠ base).card : ℝ) / Fintype.card Y ≤
      oldChangingFraction (Fintype.card Y) s := by
    apply le_min
    · exact (div_le_one (by positivity)).mpr (by exact_mod_cast Finset.card_le_univ _)
    · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast (show (Finset.univ.filter fun y ↦ β y ≠ base).card ≤ 2 * s - 1 by omega)
  exact (uniformProjector_commutator_le β base U hU).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hfrac) (by norm_num))

end localExtraction

section globalExtraction
variable {X Y Msg Salt : Type} [Fintype X] [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [Nonempty Y] [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]

/-- A function of Merkle extraction changes on at most the fraction in FIX (27), in every
occupied-cell context of a population-restricted database. Repeated-index tuples are included. -/
theorem extraction_changingFraction_le
    (enc : _root_.SaltedMerkle.Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ)
    (tic : TpIC k Y) {κ : Type*} [DecidableEq κ]
    (f : TpDLen k (DmOf (fun i ↦ 2 ^ d i) Msg
      (fun i ↦ _root_.SaltedMerkle.Td Y Salt (d i))) tic.1 → κ)
    (D : Database (Fin k × X) Y) (s : ℕ) (hs : D.size ≤ s)
    (c : Fin k × X) (hc : (D c).isSome) :
    changingFraction (fun D ↦ f ((_root_.SaltedMerkle.multiExtract enc d).extract tic
      (Function.curry D))) c (fun i ↦ D i.1) ≤ oldChangingFraction (Fintype.card Y) s := by
  classical
  let D0 : Database X Y := Function.update (Function.curry D c.1) c.2 none
  have h0 : D0 c.2 = none := Function.update_self ..
  have hpop : D0.size < s := by
    have herase := database_size_erase D c hc
    have hsum := database_size_curry (Function.update D c none)
    rw [curry_update_cell] at hsum
    have hj := Finset.single_le_sum
      (f := fun j : Fin k ↦ Database.size
        (Function.update (Function.curry D) c.1 D0 j))
      (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ c.1)
    simp only [Function.update_self] at hj
    change Database.size (Function.update D c none) =
      ∑ j, Database.size (Function.update (Function.curry D) c.1 D0 j) at hsum
    omega
  let π := onlineLabel (_root_.SaltedMerkle.multiExtract enc d) ![tic] (Function.curry D) c.1
  let β := fun y ↦ f ((_root_.SaltedMerkle.multiExtract enc d).extract tic
    (Function.update (Function.curry D) c.1 (Function.update D0 c.2 (some y))))
  let base := f ((_root_.SaltedMerkle.multiExtract enc d).extract tic
    (Function.update (Function.curry D) c.1 D0))
  have hsub : (Finset.univ.filter fun y ↦ β y ≠ base) ⊆
      (Finset.univ.filter fun y ↦ π (Function.update D0 c.2 (some y)) ≠ π D0) := by
    intro y hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro heq
    exact (Finset.mem_filter.mp hy).2 (congrArg (fun z ↦ f (z 0)) heq)
  have hcard : (Finset.univ.filter fun y ↦ β y ≠ base).card ≤ 2 * D0.size + 1 :=
    (Finset.card_le_card hsub).trans
      (_root_.SaltedMerkle.card_onlineLabel_changes_le enc d tic
        (Function.curry D) c.1 D0 c.2 h0)
  have heq : changingFraction (fun D ↦ f ((_root_.SaltedMerkle.multiExtract enc d).extract tic
      (Function.curry D))) c (fun i ↦ D i.1) =
        ((Finset.univ.filter fun y ↦ β y ≠ base).card : ℝ) / Fintype.card Y := by
    rw [changingFraction_eq_update]
    simp only [curry_update_cell D c.1 c.2, β, base, D0, Function.update_idem]
  rw [heq]
  apply le_min
  · exact (div_le_one (by positivity)).mpr (by exact_mod_cast Finset.card_le_univ _)
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (show (Finset.univ.filter fun y ↦ β y ≠ base).card ≤ 2 * s - 1 by omega)

/-- The componentwise Merkle extraction increment of FIX (27), for every function selecting
extraction components and every ancilla unitary family. The input is any positive subnormalized
state supported on the original population-`s` subspace, including entangled states. -/
theorem extraction_invalid_increment
    (enc : _root_.SaltedMerkle.Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ)
    (tic : TpIC k Y) {κ Z : Type*} [Fintype Z] [DecidableEq Z]
    (f : TpDLen k (DmOf (fun i ↦ 2 ^ d i) Msg
      (fun i ↦ _root_.SaltedMerkle.Td Y Salt (d i))) tic.1 → κ)
    (U : κ → Matrix Z Z ℂ) (hU : ∀ a, U a ∈ unitaryGroup Z ℂ) (s : ℕ)
    {ρ : Matrix (Database (Fin k × X) Y × Z) (Database (Fin k × X) Y × Z) ℂ}
    (hρ : ρ.PosSemidef) (ht : ρ.trace.re ≤ 1) (hpop : populationCut s * ρ = ρ) :
    let V := databaseControl
      (fun D ↦ f ((_root_.SaltedMerkle.multiExtract enc d).extract tic (Function.curry D))) U
    let R := fun c : Fin k × X ↦ databaseInvalidCell (Y := Y) (Z := Z) c
    (∑' c, ENNReal.ofReal (MatrixMap.conj (R c) (MatrixMap.conj V ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
      (∑' c, ENNReal.ofReal (MatrixMap.conj (R c) ρ).trace.re) ^ (2⁻¹ : ℝ) +
        ENNReal.ofReal (2 * Real.sqrt (s * oldChangingFraction (Fintype.card Y) s)) := by
  classical
  exact databaseControl_invalid_increment _ U hU s (le_min (by norm_num) (by positivity))
    (fun D hD c hc ↦ extraction_changingFraction_le enc d tic f D s hD c hc) hρ ht hpop

end globalExtraction

section coherentExtraction
variable {X Y Msg Salt : Type} [Fintype X] [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [Nonempty Y] [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
  {Z : Type} [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

/-- The actual coherent Merkle extraction port satisfies the summed invalid commutator
Gram bound of FIX (27). Each tuple is bounded separately before the orthogonal blocks
are assembled, including rejected duplicate-index tuples. Any injective response code is allowed. -/
theorem extractUnitary_invalid_gram_le
    (enc : _root_.SaltedMerkle.Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ)
    (code : TpDCode k (DmOf (fun i ↦ 2 ^ d i) Msg
      (fun i ↦ _root_.SaltedMerkle.Td Y Salt (d i))) Z) (s : ℕ) :
    let V := extractUnitary (_root_.SaltedMerkle.multiExtract enc d) code
    let K := diagonal (fun a : (TpIC k Y × Z) × (Fin k → Database X Y) ↦
      if databasePopulation a.2 ≤ s then (1 : ℂ) else 0)
    let R := fun c : Fin k × X ↦
      (1 : Matrix (TpIC k Y × Z) (TpIC k Y × Z) ℂ) ⊗ₖ CompressedReplay.invalid c
    ((4 * s * oldChangingFraction (Fintype.card Y) s) • K -
      K * (∑ c, (V * R c - R c * V)ᴴ * (V * R c - R c * V)) * K).PosSemidef := by
  classical
  let ME := _root_.SaltedMerkle.multiExtract enc d
  let e := flatExtractSplit (k := k) (X := X) (Y := Y) (Cm := Y) (Z := Z)
  let V := fun tic : TpIC k Y ↦ databaseControl
    (fun D ↦ code.enc ⟨tic.1, ME.extract tic (Function.curry D)⟩) (xorShift Z)
  let K := fun _ : TpIC k Y ↦ populationCut (C := Fin k × X) (Y := Y) (Z := Z) s
  let R := fun c : Fin k × X ↦ fun _ : TpIC k Y ↦
    databaseInvalidCell (Y := Y) (Z := Z) c
  let F := fun c ↦ V * R c - R c * V
  let a := 4 * s * oldChangingFraction (Fintype.card Y) s
  have hblocks : ∀ tic, (a • K tic - K tic *
      (∑ c, (F c tic)ᴴ * F c tic) * K tic).PosSemidef := by
    intro tic
    exact databaseControl_sum_commutator_gram_le _ (xorShift Z) xorShift_mem_unitaryGroup s
      (le_min (by norm_num) (by positivity))
      (fun D hD c hc ↦ extraction_changingFraction_le enc d tic
        (fun dm ↦ code.enc ⟨tic.1, dm⟩) D s hD c hc)
  have h := liftBlocks_sum_gram_le e V K R a hblocks
  have hV : liftBlocks e V = extractUnitary ME code := (extractUnitary_flat_blocks ME code).symm
  have hR (c : Fin k × X) : liftBlocks e (R c) =
      (1 : Matrix (TpIC k Y × Z) (TpIC k Y × Z) ℂ) ⊗ₖ CompressedReplay.invalid c :=
    (invalid_flat_blocks c).symm
  have hK : liftBlocks e K = diagonal (fun a : (TpIC k Y × Z) × (Fin k → Database X Y) ↦
      if databasePopulation a.2 ≤ s then (1 : ℂ) else 0) := (population_flat_blocks s).symm
  dsimp only at h
  rw [hV, hK] at h
  simp only [hR] at h
  exact h

end coherentExtraction

/-- FIX (35): total calls `u`, ordinary mass `w`, extraction mass `e`, and raw checks `q`.
This is a numerical expression, with no claim about the probability of an experiment. -/
@[expose]
noncomputable def oldOfflineError (N u : ℕ) (w e : ℝ) (q : ℕ) : ℝ :=
  min 1 ((Real.sqrt (3 * w * u * (u - 1 : ℕ) / N) + 2 * Real.sqrt ((q : ℝ) / N) +
    2 * Real.sqrt (e * oldLeakagePolynomial u / N) +
    2 * Real.sqrt (u * oldChangingFraction N u)) ^ 2)

/-- The Merkle P4 numerical budget uses `d + 1` hash checks per opened position. -/
@[expose]
noncomputable def oldMerkleOfflineError (N d u : ℕ) (w e : ℝ) (qs : ℕ) : ℝ :=
  oldOfflineError N u w e (qs * (d + 1))

/-- No leakage accumulates before the first call. -/
@[simp] theorem oldLeakagePolynomial_zero : oldLeakagePolynomial 0 = 0 := by
  norm_num [oldLeakagePolynomial]

/-- One call gives a zero leakage polynomial. -/
@[simp] theorem oldLeakagePolynomial_one : oldLeakagePolynomial 1 = 0 := by
  norm_num [oldLeakagePolynomial]

/-- The leakage polynomial is nonnegative, including the two exceptional small budgets. -/
theorem oldLeakagePolynomial_nonneg (u : ℕ) : 0 ≤ oldLeakagePolynomial u := by
  unfold oldLeakagePolynomial
  split_ifs <;> positivity

/-- The polynomial in FIX (28) is the exact sum of the prefix leakage coefficients. -/
theorem oldLeakagePolynomial_eq_sum (u : ℕ) :
    oldLeakagePolynomial u = ∑ j ∈ Finset.range u, (j : ℝ) * (2 * j - 1) := by
  have hs (n : ℕ) :
      (∑ j ∈ Finset.range n, (j : ℝ) * (2 * j - 1)) =
        (n : ℝ) * (n - 1) * (4 * n - 5) / 6 := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [hs]
  rcases u with _ | _ | u
  · norm_num [oldLeakagePolynomial]
  · norm_num [oldLeakagePolynomial]
  · simp only [oldLeakagePolynomial, show 2 ≤ u + 1 + 1 by omega, ite_true]
    rw [Nat.cast_sub (by omega : 1 ≤ u + 1 + 1),
      Nat.cast_sub (by omega : 5 ≤ 4 * (u + 1 + 1))]
    push_cast
    ring

/-- FIX (28), as an extended-nonnegative-real Cauchy--Schwarz estimate. The masses may be
infinite; no conversion of a mass to a real number is used. This lemma only aggregates given
prefix masses and does not identify them with the extraction masses of a runtime. -/
theorem oldLeakage_sum_sqrt_le (u : ℕ) (N : ℝ≥0∞) (mass : ℕ → ℝ≥0∞) :
    ∑ j ∈ Finset.range u,
        (ENNReal.ofReal ((j : ℝ) * (2 * j - 1)) / N * mass j) ^ (2⁻¹ : ℝ) ≤
      (ENNReal.ofReal (oldLeakagePolynomial u) / N *
        ∑ j ∈ Finset.range u, mass j) ^ (2⁻¹ : ℝ) := by
  have hn (j : ℕ) : 0 ≤ (j : ℝ) * (2 * j - 1) := by
    rcases j with _ | j
    · norm_num
    · push_cast
      exact mul_nonneg (by positivity) (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  have hs : (∑ j ∈ Finset.range u, ENNReal.ofReal ((j : ℝ) * (2 * j - 1)) / N) =
      ENNReal.ofReal (oldLeakagePolynomial u) / N := by
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hn j),
      ← oldLeakagePolynomial_eq_sum]
  rw [← hs]
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  simpa only [rpow_inv_two_rpow_two, one_div] using
    ENNReal.inner_le_Lp_mul_Lq (Finset.range u)
      (fun j ↦ (ENNReal.ofReal ((j : ℝ) * (2 * j - 1)) / N) ^ (2⁻¹ : ℝ))
      (fun j ↦ mass j ^ (2⁻¹ : ℝ)) Real.HolderConjugate.two_two

/-- The collision coefficient from NOTE (91) is bounded by the FIX (35) coefficient from
four total calls onward. The small budgets are deliberately excluded. -/
theorem collisionCoefficient_le_fix {u : ℕ} (hu : 4 ≤ u) {N w : ℝ}
    (hN : 0 < N) (hw : 0 ≤ w) :
    ((7 * u + 5) * u / (4 * N)) * min w u ≤ 3 * w * u * (u - 1 : ℕ) / N := by
  have hu' : (4 : ℝ) ≤ u := by exact_mod_cast hu
  have hc : (7 * (u : ℝ) + 5) * u / (4 * N) ≤ 3 * u * (u - 1) / N := by
    apply (div_le_div_iff₀ (by positivity) hN).mpr
    have hp : 0 ≤ (u : ℝ) * N := by positivity
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 5 * u - 17 by linarith) hp]
  calc
    _ ≤ ((7 * u + 5) * u / (4 * N)) * w :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
    _ ≤ (3 * u * (u - 1) / N) * w := mul_le_mul_of_nonneg_right hc hw
    _ = _ := by rw [Nat.cast_sub (by omega : 1 ≤ u)]; push_cast; ring

/-- The finite error is a number in `[0, 1]`. -/
theorem oldOfflineError_mem_Icc (N u : ℕ) (w e : ℝ) (q : ℕ) :
    oldOfflineError N u w e q ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_min zero_le_one (sq_nonneg _), min_le_left _ _⟩

/-- Zero total calls and zero checks give zero error for every mass parameter. -/
@[simp] theorem oldOfflineError_zero (N : ℕ) (w e : ℝ) :
    oldOfflineError N 0 w e 0 = 0 := by
  simp [oldOfflineError]

/-- The Merkle specialization retains the probability cap. -/
theorem oldMerkleOfflineError_mem_Icc (N d u : ℕ) (w e : ℝ) (qs : ℕ) :
    oldMerkleOfflineError N d u w e qs ∈ Set.Icc (0 : ℝ) 1 :=
  oldOfflineError_mem_Icc N u w e (qs * (d + 1))

end SaltedMerkle
end Quantum

namespace Quantum.SaltedMerkle
section oldCoherent
variable {X Y Msg Salt : Type} [Fintype X] [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [AddCommGroup Y] [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
  {Z : Type} [Fintype Z] [DecidableEq Z] [AddCommGroup Z]
open EmulatedOracle

/-- The old coherent ordinary/extraction oracle satisfies the invalid commutator Gram bound
of FIX (27), charging only extraction mass. Ordinary ports contribute zero. -/
theorem old_coherent_invalid_gram_le
    (enc : _root_.SaltedMerkle.Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ)
    (code : TpDCode k (DmOf (fun i ↦ 2 ^ d i) Msg
      (fun i ↦ _root_.SaltedMerkle.Td Y Salt (d i))) Z) (s : ℕ) :
    let E := (compressedVCOracle k X Y).withExtract (_root_.SaltedMerkle.multiExtract enc d) code
    let U : Matrix (cohIn (extIn k X Y Y Z) × (Fin k → Database X Y))
        (cohIn (extIn k X Y Y Z) × (Fin k → Database X Y)) ℂ := E.coherent.U ()
    let K := (1 : Matrix (cohIn (extIn k X Y Y Z)) (cohIn (extIn k X Y Y Z)) ℂ) ⊗ₖ
      diagonal (fun D : Fin k → Database X Y ↦ if databasePopulation D ≤ s then (1 : ℂ) else 0)
    let R := fun c : Fin k × X ↦
      (1 : Matrix (cohIn (extIn k X Y Y Z)) (cohIn (extIn k X Y Y Z)) ℂ) ⊗ₖ
        CompressedReplay.invalid (Y := Y) c
    (selectedCharge (In := extIn k X Y Y Z) (D := QReg.of (Fin k → Database X Y))
      (fun p : Fin k ⊕ Unit ↦ p.isRight) (4 * s * oldChangingFraction (Fintype.card Y) s) * K -
      K * (∑ c, (U * R c - R c * U)ᴴ *
        (U * R c - R c * U)) * K).PosSemidef := by
  refine coherent_sum_commutator_gram_le
    ((compressedVCOracle k X Y).withExtract (_root_.SaltedMerkle.multiExtract enc d) code)
    (fun c : Fin k × X ↦ CompressedReplay.invalid (Y := Y) c)
    (diagonal fun D : Fin k → Database X Y ↦ if databasePopulation D ≤ s then 1 else 0)
    (fun p : Fin k ⊕ Unit ↦ p.isRight) _ ?_
  intro p
  cases p with
  | inl i =>
    have hc (c : Fin k × X) := CompressedReplay.invalid_commute_ordinary (Y := Y) i c
    let O : Matrix ((X × Y) × (Fin k → Database X Y))
        ((X × Y) × (Fin k → Database X Y)) ℂ := (compressedVCOracle k X Y).U i
    let Kp : Matrix ((X × Y) × (Fin k → Database X Y))
        ((X × Y) × (Fin k → Database X Y)) ℂ :=
      (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
        diagonal fun D : Fin k → Database X Y ↦ if databasePopulation D ≤ s then 1 else 0
    change ((0 : ℝ) • Kp - Kp * (∑ c : Fin k × X,
      (O * (1 ⊗ₖ CompressedReplay.invalid (Y := Y) c) -
        (1 ⊗ₖ CompressedReplay.invalid (Y := Y) c) * O)ᴴ *
      (O * (1 ⊗ₖ CompressedReplay.invalid (Y := Y) c) -
        (1 ⊗ₖ CompressedReplay.invalid (Y := Y) c) * O)) * Kp).PosSemidef
    simp only [O, hc, sub_self, conjTranspose_zero, Matrix.zero_mul, Finset.sum_const_zero,
      zero_smul, Matrix.mul_zero, sub_self]
    exact (PosSemidef.zero : (0 : Matrix ((X × Y) × (Fin k → Database X Y))
      ((X × Y) × (Fin k → Database X Y)) ℂ).PosSemidef)
  | inr u =>
    have hh := extractUnitary_invalid_gram_le enc d code s
    have he : (1 : Matrix (TpIC k Y × Z) (TpIC k Y × Z) ℂ) ⊗ₖ
        diagonal (fun D : Fin k → Database X Y ↦
          if databasePopulation D ≤ s then (1 : ℂ) else 0) =
        diagonal (fun a : (TpIC k Y × Z) × (Fin k → Database X Y) ↦
          if databasePopulation a.2 ≤ s then (1 : ℂ) else 0) := by
      rw [← diagonal_one, diagonal_kronecker_diagonal]
      simp only [one_mul]
    let V := extractUnitary (_root_.SaltedMerkle.multiExtract enc d) code
    let R := fun c : Fin k × X ↦
      (1 : Matrix (TpIC k Y × Z) (TpIC k Y × Z) ℂ) ⊗ₖ CompressedReplay.invalid (Y := Y) c
    let Kp := (1 : Matrix (TpIC k Y × Z) (TpIC k Y × Z) ℂ) ⊗ₖ
      diagonal fun D : Fin k → Database X Y ↦ if databasePopulation D ≤ s then (1 : ℂ) else 0
    change ((4 * s * oldChangingFraction (Fintype.card Y) s) • Kp -
      Kp * (∑ c, (V * R c - R c * V)ᴴ * (V * R c - R c * V)) * Kp).PosSemidef
    dsimp only [Kp]
    rw [he]
    exact hh

/-- One actual coherent call increases the square root of invalid potential by at most
`√(4 s a_N(s) · extraction mass)`, on positive inputs supported at population at most `s`.
The input need not be normalized; workspace entanglement is retained by the runtime lift. -/
theorem old_coherent_invalid_potential_step
    (enc : _root_.SaltedMerkle.Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ)
    (code : TpDCode k (DmOf (fun i ↦ 2 ^ d i) Msg
      (fun i ↦ _root_.SaltedMerkle.Td Y Salt (d i))) Z) (s : ℕ)
    {σ : Matrix (cohIn (extIn k X Y Y Z) × (Fin k → Database X Y))
      (cohIn (extIn k X Y Y Z) × (Fin k → Database X Y)) ℂ} (hσ : σ.PosSemidef)
    (hs : QuerySupportedOn (fun a : cohIn (extIn k X Y Y Z) × (Fin k → Database X Y) ↦
      databasePopulation a.2) (Set.Iic s) σ) :
    let E := (compressedVCOracle k X Y).withExtract (_root_.SaltedMerkle.multiExtract enc d) code
    let U : Matrix (cohIn (extIn k X Y Y Z) × (Fin k → Database X Y))
        (cohIn (extIn k X Y Y Z) × (Fin k → Database X Y)) ℂ := E.coherent.U ()
    QuantumRuntime.potential CompressedReplay.invalidStack (MatrixMap.conj U σ) ^ (2⁻¹ : ℝ) ≤
      QuantumRuntime.potential CompressedReplay.invalidStack σ ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal (4 * s * oldChangingFraction (Fintype.card Y) s) *
          E.selectedMass (fun p : Fin k ⊕ Unit ↦ p.isRight) σ) ^ (2⁻¹ : ℝ) := by
  classical
  let E := (compressedVCOracle k X Y).withExtract (_root_.SaltedMerkle.multiExtract enc d) code
  let U : Matrix (cohIn (extIn k X Y Y Z) × (Fin k → Database X Y))
      (cohIn (extIn k X Y Y Z) × (Fin k → Database X Y)) ℂ := E.coherent.U ()
  let K := diagonal (fun a : cohIn (extIn k X Y Y Z) × (Fin k → Database X Y) ↦
    if databasePopulation a.2 ≤ s then (1 : ℂ) else 0)
  let R := fun c : Fin k × X ↦
    (1 : Matrix (cohIn (extIn k X Y Y Z)) (cohIn (extIn k X Y Y Z)) ℂ) ⊗ₖ
      CompressedReplay.invalid (Y := Y) c
  let θ := 4 * s * oldChangingFraction (Fintype.card Y) s
  have hK : Kᴴ = K := by simp [K, diagonal_conjTranspose]
  have hcut : K * σ = σ := by
    ext a b
    simp only [K, diagonal_mul]
    by_cases ha : databasePopulation a.2 ≤ s
    · simp [ha]
    · have hz : σ a b = 0 := by
        by_contra hz
        exact ha (hs a b hz).1
      simp [hz]
  have he : (1 : Matrix (cohIn (extIn k X Y Y Z)) (cohIn (extIn k X Y Y Z)) ℂ) ⊗ₖ
      diagonal (fun D : Fin k → Database X Y ↦
        if databasePopulation D ≤ s then (1 : ℂ) else 0) = K := by
    rw [← diagonal_one, diagonal_kronecker_diagonal]
    simp only [one_mul]
    rfl
  have hg := old_coherent_invalid_gram_le enc d code s
  dsimp only at hg
  rw [he] at hg
  have hleak := sum_conj_trace_le_of_gram (fun c ↦ U * R c - R c * U) K
    (selectedCharge (In := extIn k X Y Y Z) (D := QReg.of (Fin k → Database X Y))
      (fun p : Fin k ⊕ Unit ↦ p.isRight) θ * K) hK hg hσ hcut
  rw [Matrix.mul_assoc, hcut] at hleak
  have hleak' := hleak.trans_eq (E.ofReal_trace_selectedCharge
    (fun p : Fin k ⊕ Unit ↦ p.isRight)
    (show 0 ≤ θ from mul_nonneg (by positivity) (le_min (by norm_num) (by positivity))) hσ)
  have hU : Uᴴ * U = 1 := mem_unitaryGroup_iff'.mp (E.coherent.unitary ())
  have htri := MatrixMap.rpow_inv_two_tsum_conj_unitary_le R U hU hσ
  have hneg (c : Fin k × X) : MatrixMap.conj (R c * U - U * R c) σ =
      MatrixMap.conj (U * R c - R c * U) σ := by
    have hh : R c * U - U * R c = -(U * R c - R c * U) := by abel
    rw [hh]
    simp only [MatrixMap.conj_apply, conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  simp only [hneg] at htri
  have hl := CompressedReplay.invalidStack_potential_eq
    (hσ.mul_mul_conjTranspose_same U)
  have hr := CompressedReplay.invalidStack_potential_eq hσ
  exact (congrArg (fun z : ℝ≥0∞ ↦ z ^ (2⁻¹ : ℝ)) hl).trans_le
    ((htri.trans (add_le_add le_rfl (ENNReal.rpow_le_rpow hleak' (by norm_num)))).trans_eq
      (congrArg (fun z : ℝ≥0∞ ↦ z ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal θ * E.selectedMass (fun p : Fin k ⊕ Unit ↦ p.isRight) σ) ^
          (2⁻¹ : ℝ)) hr.symm))

end oldCoherent
end Quantum.SaltedMerkle

namespace Quantum.SaltedMerkle
open EmulatedOracle QuantumRuntime
variable {X Y Msg Salt : Type} [Fintype X] [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [AddCommGroup Y] [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
  {Z : Type} [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

/-- The invalid norm after any old-oracle program is bounded by the sum of extraction
increments on its actual prefixes. This is FIX (28) before Cauchy–Schwarz; adaptive local
instruments, register-changing leaves, and subnormalized inputs are allowed. -/
theorem old_run_invalid_prefix_le
    (enc : _root_.SaltedMerkle.Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ)
    (code : TpDCode k (DmOf (fun i ↦ 2 ^ d i) Msg
      (fun i ↦ _root_.SaltedMerkle.Td Y Salt (d i))) Z)
    {L : LocalSig.{u, v}} (I : L.Interp) {W : QReg → Type w} {A : QReg}
    (x : QuantumComp L (cohSpec (extIn k X Y Y Z)) W A) (ρ : SubState A) :
    let E := (compressedVCOracle k X Y).withExtract (_root_.SaltedMerkle.multiExtract enc d) code
    (∑' p, potential CompressedReplay.invalidStack
      (E.coherent.toRuntime.jointPost I x ρ p).matrix) ^
      (2⁻¹ : ℝ) ≤
        ∑' j, (ENNReal.ofReal (4 * j * oldChangingFraction (Fintype.card Y) j) *
          E.coherent.toRuntime.queryWeight I
            (fun _ σ ↦ E.selectedMass (fun p : Fin k ⊕ Unit ↦ p.isRight) σ)
            x (ρ.matrix ⊗ₖ E.init.matrix) j) ^ (2⁻¹ : ℝ) := by
  let E := (compressedVCOracle k X Y).withExtract (_root_.SaltedMerkle.multiExtract enc d) code
  have hρ : (ρ.matrix ⊗ₖ E.init.matrix).PosSemidef := ρ.posSemidef.kronecker E.init.posSemidef
  have hpop : QuerySupportedOn
      (fun a : A × (Fin k → Database X Y) ↦ databasePopulation a.2) (Set.Iic 0)
      (ρ.matrix ⊗ₖ E.init.matrix) := by
    change QuerySupportedOn _ _
      (ρ.matrix ⊗ₖ (SubState.basis (fun _ : Fin k ↦ (Database.empty : Database X Y))).matrix)
    rw [SubState.matrix_basis]
    intro a b hab
    rw [kroneckerMap_apply] at hab
    have hs := right_ne_zero_of_mul hab
    rw [Matrix.single_apply] at hs
    split_ifs at hs with he
    · simp [← he.1, ← he.2, databasePopulation, Database.size_empty]
    · exact (hs rfl).elim
  have hh := E.run_potential_rpow_le databasePopulation I CompressedReplay.invalidStack
    (databasePopulation_withExtract_le (_root_.SaltedMerkle.multiExtract enc d) code)
    (fun n σ ↦ ENNReal.ofReal (4 * n * oldChangingFraction (Fintype.card Y) n) *
      E.selectedMass (fun p : Fin k ⊕ Unit ↦ p.isRight) σ)
    (fun n σ hσ hs ↦ old_coherent_invalid_potential_step enc d code n hσ hs) x 0 hρ hpop
  have hi : potential (D := E.S) CompressedReplay.invalidStack
      (ρ.matrix ⊗ₖ E.init.matrix) = 0 :=
    CompressedReplay.invalidStack_initial_potential_zero ρ.matrix
  simp only [hi, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), zero_add,
    E.coherent.toRuntime.queryWeight_const_mul] at hh
  simp only [QuantumRuntime.matrix_jointPost]
  convert hh using 1
  rfl

end Quantum.SaltedMerkle

namespace Quantum.SaltedMerkle

/-- The capped local coefficient is bounded by the uncapped FIX (28) coefficient.
The inequality also covers zero label cardinality, using extended-real division. -/
theorem oldChangingFraction_weight_le (N j : ℕ) :
    ENNReal.ofReal (4 * j * oldChangingFraction N j) ≤
      4 * (ENNReal.ofReal ((j : ℝ) * (2 * j - 1)) / N) := by
  have h : 4 * j * oldChangingFraction N j ≤
      4 * ((j : ℝ) * (2 * j - 1) / N) := by
    rcases j with _ | j
    · simp
    · have hh := mul_le_mul_of_nonneg_left
        (min_le_right (1 : ℝ) ((2 * (j + 1) - 1 : ℕ) / (N : ℝ)))
        (by positivity : 0 ≤ 4 * ((j + 1 : ℕ) : ℝ))
      unfold oldChangingFraction
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * (j + 1))] at hh ⊢
      push_cast at hh ⊢
      convert hh using 1
      ring
  refine (ENNReal.ofReal_le_ofReal h).trans ?_
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  simpa using mul_le_mul_right (ENNReal.ofReal_div_le (Nat.cast_nonneg N)
    (x := (j : ℝ) * (2 * j - 1))) 4

/-- The sum of actual local leakage amplitudes satisfies FIX (28). All masses are
extended nonnegative reals, including infinite values. -/
theorem oldLeakage_coefficient_sum_le (N u : ℕ) (mass : ℕ → ℝ≥0∞) :
    ∑ j ∈ Finset.range u,
        (ENNReal.ofReal (4 * j * oldChangingFraction N j) * mass j) ^ (2⁻¹ : ℝ) ≤
      2 * (ENNReal.ofReal (oldLeakagePolynomial u) / N *
        ∑ j ∈ Finset.range u, mass j) ^ (2⁻¹ : ℝ) := by
  have hfour : (4 : ℝ≥0∞) ^ (2⁻¹ : ℝ) = 2 := by
    have h := ENNReal.rpow_mul (2 : ℝ≥0∞) (2 : ℝ) (2⁻¹ : ℝ)
    norm_num [ENNReal.rpow_two] at h
    simpa only [one_div] using h.symm
  calc
    _ ≤ ∑ j ∈ Finset.range u,
        (4 * (ENNReal.ofReal ((j : ℝ) * (2 * j - 1)) / N * mass j)) ^ (2⁻¹ : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_assoc]
      exact ENNReal.rpow_le_rpow
        (mul_le_mul_left (oldChangingFraction_weight_le N j) (mass j)) (by norm_num)
    _ = 2 * ∑ j ∈ Finset.range u,
        (ENNReal.ofReal ((j : ℝ) * (2 * j - 1)) / N * mass j) ^ (2⁻¹ : ℝ) := by
      simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹),
        hfour, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_right (oldLeakage_sum_sqrt_le u N mass) 2
end Quantum.SaltedMerkle

namespace Quantum.SaltedMerkle
open EmulatedOracle QuantumRuntime
variable {X Y Msg Salt : Type} [Fintype X] [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [AddCommGroup Y] [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
  {Z : Type} [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

/-- The original post-adversary invalid norm satisfies FIX (28):
`2 √(e T(t) / N)`, with `e` the actual extraction query mass. The bound applies to every
coherent program within the total query budget, with adaptive local instruments and
register-changing leaves. Masses remain in `ℝ≥0∞` throughout. -/
theorem old_run_invalid_le
    (enc : _root_.SaltedMerkle.Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ)
    (code : TpDCode k (DmOf (fun i ↦ 2 ^ d i) Msg
      (fun i ↦ _root_.SaltedMerkle.Td Y Salt (d i))) Z)
    {L : LocalSig.{u, v}} (I : L.Interp) {W : QReg → Type w} {A : QReg}
    (x : QuantumComp L (cohSpec (extIn k X Y Y Z)) W A) (ρ : SubState A)
    (t : ℕ) (hx : x.IsQueryBound fun _ ↦ t) :
    let E := (compressedVCOracle k X Y).withExtract (_root_.SaltedMerkle.multiExtract enc d) code
    (∑' p, potential CompressedReplay.invalidStack
      (E.coherent.toRuntime.jointPost I x ρ p).matrix) ^ (2⁻¹ : ℝ) ≤
        2 * (ENNReal.ofReal (oldLeakagePolynomial t) / Fintype.card Y *
          E.totalMass I x (ρ.matrix ⊗ₖ E.init.matrix) (.inr ())) ^ (2⁻¹ : ℝ) := by
  classical
  let E := (compressedVCOracle k X Y).withExtract (_root_.SaltedMerkle.multiExtract enc d) code
  let mass := fun j ↦ E.coherent.toRuntime.queryWeight I
    (fun _ σ ↦ E.selectedMass (fun p : Fin k ⊕ Unit ↦ p.isRight) σ)
    x (ρ.matrix ⊗ₖ E.init.matrix) j
  have hz : ∀ j ∉ Finset.range t, mass j = 0 := by
    intro j hj
    exact E.coherent.toRuntime.queryWeight_eq_zero_of_isQueryBound I hx Finset.univ
      (by simp) (by simpa using hj) _
  have hm : ∑ j ∈ Finset.range t, mass j ≤ E.totalMass I x
      (ρ.matrix ⊗ₖ E.init.matrix) (.inr ()) := by
    have hh := E.tsum_queryWeight_selectedMass I (fun p : Fin k ⊕ Unit ↦ p.isRight)
      x (ρ.matrix ⊗ₖ E.init.matrix)
    rw [tsum_eq_sum hz] at hh
    simpa [selectedTotalMass, Fintype.sum_sum_type] using hh.le
  have hh := old_run_invalid_prefix_le enc d code I x ρ
  have htail : ∀ j ∉ Finset.range t,
      (ENNReal.ofReal (4 * j * oldChangingFraction (Fintype.card Y) j) * mass j) ^
        (2⁻¹ : ℝ) = 0 := fun j hj ↦ by
    rw [hz j hj, mul_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
  change _ ≤ ∑' j, (ENNReal.ofReal (4 * j * oldChangingFraction (Fintype.card Y) j) *
    mass j) ^ (2⁻¹ : ℝ) at hh
  rw [tsum_eq_sum htail] at hh
  exact hh.trans ((oldLeakage_coefficient_sum_le (Fintype.card Y) t mass).trans
    (mul_le_mul_right (ENNReal.rpow_le_rpow (mul_le_mul_right hm _)
      (by norm_num)) 2))
end Quantum.SaltedMerkle

namespace Quantum.SaltedMerkle
open _root_.SaltedMerkle
variable {X Y Msg Salt : Type} [Fintype X] [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [Nonempty Y] [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
  (enc : Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ)
/-- Extraction on one position batch commutes with either conjugated checker on a disjoint
batch. Duplicate-index tuples are included because their extraction response is constant. -/
theorem batchResponse_commute (hk : 1 ≤ k) (idx : Fin k → Fin k) (cm : Fin k → Y)
    (W B : Finset (Fin k)) (hWB : Disjoint W B)
    (p : Fin k → Database X Y → Prop) [∀ i D, Decidable (p i D)] :
    let Z := TpDCode.ConcatReg k (DmOf (fun i ↦ 2 ^ d i) Msg (fun i ↦ Td Y Salt (d i)))
    let β := TpDCode.partResponse (multiExtract enc d) B (TpIC.full hk idx cm)
    let K := compressDatabases k X Y * diagonal
      (fun D : Fin k → Database X Y ↦ if ∀ i ∈ W, p i (D (idx i)) then (1 : ℂ) else 0) *
        compressDatabases k X Y
    Commute (labelControlled (fun a : (Fin k → Database X Y) × Z ↦ β a.1)
      (fun r ↦ (1 : Matrix (Fin k → Database X Y) _ ℂ) ⊗ₖ xorShift Z r)) (K ⊗ₖ 1) := by
  classical
  dsimp only
  apply response_commute_of_support
  intro D D' hK
  by_cases hi : Function.Injective idx
  · apply partResponse_full_eq enc d
    intro i hiB
    have hs := conjugated_batch_support p idx W (compressAll X Y)
      (compressAll_mul_self X Y) D D'
    refine hs ?_ (idx i) ?_
    · convert hK using 1
      simp only [compressDatabases, Matrix.mul_apply, diagonal_apply]
      congr! 6
    · intro hj
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hj
      exact Finset.disjoint_left.mp hWB ((hi he) ▸ hj) hiB
  · exact partResponse_full_eq_of_not_injective enc d hk idx cm B D D' hi
end Quantum.SaltedMerkle
