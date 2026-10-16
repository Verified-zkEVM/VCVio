/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.HadamardTruncation
public import VCVio.Quantum.VC.HadamardPopulation

/-!
# P2 for the empty-sector extension

The population invariant permits truncation at `t + 1`. The `comSplit` decomposition and
`instability_extractLabel_le` compare each extractor-controlled block with the online partition.
The repair note's coefficient `24` improves the paper's coefficient `80`.
-/

public section

open Matrix OracleSpec
open scoped Kronecker ENNReal ComplexOrder Matrix.Norms.L2Operator

universe v w

namespace Quantum

section size

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  (V : Matrix Y Y ℂ)

/-- The one-database extension raises population by at most one. -/
theorem size_le_of_extendedCompressedOracle_apply_ne_zero
    {p q : (X × Y) × Database X Y} (h : extendedCompressedOracle V p q ≠ 0) :
    p.2.size ≤ q.2.size + 1 := by
  obtain ⟨⟨x, r⟩, d⟩ := p
  obtain ⟨⟨z, s⟩, e⟩ := q
  rw [extendedCompressedOracle_apply] at h
  split_ifs at h with hc
  · have he : d = Function.update e x (d x) := by
      funext j
      by_cases hj : j = x
      · subst j; simp
      · rw [Function.update_of_ne hj]
        exact hc.2 j hj
    change d.size ≤ e.size + 1
    rw [he]
    exact Database.size_update_le _ _ _
  · exact False.elim (h rfl)

/-- The compressed oracle raises the number of nonempty cells by at most one:
`cO P_size^(t) = P_size^(t+1) cO P_size^(t)`. -/
theorem extendedCompressedOracle_mul_sizeProjector (t : ℕ) :
    extendedCompressedOracle (X := X) V * sizeProjector X Y t =
      sizeProjector X Y (t + 1) * extendedCompressedOracle (X := X) V * sizeProjector X Y t := by
  ext a b
  simp only [sizeProjector, mul_diagonal, diagonal_mul]
  by_cases hb : b.2.size ≤ t
  · by_cases h : extendedCompressedOracle (X := X) V a b = 0
    · simp [h]
    · have ha : a.2.size ≤ t + 1 :=
        (size_le_of_extendedCompressedOracle_apply_ne_zero V h).trans (Nat.add_le_add_right hb 1)
      simp [ha, hb]
  · simp [hb]

variable {E : Type} [Fintype E] [DecidableEq E]

/-- **The truncation step on one block.** If `L` commutes with `P_size^(t) ⊗ 1`, then on the
range of `P_size^(t) ⊗ 1` the commutator of `L` with `cO ⊗ 1` is its commutator with the truncated
oracle `O^(t+1) ⊗ 1`. -/
theorem extended_commutator_mul_sizeProjector_kronecker_eq (t : ℕ)
    (L : Matrix (((X × Y) × Database X Y) × E) (((X × Y) × Database X Y) × E) ℂ)
    (hL : L * (sizeProjector X Y t ⊗ₖ (1 : Matrix E E ℂ)) =
      (sizeProjector X Y t ⊗ₖ (1 : Matrix E E ℂ)) * L) :
    (L * (extendedCompressedOracle (X := X) V ⊗ₖ (1 : Matrix E E ℂ)) -
        (extendedCompressedOracle (X := X) V ⊗ₖ (1 : Matrix E E ℂ)) * L) *
        (sizeProjector X Y t ⊗ₖ (1 : Matrix E E ℂ)) =
      (L * (truncatedExtendedOracle (X := X) V (t + 1) ⊗ₖ (1 : Matrix E E ℂ)) -
        (truncatedExtendedOracle (X := X) V (t + 1) ⊗ₖ (1 : Matrix E E ℂ)) * L) *
        (sizeProjector X Y t ⊗ₖ (1 : Matrix E E ℂ)) := by
  have hT : (truncatedExtendedOracle (X := X) V (t + 1) ⊗ₖ (1 : Matrix E E ℂ)) *
      (sizeProjector X Y t ⊗ₖ (1 : Matrix E E ℂ)) =
      (extendedCompressedOracle (X := X) V ⊗ₖ (1 : Matrix E E ℂ)) *
        (sizeProjector X Y t ⊗ₖ (1 : Matrix E E ℂ)) := by
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, truncatedExtendedOracle, Matrix.mul_assoc _ _
      (sizeProjector X Y t), sizeProjector_succ_mul_sizeProjector,
      ← extendedCompressedOracle_mul_sizeProjector V]
  have e : ∀ M, (L * M - M * L) * (sizeProjector X Y t ⊗ₖ (1 : Matrix E E ℂ)) =
      L * (M * (sizeProjector X Y t ⊗ₖ (1 : Matrix E E ℂ))) -
        M * (sizeProjector X Y t ⊗ₖ (1 : Matrix E E ℂ)) * L := fun M ↦ by
    rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc M, hL, ← Matrix.mul_assoc M]
  rw [e, e, hT]

end size

section defectBlocks

variable {X Y Tc Z Env ι : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [Fintype Tc] [DecidableEq Tc] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  [Fintype Env] [DecidableEq Env] [Fintype ι] [DecidableEq ι]
  (V₀ : Matrix Y Y ℂ)

/-- **The commutation defect on the range of `|D_i| ≤ t` is block diagonal.** Let `V` add
`f tc s` to the extraction register, placed on the output of a P2 adversary as in
`Quantum.comDefect`, and let the compressed oracle act on the query register and the table `D_i`.
On the range of the projector onto `|D_i| ≤ t`, their commutator is the block-diagonal operator,
for `Quantum.comSplit i`, whose block at `c = (tc, (D_j)_{j ≠ i})` is the commutator of the
purified measurement of `D_i ↦ f tc D` with the truncated oracle `O^(t+1) ⊗ 1`. -/
theorem extended_commutator_onFactor_mul_diagonal_eq (i : ι) (f : Tc → (ι → Database X Y) → Z)
    {V : Matrix ((Tc × Z) × (ι → Database X Y)) ((Tc × Z) × (ι → Database X Y)) ℂ}
    (hV : ∀ tc tc' z z' s s', V ((tc, z), s) ((tc', z'), s') =
      if tc = tc' ∧ z = z' + f tc' s' ∧ s = s' then 1 else 0) (t : ℕ) :
    (onFactor (slotSnd₃ (X × Y) (Tc × Z) Env (ι → Database X Y)) V *
          onFactor (slotFst₃ (X × Y) (Tc × Z) Env (ι → Database X Y))
            (onFactor (splitAt (X × Y) (Database X Y) i) (extendedCompressedOracle (X := X) V₀)) -
        onFactor (slotFst₃ (X × Y) (Tc × Z) Env (ι → Database X Y))
            (onFactor (splitAt (X × Y) (Database X Y) i) (extendedCompressedOracle (X := X) V₀)) *
          onFactor (slotSnd₃ (X × Y) (Tc × Z) Env (ι → Database X Y)) V) *
        diagonal (fun m : (((X × Y) × (Tc × Z)) × Env) × (ι → Database X Y) ↦
          if (m.2 i).size ≤ t then (1 : ℂ) else 0) =
      (blockDiagonal fun c : Tc × ({j // j ≠ i} → Database X Y) ↦
          labelControlled (fun a : ((X × Y) × Database X Y) × (Z × Env) ↦
              f c.1 ((Equiv.funSplitAt i (Database X Y)).symm (a.1.2, c.2)))
            (fun l ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ
              (xorShift Z l ⊗ₖ (1 : Matrix Env Env ℂ))) *
            (truncatedExtendedOracle (X := X) V₀ (t + 1) ⊗ₖ (1 : Matrix (Z × Env) (Z × Env) ℂ)) -
          (truncatedExtendedOracle (X := X) V₀ (t + 1) ⊗ₖ (1 : Matrix (Z × Env) (Z × Env) ℂ)) *
            labelControlled (fun a : ((X × Y) × Database X Y) × (Z × Env) ↦
              f c.1 ((Equiv.funSplitAt i (Database X Y)).symm (a.1.2, c.2)))
            (fun l ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ
              (xorShift Z l ⊗ₖ (1 : Matrix Env Env ℂ)))).submatrix (comSplit i) (comSplit i) *
        diagonal (fun m : (((X × Y) × (Tc × Z)) × Env) × (ι → Database X Y) ↦
          if (m.2 i).size ≤ t then (1 : ℂ) else 0) := by
  rw [onFactor_slotSnd₃_eq_blockDiagonal i f hV, onFactor_slotFst₃_onFactor_splitAt i,
    diagonal_apply_eq_blockDiagonal i fun D : Database X Y ↦ if D.size ≤ t then 1 else 0]
  have hsub : ∀ A B : Matrix ((((X × Y) × Database X Y) × (Z × Env)) ×
      (Tc × ({j // j ≠ i} → Database X Y))) ((((X × Y) × Database X Y) × (Z × Env)) ×
      (Tc × ({j // j ≠ i} → Database X Y))) ℂ,
      A.submatrix (comSplit (XY := X × Y) (Tc := Tc) (Z := Z) (Env := Env) i) (comSplit i) -
          B.submatrix (comSplit (XY := X × Y) (Tc := Tc) (Z := Z) (Env := Env) i) (comSplit i) =
        (A - B).submatrix (comSplit (XY := X × Y) (Tc := Tc) (Z := Z) (Env := Env) i)
          (comSplit i) := fun _ _ ↦ rfl
  rw [submatrix_mul_equiv, submatrix_mul_equiv, hsub, submatrix_mul_equiv, submatrix_mul_equiv,
    ← blockDiagonal_mul, ← blockDiagonal_mul, ← blockDiagonal_sub, ← blockDiagonal_mul,
    ← blockDiagonal_mul]
  refine congrArg (fun F ↦ (blockDiagonal F).submatrix _ _) (funext fun c ↦ ?_)
  have h := extended_commutator_mul_sizeProjector_kronecker_eq V₀ t _
    (labelControlled_mul_sizeProjector_kronecker
      (fun D ↦ f c.1 ((Equiv.funSplitAt i (Database X Y)).symm (D, c.2)))
      (fun l ↦ xorShift Z l ⊗ₖ (1 : Matrix Env Env ℂ)) t)
  rw [sizeProjector] at h
  rw [Pi.sub_apply]
  exact h

end defectBlocks

section lemma92

open EmulatedOracle (cohSpec)

variable {k : ℕ} {X Y Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  (V : Matrix Y Y ℂ) (hV : V ∈ unitaryGroup Y ℂ)
  {Dm : Fin k → Type} (ME : MultiExtractor k Cm Dm (Fin k → Database X Y))
  (code : TpDCode k Dm Z)

/-- **Lemma 9.2 of ePrint 2025/2166 with the constant `24`** (pp. 58–59): the k compressed
oracles satisfy the commutation half of P2 with
`κcom t = 24 · sup_{j', tic, (D_j)_j} I(P_online^{tic, (D_j)_{j ≠ j'}}, t + 1)`.

On the joint state after `t` queries the database `D_i` has at most `t` nonempty cells
(`Quantum.querySupportedOn_jointPost₂_extendedVCOracle_withExtract`). There the commutation
defect is block diagonal for `Quantum.comSplit`, and each block is the commutator of a purified
measurement with `O^(t+1) ⊗ 1`, bounded by the repair note with the constant `24`. -/
theorem comBound_extendedVCOracle [UniformAnswerMeasure (X →ₒ Y)]
    (hY : ∀ y : Y, y + y = 0) (hVV : V * V = 1) :
    ComBound.{v, w} (extendedVCOracle k X Y V hV) ME code (comBoundError ME) := by
  intro i t A Env α x ρ hx
  set S := ⨆ (j' : Fin k) (tic : TpIC k Cm) (Dfix : Fin k → Database X Y),
    Database.instability (onlineLabel ME ![tic] Dfix j') (t + 1) with hSdef
  have hS : S ≠ ⊤ := iSup_instability_onlineLabel_ne_top ME (t + 1)
  -- the blocks
  let f : TpIC k Cm → (Fin k → Database X Y) → Z := fun tc s ↦ code.enc ⟨tc.1, ME.extract tc s⟩
  let lab : TpIC k Cm × ({j // j ≠ i} → Database X Y) → Database X Y → Z :=
    fun c D ↦ f c.1 ((Equiv.funSplitAt i (Database X Y)).symm (D, c.2))
  let Lb : TpIC k Cm × ({j // j ≠ i} → Database X Y) →
      Matrix (((X × Y) × Database X Y) × (Z × Env)) (((X × Y) × Database X Y) × (Z × Env)) ℂ :=
    fun c ↦ labelControlled (fun a ↦ lab c a.1.2) fun l ↦
      (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ
        (xorShift Z l ⊗ₖ (1 : Matrix Env Env ℂ))
  let T := truncatedExtendedOracle (X := X) V (t + 1) ⊗ₖ (1 : Matrix (Z × Env) (Z × Env) ℂ)
  let e := comSplit (XY := X × Y) (Tc := TpIC k Cm) (Z := Z) (Env := Env) (DB := Database X Y) i
  let Psz : Matrix (ComOut k X Y Cm Z Env × (extendedVCOracle k X Y V hV).S)
      (ComOut k X Y Cm Z Env × (extendedVCOracle k X Y V hV).S) ℂ :=
    diagonal fun m ↦ if (m.2 i).size ≤ t then 1 else 0
  -- on the range of `Psz`, the defect is block diagonal
  have hC : comDefect (extendedVCOracle k X Y V hV) ME code Env i * Psz =
      ((blockDiagonal fun c ↦ Lb c * T - T * Lb c).submatrix e e :
        Matrix (ComOut k X Y Cm Z Env × (extendedVCOracle k X Y V hV).S)
          (ComOut k X Y Cm Z Env × (extendedVCOracle k X Y V hV).S) ℂ) * Psz := by
    unfold comDefect
    rw [extendedVCOracle_U, extendedVCPort_eq_onFactor]
    exact extended_commutator_onFactor_mul_diagonal_eq V i f (extractUnitary_apply ME code) t
  -- each block, by Corollary 5.6 with the constant `24`
  have hb : ∀ c, ‖Lb c * T - T * Lb c‖ ^ 2 ≤ 24 * S.toReal := fun c ↦ by
    have h := norm_auxiliaryCommutator_truncatedExtendedOracle_sq_le hY hV hVV (lab c) (t + 1)
      (fun l ↦ xorShift Z l ⊗ₖ (1 : Matrix Env Env ℂ))
      fun l ↦ kronecker_mem_unitary (xorShift_mem_unitaryGroup l) (one_mem _)
    have h' := ENNReal.toReal_mono hS (instability_extractLabel_le ME code i c (t + 1))
    exact h.trans (by gcongr)
  -- one outcome
  let σf : α → Matrix (ComOut k X Y Cm Z Env × (extendedVCOracle k X Y V hV).S)
      (ComOut k X Y Cm Z Env × (extendedVCOracle k X Y V hV).S) ℂ := fun a ↦
    (((extendedVCOracle k X Y V hV).withExtract ME code).coherent.toRuntime.jointPost₂
      .instruments x ρ a).matrix
  have hleaf : ∀ a, ENNReal.ofReal (comDefect (extendedVCOracle k X Y V hV) ME code Env i *
      σf a * (comDefect (extendedVCOracle k X Y V hV) ME code Env i)ᴴ).trace.re
      ≤ ENNReal.ofReal (24 * S.toReal) * ENNReal.ofReal (σf a).trace.re := fun a ↦ by
    have hsupp : QuerySupportedOn
        (fun m : ComOut k X Y Cm Z Env × (extendedVCOracle k X Y V hV).S ↦ (m.2 i).size)
        (Set.Iic t) (σf a) :=
      querySupportedOn_jointPost₂_extendedVCOracle_withExtract V hV ME code i x hx ρ a
    have hσ : MatrixMap.conj Psz (σf a) = σf a :=
      QuerySupportedOn.conj_diagonal_eq_self (fun m hm ↦ by simp [Set.mem_Iic.mp hm]) hsupp
    have hpsd : (σf a).PosSemidef := SubState.posSemidef _
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal
      (re_trace_mul_mul_conjTranspose_le_of_blockDiagonal
        (N := ComOut k X Y Cm Z Env × (extendedVCOracle k X Y V hV).S) e _ (by positivity) hb hC hσ
        hpsd)
  calc comError (extendedVCOracle k X Y V hV) ME code i x ρ
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


end lemma92

end Quantum
