/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.Online

/-!
# Online indistinguishability from recording commutators

The private recording swap is exact on extraction and recording. Ordinary-query defects and
summed checked-read branch Grams give both square-root comparisons of Chiesa, Di, Hu and Zheng,
ePrint 2025/2166, Definition 7.3, P5. Source mass counts each checked read once.
-/

public section

open Matrix
open scoped Kronecker ENNReal ComplexOrder Matrix.Norms.L2Operator
namespace Quantum

section readRecording
variable {S R A : Type*} [DecidableEq R]

/-- The retained-answer commutator with a private controlled permutation. -/
@[expose]
noncomputable def readPermutationDefect (e : S → Equiv.Perm R)
    (M : A → Matrix S S ℂ) : Matrix ((S × R) × A) (S × R) ℂ :=
  fun a b ↦ M a.2 a.1.1 b.1 *
    ((if a.1.2 = e a.1.1 b.2 then 1 else 0) - if a.1.2 = e b.1 b.2 then 1 else 0)
end readRecording

section readSectors
variable {k : ℕ} {Cm Cell S A : Type*} {Dm : Fin k → Type*}
  [Fintype Cm] [DecidableEq Cm] [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
  [Fintype Cell] [DecidableEq Cell] [Fintype S] [DecidableEq S]
  [Fintype A]

/-- Orthogonal occupied-key sectors bound the whole retained-answer stack by their maximum.
No measurement of the coherent recording register is performed. -/
theorem l2_opNorm_readRecordingDefect_le
    (ME : MultiExtractor k Cm Dm S) (M : A → Matrix S S ℂ)
    (g : S → ℕ) (bot : Cell) (t : ℕ) (c : ℝ) (hc : 0 ≤ c) (s₀ : S)
    (hlocal : ∀ keys : Finset (TpIC k Cm),
      ‖readPermutationDefect
        (fun s ↦ RecReg.swapEquiv (RecReg.restrictedExtractor ME keys s₀)
          (fun q ↦ ME.extract q.1 s)) M *
        diagonal (fun a : S × RecReg k Cm Dm Cell ↦
          if g a.1 + keys.card ≤ t then (1 : ℂ) else 0)‖ ≤ c) :
    ‖readPermutationDefect (RecReg.swapEquiv ME) M *
      diagonal (fun a : S × RecReg k Cm Dm Cell ↦
        if g a.1 + RecReg.population bot a.2 ≤ t then (1 : ℂ) else 0)‖ ≤ c := by
  classical
  let β : S × RecReg k Cm Dm Cell → Finset (TpIC k Cm) :=
    fun a ↦ RecReg.occupied bot a.2
  refine l2_opNorm_le_of_submatrix_le (fun a ↦ β a.1) β ?_ hc ?_
  · intro a b hab
    rw [mul_diagonal] at hab
    have hd := left_ne_zero_of_mul hab
    unfold readPermutationDefect at hd
    have hn := right_ne_zero_of_mul hd
    split_ifs at hn with h₁ h₂ h₂
    · simp at hn
    · change RecReg.occupied bot a.1.2 = RecReg.occupied bot b.2
      rw [h₁]
      exact RecReg.occupied_swap ME a.1.1 bot b.2
    · change RecReg.occupied bot a.1.2 = RecReg.occupied bot b.2
      rw [h₂]
      exact RecReg.occupied_swap ME b.1 bot b.2
    · simp at hn
  · intro keys
    let K := readPermutationDefect
      (fun s ↦ RecReg.swapEquiv (RecReg.restrictedExtractor ME keys s₀)
        (fun q ↦ ME.extract q.1 s)) M *
      diagonal (fun a : S × RecReg k Cm Dm Cell ↦
        if g a.1 + keys.card ≤ t then (1 : ℂ) else 0)
    have he : (readPermutationDefect (RecReg.swapEquiv ME) M *
        diagonal (fun a : S × RecReg k Cm Dm Cell ↦
          if g a.1 + RecReg.population bot a.2 ≤ t then (1 : ℂ) else 0)).submatrix
        (Subtype.val : {a : (S × RecReg k Cm Dm Cell) × A // β a.1 = keys} → _)
        (Subtype.val : {a // β a = keys} → _) =
        K.submatrix (Subtype.val : {a : (S × RecReg k Cm Dm Cell) × A // β a.1 = keys} → _)
          (Subtype.val : {a // β a = keys} → _) := by
      ext a b
      have hb : RecReg.occupied bot b.1.2 = keys := b.2
      have hs (s : S) := RecReg.swap_restrictedExtractor ME keys s₀ s bot b.1.2
        (Finset.Subset.trans (Finset.Subset.refl _) (by rw [hb]))
      simp only [submatrix_apply, mul_diagonal, readPermutationDefect, RecReg.swapEquiv,
        Equiv.coe_fn_mk, hs, RecReg.population, hb, K]
      rfl
    rw [he]
    exact (l2_opNorm_submatrix_le_of_injective K Subtype.val_injective
      Subtype.val_injective).trans (hlocal keys)
end readSectors

section fixedRead
variable {X Y : Type} {R ι : Type*} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Fintype R] [DecidableEq R]

/-- Fixing a classical address in the retained-answer stack introduces no answer-count factor. -/
theorem l2_opNorm_fixedReadPermutationDefect_sq_le
    [OracleSpec.UniformAnswerMeasure (X →ₒ Y)]
    (π : Database X Y → ι) (e : ι → Equiv.Perm R) (x : X) (p : ℕ) :
    ‖readPermutationDefect (fun D ↦ e (π D)) (checkedReadProjector x) *
      diagonal (fun a : Database X Y × R ↦ if a.1.size ≤ p then (1 : ℂ) else 0)‖ ^ 2 ≤
      24 * (Database.instability π (p + 1)).toReal := by
  classical
  let f : Database X Y × R → (X × Database X Y) × R := fun a ↦ ((x, a.1), a.2)
  let f' : (Database X Y × R) × Option Y → ((X × Database X Y) × R) × Option Y :=
    fun a ↦ (f a.1, a.2)
  have hf : Function.Injective f := by
    intro a b h
    change ((x, a.1), a.2) = ((x, b.1), b.2) at h
    exact Prod.ext (congrArg (fun a ↦ a.1.2) h)
      (congrArg (fun z : (X × Database X Y) × R ↦ z.2) h)
  have hf' : Function.Injective f' := by
    intro a b h
    change (f a.1, a.2) = (f b.1, b.2) at h
    exact Prod.ext (hf (congrArg Prod.fst h))
      (congrArg (fun z : ((X × Database X Y) × R) × Option Y ↦ z.2) h)
  let K := MatrixMap.stinespring (checkedReadDefect π (fun l ↦ basisMatrix (e l))) *
    diagonal (fun a : (X × Database X Y) × R ↦ if a.1.2.size ≤ p then (1 : ℂ) else 0)
  have he : readPermutationDefect (fun D ↦ e (π D)) (checkedReadProjector x) *
      diagonal (fun a : Database X Y × R ↦ if a.1.size ≤ p then (1 : ℂ) else 0) =
        -(K.submatrix f' f) := by
    ext a b
    simp only [mul_diagonal, readPermutationDefect, Matrix.neg_apply, submatrix_apply,
      K, MatrixMap.stinespring_apply, f', f, checkedReadDefect_apply,
      selectedCheckedReadProjector_apply, ite_true, basisMatrix_apply]
    ring
  rw [he, norm_neg]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (l2_opNorm_submatrix_le_of_injective K hf' hf) 2).trans
      (l2_opNorm_checkedReadDefectStack_sq_le π (fun l ↦ basisMatrix (e l))
        (fun l ↦ basisMatrix_perm_mem_unitaryGroup (e l)) p)
end fixedRead

section readFamily
variable {X Y R A : Type} {k : ℕ} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype R] [DecidableEq R] [Fintype A]

/-- Unchanged databases form orthogonal sectors for the complete answer stack. -/
theorem l2_opNorm_familyReadDefect_source_le (i : Fin k)
    (M : A → Matrix (Database X Y) (Database X Y) ℂ)
    (F : A → Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ)
    (hM : ∀ a D D', F a D D' =
      if (fun j : {j // j ≠ i} ↦ D j.1) = (fun j ↦ D' j.1) then M a (D i) (D' i) else 0)
    (e : (Fin k → Database X Y) → Equiv.Perm R) (n t : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hlocal : ∀ Dfix : Fin k → Database X Y,
      ‖readPermutationDefect (fun D ↦ e (Function.update Dfix i D)) M *
        diagonal (fun a : Database X Y × R ↦
          if a.1.size + n ≤ t then (1 : ℂ) else 0)‖ ≤ c) :
    ‖readPermutationDefect e F * diagonal (fun a : (Fin k → Database X Y) × R ↦
      if (∑ j, (a.1 j).size) + n ≤ t then (1 : ℂ) else 0)‖ ≤ c := by
  classical
  let β : (Fin k → Database X Y) × R → ({j // j ≠ i} → Database X Y) :=
    fun a j ↦ a.1 j.1
  refine l2_opNorm_le_of_submatrix_le (fun a ↦ β a.1) β ?_ hc ?_
  · intro a b hab
    rw [mul_diagonal] at hab
    have hm := left_ne_zero_of_mul (left_ne_zero_of_mul hab)
    change F a.2 a.1.1 b.1 ≠ 0 at hm
    rw [hM] at hm
    split_ifs at hm with h
    · exact h
    · exact (hm rfl).elim
  · intro rest
    let Fiber := {a : (Fin k → Database X Y) × R // β a = rest}
    let Rows := {a : ((Fin k → Database X Y) × R) × A // β a.1 = rest}
    let fix : Fin k → Database X Y := (Equiv.funSplitAt i (Database X Y)).symm
      (Database.empty, rest)
    let f : Fiber → Database X Y × R := fun a ↦ (a.1.1 i, a.1.2)
    let f' : Rows → (Database X Y × R) × A := fun a ↦ (f ⟨a.1.1, a.2⟩, a.1.2)
    have hd (a : Fiber) : Function.update fix i (a.1.1 i) = a.1.1 := by
      funext j
      by_cases hj : j = i
      · subst j
        simp
      · rw [Function.update_of_ne hj]
        have ha := congrFun a.2 ⟨j, hj⟩
        simpa only [fix, Equiv.funSplitAt_symm_apply, dite_eq_right hj] using ha.symm
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have h₁ := congrArg Prod.fst hab
      have h₂ := congrArg Prod.snd hab
      dsimp only [f] at h₁ h₂
      exact Prod.ext (by rw [← hd a, ← hd b, h₁]) h₂
    have hf' : Function.Injective f' := by
      intro a b hab
      change (f ⟨a.1.1, a.2⟩, a.1.2) = (f ⟨b.1.1, b.2⟩, b.1.2) at hab
      apply Subtype.ext
      exact Prod.ext (congrArg Subtype.val (hf (congrArg Prod.fst hab)))
        (congrArg (fun z : (Database X Y × R) × A ↦ z.2) hab)
    let K := readPermutationDefect (fun D ↦ e (Function.update fix i D)) M *
      diagonal (fun a : Database X Y × R ↦ if a.1.size + n ≤ t then (1 : ℂ) else 0)
    let P0 : Matrix Fiber Fiber ℂ :=
      diagonal (fun a ↦ if (∑ j, (a.1.1 j).size) + n ≤ t then 1 else 0)
    have he : (readPermutationDefect e F *
        diagonal (fun a : (Fin k → Database X Y) × R ↦
          if (∑ j, (a.1 j).size) + n ≤ t then (1 : ℂ) else 0)).submatrix
        (Subtype.val : Rows → _) (Subtype.val : Fiber → _) = K.submatrix f' f * P0 := by
      ext a b
      have hr : β a.1.1 = β b.1 := a.2.trans b.2.symm
      have hda := hd ⟨a.1.1, a.2⟩
      have hs : (b.1.1 i).size ≤ ∑ j, (b.1.1 j).size :=
        Finset.single_le_sum (f := fun j ↦ (b.1.1 j).size)
          (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      simp only [submatrix_apply, mul_diagonal, readPermutationDefect, hM,
        show (fun j : {j // j ≠ i} ↦ a.1.1.1 j.1) = (fun j ↦ b.1.1 j.1) from hr,
        ite_true, K, P0, f', f, hd, hda]
      by_cases hg : (∑ j, (b.1.1 j).size) + n ≤ t
      · have hi : (b.1.1 i).size + n ≤ t := by omega
        simp [hg, hi]
      · simp [hg]
    rw [he]
    apply le_trans ?_ (hlocal fix)
    apply l2_opNorm_submatrix_mul_mask_le K f' f hf' hf
    intro a
    split_ifs <;> norm_num
end readFamily

section compressedReadSectors
variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

private theorem recordingReadProjector_split (i : Fin k) (x : X) (a : Option Y)
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

variable {Cm Cell : Type} {Dm : Fin k → Type}
  [OracleSpec.UniformAnswerMeasure (X →ₒ Y)] [Fintype Cm] [DecidableEq Cm]
  [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)] [Fintype Cell] [DecidableEq Cell]

/-- The recording read's complete answer stack obeys the occupied-key instability rate.
The source mask is the joint database and recording population. -/
theorem l2_opNorm_compressed_readRecordingDefect_source_sq_le
    (ME : MultiExtractor k Cm Dm (Fin k → Database X Y)) (bot : Cell)
    (i : Fin k) (x : X) (t : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hi : ∀ keys : Finset (TpIC k Cm), 1 ≤ keys.card → keys.card ≤ t →
      ∀ Dfix : Fin k → Database X Y,
        24 * (Database.instability
          (fun D ↦ fun q : keys ↦ ME.extract q.1 (Function.update Dfix i D))
          (t - keys.card + 1)).toReal ≤ r) :
    ‖readPermutationDefect (RecReg.swapEquiv ME) (compressedReadProjector k X Y (i, x)) *
      diagonal (fun a : (Fin k → Database X Y) × RecReg k Cm Dm Cell ↦
        if (∑ j, (a.1 j).size) + RecReg.population bot a.2 ≤ t
        then (1 : ℂ) else 0)‖ ^ 2 ≤ r := by
  refine le_trans ?_ (le_of_eq (Real.sq_sqrt hr))
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg r)).mpr
  apply l2_opNorm_readRecordingDefect_le ME _ (fun D ↦ ∑ j, (D j).size) bot t
    (Real.sqrt r) (Real.sqrt_nonneg r) (fun _ ↦ Database.empty)
  intro keys
  by_cases hz : keys = ∅
  · subst keys
    have he : ∀ s r : Fin k → Database X Y,
        (fun q : (∅ : Finset (TpIC k Cm)) ↦ ME.extract q.1 s) =
          (fun q : (∅ : Finset (TpIC k Cm)) ↦ ME.extract q.1 r) := by
      intro s r
      exact Subsingleton.elim _ _
    have hzero : readPermutationDefect
        (fun s ↦ RecReg.swapEquiv (Cell := Cell)
          (RecReg.restrictedExtractor ME ∅ (fun _ ↦ Database.empty))
          (fun q ↦ ME.extract q.1 s)) (compressedReadProjector k X Y (i, x)) = 0 := by
      ext a b
      simp only [readPermutationDefect, he a.1.1 b.1, sub_self, mul_zero, Matrix.zero_apply]
    rw [hzero, Matrix.zero_mul, norm_zero]
    exact Real.sqrt_nonneg r
  · by_cases ht : keys.card ≤ t
    · apply l2_opNorm_familyReadDefect_source_le i (checkedReadProjector x) _
        (recordingReadProjector_split i x) _ keys.card t (Real.sqrt r) (Real.sqrt_nonneg r)
      intro Dfix
      have h := l2_opNorm_fixedReadPermutationDefect_sq_le
        (fun D ↦ fun q : keys ↦ ME.extract q.1 (Function.update Dfix i D))
        (RecReg.swapEquiv (Cell := Cell)
          (RecReg.restrictedExtractor ME keys (fun _ ↦ Database.empty))) x (t - keys.card)
      have hn : 1 ≤ keys.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hz)
      have hb := h.trans (hi keys hn ht Dfix)
      have hcut (D : Database X Y) : D.size + keys.card ≤ t ↔ D.size ≤ t - keys.card := by omega
      simpa only [hcut] using (Real.le_sqrt (norm_nonneg _) hr).mpr hb
    · have hcut (a : (Fin k → Database X Y) × RecReg k Cm Dm Cell) :
          ¬ (∑ j, (a.1 j).size) + keys.card ≤ t := by omega
      simp only [hcut, ite_false, diagonal_zero, Matrix.mul_zero, norm_zero]
      exact Real.sqrt_nonneg r
end compressedReadSectors

section readGram
variable {S R A : Type*} [Fintype S] [DecidableEq S] [Fintype R] [DecidableEq R]
  [Fintype A]

/-- The Gram matrix of a rotated read difference is that of the retained-answer commutator. -/
theorem read_rotated_sum_gram (e : S → Equiv.Perm R) (M : A → Matrix S S ℂ)
    (P : Matrix (S × R) (S × R) ℂ) {r : ℝ}
    (h : ‖readPermutationDefect e M * P‖ ^ 2 ≤ r) :
    let V := basisMatrix (Equiv.prodCongrRight e)
    (r • (1 : Matrix (S × R) (S × R) ℂ) - ∑ a,
      (((M a ⊗ₖ (1 : Matrix R R ℂ)) - Vᴴ * (M a ⊗ₖ 1) * V) * P)ᴴ *
        (((M a ⊗ₖ (1 : Matrix R R ℂ)) - Vᴴ * (M a ⊗ₖ 1) * V) * P)).PosSemidef := by
  classical
  dsimp only
  let V := basisMatrix (Equiv.prodCongrRight e)
  have hv := basisMatrix_perm_mem_unitaryGroup (Equiv.prodCongrRight e)
  have he (a : A) (i j : S × R) :
      (V * (M a ⊗ₖ (1 : Matrix R R ℂ)) - (M a ⊗ₖ 1) * V :
        Matrix (S × R) (S × R) ℂ) i j = M a i.1 j.1 *
        ((if i.2 = e i.1 j.2 then 1 else 0) - if i.2 = e j.1 j.2 then 1 else 0) := by
    rcases i with ⟨s, v⟩
    rcases j with ⟨s', w⟩
    dsimp only [V]
    rw [Matrix.sub_apply, basisMatrix_equiv_mul_apply, mul_basisMatrix_perm_apply]
    simp only [Equiv.prodCongrRight_symm, Equiv.prodCongrRight_apply, Function.comp_apply,
      kroneckerMap_apply, Matrix.one_apply, Equiv.symm_apply_eq, mul_sub]
  have hk : MatrixMap.stinespring (fun a ↦
      (V * (M a ⊗ₖ (1 : Matrix R R ℂ)) - (M a ⊗ₖ 1) * V) * P) =
        readPermutationDefect e M * P := by
    ext i j
    simp only [MatrixMap.stinespring_apply, Matrix.mul_apply, he, readPermutationDefect]
  simp_rw [source_rotated_difference_gram _ _ _ (mem_unitaryGroup_iff'.mp hv)
    (mem_unitaryGroup_iff.mp hv)]
  rw [← MatrixMap.conjTranspose_stinespring_mul_stinespring, hk]
  exact MatrixMap.posSemidef_scalar_sub_gram_of_norm_sq_le _ h

private theorem one_kronecker_sub {J D : Type*} [DecidableEq J]
    (C B : Matrix D D ℂ) : (1 : Matrix J J ℂ) ⊗ₖ (C - B) = 1 ⊗ₖ C - 1 ⊗ₖ B := by
  ext i j
  simp only [kroneckerMap_apply, Matrix.sub_apply, mul_sub]

/-- Framing a sum of branch Grams preserves its scalar bound. -/
theorem sum_gram_frame {J D B : Type*} [Fintype J] [DecidableEq J]
    [Fintype D] [DecidableEq D] [Fintype B]
    (C : B → Matrix D D ℂ) (P : Matrix D D ℂ) {r : ℝ}
    (h : (r • (1 : Matrix D D ℂ) - ∑ a, (C a * P)ᴴ * (C a * P)).PosSemidef) :
    (r • (1 : Matrix (J × D) (J × D) ℂ) -
      ∑ a, (((1 : Matrix J J ℂ) ⊗ₖ C a) * (1 ⊗ₖ P))ᴴ *
        (((1 : Matrix J J ℂ) ⊗ₖ C a) * (1 ⊗ₖ P))).PosSemidef := by
  convert (PosSemidef.one (n := J) (R := ℂ)).kronecker h using 1
  simp only [← mul_kronecker_mul, Matrix.one_mul, conjTranspose_kronecker, conjTranspose_one]
  ext i j
  simp [kroneckerMap_apply, Matrix.sum_apply, Matrix.sub_apply, Matrix.smul_apply,
    Finset.mul_sum, mul_sub, Matrix.one_apply]
  simp only [Prod.ext_iff]
  split_ifs <;> simp_all

end readGram

/-- A private isometric rotation fixing initialization preserves the full mixed observation law. -/
theorem QuantumRuntime.evalDistMap_rotateSteps {spec : QuantumOracleSpec}
    (R : QuantumRuntime spec) (V : Matrix R.D R.D ℂ) (hV : Vᴴ * V = 1)
    (hinit : MatrixMap.conj V R.init.matrix = R.init.matrix)
    {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}
    (x : QuantumComp L spec W A) (ρ : SubState A) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ B, W B) → γ) :
    (QuantumRuntime.mk R.D R.init (Hybrid.rotateSteps V hV R.step)).evalDistMap I x ρ f =
      R.evalDistMap I x ρ f := by
  simp only [QuantumRuntime.evalDistMap]
  refine congrArg MeasureTheory.Measure.sum (funext fun p ↦ ?_)
  rw [QuantumRuntime.trace_jointPost_eq_of_simulation (R₁ := R)
    (R₂ := QuantumRuntime.mk R.D R.init (Hybrid.rotateSteps V hV R.step)) I
    (Hybrid.rotateSteps_simulation hV) (MatrixMap.isTP_conj hV) hinit x ρ p]

namespace EmulatedOracle
variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg}
/-- Branch operators for coherent ports and classical reads on one private register. -/
@[expose]
noncomputable def withReadKraus (E : EmulatedOracle P In) {Addr Ans : Type}
    (M : Addr → Ans → Matrix E.S E.S ℂ) :
    ∀ i : ((cohSpec In).sum (classicalReadSpec Addr Ans)).Port,
      ((cohSpec In).sum (classicalReadSpec Addr Ans)).Result i →
        Matrix (((cohSpec In).sum (classicalReadSpec Addr Ans)).Out i × E.S)
          (((cohSpec In).sum (classicalReadSpec Addr Ans)).In i × E.S) ℂ
  | .inl p, _ => E.coherent.U p
  | .inr c, a => (1 : Matrix Unit Unit ℂ) ⊗ₖ M c a

/-- Conjugate every oracle port by a private unitary while keeping the initial state. -/
@[expose, reducible]
noncomputable def rotatePrivate (E : EmulatedOracle P In) (V : Matrix E.S E.S ℂ)
    (hV : V ∈ unitaryGroup _ ℂ) : EmulatedOracle P In where
  S := E.S
  init := E.init
  U p := (1 ⊗ₖ V)ᴴ * E.U p * (1 ⊗ₖ V)
  unitary p := by
    have h := kronecker_mem_unitary (one_mem (unitaryGroup (In p) ℂ)) hV
    exact mul_mem (mul_mem (Unitary.star_mem h) (E.unitary p)) h

/-- A private unitary rotation fixing initialization preserves every coherent observation law. -/
theorem outcomeLawWith_rotatePrivate (E : EmulatedOracle P In) (V : Matrix E.S E.S ℂ)
    (hV : V ∈ unitaryGroup _ ℂ) (hinit : MatrixMap.conj Vᴴ E.init.matrix = E.init.matrix)
    {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}
    (x : QuantumComp L (cohSpec In) W A) (ρ : SubState A)
    {γ : Type*} [MeasurableSpace γ] (f : (Σ B, W B) → γ) :
    (E.rotatePrivate V hV).coherent.toRuntime.evalDistMap I x ρ f =
      E.coherent.toRuntime.evalDistMap I x ρ f := by
  have hv : V * Vᴴ = 1 := by
    simpa only [star_eq_conjTranspose] using mem_unitaryGroup_iff.mp hV
  apply outcomeLawWith_eq_of_intertwine E.coherent (E.rotatePrivate V hV).coherent Vᴴ
    (by simpa only [conjTranspose_conjTranspose] using hv)
  · intro i
    cases i
    apply coherent_U_mul_one_kronecker
    intro p
    change ((1 ⊗ₖ V)ᴴ * E.U p * (1 ⊗ₖ V)) * (1 ⊗ₖ Vᴴ) = (1 ⊗ₖ Vᴴ) * E.U p
    have he : (1 ⊗ₖ V) * ((1 : Matrix (In p) (In p) ℂ) ⊗ₖ Vᴴ) = 1 := by
      rw [← mul_kronecker_mul, hv, Matrix.one_mul,
        one_kronecker_one]
    rw [Matrix.mul_assoc, he, Matrix.mul_one, conjTranspose_kronecker, conjTranspose_one]
  · exact hinit
end EmulatedOracle

section
variable {A : Type*} [Fintype A] [DecidableEq A]
/-- Conjugating twice by a self-adjoint unitary fixes every operator. -/
theorem conjugate_involution (V U : Matrix A A ℂ) (hv : Vᴴ = V) (hV : Vᴴ * V = 1) :
    Vᴴ * (Vᴴ * U * V) * V = U := by
  have hh : V * V = 1 := by rwa [hv] at hV
  rw [hv]
  calc
    V * (V * U * V) * V = (V * V) * U * (V * V) := by simp only [Matrix.mul_assoc]
    _ = U := by rw [hh, Matrix.one_mul, Matrix.mul_one]
/-- Equal operators have zero source-projected discrepancy. -/
theorem gram_zero_of_eq (U V P : Matrix A A ℂ) (h : V = U) :
    ((0 : ℝ) • 1 - ((U - V) * P)ᴴ * ((U - V) * P)).PosSemidef := by
  subst V
  simpa using (PosSemidef.zero : (0 : Matrix A A ℂ).PosSemidef)
end
namespace VCOracle
open EmulatedOracle
variable {k : ℕ} {X Y Cm Z Yr Cell : Type} {Dm : Fin k → Type}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  [Fintype Yr] [DecidableEq Yr] [Fintype Cell] [DecidableEq Cell]
  [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
  (E : VCOracle k X Y) (ME : MultiExtractor k Cm Dm E.S) (code : TpDCode k Dm Z)
  (bot : Cell) (U : Matrix (Yr × Cell) (Yr × Cell) ℂ) (hU : U ∈ unitaryGroup _ ℂ)
/-- A recording read applies its private answer projector and carries all record cells. -/
theorem recordingRead_branch (c : Fin k × X) (a : Option Y) :
    (E.recordingRead (Dm := Dm) (Cell := Cell) c).branch a =
      MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        (E.classicalRead.A c a ⊗ₖ (1 : Matrix (RecReg k Cm Dm Cell) (RecReg k Cm Dm Cell) ℂ))) := by
  ext σ : 1
  rw [recordingRead, SubInstrument.branch_reindex_apply, DSubInstrument.branch_frame_apply,
    ProjectiveClassicalAnswers.step_branch, MatrixMap.amplify_conj, MatrixMap.conj_apply,
    ← MatrixMap.conj_reindex_apply]
  congr 2
  ext ⟨u, s, r⟩ ⟨v, s', r'⟩
  simp only [reindex_apply, submatrix_apply, Equiv.prodAssoc_symm_apply,
    kroneckerMap_apply, mul_assoc]

/-- Each branch of the unsplit mixed recording runtime has its explicit Kraus operator. -/
theorem mixedRecordRuntime_step_branch (p : (mixedRecSpec k X Y Cm Z Yr).Port)
    (a : (mixedRecSpec k X Y Cm Z Yr).Result p) :
    ((E.mixedRecordRuntime ME code bot U hU).step p).branch a =
      MatrixMap.conj ((E.withRecord ME code bot U hU).withReadKraus
        (fun c a ↦ E.classicalRead.A c a ⊗ₖ
          (1 : Matrix (RecReg k Cm Dm Cell) (RecReg k Cm Dm Cell) ℂ)) p a) := by
  cases p with
  | inl p => exact (E.withRecord ME code bot U hU).coherent.toRuntime_step_branch p a
  | inr c => exact recordingRead_branch E c a

/-- The split mixed recording runtime uses the same read branch matrices. -/
theorem mixedRecordMERuntime_step_branch (p : (mixedRecSpec k X Y Cm Z Yr).Port)
    (a : (mixedRecSpec k X Y Cm Z Yr).Result p) :
    ((E.mixedRecordMERuntime ME code bot U hU).step p).branch a =
      MatrixMap.conj ((E.withRecordME ME code bot U hU).withReadKraus
        (fun c a ↦ E.classicalRead.A c a ⊗ₖ
          (1 : Matrix (RecReg k Cm Dm Cell) (RecReg k Cm Dm Cell) ℂ)) p a) := by
  cases p with
  | inl p => exact (E.withRecordME ME code bot U hU).coherent.toRuntime_step_branch p a
  | inr c => exact recordingRead_branch E c a

/-- Every mixed call advances the joint population grade by at most one. -/
theorem mixedRecordRuntime_step_grade (g : E.S → ℕ)
    (hE : ∀ i a b s r, E.U i (a, s) (b, r) ≠ 0 → g s ≤ g r + 1)
    (hread : ∀ c a s r, E.classicalRead.A c a s r ≠ 0 → g s ≤ g r + 1)
    (p : (mixedRecSpec k X Y Cm Z Yr).Port)
    (a : (mixedRecSpec k X Y Cm Z Yr).Result p) (t : ℕ)
    (σ : Matrix ((mixedRecSpec k X Y Cm Z Yr).In p × (E.S × RecReg k Cm Dm Cell))
      ((mixedRecSpec k X Y Cm Z Yr).In p × (E.S × RecReg k Cm Dm Cell)) ℂ)
    (hs : QuerySupportedOn (fun m ↦ g m.2.1 + RecReg.population bot m.2.2) (Set.Iic t) σ) :
    QuerySupportedOn (fun m ↦ g m.2.1 + RecReg.population bot m.2.2) (Set.Iic (t + 1))
      (((E.mixedRecordRuntime ME code bot U hU).step p).branch a σ) := by
  cases p with
  | inl p =>
    exact (E.withRecord ME code bot U hU).coherent.querySupportedOn_toRuntime_step
      (fun s ↦ g s.1 + RecReg.population bot s.2)
      ((E.withRecord ME code bot U hU).coherent_U_grade _
        (fun p a b d d' h ↦ withRecord_U_grade E ME code bot g hE U hU p b a d' d h))
      p a t σ hs
  | inr c =>
    rw [mixedRecordRuntime_step_branch]
    refine hs.conj ?_
    intro i j hij hj
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ
      (E.classicalRead.A c a ⊗ₖ (1 : Matrix (RecReg k Cm Dm Cell)
        (RecReg k Cm Dm Cell) ℂ))) i j ≠ 0 at hij
    have ha := left_ne_zero_of_mul (right_ne_zero_of_mul hij)
    have hh := right_ne_zero_of_mul (right_ne_zero_of_mul hij)
    have he : i.2.2 = j.2.2 := by
      simpa only [Matrix.one_apply, ne_eq, ite_eq_right_iff, one_ne_zero,
        imp_false, not_not] using hh
    have hg := hread c a i.2.1 j.2.1 ha
    change g i.2.1 + RecReg.population bot i.2.2 ≤ t + 1
    change g j.2.1 + RecReg.population bot j.2.2 ≤ t at hj
    rw [he]
    omega

/-- Ordinary index weights and each read-input trace are bounded by the full input trace. -/
theorem recordVCWeight_le_trace (p : (mixedRecSpec k X Y Cm Z Yr).Port)
    (σ : Matrix ((mixedRecSpec k X Y Cm Z Yr).In p × (E.S × RecReg k Cm Dm Cell))
      ((mixedRecSpec k X Y Cm Z Yr).In p × (E.S × RecReg k Cm Dm Cell)) ℂ)
    (hσ : σ.PosSemidef) :
    E.recordVCWeight ME code bot U hU p σ ≤ ENNReal.ofReal σ.trace.re := by
  cases p with
  | inr c => exact le_rfl
  | inl p =>
    cases p
    let R := E.withRecord ME code bot U hU
    change Matrix (EmulatedOracle.cohIn (recIn k X Y Cm Z Yr) × R.S)
      (EmulatedOracle.cohIn (recIn k X Y Cm Z Yr) × R.S) ℂ at σ
    have hn (i) : 0 ≤ (MatrixMap.conj (R.indexProj i) σ).trace.re :=
      (hσ.mul_mul_conjTranspose_same _).trace_re_nonneg
    have ht : ∑ i, ENNReal.ofReal (MatrixMap.conj (R.indexProj i) σ).trace.re =
        ENNReal.ofReal σ.trace.re := by
      rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (fun i _ ↦ hn i),
        ← Complex.re_sum, R.sum_trace_conj_indexProj]
    change (∑ i : Fin k, ENNReal.ofReal
      (MatrixMap.conj (R.indexProj (.inl (.inl i))) σ).trace.re) ≤ ENNReal.ofReal σ.trace.re
    rw [← ht, Fintype.sum_sum_type, Fintype.sum_sum_type]
    change (∑ i : Fin k, _) ≤ (∑ i : Fin k, _) + _ + _
    exact le_self_add.trans le_self_add

/-- The ordinary-port recording comparison satisfies the source-projected Gram bound. -/
theorem withRecord_rotated_ordinary_gram
    (g : E.S → ℕ) (j : ℕ) (r : ℝ) (i : Fin k)
    (h : ‖permutationDefect (RecReg.swapEquiv ME) (E.U i) *
      diagonal (fun a : (X × Y) × E.S × RecReg k Cm Dm Cell ↦
        if g a.2.1 + RecReg.population bot a.2.2 ≤ j then (1 : ℂ) else 0)‖ ^ 2 ≤ r) :
    let F := (E.withRecordME ME code bot U hU).rotatePrivate (RecReg.swapUnitary ME)
      (RecReg.swapUnitary_mem_unitaryGroup ME)
    let C : Matrix ((X × Y) × E.S × RecReg k Cm Dm Cell)
        ((X × Y) × E.S × RecReg k Cm Dm Cell) ℂ :=
      (show Matrix ((X × Y) × E.S × RecReg k Cm Dm Cell)
          ((X × Y) × E.S × RecReg k Cm Dm Cell) ℂ from
        (E.withRecord ME code bot U hU).U (.inl (.inl i))) -
      (show Matrix ((X × Y) × E.S × RecReg k Cm Dm Cell)
          ((X × Y) × E.S × RecReg k Cm Dm Cell) ℂ from F.U (.inl (.inl i)))
    let P := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ diagonal
      (fun a : E.S × RecReg k Cm Dm Cell ↦
        if g a.1 + RecReg.population bot a.2 ≤ j then (1 : ℂ) else 0)
    (r • 1 - (C * P)ᴴ * (C * P)).PosSemidef := by
  exact posSemidef_rotated_port_difference_of_source_bound ME (E.U i) g bot j r h

/-- The private recording swap commutes with extraction (ePrint 2025/2166, Lemma 9.7, p. 69). -/
theorem withRecord_rotated_extract :
    let F := (E.withRecordME ME code bot U hU).rotatePrivate (RecReg.swapUnitary ME)
      (RecReg.swapUnitary_mem_unitaryGroup ME)
    F.U (.inl (.inr ())) = (E.withRecord ME code bot U hU).U (.inl (.inr ())) := by
  exact extractUnitary_swap_conjugacy ME code

/-- Conjugating split recording gives unsplit recording (ePrint 2025/2166, Lemma 9.13, p. 67). -/
theorem withRecord_rotated_record :
    let F := (E.withRecordME ME code bot U hU).rotatePrivate (RecReg.swapUnitary ME)
      (RecReg.swapUnitary_mem_unitaryGroup ME)
    F.U (.inr ()) = (E.withRecord ME code bot U hU).U (.inr ()) := by
  have hc := recordUnitary_swap_conjugacy ME U
  have hv := kronecker_mem_unitary (one_mem (unitaryGroup (TpIC k Cm × Yr) ℂ))
    (RecReg.swapUnitary_mem_unitaryGroup (Cell := Cell) ME)
  have hh : ((1 : Matrix (TpIC k Cm × Yr) (TpIC k Cm × Yr) ℂ) ⊗ₖ
      RecReg.swapUnitary (Cell := Cell) ME)ᴴ = 1 ⊗ₖ RecReg.swapUnitary ME := by
    rw [conjTranspose_kronecker, conjTranspose_one, RecReg.swapUnitary_conjTranspose]
  have he := conjugate_involution _ (recordUnitary (S := E.S) U) hh
    (mem_unitaryGroup_iff'.mp hv)
  rw [hc] at he
  exact he

private theorem recording_ordinary_weight_le (g : E.S → ℕ) (j : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hC : ∀ i,
      ‖permutationDefect (RecReg.swapEquiv ME) (E.U i) *
        diagonal (fun a : (X × Y) × E.S × RecReg k Cm Dm Cell ↦
          if g a.2.1 + RecReg.population bot a.2.2 ≤ j then (1 : ℂ) else 0)‖ ^ 2 ≤ r)
    (σ : Matrix (cohIn (recIn k X Y Cm Z Yr) × (E.S × RecReg k Cm Dm Cell))
      (cohIn (recIn k X Y Cm Z Yr) × (E.S × RecReg k Cm Dm Cell)) ℂ)
    (hσ : σ.PosSemidef)
    (hsupp : QuerySupportedOn
      (fun s : cohIn (recIn k X Y Cm Z Yr) × (E.S × RecReg k Cm Dm Cell) ↦
        g s.2.1 + RecReg.population bot s.2.2) (Set.Iic j) σ) :
    let R := E.withRecord ME code bot U hU
    let F := (E.withRecordME ME code bot U hU).rotatePrivate
      (RecReg.swapUnitary ME) (RecReg.swapUnitary_mem_unitaryGroup ME)
    ENNReal.ofReal (MatrixMap.conj (R.coherent.U () -
      (show Matrix (cohIn (recIn k X Y Cm Z Yr) × R.S)
        (cohIn (recIn k X Y Cm Z Yr) × R.S) ℂ from F.coherent.U ())) σ).trace.re ≤
      ENNReal.ofReal r * ∑ i : Fin k,
        ENNReal.ofReal (MatrixMap.conj (R.indexProj (.inl (.inl i))) σ).trace.re := by
  let D := QReg.of (E.S × RecReg k Cm Dm Cell)
  let R : EmulatedOracle ((Fin k ⊕ Unit) ⊕ Unit) (recIn k X Y Cm Z Yr) :=
    { S := D, init := (E.withRecord ME code bot U hU).init,
      U := (E.withRecord ME code bot U hU).U,
      unitary := (E.withRecord ME code bot U hU).unitary }
  let F := (E.withRecordME ME code bot U hU).rotatePrivate
    (RecReg.swapUnitary ME) (RecReg.swapUnitary_mem_unitaryGroup ME)
  have hp : ∀ p,
      ((if ordinaryPort p then r else 0) •
        (1 : Matrix (recIn k X Y Cm Z Yr p × R.S) (recIn k X Y Cm Z Yr p × R.S) ℂ) -
        ((R.U p - (show Matrix (recIn k X Y Cm Z Yr p × R.S)
          (recIn k X Y Cm Z Yr p × R.S) ℂ from F.U p)) *
          (1 ⊗ₖ diagonal (fun s : E.S × RecReg k Cm Dm Cell ↦
          if g s.1 + RecReg.population bot s.2 ≤ j then (1 : ℂ) else 0)))ᴴ *
        ((R.U p - (show Matrix (recIn k X Y Cm Z Yr p × R.S)
          (recIn k X Y Cm Z Yr p × R.S) ℂ from F.U p)) *
          (1 ⊗ₖ diagonal (fun s : E.S × RecReg k Cm Dm Cell ↦
          if g s.1 + RecReg.population bot s.2 ≤ j then (1 : ℂ) else 0)))).PosSemidef := by
    rintro ((i | u) | u)
    · exact withRecord_rotated_ordinary_gram E ME code bot U hU g j (r) i (hC i)
    · cases u
      exact gram_zero_of_eq _ _ _ (withRecord_rotated_extract E ME code bot U hU)
    · cases u
      exact gram_zero_of_eq _ _ _ (withRecord_rotated_record E ME code bot U hU)
  have h := R.ofReal_trace_coherentBlocks_conj_le_selectedMass
    (fun p ↦ R.U p - (show Matrix (recIn k X Y Cm Z Yr p × R.S)
      (recIn k X Y Cm Z Yr p × R.S) ℂ from F.U p)) _
    ordinaryPort hr hp hσ ?_
  · change ENNReal.ofReal (MatrixMap.conj
      (coherentBlocks R.U - coherentBlocks (In := recIn k X Y Cm Z Yr) (D := R.S) (show ∀ p,
        Matrix (recIn k X Y Cm Z Yr p × R.S) (recIn k X Y Cm Z Yr p × R.S) ℂ
          from F.U)) σ).trace.re ≤ _
    rw [← coherentBlocks_sub]
    convert h using 1
    simp [selectedMass, ordinaryPort, Fintype.sum_sum_type]
    rfl
  · change MatrixMap.conj ((1 : Matrix (cohIn (recIn k X Y Cm Z Yr))
      (cohIn (recIn k X Y Cm Z Yr)) ℂ) ⊗ₖ diagonal (fun s : D ↦
        if g s.1 + RecReg.population bot s.2 ≤ j then (1 : ℂ) else 0)) σ = σ
    rw [← diagonal_one, diagonal_kronecker_diagonal]
    exact hsupp.conj_diagonal_eq_self fun m hm ↦ by simp [Set.mem_Iic.mp hm]

private theorem recording_read_gram (g : E.S → ℕ) (j : ℕ) (r : ℝ)
    (c : Fin k × X)
    (h : ‖readPermutationDefect (RecReg.swapEquiv ME) (E.classicalRead.A c) *
      diagonal (fun s : E.S × RecReg k Cm Dm Cell ↦
        if g s.1 + RecReg.population bot s.2 ≤ j then (1 : ℂ) else 0)‖ ^ 2 ≤ r) :
    let D := E.S × RecReg k Cm Dm Cell
    let V := RecReg.swapUnitary (Cell := Cell) ME
    let C := fun a ↦ (1 : Matrix Unit Unit ℂ) ⊗ₖ
      (E.classicalRead.A c a ⊗ₖ (1 : Matrix (RecReg k Cm Dm Cell) _ ℂ)) -
      (1 ⊗ₖ V) * (1 ⊗ₖ (E.classicalRead.A c a ⊗ₖ 1)) * (1 ⊗ₖ Vᴴ)
    let P := (1 : Matrix Unit Unit ℂ) ⊗ₖ diagonal (fun s : D ↦
      if g s.1 + RecReg.population bot s.2 ≤ j then (1 : ℂ) else 0)
    (r • (1 : Matrix (Unit × D) (Unit × D) ℂ) -
      ∑ a : Option Y, (C a * P)ᴴ * (C a * P)).PosSemidef := by
  have hb := sum_gram_frame (J := Unit) _ _
    (read_rotated_sum_gram (RecReg.swapEquiv ME) (E.classicalRead.A c) _ h)
  dsimp only
  simp only [← mul_kronecker_mul, Matrix.one_mul, ← one_kronecker_sub,
    RecReg.swapUnitary_conjTranspose]
  change (r • (1 : Matrix (Unit × (E.S × RecReg k Cm Dm Cell))
    (Unit × (E.S × RecReg k Cm Dm Cell)) ℂ) - ∑ a : Option Y,
    (((1 : Matrix Unit Unit ℂ) ⊗ₖ (E.classicalRead.A c a ⊗ₖ 1 -
      (RecReg.swapUnitary ME)ᴴ * (E.classicalRead.A c a ⊗ₖ 1) *
        RecReg.swapUnitary ME)) * (1 ⊗ₖ _))ᴴ *
    (((1 : Matrix Unit Unit ℂ) ⊗ₖ (E.classicalRead.A c a ⊗ₖ 1 -
      (RecReg.swapUnitary ME)ᴴ * (E.classicalRead.A c a ⊗ₖ 1) *
        RecReg.swapUnitary ME)) * (1 ⊗ₖ _))).PosSemidef at hb
  simpa only [← mul_kronecker_mul, Matrix.one_mul, RecReg.swapUnitary_conjTranspose] using hb

/-- Mixed recording comparison charges ordinary queries and checked reads in the source world.
Extraction and recording are exactly conjugate; read branches contribute a summed Gram defect. -/
theorem outcomeLawWith_recording_rpow_bounds
    (g : E.S → ℕ)
    (hE : ∀ i a b s r, E.U i (a, s) (b, r) ≠ 0 → g s ≤ g r + 1)
    (hread : ∀ c a s r, E.classicalRead.A c a s r ≠ 0 → g s ≤ g r + 1)
    (hinit : QuerySupportedOn g (Set.Iic 0) E.init.matrix)
    (rate : ℕ → ℝ) (hrate : ∀ j, 0 ≤ rate j)
    {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}
    {x : QuantumComp L (mixedRecSpec k X Y Cm Z Yr) W A}
    {t : ℕ} (hx : x.IsTotalQueryBound t) (ρ : SubState A)
    (hC : ∀ j < t, ∀ i,
      ‖permutationDefect (RecReg.swapEquiv ME) (E.U i) *
        diagonal (fun a : (X × Y) × E.S × RecReg k Cm Dm Cell ↦
          if g a.2.1 + RecReg.population bot a.2.2 ≤ j then (1 : ℂ) else 0)‖ ^ 2 ≤ rate j)
    (hreadC : ∀ j < t, ∀ c,
      ‖readPermutationDefect (RecReg.swapEquiv ME) (E.classicalRead.A c) *
        diagonal (fun a : E.S × RecReg k Cm Dm Cell ↦
          if g a.1 + RecReg.population bot a.2 ≤ j then (1 : ℂ) else 0)‖ ^ 2 ≤ rate j)
    {γ : Type*} [MeasurableSpace γ] (f : (Σ B, W B) → γ) {event : Set γ}
    (hevent : MeasurableSet event) :
    let R := E.mixedRecordRuntime ME code bot U hU
    let T := E.mixedRecordMERuntime ME code bot U hU
    let err := ((∑ j ∈ Finset.range t, ENNReal.ofReal (rate j)) *
      R.totalWeight I (E.recordVCWeight ME code bot U hU) x
        (ρ.matrix ⊗ₖ R.init.matrix)) ^ (2⁻¹ : ℝ)
    R.evalDistMap I x ρ f event ^ (2⁻¹ : ℝ) ≤
      T.evalDistMap I x ρ f event ^ (2⁻¹ : ℝ) + err ∧
    T.evalDistMap I x ρ f event ^ (2⁻¹ : ℝ) ≤
      R.evalDistMap I x ρ f event ^ (2⁻¹ : ℝ) + err := by
  let : ∀ p, Fintype ((mixedRecSpec k X Y Cm Z Yr).Result p) := fun p ↦
    match p with
    | .inl _ => inferInstanceAs (Fintype Unit)
    | .inr _ => inferInstanceAs (Fintype (Option Y))
  let D := QReg.of (E.S × RecReg k Cm Dm Cell)
  let R : EmulatedOracle ((Fin k ⊕ Unit) ⊕ Unit) (recIn k X Y Cm Z Yr) :=
    { S := D, init := (E.withRecord ME code bot U hU).init,
      U := (E.withRecord ME code bot U hU).U,
      unitary := (E.withRecord ME code bot U hU).unitary }
  let T : EmulatedOracle ((Fin k ⊕ Unit) ⊕ Unit) (recIn k X Y Cm Z Yr) :=
    { S := D, init := R.init, U := (E.withRecordME ME code bot U hU).U,
      unitary := (E.withRecordME ME code bot U hU).unitary }
  let Rm : QuantumRuntime (mixedRecSpec k X Y Cm Z Yr) :=
    { D := D, init := R.init, step := (E.mixedRecordRuntime ME code bot U hU).step }
  let Tm : QuantumRuntime (mixedRecSpec k X Y Cm Z Yr) :=
    { D := D, init := R.init, step := (E.mixedRecordMERuntime ME code bot U hU).step }
  let V := RecReg.swapUnitary (Cell := Cell) ME
  have hv : Vᴴ = V := RecReg.swapUnitary_conjTranspose ME
  have hV := RecReg.swapUnitary_mem_unitaryGroup (Cell := Cell) ME
  have hVV : Vᴴ * V = 1 := mem_unitaryGroup_iff'.mp hV
  let F := T.rotatePrivate V hV
  let reads := fun c a ↦ E.classicalRead.A c a ⊗ₖ
    (1 : Matrix (RecReg k Cm Dm Cell) (RecReg k Cm Dm Cell) ℂ)
  let K₀ : ∀ p : (mixedRecSpec k X Y Cm Z Yr).Port,
      (mixedRecSpec k X Y Cm Z Yr).Result p →
        Matrix ((mixedRecSpec k X Y Cm Z Yr).Out p × D)
          ((mixedRecSpec k X Y Cm Z Yr).In p × D) ℂ := R.withReadKraus reads
  let K₁ : ∀ p : (mixedRecSpec k X Y Cm Z Yr).Port,
      (mixedRecSpec k X Y Cm Z Yr).Result p →
        Matrix ((mixedRecSpec k X Y Cm Z Yr).Out p × D)
          ((mixedRecSpec k X Y Cm Z Yr).In p × D) ℂ := T.withReadKraus reads
  let Kr : ∀ p : (mixedRecSpec k X Y Cm Z Yr).Port,
      (mixedRecSpec k X Y Cm Z Yr).Result p →
        Matrix ((mixedRecSpec k X Y Cm Z Yr).Out p × D)
          ((mixedRecSpec k X Y Cm Z Yr).In p × D) ℂ := fun p a ↦
    ((1 : Matrix ((mixedRecSpec k X Y Cm Z Yr).Out p)
      ((mixedRecSpec k X Y Cm Z Yr).Out p) ℂ) ⊗ₖ V) * K₁ p a * (1 ⊗ₖ Vᴴ)
  have h₀ : ∀ p a, (Rm.step p).branch a = MatrixMap.conj (K₀ p a) :=
    mixedRecordRuntime_step_branch E ME code bot U hU
  have h₁ : ∀ p a, (Tm.step p).branch a = MatrixMap.conj (K₁ p a) :=
    mixedRecordMERuntime_step_branch E ME code bot U hU
  have hrot : ∀ p a, (Hybrid.rotateSteps V hVV Tm.step p).branch a =
      MatrixMap.conj (Kr p a) := by
    intro p a
    exact Hybrid.branch_krausSandwich_of_eq_conj (h₁ p) _ _ _ _ a
  have hg : QuerySupportedOn
      (fun a : A × R.S ↦ g a.2.1 + RecReg.population bot a.2.2) (Set.Iic 0)
        (ρ.matrix ⊗ₖ R.init.matrix) := recording_initial_grade E bot g hinit ρ
  have hb := Rm.tsum_rpow_queryWeight_le_of_total_grade I
    (fun s ↦ g s.1 + RecReg.population bot s.2)
    (mixedRecordRuntime_step_grade E ME code bot U hU g hE hread)
    (QuantumRuntime.krausWeight (fun p a ↦ K₀ p a - Kr p a))
    (E.recordVCWeight ME code bot U hU) hx (ρ.prod R.init).posSemidef hg
    (fun j ↦ ENNReal.ofReal (rate j)) ?_
  · have hb₀ := QuantumRuntime.rpow_inv_two_outcomeLawWith_le I R.init h₀ hrot x ρ f hevent
    have hb₁ := QuantumRuntime.rpow_inv_two_outcomeLawWith_le' I R.init h₀ hrot x ρ f hevent
    have hl := Tm.evalDistMap_rotateSteps V hVV
      (RecReg.swapUnitary_initial ME E.init.matrix bot) I x ρ f
    change (QuantumRuntime.mk R.S R.init (Hybrid.rotateSteps V hVV Tm.step)).evalDistMap
      I x ρ f = Tm.evalDistMap I x ρ f at hl
    rw [hl] at hb₀ hb₁
    exact ⟨hb₀.trans (add_le_add le_rfl hb), hb₁.trans (add_le_add le_rfl hb)⟩
  · intro j hj p σ hσ hsupp
    cases p with
    | inl p =>
      cases p
      let TU : ∀ p, Matrix (recIn k X Y Cm Z Yr p × D)
          (recIn k X Y Cm Z Yr p × D) ℂ := T.U
      have he : Kr (.inl ()) () = F.coherent.U () := by
        dsimp only [Kr, K₁, EmulatedOracle.withReadKraus]
        change ((1 : Matrix (cohIn (recIn k X Y Cm Z Yr))
          (cohIn (recIn k X Y Cm Z Yr)) ℂ) ⊗ₖ V) * coherentBlocks TU *
            ((1 : Matrix (cohIn (recIn k X Y Cm Z Yr))
              (cohIn (recIn k X Y Cm Z Yr)) ℂ) ⊗ₖ Vᴴ) =
          coherentBlocks (In := recIn k X Y Cm Z Yr) (D := D)
            (fun p ↦ ((1 : Matrix (recIn k X Y Cm Z Yr p)
            (recIn k X Y Cm Z Yr p) ℂ) ⊗ₖ V)ᴴ * TU p * (1 ⊗ₖ V))
        simp only [conjTranspose_kronecker, conjTranspose_one]
        change _ = coherentBlocks (In := recIn k X Y Cm Z Yr) (D := D)
          ((fun p ↦ (1 : Matrix (recIn k X Y Cm Z Yr p)
          (recIn k X Y Cm Z Yr p) ℂ) ⊗ₖ Vᴴ) * TU * (fun p ↦ 1 ⊗ₖ V))
        rw [coherentBlocks_mul, coherentBlocks_mul, coherentBlocks_database,
          coherentBlocks_database, hv]
      change (∑' a : Unit, ENNReal.ofReal
        (MatrixMap.conj (K₀ (.inl ()) a - Kr (.inl ()) a) σ).trace.re) ≤ _
      rw [tsum_fintype, Fintype.sum_unique, he]
      exact recording_ordinary_weight_le E ME code bot U hU g j (rate j)
        (hrate j) (hC j hj) σ hσ hsupp
    | inr c =>
      let P := diagonal (fun s : E.S × RecReg k Cm Dm Cell ↦
        if g s.1 + RecReg.population bot s.2 ≤ j then (1 : ℂ) else 0)
      have hgram : ((rate j) • (1 : Matrix (Unit × R.S) (Unit × R.S) ℂ) -
          ∑ a : Option Y, ((K₀ (.inr c) a - Kr (.inr c) a) * (1 ⊗ₖ P))ᴴ *
            ((K₀ (.inr c) a - Kr (.inr c) a) * (1 ⊗ₖ P))).PosSemidef :=
        recording_read_gram E ME bot g j (rate j) c (hreadC j hj c)
      have h := Rm.krausWeight_le_of_sum_gram (fun p a ↦ K₀ p a - Kr p a) (.inr c)
        (1 ⊗ₖ P) 1 (hrate j) hgram hσ ?_
      · rw [Matrix.one_mul] at h
        change (∑' a : Option Y, ENNReal.ofReal
          (MatrixMap.conj (K₀ (.inr c) a - Kr (.inr c) a) σ).trace.re) ≤ _ at h ⊢
        exact h
      · rw [← diagonal_one, diagonal_kronecker_diagonal]
        exact hsupp.conj_diagonal_eq_self fun m hm ↦ by simp [Set.mem_Iic.mp hm]

end VCOracle

/-- Square-root comparisons of subprobabilities allow an error cap of one. -/
theorem rpow_bounds_cap {p q ε : ℝ≥0∞} (hp : p ≤ 1) (hq : q ≤ 1)
    (h : p ^ (2⁻¹ : ℝ) ≤ q ^ (2⁻¹ : ℝ) + ε ^ (2⁻¹ : ℝ) ∧
      q ^ (2⁻¹ : ℝ) ≤ p ^ (2⁻¹ : ℝ) + ε ^ (2⁻¹ : ℝ)) :
    p ^ (2⁻¹ : ℝ) ≤ q ^ (2⁻¹ : ℝ) + (min 1 ε) ^ (2⁻¹ : ℝ) ∧
      q ^ (2⁻¹ : ℝ) ≤ p ^ (2⁻¹ : ℝ) + (min 1 ε) ^ (2⁻¹ : ℝ) := by
  rcases le_total ε 1 with hε | hε
  · simpa only [min_eq_right hε] using h
  · rw [min_eq_left hε, ENNReal.one_rpow]
    have hp' : p ^ (2⁻¹ : ℝ) ≤ 1 := by
      simpa using ENNReal.rpow_le_rpow hp (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    have hq' : q ^ (2⁻¹ : ℝ) ≤ 1 := by
      simpa using ENNReal.rpow_le_rpow hq (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    exact ⟨hp'.trans le_add_self, hq'.trans le_add_self⟩
universe v w
namespace VCOracle
open EmulatedOracle
variable {k : ℕ} {X Y Cm Z : Type} {Dm : Fin k → Type}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
/-- P5 from ordinary-query commutators and summed checked-read branch Grams.
The local operator hypothesis is quantified over finite recording cell types, independently
of the recording unitary and adversary. The conclusion covers every mixed adaptive program
and arbitrary local instruments in `OnlineIndistinguishable` (ePrint 2025/2166, Definition 7.3,
pp. 50–51). -/
theorem onlineIndistinguishable_of_recording_source_bounds
    (E : VCOracle k X Y) (ME : MultiExtractor k Cm Dm E.S) (code : TpDCode k Dm Z)
    (g : E.S → ℕ)
    (hE : ∀ i a b s r, E.U i (a, s) (b, r) ≠ 0 → g s ≤ g r + 1)
    (hread : ∀ c a s r, E.classicalRead.A c a s r ≠ 0 → g s ≤ g r + 1)
    (hinit : QuerySupportedOn g (Set.Iic 0) E.init.matrix)
    (rate : ℕ → ℝ) (hrate : ∀ j, 0 ≤ rate j)
    (hC : ∀ (Cell : Type) [Fintype Cell] [DecidableEq Cell] (bot : Cell) (j : ℕ) (i : Fin k),
      ‖permutationDefect (RecReg.swapEquiv ME) (E.U i) *
        diagonal (fun a : (X × Y) × E.S × RecReg k Cm Dm Cell ↦
          if g a.2.1 + RecReg.population bot a.2.2 ≤ j then (1 : ℂ) else 0)‖ ^ 2 ≤ rate j)
    (hreadC : ∀ (Cell : Type) [Fintype Cell] [DecidableEq Cell] (bot : Cell) (j : ℕ)
      (c : Fin k × X),
      ‖readPermutationDefect (RecReg.swapEquiv ME) (E.classicalRead.A c) *
        diagonal (fun a : E.S × RecReg k Cm Dm Cell ↦
          if g a.1 + RecReg.population bot a.2 ≤ j then (1 : ℂ) else 0)‖ ^ 2 ≤ rate j) :
    OnlineIndistinguishable.{v, w} E ME code
      (fun t wVC _ _ ↦ min 1
        ((∑ j ∈ Finset.range t, ENNReal.ofReal (rate j)) * min wVC (t : ℝ≥0∞))) := by
  intro Yr Cell _ _ _ _ bot U hU t wVC wME wRec A W x f ρ hx h₁ _ _
  let R := E.mixedRecordRuntime ME code bot U hU
  have hb := outcomeLawWith_recording_rpow_bounds E ME code bot U hU g hE hread hinit rate hrate
    .instruments hx ρ (fun j _ i ↦ hC Cell bot j i) (fun j _ c ↦ hreadC Cell bot j c)
    f (measurableSet_singleton true)
  have ht := R.totalWeight_le_of_isTotalQueryBound .instruments
    (recordVCWeight_le_trace E ME code bot U hU) hx (ρ.prod R.init).posSemidef
  have htr : ENNReal.ofReal (ρ.matrix ⊗ₖ R.init.matrix).trace.re ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (ρ.prod R.init).trace_re_le_one
  have hmass : R.totalWeight .instruments (E.recordVCWeight ME code bot U hU) x
      (ρ.matrix ⊗ₖ R.init.matrix) ≤ min wVC (t : ℝ≥0∞) :=
    le_min h₁ (ht.trans (mul_le_of_le_one_right' htr))
  have hm := ENNReal.rpow_le_rpow (mul_le_mul_right hmass
    (∑ j ∈ Finset.range t, ENNReal.ofReal (rate j))) (by norm_num : (0 : ℝ) ≤ 2⁻¹)
  exact rpow_bounds_cap
    (R.outcomeLawWith_le_one .instruments x ρ f {true})
    ((E.mixedRecordMERuntime ME code bot U hU).outcomeLawWith_le_one .instruments x ρ f {true})
    ⟨hb.1.trans (add_le_add le_rfl hm), hb.2.trans (add_le_add le_rfl hm)⟩

end VCOracle
section
variable {k : ℕ} {X Y Cm Z : Type} {Dm : Fin k → Type}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
/-- A checked read increases total database population by at most one. -/
theorem compressedReadProjector_totalSize_le (c : Fin k × X) (a : Option Y)
    (s r : Fin k → Database X Y) (h : compressedReadProjector k X Y c a s r ≠ 0) :
    ∑ i, (s i).size ≤ (∑ i, (r i).size) + 1 := by
  have hi := compressedReadProjector_size_le c.1 c a r s h
  rw [recordingReadProjector_split] at h
  split_ifs at h with he
  · have hj (j : Fin k) : (s j).size ≤ (r j).size + if j = c.1 then 1 else 0 := by
      by_cases hji : j = c.1
      · simpa [hji] using hi
      · simp [hji, congrFun he ⟨j, hji⟩]
    simpa [Finset.sum_add_distrib] using Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hj j)
  · exact (h rfl).elim

/-- The empty compressed-oracle family has total database size zero. -/
theorem compressedVCOracle_initial_totalSize :
    QuerySupportedOn (fun D : Fin k → Database X Y ↦ ∑ i, (D i).size) (Set.Iic 0)
      (compressedVCOracle k X Y).init.matrix := by
  change QuerySupportedOn _ _
    (SubState.basis (fun _ : Fin k ↦ (Database.empty : Database X Y))).matrix
  rw [SubState.matrix_basis]
  intro a b hab
  rw [Matrix.single_apply] at hab
  split_ifs at hab with he
  · rcases he with ⟨rfl, rfl⟩
    simp [Database.size]
  · exact (hab rfl).elim

/-- Mixed P5 with coefficient 24 from occupied-key joint-label instabilities.
The recording argument follows Chiesa, Di, Hu and Zheng, ePrint 2025/2166, Lemma 9.7.
Empty occupied sets
contribute zero, and nonempty sectors are combined by a maximum, without measuring their keys. -/
theorem compressed_online_of_instability [OracleSpec.UniformAnswerMeasure (X →ₒ Y)]
    (ME : MultiExtractor k Cm Dm (Fin k → Database X Y)) (code : TpDCode k Dm Z)
    (rate : ℕ → ℝ) (hrate : ∀ j, 0 ≤ rate j)
    (hi : ∀ (t : ℕ) (i : Fin k) (keys : Finset (TpIC k Cm)),
      1 ≤ keys.card → keys.card ≤ t → ∀ Dfix : Fin k → Database X Y,
        24 * (Database.instability
          (fun D ↦ fun q : keys ↦ ME.extract q.1 (Function.update Dfix i D))
          (t - keys.card + 1)).toReal ≤ rate t) :
    OnlineIndistinguishable.{v, w} (compressedVCOracle k X Y) ME code
      (fun t wVC _ _ ↦ min 1
        ((∑ j ∈ Finset.range t, ENNReal.ofReal (rate j)) * min wVC (t : ℝ≥0∞))) := by
  apply VCOracle.onlineIndistinguishable_of_recording_source_bounds
    (compressedVCOracle k X Y) ME code (fun D ↦ ∑ i, (D i).size)
    (compressedVCOracle_U_totalSize_le) compressedReadProjector_totalSize_le
    compressedVCOracle_initial_totalSize rate hrate
  · intro Cell _ _ bot j i
    exact l2_opNorm_compressed_recordingDefect_source_sq_le ME bot i j (rate j) (hrate j)
      (hi j i)
  · intro Cell _ _ bot j c
    exact l2_opNorm_compressed_readRecordingDefect_source_sq_le ME bot c.1 c.2 j
      (rate j) (hrate j) (hi j c.1)
end

end Quantum
