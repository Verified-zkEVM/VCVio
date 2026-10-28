/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.Proximity.Functional

/-! # Affine-table interpretation of Proximity's bad reduction

The challenge and the independently chosen signing secret are kept distinct. Two independent
uniform scalar tables supply the hidden slopes and masks used by affine extraction.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace Proximity.AGM

private theorem pair_tables {F ι : Type} [SampleableType F] [Fintype ι] [DecidableEq ι] :
    (do let a ← $ᵗ (ι → F); let b ← $ᵗ (ι → F); return fun i => (a i, b i)) =ᵈ
      ($ᵗ (ι → F × F) : ProbComp _) := by
  apply SampleableType.evalDistEq_uniformSample_pair_of_bijective
  constructor
  · intro ⟨a, b⟩ ⟨c, d⟩ h
    exact Prod.ext (funext fun i => congrArg Prod.fst (congrFun h i))
      (funext fun i => congrArg Prod.snd (congrFun h i))
  · intro ρ
    exact ⟨(fun i => (ρ i).1, fun i => (ρ i).2), rfl⟩

private theorem table_pair {F I : Type} [Zero F] [DecidableEq I]
    (S : Finset I) (a b : S → F) (i : I) :
    extendTable S (0, 0) (fun j => (a j, b j)) i =
      (extendTable S 0 a i, extendTable S 0 b i) := by
  simp only [GroupModel.LinearFunctional.extendTable]
  split <;> rfl

private theorem table_affine {F I : Type} [Ring F] [DecidableEq I]
    (S : Finset I) (a b : S → F) (α : F) (i : I) :
    extendTable S 0 (fun j => a j * α + b j) i =
      extendTable S 0 a i * α + extendTable S 0 b i := by
  simp only [GroupModel.LinearFunctional.extendTable]
  split <;> simp

/-- Weighted evaluation of a pair table is componentwise. -/
theorem value_pair {F I : Type} [CommSemiring F] (a b : I → F) (ts : List (I × F)) :
    Weighted.value (fun i => (a i, b i)) ts = (Weighted.value a ts, Weighted.value b ts) := by
  apply Prod.ext
  · exact (Weighted.value_map (LinearMap.fst F F F) (fun i => (a i, b i)) ts).symm
  · exact (Weighted.value_map (LinearMap.snd F F F) (fun i => (a i, b i)) ts).symm

/-- Weighted evaluation commutes with affine masking of scalar tables. -/
theorem value_affine {F I : Type} [CommSemiring F]
    (a b : I → F) (α : F) (ts : List (I × F)) :
    Weighted.value (fun i => a i * α + b i) ts =
      Weighted.value a ts * α + Weighted.value b ts := by
  have h := Weighted.value_map
    ((LinearMap.fst F F F).smulRight α + LinearMap.snd F F F) (fun i => (a i, b i)) ts
  simpa only [value_pair, LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, smul_eq_mul] using h

/-- The named bad reduction extracts the affine gap from two independent finite tables. -/
theorem badReduction_table {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ}
    [Field F] [SampleableType F] [DecidableEq Slot]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂) (α : F)
    (S : Finset (Index Slot dimension))
    (hS : ∀ κ : F, WeightedInterfaceCovered S terms (fun out => out.value.data)
      (A.rawMain (κ • g₂))) :
    badReduction A g₁ (α • g₁) g₂ (α • g₂) =ᵈ (do
      let κ ← $ᵗ F
      let a ← $ᵗ (S → F); let b ← $ᵗ (S → F)
      let ρ := extendTable S 0 (fun i => a i * α + b i)
      let z ← weightedFixedRun (fun i => ρ i • g₁)
        (fun m => Weighted.value ρ (terms m) • (κ • g₁)) (A.rawMain (κ • g₂))
      return (0 - ∑ i, gap S z i * b i) / (∑ i, gap S z i * a i)) := by
  unfold badReduction
  apply _root_.EvalDistEq.bind_right
  intro κ
  refine (badProgram_rom_table A α κ S (hS κ)).trans ?_
  have ht := (pair_tables (F := F) (ι := S)).bind_left (fun ab => do
    let table := extendTable S (0, 0) ab
    let point := fun r : F × F => r.1 • (α • g₁) + r.2 • g₁
    let z ← weightedFixedRun (point ∘ table)
      (fun m => κ • point (Weighted.value table (terms m))) (A.rawMain (κ • g₂))
    let repr := evaluate (coefficients z.1) ([(0, 0)] ++ z.2.map
      (Sum.elim (fun _ => ((0 : F), (0 : F))) (fun m => Weighted.value table (terms m))))
    let target := Weighted.value table (terms z.1.value.data)
    return (repr.2 - target.2) / (target.1 - repr.1))
  simp only [bind_assoc, pure_bind] at ht
  refine ht.symm.trans ?_
  apply _root_.EvalDistEq.bind_right
  intro a
  apply _root_.EvalDistEq.bind_right
  intro b
  have hp : extendTable S (0, 0) (fun i => (a i, b i)) =
      fun i => (extendTable S 0 a i, extendTable S 0 b i) := by
    funext i
    exact table_pair S a b i
  have ha : extendTable S 0 (fun i => a i * α + b i) =
      fun i => extendTable S 0 a i * α + extendTable S 0 b i := by
    funext i
    exact table_affine S a b α i
  rw [hp, ha]
  simp only [value_pair, value_affine, Function.comp_def]
  have hs (m : Proximity.Message F Slot dimension) :
      κ • (Weighted.value (extendTable S 0 a) (terms m) • α • g₁ +
        Weighted.value (extendTable S 0 b) (terms m) • g₁) =
      (Weighted.value (extendTable S 0 a) (terms m) * α +
        Weighted.value (extendTable S 0 b) (terms m)) • κ • g₁ := by
    simp only [smul_smul, ← add_smul]
    congr 1
    ring
  simp only [hs, add_smul, mul_smul, bind_pure_comp]
  convert _root_.EvalDistEq.refl _ using 1
  congr 1
  funext z
  rw [functional_bad]
  simp only [gap, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib,
    ← tableEval_apply, tableEval_weights]
  congr 1
  ring

end Proximity.AGM
