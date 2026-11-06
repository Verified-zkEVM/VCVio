/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

module

public import VCVio.EvalDist.EvalDistEq
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.EvalDist.DiscreteTVDistBind

/-!
# Total variation of coordinatewise maps of uniform tables

The total variation between a coordinatewise map of a uniform dependent table and the uniform
target table is at most the sum of the coordinatewise losses.
-/

public section

open OracleComp SampleableType
open scoped ENNReal

noncomputable section

namespace OracleComp

-- Split each uniform table into its first cell and its remaining cells. This retains the
-- entire dependent output tuple while reducing its distance to the independent-pair bound.
private theorem discreteTVDist_map_uniform_cons_le (k : ℕ) (A B : Fin (k + 1) → Type)
    [∀ i, SampleableType (A i)] [∀ i, SampleableType (B i)]
    [SampleableType ((i : Fin (k + 1)) → A i)]
    [SampleableType ((i : Fin (k + 1)) → B i)]
    [SampleableType ((i : Fin k) → A i.succ)]
    [SampleableType ((i : Fin k) → B i.succ)]
    (f : (i : Fin (k + 1)) → B i → A i) :
    discreteTVDist ((fun b i => f i (b i)) <$> ($ᵗ ((i : Fin (k + 1)) → B i)))
        ($ᵗ ((i : Fin (k + 1)) → A i)) ≤
      discreteTVDist (f 0 <$> ($ᵗ (B 0))) ($ᵗ (A 0)) +
        discreteTVDist ((fun b i => f i.succ (b i)) <$> ($ᵗ ((i : Fin k) → B i.succ)))
          ($ᵗ ((i : Fin k) → A i.succ)) := by
  have hsplit (C : Fin (k + 1) → Type) [∀ i, SampleableType (C i)]
      [SampleableType ((i : Fin (k + 1)) → C i)]
      [SampleableType ((i : Fin k) → C i.succ)] (P : ((i : Fin (k + 1)) → C i) → Prop) :
      Pr{let x ← $ᵗ (C 0); let xs ← $ᵗ ((i : Fin k) → C i.succ)}[
        P (Fin.consEquiv C (x, xs))] = Pr{let c ← $ᵗ ((i : Fin (k + 1)) → C i)}[P c] :=
    SampleableType.prEvent_uniformSample_pair_of_bijective
      (g := fun x xs => Fin.consEquiv C (x, xs)) (Fin.consEquiv C).bijective P
  have hcons (x : B 0) (xs : (i : Fin k) → B i.succ) :
      (fun i => f i (Fin.consEquiv B (x, xs) i)) =
        Fin.consEquiv A (f 0 x, fun i => f i.succ (xs i)) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  calc
    discreteTVDist ((fun b i => f i (b i)) <$> ($ᵗ ((i : Fin (k + 1)) → B i)))
        ($ᵗ ((i : Fin (k + 1)) → A i)) =
      discreteTVDist
        (Fin.consEquiv A <$> (do
          let x ← f 0 <$> ($ᵗ (B 0))
          let xs ← (fun b i => f i.succ (b i)) <$> ($ᵗ ((i : Fin k) → B i.succ))
          pure (x, xs)))
        (Fin.consEquiv A <$> (do
          let x ← $ᵗ (A 0)
          let xs ← $ᵗ ((i : Fin k) → A i.succ)
          pure (x, xs))) := by
        refine discreteTVDist.congr_evalDistEq (.of_forall_prEvent_eq fun P => ?_)
          (.of_forall_prEvent_eq fun P => ?_)
        · simp only [prEvent_norm]
          rw [← hsplit B (fun b => P (fun i => f i (b i)))]
          simp only [hcons]
        · simpa only [prEvent_norm] using (hsplit A P).symm
    _ ≤ discreteTVDist (f 0 <$> ($ᵗ (B 0))) ($ᵗ (A 0)) +
        discreteTVDist ((fun b i => f i.succ (b i)) <$> ($ᵗ ((i : Fin k) → B i.succ)))
          ($ᵗ ((i : Fin k) → A i.succ)) := by
      refine (discreteTVDist.map_le
        (α := A 0 × ((i : Fin k) → A i.succ)) _ _ (Fin.consEquiv A)).trans ?_
      exact discreteTVDist.pair_le _ _ _ _

private theorem discreteTVDist_map_uniform_fin_le_sum (k : ℕ) (A B : Fin k → Type)
    [∀ i, SampleableType (A i)] [∀ i, SampleableType (B i)]
    [SampleableType ((i : Fin k) → A i)] [SampleableType ((i : Fin k) → B i)]
    (f : (i : Fin k) → B i → A i) :
    discreteTVDist ((fun b i => f i (b i)) <$> ($ᵗ ((i : Fin k) → B i)))
        ($ᵗ ((i : Fin k) → A i)) ≤
      ∑ i, discreteTVDist (f i <$> ($ᵗ (B i))) ($ᵗ (A i)) := by
  classical
  induction k with
  | zero =>
    rw [Fin.sum_univ_zero]
    apply le_of_eq
    refine discreteTVDist.eq_zero_of_evalDistEq (evalDistEq_iff_forall_prEvent_eq_output.mpr
      fun a => ?_)
    rw [prEvent_map]
    exact ((SampleableType.prEvent_uniformSample_eq_one_iff _).mpr
      (fun _ => Subsingleton.elim _ _)).trans
        ((SampleableType.prEvent_uniformSample_eq_one_iff _).mpr
          (fun _ => Subsingleton.elim _ _)).symm
  | succ k ih =>
    let : ∀ i, Fintype (A i) := fun _ => Fintype.ofFinite _
    let : ∀ i, Fintype (B i) := fun _ => Fintype.ofFinite _
    let : SampleableType ((i : Fin k) → A i.succ) := SampleableType.ofFintype _
    let : SampleableType ((i : Fin k) → B i.succ) := SampleableType.ofFintype _
    refine (discreteTVDist_map_uniform_cons_le k A B f).trans ?_
    rw [Fin.sum_univ_succ]
    exact add_le_add le_rfl (ih _ _ _)

/-- Total variation between coordinatewise decoding of a uniform dependent product and the
uniform target product is at most the sum of the coordinatewise losses. -/
theorem discreteTVDist_map_uniform_pi_le_sum
    {I : Type} [Fintype I]
    (A B : I → Type)
    [∀ i, SampleableType (A i)] [∀ i, SampleableType (B i)]
    [SampleableType ((i : I) → A i)] [SampleableType ((i : I) → B i)]
    (f : (i : I) → B i → A i) (error : I → ℝ)
    (h : ∀ i, discreteTVDist (f i <$> ($ᵗ (B i))) ($ᵗ (A i)) ≤ error i) :
    discreteTVDist
        ((fun b i => f i (b i)) <$> ($ᵗ ((i : I) → B i)))
        ($ᵗ ((i : I) → A i)) ≤
      ∑ i, error i := by
  classical
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let : ∀ i, Fintype (A i) := fun _ => Fintype.ofFinite _
  let : ∀ i, Fintype (B i) := fun _ => Fintype.ofFinite _
  let : SampleableType ((j : Fin (Fintype.card I)) → A (e j)) := SampleableType.ofFintype _
  let : SampleableType ((j : Fin (Fintype.card I)) → B (e j)) := SampleableType.ofFintype _
  let reindex (C : I → Type) := Equiv.piCongrLeft C e
  have hmap (b : (j : Fin (Fintype.card I)) → B (e j)) :
      reindex A (fun j => f (e j) (b j)) = fun i => f i (reindex B b i) := by
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    simp [reindex]
  calc
    _ = discreteTVDist
        (reindex A <$> ((fun b j => f (e j) (b j)) <$> ($ᵗ ((j : Fin (Fintype.card I)) → B (e j)))))
        (reindex A <$> ($ᵗ ((j : Fin (Fintype.card I)) → A (e j)))) := by
      refine discreteTVDist.congr_evalDistEq (.of_forall_prEvent_eq fun P => ?_)
        (.of_forall_prEvent_eq fun P => ?_)
      · simp only [prEvent_map, hmap]
        exact (SampleableType.prEvent_uniformSample_equiv (reindex B)
          (fun b => P (fun i => f i (b i)))).symm
      · rw [prEvent_map]
        exact (SampleableType.prEvent_uniformSample_equiv (reindex A) P).symm
    _ ≤ discreteTVDist
        ((fun b j => f (e j) (b j)) <$> ($ᵗ ((j : Fin (Fintype.card I)) → B (e j))))
        ($ᵗ ((j : Fin (Fintype.card I)) → A (e j))) := discreteTVDist.map_le _ _ _
    _ ≤ ∑ j, discreteTVDist (f (e j) <$> ($ᵗ (B (e j)))) ($ᵗ (A (e j))) :=
      discreteTVDist_map_uniform_fin_le_sum _ _ _ _
    _ ≤ ∑ j, error (e j) := Finset.sum_le_sum fun j _ => h (e j)
    _ = ∑ i, error i := e.sum_comp error

end OracleComp
