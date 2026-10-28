/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericUber
public import VCVio.CryptoFoundations.GroupModel.DecisionalPairing
import Mathlib.Data.List.GetD
import all VCVio.CryptoFoundations.GroupModel.Instances

/-! # Generic decisional uber bounds

At Type 3, adjoining any target outside the initial accessible span adds one independent
coordinate to the target relation kernel. A fresh polynomial variable supplies the random
challenge. T7 then bounds distinguishing advantage by the two sorted collision sums.
-/

public section

open OracleComp OracleSpec MeasureTheory MvPolynomial
open scoped ENNReal


namespace GroupModel

variable {F ι : Type}

private theorem evRepr_append_singleton [Field F] (Q : List (MvPolynomial ι F))
    (f : MvPolynomial ι F) (r : Repr F) :
    evRepr (Q ++ [f]) r = evRepr Q r + r Q.length • f := by
  rw [evRepr_apply, evRepr_apply, List.length_append, List.length_singleton,
    Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hi)]
  · rw [List.getD_append_right _ _ _ _ le_rfl]
    simp

private theorem evReprT_append_singleton [Field F] (P R Q : List (MvPolynomial ι F))
    (f : MvPolynomial ι F) (r : ReprT F) :
    evReprT (LinearMap.mul F _) P R (Q ++ [f]) r =
      evReprT (LinearMap.mul F _) P R Q r + r.1 Q.length • f := by
  simp only [evReprT_apply, evRepr_append_singleton]
  ac_rfl

private theorem evReprT_mem [Field F] (P R Q : List (MvPolynomial ι F)) (r : ReprT F) :
    evReprT (LinearMap.mul F _) P R Q r ∈ accessibleSpan pairingSig (uberTable P R Q) .gₜ := by
  let V := accessibleSpan pairingSig (uberTable P R Q)
  have hm : ∀ s p, p ∈ uberTable P R Q s → p ∈ V s := fun s _ hp =>
    mem_accessibleSpan _ _ s hp
  have hl := lookup_mem_submodule hm
  rw [evReprT_apply, evRepr_apply]
  apply (V .gₜ).add_mem
  · exact (V .gₜ).sum_mem (fun i _ => (V .gₜ).smul_mem _ (hl .gₜ i))
  · apply (V .gₜ).sum_mem
    intro i _
    apply (V .gₜ).sum_mem
    intro j _
    exact (V .gₜ).smul_mem _ ((accessibleSpan_spanClosed pairingSig _).2 () _ _
      (hl .g₁ i) (hl .g₂ j))

private theorem add_smul_eq_zero_iff [Field F] (V : Submodule F (MvPolynomial ι F))
    {p f : MvPolynomial ι F} (hp : p ∈ V) (hf : f ∉ V) (c : F) :
    p + c • f = 0 ↔ p = 0 ∧ c = 0 := by
  constructor
  · intro h
    have hc : c = 0 := by
      by_contra hc
      apply hf
      have hm : c • f ∈ V := by rw [eq_neg_of_add_eq_zero_right h]; exact V.neg_mem hp
      simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using V.smul_mem c⁻¹ hm
    exact ⟨by simpa [hc] using h, hc⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- Appending either of two targets outside the initial accessible span gives the same
Type 3 relation kernel, without independence assumptions on the original lists. -/
theorem uberTables_sameKernel_of_not_mem [Field F] (P R Q : List (MvPolynomial ι F))
    (f g : MvPolynomial ι F)
    (hf : f ∉ accessibleSpan pairingSig (uberTable P R Q) .gₜ)
    (hg : g ∉ accessibleSpan pairingSig (uberTable P R Q) .gₜ) :
    SameKernel.pairing (uberTable P R (Q ++ [f])) (uberTable P R (Q ++ [g])) := by
  refine ⟨fun s => by cases s <;> simp [uberTable], ?_⟩
  intro s r
  cases s with
  | g₁ | g₂ => rfl
  | gₜ =>
    change ReprT F at r
    change evReprT _ P R (Q ++ [f]) r = 0 ↔ evReprT _ P R (Q ++ [g]) r = 0
    rw [evReprT_append_singleton, evReprT_append_singleton,
      add_smul_eq_zero_iff _ (evReprT_mem P R Q r) hf,
      add_smul_eq_zero_iff _ (evReprT_mem P R Q r) hg]

private theorem map_mem_accessibleSpan [CommSemiring F] {κ : Type}
    (φ : MvPolynomial ι F →ₐ[F] MvPolynomial κ F)
    (tbl : Tbl (fun _ : PSort => MvPolynomial ι F)) (s : PSort)
    {p : MvPolynomial ι F} (hp : p ∈ accessibleSpan pairingSig tbl s) :
    φ p ∈ accessibleSpan pairingSig (mapTbl (fun _ => φ) tbl) s := by
  let V := accessibleSpan pairingSig (mapTbl (fun _ => φ) tbl)
  apply accessibleSpan_le pairingSig tbl (fun s => (V s).comap φ.toLinearMap) ?_ ?_ s hp
  · refine ⟨fun o => o.elim, ?_⟩
    intro o p q hp hq
    change φ (p * q) ∈ V .gₜ
    rw [map_mul]
    exact (accessibleSpan_spanClosed pairingSig _).2 () _ _ hp hq
  · intro t q hq
    exact mem_accessibleSpan _ _ t (List.mem_map.mpr ⟨q, hq, rfl⟩)

private noncomputable def specialize [CommSemiring F] (c : MvPolynomial ι F) :
    MvPolynomial (Option ι) F →ₐ[F] MvPolynomial ι F := aeval (fun z => Option.elim z c X)

private theorem specialize_rename [CommSemiring F] (c p : MvPolynomial ι F) :
    specialize c (rename some p) = p := by
  simp [specialize, aeval_def, eval₂_rename, Function.comp_def]

/-- Renaming the original variables preserves target non-membership in the Type 3 span. -/
theorem rename_not_mem_accessibleSpan [Field F] (P R Q : List (MvPolynomial ι F))
    (f : MvPolynomial ι F) (hf : f ∉ accessibleSpan pairingSig (uberTable P R Q) .gₜ) :
    rename some f ∉ accessibleSpan pairingSig
      (uberTable (P.map (rename some)) (R.map (rename some)) (Q.map (rename some))) .gₜ := by
  intro h
  have hm := map_mem_accessibleSpan (specialize (0 : MvPolynomial ι F)) _ .gₜ h
  have ht : mapTbl (fun _ => specialize (0 : MvPolynomial ι F))
      (uberTable (P.map (rename some)) (R.map (rename some)) (Q.map (rename some))) =
      uberTable P R Q := by
    funext s
    cases s <;> simp [mapTbl, uberTable, List.map_map, specialize_rename, Function.comp_def]
  rw [ht, specialize_rename] at hm
  exact hf hm

/-- The fresh variable is outside every accessible span generated by the old variables. -/
theorem fresh_not_mem_accessibleSpan [Field F] (P R Q : List (MvPolynomial ι F)) :
    X none ∉ accessibleSpan pairingSig
      (uberTable (P.map (rename some)) (R.map (rename some)) (Q.map (rename some))) .gₜ := by
  let φ₀ := specialize (0 : MvPolynomial ι F)
  let φ₁ := specialize (1 : MvPolynomial ι F)
  let V := LinearMap.ker (φ₀.toLinearMap - φ₁.toLinearMap)
  have hmem (p : MvPolynomial (Option ι) F) : p ∈ V ↔ φ₀ p = φ₁ p := by
    simp [V, LinearMap.mem_ker, sub_eq_zero]
  have hV : pairingSig.SpanClosed (fun _ => V) := by
    refine ⟨fun o => o.elim, ?_⟩
    intro o p q hp hq
    rw [hmem] at hp hq ⊢
    simp only [map_mul, hp, hq]
  have ht : ∀ s p, p ∈ uberTable (P.map (rename some)) (R.map (rename some))
      (Q.map (rename some)) s → p ∈ V := by
    intro s p hp
    rw [hmem]
    cases s <;> obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp <;>
      simp only [φ₀, φ₁, specialize_rename]
  intro h
  have hh := (hmem _).mp (accessibleSpan_le _ _ (fun _ => V) hV ht .gₜ h)
  simp [φ₀, φ₁, specialize] at hh

/-- Real and fresh-variable uber challenge tables have equal relation kernels whenever
the target lies outside the accessible span of the original Type 3 tables. -/
theorem uberTables_sameKernel [Field F] (P R Q : List (MvPolynomial ι F))
    (f : MvPolynomial ι F) (hf : f ∉ accessibleSpan pairingSig (uberTable P R Q) .gₜ) :
    SameKernel.pairing
      (uberTable (P.map (rename some)) (R.map (rename some))
        (Q.map (rename some) ++ [rename some f]))
      (uberTable (P.map (rename some)) (R.map (rename some))
        (Q.map (rename some) ++ [X none])) :=
  uberTables_sameKernel_of_not_mem _ _ _ _ _
    (rename_not_mem_accessibleSpan P R Q f hf) (fresh_not_mem_accessibleSpan P R Q)

private theorem uberTable_degreeLE_rename_append [Field F]
    (P R Q : List (MvPolynomial ι F)) {D : PSort → ℕ}
    (hd : DegreeLE D (uberTable P R Q)) (t : MvPolynomial (Option ι) F)
    (ht : t.totalDegree ≤ D .gₜ) :
    DegreeLE D (uberTable (P.map (rename some)) (R.map (rename some))
      (Q.map (rename some) ++ [t])) := by
  intro s p hp
  cases s with
  | g₁ =>
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact (totalDegree_rename_le _ _).trans (hd .g₁ q hq)
  | g₂ =>
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact (totalDegree_rename_le _ _).trans (hd .g₂ q hq)
  | gₜ =>
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact (totalDegree_rename_le _ _).trans (hd .gₜ q hq)
    · exact (List.mem_singleton.mp hp) ▸ ht

end GroupModel

namespace Uber

open GroupModel

variable {F G₁ G₂ Gₜ : Type}

private theorem uniform_option [SampleableType F] {v : ℕ} :
    (do let x ← $ᵗ (Fin v → F); let y ← $ᵗ F
        pure (fun z => Option.elim z y x)) =ᵈ ($ᵗ (Option (Fin v) → F) : ProbComp _) := by
  apply EvalDistEq.of_forall_prEvent_eq
  intro p
  have hb : Function.Bijective
      (Function.uncurry (fun (x : Fin v → F) (y : F) => fun z => Option.elim z y x)) := by
    constructor
    · intro a b h
      exact Prod.ext (funext (fun i => congrFun h (some i))) (congrFun h none)
    · intro z
      exact ⟨(fun i => z (some i), z none), by funext i; cases i <;> rfl⟩
  simpa only [SampleableType.uniformSample_prod_eq_bind, prEvent_norm] using
    SampleableType.prEvent_uniformSample_pair_of_bijective hb p

private theorem runGen_uber_challenge [Field F] [DecidableEq F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    {v : ℕ} (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (P R Q : List (MvPolynomial (Fin v) F)) (t : MvPolynomial (Option (Fin v)) F)
    (A : OracleComp (genSpec F pairingSig) Bool) (x : Option (Fin v) → F) :
    DecisionalAdversary.ofGeneric e A
      (P.map (fun p => MvPolynomial.eval (x ∘ some) p • g₁))
      (R.map (fun p => MvPolynomial.eval (x ∘ some) p • g₂))
      (Q.map (fun p => MvPolynomial.eval (x ∘ some) p • e g₁ g₂))
      (MvPolynomial.eval x t • e g₁ g₂) =
    Prod.fst <$> runGen (symbolic F pairingSig (Option (Fin v)))
      (fun _ p => MvPolynomial.eval x p) A
      (uberTable (P.map (rename some)) (R.map (rename some))
        (Q.map (rename some) ++ [t])) := by
  have ht : mapTbl (fun s => (evalHom.pairing e g₁ g₂ x).toFun s)
      (uberTable (P.map (rename some)) (R.map (rename some))
        (Q.map (rename some) ++ [t])) =
      (fun | .g₁ => P.map (fun p => MvPolynomial.eval (x ∘ some) p • g₁)
           | .g₂ => R.map (fun p => MvPolynomial.eval (x ∘ some) p • g₂)
           | .gₜ => Q.map (fun p => MvPolynomial.eval (x ∘ some) p • e g₁ g₂) ++
               [MvPolynomial.eval x t • e g₁ g₂]) := by
    rw [mapTbl_uberTable_evalHom]
    funext s
    cases s with
    | g₁ =>
      change ((P.map (rename some)).map (fun p => MvPolynomial.eval x p • g₁) : List G₁) = _
      simp only [List.map_map, Function.comp_def, eval_rename]
      rfl
    | g₂ =>
      change ((R.map (rename some)).map (fun p => MvPolynomial.eval x p • g₂) : List G₂) = _
      simp only [List.map_map, Function.comp_def, eval_rename]
      rfl
    | gₜ =>
      change ((Q.map (rename some) ++ [t]).map
        (fun p => MvPolynomial.eval x p • e g₁ g₂) : List Gₜ) = _
      simp only [List.map_append, List.map_cons, List.map_nil, List.map_map,
        Function.comp_def, eval_rename]
  unfold DecisionalAdversary.ofGeneric
  erw [← ht]
  rw [runGen_pairing_mapTbl_evalHom e g₁ g₂ hg₁ hg₂ he]
  simp only [Functor.map_map, Prod.map, id_eq]

private theorem real_experiment_evalDistEq [Field F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    {v : ℕ} (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (P R Q : List (MvPolynomial (Fin v) F)) (f : MvPolynomial (Fin v) F)
    (A : OracleComp (genSpec F pairingSig) Bool) :
    realExperiment e g₁ g₂ P R Q f (DecisionalAdversary.ofGeneric e A) =ᵈ
      (do let x ← $ᵗ (Option (Fin v) → F)
          Prod.fst <$> runGen (symbolic F pairingSig (Option (Fin v)))
            (fun _ p => MvPolynomial.eval x p) A
            (uberTable (P.map (rename some)) (R.map (rename some))
              (Q.map (rename some) ++ [rename some f]))) := by
  let run (x : Option (Fin v) → F) := DecisionalAdversary.ofGeneric e A
    (P.map (fun p => MvPolynomial.eval (x ∘ some) p • g₁))
    (R.map (fun p => MvPolynomial.eval (x ∘ some) p • g₂))
    (Q.map (fun p => MvPolynomial.eval (x ∘ some) p • e g₁ g₂))
    (MvPolynomial.eval (x ∘ some) f • e g₁ g₂)
  have hs := (uniform_option (F := F) (v := v)).bind_left run
  have hc := EvalDistEq.bind_right ($ᵗ (Fin v → F) : ProbComp _) (fun x =>
    OracleComp.EvalDistEq.bind_const ($ᵗ F) (run (fun z => Option.elim z 0 x)))
  have heq := hc.symm.trans (by
    simpa only [bind_assoc, pure_bind, run, Function.comp_def, Option.elim_some] using hs)
  have hr (x : Option (Fin v) → F) : run x =
      Prod.fst <$> runGen (symbolic F pairingSig (Option (Fin v)))
        (fun _ p => MvPolynomial.eval x p) A
        (uberTable (P.map (rename some)) (R.map (rename some))
          (Q.map (rename some) ++ [rename some f])) := by
    simpa only [run, eval_rename] using
      runGen_uber_challenge e g₁ g₂ hg₁ hg₂ he P R Q (rename some f) A x
  apply EvalDistEq.of_forall_prEvent_eq
  intro p
  simpa only [realExperiment, ← hr, run, Function.comp_def, Option.elim_some, prEvent_norm]
    using heq.prEvent_eq p

private theorem random_experiment_evalDistEq [Field F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    {v : ℕ} (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (P R Q : List (MvPolynomial (Fin v) F)) (A : OracleComp (genSpec F pairingSig) Bool) :
    randomExperiment e g₁ g₂ P R Q (DecisionalAdversary.ofGeneric e A) =ᵈ
      (do let x ← $ᵗ (Option (Fin v) → F)
          Prod.fst <$> runGen (symbolic F pairingSig (Option (Fin v)))
            (fun _ p => MvPolynomial.eval x p) A
            (uberTable (P.map (rename some)) (R.map (rename some))
              (Q.map (rename some) ++ [X none]))) := by
  have hs := (uniform_option (F := F) (v := v)).bind_left (fun x =>
    DecisionalAdversary.ofGeneric e A
      (P.map (fun p => MvPolynomial.eval (x ∘ some) p • g₁))
      (R.map (fun p => MvPolynomial.eval (x ∘ some) p • g₂))
      (Q.map (fun p => MvPolynomial.eval (x ∘ some) p • e g₁ g₂)) (x none • e g₁ g₂))
  apply EvalDistEq.of_forall_prEvent_eq
  intro p
  simpa only [randomExperiment, bind_assoc, pure_bind, Function.comp_def,
    Option.elim_some, Option.elim_none, prEvent_norm,
    ← runGen_uber_challenge e g₁ g₂ hg₁ hg₂ he, eval_X] using hs.prEvent_eq p

/-- The Type 3 decisional uber advantage is at most the two sorted collision sums.
The real profile bounds the target polynomial, and the random profile bounds a fresh
variable. Neither profile requires independence among the initially supplied lists. -/
theorem advantage_ofGeneric_le [Field F] [Fintype F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    {v : ℕ} (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (P R Q : List (MvPolynomial (Fin v) F)) (f : MvPolynomial (Fin v) F)
    (hf : f ∉ accessibleSpan pairingSig (uberTable P R Q) .gₜ)
    {D₀ D₁ n : PSort → ℕ} (hD₀ : pairingSig.DegreeClosed D₀)
    (hD₁ : pairingSig.DegreeClosed D₁)
    (hd₀ : DegreeLE D₀ (uberTable P R Q)) (hd₁ : DegreeLE D₁ (uberTable P R Q))
    (hdeg : f.totalDegree ≤ D₀ .gₜ) (hone : 1 ≤ D₁ .gₜ)
    (A : OracleComp (genSpec F pairingSig) Bool)
    (hn : ∀ s, IsQueryBoundP A (appendsTo s) (n s)) :
    advantage e g₁ g₂ P R Q f (DecisionalAdversary.ofGeneric e A) ≤
      ((((P.length + n .g₁ + 1).choose 2 * (D₀ .g₁ + D₁ .g₁) +
        (R.length + n .g₂ + 1).choose 2 * (D₀ .g₂ + D₁ .g₂) +
        (Q.length + n .gₜ + 2).choose 2 * (D₀ .gₜ + D₁ .gₜ) : ℕ) : ℝ≥0∞) /
          Fintype.card F) := by
  classical
  let : Fintype PSort := ⟨{.g₁, .g₂, .gₜ}, by intro s; cases s <;> simp⟩
  let : MeasurableSpace ((Option (Fin v) → F) × Bool) := ⊤
  let T₀ := uberTable (P.map (rename some)) (R.map (rename some))
    (Q.map (rename some) ++ [rename some f])
  let T₁ := uberTable (P.map (rename some)) (R.map (rename some))
    (Q.map (rename some) ++ [X none])
  let left : ProbComp ((Option (Fin v) → F) × Bool) := do
    let x ← $ᵗ (Option (Fin v) → F)
    let z ← runGen (symbolic F pairingSig (Option (Fin v)))
      (fun _ p => MvPolynomial.eval x p) A T₀
    pure (x, z.1)
  let right : ProbComp ((Option (Fin v) → F) × Bool) := do
    let x ← $ᵗ (Option (Fin v) → F)
    let z ← runGen (symbolic F pairingSig (Option (Fin v)))
      (fun _ p => MvPolynomial.eval x p) A T₁
    pure (x, z.1)
  have hl : realExperiment e g₁ g₂ P R Q f (DecisionalAdversary.ofGeneric e A) =ᵈ
      Prod.snd <$> left := by
    simpa only [left, map_bind, map_pure, bind_pure_comp, Functor.map_map, Function.comp_def]
      using real_experiment_evalDistEq e g₁ g₂ hg₁ hg₂ he P R Q f A
  have hr : randomExperiment e g₁ g₂ P R Q (DecisionalAdversary.ofGeneric e A) =ᵈ
      Prod.snd <$> right := by
    simpa only [right, map_bind, map_pure, bind_pure_comp, Functor.map_map, Function.comp_def]
      using random_experiment_evalDistEq e g₁ g₂ hg₁ hg₂ he P R Q A
  have hb := measureETVDist_runGen_pairing_sameKernel_uniform_le hD₀ hD₁ A hn T₀ T₁
    (uberTable_degreeLE_rename_append P R Q hd₀ _ ((totalDegree_rename_le _ _).trans hdeg))
    (uberTable_degreeLE_rename_append P R Q hd₁ _ (by simpa using hone))
    (uberTables_sameKernel P R Q f hf)
  rw [advantage, hl.evalDist_eq, hr.evalDist_eq]
  calc
    _ ≤ measureETVDist (Prod.snd <$> left) (Prod.snd <$> right) :=
      measure_absDiff_apply_le_measureETVDist _ _ (MeasurableSet.singleton true)
    _ ≤ measureETVDist left right := measureETVDist_map_le _ _ _ Measurable.of_discrete
    _ ≤ ∑ s, (((T₀ s).length + n s + 1).choose 2 : ℝ≥0∞) *
        ((D₀ s : ℝ≥0∞) / Fintype.card F + (D₁ s : ℝ≥0∞) / Fintype.card F) := hb
    _ = _ := by
      change (∑ s ∈ ({.g₁, .g₂, .gₜ} : Finset PSort),
        (((T₀ s).length + n s + 1).choose 2 : ℝ≥0∞) *
          ((D₀ s : ℝ≥0∞) / Fintype.card F + (D₁ s : ℝ≥0∞) / Fintype.card F)) = _
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      simp only [T₀, uberTable, List.length_map, List.length_append, List.length_singleton]
      rw [Nat.add_right_comm Q.length 1 (n .gₜ)]
      simp only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_add, Nat.cast_mul, div_eq_mul_inv]
      ring

/-- A total group-operation budget supplies each per-sort budget in the decisional uber bound. -/
theorem advantage_ofGeneric_le_of_total [Field F] [Fintype F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    {v : ℕ} (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (P R Q : List (MvPolynomial (Fin v) F)) (f : MvPolynomial (Fin v) F)
    (hf : f ∉ accessibleSpan pairingSig (uberTable P R Q) .gₜ)
    {D₀ D₁ : PSort → ℕ} (hD₀ : pairingSig.DegreeClosed D₀) (hD₁ : pairingSig.DegreeClosed D₁)
    (hd₀ : DegreeLE D₀ (uberTable P R Q)) (hd₁ : DegreeLE D₁ (uberTable P R Q))
    (hdeg : f.totalDegree ≤ D₀ .gₜ) (hone : 1 ≤ D₁ .gₜ)
    (A : OracleComp (genSpec F pairingSig) Bool) (q : ℕ)
    (hq : IsQueryBoundP A (fun i => isGroupOp i = true) q) :
    advantage e g₁ g₂ P R Q f (DecisionalAdversary.ofGeneric e A) ≤
      ((((P.length + q + 1).choose 2 * (D₀ .g₁ + D₁ .g₁) +
        (R.length + q + 1).choose 2 * (D₀ .g₂ + D₁ .g₂) +
        (Q.length + q + 2).choose 2 * (D₀ .gₜ + D₁ .gₜ) : ℕ) : ℝ≥0∞) /
          Fintype.card F) :=
  advantage_ofGeneric_le e g₁ g₂ hg₁ hg₂ he P R Q f hf hD₀ hD₁ hd₀ hd₁ hdeg hone A
    (n := fun _ => q) (fun s => hq.appendsTo s)

end Uber
