/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.DecisionalPairing
public import VCVio.CryptoFoundations.GroupModel.GenericDDH
public import VCVio.CryptoFoundations.GroupModel.GenericPairing
public import VCVio.CryptoFoundations.HardnessAssumptions.XDH
import all VCVio.CryptoFoundations.GroupModel.Instances

/-! # Generic hardness of external Diffie–Hellman

At the Type 3 pairing signature, DDH in the first source group remains generically hard
when the second generator and the pairing are public. The real and random accessible
spans have equal relation kernels, with degree bounds `(2, 0, 2)` and `(1, 0, 1)`.
-/

public section

open OracleComp OracleSpec MeasureTheory MvPolynomial GroupModel
open scoped ENNReal

namespace GroupModel

variable {F : Type}

/-- The symbolic XDH table with fourth first-source entry `p`, second generator `1`,
and no initially supplied target elements. -/
@[expose] noncomputable def xdhTable [Field F] (p : MvPolynomial (Fin 3) F) :
    Tbl (fun _ : PSort => MvPolynomial (Fin 3) F)
  | .g₁ => [1, X 0, X 1, p]
  | .g₂ => [1]
  | .gₜ => []

private theorem evReprT_xdhTable [Field F] (p : MvPolynomial (Fin 3) F) (r : ReprT F) :
    evReprT (LinearMap.mul F _) (xdhTable p .g₁) (xdhTable p .g₂)
      (xdhTable p .gₜ) r = evRepr (xdhTable p .g₁) (fun i => r.2 i 0) := by
  simp [evReprT_apply, evRepr_apply, xdhTable]

/-- The real and random XDH tables have the same accessible relation kernel.
Pairing with the sole second-source entry `1` preserves the first-source independent span. -/
theorem xdhTables_sameKernel [Field F] :
    SameKernel.pairing (xdhTable (X 0 * X 1 : MvPolynomial (Fin 3) F)) (xdhTable (X 2)) := by
  refine ⟨fun s => by cases s <;> rfl, ?_⟩
  intro s r
  cases s with
  | g₁ => exact (ddhTables_sameKernel (F := F) ()).2 r
  | g₂ => rfl
  | gₜ =>
    change ReprT F at r
    change evReprT _ _ _ _ r = 0 ↔ evReprT _ _ _ _ r = 0
    rw [evReprT_xdhTable, evReprT_xdhTable]
    exact (ddhTables_sameKernel (F := F) ()).2 (fun i => r.2 i 0)

/-- The real XDH table has per-sort degrees `(2, 0, 2)` and the random table
has per-sort degrees `(1, 0, 1)`. Both profiles are closed under the public pairing. -/
theorem xdhTables_degreeLE [Field F] :
    DegreeLE (fun | .g₁ => 2 | .g₂ => 0 | .gₜ => 2)
      (xdhTable (X 0 * X 1 : MvPolynomial (Fin 3) F)) ∧
    DegreeLE (fun | .g₁ => 1 | .g₂ => 0 | .gₜ => 1) (xdhTable (F := F) (X 2)) := by
  constructor
  · intro s p hp
    cases s with
    | g₁ => exact (ddhTables_degreeLE (F := F)).1 () p hp
    | g₂ =>
      have hp : p = 1 := by simpa [xdhTable] using hp
      simp [hp]
    | gₜ => simp [xdhTable] at hp
  · intro s p hp
    cases s with
    | g₁ => exact (ddhTables_degreeLE (F := F)).2 () p hp
    | g₂ =>
      have hp : p = 1 := by simpa [xdhTable] using hp
      simp [hp]
    | gₜ => simp [xdhTable] at hp

end GroupModel

namespace XDH

variable {F G₁ G₂ Gₜ : Type}

/-- Run a generic Boolean adversary on the four first-source XDH elements and the
second-source generator, with the supplied public pairing and an empty target table. -/
@[expose] def Adversary.ofGeneric [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (A : OracleComp (genSpec F pairingSig) Bool) :
    Adversary F G₁ G₂ :=
  fun g₁ X Y T g₂ => Prod.fst <$> runGen (pairingReal e) (fun _ => id) A
    (fun | .g₁ => [g₁, X, Y, T] | .g₂ => [g₂] | .gₜ => [])

/-- Three independent uniform samples form a uniform function on `Fin 3`. -/
theorem uniformSample_fin_three [SampleableType F] :
    (do let a ← $ᵗ F; let b ← $ᵗ F; let c ← $ᵗ F
        pure (![a, b, c] : Fin 3 → F)) =ᵈ ($ᵗ (Fin 3 → F) : ProbComp _) := by
  have hb : Function.Bijective (Function.uncurry
      (fun (a : F) (bc : F × F) => (![a, bc.1, bc.2] : Fin 3 → F))) := by
    constructor
    · intro a b h
      have h₀ := congrFun h 0
      have h₁ := congrFun h 1
      have h₂ := congrFun h 2
      apply Prod.ext
      · simpa [Function.uncurry] using h₀
      · exact Prod.ext (by simpa [Function.uncurry] using h₁) (by simpa [Function.uncurry] using h₂)
    · intro f
      refine ⟨(f 0, f 1, f 2), ?_⟩
      funext i
      fin_cases i <;> rfl
  apply EvalDistEq.of_forall_prEvent_eq
  intro p
  simpa only [SampleableType.uniformSample_prod_eq_bind, prEvent_norm] using
    SampleableType.prEvent_uniformSample_pair_of_bijective hb p

private theorem runGen_xdh [Field F] [DecidableEq F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0) (x : Fin 3 → F)
    (A : OracleComp (genSpec F pairingSig) Bool) (p : MvPolynomial (Fin 3) F) :
    Adversary.ofGeneric e A g₁ (x 0 • g₁) (x 1 • g₁) (MvPolynomial.eval x p • g₁) g₂ =
      Prod.fst <$> runGen (symbolic F pairingSig (Fin 3))
        (fun _ p => MvPolynomial.eval x p) A (xdhTable p) := by
  have ht : mapTbl (fun s => (evalHom.pairing e g₁ g₂ x).toFun s) (xdhTable p) =
      (fun | .g₁ => [g₁, x 0 • g₁, x 1 • g₁, MvPolynomial.eval x p • g₁]
           | .g₂ => [g₂] | .gₜ => []) := by
    funext s
    cases s <;> simp [mapTbl, xdhTable, evalAt_apply]
  unfold Adversary.ofGeneric
  rw [← ht, runGen_pairing_mapTbl_evalHom e g₁ g₂ hg₁ hg₂ he x A]
  simp only [Functor.map_map, Prod.map, id_eq]

private theorem real_experiment_evalDistEq [Field F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0) (A : OracleComp (genSpec F pairingSig) Bool) :
    realExperiment g₁ g₂ (Adversary.ofGeneric e A) =ᵈ
      (do let x ← $ᵗ (Fin 3 → F)
          Prod.fst <$> runGen (symbolic F pairingSig (Fin 3))
            (fun _ p => MvPolynomial.eval x p) A (xdhTable (X 0 * X 1))) := by
  have hs := (uniformSample_fin_three (F := F)).bind_left (fun x =>
    Adversary.ofGeneric e A g₁ (x 0 • g₁) (x 1 • g₁) ((x 0 * x 1) • g₁) g₂)
  have hc := EvalDistEq.bind_right ($ᵗ F : ProbComp F) (fun a =>
    EvalDistEq.bind_right ($ᵗ F : ProbComp F) (fun b =>
      OracleComp.EvalDistEq.bind_const ($ᵗ F)
        (Adversary.ofGeneric e A g₁ (a • g₁) (b • g₁) ((a * b) • g₁) g₂)))
  have heq := hc.symm.trans (by
    simpa only [bind_assoc, pure_bind, Matrix.cons_val_zero, Matrix.cons_val_one] using hs)
  apply EvalDistEq.of_forall_prEvent_eq
  intro p
  simpa [realExperiment, ← runGen_xdh e g₁ g₂ hg₁ hg₂ he, prEvent_norm] using
    heq.prEvent_eq p

private theorem random_experiment_evalDistEq [Field F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0) (A : OracleComp (genSpec F pairingSig) Bool) :
    randomExperiment g₁ g₂ (Adversary.ofGeneric e A) =ᵈ
      (do let x ← $ᵗ (Fin 3 → F)
          Prod.fst <$> runGen (symbolic F pairingSig (Fin 3))
            (fun _ p => MvPolynomial.eval x p) A (xdhTable (X 2))) := by
  have hs := (uniformSample_fin_three (F := F)).bind_left (fun x =>
    Adversary.ofGeneric e A g₁ (x 0 • g₁) (x 1 • g₁) (x 2 • g₁) g₂)
  apply EvalDistEq.of_forall_prEvent_eq
  intro p
  simpa [randomExperiment, ← runGen_xdh e g₁ g₂ hg₁ hg₂ he, prEvent_norm] using
    hs.prEvent_eq p

/-- In a Type 3 pairing group, a generic XDH adversary with per-sort append budgets
`n₁, n₂, nₜ` has advantage at most
`3 * ((n₁ + 5).choose 2 + (nₜ + 1).choose 2) / |F|`.
The second-source degree is zero, so its budget contributes no collision term.
Equality queries are free. Nonzero generators suffice; they need not span the carriers. -/
theorem advantage_ofGeneric_le [Field F] [Fintype F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (A : OracleComp (genSpec F pairingSig) Bool) (n₁ n₂ nₜ : ℕ)
    (hn₁ : IsQueryBoundP A (appendsTo .g₁) n₁)
    (hn₂ : IsQueryBoundP A (appendsTo .g₂) n₂)
    (hnₜ : IsQueryBoundP A (appendsTo .gₜ) nₜ) :
    advantage g₁ g₂ (Adversary.ofGeneric e A) ≤
      (3 * ((n₁ + 5).choose 2 + (nₜ + 1).choose 2) : ℕ) / (Fintype.card F : ℝ≥0∞) := by
  classical
  let : Fintype PSort := ⟨{.g₁, .g₂, .gₜ}, by intro s; cases s <;> simp⟩
  let : MeasurableSpace ((Fin 3 → F) × Bool) := ⊤
  let D₀ : PSort → ℕ := fun | .g₁ => 2 | .g₂ => 0 | .gₜ => 2
  let D₁ : PSort → ℕ := fun | .g₁ => 1 | .g₂ => 0 | .gₜ => 1
  let n : PSort → ℕ := fun | .g₁ => n₁ | .g₂ => n₂ | .gₜ => nₜ
  have hD₀ : pairingSig.DegreeClosed D₀ := degreeClosed_pairingSig 2 0 2
  have hD₁ : pairingSig.DegreeClosed D₁ := degreeClosed_pairingSig 1 0 1
  have hn : ∀ s, IsQueryBoundP A (appendsTo s) (n s) := by
    intro s
    cases s
    · exact hn₁
    · exact hn₂
    · exact hnₜ
  let left : ProbComp ((Fin 3 → F) × Bool) := do
    let x ← $ᵗ (Fin 3 → F)
    let z ← runGen (symbolic F pairingSig (Fin 3))
      (fun _ p => MvPolynomial.eval x p) A (xdhTable (X 0 * X 1))
    pure (x, z.1)
  let right : ProbComp ((Fin 3 → F) × Bool) := do
    let x ← $ᵗ (Fin 3 → F)
    let z ← runGen (symbolic F pairingSig (Fin 3))
      (fun _ p => MvPolynomial.eval x p) A (xdhTable (X 2))
    pure (x, z.1)
  have hl : realExperiment g₁ g₂ (Adversary.ofGeneric e A) =ᵈ Prod.snd <$> left := by
    simpa only [left, map_bind, map_pure, bind_pure_comp, Functor.map_map, Function.comp_def] using
      real_experiment_evalDistEq e g₁ g₂ hg₁ hg₂ he A
  have hr : randomExperiment g₁ g₂ (Adversary.ofGeneric e A) =ᵈ Prod.snd <$> right := by
    simpa only [right, map_bind, map_pure, bind_pure_comp, Functor.map_map, Function.comp_def] using
      random_experiment_evalDistEq e g₁ g₂ hg₁ hg₂ he A
  rw [advantage, hl.evalDist_eq, hr.evalDist_eq]
  have hb := measureETVDist_runGen_pairing_sameKernel_uniform_le hD₀ hD₁ A hn
    (xdhTable (X 0 * X 1)) (xdhTable (X 2))
    xdhTables_degreeLE.1 xdhTables_degreeLE.2 xdhTables_sameKernel
  calc
    _ ≤ measureETVDist (Prod.snd <$> left) (Prod.snd <$> right) :=
      measure_absDiff_apply_le_measureETVDist _ _ (MeasurableSet.singleton true)
    _ ≤ measureETVDist left right := measureETVDist_map_le _ _ _ Measurable.of_discrete
    _ ≤ ∑ s, (((xdhTable (X 0 * X 1 : MvPolynomial (Fin 3) F) s).length + n s + 1).choose 2 :
        ℝ≥0∞) * ((D₀ s : ℝ≥0∞) / Fintype.card F + (D₁ s : ℝ≥0∞) / Fintype.card F) := hb
    _ = _ := by
      change (∑ s ∈ ({.g₁, .g₂, .gₜ} : Finset PSort),
        (((xdhTable (X 0 * X 1 : MvPolynomial (Fin 3) F) s).length + n s + 1).choose 2 :
          ℝ≥0∞) * ((D₀ s : ℝ≥0∞) / Fintype.card F + (D₁ s : ℝ≥0∞) / Fintype.card F)) = _
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      simp only [xdhTable, n, D₀, D₁, List.length_cons, List.length_nil, zero_add,
        Nat.cast_zero]
      simp only [Nat.add_comm 4 n₁, Nat.add_assoc, Nat.reduceAdd,
        Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, div_eq_mul_inv]
      ring

/-- A total group-operation budget bounds each append budget, giving the XDH bound
`3 * ((q + 5).choose 2 + (q + 1).choose 2) / |F|`. Equality queries are free. -/
theorem advantage_ofGeneric_le_of_total [Field F] [Fintype F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (A : OracleComp (genSpec F pairingSig) Bool) (q : ℕ)
    (hq : IsQueryBoundP A (fun i => isGroupOp i = true) q) :
    advantage g₁ g₂ (Adversary.ofGeneric e A) ≤
      (3 * ((q + 5).choose 2 + (q + 1).choose 2) : ℕ) / (Fintype.card F : ℝ≥0∞) :=
  advantage_ofGeneric_le e g₁ g₂ hg₁ hg₂ he A q q q
    (hq.appendsTo .g₁) (hq.appendsTo .g₂) (hq.appendsTo .gₜ)

end XDH
