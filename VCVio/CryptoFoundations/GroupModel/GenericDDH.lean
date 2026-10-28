/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericHardness
public import VCVio.CryptoFoundations.GroupModel.Decisional
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Generic hardness of decisional Diffie–Hellman

A generic computation induces an ordinary DDH adversary by running on the four challenge
handles. With at most `q` group operations its advantage is at most
`3 * (q + 5).choose 2 / |F|`; equality queries are free. The real and random polynomial
tables have the same linear relations and degrees two and one, respectively.
-/

public section

open OracleComp OracleSpec MeasureTheory MvPolynomial
open scoped ENNReal

namespace GroupModel

variable {F G : Type}

/-- Run a generic Boolean computation on the generator and three DDH challenge elements. -/
@[expose] def DDHAdversary.ofGeneric [Field F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (A : OracleComp (genSpec F groupSig) Bool) : DiffieHellman.DDHAdversary F G :=
  fun g X Y T => Prod.fst <$> runGen (Model.group G) (fun _ => id) A
    (fun _ => [g, X, Y, T])

private theorem ddh_left_independent [Field F] :
    LinearIndependent F
      ([1, X 0, X 1, X 0 * X 1] : List (MvPolynomial (Fin 3) F)).get := by
  let e : Fin 4 → (Fin 3 →₀ ℕ) :=
    ![0, Finsupp.single 0 1, Finsupp.single 1 1, Finsupp.single 0 1 + Finsupp.single 1 1]
  have he : Function.Injective e := by
    intro i j h
    have h₀ := congrArg (fun f : Fin 3 →₀ ℕ => f 0) h
    have h₁ := congrArg (fun f : Fin 3 →₀ ℕ => f 1) h
    have h₂ := congrArg (fun f : Fin 3 →₀ ℕ => f 2) h
    clear h
    fin_cases i <;> fin_cases j <;> simp_all [e]
  convert (basisMonomials (Fin 3) F).linearIndependent.comp e he using 1
  funext i
  fin_cases i <;> simp [e, coe_basisMonomials, X, monomial_mul_monomial]

private theorem ddh_right_independent [Field F] :
    LinearIndependent F
      ([1, X 0, X 1, X 2] : List (MvPolynomial (Fin 3) F)).get := by
  let e : Fin 4 → (Fin 3 →₀ ℕ) :=
    ![0, Finsupp.single 0 1, Finsupp.single 1 1, Finsupp.single 2 1]
  have he : Function.Injective e := by
    intro i j h
    have h₀ := congrArg (fun f : Fin 3 →₀ ℕ => f 0) h
    have h₁ := congrArg (fun f : Fin 3 →₀ ℕ => f 1) h
    have h₂ := congrArg (fun f : Fin 3 →₀ ℕ => f 2) h
    clear h
    fin_cases i <;> fin_cases j <;> simp_all [e]
  convert (basisMonomials (Fin 3) F).linearIndependent.comp e he using 1
  funext i
  fin_cases i <;> simp [e, coe_basisMonomials, X]

private theorem ddh_sameKernel [Field F] :
    SameKernel (F := F) (ι := Fin 3)
      (fun _ : Unit => [1, X 0, X 1, X 0 * X 1])
      (fun _ : Unit => [1, X 0, X 1, X 2]) :=
  sameKernel_of_linearIndependent (fun _ => rfl)
    (fun _ => ddh_left_independent) (fun _ => ddh_right_independent)

private theorem ddh_degreeLE [Field F] :
    DegreeLE (F := F) (ι := Fin 3) 2
      (fun _ : Unit => [1, X 0, X 1, X 0 * X 1]) ∧
    DegreeLE (F := F) (ι := Fin 3) 1
      (fun _ : Unit => [1, X 0, X 1, X 2]) := by
  constructor
  · intro s p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp
    · exact (totalDegree_mul _ _).trans (by simp)
  · intro s p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp

private theorem uniform_fin_three [SampleableType F] :
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

private theorem runGen_ddh [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]
    [DecidableEq G] (g : G) (hg : g ≠ 0) (x : Fin 3 → F)
    (A : OracleComp (genSpec F groupSig) Bool) (p : MvPolynomial (Fin 3) F) :
    DDHAdversary.ofGeneric A g (x 0 • g) (x 1 • g) (MvPolynomial.eval x p • g) =
      Prod.fst <$> runGen (symbolic F groupSig (Fin 3))
        (fun _ p => MvPolynomial.eval x p) A (fun _ => [1, X 0, X 1, p]) := by
  have ht : mapTbl (fun _ : Unit => evalAt g x) (fun _ => [1, X 0, X 1, p]) =
      (fun _ => [g, x 0 • g, x 1 • g, MvPolynomial.eval x p • g]) := by
    funext u
    simp [mapTbl, evalAt_apply]
  unfold DDHAdversary.ofGeneric
  rw [← ht]
  have h := runGen_group_mapTbl_evalAt g hg x A (fun _ => [1, X 0, X 1, p])
  rw [h]
  simp only [Functor.map_map, Prod.map, id_eq, groupSig, discreteSig]

private theorem real_experiment_evalDistEq [Field F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (g : G) (hg : g ≠ 0) (A : OracleComp (genSpec F groupSig) Bool) :
    DiffieHellman.ddhRealExperiment g (DDHAdversary.ofGeneric A) =ᵈ
      (do let x ← $ᵗ (Fin 3 → F)
          Prod.fst <$> runGen (symbolic F groupSig (Fin 3))
            (fun _ p => MvPolynomial.eval x p) A (fun _ => [1, X 0, X 1, X 0 * X 1])) := by
  have hs := (uniform_fin_three (F := F)).bind_left (fun x =>
    DDHAdversary.ofGeneric A g (x 0 • g) (x 1 • g) ((x 0 * x 1) • g))
  have hc := EvalDistEq.bind_right ($ᵗ F : ProbComp F) (fun a =>
    EvalDistEq.bind_right ($ᵗ F : ProbComp F) (fun b =>
      OracleComp.EvalDistEq.bind_const ($ᵗ F)
        (DDHAdversary.ofGeneric A g (a • g) (b • g) ((a * b) • g))))
  have he := hc.symm.trans (by
    simpa only [bind_assoc, pure_bind, Matrix.cons_val_zero, Matrix.cons_val_one] using hs)
  apply EvalDistEq.of_forall_prEvent_eq
  intro p
  simpa [DiffieHellman.ddhRealExperiment, ← runGen_ddh g hg, prEvent_norm] using
    he.prEvent_eq p

private theorem random_experiment_evalDistEq [Field F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (g : G) (hg : g ≠ 0) (A : OracleComp (genSpec F groupSig) Bool) :
    DiffieHellman.ddhRandomExperiment g (DDHAdversary.ofGeneric A) =ᵈ
      (do let x ← $ᵗ (Fin 3 → F)
          Prod.fst <$> runGen (symbolic F groupSig (Fin 3))
            (fun _ p => MvPolynomial.eval x p) A (fun _ => [1, X 0, X 1, X 2])) := by
  have hs := (uniform_fin_three (F := F)).bind_left (fun x =>
    DDHAdversary.ofGeneric A g (x 0 • g) (x 1 • g) (x 2 • g))
  apply EvalDistEq.of_forall_prEvent_eq
  intro p
  simpa [DiffieHellman.ddhRandomExperiment, ← runGen_ddh g hg, prEvent_norm] using
    hs.prEvent_eq p

/-- A generic DDH adversary using at most `q` group operations has advantage at most
`3 * (q + 5).choose 2 / |F|` in the ordinary real and random experiments.
Equality queries are free. -/
theorem ddhAdvantage_ofGeneric_le [Field F] [Fintype F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (g : G) (hg : g ≠ 0) (A : OracleComp (genSpec F groupSig) Bool)
    (q : ℕ) (hq : IsQueryBoundP A (fun i => isGroupOp i = true) q) :
    DiffieHellman.ddhAdvantage g (DDHAdversary.ofGeneric (G := G) A) ≤
      (3 * (q + 5).choose 2 : ℕ) / (Fintype.card F : ℝ≥0∞) := by
  classical
  let : MeasurableSpace ((Fin 3 → F) × Bool) := ⊤
  let left : ProbComp ((Fin 3 → F) × Bool) := do
    let x ← $ᵗ (Fin 3 → F)
    let z ← runGen (symbolic F groupSig (Fin 3))
      (fun _ p => MvPolynomial.eval x p) A (fun _ => [1, X 0, X 1, X 0 * X 1])
    pure (x, z.1)
  let right : ProbComp ((Fin 3 → F) × Bool) := do
    let x ← $ᵗ (Fin 3 → F)
    let z ← runGen (symbolic F groupSig (Fin 3))
      (fun _ p => MvPolynomial.eval x p) A (fun _ => [1, X 0, X 1, X 2])
    pure (x, z.1)
  have hl : DiffieHellman.ddhRealExperiment g (DDHAdversary.ofGeneric A) =ᵈ
      Prod.snd <$> left := by
    simpa only [left, map_bind, map_pure, bind_pure_comp, Functor.map_map, Function.comp_def] using
      real_experiment_evalDistEq g hg A
  have hr : DiffieHellman.ddhRandomExperiment g (DDHAdversary.ofGeneric A) =ᵈ
      Prod.snd <$> right := by
    simpa only [right, map_bind, map_pure, bind_pure_comp, Functor.map_map, Function.comp_def] using
      random_experiment_evalDistEq g hg A
  rw [DiffieHellman.ddhAdvantage, hl.evalDist_eq, hr.evalDist_eq]
  have hb := measureETVDist_runGen_sameKernel_uniform_le A hq
    (fun _ => [1, X 0, X 1, X 0 * X 1]) (fun _ => [1, X 0, X 1, X 2])
    ddh_degreeLE.1 ddh_degreeLE.2 ddh_sameKernel
  calc
    _ ≤ measureETVDist (Prod.snd <$> left) (Prod.snd <$> right) :=
      measure_absDiff_apply_le_measureETVDist _ _ (MeasurableSet.singleton true)
    _ ≤ measureETVDist left right := measureETVDist_map_le _ _ _ Measurable.of_discrete
    _ ≤ ((q + 5).choose 2 : ℝ≥0∞) * (2 / Fintype.card F) +
        ((q + 5).choose 2 : ℝ≥0∞) * (1 / Fintype.card F) := by
      simpa [left, right, groupSig, discreteSig, Nat.add_comm 4 q, Nat.add_assoc] using hb
    _ = _ := by
      simp only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
      rw [← mul_add, ← add_mul]
      norm_num
      ac_rfl

end GroupModel
