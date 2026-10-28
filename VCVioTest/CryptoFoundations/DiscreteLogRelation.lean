/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.DiscreteLogRelation
public import Mathlib.Algebra.Field.ZMod

/-!
 # Discrete-log relation regression tests

The fixed coefficient vector `![1, -1]` finds precisely collisions between two supplied
elements. Its standard-model reduction specializes over the field with five elements.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace DiscreteLogRelation

/-- The fixed two-coordinate relation adversary satisfies the reduction bound over `ZMod 5`. -/
theorem reduction_zmod_five :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let A : Adversary (ZMod 5) (ZMod 5) (Fin 2) unifSpec := fun _ => pure ![1, -1]
    Pr{let b ← plainExperiment (1 : ZMod 5) A}[b = true] ≤
      Pr{let b ← DiffieHellman.dlogExperiment (1 : ZMod 5) (plainReduction A)}[b = true] +
        (1 / 5 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  dsimp only
  simpa [ZMod.card] using experiment_le plainImpl () (F := ZMod 5) (1 : ZMod 5)
    (by
      simp only [smul_eq_mul, mul_one]
      exact ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩)
    (plainAdversary (fun _ => pure ![1, -1]))

/-- The vector `![1, -1]` wins exactly on equality of the two sampled scalars. -/
theorem pair_experiment_zmod_five :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    plainExperiment (F := ZMod 5) (1 : ZMod 5) (fun _ => pure ![1, -1]) =
      (do
        let x ← @uniformSample (Fin 2 → ZMod 5) instSampleableTypePiFintype
        pure (decide (x 0 = x 1))) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hn : (![1, -1] : Fin 2 → ZMod 5) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num at h0
  simp [plainExperiment, experiment, plainAdversary, hn, Fin.sum_univ_two,
    sub_eq_zero, ← sub_eq_add_neg]

/-- Zero-extension into an optional slot preserves the explicit vanishing coefficients. -/
theorem embed_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    ∃ r : RelationWitness (F := ZMod 101)
        (fun i : Option (Fin 2) => i.elim (9 : ZMod 101) ![1, 7]),
      r.coeffs none = 0 ∧ r.coeffs (some 0) = 7 ∧ r.coeffs (some 1) = -1 := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  let r : RelationWitness (F := ZMod 101) (![1, 7] : Fin 2 → ZMod 101) :=
    ⟨![7, -1], by intro hz; exact (by decide : (7 : ZMod 101) ≠ 0) (congrFun hz 0),
      by norm_num [representationEval, Fin.sum_univ_two]⟩
  let e : Fin 2 ↪ Option (Fin 2) := ⟨some, Option.some_injective _⟩
  refine ⟨r.embed e (fun _ => rfl), ?_⟩
  simp [RelationWitness.embed, embedCoeffs, e, r]

/-- Known logs extract the challenge logarithm from the explicit relation `7 • 1 - 7 = 0`. -/
theorem extractLog_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    ∃ d : DiscreteLogWitness (F := ZMod 101) (1 : ZMod 101) 7, d.log = 7 := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  let r : RelationWitness (F := ZMod 101) (![1, 7] : Fin 2 → ZMod 101) :=
    ⟨![7, -1], by intro hz; exact (by decide : (7 : ZMod 101) ≠ 0) (congrFun hz 0),
      by norm_num [representationEval, Fin.sum_univ_two]⟩
  have hk : ∀ i : Fin 2, i ≠ 1 → (![1, 7] : Fin 2 → ZMod 101) i =
      (![1, 0] : Fin 2 → ZMod 101) i • (1 : ZMod 101) := by
    intro i hi
    fin_cases i <;> simp_all
  refine ⟨r.extractLog 1 ![1, 0] 1 hk (by norm_num [r]), ?_⟩
  norm_num [RelationWitness.extractLog, relationLogExcept, r, Fin.sum_univ_two]

/-- A zero challenge coefficient takes the relation branch, preserving the other two slots. -/
theorem discharge_zero_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    ∃ r : RelationWitness (F := ZMod 101) (![1, 1, 7] : Fin 3 → ZMod 101),
      (r.discharge 1 ![1, 1, 0] 2 (by
        intro i hi
        fin_cases i <;> simp_all)).isLeft = true := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  let r : RelationWitness (F := ZMod 101) (![1, 1, 7] : Fin 3 → ZMod 101) :=
    ⟨![1, -1, 0], by intro hz; have h := congrFun hz 0; norm_num at h,
      by norm_num [representationEval, Fin.sum_univ_succ]⟩
  exact ⟨r, by simp [RelationWitness.discharge, r]⟩

/-- A stateful counter supplies successive answers to the same finder, with no state reset. -/
theorem counter_experiment_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    let impl : QueryImpl (Unit →ₒ ℕ) (StateT ℕ ProbComp) :=
      fun _ => modifyGet (fun n => (n, n + 1))
    let A : Adversary (ZMod 101) (ZMod 101) (Fin 2) (Unit →ₒ ℕ) := fun _ => do
      let n ← (Unit →ₒ ℕ).query ()
      let m ← (Unit →ₒ ℕ).query ()
      pure ![(n : ZMod 101), -(m : ZMod 101)]
    experiment impl 7 (1 : ZMod 101) A =
      plainExperiment (F := ZMod 101) (1 : ZMod 101) (fun _ => pure ![7, -8]) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  simp [experiment, plainExperiment, plainAdversary, simulateQ_bind, StateT.run'_eq,
    StateT.run_bind]

/-- The named DLog reduction accepts a stateful counter interpretation directly. -/
theorem counter_reduction_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    let impl : QueryImpl (Unit →ₒ ℕ) (StateT ℕ ProbComp) :=
      fun _ => modifyGet (fun n => (n, n + 1))
    ∀ A : Adversary (ZMod 101) (ZMod 101) Bool (Unit →ₒ ℕ),
      Pr{let b ← experiment impl 7 (1 : ZMod 101) A}[b = true] ≤
        Pr{let b ← (DiffieHellman.dlogExperiment 1 (reduction impl 7 A))}[b = true] +
          (1 / 101 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  dsimp only
  intro A
  simpa [ZMod.card] using experiment_le (F := ZMod 101) _ 7 (1 : ZMod 101)
    (by
      simp only [smul_eq_mul, mul_one]
      exact ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩) A

/-- Two distinct natural-number labels give a uniform Boolean-indexed generator basis. -/
theorem generator_oracle_zmod_101 :
    (simulateQ randomOracle
      (queryBasis (G := ZMod 101) (fun b : Bool => if b then 17 else 42))).run' ∅ =ᵈ
      ($ᵗ (Bool → ZMod 101)) := by
  have h := queryBasis_empty_evalDistEq_uniform (G := ZMod 101)
    (fun b : Bool => if b then (17 : ℕ) else 42)
    (by intro a b h; cases a <;> cases b <;> simp_all)
  refine h.trans (EvalDistEq.of_forall_prEvent_eq ?_)
  intro p
  exact SampleableType.prEvent_uniformSample_inst_irrel _ _ p

end DiscreteLogRelation
