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
elements. The finder `alwaysWins` returns `![b₁, -b₀]` on a nonzero basis `b` and `![1, 0]` on
the zero basis, so it wins every relation experiment; over the field with five elements
`experiment_le` then makes the named reduction solve discrete logarithm with probability at
least `4/5`.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace DiscreteLogRelation

/-- A two-coordinate finder that always wins: `![b₁, -b₀]` on a nonzero basis `b`, and `![1, 0]`
on the zero basis. -/
def alwaysWins : Adversary (ZMod 5) (ZMod 5) (Fin 2) unifSpec :=
  fun b => pure (if b = 0 then ![1, 0] else ![b 1, -b 0])

/-- `alwaysWins` wins the plain relation experiment over `ZMod 5` with probability one. -/
theorem alwaysWins_experiment :
    Pr{let b ← plainExperiment (1 : ZMod 5) alwaysWins}[b = true] = 1 := by
  have h : plainExperiment (1 : ZMod 5) alwaysWins =
      (do let _ ← @uniformSample (Fin 2 → ZMod 5) instSampleableTypeFunc; pure true) := by
    simp only [plainExperiment, experiment, plainAdversary, alwaysWins, StateT.run'_eq,
      map_run_plainImpl, pure_bind]
    congr 1
    funext x
    congr 1
    revert x
    decide
  simp [h]

/-- The named plain reduction from `alwaysWins` solves discrete logarithm over `ZMod 5` with
probability at least `4/5`, by `experiment_le` and `alwaysWins_experiment`. -/
theorem alwaysWins_reduction :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    (4 / 5 : ℝ≥0∞) ≤
      Pr{let b ← DiffieHellman.dlogExperiment (1 : ZMod 5) (plainReduction alwaysWins)}[
        b = true] := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := experiment_le plainImpl () (1 : ZMod 5) one_ne_zero (plainAdversary alwaysWins)
  rw [← plainExperiment_eq, alwaysWins_experiment, ZMod.card] at h
  have h45 : (4 / 5 : ℝ≥0∞) + 1 / 5 = 1 := by
    rw [ENNReal.div_add_div_same, show (4 : ℝ≥0∞) + 1 = 5 by norm_num]
    exact ENNReal.div_self (by norm_num) (by norm_num)
  exact (ENNReal.add_le_add_iff_right (by simp)).mp (h45.trans_le (by exact_mod_cast h))

/-- The vector `![1, -1]` wins exactly on equality of the two sampled scalars. -/
theorem pair_experiment_zmod_five :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    plainExperiment (F := ZMod 5) (1 : ZMod 5) (fun _ => pure ![1, -1]) =
      (do
        let x ← @uniformSample (Fin 2 → ZMod 5) instSampleableTypeFunc
        pure (decide (x 0 = x 1))) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hn : (![1, -1] : Fin 2 → ZMod 5) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num at h0
  -- The experiment sums with the `Fintype` instance of the enumeration of `Fin 2`.
  have huniv : @Finset.univ (Fin 2) FinEnum.instFintype = Finset.univ := by
    congr 1
  simp [plainExperiment, experiment, plainAdversary, hn, huniv, Fin.sum_univ_two,
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
  simpa [ZMod.card] using experiment_le (F := ZMod 101) _ 7 (1 : ZMod 101) one_ne_zero A

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
