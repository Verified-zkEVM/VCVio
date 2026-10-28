/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.MasterBound
public import VCVio.CryptoFoundations.HardnessAssumptions.PairingDLog
import all VCVio.CryptoFoundations.GroupModel.Instances
import Mathlib.Algebra.Module.Torsion.Free

/-! # Generic hardness in Type 3 pairing groups

Evaluation transports symbolic computations to real bilinear groups. Per-sort collision
bounds then control recovery of a common exponent from its powers in the source groups.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace GroupModel

variable {F G₁ G₂ Gₜ ι α : Type}

/-- Evaluating the symbolic table commutes with a real pairing run when scalar multiplication
by each chosen source generator and their pairing is injective. -/
theorem runGen_pairing_mapTbl_evalHom [Field F] [DecidableEq F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0) (x : ι → F)
    (A : OracleComp (genSpec F pairingSig) α)
    (tbl : Tbl (fun _ : PSort => MvPolynomial ι F)) :
    runGen (pairingReal e) (fun _ => id) A
        (mapTbl (fun s => (evalHom.pairing e g₁ g₂ x).toFun s) tbl) =
      Prod.map id (mapTbl (fun s => (evalHom.pairing e g₁ g₂ x).toFun s)) <$>
        runGen (symbolic F pairingSig ι) (fun _ p => MvPolynomial.eval x p) A tbl := by
  have h := runGen_map (evalHom.pairing e g₁ g₂ x) (fun _ => id) A tbl
  simp only [Function.comp_def, id_eq] at h
  rw [← h]
  congr 1
  unfold runGen run
  rw [impl_congr (symbolic F pairingSig ι)
    (fun s p => (evalHom.pairing e g₁ g₂ x).toFun s p)
    (fun _ p => MvPolynomial.eval x p) (by
      intro s p r
      cases s
      · change (evalAt g₁ x p = evalAt g₁ x r) ↔ _
        simp only [evalAt_apply]
        exact (smul_left_injective F hg₁).eq_iff
      · change (evalAt g₂ x p = evalAt g₂ x r) ↔ _
        simp only [evalAt_apply]
        exact (smul_left_injective F hg₂).eq_iff
      · change (evalAt (e g₁ g₂) x p = evalAt (e g₁ g₂) x r) ↔ _
        simp only [evalAt_apply]
        exact (smul_left_injective F he).eq_iff) ProbComp]

end GroupModel

namespace PairingDLog

open GroupModel

/-- Interpret a generic scalar-valued adversary in a real pairing group on the two lists
of source powers, with an initially empty target table. -/
@[expose] def Adversary.ofGeneric {F G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    {q₁ q₂ : ℕ} (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ)
    (A : OracleComp (genSpec F pairingSig) F) : Adversary F G₁ G₂ q₁ q₂ :=
  fun xs ys => Prod.fst <$> runGen (pairingReal e) (fun _ => id) A (fun
    | .g₁ => List.ofFn xs
    | .g₂ => List.ofFn ys
    | .gₜ => [])

private theorem uniform_unit {F : Type} [SampleableType F] :
    (fun a (_ : Unit) => a) <$> ($ᵗ F : ProbComp F) =ᵈ
      ($ᵗ (Unit → F) : ProbComp (Unit → F)) := by
  apply SampleableType.map_uniformSample_evalDistEq_of_bijective
  exact ⟨fun _ _ h => congrFun h (), fun f => ⟨f (), by funext u; cases u; rfl⟩⟩

/-- In a Type 3 pairing group, a generic adversary recovering a common exponent from
powers through `q₁` and `q₂` has success bounded by the three collision terms and one
additional linear root term, divided by the scalar field cardinality. -/
theorem experiment_ofGeneric_le {F G₁ G₂ Gₜ : Type}
    [Field F] [Fintype F] [SampleableType F] [DecidableEq F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (q₁ q₂ : ℕ) (A : OracleComp (genSpec F pairingSig) F) (n₁ n₂ nₜ : ℕ)
    (hn₁ : IsQueryBoundP A (appendsTo .g₁) n₁)
    (hn₂ : IsQueryBoundP A (appendsTo .g₂) n₂)
    (hnₜ : IsQueryBoundP A (appendsTo .gₜ) nₜ) :
    Pr{let b ← experiment g₁ g₂ (Adversary.ofGeneric (q₁ := q₁) (q₂ := q₂) e A)}[b = true] ≤
      (((q₁ + n₁ + 2).choose 2 * q₁ + (q₂ + n₂ + 2).choose 2 * q₂ +
        (nₜ + 1).choose 2 * (q₁ + q₂) + 1 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  classical
  let : Fintype PSort := ⟨{.g₁, .g₂, .gₜ}, by intro s; cases s <;> simp⟩
  let tbl : Tbl (fun _ : PSort => MvPolynomial Unit F) := fun
    | .g₁ => List.ofFn (fun i : Fin (q₁ + 1) => MvPolynomial.X () ^ (i : ℕ))
    | .g₂ => List.ofFn (fun i : Fin (q₂ + 1) => MvPolynomial.X () ^ (i : ℕ))
    | .gₜ => []
  let D : PSort → ℕ := fun | .g₁ => q₁ | .g₂ => q₂ | .gₜ => q₁ + q₂
  let n : PSort → ℕ := fun | .g₁ => n₁ | .g₂ => n₂ | .gₜ => nₜ
  have hD : pairingSig.DegreeClosed D := by
    exact ⟨fun o => o.elim, fun _ => le_rfl⟩
  have hd : DegreeLE D tbl := by
    intro s p hp
    cases s with
    | g₁ =>
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
      simpa only [MvPolynomial.totalDegree_X_pow] using Nat.le_of_lt_succ i.isLt
    | g₂ =>
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
      simpa only [MvPolynomial.totalDegree_X_pow] using Nat.le_of_lt_succ i.isLt
    | gₜ => exact False.elim (List.not_mem_nil hp)
  have hn : ∀ s, IsQueryBoundP A (appendsTo s) (n s) := by
    intro s
    cases s
    · exact hn₁
    · exact hn₂
    · exact hnₜ
  have hr (a : F) :
      runGen (pairingReal e) (fun _ => id) A (fun
        | .g₁ => List.ofFn (fun i : Fin (q₁ + 1) => a ^ (i : ℕ) • g₁)
        | .g₂ => List.ofFn (fun i : Fin (q₂ + 1) => a ^ (i : ℕ) • g₂)
        | .gₜ => []) =
        Prod.map id (mapTbl (fun s => (evalHom.pairing e g₁ g₂
          (fun _ : Unit => a)).toFun s)) <$>
          runGen (symbolic F pairingSig Unit)
            (fun _ p => MvPolynomial.eval (fun _ : Unit => a) p) A tbl := by
    have ht : mapTbl (fun s => (evalHom.pairing e g₁ g₂
        (fun _ : Unit => a)).toFun s) tbl = (fun
        | .g₁ => List.ofFn (fun i : Fin (q₁ + 1) => a ^ (i : ℕ) • g₁)
        | .g₂ => List.ofFn (fun i : Fin (q₂ + 1) => a ^ (i : ℕ) • g₂)
        | .gₜ => []) := by
      funext s
      cases s
      · change List.map _ (List.ofFn _) = _
        rw [List.map_ofFn]
        congr 1
        funext i
        simp only [Function.comp_apply, evalHom.pairing_apply_g₁, evalAt_apply,
          map_pow, MvPolynomial.eval_X]
        rfl
      · change List.map _ (List.ofFn _) = _
        rw [List.map_ofFn]
        congr 1
        funext i
        simp only [Function.comp_apply, evalHom.pairing_apply_g₂, evalAt_apply,
          map_pow, MvPolynomial.eval_X]
        rfl
      · rfl
    rw [← ht]
    exact runGen_pairing_mapTbl_evalHom e g₁ g₂ hg₁ hg₂ he _ A tbl
  have hs := (uniform_unit (F := F)).bind_left (fun x =>
    (fun z => z.1 = x ()) <$> runGen (symbolic F pairingSig Unit)
      (fun _ p => MvPolynomial.eval x p) A tbl)
  have hevent : Pr{let b ← (experiment g₁ g₂
      (Adversary.ofGeneric (q₁ := q₁) (q₂ := q₂) e A))}[b = true] =
      Pr{let x ← $ᵗ (Unit → F); let z ← (runGen (symbolic F pairingSig Unit)
        (fun _ p => MvPolynomial.eval x p) A tbl)}[z.1 = x ()] := by
    simpa only [experiment, Adversary.ofGeneric, hr, prEvent_norm,
      bind_map_left, Functor.map_map, Function.comp_def, Prod.map, id_eq,
      decide_eq_true_eq] using hs.prEvent_eq id
  rw [hevent]
  have hb := computational_runGen_symbolic_le ($ᵗ (Unit → F)) hD
    (ε := fun s => (D s : ℝ≥0∞) / Fintype.card F)
    (ε' := (1 : ℝ≥0∞) / Fintype.card F)
    (fun _ f hf hd => prob_eval_zero_univ_le_div f hf hd) A hn tbl hd
    (fun z => MvPolynomial.X () - MvPolynomial.C z.1) 1
    (fun z _ => (MvPolynomial.totalDegree_sub_C_le _ _).trans (by simp))
    (fun x z => z.1 = x ())
    (fun x z _ h => by
      constructor
      · intro hz
        have ht := congrArg MvPolynomial.totalDegree (sub_eq_zero.mp hz)
        simp only [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C,
          Nat.one_ne_zero] at ht
      · simp [h])
    (fun f hf hd => by simpa only [Nat.cast_one] using prob_eval_zero_univ_le_div f hf hd)
  refine hb.trans_eq ?_
  change (∑ s ∈ ({.g₁, .g₂, .gₜ} : Finset PSort),
    (((tbl s).length + n s + 1).choose 2 : ℝ≥0∞) *
      ((D s : ℝ≥0∞) / Fintype.card F)) + 1 / Fintype.card F = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [tbl, n, D, List.length_ofFn, List.length_nil, zero_add]
  rw [Nat.add_right_comm q₁ 1 n₁, Nat.add_right_comm q₂ 1 n₂]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, ENNReal.add_div, mul_div_assoc]
  ac_rfl

/-- A total group-operation budget bounds each of the three append budgets, yielding
one common budget in the Type 3 powers discrete-logarithm bound. Equality queries are free. -/
theorem experiment_ofGeneric_le_of_total {F G₁ G₂ Gₜ : Type}
    [Field F] [Fintype F] [SampleableType F] [DecidableEq F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (q₁ q₂ : ℕ) (A : OracleComp (genSpec F pairingSig) F) (q : ℕ)
    (hq : IsQueryBoundP A (fun i => isGroupOp i = true) q) :
    Pr{let b ← experiment g₁ g₂ (Adversary.ofGeneric (q₁ := q₁) (q₂ := q₂) e A)}[b = true] ≤
      (((q₁ + q + 2).choose 2 * q₁ + (q₂ + q + 2).choose 2 * q₂ +
        (q + 1).choose 2 * (q₁ + q₂) + 1 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  exact experiment_ofGeneric_le e g₁ g₂ hg₁ hg₂ he q₁ q₂ A q q q
    (hq.appendsTo .g₁) (hq.appendsTo .g₂) (hq.appendsTo .gₜ)

end PairingDLog
