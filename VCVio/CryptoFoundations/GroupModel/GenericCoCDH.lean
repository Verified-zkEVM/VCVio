/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericPairing
public import VCVio.CryptoFoundations.HardnessAssumptions.CoCDH
import all VCVio.CryptoFoundations.GroupModel.Instances
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! # Generic hardness of Type 3 co-CDH

The two independent hidden scalars give source degrees one and target degree two. A source
handle cannot represent their product symbolically, so T8 bounds co-CDH success by the
per-sort collision terms and a quadratic root term. Out-of-range handles denote zero.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace GroupModel.CoCDH

/-- Interpret a generic adversary on the source tables `[g₁, X, h]`, `[g₂, X₂]` and an
empty target table, and read its first-source output handle, with zero out of range. -/
@[expose] def Adversary.ofGeneric {F G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (A : OracleComp (genSpec F pairingSig) Handle) :
    _root_.CoCDH.Adversary F G₁ G₂ :=
  fun g₁ g₂ X X₂ h => (fun z => lookup z.2 .g₁ z.1) <$>
    runGen (pairingReal e) (fun _ => id) A (fun
      | .g₁ => [g₁, X, h]
      | .g₂ => [g₂, X₂]
      | .gₜ => [])

/-- A Type 3 generic co-CDH adversary with append budgets `n₁`, `n₂`, `nₜ` succeeds with
probability at most `((n₁ + 4).choose 2 + (n₂ + 3).choose 2 +
2 * (nₜ + 1).choose 2 + 2) / |F|`. The first generator parametrizes its group bijectively;
the second generator and their pairing are nonzero. Equality queries are free. -/
theorem experiment_ofGeneric_le {F G₁ G₂ Gₜ : Type}
    [Field F] [Fintype F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [DecidableEq G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg : Function.Bijective (· • g₁ : F → G₁)) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (A : OracleComp (genSpec F pairingSig) Handle) (n₁ n₂ nₜ : ℕ)
    (hn₁ : IsQueryBoundP A (appendsTo .g₁) n₁)
    (hn₂ : IsQueryBoundP A (appendsTo .g₂) n₂)
    (hnₜ : IsQueryBoundP A (appendsTo .gₜ) nₜ) :
    Pr{let b ← _root_.CoCDH.experiment g₁ g₂ (Adversary.ofGeneric e A)}[b = true] ≤
      (((n₁ + 4).choose 2 + (n₂ + 3).choose 2 + 2 * (nₜ + 1).choose 2 + 2 : ℕ) :
        ℝ≥0∞) / Fintype.card F := by
  classical
  have hg₁ : g₁ ≠ 0 := by
    intro h
    have hc : (0 : F) = 1 := hg.injective (by simp [h])
    exact zero_ne_one hc
  let : Fintype PSort := ⟨{.g₁, .g₂, .gₜ}, by intro s; cases s <;> simp⟩
  let tbl : Tbl (fun _ : PSort => MvPolynomial (Fin 2) F) := fun
    | .g₁ => [1, MvPolynomial.X 0, MvPolynomial.X 1]
    | .g₂ => [1, MvPolynomial.X 0]
    | .gₜ => []
  let D : PSort → ℕ := fun | .g₁ => 1 | .g₂ => 1 | .gₜ => 2
  let n : PSort → ℕ := fun | .g₁ => n₁ | .g₂ => n₂ | .gₜ => nₜ
  have hD : pairingSig.DegreeClosed D := degreeClosed_pairingSig 1 1 0
  have hd : DegreeLE D tbl := by
    intro s p hp
    cases s <;> simp only [tbl, List.mem_cons, List.not_mem_nil, or_false] at hp
    · rcases hp with rfl | rfl | rfl <;> simp [D]
    · rcases hp with rfl | rfl <;> simp [D]
  have hn : ∀ s, IsQueryBoundP A (appendsTo s) (n s) := by
    intro s
    cases s
    · exact hn₁
    · exact hn₂
    · exact hnₜ
  -- Transport the real tables through evaluation at the two hidden scalars.
  have hr (a b : F) :
      runGen (pairingReal e) (fun _ => id) A (fun
        | .g₁ => [g₁, a • g₁, b • g₁]
        | .g₂ => [g₂, a • g₂]
        | .gₜ => []) =
        Prod.map id (mapTbl (fun s => (evalHom.pairing e g₁ g₂ ![a, b]).toFun s)) <$>
          runGen (symbolic F pairingSig (Fin 2))
            (fun _ p => MvPolynomial.eval ![a, b] p) A tbl := by
    have ht : mapTbl (fun s => (evalHom.pairing e g₁ g₂ ![a, b]).toFun s) tbl = (fun
        | .g₁ => [g₁, a • g₁, b • g₁]
        | .g₂ => [g₂, a • g₂]
        | .gₜ => []) := by
      funext s
      cases s <;> simp [mapTbl, tbl, evalHom.pairing_apply_g₁,
        evalHom.pairing_apply_g₂, evalAt_apply]
    rw [← ht]
    exact runGen_pairing_mapTbl_evalHom e g₁ g₂ hg₁ hg₂ he _ A tbl
  have ha (a b : F) :
      Adversary.ofGeneric e A g₁ g₂ (a • g₁) (a • g₂) (b • g₁) =
        (fun z => MvPolynomial.eval ![a, b] (lookup z.2 .g₁ z.1) • g₁) <$>
          runGen (symbolic F pairingSig (Fin 2))
            (fun _ p => MvPolynomial.eval ![a, b] p) A tbl := by
    rw [Adversary.ofGeneric, hr]
    erw [Functor.map_map]
    congr 1
    funext z
    simp only [Prod.map, id_eq, lookup_mapTbl, evalHom.pairing_apply_g₁, evalAt_apply]
    rfl
  let E := fun (x : Fin 2 → F) (z : Handle × Tbl (fun _ : PSort => MvPolynomial (Fin 2) F)) =>
    MvPolynomial.eval x (lookup z.2 .g₁ z.1) = x 0 * x 1
  have hb : Function.Bijective (Function.uncurry (fun (a b : F) => (![a, b] : Fin 2 → F))) := by
    constructor
    · intro a b h
      exact Prod.ext (congrFun h 0) (congrFun h 1)
    · intro f
      refine ⟨(f 0, f 1), ?_⟩
      funext i
      fin_cases i <;> rfl
  have hs := (SampleableType.evalDistEq_uniformSample_pair_of_bijective hb).bind_left (fun x =>
    E x <$> runGen (symbolic F pairingSig (Fin 2)) (fun _ p => MvPolynomial.eval x p) A tbl)
  have hh := SampleableType.map_uniformSample_evalDistEq_of_bijective hg
  have hevent : Pr{let b ← _root_.CoCDH.experiment g₁ g₂ (Adversary.ofGeneric e A)}[b = true] =
      Pr{let x ← $ᵗ (Fin 2 → F); let z ← (runGen (symbolic F pairingSig (Fin 2))
        (fun _ p => MvPolynomial.eval x p) A tbl)}[E x z] := by
    have hh' := EvalDistEq.bind_right ($ᵗ F) (fun a =>
      hh.bind_left (fun h => do
        let w ← Adversary.ofGeneric e A g₁ g₂ (a • g₁) (a • g₂) h
        pure (decide (w = a • h))))
    unfold _root_.CoCDH.experiment
    rw [← hh'.prEvent_eq (· = true)]
    simp only [bind_map_left, ha]
    simpa only [prEvent_norm, bind_map_left,
      Functor.map_map, Function.comp_def, Prod.map, id_eq, decide_eq_true_eq,
      smul_smul,
      smul_left_inj hg₁, E, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] using hs.prEvent_eq id
  rw [hevent]
  -- Every symbolic first-source output has degree at most one, including the zero default.
  let target : MvPolynomial (Fin 2) F := MvPolynomial.X 0 * MvPolynomial.X 1
  let W := fun (z : Handle × Tbl (fun _ : PSort => MvPolynomial (Fin 2) F)) =>
    target - lookup z.2 .g₁ z.1
  have ht : target.totalDegree = 2 := by
    rw [MvPolynomial.totalDegree_mul_of_isDomain (MvPolynomial.X_ne_zero 0)
      (MvPolynomial.X_ne_zero 1)]
    simp
  have hp (z : Handle × Tbl (fun _ : PSort => MvPolynomial (Fin 2) F))
      (hz : z ∈ support (runGen (symbolic F pairingSig (Fin 2)) (fun _ => id) A tbl)) :
      (lookup z.2 .g₁ z.1).totalDegree ≤ 1 :=
    (runGen_degreeLE hD (fun _ => id) A tbl hd z hz).lookup .g₁ z.1
  have hW (z : Handle × Tbl (fun _ : PSort => MvPolynomial (Fin 2) F))
      (hz : z ∈ support (runGen (symbolic F pairingSig (Fin 2)) (fun _ => id) A tbl)) :
      (W z).totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_sub _ _).trans (max_le (by omega) ((hp z hz).trans (by omega)))
  have hE (x : Fin 2 → F) (z : Handle × Tbl (fun _ : PSort => MvPolynomial (Fin 2) F))
      (hz : z ∈ support (runGen (symbolic F pairingSig (Fin 2)) (fun _ => id) A tbl))
      (h : E x z) : W z ≠ 0 ∧ MvPolynomial.eval x (W z) = 0 := by
    constructor
    · intro heq
      have heq := congrArg MvPolynomial.totalDegree (sub_eq_zero.mp heq)
      have hdeg := hp z hz
      omega
    · simpa only [W, target, map_sub, map_mul, MvPolynomial.eval_X, sub_eq_zero] using h.symm
  have hb := prEvent_runGen_symbolic_le_add_of_polynomial ($ᵗ (Fin 2 → F)) hD
    (ε := fun s => (D s : ℝ≥0∞) / Fintype.card F)
    (ε' := (2 : ℝ≥0∞) / Fintype.card F)
    (fun _ f hf hd => prob_eval_zero_univ_le_div f hf hd) A hn tbl hd W 2 hW E hE
    (fun f hf hd => prob_eval_zero_univ_le_div f hf hd)
  refine hb.trans_eq ?_
  change (∑ s ∈ ({.g₁, .g₂, .gₜ} : Finset PSort),
    (((tbl s).length + n s + 1).choose 2 : ℝ≥0∞) *
      ((D s : ℝ≥0∞) / Fintype.card F)) + 2 / Fintype.card F = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [tbl, n, D, List.length_cons, List.length_nil, Nat.reduceAdd, zero_add]
  rw [Nat.add_comm 3 n₁, Nat.add_comm 2 n₂]
  simp only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one, div_eq_mul_inv, one_mul, add_mul]
  simp only [mul_comm, mul_assoc, add_assoc]

/-- A total group-operation budget bounds all three append budgets in the Type 3 co-CDH
bound. Equality queries do not count against this budget. -/
theorem experiment_ofGeneric_le_of_total {F G₁ G₂ Gₜ : Type}
    [Field F] [Fintype F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [DecidableEq G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg : Function.Bijective (· • g₁ : F → G₁)) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (A : OracleComp (genSpec F pairingSig) Handle) (q : ℕ)
    (hq : IsQueryBoundP A (fun i => isGroupOp i = true) q) :
    Pr{let b ← _root_.CoCDH.experiment g₁ g₂ (Adversary.ofGeneric e A)}[b = true] ≤
      (((q + 4).choose 2 + (q + 3).choose 2 + 2 * (q + 1).choose 2 + 2 : ℕ) :
        ℝ≥0∞) / Fintype.card F := by
  exact experiment_ofGeneric_le e g₁ g₂ hg hg₂ he A q q q
    (hq.appendsTo .g₁) (hq.appendsTo .g₂) (hq.appendsTo .gₜ)

end GroupModel.CoCDH
