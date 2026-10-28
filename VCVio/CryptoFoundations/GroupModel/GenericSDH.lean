/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericPairing
public import VCVio.CryptoFoundations.HardnessAssumptions.SDH
import all VCVio.CryptoFoundations.GroupModel.Instances
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.BigOperators

/-! # Generic strong Diffie–Hellman bounds in Type 3 bilinear groups

The source degrees are `D` and one, and the target degree is `D + 1`.
Uniform nonzero trapdoors give a root bound with denominator `|F| - 1`.
The computational master theorem combines the three collision terms with the
output-polynomial term for `t`-SDH or ARSDH. Handles outside the table denote zero.
-/

public section

open OracleComp OracleSpec MeasureTheory GroupModel
open scoped ENNReal

variable {F G₁ G₂ Gₜ α : Type}

namespace TSDH

/-- Interpret a generic `t`-SDH adversary using the public pairing and read its output
in the first source group, with zero for an out-of-range handle. -/
@[expose] def Adversary.ofGeneric [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    {D : ℕ} (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ)
    (A : OracleComp (genSpec F pairingSig) (F × Handle)) : Adversary F G₁ G₂ D :=
  fun xs ys => (fun z => (z.1.1, lookup z.2 .g₁ z.1.2)) <$>
    runGen (pairingReal e) (fun _ => id) A (fun
      | .g₁ => List.ofFn xs | .g₂ => List.ofFn ys | .gₜ => [])

end TSDH

namespace ARSDH

/-- Interpret a generic ARSDH adversary using the public pairing and read both output
handles in the first source group, with zero for out-of-range handles. -/
@[expose] def Adversary.ofGeneric [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    {D : ℕ} (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ)
    (A : OracleComp (genSpec F pairingSig) (Finset F × Handle × Handle)) :
    Adversary F G₁ G₂ D :=
  fun xs ys => (fun z => (z.1.1, lookup z.2 .g₁ z.1.2.1, lookup z.2 .g₁ z.1.2.2)) <$>
    runGen (pairingReal e) (fun _ => id) A (fun
      | .g₁ => List.ofFn xs | .g₂ => List.ofFn ys | .gₜ => [])

end ARSDH

namespace GroupModel

private theorem sampleTrapdoor_root_le [Field F] [Fintype F] [DecidableEq F]
    (f : MvPolynomial Unit F) (hf : f ≠ 0) {d : ℕ} (hd : f.totalDegree ≤ d) :
    Pr{let a ← SDH.sampleTrapdoor F}[MvPolynomial.eval (fun _ => a) f = 0] ≤
      (d : ℝ≥0∞) / (Fintype.card F - 1 : ℕ) := by
  classical
  let : Nonempty {x : F // x ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  let := SampleableType.subtype F (· ≠ 0)
  have hu : (fun a (_ : Unit) => a) <$> ($ᵗ {x : F // x ≠ 0}) =ᵈ
      ($ᵗ (Unit → {x : F // x ≠ 0})) := by
    apply SampleableType.map_uniformSample_evalDistEq_of_bijective
    exact ⟨fun _ _ h => congrFun h (), fun f => ⟨f (), by funext u; cases u; rfl⟩⟩
  have hc : ({x : F | x ≠ 0}).toFinset.card = Fintype.card F - 1 := by
    simp [Finset.filter_ne', Finset.card_erase_of_mem]
  have hm : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F)
    omega
  have hb := @prob_eval_zero_le_div F _ Unit _ (fun _ => {x : F | x ≠ 0})
    (fun _ => inferInstance) (fun _ => ⟨⟨1, one_ne_zero⟩⟩)
    (inferInstanceAs (SampleableType (Unit → {x : F // x ≠ 0})))
    f hf d (Fintype.card F - 1) hd hm (fun _ => hc.ge)
  have he := hu.prEvent_eq (fun x => MvPolynomial.eval (fun i => (x i).val) f = 0)
  simpa only [SDH.sampleTrapdoor, prEvent_norm] using he.le.trans hb

private noncomputable def sdhTable [CommSemiring F] (D : ℕ) :
    Tbl (fun _ : PSort => MvPolynomial Unit F) :=
  fun | .g₁ => List.ofFn (fun i : Fin (D + 1) => MvPolynomial.X () ^ (i : ℕ))
      | .g₂ => [1, MvPolynomial.X ()]
      | .gₜ => []

private def sdhDegree (D : ℕ) : PSort → ℕ :=
  fun | .g₁ => D | .g₂ => 1 | .gₜ => D + 1

private theorem sdhDegree_closed (D : ℕ) : pairingSig.DegreeClosed (sdhDegree D) := by
  convert degreeClosed_pairingSig D 1 0 using 1
  congr 1

private theorem sdhTable_degreeLE [Field F] (D : ℕ) :
    DegreeLE (sdhDegree D) (sdhTable (F := F) D) := by
  intro s p hp
  cases s with
  | g₁ =>
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    simpa only [MvPolynomial.totalDegree_X_pow, sdhDegree] using Nat.le_of_lt_succ i.isLt
  | g₂ =>
    simp only [sdhTable, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [sdhDegree]
  | gₜ => exact False.elim (List.not_mem_nil hp)

private theorem sdh_run_map [Field F] [DecidableEq F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (D : ℕ) (A : OracleComp (genSpec F pairingSig) α) (a : F) :
    runGen (pairingReal e) (fun _ => id) A (fun
      | .g₁ => List.ofFn (fun i : Fin (D + 1) => a ^ (i : ℕ) • g₁)
      | .g₂ => List.ofFn ![g₂, a • g₂] | .gₜ => []) =
    Prod.map id (mapTbl (fun s => (evalHom.pairing e g₁ g₂
      (fun _ : Unit => a)).toFun s)) <$>
      runGen (symbolic F pairingSig Unit)
        (fun _ p => MvPolynomial.eval (fun _ : Unit => a) p) A (sdhTable D) := by
  have ht : mapTbl (fun s => (evalHom.pairing e g₁ g₂
      (fun _ : Unit => a)).toFun s) (sdhTable D) = (fun
      | .g₁ => List.ofFn (fun i : Fin (D + 1) => a ^ (i : ℕ) • g₁)
      | .g₂ => List.ofFn ![g₂, a • g₂] | .gₜ => []) := by
    funext s
    cases s with
    | g₁ =>
      change List.map _ (List.ofFn _) = _
      rw [List.map_ofFn]
      congr 1
      funext i
      simp only [Function.comp_apply, evalHom.pairing_apply_g₁, evalAt_apply,
        map_pow, MvPolynomial.eval_X]
      rfl
    | g₂ => simp [mapTbl, sdhTable, evalHom.pairing_apply_g₂, evalAt_apply, List.ofFn_succ]
    | gₜ => rfl
  rw [← ht]
  exact runGen_pairing_mapTbl_evalHom e g₁ g₂ hg₁ hg₂ he _ A _

private theorem sdh_lookup_map [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) (x : Unit → F)
    (tbl : Tbl (fun _ : PSort => MvPolynomial Unit F)) (h : Handle) :
    lookup (mapTbl (fun s => (evalHom.pairing e g₁ g₂ x).toFun s) tbl) .g₁ h =
      MvPolynomial.eval x (lookup tbl .g₁ h) • g₁ := by
  exact (lookup_mapTbl (fun s => (evalHom.pairing e g₁ g₂ x).toFun s) tbl .g₁ h).trans
    (by rw [evalHom.pairing_apply_g₁, evalAt_apply])

private theorem sdh_symbolic_bound [Field F] [Fintype F] [DecidableEq F]
    (D : ℕ) (A : OracleComp (genSpec F pairingSig) α) (n₁ n₂ nₜ : ℕ)
    (hn₁ : IsQueryBoundP A (appendsTo .g₁) n₁)
    (hn₂ : IsQueryBoundP A (appendsTo .g₂) n₂)
    (hnₜ : IsQueryBoundP A (appendsTo .gₜ) nₜ)
    (W : α × Tbl (fun _ : PSort => MvPolynomial Unit F) → MvPolynomial Unit F)
    (k : ℕ)
    (hW : ∀ z, DegreeLE (sdhDegree D) z.2 → (W z).totalDegree ≤ k)
    (E : (Unit → F) → (α × Tbl (fun _ : PSort => MvPolynomial Unit F)) → Prop)
    (hE : ∀ x z, DegreeLE (sdhDegree D) z.2 → E x z →
      W z ≠ 0 ∧ MvPolynomial.eval x (W z) = 0) :
    Pr{let a ← SDH.sampleTrapdoor F; let z ← (runGen (symbolic F pairingSig Unit)
      (fun _ p => MvPolynomial.eval (fun _ => a) p) A (sdhTable D))}[E (fun _ => a) z] ≤
      (((D + n₁ + 2).choose 2 * D + (n₂ + 3).choose 2 +
        (nₜ + 1).choose 2 * (D + 1) + k : ℕ) : ℝ≥0∞) /
        (Fintype.card F - 1 : ℕ) := by
  classical
  let : Fintype PSort := ⟨{.g₁, .g₂, .gₜ}, by intro s; cases s <;> simp⟩
  let n : PSort → ℕ := fun | .g₁ => n₁ | .g₂ => n₂ | .gₜ => nₜ
  have hn : ∀ s, IsQueryBoundP A (appendsTo s) (n s) := by
    intro s
    cases s
    · exact hn₁
    · exact hn₂
    · exact hnₜ
  have hb := prEvent_runGen_symbolic_le_add_of_polynomial
    ((fun a (_ : Unit) => a) <$> SDH.sampleTrapdoor F) (sdhDegree_closed D)
    (ε := fun s => (sdhDegree D s : ℝ≥0∞) / (Fintype.card F - 1 : ℕ))
    (ε' := (k : ℝ≥0∞) / (Fintype.card F - 1 : ℕ))
    (fun _ f hf hd => by simpa only [prEvent_norm] using sampleTrapdoor_root_le f hf hd)
    A hn (sdhTable D) (sdhTable_degreeLE D) W k
    (fun z hz => hW z (runGen_degreeLE (sdhDegree_closed D) _ A _ (sdhTable_degreeLE D) z hz))
    E (fun x z hz => hE x z
      (runGen_degreeLE (sdhDegree_closed D) _ A _ (sdhTable_degreeLE D) z hz))
    (fun f hf hd => by simpa only [prEvent_norm] using sampleTrapdoor_root_le f hf hd)
  simp only [prEvent_norm] at hb
  refine hb.trans_eq ?_
  change (∑ s ∈ ({.g₁, .g₂, .gₜ} : Finset PSort),
    (((sdhTable (F := F) D s).length + n s + 1).choose 2 : ℝ≥0∞) *
      ((sdhDegree D s : ℝ≥0∞) / (Fintype.card F - 1 : ℕ))) + _ = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [sdhTable, n, sdhDegree, List.length_ofFn, List.length_cons,
    List.length_nil, zero_add, Nat.cast_one]
  rw [Nat.add_right_comm D 1 n₁]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  have h₂ : 2 + (n₂ + 1) = n₂ + 3 := by omega
  rw [h₂]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, ENNReal.add_div, mul_div_assoc, mul_one_div]
  ac_rfl

end GroupModel

namespace TSDH

/-- A generic `t`-SDH adversary in a Type 3 bilinear group has success at most the
three per-sort collision terms plus `D + 1`, divided by the number of nonzero scalars.
Equality queries are free; each source or target append is charged to its own budget. -/
theorem experiment_ofGeneric_le [Field F] [Fintype F] [DecidableEq F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (D : ℕ) (A : OracleComp (genSpec F pairingSig) (F × Handle)) (n₁ n₂ nₜ : ℕ)
    (hn₁ : IsQueryBoundP A (appendsTo .g₁) n₁)
    (hn₂ : IsQueryBoundP A (appendsTo .g₂) n₂)
    (hnₜ : IsQueryBoundP A (appendsTo .gₜ) nₜ) :
    Pr{let b ← experiment g₁ g₂ (Adversary.ofGeneric (D := D) e A)}[b = true] ≤
      (((D + n₁ + 2).choose 2 * D + (n₂ + 3).choose 2 +
        (nₜ + 1).choose 2 * (D + 1) + (D + 1) : ℕ) : ℝ≥0∞) /
        (Fintype.card F - 1 : ℕ) := by
  classical
  let E := fun (x : Unit → F) (z : (F × Handle) × Tbl (fun _ : PSort => MvPolynomial Unit F)) =>
    x () + z.1.1 ≠ 0 ∧ MvPolynomial.eval x (lookup z.2 .g₁ z.1.2) = (x () + z.1.1)⁻¹
  have hr := sdh_run_map e g₁ g₂ hg₁ hg₂ he D A
  have hl := sdh_lookup_map e g₁ g₂
  have hevent : Pr{let b ← experiment g₁ g₂ (Adversary.ofGeneric (D := D) e A)}[b = true] =
      Pr{let a ← SDH.sampleTrapdoor F; let z ← (runGen (symbolic F pairingSig Unit)
        (fun _ p => MvPolynomial.eval (fun _ => a) p) A (sdhTable D))}[E (fun _ => a) z] := by
    simp only [experiment, Adversary.ofGeneric]
    dsimp only [PFam] at hr hl ⊢
    simp_rw [hr]
    simp only [prEvent_norm,
      bind_map_left, Functor.map_map, Prod.map, id_eq,
      decide_eq_true_eq, hl,
      smul_left_inj hg₁, E]
  rw [hevent]
  let W := fun (z : (F × Handle) × Tbl (fun _ : PSort => MvPolynomial Unit F)) =>
    lookup z.2 .g₁ z.1.2 * (MvPolynomial.X () + MvPolynomial.C z.1.1) - 1
  refine sdh_symbolic_bound D A n₁ n₂ nₜ hn₁ hn₂ hnₜ W (D + 1) ?_ E ?_
  · intro z hz
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      apply Nat.add_le_add (hz.lookup .g₁ z.1.2)
      exact (MvPolynomial.totalDegree_add _ _).trans (by simp)
    · simp
  · intro x z _ hz
    constructor
    · intro hw
      have hh := congrArg (MvPolynomial.eval (fun _ : Unit => -z.1.1)) hw
      simp [W] at hh
    · simp only [W, map_sub, map_mul, map_add, MvPolynomial.eval_X,
        MvPolynomial.eval_C, map_one, sub_eq_zero]
      rw [hz.2]
      exact inv_mul_cancel₀ hz.1

/-- A total group-operation budget gives a common append budget in all three sorts
for the generic `t`-SDH bound. Equality queries are free. -/
theorem experiment_ofGeneric_le_of_total [Field F] [Fintype F] [DecidableEq F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (D : ℕ) (A : OracleComp (genSpec F pairingSig) (F × Handle)) (q : ℕ)
    (hq : IsQueryBoundP A (fun i => isGroupOp i = true) q) :
    Pr{let b ← experiment g₁ g₂ (Adversary.ofGeneric (D := D) e A)}[b = true] ≤
      (((D + q + 2).choose 2 * D + (q + 3).choose 2 +
        (q + 1).choose 2 * (D + 1) + (D + 1) : ℕ) : ℝ≥0∞) /
        (Fintype.card F - 1 : ℕ) := by
  exact experiment_ofGeneric_le e g₁ g₂ hg₁ hg₂ he D A q q q
    (hq.appendsTo .g₁) (hq.appendsTo .g₂) (hq.appendsTo .gₜ)

end TSDH

namespace ARSDH

private theorem vanishing_degree [Field F] (S : Finset F) :
    let Z : MvPolynomial Unit F := ∏ s ∈ S, (MvPolynomial.X () - MvPolynomial.C s)
    Z ≠ 0 ∧ Z.totalDegree = S.card := by
  classical
  have hd (s : F) :
      (MvPolynomial.X () - MvPolynomial.C s : MvPolynomial Unit F).totalDegree = 1 := by
    rw [sub_eq_add_neg, MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt]
    · simp
    · simp
  have hn (s : F) : (MvPolynomial.X () - MvPolynomial.C s : MvPolynomial Unit F) ≠ 0 := by
    intro h
    have := hd s
    simp [h] at this
  induction S using Finset.induction_on with
  | empty => simp
  | @insert s S hs ih =>
    dsimp only at ih ⊢
    rw [Finset.prod_insert hs, Finset.card_insert_of_notMem hs]
    exact ⟨mul_ne_zero (hn s) ih.1, by
      rw [MvPolynomial.totalDegree_mul_of_isDomain (hn s) ih.1, hd, ih.2, Nat.add_comm]⟩

/-- A generic ARSDH adversary in a Type 3 bilinear group has success at most the
three per-sort collision terms plus `2 * D + 1`, divided by the number of nonzero scalars.
Nonvanishing of the output polynomial follows from the nonzero first output and the
strict degree gap between source entries and the vanishing polynomial. -/
theorem experiment_ofGeneric_le [Field F] [Fintype F] [DecidableEq F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (D : ℕ) (A : OracleComp (genSpec F pairingSig) (Finset F × Handle × Handle))
    (n₁ n₂ nₜ : ℕ)
    (hn₁ : IsQueryBoundP A (appendsTo .g₁) n₁)
    (hn₂ : IsQueryBoundP A (appendsTo .g₂) n₂)
    (hnₜ : IsQueryBoundP A (appendsTo .gₜ) nₜ) :
    Pr{let b ← experiment g₁ g₂ (Adversary.ofGeneric (D := D) e A)}[b = true] ≤
      (((D + n₁ + 2).choose 2 * D + (n₂ + 3).choose 2 +
        (nₜ + 1).choose 2 * (D + 1) + (2 * D + 1) : ℕ) : ℝ≥0∞) /
        (Fintype.card F - 1 : ℕ) := by
  classical
  let Z := fun (S : Finset F) =>
    ∏ s ∈ S, (MvPolynomial.X () - MvPolynomial.C s : MvPolynomial Unit F)
  let E := fun (x : Unit → F)
      (z : (Finset F × Handle × Handle) × Tbl (fun _ : PSort => MvPolynomial Unit F)) =>
    z.1.1.card = D + 1 ∧ MvPolynomial.eval x (Z z.1.1) ≠ 0 ∧
      MvPolynomial.eval x (lookup z.2 .g₁ z.1.2.1) ≠ 0 ∧
      MvPolynomial.eval x (lookup z.2 .g₁ z.1.2.2) =
        (MvPolynomial.eval x (Z z.1.1))⁻¹ * MvPolynomial.eval x (lookup z.2 .g₁ z.1.2.1)
  have hr := sdh_run_map e g₁ g₂ hg₁ hg₂ he D A
  have hl := sdh_lookup_map e g₁ g₂
  have hevent : Pr{let b ← experiment g₁ g₂ (Adversary.ofGeneric (D := D) e A)}[b = true] =
      Pr{let a ← SDH.sampleTrapdoor F; let z ← (runGen (symbolic F pairingSig Unit)
        (fun _ p => MvPolynomial.eval (fun _ => a) p) A (sdhTable D))}[E (fun _ => a) z] := by
    simp only [experiment, Adversary.ofGeneric]
    dsimp only [PFam] at hr hl ⊢
    simp_rw [hr]
    simp only [prEvent_norm,
      bind_map_left, Functor.map_map, Prod.map, id_eq,
      decide_eq_true_eq, hl,
      smul_smul, smul_left_inj hg₁, ne_eq, smul_eq_zero, hg₁, or_false,
      E, Z, map_prod, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
      Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [hevent]
  let W := fun (z : (Finset F × Handle × Handle) ×
      Tbl (fun _ : PSort => MvPolynomial Unit F)) =>
    if z.1.1.card = D + 1 then
      lookup z.2 .g₁ z.1.2.2 * Z z.1.1 - lookup z.2 .g₁ z.1.2.1 else 0
  refine sdh_symbolic_bound D A n₁ n₂ nₜ hn₁ hn₂ hnₜ W (2 * D + 1) ?_ E ?_
  · intro z hz
    dsimp only [W]
    split_ifs with hc
    · apply (MvPolynomial.totalDegree_sub _ _).trans
      apply max_le
      · have hb := hz.lookup .g₁ z.1.2.2
        have hZ : (Z z.1.1).totalDegree = D + 1 := (vanishing_degree z.1.1).2.trans hc
        have hm := MvPolynomial.totalDegree_mul (lookup z.2 .g₁ z.1.2.2) (Z z.1.1)
        dsimp only [sdhDegree] at hb
        omega
      · exact (hz.lookup .g₁ z.1.2.1).trans (by dsimp only [sdhDegree]; omega)
    · simp
  · intro x z hd hz
    obtain ⟨hc, hZ, ha, hab⟩ := hz
    have hw : W z = lookup z.2 .g₁ z.1.2.2 * Z z.1.1 - lookup z.2 .g₁ z.1.2.1 := by
      simp only [W, hc, ↓reduceIte]
    rw [hw]
    constructor
    · intro hzero
      have hba := sub_eq_zero.mp hzero
      have hane : lookup z.2 .g₁ z.1.2.1 ≠ 0 := by
        intro h
        exact ha (by rw [h, map_zero])
      have hbne : lookup z.2 .g₁ z.1.2.2 ≠ 0 := by
        intro h
        apply hane
        rw [← hba, h, zero_mul]
      have hdeg := congrArg MvPolynomial.totalDegree hba
      rw [MvPolynomial.totalDegree_mul_of_isDomain hbne (vanishing_degree z.1.1).1,
        (vanishing_degree z.1.1).2, hc] at hdeg
      have hda := hd.lookup .g₁ z.1.2.1
      dsimp only [sdhDegree] at hda
      omega
    · simp only [map_sub, map_mul, sub_eq_zero]
      rw [hab]
      calc
        (MvPolynomial.eval x (Z z.1.1))⁻¹ * MvPolynomial.eval x (lookup z.2 .g₁ z.1.2.1) *
            MvPolynomial.eval x (Z z.1.1) =
          ((MvPolynomial.eval x (Z z.1.1))⁻¹ * MvPolynomial.eval x (Z z.1.1)) *
            MvPolynomial.eval x (lookup z.2 .g₁ z.1.2.1) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hZ, one_mul]

/-- A total group-operation budget gives a common append budget in all three sorts
for the generic ARSDH bound. Equality queries are free. -/
theorem experiment_ofGeneric_le_of_total [Field F] [Fintype F] [DecidableEq F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (D : ℕ) (A : OracleComp (genSpec F pairingSig) (Finset F × Handle × Handle)) (q : ℕ)
    (hq : IsQueryBoundP A (fun i => isGroupOp i = true) q) :
    Pr{let b ← experiment g₁ g₂ (Adversary.ofGeneric (D := D) e A)}[b = true] ≤
      (((D + q + 2).choose 2 * D + (q + 3).choose 2 +
        (q + 1).choose 2 * (D + 1) + (2 * D + 1) : ℕ) : ℝ≥0∞) /
        (Fintype.card F - 1 : ℕ) := by
  exact experiment_ofGeneric_le e g₁ g₂ hg₁ hg₂ he D A q q q
    (hq.appendsTo .g₁) (hq.appendsTo .g₂) (hq.appendsTo .gₜ)

end ARSDH
