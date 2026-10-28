/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.DiscreteLogRelation
public import VCVio.CryptoFoundations.GroupModel.GenericHardness

/-! # Generic hardness of discrete-log relations

A generic adversary receives the `n` challenge elements as its initial table. With at most `q`
group operations, its relation-finding probability is at most
`((q + n + 1).choose 2 + 1) / |F|`. The master bound T3 compares the hidden-point run directly
with the exact symbolic run; a nonzero output coefficient vector then defines a nonzero
linear polynomial, bounded by Schwartz–Zippel. No reduction cost certificate is needed.

The bound must depend on `n`: free equality tests among the given elements already reveal
relations on collisions. The generator is not an additional initial table entry.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace GroupModel

variable {F G : Type} {n : ℕ}

/-- Interpret a generic coefficient-valued computation on the table of supplied group elements.
The table contains exactly `n` entries, without an additional generator entry. -/
@[expose] def DiscreteLogRelation.Adversary.ofGeneric [Field F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (A : OracleComp (genSpec F groupSig) (Fin n → F)) :
    _root_.DiscreteLogRelation.Adversary F G n :=
  fun xs => Prod.fst <$> runGen (Model.group G) (fun _ => id) A (fun _ => List.ofFn xs)

/-- A generic relation adversary on `n` given elements with at most `q` group operations
succeeds with probability at most `((q + n + 1).choose 2 + 1) / |F|`. Equality queries are free,
and handles outside the table retain the ordinary zero-default semantics. -/
theorem experiment_ofGeneric_le [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (g : G) (hg : g ≠ 0) (A : OracleComp (genSpec F groupSig) (Fin n → F))
    (q : ℕ) (hq : IsQueryBoundP A (fun i => isGroupOp i = true) q) :
    Pr{let b ← (_root_.DiscreteLogRelation.experiment g
      (DiscreteLogRelation.Adversary.ofGeneric (G := G) A))}[b = true] ≤
      (((q + n + 1).choose 2 + 1 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  classical
  let tbl : Tbl (fun _ : Unit => MvPolynomial (Fin n) F) :=
    fun _ => List.ofFn MvPolynomial.X
  have hd : DegreeLE (fun _ => 1) tbl := by
    intro s p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    simp
  let E := fun (x : Fin n → F)
      (z : (Fin n → F) × Tbl (fun _ : Unit => MvPolynomial (Fin n) F)) =>
    z.1 ≠ 0 ∧ ∑ i, z.1 i * x i = 0
  have hr (x : Fin n → F) :
      runGen (Model.group G) (fun _ => id) A (fun _ => List.ofFn (fun i => x i • g)) =
        Prod.map id (mapTbl (fun _ => evalAt g x)) <$>
          runGen (symbolic F groupSig (Fin n)) (fun _ p => MvPolynomial.eval x p) A tbl := by
    have ht : mapTbl (fun _ : Unit => evalAt g x) tbl =
        (fun _ => List.ofFn (fun i => x i • g)) := by
      funext u
      simp [mapTbl, tbl, evalAt_apply, List.map_ofFn, Function.comp_def]
    rw [← ht]
    exact runGen_group_mapTbl_evalAt g hg x A tbl
  have he : Pr{let b ← (_root_.DiscreteLogRelation.experiment g
        (DiscreteLogRelation.Adversary.ofGeneric (G := G) A))}[b = true] =
      Pr{let x ← $ᵗ (Fin n → F); let z ← (runGen (symbolic F groupSig (Fin n))
        (fun _ p => MvPolynomial.eval x p) A tbl)}[E x z] := by
    simp only [_root_.DiscreteLogRelation.experiment, DiscreteLogRelation.Adversary.ofGeneric,
      hr, prEvent_norm, decide_eq_true_eq, Prod.map, id_eq, smul_smul,
      ← Finset.sum_smul, smul_eq_zero, hg, or_false, E]
  rw [he]
  let W := fun (z : (Fin n → F) × Tbl (fun _ : Unit => MvPolynomial (Fin n) F)) =>
    ∑ i, MvPolynomial.C (z.1 i) * MvPolynomial.X i
  have hW (z : (Fin n → F) × Tbl (fun _ : Unit => MvPolynomial (Fin n) F)) :
      (W z).totalDegree ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  have hE (x : Fin n → F)
      (z : (Fin n → F) × Tbl (fun _ : Unit => MvPolynomial (Fin n) F))
      (he : E x z) : W z ≠ 0 ∧ MvPolynomial.eval x (W z) = 0 := by
    constructor
    · intro h
      apply he.1
      funext i
      have hx := congrArg (MvPolynomial.eval (Pi.single i 1)) h
      simpa [W, Pi.single_apply, mul_ite] using hx
    · simpa [W] using he.2
  have h := computational_runGen_symbolic_le ($ᵗ (Fin n → F))
    (degreeClosed_discreteSig (fun _ : Unit => 1))
    (fun _ f hf hd => prob_eval_zero_univ_le_div f hf hd) A
    (fun s => hq.appendsTo s) tbl hd W 1 (fun z _ => hW z) E
    (fun x z _ he => hE x z he)
    (fun f hf hd => prob_eval_zero_univ_le_div f hf hd)
  refine h.trans_eq ?_
  simp only [Fintype.sum_unique, tbl, List.length_ofFn, Nat.cast_one,
    Nat.add_comm n q, Nat.cast_add, ENNReal.add_div]
  simp [div_eq_mul_inv]

end GroupModel
