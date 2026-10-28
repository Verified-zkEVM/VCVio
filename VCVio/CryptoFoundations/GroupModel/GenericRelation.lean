/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.DiscreteLogRelation
public import VCVio.CryptoFoundations.GroupModel.GenericHardness

/-!
# Generic hardness of discrete-log relations

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

private theorem relation_event_le [Field F] [Fintype F] [SampleableType F]
    (a : Fin n → F) :
    Pr{let x ← $ᵗ (Fin n → F)}[a ≠ 0 ∧ ∑ i, a i * x i = 0] ≤
      (1 : ℝ≥0∞) / Fintype.card F := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  let p : MvPolynomial (Fin n) F := ∑ i, MvPolynomial.C (a i) * MvPolynomial.X i
  have hn : p ≠ 0 := by
    intro h
    apply ha
    funext i
    have he := congrArg (MvPolynomial.eval (Pi.single i 1)) h
    simpa [p, Pi.single_apply, mul_ite] using he
  have hd : p.totalDegree ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  simpa [p, ha] using prob_eval_zero_univ_le_div p hn hd

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
  have hd : DegreeLE 1 tbl := by
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
  let : MeasurableSpace ((Fin n → F) ×
      ((Fin n → F) × Tbl (fun _ : Unit => MvPolynomial (Fin n) F))) := ⊤
  have hm := (prEvent_runGen_symbolic_le_add ($ᵗ (Fin n → F))
    (fun f hf hd => prob_eval_zero_univ_le_div f hf hd) A hq tbl hd
    {w | E w.1 w.2} (MeasurableSet.of_discrete)).1
  have hs : Pr{let x ← $ᵗ (Fin n → F); let z ← (runGen (symbolic F groupSig (Fin n))
      (fun _ => id) A tbl)}[E x z] ≤ (1 : ℝ≥0∞) / Fintype.card F := by
    rw [prEvent_bind_map_swap]
    simpa only [map_bind, Functor.map_map, id_eq] using
      prEvent_bind_le_of_forall_le
        (runGen (symbolic F groupSig (Fin n)) (fun _ => id) A tbl)
        (fun z => (fun x => E x z) <$> ($ᵗ (Fin n → F) : ProbComp _)) id
        (fun z => by simpa only [Functor.map_map, id_eq, E] using relation_event_le z.1)
  simp only [Set.mem_ofPred_eq, Nat.cast_one] at hm
  refine hm.trans ((add_le_add hs le_rfl).trans_eq ?_)
  simp only [Fintype.sum_unique, tbl,
    List.length_ofFn, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul]
  rw [Nat.add_comm n q, add_mul, one_mul, add_comm]

end GroupModel
