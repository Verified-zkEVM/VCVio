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

A generic adversary receives `Fintype.card ι` challenge elements as its initial table.
With at most `q`
group operations, its relation-finding probability is at most
`((q + Fintype.card ι + 1).choose 2 + 1) / |F|`. The master bound T3 compares
the hidden-point run directly with the exact symbolic run. A nonzero output coefficient vector
defines a nonzero
linear polynomial, bounded by Schwartz–Zippel. No reduction cost certificate is needed.

The bound depends on the basis cardinality: free equality tests among the given elements reveal
relations on collisions. The generator is not an additional initial table entry.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace GroupModel

variable {F G ι : Type}

/-- Interpret a generic coefficient-valued computation on the table of supplied group elements.
The table contains exactly `Fintype.card ι` entries, without an additional generator entry. -/
@[expose] noncomputable def DiscreteLogRelation.Adversary.ofGeneric
    [Fintype ι] [Field F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (A : OracleComp (genSpec F groupSig) (ι → F)) :
    _root_.DiscreteLogRelation.Adversary F G ι unifSpec :=
  fun xs => Prod.fst <$> runGen (Model.group G) (fun _ => id) A
    (fun _ => List.ofFn (xs ∘ (Fintype.equivFin ι).symm))

private theorem relation_event_le [Fintype ι] [DecidableEq ι]
    [Field F] [Fintype F] [SampleableType F]
    (a : ι → F) :
    Pr{let x ← $ᵗ (ι → F)}[a ≠ 0 ∧ ∑ i, a i * x i = 0] ≤
      (1 : ℝ≥0∞) / Fintype.card F := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  simpa only [ha, ne_eq, not_false_eq_true, true_and] using
    _root_.DiscreteLogRelation.prEvent_sum_mul_eq_zero_le a ha

/-- A generic relation adversary given a finite basis and at most `q` group operations
succeeds with probability at most `((q + Fintype.card ι + 1).choose 2 + 1) / |F|`. Equality queries
are free, and handles outside the table retain the ordinary zero-default semantics. -/
theorem experiment_ofGeneric_le [Fintype ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (g : G) (hg : g ≠ 0) (A : OracleComp (genSpec F groupSig) (ι → F))
    (q : ℕ) (hq : IsQueryBoundP A (fun i => isGroupOp i = true) q) :
    Pr{let b ← (_root_.DiscreteLogRelation.plainExperiment g
      (DiscreteLogRelation.Adversary.ofGeneric (G := G) A))}[b = true] ≤
      (((q + Fintype.card ι + 1).choose 2 + 1 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  classical
  let tbl : Tbl (fun _ : Unit => MvPolynomial ι F) :=
    fun _ => List.ofFn (MvPolynomial.X ∘ (Fintype.equivFin ι).symm)
  have hd : DegreeLE 1 tbl := by
    intro s p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    simp
  let E := fun (x : ι → F)
      (z : (ι → F) × Tbl (fun _ : Unit => MvPolynomial ι F)) =>
    z.1 ≠ 0 ∧ ∑ i, z.1 i * x i = 0
  have hr (x : ι → F) :
      runGen (Model.group G) (fun _ => id) A
        (fun _ => List.ofFn (fun j => x ((Fintype.equivFin ι).symm j) • g)) =
        Prod.map id (mapTbl (fun _ => evalAt g x)) <$>
          runGen (symbolic F groupSig ι) (fun _ p => MvPolynomial.eval x p) A tbl := by
    have ht : mapTbl (fun _ : Unit => evalAt g x) tbl =
        (fun _ => List.ofFn (fun j => x ((Fintype.equivFin ι).symm j) • g)) := by
      funext u
      simp [mapTbl, tbl, evalAt_apply, List.map_ofFn, Function.comp_def]
    rw [← ht]
    exact runGen_group_mapTbl_evalAt g hg x A tbl
  have he : Pr{let b ← (_root_.DiscreteLogRelation.plainExperiment g
        (DiscreteLogRelation.Adversary.ofGeneric (G := G) A))}[b = true] =
      Pr{let x ← $ᵗ (ι → F); let z ← (runGen (symbolic F groupSig ι)
        (fun _ p => MvPolynomial.eval x p) A tbl)}[E x z] := by
    simp only [_root_.DiscreteLogRelation.plainExperiment, DiscreteLogRelation.Adversary.ofGeneric,
      _root_.DiscreteLogRelation.experiment, _root_.DiscreteLogRelation.plainAdversary,
      StateT.run'_eq, _root_.DiscreteLogRelation.map_run_plainImpl,
      Function.comp_def, hr, prEvent_norm, decide_eq_true_eq, Prod.map, id_eq, smul_smul,
      ← Finset.sum_smul, smul_eq_zero, hg, or_false, E]
  rw [he]
  let : MeasurableSpace ((ι → F) ×
      ((ι → F) × Tbl (fun _ : Unit => MvPolynomial ι F))) := ⊤
  have hm := (prEvent_runGen_symbolic_le_add ($ᵗ (ι → F))
    (fun f hf hd => prob_eval_zero_univ_le_div f hf hd) A hq tbl hd
    {w | E w.1 w.2} (MeasurableSet.of_discrete)).1
  have hs : Pr{let x ← $ᵗ (ι → F); let z ← (runGen (symbolic F groupSig ι)
      (fun _ => id) A tbl)}[E x z] ≤ (1 : ℝ≥0∞) / Fintype.card F := by
    rw [prEvent_bind_map_swap]
    simpa only [map_bind, Functor.map_map, id_eq] using
      prEvent_bind_le_of_forall_le
        (runGen (symbolic F groupSig ι) (fun _ => id) A tbl)
        (fun z => (fun x => E x z) <$> ($ᵗ (ι → F) : ProbComp _)) id
        (fun z => by simpa only [Functor.map_map, id_eq, E] using relation_event_le z.1)
  simp only [Set.mem_ofPred_eq, Nat.cast_one] at hm
  refine hm.trans ((add_le_add hs le_rfl).trans_eq ?_)
  simp only [Fintype.sum_unique, tbl,
    List.length_ofFn, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul]
  rw [Nat.add_comm (Fintype.card ι) q, add_mul, one_mul, add_comm]

end GroupModel
