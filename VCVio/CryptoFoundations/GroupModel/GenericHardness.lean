/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.MasterBound
public import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
Generic hardness of discrete logarithms and computational Diffie–Hellman

Generic computations induce ordinary adversaries by interpreting their handles in a module.
Polynomial collision bounds control their success, including handles outside the table.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace GroupModel

variable {F G ι α : Type}

/-- Run a generic scalar-valued computation on the generator and challenge, returning its guess. -/
@[expose] def DLogAdversary.ofGeneric [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (A : OracleComp (genSpec F groupSig) F) : DiffieHellman.DLogAdversary F G :=
  fun g X => Prod.fst <$> runGen (Model.group G) (fun _ => id) A (fun _ => [g, X])

/-- Run a generic handle-valued computation on the generator and two challenges, then read its
output handle; an out-of-range handle returns zero. -/
@[expose] def CDHAdversary.ofGeneric [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (A : OracleComp (genSpec F groupSig) Handle) : DiffieHellman.CDHAdversary F G :=
  fun g X Y => (fun z => lookup z.2 () z.1) <$>
    runGen (Model.group G) (fun _ => id) A (fun _ => [g, X, Y])

/-- Evaluating a symbolic table at a hidden point commutes with running the generic
computation in a module with a nonzero generator. -/
theorem runGen_group_mapTbl_evalAt [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]
    [DecidableEq G] (g : G) (hg : g ≠ 0) (x : ι → F)
    (A : OracleComp (genSpec F (discreteSig Unit)) α)
    (tbl : Tbl (fun _ : Unit => MvPolynomial ι F)) :
    runGen (Model.group G) (fun _ => id) A (mapTbl (fun _ => evalAt g x) tbl) =
      Prod.map id (mapTbl (fun _ => evalAt g x)) <$>
        runGen (symbolic F (discreteSig Unit) ι) (fun _ p => MvPolynomial.eval x p) A tbl := by
  have h := runGen_map (evalHom.discrete (fun _ : Unit => g) x) (fun _ => id) A tbl
  have he : (fun s => ⇑((evalHom.discrete (fun _ : Unit => g) x).toFun s)) =
      (fun _ => ⇑(evalAt g x)) := by
    funext s p
    exact evalHom.discrete_apply _ _ _ _
  simp only [Function.comp_def, id_eq, evalHom.discrete_apply] at h
  rw [he] at h
  change runGen (Model.discrete (fun _ : Unit => G)) _ _ _ = _
  rw [← h]
  congr 1
  unfold runGen run
  rw [impl_congr (symbolic F (discreteSig Unit) ι) (fun _ p => evalAt g x p)
    (fun _ p => MvPolynomial.eval x p) (by
      intro s p r
      simpa only [Function.comp_apply, id_eq, evalAt_apply] using
        (smul_left_injective F hg).eq_iff) ProbComp]

private theorem uniform_unit [SampleableType F] :
    (fun a (_ : Unit) => a) <$> ($ᵗ F : ProbComp F) =ᵈ
      ($ᵗ (Unit → F) : ProbComp (Unit → F)) := by
  apply SampleableType.map_uniformSample_evalDistEq_of_bijective
  exact ⟨fun _ _ h => congrFun h (), fun f => ⟨f (), by funext u; cases u; rfl⟩⟩

private theorem uniform_bool [SampleableType F] :
    (do let a ← $ᵗ F; let b ← $ᵗ F; pure (fun i : Bool => if i then b else a)) =ᵈ
      ($ᵗ (Bool → F) : ProbComp (Bool → F)) := by
  have hb : Function.Bijective (Function.uncurry (fun (a b : F) (i : Bool) =>
      if i then b else a)) := by
    constructor
    · intro a b h
      apply Prod.ext
      · simpa [Function.uncurry] using congrFun h false
      · simpa [Function.uncurry] using congrFun h true
    · intro f
      exact ⟨(f false, f true), by funext i; cases i <;> rfl⟩
  apply EvalDistEq.of_forall_prEvent_eq
  intro p
  simpa only [prEvent_norm] using
    SampleableType.prEvent_uniformSample_pair_of_bijective hb p

/-- A generic discrete-logarithm adversary using at most `q` group operations succeeds with
probability at most `((q + 3).choose 2 + 1) / |F|`. Equality queries are free. -/
theorem dlogExperiment_ofGeneric_le [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (g : G) (hg : g ≠ 0) (A : OracleComp (genSpec F groupSig) F)
    (q : ℕ) (hq : IsQueryBoundP A (fun i => isGroupOp i = true) q) :
    Pr{let b ← DiffieHellman.dlogExperiment g (DLogAdversary.ofGeneric (G := G) A)}[b = true] ≤
      (((q + 3).choose 2 + 1 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  let tbl : Tbl (fun _ : Unit => MvPolynomial Unit F) := fun _ => [1, MvPolynomial.X ()]
  have hd : DegreeLE (fun _ => 1) tbl := by
    intro s p hp
    simp only [tbl, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp
  have hr (a : F) :
      runGen (Model.group G) (fun _ => id) A (fun _ => [g, a • g]) =
        Prod.map id (mapTbl (fun _ => evalAt g (fun _ : Unit => a))) <$>
          runGen (symbolic F groupSig Unit)
            (fun _ p => MvPolynomial.eval (fun _ : Unit => a) p) A tbl := by
    have ht : mapTbl (fun _ : Unit => evalAt g (fun _ : Unit => a)) tbl =
        (fun _ => [g, a • g]) := by
      funext u
      simp [mapTbl, tbl, evalAt_apply]
    rw [← ht]
    exact runGen_group_mapTbl_evalAt g hg (fun _ : Unit => a) A tbl
  have hs := (uniform_unit (F := F)).bind_left (fun x =>
    (fun z => z.1 = x ()) <$> runGen (symbolic F groupSig Unit)
      (fun _ p => MvPolynomial.eval x p) A tbl)
  have he : Pr{let b ← (DiffieHellman.dlogExperiment g
      (DLogAdversary.ofGeneric (G := G) A))}[b = true] =
      Pr{let x ← $ᵗ (Unit → F); let z ← (runGen (symbolic F groupSig Unit)
        (fun _ p => MvPolynomial.eval x p) A tbl)}[z.1 = x ()] := by
    simpa only [DiffieHellman.dlogExperiment, DLogAdversary.ofGeneric, hr,
      prEvent_norm, bind_map_left, Functor.map_map, Function.comp_def,
      Prod.map, id_eq, decide_eq_true_eq] using hs.prEvent_eq id
  rw [he]
  let W := fun (z : F × Tbl (fun _ : Unit => MvPolynomial Unit F)) =>
    MvPolynomial.X () - MvPolynomial.C z.1
  have hW (z : F × Tbl (fun _ : Unit => MvPolynomial Unit F)) :
      (W z).totalDegree ≤ 1 := by
    exact (MvPolynomial.totalDegree_sub_C_le _ _).trans (by simp)
  have hE (x : Unit → F) (z : F × Tbl (fun _ : Unit => MvPolynomial Unit F))
      (h : z.1 = x ()) : W z ≠ 0 ∧ MvPolynomial.eval x (W z) = 0 := by
    constructor
    · intro he
      have hd := congrArg MvPolynomial.totalDegree (sub_eq_zero.mp he)
      simp at hd
    · simp [W, h]
  have h := prEvent_runGen_symbolic_le_add_of_polynomial ($ᵗ (Unit → F))
    (degreeClosed_discreteSig (fun _ : Unit => 1))
    (fun _ f hf hd => prob_eval_zero_univ_le_div f hf hd) A
    (fun s => hq.appendsTo s) tbl hd W 1 (fun z _ => hW z)
    (fun x z => z.1 = x ()) (fun x z _ he => hE x z he)
    (fun f hf hd => prob_eval_zero_univ_le_div f hf hd)
  refine h.trans_eq ?_
  simp only [Fintype.sum_unique, tbl, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.cast_one, Nat.add_comm 2 q, Nat.add_assoc, Nat.cast_add, ENNReal.add_div]
  simp [div_eq_mul_inv]

/-- A generic computational Diffie–Hellman adversary using at most `q` group operations
succeeds with probability at most `((q + 4).choose 2 + 2) / |F|`. Equality queries are free. -/
theorem cdhExperiment_ofGeneric_le [Field F] [Fintype F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (g : G) (hg : g ≠ 0) (A : OracleComp (genSpec F groupSig) Handle)
    (q : ℕ) (hq : IsQueryBoundP A (fun i => isGroupOp i = true) q) :
    Pr{let b ← DiffieHellman.cdhExperiment g (CDHAdversary.ofGeneric (G := G) A)}[b = true] ≤
      (((q + 4).choose 2 + 2 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  classical
  let tbl : Tbl (fun _ : Unit => MvPolynomial Bool F) :=
    fun _ => [1, MvPolynomial.X false, MvPolynomial.X true]
  have hd : DegreeLE (fun _ => 1) tbl := by
    intro s p hp
    simp only [tbl, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp
  have hr (a b : F) :
      runGen (Model.group G) (fun _ => id) A (fun _ => [g, a • g, b • g]) =
        Prod.map id (mapTbl (fun _ => evalAt g (fun i : Bool => if i then b else a))) <$>
          runGen (symbolic F groupSig Bool)
            (fun _ p => MvPolynomial.eval (fun i : Bool => if i then b else a) p) A tbl := by
    have ht : mapTbl (fun _ : Unit => evalAt g (fun i : Bool => if i then b else a)) tbl =
        (fun _ => [g, a • g, b • g]) := by
      funext u
      simp [mapTbl, tbl, evalAt_apply]
    rw [← ht]
    exact runGen_group_mapTbl_evalAt g hg (fun i : Bool => if i then b else a) A tbl
  let E := fun (x : Bool → F) (z : Handle × Tbl (fun _ : Unit => MvPolynomial Bool F)) =>
    MvPolynomial.eval x (lookup z.2 () z.1) = x false * x true
  have hs := (uniform_bool (F := F)).bind_left (fun x =>
    E x <$> runGen (symbolic F groupSig Bool) (fun _ p => MvPolynomial.eval x p) A tbl)
  have he : Pr{let b ← (DiffieHellman.cdhExperiment g
      (CDHAdversary.ofGeneric (G := G) A))}[b = true] =
      Pr{let x ← $ᵗ (Bool → F); let z ← (runGen (symbolic F groupSig Bool)
        (fun _ p => MvPolynomial.eval x p) A tbl)}[E x z] := by
    simpa only [DiffieHellman.cdhExperiment, CDHAdversary.ofGeneric, hr,
      prEvent_norm, bind_map_left, Functor.map_map, Function.comp_def,
      Prod.map, id_eq, decide_eq_true_eq, lookup_mapTbl, evalAt_apply,
      smul_left_inj hg, E, Bool.false_eq_true, ↓reduceIte] using hs.prEvent_eq id
  rw [he]
  let target : MvPolynomial Bool F := MvPolynomial.X false * MvPolynomial.X true
  let W := fun (z : Handle × Tbl (fun _ : Unit => MvPolynomial Bool F)) =>
    target - lookup z.2 () z.1
  have ht : target.totalDegree = 2 := by
    rw [MvPolynomial.totalDegree_mul_of_isDomain (MvPolynomial.X_ne_zero false)
      (MvPolynomial.X_ne_zero true)]
    simp
  have hp (z : Handle × Tbl (fun _ : Unit => MvPolynomial Bool F))
      (hz : z ∈ support (runGen (symbolic F groupSig Bool) (fun _ => id) A tbl)) :
      (lookup z.2 () z.1).totalDegree ≤ 1 :=
    (runGen_degreeLE (degreeClosed_discreteSig (fun _ : Unit => 1))
      (fun _ => id) A tbl hd z hz).lookup () z.1
  have hW (z : Handle × Tbl (fun _ : Unit => MvPolynomial Bool F))
      (hz : z ∈ support (runGen (symbolic F groupSig Bool) (fun _ => id) A tbl)) :
      (W z).totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_sub _ _).trans (max_le (by omega) ((hp z hz).trans (by omega)))
  have hE (x : Bool → F) (z : Handle × Tbl (fun _ : Unit => MvPolynomial Bool F))
      (hz : z ∈ support (runGen (symbolic F groupSig Bool) (fun _ => id) A tbl))
      (he : E x z) : W z ≠ 0 ∧ MvPolynomial.eval x (W z) = 0 := by
    constructor
    · intro heq
      have heq := congrArg MvPolynomial.totalDegree (sub_eq_zero.mp heq)
      have hdeg := hp z hz
      omega
    · simpa only [W, target, map_sub, map_mul, MvPolynomial.eval_X, sub_eq_zero] using he.symm
  have h := prEvent_runGen_symbolic_le_add_of_polynomial ($ᵗ (Bool → F))
    (degreeClosed_discreteSig (fun _ : Unit => 1))
    (fun _ f hf hd => prob_eval_zero_univ_le_div f hf hd) A
    (fun s => hq.appendsTo s) tbl hd W 2 hW E hE
    (fun f hf hd => prob_eval_zero_univ_le_div f hf hd)
  refine h.trans_eq ?_
  simp only [Fintype.sum_unique, tbl, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.cast_one, Nat.add_comm 3 q, Nat.add_assoc, Nat.cast_add, ENNReal.add_div]
  simp [div_eq_mul_inv]

end GroupModel
