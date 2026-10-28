/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.Pedersen
public import VCVio.CryptoFoundations.GroupModel.GenericHardness
import Mathlib.Data.List.GetD

/-!
# Unconditional generic binding of Pedersen commitments

A generic binder making at most `q` group operations wins the Pedersen binding experiment
with probability at most `((q + 9).choose 2 + 1) / |F|`. The existing Pedersen reduction
is realized by a generic discrete-logarithm solver with six additional group operations.
-/

public section

open OracleComp OracleSpec CommitmentScheme DiffieHellman GroupModel
open scoped ENNReal

namespace pedersenCommit

variable {F G : Type}

/-- Run a generic binder on the table `[g, h]` and read its commitment handle, returning zero
for an out-of-range handle, together with its two message/randomness pairs. -/
@[expose] def BindingAdversary.ofGeneric [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq G] (g : G)
    (A : OracleComp (genSpec F groupSig) (Handle × F × F × F × F)) :
    CommitmentScheme.BindingAdversary G F G F := fun h =>
  (fun z => (lookup z.2 () z.1.1, z.1.2)) <$>
    runGen (Model.group G) (fun _ => id) A (fun _ => [g, h])

/-- Extract a discrete logarithm from a generic binder using four scalar multiplications,
two additions, and two free equality tests. The first fresh handle identifies the old table
length, so invalid commitment handles retain their zero interpretation during verification. -/
@[expose] def dlogOfGeneric [Field F] [DecidableEq F]
    (A : OracleComp (genSpec F groupSig) (Handle × F × F × F × F)) :
    OracleComp (genSpec F groupSig) F := do
  let out ← A
  let (c, m₁, d₁, m₂, d₂) := out
  let aRaw ← OracleComp.lift ((genSpec F groupSig).query (.inl (.smul () d₁ 0)))
  let a : Handle := aRaw
  let bRaw ← OracleComp.lift ((genSpec F groupSig).query (.inl (.smul () m₁ 1)))
  let b : Handle := bRaw
  let uRaw ← OracleComp.lift ((genSpec F groupSig).query (.inl (.add () a b)))
  let u : Handle := uRaw
  let eRaw ← OracleComp.lift ((genSpec F groupSig).query (.inl (.smul () d₂ 0)))
  let e : Handle := eRaw
  let fRaw ← OracleComp.lift ((genSpec F groupSig).query (.inl (.smul () m₂ 1)))
  let f : Handle := fRaw
  let vRaw ← OracleComp.lift ((genSpec F groupSig).query (.inl (.add () e f)))
  let v : Handle := vRaw
  let c' := if c < a then c else a + 6
  let ok₁Raw ← OracleComp.lift ((genSpec F groupSig).query (.inl (.eq () u c')))
  let ok₁ : Bool := ok₁Raw
  let ok₂Raw ← OracleComp.lift ((genSpec F groupSig).query (.inl (.eq () v c')))
  let ok₂ : Bool := ok₂Raw
  pure (if m₁ ≠ m₂ ∧ ok₁ = true ∧ ok₂ = true then (d₁ - d₂) / (m₂ - m₁) else 0)

private def checkOpenings [Field F] [DecidableEq F]
    (out : Handle × F × F × F × F) : OracleComp (genSpec F groupSig) F :=
  dlogOfGeneric (pure out)

/-- Verifying the two openings adds at most six group operations to the binder's budget. -/
theorem isQueryBoundP_dlogOfGeneric [Field F] [DecidableEq F]
    (A : OracleComp (genSpec F groupSig) (Handle × F × F × F × F)) (q : ℕ)
    (hq : IsQueryBoundP A (fun i => isGroupOp i = true) q) :
    IsQueryBoundP (dlogOfGeneric A) (fun i => isGroupOp i = true) (q + 6) := by
  apply isQueryBoundP_bind hq
  rintro ⟨c, m₁, d₁, m₂, d₂⟩ _
  simp [isQueryBoundP_query_bind_iff, isGroupOp, Query.isOp, OracleComp.lift]

private theorem runGen_bind [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    {α β : Type} (A : OracleComp (genSpec F groupSig) α)
    (B : α → OracleComp (genSpec F groupSig) β) (tbl : Tbl (fun _ : Unit => G)) :
    runGen (Model.group G) (fun _ => id) (A >>= B) tbl =
      (runGen (Model.group G) (fun _ => id) A tbl >>= fun z =>
        runGen (Model.group G) (fun _ => id) (B z.1) z.2) := by
  simp only [runGen, run, simulateQ_bind, StateT.run_bind]

private theorem runGen_smul [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (tbl : Tbl (fun _ : Unit => G)) (d : F) (a : Handle) :
    runGen (Model.group G) (fun _ => id)
      (OracleComp.lift ((genSpec F groupSig).query (.inl (.smul () d a)))) tbl =
      pure ((tbl ()).length, append tbl () (d • lookup tbl () a)) := rfl

private theorem runGen_add [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (tbl : Tbl (fun _ : Unit => G)) (a b : Handle) :
    runGen (Model.group G) (fun _ => id)
      (OracleComp.lift ((genSpec F groupSig).query (.inl (.add () a b)))) tbl =
      pure ((tbl ()).length, append tbl () (lookup tbl () a + lookup tbl () b)) := rfl

private theorem runGen_eq [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (tbl : Tbl (fun _ : Unit => G)) (a b : Handle) :
    runGen (Model.group G) (fun _ => id)
      (OracleComp.lift ((genSpec F groupSig).query (.inl (.eq () a b)))) tbl =
      pure (decide (lookup tbl () a = lookup tbl () b), tbl) := rfl

private theorem runGen_pure [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    {α : Type} (tbl : Tbl (fun _ : Unit => G)) (a : α) :
    runGen (Model.group (F := F) G) (fun _ => id) (pure a) tbl = pure (a, tbl) := rfl

private theorem getD_append_guard [Zero G] (xs ys : List G) (c : Handle) :
    (xs ++ ys).getD (if c < xs.length then c else xs.length + ys.length) 0 =
      xs.getD c 0 := by
  by_cases hc : c < xs.length
  · rw [ite_eq_left hc, List.getD_append _ _ _ _ hc]
  · rw [ite_eq_right hc, List.getD_eq_default _ _ (by simp),
      List.getD_eq_default _ _ (Nat.le_of_not_gt hc)]

private theorem run_checkOpenings [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (g h : G) (tail : List G) (c : Handle) (m₁ d₁ m₂ d₂ : F) :
    Prod.fst <$> runGen (Model.group G) (fun _ => id)
      (checkOpenings (c, m₁, d₁, m₂, d₂)) (fun _ => g :: h :: tail) =
    pure (if m₁ ≠ m₂ ∧ d₁ • g + m₁ • h = (g :: h :: tail).getD c 0 ∧
        d₂ • g + m₂ • h = (g :: h :: tail).getD c 0 then
      (d₁ - d₂) / (m₂ - m₁) else 0) := by
  unfold checkOpenings dlogOfGeneric
  rw [pure_bind]
  erw [runGen_bind, runGen_smul, pure_bind,
    runGen_bind, runGen_smul, pure_bind,
    runGen_bind, runGen_add, pure_bind,
    runGen_bind, runGen_smul, pure_bind,
    runGen_bind, runGen_smul, pure_bind,
    runGen_bind, runGen_add, pure_bind,
    runGen_bind, runGen_eq, pure_bind,
    runGen_bind, runGen_eq, pure_bind, runGen_pure, map_pure]
  have hc := getD_append_guard (g :: h :: tail)
    [d₁ • g, m₁ • h, d₁ • g + m₁ • h, d₂ • g, m₂ • h, d₂ • g + m₂ • h] c
  simpa [lookup, append] using congrArg (fun value : G =>
    (pure (if m₁ ≠ m₂ ∧ d₁ • g + m₁ • h = value ∧ d₂ • g + m₂ • h = value then
      (d₁ - d₂) / (m₂ - m₁) else 0) : ProbComp F)) hc

/-- Interpreting the generic extractor on `[g, h]` gives exactly the existing Pedersen
reduction applied to the interpreted generic binder. -/
theorem dlogReduction_ofGeneric_eq [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G] (g h : G)
    (A : OracleComp (genSpec F groupSig) (Handle × F × F × F × F)) :
    dlogReduction (BindingAdversary.ofGeneric g A) g h =
      DLogAdversary.ofGeneric (dlogOfGeneric A) g h := by
  have he : dlogOfGeneric A = A >>= checkOpenings := by
    rfl
  simp only [dlogReduction, BindingAdversary.ofGeneric, DLogAdversary.ofGeneric,
    he, runGen_bind, map_bind, bind_map_left]
  apply bind_congr_of_forall_mem_support
  rintro ⟨⟨c, m₁, d₁, m₂, d₂⟩, tbl⟩ hz
  have hp := runGen_prefix (Model.group G) (fun _ => id) A (fun _ => [g, h])
    ((c, m₁, d₁, m₂, d₂), tbl) hz ()
  obtain ⟨tail, ht⟩ := hp
  have ht' : tbl = fun _ => g :: h :: tail := by
    funext u
    cases u
    simpa using ht.symm
  subst tbl
  rw [run_checkOpenings]
  congr 1
  apply if_congr
  · exact decide_eq_true_iff
  · rfl
  · rfl

/-- The Pedersen reduction and its generic realization induce identical DLog experiments. -/
theorem dlogExperiment_dlogReduction_ofGeneric [Field F] [DecidableEq F]
    [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G] (g : G)
    (A : OracleComp (genSpec F groupSig) (Handle × F × F × F × F)) :
    dlogExperiment g (dlogReduction (BindingAdversary.ofGeneric g A)) =
      dlogExperiment g (DLogAdversary.ofGeneric (dlogOfGeneric A)) := by
  simp only [dlogExperiment, dlogReduction_ofGeneric_eq]

/-- A generic binder using at most `q` group operations wins the unchanged Pedersen binding
experiment with probability at most `((q + 9).choose 2 + 1) / |F|`. -/
theorem bindingAdvantage_ofGeneric_le [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G] {g : G}
    (hg : Function.Bijective (· • g : F → G))
    (A : OracleComp (genSpec F groupSig) (Handle × F × F × F × F)) (q : ℕ)
    (hq : IsQueryBoundP A (fun i => isGroupOp i = true) q) :
    bindingAdvantage (pedersenCommit g) (BindingAdversary.ofGeneric g A) ≤
      (((q + 9).choose 2 + 1 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  have hg0 : g ≠ 0 := by
    intro h
    have h01 : (0 : F) = 1 := hg.1 (by simp [h])
    exact zero_ne_one h01
  apply (binding_le_dlog hg (BindingAdversary.ofGeneric g A)).trans
  rw [dlogExperiment_dlogReduction_ofGeneric, ← prEvent_eq_evalDist_singleton]
  simpa only [Nat.add_assoc] using
    dlogExperiment_ofGeneric_le g hg0 (dlogOfGeneric A) (q + 6)
      (isQueryBoundP_dlogOfGeneric A q hq)

end pedersenCommit
