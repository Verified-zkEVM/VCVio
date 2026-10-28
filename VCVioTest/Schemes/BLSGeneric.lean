/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.BLS.Generic.Security
public import VCVio.Schemes.BLS.Generic.ReductionCost
public import VCVio.CryptoFoundations.GroupModel.PairingExecution
public import VCVio.CryptoFoundations.GroupModel.DLog11
public import Mathlib.Algebra.Field.ZMod
import all VCVio.Schemes.BLS.Generic.Adversary
import all VCVio.CryptoFoundations.GroupModel.Instances

/-! # Generic BLS translation and Type 3 DLog regression tests

A handle adversary hashes and signs one message, computes a pairing and a target equality,
and returns a scaled signature on a different message. Tests check its protocol, separate
query budgets and exact forgetful translation. The scalar-recovery fixture instantiates the
independent generic DLog bound numerically over the field with 101 elements.
-/

public section

open OracleComp OracleSpec GroupModel GroupModel.Interaction
open scoped ENNReal

namespace BLSGenericTest

attribute [local implicit_reducible] spec handleSpec

/-- The field used by the concrete generic-group fixtures. -/
abbrev K := ZMod 101

/-- The regression field has prime cardinality. -/
local instance prime101 : Fact (Nat.Prime 101) := ⟨by decide⟩
/-- Sampling uses the direct finite representation without enumerating a field at load time. -/
local instance sampleField : SampleableType K := inferInstanceAs (SampleableType (Fin 101))
/-- Equality is decided separately at each of the three pairing sorts. -/
local instance pairingEq : ∀ s, DecidableEq (PFam K K K s)
  | .g₁ => inferInstanceAs (DecidableEq K)
  | .g₂ => inferInstanceAs (DecidableEq K)
  | .gₜ => inferInstanceAs (DecidableEq K)

/-- Hash and sign `false`, exercise the target group, and return a scaled signature on `true`. -/
@[expose] def scaledSignature : BLS.Generic.Adversary K Bool := fun _ => do
  let hashed ← (BLS.Generic.adversarySpec K Bool).query
    (.inr (.inr (.inr ⟨.inl false, fun _ => []⟩)))
  let signed ← (BLS.Generic.adversarySpec K Bool).query
    (.inr (.inr (.inr ⟨.inr false, fun _ => []⟩)))
  let t ← (BLS.Generic.adversarySpec K Bool).query
    (.inl (.bil () ((hashed.groups .g₁).headD 0) 1))
  let same : Bool ← (BLS.Generic.adversarySpec K Bool).query (.inl (.eq .gₜ t t))
  let sig ← (BLS.Generic.adversarySpec K Bool).query
    (.inl (.smul .g₁ (if same then 2 else 3) ((signed.groups .g₁).headD 0)))
  return ⟨true, fun | .g₁ => [sig] | .g₂ => [] | .gₜ => []⟩

/-- Every reply path of the explicit handle program obeys the BLS message protocol. -/
theorem scaledSignature_protocol : BLS.Generic.FollowsProtocol scaledSignature := by
  intro input
  simp only [scaledSignature, allPathsSatisfy_query_bind, allPathsSatisfy_pure,
    Set.mem_univ, forall_const]
  simp

/-- Pairing and scaling cost two group operations; target equality is free. -/
theorem scaledSignature_group_budget (input : Message Unit (fun _ : PSort => Handle)) :
    IsQueryBoundP (scaledSignature input) (fun i => isGroupOp i = true) 2 := by
  simp [scaledSignature, isGroupOp, GroupModel.Query.isOp]

/-- The explicit program makes one direct hash request. -/
theorem scaledSignature_hash_budget (input : Message Unit (fun _ : PSort => Handle)) :
    IsQueryBoundP (scaledSignature input) BLS.Generic.isHash 1 := by
  simp [scaledSignature, BLS.Generic.isHash]

/-- The explicit program makes one signing request. -/
theorem scaledSignature_sign_budget (input : Message Unit (fun _ : PSort => Handle)) :
    IsQueryBoundP (scaledSignature input) BLS.Generic.isSign 1 := by
  simp [scaledSignature, BLS.Generic.isSign]

/-- Real execution queries the two BLS oracles and returns twice the signing reply. -/
theorem scaledSignature_real_main (pk : K × K) :
    (scaledSignature.toUnforgeableAdversary (LinearMap.mul K K) 1 1).main pk = (do
      let _ ← (BLS.AGM.rawSpec Bool K).query (.inl (.inr false))
      let sig : K ← (BLS.AGM.rawSpec Bool K).query (.inr false)
      pure (true, (2 : K) • sig)) := by
  simp only [BLS.Generic.Adversary.toUnforgeableAdversary, lookupMessage,
    List.headD_eq_head?_getD, List.head?_map, HandleAdversary.run, run, scaledSignature,
    add_apply_inr, add_apply_inl, bind_pure_comp, simulateQ_bind, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, QueryImpl.add_apply_inr, id_map,
    QueryImpl.add_apply_inl, impl, lookup, List.getD_eq_getElem?_getD, id_eq, decide_true,
    LawfulMonadStateOf.get_map_const, map_pure, simulateQ_map, ite_smul, pure_bind,
    ↓dreduceIte, ↓reduceIte, BLS.Generic.initialInput, StateT.run_bind, StateT.run_map,
    map_bind, Functor.map_map, List.head?_cons, Option.map_some, Option.getD_some, smul_eq_mul]
  unfold liftGame BLS.Generic.oracle
  simp [StateT.run, lookupMessage, pushGroups, push, append, pairingSig, PFam]
  rfl

/-- The translated certificate forgets to the same real BLS adversary through ordinary imports. -/
theorem scaledSignature_forget :
    (scaledSignature.toAlgebraic scaledSignature_protocol
      (LinearMap.mul K K) 1 1).toUnforgeableAdversary =
      scaledSignature.toUnforgeableAdversary (LinearMap.mul K K) 1 1 :=
  BLS.Generic.Adversary.toAlgebraic_toUnforgeableAdversary _ _ _ _ _

/-- The pairing fixture enters the original BLS advantage through the algebraic theorem. -/
theorem scaledSignature_algebraic_bound :
    SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (Bool →ₒ K))
      (scaledSignature.toUnforgeableAdversary (LinearMap.mul K K) 1 1) ≤
      Pr{let b ← DLog11.experiment (1 : K) 1 (BLS.goodReduction
      (scaledSignature.toAlgebraic scaledSignature_protocol (LinearMap.mul K K) 1 1))}[b = true] +
      Pr{let b ← DLog11.experiment (1 : K) 1 (BLS.badReduction
      (scaledSignature.toAlgebraic scaledSignature_protocol (LinearMap.mul K K) 1 1))}[b = true] +
      1 / 101 := by
  simpa only [ZMod.card, Nat.cast_ofNat] using
    BLS.unforgeableAdvantage_le_of_generic_algebraic
    scaledSignature scaledSignature_protocol (LinearMap.mul K K) 1 1
    (by simpa only [smul_eq_mul, mul_one] using
      (show Function.Bijective (fun x : K => x) from ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩))
    (by simpa only [LinearMap.mul_apply', one_mul] using (one_ne_zero : (1 : K) ≠ 0))

/-- One target-group operation gives the common-exponent bound `15/101` in `DLog11`. -/
theorem dlog11_pairing_bound :
    let A : OracleComp (genSpec K pairingSig) K := do
      let _ ← (genSpec K pairingSig).query (.inl (.bil () 1 1))
      pure 0
    Pr{let b ← (DLog11.experiment (1 : K) 1
        (DLog11.Adversary.ofGeneric (LinearMap.mul K K) A))}[b = true] ≤ (15 / 101 : ℝ≥0∞) := by
  dsimp only
  apply (DLog11.experiment_ofGeneric_le_of_total
    (LinearMap.mul K K) 1 1 one_ne_zero one_ne_zero
    (by simpa only [LinearMap.mul_apply', one_mul] using (one_ne_zero : (1 : K) ≠ 0))
    _ 1 ?_).trans
  · norm_num [ZMod.card, Nat.choose]
  · exact ⟨by decide, fun _ => trivial⟩

/-- The concrete adversary's good reduction spends at most seven group operations. -/
theorem scaledSignature_goodProgram_budget :
    IsQueryBoundP (BLS.Generic.goodProgram scaledSignature)
      (fun i => isGroupOp i = true) 7 :=
  BLS.Generic.isQueryBoundP_goodProgram scaledSignature 2 1 1
    (scaledSignature_group_budget _) (scaledSignature_hash_budget _)
    (scaledSignature_sign_budget _)

/-- The concrete adversary's bad reduction spends at most fourteen group operations. -/
theorem scaledSignature_badProgram_budget :
    IsQueryBoundP (BLS.Generic.badProgram scaledSignature)
      (fun i => isGroupOp i = true) 14 :=
  BLS.Generic.isQueryBoundP_badProgram scaledSignature 2 1 1
    (scaledSignature_group_budget _) (scaledSignature_hash_budget _)
    (scaledSignature_sign_budget _)

/-- The named good generic reduction instantiates the unconditional DLog bound at `147/101`. -/
theorem scaledSignature_goodProgram_bound :
    Pr{let b ← (DLog11.experiment (1 : K) 1
      (DLog11.Adversary.ofGeneric (LinearMap.mul K K)
        (BLS.Generic.goodProgram scaledSignature)))}[b = true] ≤ (147 / 101 : ℝ≥0∞) := by
  apply (DLog11.experiment_ofGeneric_le_of_total
    (LinearMap.mul K K) 1 1 one_ne_zero one_ne_zero
    (by simpa only [LinearMap.mul_apply', one_mul] using (one_ne_zero : (1 : K) ≠ 0))
    _ 7 scaledSignature_goodProgram_budget).trans
  norm_num [ZMod.card, Nat.choose]

/-- The named bad generic reduction instantiates the unconditional DLog bound at `483/101`. -/
theorem scaledSignature_badProgram_bound :
    Pr{let b ← (DLog11.experiment (1 : K) 1
      (DLog11.Adversary.ofGeneric (LinearMap.mul K K)
        (BLS.Generic.badProgram scaledSignature)))}[b = true] ≤ (483 / 101 : ℝ≥0∞) := by
  apply (DLog11.experiment_ofGeneric_le_of_total
    (LinearMap.mul K K) 1 1 one_ne_zero one_ne_zero
    (by simpa only [LinearMap.mul_apply', one_mul] using (one_ne_zero : (1 : K) ≠ 0))
    _ 14 scaledSignature_badProgram_budget).trans
  norm_num [ZMod.card, Nat.choose]

/-- Real tracked execution retains the concrete adversary's complete explained output. -/
theorem scaledSignature_tracked
    (random : QueryImpl unifSpec ProbComp)
    (handler : QueryImpl (plainSpec (fun _ : Bool => K)
      (BLS.Generic.Query Bool) (fun _ => Unit)) ProbComp)
    (st : Pairing.Tracked K (fun _ : Bool => K) K) :
    simulateQ (fun q => withCoins random handler q.value)
      (Pairing.explainProgram (LinearMap.mul K K)
        (scaledSignature BLS.Generic.reductionInput) st) =
      (fun z => explain z.2.1 (Pairing.sourceMessage z.1)) <$>
        (simulateQ (Pairing.trackedImpl (LinearMap.mul K K) random handler)
          (scaledSignature BLS.Generic.reductionInput)).run st :=
  Pairing.explainProgram_run_tracked _ _ _ _ _

/-- Repeated replies remain separate coefficient positions, including zero-valued receipts. -/
theorem repeatedReceipts_coefficients :
    let st := BLS.Generic.initialReductionState (F := K) (M := Bool) 1 1
    let st' := BLS.Generic.reductionReceive
      (BLS.Generic.reductionReceive st false false 7) true false 8
    let scaled := Pairing.step (0 : K →ₗ[K] K →ₗ[K] K) (.smul .g₁ 2 3) st'.metadata
    (explain scaled.2.1 (⟨(), fun | false => [scaled.1] | true => []⟩ :
      Message Unit (fun _ : Bool => Handle))).coefficients false = [[0, 0, 0, 2]] := by
  simp [BLS.Generic.initialReductionState, BLS.Generic.reductionReceive,
    Pairing.step, receive, receiveAt, groupStep, explain, trackInputs, append, lookup]

/-- The good algebraic reduction agrees with its generic program on arbitrary challenge points. -/
theorem scaledSignature_goodReduction (X Y : K) :
    BLS.goodReduction (scaledSignature.toAlgebraic scaledSignature_protocol
      (LinearMap.mul K K) 1 1) 1 X 1 Y =
      DLog11.Adversary.ofGeneric (LinearMap.mul K K)
        (BLS.Generic.goodProgram scaledSignature) 1 X 1 Y :=
  BLS.Generic.goodReduction_toAlgebraic _ _ _ _ _ _ _

/-- The bad algebraic reduction agrees with its generic program, including sampled signing keys. -/
theorem scaledSignature_badReduction (X Y : K) :
    BLS.badReduction (scaledSignature.toAlgebraic scaledSignature_protocol
      (LinearMap.mul K K) 1 1) 1 X 1 Y =
      DLog11.Adversary.ofGeneric (LinearMap.mul K K)
        (BLS.Generic.badProgram scaledSignature) 1 X 1 Y :=
  BLS.Generic.badReduction_toAlgebraic _ _ _ _ _ _ _

/-- The unconditional theorem elaborates through public imports with the concrete bound `967/101`.
The small test field checks the arithmetic and API; this numerical upper bound exceeds one. -/
theorem scaledSignature_generic_bound :
    SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (Bool →ₒ K))
      (scaledSignature.toUnforgeableAdversary (LinearMap.mul K K) 1 1) ≤
      (967 / 101 : ℝ≥0∞) := by
  simpa only [ZMod.card, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Nat.cast_ofNat] using
    BLS.unforgeableAdvantage_le_generic scaledSignature scaledSignature_protocol
      (LinearMap.mul K K) 1 1
      (by simpa only [smul_eq_mul, mul_one] using
        (show Function.Bijective (fun x : K => x) from ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩))
      (by simpa only [LinearMap.mul_apply', one_mul] using (one_ne_zero : (1 : K) ≠ 0))
      2 1 1 (scaledSignature_group_budget _) (scaledSignature_hash_budget _)
      (scaledSignature_sign_budget _)

end BLSGenericTest
