/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.AGM.Security
import all VCVio.Schemes.BLS.AGM.Reductions
public import Mathlib.Algebra.Field.ZMod

/-! # Concrete algebraic BLS fixtures over the field of order 101

Multiplication is the pairing and both generators are one. Each fixture asks one hash query.
`oneHash` explains its output by the newly received point; `keyReader` reads the secret scalar
off the public key, since the first generator is one, and forges on every run, so the theorem's
two reductions together must succeed with probability at least `100 / 101`. Sampling uses
`Fin 101` directly, so module initialization does not enumerate a field.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction
open scoped ENNReal

namespace BLSAGMTest

/-- Primality of the concrete test field. -/
local instance prime101 : Fact (Nat.Prime 101) := ⟨by decide⟩
/-- Uniform sampling through `Fin 101`, without a load-time enumeration. -/
local instance sampleField : SampleableType (ZMod 101) :=
  inferInstanceAs (SampleableType (Fin 101))

/-- The test field. -/
abbrev K := ZMod 101
/-- The two source groups, both the test field. -/
abbrev Groups := BLS.AGM.Group K K
/-- The algebraic adversary's oracle family. -/
abbrev Spec := explainedSpec K Groups (BLS.AGM.Query Bool) BLS.AGM.Reply

/-- Output the hash reply itself as the signature on `false`. -/
def output (inputs : GroupModel.Interaction.Groups Groups)
    (reply : Message Unit Groups) : Explained K Bool Groups :=
  Explained.ofVectors (extend inputs reply.groups) false (fun s => match s with
    | false => [fun i => if i.val = (inputs false).length then 1 else 0]
    | true => [])

/-- Ask for the hash of `false` and return it as the signature. -/
def oneHash : BLS.AlgebraicAdversary K Bool K K (LinearMap.mul K K) 1 1 where
  main input := do
    let reply ← Spec.query ⟨⟨.inl (.inr false), BLS.AGM.groupInputs [] []⟩, fun _ => []⟩
    return output input.groups reply
  algebraic input := by
    constructor
    · exact fun s => by cases s <;> exact .nil
    · intro reply
      exact Explained.valid_ofVectors _ _ _

/-- `oneHash` forgets to the ordinary hash-and-return program. -/
theorem oneHash_toUnforgeableAdversary (pk : K × K) :
    oneHash.toUnforgeableAdversary.main pk = (do
      let h ← (BLS.AGM.rawSpec Bool K).query (.inl (.inr false))
      pure (false, h)) := by
  simp [BLS.AlgebraicAdversary.toUnforgeableAdversary, oneHash, BLS.AGM.oracle,
    output, Explained.ofVectors,
    BLS.AGM.forgery, BLS.AGM.initialInput, BLS.AGM.groupInputs, extend, evaluate]

/-- The good reduction against `oneHash` computes `ρ / ρ` for a uniform `ρ`. -/
theorem goodReduction_oneHash (X Y : K) :
    BLS.goodReduction oneHash 1 X 1 Y = (fun ρ : K => ρ / ρ) <$> ($ᵗ K) := by
  simp only [BLS.goodReduction, BLS.reductionRun,
    GroupModel.LinearFunctional.extractionProgram, smul_eq_mul, mul_one, BLS.AGM.oracle,
    add_apply_inl, bind_pure_comp, add_apply_inr, oneHash, output, Explained.ofVectors, extend,
    evaluate, List.length_append, List.getElem?_ofFn, Fin.cast_mk, BLS.AGM.initialInput,
    BLS.AGM.groupInputs, List.cons_append, List.nil_append, List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, simulateQ_map, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, Functor.map_map, id_eq, id_map, StateT.run_map, bind_map_left,
    simulateQ_bind, QueryImpl.add_apply_inr, QueryImpl.withCaching_apply, uniformSampleImpl_apply,
    map_bind, StateT.run'_eq, StateT.run_bind, StateT.run_get, pure_bind, BLS.coefficients,
    List.isEmpty_iff, List.headD_eq_head?_getD, List.mapIdx_cons, Nat.ofNat_pos, ↓reduceDIte,
    Fin.zero_eta, Fin.isValue, Option.getD_some, Nat.one_lt_ofNat, Fin.mk_one, Nat.lt_add_one,
    Fin.reduceFinMk, List.mapIdx_nil, List.sum_cons, List.sum_nil, add_zero, List.map_cons,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, OfNat.zero_ne_ofNat, ↓reduceIte, Nat.one_mod,
    OfNat.one_ne_ofNat, zero_mul, Nat.mod_succ, one_mul, List.map_nil, List.cons_ne_self,
    List.ofFn_succ, Fin.val_succ, Nat.reduceEqDiff, zero_ne_one, Fin.val_eq_zero, List.ofFn_zero,
    List.head?_cons, getElem?_pos, List.getElem_cons_zero, zero_smul, List.getElem?_cons_succ,
    Order.lt_two_iff, zero_le]
  rw [GroupModel.LinearFunctional.transcriptOracle_hash]
  simp [GroupModel.LinearFunctional.readTranscript]

/-- Returning the first generator guesses the sampled scalar with probability exactly `1/101`
in the concrete (1,1)-DLog experiment. -/
theorem dlog11_identity_guess_probability :
    Pr{let b ← (DLog11.experiment (1 : ZMod 101) (1 : ZMod 101)
      (fun g _ _ _ => pure g))}[b = true] = (1 / 101 : ℝ≥0∞) := by
  simp only [DLog11.experiment_eq, prEvent_norm, decide_eq_true_eq]
  simpa [eq_comm] using
    SampleableType.prEvent_uniformSample_eq_singleton (1 : ZMod 101)

/-- Explain `pk₁ • h` by the coefficient `pk₁` on the hash reply `h`, the third received
first-source point after the generator and the public key. -/
def keyOutput (inputs : GroupModel.Interaction.Groups Groups)
    (reply : Message Unit Groups) : Explained K Bool Groups :=
  Explained.ofVectors (extend inputs reply.groups) false (fun s => match s with
    | false => [fun i => if i.val = (inputs false).length then (inputs false).getD 1 0 else 0]
    | true => [])

/-- Ask for the hash of `false` and sign it with the scalar read off the public key. -/
def keyReader : BLS.AlgebraicAdversary K Bool K K (LinearMap.mul K K) 1 1 where
  main input := do
    let reply ← Spec.query ⟨⟨.inl (.inr false), BLS.AGM.groupInputs [] []⟩, fun _ => []⟩
    return keyOutput input.groups reply
  algebraic input := by
    constructor
    · exact fun s => by cases s <;> exact .nil
    · intro reply
      exact Explained.valid_ofVectors _ _ _

/-- `keyReader` forgets to hashing `false` and multiplying by the first public-key point. -/
theorem keyReader_toUnforgeableAdversary (pk : K × K) :
    keyReader.toUnforgeableAdversary.main pk = (do
      let h : K ← (BLS.AGM.rawSpec Bool K).query (.inl (.inr false))
      pure (false, pk.1 * h)) := by
  simp [BLS.AlgebraicAdversary.toUnforgeableAdversary, keyReader, BLS.AGM.oracle,
    keyOutput, Explained.ofVectors,
    BLS.AGM.forgery, BLS.AGM.initialInput, BLS.AGM.groupInputs, extend, evaluate]

/-- `keyReader` forges on every run. -/
theorem unforgeableAdvantage_keyReader :
    SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (Bool →ₒ K))
      keyReader.toUnforgeableAdversary = 1 := by
  unfold SignatureAlg.unforgeableAdvantage
  rw [ProbCompRuntime.rom_evalDist]
  change 𝒟[_] {b | b = true} = 1
  rw [evalDist_apply_setOf_simulateQ_romImpl_run'_eq_one_iff]
  intro f _
  rw [OracleComp.evalDist_apply_setOf_eq_one_iff_forall_mem_support]
  intro b hb
  simp only [SignatureAlg.unforgeableExperiment, keyReader_toUnforgeableAdversary, BLS.scheme,
    smul_eq_mul, mul_one, bind_pure_comp, LinearMap.mul_apply_apply, LinearMap.mul_apply',
    add_apply_inl, add_apply_inr, SignatureAlg.runWithSigningOracle_def,
    SignatureAlg.signingOracle, QueryImpl.passthrough_add, simulateQ_bind, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, QueryImpl.add_apply_inl,
    QueryImpl.liftTarget_apply, QueryImpl.id'_apply, id_map,
    simulateQ_map, Functor.map_map, WriterT.run_liftM, List.empty_eq, WriterT.run_map,
    bind_map_left, QueryLog.wasQueried_nil, Bool.not_false, Bool.true_and,
    MonadAttach.support_bind, MonadAttach.mem_support, MonadAttach.support_map, Set.mem_iUnion,
    Set.mem_image, exists_prop] at hb
  obtain ⟨i, -, i₁, hi₁, x, hx, rfl⟩ := hb
  have hq : simulateQ (unifFwdAnswerImpl f) (liftM ((Bool →ₒ K).query false)) =
      (pure (f false) : ProbComp K) := by
    change simulateQ (unifSpec.passthrough + f.liftTarget ProbComp)
      (liftM ((Bool →ₒ K).query false)) = _
    exact QueryImpl.simulateQ_add_liftM_query_right
      (unifSpec.passthrough : QueryImpl unifSpec ProbComp) (f.liftTarget ProbComp) false
  rw [hq] at hx
  change MonadAttach.CanReturn (pure (f false) : ProbComp K) i₁ at hi₁
  simp only [MonadAttach.canReturn_pure_iff] at hi₁ hx
  subst hi₁ hx
  simp [mul_comm]

/-- The bound is not vacuous here: the two named reductions together solve (1,1)-DLog with
probability at least `100 / 101`. -/
theorem one_le_prEvent_goodReduction_add_badReduction :
    1 ≤ Pr{let b ← DLog11.experiment (1 : K) (1 : K) (BLS.goodReduction keyReader)}[b = true] +
      Pr{let b ← DLog11.experiment (1 : K) (1 : K) (BLS.badReduction keyReader)}[b = true] +
      1 / 101 := by
  have h := BLS.unforgeableAdvantage_le_of_algebraic keyReader (fun a => ⟨a, by simp⟩) (by simp)
  simpa [unforgeableAdvantage_keyReader] using h

end BLSAGMTest
