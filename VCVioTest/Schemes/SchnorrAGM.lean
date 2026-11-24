/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.Schnorr.AGM.Security
public import Mathlib.Algebra.Field.ZMod

/-! # Algebraic Schnorr fixtures over the field of order 101

A certified adversary requests a signature on `false` and hashes the zero commitment on
`true`. It computes the response using the transparent scalar model of the test group, so it
forges on every run, and the theorem bounds the named reduction's success below by `97 / 101`.
Sampling uses `Fin 101`, avoiding enumeration during module initialization.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction Schnorr.AGM Schnorr.AGM.Reduction
open scoped ENNReal

namespace SchnorrAGMTest

/-- Primality of the concrete test field. -/
local instance prime101 : Fact (Nat.Prime 101) := ⟨by decide⟩
/-- Uniform sampling without a load-time field enumeration. -/
local instance sampleField : SampleableType (ZMod 101) :=
  inferInstanceAs (SampleableType (Fin 101))

/-- The concrete field used by the fixture. -/
abbrev K := ZMod 101
/-- The explained request specification for the concrete fixture. -/
abbrev Spec := explainedSpec K (Group K) (Request Bool) (Reply K Bool)

/-- Explain the zero group point over any received basis. -/
@[expose] def zeroPoint {D : Type} (basis : Groups (Group K)) (data : D) :
    Explained K D (Group K) :=
  Explained.ofVectors basis data (fun _ => [fun _ => 0])

@[simp] private theorem zeroPoint_groups {D : Type} (basis : Groups (Group K)) (data : D) :
    (zeroPoint basis data).value.groups () = [0] := by
  simp [zeroPoint, Explained.ofVectors, evaluate, List.mapIdx_eq_ofFn]

@[simp] private theorem zeroPoint_data {D : Type} (basis : Groups (Group K)) (data : D) :
    (zeroPoint basis data).value.data = data := rfl

/-- A certified program making one signing request and one hash request on distinct messages. -/
@[expose] def oneHashOneSign : Schnorr.AlgebraicAdversary K K Bool where
  main input := do
    let sig ← Spec.query ⟨⟨.sign false, fun _ => []⟩, fun _ => []⟩
    let basis := extend input.groups sig.groups
    let hash ← Spec.query (zeroPoint basis (.hash true))
    pure (zeroPoint (extend basis hash.groups)
      (true, (show K from hash.data) * (input.groups ()).getD 1 0))
  algebraic input := by
    constructor
    · exact fun _ => .nil
    · intro sig
      constructor
      · exact Explained.valid_ofVectors _ _ _
      · intro hash
        exact Explained.valid_ofVectors _ _ _

/-- The concrete fixture obeys the explicit one-sign query budget on every reply path. -/
theorem oneHashOneSign_sign_bound (pk : K) :
    IsQueryBoundP (oneHashOneSign.main (initial 1 pk)) (fun q => signRequest q = true) 1 := by
  simp [oneHashOneSign, isQueryBoundP_query_bind_iff, signRequest, zeroPoint,
    Explained.ofVectors]

/-- The concrete fixture obeys the explicit one-hash query budget on every reply path. -/
theorem oneHashOneSign_hash_bound (pk : K) :
    IsQueryBoundP (oneHashOneSign.main (initial 1 pk)) (fun q => hashRequest q = true) 1 := by
  simp [oneHashOneSign, isQueryBoundP_query_bind_iff, hashRequest, zeroPoint,
    Explained.ofVectors]

/-- Erasure uses the original signature oracles, signs one message and forges on the other. -/
theorem oneHashOneSign_raw (pk : K) :
    (oneHashOneSign.toUnforgeableAdversary 1).main pk = (do
      let _ ← (rawSpec K Bool K).query (.inr false)
      let c : K ← (rawSpec K Bool K).query (.inl (.inr (true, 0)))
      pure (true, (0, c * pk))) := by
  simp only [Schnorr.AlgebraicAdversary.toUnforgeableAdversary, oracle, add_apply_inl,
    bind_pure_comp, add_apply_inr, oneHashOneSign, zeroPoint_data, List.getD_eq_getElem?_getD,
    initial, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Order.lt_two_iff,
    Std.le_refl, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Option.getD_some,
    simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    List.headD_nil, Functor.map_map, id_eq, simulateQ_map, bind_map_left, map_bind, forgery,
    zeroPoint_groups, List.headD_eq_head?_getD, List.head?_cons]
  conv_lhs =>
    enter [2, sig]
    erw [zeroPoint_groups]
  simp only [List.headD_cons]
  dsimp only [scalarReply]
  apply bind_congr
  intro sig
  rfl

/-- With no signing request the fixture exceeds the signing budget `0`. -/
theorem not_oneHashOneSign_sign_bound_zero :
    ¬ IsQueryBoundP (oneHashOneSign.main (initial 1 0)) (fun q => signRequest q = true) 0 := by
  simp [oneHashOneSign, isQueryBoundP_query_bind_iff, signRequest]

/-- The fixture exceeds the hash budget `0`. -/
theorem not_oneHashOneSign_hash_bound_zero :
    ¬ IsQueryBoundP (oneHashOneSign.main (initial 1 0)) (fun q => hashRequest q = true) 0 := by
  simp only [oneHashOneSign, zeroPoint, Explained.ofVectors, List.getD_eq_getElem?_getD,
    List.map_cons, List.ofFn_const, List.map_nil, bind_pure_comp, hashRequest,
    isQueryBoundP_query_bind_iff, Bool.false_eq_true, not_false_eq_true, lt_self_iff_false,
    or_false, ↓reduceIte, isQueryBoundP_map_iff, isQueryBoundP_query_iff, imp_false,
    not_true_eq_false, true_and, not_forall, exists_const_iff, and_true]
  exact ⟨⟨(0 : K), fun _ => []⟩⟩

/-- The fixture forges on every run: `true` is never signed, and the response `c * pk` verifies
against the zero commitment because the generator is one. -/
theorem unforgeableAdvantage_oneHashOneSign :
    SignatureAlg.unforgeableAdvantage (FiatShamir.runtime (Commit := K) (Chal := K) Bool)
      (oneHashOneSign.toUnforgeableAdversary 1) = 1 := by
  unfold SignatureAlg.unforgeableAdvantage
  rw [FiatShamir.runtime_eq_runtimeWithCache_empty, FiatShamir.runtimeWithCache_evalDist,
    show ({true} : Set Bool) = {b | b = true} by ext; simp]
  convert (evalDist_apply_setOf_simulateQ_romImpl_run'_eq_one_iff
    (SignatureAlg.unforgeableExperiment (oneHashOneSign.toUnforgeableAdversary 1)) ∅
    (fun b => b = true)).2 ?_
  intro f _
  rw [OracleComp.evalDist_apply_setOf_eq_one_iff_forall_mem_support]
  intro b hb
  simp only [SignatureAlg.unforgeableExperiment, oneHashOneSign_raw] at hb
  simp only [Schnorr.signature, FiatShamir, smul_eq_mul, DiffieHellman.dlogGenerable, mul_one,
    bind_pure_comp, liftM_map, Schnorr.sigma, HasQuery.instOfMonadLift_query, liftM_pure, map_pure,
    bind_map_left, add_apply_inr, add_apply_inl, SignatureAlg.runWithSigningOracle_def,
    SignatureAlg.signingOracle, QueryImpl.passthrough_add, simulateQ_bind, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, QueryImpl.add_apply_inr,
    QueryImpl.withLogging_apply, map_bind, Functor.map_map, id_eq, simulateQ_map,
    QueryImpl.add_apply_inl, PFunctor.Handler.liftTarget_apply, ofPFunctor_toPFunctor,
    QueryImpl.id'_apply, id_map, bind_assoc, WriterT.run_bind, WriterT.run_liftM, List.empty_eq,
    WriterT.run_tell, WriterT.run_map, List.append_nil, pure_bind, List.nil_append, ne_eq,
    Bool.false_eq_true, not_false_eq_true, QueryLog.wasQueried_cons_of_ne,
    QueryLog.wasQueried_nil, Bool.not_false, zero_add, mul_eq_mul_right_iff, Bool.decide_or,
    Bool.true_and, MonadAttach.support_bind, MonadAttach.mem_support, MonadAttach.support_map,
    Set.mem_iUnion, Set.mem_image, exists_prop, exists_and_right] at hb
  obtain ⟨sk, -, r, -, -, i, hi, x, hx, rfl⟩ := hb
  have hq : simulateQ (unifFwdAnswerImpl f) (liftM ((Bool × K →ₒ K).query (true, 0))) =
      (pure (f (true, 0)) : ProbComp K) := by
    change simulateQ (unifSpec.passthrough + f.liftTarget ProbComp)
      (liftM ((Bool × K →ₒ K).query (true, 0))) = _
    exact QueryImpl.simulateQ_add_liftM_query_right
      (unifSpec.passthrough : QueryImpl unifSpec ProbComp) (f.liftTarget ProbComp) (true, 0)
  rw [hq] at hx
  change MonadAttach.CanReturn (pure (f (true, 0)) : ProbComp K) i at hi
  simp only [MonadAttach.canReturn_pure_iff] at hi hx
  subst hi hx
  simp

/-- The bound is not vacuous here: the named reduction solves discrete log with probability at
least `97 / 101`. -/
theorem one_le_prEvent_agmReduction_add :
    1 ≤ Pr{let b ← (DiffieHellman.dlogExperiment (1 : K)
      (Schnorr.agmReduction 1 oneHashOneSign))}[b = true] + 4 / 101 := by
  have hg : Function.Bijective (fun x : K => x • (1 : K)) :=
    ⟨fun a b hab => by simpa using hab, fun b => ⟨b, by simp⟩⟩
  have h := Schnorr.unforgeableAdvantage_le_of_algebraic (1 : K) hg oneHashOneSign 1 1
    oneHashOneSign_sign_bound oneHashOneSign_hash_bound
  rw [unforgeableAdvantage_oneHashOneSign] at h
  refine h.trans (le_of_eq ?_)
  rw [ZMod.card, add_assoc, ENNReal.div_add_div_same]
  norm_num

private theorem oneHashOneSign_run (pk : K) :
    run 1 pk oneHashOneSign = (do
      let c ← $ᵗ K
      let z ← $ᵗ K
      let h ← $ᵗ K
      pure ((true, h * pk / h),
        record (signedState {} 1 pk false c z) (true, 0) ⟨0, 0⟩ h)) := by
  simp only [run, oneHashOneSign, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  conv_lhs =>
    enter [1]
    dsimp only [handler, StateT.run]
  simp only [initial, bind_assoc, pure_bind]
  apply bind_congr
  intro c
  apply bind_congr
  intro z
  simp [zeroPoint, Explained.ofVectors, extend, scalarReply, signingReply,
    finish, Reduction.read, signedState, programEntry_eq, flatten, combine,
    initialRepresentations, record, evaluate, List.mapIdx_eq_ofFn]
  simp [Reduction.read, StateT.run]

/-- An actual reduction run with secret 7, signing coins 3 and 11, and hash answer 5
accepts and extracts 7. The signing commitment is 91 in the field of order 101. -/
theorem explicit_run :
    ((true, (7 : K)), record (signedState {} 1 7 false (3 : K) 11) (true, 0) ⟨0, 0⟩ 5) ∈
      support (run 1 7 oneHashOneSign) := by
  rw [oneHashOneSign_run, mem_support_bind_iff]
  refine ⟨3, by simp, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨11, by simp, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨5, by simp, ?_⟩
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, true_and]
  refine ⟨?_, trivial⟩
  apply (eq_div_iff (by decide : (5 : K) ≠ 0)).2
  ring

/-- The named DLog reduction outputs the secret on the explicit run above. -/
theorem explicit_run_extraction :
    (7 : K) ∈ support (Schnorr.agmReduction 1 oneHashOneSign 1 7) := by
  rw [Schnorr.agmReduction, support_map]
  exact ⟨_, explicit_run, rfl⟩

end SchnorrAGMTest
