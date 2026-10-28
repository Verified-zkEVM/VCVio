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
`true`. It computes the response using the transparent scalar model of the test group.
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
  protocol input := by
    rw [allPathsSatisfy_query_bind]
    refine ⟨rfl, fun sig _ => ?_⟩
    rw [allPathsSatisfy_query_bind]
    refine ⟨?_, fun hash _ => ?_⟩
    · change ((zeroPoint _ (Request.hash true)).value.groups ()).length = 1
      rw [zeroPoint_groups]
      rfl
    · simp only [allPathsSatisfy_pure, zeroPoint_groups, List.length_singleton]

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

/-- The averaged extractor bound specializes to the explicit one-hash, one-sign fixture. -/
theorem oneHashOneSign_extraction_bound :
    Pr{let x ← $ᵗ K; let p ← (Schnorr.AGM.Reduction.run 1
      (x • (1 : K)) oneHashOneSign)}[p.1.1 = true] ≤
      Pr{let b ← (DiffieHellman.dlogExperiment (1 : K)
        (Schnorr.agmReduction 1 oneHashOneSign))}[b = true] + (2 / 101 : ℝ≥0∞) := by
  have h := run_success_le_dlogExperiment (1 : K)
    (by intro a b hab; simpa using hab) oneHashOneSign 1 oneHashOneSign_hash_bound
  simpa [div_eq_mul_inv, show (1 + 1 : ℝ≥0∞) = 2 from by norm_num] using h

/-- The original Schnorr EUF-CMA theorem instantiated with one signing and one hash request. -/
theorem oneHashOneSign_security :
    SignatureAlg.unforgeableAdvantage
        (FiatShamir.runtime (Commit := K) (Chal := K) Bool)
        (oneHashOneSign.toUnforgeableAdversary 1) ≤
      Pr{let b ← (DiffieHellman.dlogExperiment (1 : K)
        (Schnorr.agmReduction 1 oneHashOneSign))}[b = true] +
        (2 / 101 : ℝ≥0∞) + (2 / 101 : ℝ≥0∞) := by
  have hg : Function.Bijective (fun x : K => x • (1 : K)) := by
    constructor
    · intro a b hab
      simpa using hab
    · intro b
      exact ⟨b, by simp⟩
  simpa [show (1 + 1 : ℝ≥0∞) = 2 from by norm_num] using
    Schnorr.unforgeableAdvantage_le_of_algebraic (1 : K) hg
    oneHashOneSign 1 1 oneHashOneSign_sign_bound oneHashOneSign_hash_bound

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
  simp only [initial, ne_eq, not_true_eq_false, ite_false, bind_assoc, pure_bind]
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
