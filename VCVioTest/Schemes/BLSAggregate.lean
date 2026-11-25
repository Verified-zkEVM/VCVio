/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Aggregate.Security
public import Mathlib.Algebra.Field.ZMod

/-! # Aggregate BLS regression theorems

Concrete two-signer verification and duplicate-message rejection over `ZMod 101` with
multiplication as the pairing. A separate two-dimensional second-source example records
the distinction between a linear source map and compatibility with the pairing.
A one-hash, one-sign adversary instantiates the Type 2 security theorem with loss four; its
three budgets are tight, and it always wins, so the theorem bounds the named reduction's success
below by `1 / 4`.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace BLSAggregateTest

/-- Primality of the local test field. -/
local instance prime101 : Fact (Nat.Prime 101) := ⟨by decide⟩

/-- Sample through `Fin 101` without enumerating a finite type at module initialization. -/
local instance sampleField : SampleableType (ZMod 101) :=
  inferInstanceAs (SampleableType (Fin 101))

local notation "toyScheme" =>
  BLS.Aggregate.scheme (M := Bool) (LinearMap.mul (ZMod 101) (ZMod 101)) 1

/-- Signers with secrets two and three sign different messages with hashes seven and five;
their aggregate signature is 29 and verifies. -/
theorem two_signer_correctness :
    simulateQ (unifFwdAnswerImpl
      (⟨fun b => if b then 5 else 7⟩ : QueryImpl (Bool →ₒ ZMod 101) Id))
      ((toyScheme).aggregateVerify [(2, false), (3, true)] 29) =
        (pure true : ProbComp Bool) := by
  have h := BLS.Aggregate.aggregateVerify_honest
    (LinearMap.mul (ZMod 101) (ZMod 101)) 1 (fun b : Bool => if b then 5 else 7)
    [(2, false), (3, true)] (by simp)
  norm_num at h ⊢
  exact h

/-- The scheme rejects repeated messages even when both component signatures are honest. -/
theorem duplicate_message_rejected :
    (toyScheme).aggregateVerify [(2, false), (3, false)] 35 = pure false := by
  exact BLS.Aggregate.aggregateVerify_eq_false_of_not_nodup _ _ _ _ (by simp)

/-- A zero-query adversary returning a singleton has budgets zero, zero, and one. -/
theorem zero_query_bound :
    let A : AggregateSignatureAlg.UnforgeableAdversary toyScheme :=
      ⟨fun pk => pure ([(pk, false)], 0)⟩
    A.RomQueryBound 0 0 1 := by
  simp [AggregateSignatureAlg.UnforgeableAdversary.RomQueryBound]

/-- Hash `true`, sign `false`, and return the aggregate of the honest signatures on both
messages: the public key times the hash of `true`, plus the signature on `false`. -/
@[expose] def adversary : AggregateSignatureAlg.UnforgeableAdversary toyScheme := ⟨fun pk => do
  let h : ZMod 101 ←
    ((unifSpec + (Bool →ₒ ZMod 101)) + (Bool →ₒ ZMod 101)).query (.inl (.inr true))
  let σ : ZMod 101 ←
    ((unifSpec + (Bool →ₒ ZMod 101)) + (Bool →ₒ ZMod 101)).query (.inr false)
  return ([(pk, true), (pk, false)], pk * h + σ)⟩

/-- The adversary makes one hash query and one signing query and names two pairs. -/
theorem adversary_romQueryBound : adversary.RomQueryBound 1 1 2 := by
  intro pk
  refine ⟨?_, ?_, ?_⟩
  · simp [adversary, isQueryBoundP_query_bind_iff, SignatureAlg.IsHashQuery]
  · simp [adversary, isQueryBoundP_query_bind_iff, SignatureAlg.IsSignQuery]
  · intro z hz
    simp only [adversary, support_bind, support_query, Set.mem_iUnion, Set.mem_univ,
      exists_true_left, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨h, σ, rfl⟩ := hz
    simp

/-- The hash budget is tight. -/
theorem not_adversary_romQueryBound_hash : ¬ adversary.RomQueryBound 0 1 2 := fun h => by
  simpa [adversary, isQueryBoundP_query_bind_iff, SignatureAlg.IsHashQuery] using (h 0).1

/-- The signing budget is tight. -/
theorem not_adversary_romQueryBound_sign : ¬ adversary.RomQueryBound 1 0 2 := fun h => by
  simpa [adversary, isQueryBoundP_query_bind_iff, SignatureAlg.IsHashQuery,
    SignatureAlg.IsSignQuery] using (h 0).2.1

/-- The forgery-length budget is tight: the adversary names two pairs. -/
theorem not_adversary_romQueryBound_length : ¬ adversary.RomQueryBound 1 1 1 := fun h => by
  have hz : (([(0, true), (0, false)], 0 * 0 + 0) : List (ZMod 101 × Bool) × ZMod 101) ∈
      support (adversary.main 0) := by
    simp only [adversary, support_bind, support_query, Set.mem_iUnion, Set.mem_univ,
      exists_true_left, support_pure, Set.mem_singleton_iff]
    exact ⟨0, 0, rfl⟩
  simpa using (h 0).2.2 _ hz

/-- The adversary meets every hypothesis of the Type 2 security theorem, which bounds its
advantage by four times the success of the named reduction. -/
theorem one_hash_one_sign_bound :
    AggregateSignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (Bool →ₒ ZMod 101))
        adversary ≤
      4 * Pr{let b ← CoCDH.isoExperiment 1
              (BLS.Aggregate.coCDHReduction LinearMap.id adversary 1 1 2)}[b = true] := by
  have hg : Function.Surjective (· • (1 : ZMod 101) : ZMod 101 → ZMod 101) :=
    fun a => ⟨a, by simp⟩
  have h := BLS.Aggregate.unforgeableAdvantage_le
    (LinearMap.id (R := ZMod 101) (M := ZMod 101)) adversary 1 1 2 adversary_romQueryBound
    (by simpa using hg) hg (by simp)
  norm_num at h
  exact h

/-- The adversary always forges: the pair `(pk, true)` was never signed, and its aggregate is the
sum of the two honest signatures. -/
theorem adversary_unforgeableAdvantage :
    AggregateSignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (Bool →ₒ ZMod 101))
      adversary = 1 := by
  unfold AggregateSignatureAlg.unforgeableAdvantage
  rw [ProbCompRuntime.rom_evalDist]
  change 𝒟[_] {b | b = true} = 1
  rw [evalDist_apply_setOf_simulateQ_romImpl_run'_eq_one_iff]
  intro f _
  rw [OracleComp.evalDist_apply_setOf_eq_one_iff_forall_mem_support]
  intro b hb
  simp only [AggregateSignatureAlg.unforgeableExperiment, BLS.Aggregate.scheme, smul_eq_mul,
    mul_one, bind_pure_comp, LinearMap.mul_apply_apply, ite_not, LinearMap.mul_apply', adversary,
    add_apply_inl, add_apply_inr, SignatureAlg.runWithSigningOracle_def,
    SignatureAlg.signingOracle, QueryImpl.passthrough_add, simulateQ_bind, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, QueryImpl.add_apply_inl,
    QueryImpl.liftTarget_apply, QueryImpl.id'_apply, id_map,
    simulateQ_map, QueryImpl.add_apply_inr, QueryImpl.withLogging_apply, map_bind,
    Functor.map_map, id_eq, WriterT.run_bind, WriterT.run_liftM, List.empty_eq, WriterT.run_map,
    WriterT.run_tell, map_pure, List.nil_append, bind_map_left, bind_assoc, List.any_cons,
    decide_true, ne_eq, Bool.false_eq_true, not_false_eq_true, QueryLog.wasQueried_cons_of_ne,
    QueryLog.wasQueried_nil, Bool.not_false, Bool.and_self, QueryLog.wasQueried_cons_self,
    Bool.not_true, Bool.and_false, List.any_nil, Bool.or_self, Bool.or_false, List.map_cons,
    List.map_nil, List.nodup_cons, List.mem_cons, Bool.true_eq_false, List.not_mem_nil, or_self,
    List.nodup_nil, and_self, ↓reduceIte, Bool.true_and, MonadAttach.support_bind,
    MonadAttach.mem_support, MonadAttach.support_map, Set.mem_iUnion, Set.mem_image,
    exists_prop] at hb
  obtain ⟨i, -, i₁, hi₁, i₂, hi₂, x, hx, rfl⟩ := hb
  have hq : ∀ msg, simulateQ (unifFwdAnswerImpl f) (liftM ((Bool →ₒ ZMod 101).query msg)) =
      (pure (f msg) : ProbComp (ZMod 101)) := fun msg => by
    change simulateQ (unifSpec.passthrough + f.liftTarget ProbComp)
      (liftM ((Bool →ₒ ZMod 101).query msg)) = _
    exact QueryImpl.simulateQ_add_liftM_query_right
      (unifSpec.passthrough : QueryImpl unifSpec ProbComp) (f.liftTarget ProbComp) msg
  rw [hq] at hi₂
  change MonadAttach.CanReturn (pure (f true) : ProbComp (ZMod 101)) i₁ at hi₁
  have hq2 : ∀ msg, simulateQ (unifFwdAnswerImpl f)
      (liftM (liftM ((Bool →ₒ ZMod 101).query msg) : OracleComp (Bool →ₒ ZMod 101) (ZMod 101))) =
      (pure (f msg) : ProbComp (ZMod 101)) := fun msg => hq msg
  simp only [BLS.Aggregate.pairingSum, liftM_bind, liftM_pure, simulateQ_bind, simulateQ_pure,
    hq2, pure_bind] at hx
  simp only [MonadAttach.canReturn_pure_iff] at hi₁ hi₂ hx
  subst hi₁ hi₂ hx
  simp
  ring

/-- The bound is not vacuous here: the named Type 2 reduction solves co-CDH with probability
at least `1 / 4`. -/
theorem one_le_four_mul_prEvent_coCDHReduction :
    1 ≤ 4 * Pr{let b ← CoCDH.isoExperiment 1
                    (BLS.Aggregate.coCDHReduction LinearMap.id adversary 1 1 2)}[b = true] := by
  simpa [adversary_unforgeableAdvantage] using one_hash_one_sign_bound

/-- A linear source map can meet first-source generation and nondegeneracy without
second-source cyclicity, yet fail the arbitrary-key identity needed to strip contributions.
Here `ψ` projects the first coordinate,
while the pairing uses the sum of both coordinates. -/
theorem source_map_compatibility_counterexample :
    let ψ : (ZMod 101 × ZMod 101) →ₗ[ZMod 101] ZMod 101 := LinearMap.fst _ _ _
    let e : ZMod 101 →ₗ[ZMod 101] (ZMod 101 × ZMod 101) →ₗ[ZMod 101] ZMod 101 :=
      (LinearMap.mul (ZMod 101) (ZMod 101)).compl₂
        (LinearMap.fst _ _ _ + LinearMap.snd _ _ _)
    let g₂ : ZMod 101 × ZMod 101 := (1, 0)
    Function.Bijective (· • ψ g₂ : ZMod 101 → ZMod 101) ∧
      e (ψ g₂) g₂ ≠ 0 ∧ e (ψ (0, 1)) g₂ ≠ e (ψ g₂) (0, 1) := by
  simp

/-- A valid two-message pairing equation need not yield the challenge solution after
stripping the chosen key with a merely linear source map. The honest secret and challenge
are one, the selected mask is zero, and the other hash's scalar is one. -/
theorem arbitrary_key_stripping_counterexample :
    let ψ : (ZMod 101 × ZMod 101) →ₗ[ZMod 101] ZMod 101 := LinearMap.fst _ _ _
    let e : ZMod 101 →ₗ[ZMod 101] (ZMod 101 × ZMod 101) →ₗ[ZMod 101] ZMod 101 :=
      (LinearMap.mul (ZMod 101) (ZMod 101)).compl₂
        (LinearMap.fst _ _ _ + LinearMap.snd _ _ _)
    let g₂ : ZMod 101 × ZMod 101 := (1, 0)
    e 2 g₂ = e 1 g₂ + e 1 (0, 1) ∧ (2 : ZMod 101) - ψ (0, 1) ≠ 1 := by
  norm_num
  decide

end BLSAggregateTest
