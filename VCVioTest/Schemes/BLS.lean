/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Security
public import Mathlib.Algebra.Field.ZMod

/-! # BLS over the field of order 101

Concrete consumers of the Boneh–Lynn–Shacham scheme, with multiplication as the pairing
and both generators equal to one. The adversary hashes `false`, signs `true`, and uses
the scalar visible in this toy public key to forge on `false`. Its budget of one hash and one
signing query is tight, it meets every hypothesis of the security theorem, and it always wins,
so the theorem bounds the named reduction's success below by `1 / 3`.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace BLSTest

/-- Primality certificate for the local test field. -/
local instance prime101 : Fact (Nat.Prime 101) := ⟨by decide⟩

/-- Sample directly as `Fin 101`, without constructing an enumeration at module load. -/
local instance sampleField : SampleableType (ZMod 101) :=
  inferInstanceAs (SampleableType (Fin 101))

local notation "toyScheme" =>
  BLS.scheme (M := Bool) (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1

/-- Hash `false`, sign `true`, and forge on `false` with the scalar the toy public key shows. -/
@[expose] def adversary : SignatureAlg.UnforgeableAdversary toyScheme where
  main pk := do
    let h : ZMod 101 ←
      ((unifSpec + (Bool →ₒ ZMod 101)) + (Bool →ₒ ZMod 101)).query (.inl (.inr false))
    let _ : ZMod 101 ←
      ((unifSpec + (Bool →ₒ ZMod 101)) + (Bool →ₒ ZMod 101)).query (.inr true)
    return (false, pk.2 * h)

/-- The fixture uses one direct hash query and one signing query on every public key. -/
theorem adversary_romQueryBound : adversary.RomQueryBound 1 1 := by
  intro pk
  constructor <;>
    simp [adversary, isQueryBoundP_query_bind_iff, SignatureAlg.IsHashQuery,
      SignatureAlg.IsSignQuery]

/-- The hash budget is tight: no public key admits a budget of zero direct hash queries. -/
theorem not_adversary_romQueryBound_zero_one : ¬ adversary.RomQueryBound 0 1 := fun h => by
  simpa [adversary, isQueryBoundP_query_bind_iff, SignatureAlg.IsHashQuery] using (h (0, 0)).1

/-- The signing budget is tight: no public key admits a budget of zero signing queries. -/
theorem not_adversary_romQueryBound_one_zero : ¬ adversary.RomQueryBound 1 0 := fun h => by
  simpa [adversary, isQueryBoundP_query_bind_iff, SignatureAlg.IsHashQuery,
    SignatureAlg.IsSignQuery] using (h (0, 0)).2

/-- The one-hash, one-sign adversary meets every hypothesis of the security theorem, which then
bounds its advantage by three times the success of the named co-CDH reduction. -/
theorem one_hash_one_sign_bound :
    SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (Bool →ₒ ZMod 101)) adversary ≤
      3 * Pr{let b ← CoCDH.experiment 1 1 (BLS.coCDHReduction adversary 1 1)}[b = true] := by
  have hg : Function.Surjective (· • (1 : ZMod 101) : ZMod 101 → ZMod 101) :=
    fun y => ⟨y, by simp⟩
  have h := BLS.unforgeableAdvantage_le adversary 1 1 adversary_romQueryBound hg (by simp)
  norm_num at h
  exact h

/-- The toy adversary always forges: it hashes `false`, reads the scalar from the public key, and
signs `false` itself, which it never asked the signing oracle for. -/
theorem adversary_unforgeableAdvantage :
    SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (Bool →ₒ ZMod 101)) adversary = 1 := by
  unfold SignatureAlg.unforgeableAdvantage
  rw [ProbCompRuntime.rom_evalDist]
  change 𝒟[_] {b | b = true} = 1
  rw [evalDist_apply_setOf_simulateQ_romImpl_run'_eq_one_iff]
  intro f _
  rw [OracleComp.evalDist_apply_setOf_eq_one_iff_forall_mem_support]
  intro b hb
  simp only [SignatureAlg.unforgeableExperiment, BLS.scheme, smul_eq_mul, mul_one, bind_pure_comp,
    LinearMap.mul_apply_apply, LinearMap.mul_apply', adversary, add_apply_inl, add_apply_inr,
    SignatureAlg.runWithSigningOracle_def, SignatureAlg.signingOracle, QueryImpl.passthrough_add,
    simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
    QueryImpl.id'_apply, id_map, simulateQ_map, QueryImpl.add_apply_inr,
    QueryImpl.withLogging_apply, map_bind, Functor.map_map, id_eq, WriterT.run_bind,
    WriterT.run_liftM, List.empty_eq, WriterT.run_map, WriterT.run_tell, map_pure, List.nil_append,
    bind_map_left, bind_assoc, ne_eq, Bool.true_eq_false, not_false_eq_true,
    QueryLog.wasQueried_cons_of_ne, QueryLog.wasQueried_nil, Bool.not_false, Bool.true_and,
    MonadAttach.support_bind, MonadAttach.mem_support, MonadAttach.support_map, Set.mem_iUnion,
    Set.mem_image, exists_prop] at hb
  obtain ⟨i, -, i₁, hi₁, -, -, x, hx, rfl⟩ := hb
  have hq : ∀ msg, simulateQ (unifFwdAnswerImpl f) (liftM ((Bool →ₒ ZMod 101).query msg)) =
      (pure (f msg) : ProbComp (ZMod 101)) := fun msg => by
    change simulateQ (unifSpec.passthrough + f.liftTarget ProbComp)
      (liftM ((Bool →ₒ ZMod 101).query msg)) = _
    exact QueryImpl.simulateQ_add_liftM_query_right
      (unifSpec.passthrough : QueryImpl unifSpec ProbComp) (f.liftTarget ProbComp) msg
  rw [hq] at hx
  change MonadAttach.CanReturn (pure (f false) : ProbComp (ZMod 101)) i₁ at hi₁
  simp only [MonadAttach.canReturn_pure_iff] at hi₁ hx
  subst hi₁ hx
  simp [mul_comm]

/-- The bound is not vacuous here: the named reduction solves co-CDH with probability at least
`1 / 3`. -/
theorem one_le_three_mul_prEvent_coCDHReduction :
    1 ≤ 3 * Pr{let b ← CoCDH.experiment 1 1 (BLS.coCDHReduction adversary 1 1)}[b = true] := by
  simpa [adversary_unforgeableAdvantage] using one_hash_one_sign_bound

end BLSTest
