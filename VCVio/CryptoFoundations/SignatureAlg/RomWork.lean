/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.SignatureAlg.RomQueryCount

/-!
# Whole-experiment random-oracle work

Security budgets charge the adversary's own hash and signing queries. Honest algorithm
certificates are separate hypotheses: their bounds must count every oracle-backed derivation,
including secret providers and message randomizers. The transport sums key generation,
adversarial traffic, all signing executions, and final verification.
-/

public section

open OracleComp OracleSpec

namespace SignatureAlg

variable {ι : Type} {hs : OracleSpec ι} {M PK SK S : Type}

/-- Hash traffic of an algorithm over private uniform samples and a hash oracle. -/
@[expose] def IsAmbientHashQuery : (unifSpec + hs).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred (IsAmbientHashQuery (hs := hs)) := by
  rintro (_ | _) <;> simp only [IsAmbientHashQuery] <;> infer_instance

/-- Honest whole-ROM-work certificates, including secret derivation and message-PRF traffic. -/
structure RomWorkBounds (alg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S)
    (keygen sign verify : ℕ) : Prop where
  /-- Key generation charges all its hash-oracle calls. -/
  keygen_bound : IsQueryBoundP alg.keygen (IsAmbientHashQuery (hs := hs)) keygen
  /-- Signing charges hash calls and oracle-backed secret/randomizer derivations. -/
  sign_bound : ∀ pk sk msg,
    IsQueryBoundP (alg.sign pk sk msg) (IsAmbientHashQuery (hs := hs)) sign
  /-- Verification charges every hash-oracle call on every typed candidate. -/
  verify_bound : ∀ pk msg sig,
    IsQueryBoundP (alg.verify pk msg sig) (IsAmbientHashQuery (hs := hs)) verify

/-- Running the signing oracle adds its certified honest work once for each signing request. -/
theorem isQueryBoundP_runWithSigningOracle
    (alg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S)
    (key : PK) (sk : SK) {α : Type} (oa : OracleComp ((unifSpec + hs) + (M →ₒ S)) α)
    {qh qs sign : ℕ} (hh : IsQueryBoundP oa (IsHashQuery (hs := hs) (M := M) (S := S)) qh)
    (hsign : IsQueryBoundP oa (IsSignQuery (hs := hs) (M := M) (S := S)) qs)
    (hsignAlg : ∀ msg,
      IsQueryBoundP (alg.sign key sk msg) (IsAmbientHashQuery (hs := hs)) sign) :
    IsQueryBoundP (alg.runWithSigningOracle key sk oa) (IsAmbientHashQuery (hs := hs))
      (qh + qs * sign) := by
  induction oa using OracleComp.inductionOn generalizing qh qs with
  | pure a => simp [runWithSigningOracle]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hh hsign
    simp only [runWithSigningOracle, QueryImpl.passthrough_add, signingOracle] at ih
    simp only [runWithSigningOracle, simulateQ_bind, simulateQ_spec_query,
      WriterT.run_bind']
    rcases t with (n | t) | msg
    · simp only [IsHashQuery, IsSignQuery, not_false_eq_true, true_or, ite_false] at hh hsign
      simp only [QueryImpl.passthrough_add, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, QueryImpl.id'_apply, WriterT.run_monadLift',
        bind_map_left]
      refine (isQueryBoundP_bind (n := 0) (m := qh + qs * sign) ?_ ?_).mono (by omega)
      · simp [IsAmbientHashQuery]
      · intro u _
        simpa only [isQueryBoundP_map_iff, signingOracle] using ih u (hh.2 u) (hsign.2 u)
    · simp only [IsHashQuery, IsSignQuery, not_true_eq_false, false_or,
        not_false_eq_true, true_or, ite_true, ite_false] at hh hsign
      simp only [QueryImpl.passthrough_add, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, QueryImpl.id'_apply, WriterT.run_monadLift',
        bind_map_left]
      refine (isQueryBoundP_bind (n := 1) (m := (qh - 1) + qs * sign) ?_ ?_).mono (by omega)
      · simp [IsAmbientHashQuery]
      · intro u _
        simpa only [isQueryBoundP_map_iff, signingOracle] using ih u (hh.2 u) (hsign.2 u)
    · simp only [IsHashQuery, IsSignQuery, not_true_eq_false, false_or,
        not_false_eq_true, true_or, ite_true, ite_false] at hh hsign
      simp only [QueryImpl.passthrough_add, QueryImpl.add_apply_inr, signingOracle,
        QueryImpl.run_withLogging_apply, bind_assoc, pure_bind]
      refine (isQueryBoundP_bind (m := qh + (qs - 1) * sign) (hsignAlg msg) ?_).mono ?_
      · intro u _
        simpa only [isQueryBoundP_map_iff, signingOracle] using ih u (hh.2 u) (hsign.2 u)
      · have hq : (qs - 1) * sign + sign = qs * sign := by
          have hqs : (qs - 1).succ = qs := by omega
          rw [← Nat.succ_mul, hqs]
        omega

/-- The complete strong-forgery experiment costs `K + qh + qs * S + V` hash queries.
Cache hits count, and the honest caps are for the actual oracle-backed algorithms. -/
theorem isQueryBoundP_strongUnforgeableExperiment
    (alg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S)
    (adv : StrongUnforgeableAdversary alg) {qh qs keygen sign verify : ℕ}
    (hadv : adv.RomQueryBound qh qs) (honest : RomWorkBounds alg keygen sign verify) :
    IsQueryBoundP (strongUnforgeableExperiment adv) (IsAmbientHashQuery (hs := hs))
      (keygen + (qh + qs * sign) + verify) := by
  unfold strongUnforgeableExperiment
  refine (isQueryBoundP_bind (m := qh + qs * sign + verify)
    honest.keygen_bound ?_).mono (by omega)
  intro keys _
  apply isQueryBoundP_bind
    (isQueryBoundP_runWithSigningOracle alg keys.1 keys.2 (adv.main keys.1)
      (hadv keys.1).1 (hadv keys.1).2 (honest.sign_bound keys.1 keys.2))
  intro result _
  simpa using honest.verify_bound keys.1 result.1.1 result.1.2

end SignatureAlg
