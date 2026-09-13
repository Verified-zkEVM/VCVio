/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module

public import VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.CryptoFoundations.SyncSignatureAlg.Security

/-!
# Independent correctness probes

A one-epoch unit-message scheme suffices to distinguish the quantifiers of Definition 7.
The mixed scheme draws one fair bit: the true key always verifies and the false key never does.
Thus averaging accepts with probability one half, but the false key violates correctness at
error one half. All observations use the canonical `ProbComp` runtime.

A Boolean configuration is captured by all three algorithms of a separate family. Its correctness
holds for every configuration and every epoch type, without epoch equality or finiteness
assumptions.
-/

public section

namespace SyncSignatureProbe

open ENNReal OracleComp SyncSignatureAlg

/-- One-epoch honest signing always returns the accepted unit signature. -/
@[expose] def honest : SyncSignatureAlg ProbComp Unit Unit Unit Unit (Fin 1) where
  keygen := pure ((), ())
  sign _ _ _ := pure (some ())
  verify _ _ _ _ := true

/-- One-epoch signing always returns an explicit failure. -/
@[expose] def alwaysFails : SyncSignatureAlg ProbComp Unit Unit Unit Unit (Fin 1) where
  keygen := pure ((), ())
  sign _ _ _ := pure none
  verify _ _ _ _ := true

/-- A fair bit selects either an always-accepted or always-rejected public key. -/
@[expose] def mixed : SyncSignatureAlg ProbComp Unit Bool Unit Unit (Fin 1) where
  keygen := (fun b => (b, ())) <$> ($ᵗ Bool)
  sign _ _ _ := pure (some ())
  verify pk _ _ _ := pk

/-- Canonical runtime evaluation agrees with the existing `evalSPMF` interpretation. -/
theorem runtime_eval {α : Type} (p : ProbComp α) :
    ProbCompRuntime.probComp.evalSPMF p = evalSPMF p := rfl

/-- The honest scheme's concrete key has probability one. -/
theorem honest_key_probability :
    Pr[= ((), ()) | ProbCompRuntime.probComp.evalSPMF honest.keygen] = 1 := by
  simp [runtime_eval, honest]

/-- Every epoch and message under the honest key has acceptance mass one. -/
theorem honest_success (ep : Fin 1) (msg : Unit) :
    honest.successMass ProbCompRuntime.probComp ((), ()) ep msg = 1 := by
  simp [successMass, verificationDist, runtime_eval, honest, accepts]

/-- Honest signing has zero correctness error. -/
theorem honest_complete_zero : honest.Complete ProbCompRuntime.probComp 0 := by
  intro ks hks ep msg
  simpa using le_of_eq (honest_success ep msg).symm

/-- Explicit failure has zero acceptance mass even with an always-true verifier. -/
theorem alwaysFails_success (ep : Fin 1) (msg : Unit) :
    alwaysFails.successMass ProbCompRuntime.probComp ((), ()) ep msg = 0 := by
  simp [successMass, verificationDist, runtime_eval, alwaysFails, accepts]

/-- A returned-failure signer cannot satisfy zero-error correctness. -/
theorem not_alwaysFails_complete_zero : ¬ alwaysFails.Complete ProbCompRuntime.probComp 0 := by
  intro h
  have hkey : alwaysFails.Generated ProbCompRuntime.probComp ((), ()) := by
    simp [Generated, runtime_eval, alwaysFails]
  have hbad := h ((), ()) hkey 0 ()
  simp [alwaysFails_success] at hbad

/-- Both mixed-scheme keys have probability exactly one half. -/
theorem mixed_key_probability (b : Bool) :
    Pr[= (b, ()) | ProbCompRuntime.probComp.evalSPMF mixed.keygen] = 2⁻¹ := by
  simp [runtime_eval, mixed, probOutput_map_eq_tsum_ite]

/-- Both mixed-scheme keys are producible, including the bad key. -/
theorem mixed_generated (b : Bool) : mixed.Generated ProbCompRuntime.probComp (b, ()) := by
  rw [Generated, mixed_key_probability]
  norm_num

/-- The good key accepts with probability one. -/
theorem mixed_good_success (ep : Fin 1) (msg : Unit) :
    mixed.successMass ProbCompRuntime.probComp (true, ()) ep msg = 1 := by
  simp [successMass, verificationDist, runtime_eval, mixed, accepts]

/-- The bad key accepts with probability zero. -/
theorem mixed_bad_success (ep : Fin 1) (msg : Unit) :
    mixed.successMass ProbCompRuntime.probComp (false, ()) ep msg = 0 := by
  simp [successMass, verificationDist, runtime_eval, mixed, accepts]

/-- Averaging fixed-key verification observations over the generated key distribution. -/
@[expose] noncomputable def mixedAverage (ep : Fin 1) (msg : Unit) : ℝ≥0∞ :=
  (𝒟[ProbCompRuntime.probComp.evalSPMF mixed.keygen >>= fun ks =>
    mixed.accepts ks.1 ep msg <$>
      ProbCompRuntime.probComp.evalSPMF (mixed.sign ks.2 ep msg)]) {true}

/-- Averaged acceptance of the mixed scheme is exactly one half. -/
theorem mixed_average_probability (ep : Fin 1) (msg : Unit) : mixedAverage ep msg = 2⁻¹ := by
  simp [mixedAverage, runtime_eval, mixed, accepts]

/-- The canonical surface keygen-sign-verify execution also accepts with probability one half. -/
theorem mixed_runtime_average_probability (ep : Fin 1) (msg : Unit) :
    Pr[= true | ProbCompRuntime.probComp.evalSPMF do
      let ks ← mixed.keygen
      let out ← mixed.sign ks.2 ep msg
      pure (mixed.accepts ks.1 ep msg out)] = (2⁻¹ : ℝ≥0∞) := by
  simp [runtime_eval, mixed, accepts]

/-- The average bound at error one half holds at every epoch and message. -/
theorem mixed_average_half : ∀ ep msg, 1 - (2⁻¹ : ℝ≥0∞) ≤ mixedAverage ep msg := by
  intro ep msg
  rw [mixed_average_probability]
  norm_num

/-- The per-key correctness bound at error one half fails at the producible bad key. -/
theorem not_mixed_complete_half : ¬ mixed.Complete ProbCompRuntime.probComp (2⁻¹) := by
  intro h
  have hbad := h (false, ()) (mixed_generated false) 0 ()
  rw [mixed_bad_success] at hbad
  norm_num at hbad

/-- Average correctness at error one half does not imply per-key correctness. -/
theorem mixed_separates :
    (∀ ep msg, 1 - (2⁻¹ : ℝ≥0∞) ≤ mixedAverage ep msg) ∧
      ¬ mixed.Complete ProbCompRuntime.probComp (2⁻¹) :=
  ⟨mixed_average_half, not_mixed_complete_half⟩

/-- A configuration captured by key generation, signing and verification at arbitrary epochs. -/
@[expose] def configured (E : Type) (cfg : Bool) :
    SyncSignatureAlg ProbComp Unit Bool Bool Bool E where
  keygen := pure (cfg, cfg)
  sign sk _ _ := pure (some (cfg && sk))
  verify pk _ _ sig := (pk == cfg) && (sig == (cfg && pk))

/-- The configured family produces exactly the key pair determined by its configuration. -/
theorem configured_generated_iff (E : Type) (cfg : Bool) (ks : Bool × Bool) :
    (configured E cfg).Generated ProbCompRuntime.probComp ks ↔ ks = (cfg, cfg) := by
  by_cases h : ks = (cfg, cfg) <;> simp [Generated, configured, runtime_eval, h]

/-- Every configuration has zero correctness error, without any structure on its epoch type. -/
theorem configured_complete_zero (E : Type) :
    ∀ cfg, (configured E cfg).Complete ProbCompRuntime.probComp 0 := by
  intro cfg ks hks ep msg
  have hkey : ks = (cfg, cfg) := (configured_generated_iff E cfg ks).mp hks
  subst ks
  simp [successMass, verificationDist, runtime_eval, configured, accepts]

end SyncSignatureProbe

/-!
# Synchronized-signature security distinguishing probes

Two Boolean epochs and messages suffice to distinguish exact pair replay, alternative valid
signatures, cross-epoch freshness and failed eligible requests. The deliberately insecure toy
verifier accepts both signatures, although its signer returns only one signature.
-/


namespace SyncSignatureSecurity.Probe

open OracleComp OracleSpec

/-- A deterministic signer returns `false` except on the message `true`, which returns failure. -/
@[expose] def toy : SyncSignatureAlg ProbComp Bool Unit Unit Bool Bool where
  keygen := pure ((), ())
  sign _ _ msg := pure (if msg then none else some false)
  verify _ _ _ _ := true

/-- One successful request at epoch `false` and no request at epoch `true`. -/
@[expose] def signed : History Bool Bool Bool :=
  fun ep => if ep then none else some (false, some false)

/-- One failed eligible request at epoch `false`. -/
@[expose] def failed : History Bool Bool Bool :=
  fun ep => if ep then none else some (true, none)

/-- Exact replay loses both notions. -/
theorem replay_loses :
    strongValid toy ((), (false, false, false), signed) = false ∧
    valid toy ((), (false, false, false), signed) = false := by
  decide

/-- A different valid signature on the same epoch and message satisfies only strong validity. -/
theorem alternative_signature_valid_only_strong :
    strongValid toy ((), (false, false, true), signed) = true ∧
    valid toy ((), (false, false, true), signed) = false := by
  decide

/-- Requesting a message at another epoch does not spoil freshness at an unused epoch. -/
theorem cross_epoch_freshness :
    strongValid toy ((), (true, false, false), signed) = true ∧
    valid toy ((), (true, false, false), signed) = true := by
  decide

/-- Failure records the message: a later valid forgery for it wins only strong security. -/
theorem failed_message_valid_only_strong :
    strongValid toy ((), (false, true, true), failed) = true ∧
    valid toy ((), (false, true, true), failed) = false := by
  decide

/-- Both signatures verify despite the signer's deterministic successful answer. -/
theorem deterministic_does_not_imply_unique_valid :
    toy.sign () false false = pure (some false) ∧
    toy.verify () false false false = true ∧ toy.verify () false false true = true ∧
    (false : Bool) ≠ true := by
  simp [toy]

/-- A failed oracle answer is followed by a request at another epoch. -/
@[expose] def continueAfterFailure : OracleComp unifSpec
    (Option Bool × Option Bool × History Bool Bool Bool) := do
  let (first, history) ← signingOracle toy () (false, true) emptyHistory
  let (second, history) ← signingOracle toy () (true, false) history
  pure (first, second, history)

/-- The failed request consumes its epoch and successful interaction continues at the other one. -/
theorem failure_consumes_and_continues :
    continueAfterFailure = pure (none, some false,
      fun ep => if ep then some (false, some false) else some (true, none)) := by
  change (pure (none, some false,
    Function.update (Function.update emptyHistory false (some (true, none)))
      true (some (false, some false))) : ProbComp _) = _
  congr 3
  funext ep
  cases ep <;> rfl

/-- A repeated request after a failed request returns failure without overwriting the message. -/
theorem duplicate_failed_preserves :
    signingOracle toy () (false, false) failed = pure (none, failed) := by
  exact signingOracle_used toy () failed false false true none rfl

/-- A repeated request after success returns failure without overwriting the returned pair. -/
theorem duplicate_signed_preserves :
    signingOracle toy () (false, true) signed = pure (none, signed) := by
  exact signingOracle_used toy () signed false true false (some false) rfl

/-- The second query's epoch and message depend on the first optional response. -/
@[expose] def adaptive : Adversary unifSpec Unit Bool Bool Bool where
  forge _ := do
    let answer ← query (spec := unifSpec + signingSpec Bool Bool Bool)
      (Sum.inr (false, true))
    match answer with
    | none =>
      let second ← query (spec := unifSpec + signingSpec Bool Bool Bool)
        (Sum.inr (true, false))
      pure (true, false, second.getD true)
    | some sig => pure (false, true, sig)

/-- The adaptive interaction continues after failure and returns the later signed forgery. -/
theorem adaptive_failure_result :
    interaction toy adaptive = pure ((), (true, false, false),
      fun ep => if ep then some (false, some false) else some (true, none)) := by
  change (pure ((), (true, false, false),
    Function.update (Function.update emptyHistory false (some (true, none)))
      true (some (false, some false))) : ProbComp _) = _
  congr 4
  funext ep
  cases ep <;> rfl


universe u

variable {ι : Type u} {spec : OracleSpec ι}
variable {M PK SK S E : Type}

/-- The endpoint checks its winning predicate only after interpreting the shared interaction. -/
theorem unforgeableExp_post_runtime [DecidableEq E] [DecidableEq M]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S) :
    unforgeableExp alg runtime adv =
      𝒟[valid alg <$> runtime.evalSPMF (interaction alg adv)] := rfl

/-- The endpoint checks its winning predicate only after interpreting the shared interaction. -/
theorem strongUnforgeableExp_post_runtime [DecidableEq E] [DecidableEq M] [DecidableEq S]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S) :
    strongUnforgeableExp alg runtime adv =
      𝒟[strongValid alg <$> runtime.evalSPMF (interaction alg adv)] := rfl

end SyncSignatureSecurity.Probe
