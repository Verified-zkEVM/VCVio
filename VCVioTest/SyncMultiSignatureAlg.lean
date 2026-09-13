/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module

public import VCVio.CryptoFoundations.SyncMultiSignatureAlg
public import VCVioTest.SyncSignatureAlg
public import VCVio.CryptoFoundations.SyncMultiSignatureAlg.Security

/-!
# Independent Definition 9 probes

The honest count-sensitive scheme accepts every finite participant count. Explicit failure and
missing mass both reject at one participant. A fair-key scheme accepts only true public keys:
its singleton key average is one half, but its false key violates the same per-tuple bound.
The configured order-sensitive scheme encodes the aligned pairs as its aggregate, so swapping
signatures alone is detectably different. Repeated keys and the empty tuple remain valid inputs.
These examples establish correctness observations, not Definition 10 security or compression.
-/

public section

namespace SyncMultiSignatureProbe

open ENNReal OracleComp SyncMultiSignatureAlg

/-- Independently sequencing pure computations preserves every coordinate. -/
theorem sequence_pure {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (k : ℕ) (f : Fin k → α) :
    Fin.mOfFn k (fun i => (pure (f i) : m α)) = pure f := by
  induction k with
  | zero =>
    have hf : f = Fin.elim0 := funext fun i => i.elim0
    simp [Fin.mOfFn, hf]
  | succ k ih =>
    simp only [Fin.mOfFn, ih, pure_bind]
    congr 1
    exact Fin.cons_self_tail f

/-- Successful coordinate outputs are aligned with exactly their original public keys. -/
theorem accepts_all_some {m : Type → Type} [Monad m] {M PK SK S A E : Type}
    (alg : SyncMultiSignatureAlg m M PK SK S A E) {k : ℕ}
    (pks : Fin k → PK) (ep : E) (msg : M) (sigs : Fin k → S) :
    alg.accepts pks ep msg (fun i => some (sigs i)) =
      alg.verify pks ep msg (alg.aggregate ep msg fun i => (pks i, sigs i)) := by
  unfold accepts
  rw [show (fun i => some (sigs i)) = (fun i => (pure (sigs i) : Option S)) from rfl]
  rw [sequence_pure]
  rfl

/-- A count-sensitive honest scheme at arbitrary epochs. -/
@[expose] def honest (E : Type) :
    SyncMultiSignatureAlg ProbComp Unit Unit Unit Unit ℕ E where
  keygen := pure ((), ())
  sign _ _ _ := pure (some ())
  aggregate {k} _ _ _ := k
  verify {k} _ _ _ agg := agg == k

/-- Every fixed tuple succeeds for the honest scheme, including zero and repeated participants. -/
theorem honest_success (E : Type) (k : ℕ) (keys : Fin k → Unit × Unit)
    (ep : E) (msg : Unit) :
    (honest E).successMass ProbCompRuntime.probComp keys ep msg = 1 := by
  simp [successMass, verificationDist, honest, SyncSignatureProbe.runtime_eval,
    sequence_pure, accepts_all_some]

/-- Honest correctness holds at every participant count and every epoch type. -/
theorem honest_complete_zero (E : Type) :
    (honest E).Complete ProbCompRuntime.probComp (fun _ => 0) := by
  intro k keys hkeys ep msg
  simp [honest_success]

/-- Singleton signing returns failure despite an always-accepting aggregate verifier. -/
@[expose] def alwaysFails : SyncMultiSignatureAlg ProbComp Unit Unit Unit Unit Unit Unit where
  keygen := pure ((), ())
  sign _ _ _ := pure none
  aggregate _ _ _ := ()
  verify _ _ _ _ := true

/-- Returned signing failure has no singleton aggregate success mass. -/
theorem returned_failure :
    alwaysFails.successMass ProbCompRuntime.probComp (fun _ : Fin 1 => ((), ())) () () = 0 := by
  simp [successMass, verificationDist, alwaysFails, SyncSignatureProbe.runtime_eval,
    Fin.mOfFn, accepts]

/-- Completely missing runtime output mass is not normalized into successful signatures. -/
theorem missing_mass {m : Type → Type} [Monad m] {M PK SK S A E : Type}
    (alg : SyncMultiSignatureAlg m M PK SK S A E) (runtime : ProbCompRuntime m)
    (ks : PK × SK) (ep : E) (msg : M)
    (h : runtime.evalSPMF (alg.sign ks.2 ep msg) = failure) :
    alg.successMass runtime (fun _ : Fin 1 => ks) ep msg = 0 := by
  simp [successMass, verificationDist, Fin.mOfFn, h]

/-- With no participants the failing signer is never invoked; the empty aggregate is accepted. -/
theorem empty_failure_signer :
    alwaysFails.successMass ProbCompRuntime.probComp (fun i : Fin 0 => i.elim0) () () = 1 := by
  simp [successMass, verificationDist, alwaysFails, Fin.mOfFn, accepts]

/-- A fair public key determines whether singleton aggregate verification accepts. -/
@[expose] def mixed : SyncMultiSignatureAlg ProbComp Unit Bool Unit Unit Unit Unit where
  keygen := (fun b => (b, ())) <$> ($ᵗ Bool)
  sign _ _ _ := pure (some ())
  aggregate _ _ _ := ()
  verify pks _ _ _ := (List.ofFn pks).all id

/-- Both fair public keys, including false, are producible. -/
theorem mixed_generated (b : Bool) : mixed.Generated ProbCompRuntime.probComp (b, ()) := by
  simp [Generated, mixed, SyncSignatureProbe.runtime_eval, probOutput_map_eq_tsum_ite]

/-- The singleton good key has full successful aggregate mass. -/
theorem mixed_good :
    mixed.successMass ProbCompRuntime.probComp (fun _ : Fin 1 => (true, ())) () () = 1 := by
  simp [successMass, verificationDist, mixed, SyncSignatureProbe.runtime_eval, Fin.mOfFn, accepts,
    List.ofFn_succ]

/-- The singleton bad key has zero successful aggregate mass. -/
theorem mixed_bad :
    mixed.successMass ProbCompRuntime.probComp (fun _ : Fin 1 => (false, ())) () () = 0 := by
  simp [successMass, verificationDist, mixed, SyncSignatureProbe.runtime_eval, Fin.mOfFn, accepts,
    List.ofFn_succ]

/-- Key-averaged singleton acceptance, observing both runtime steps explicitly. -/
@[expose] noncomputable def mixedAverage : ℝ≥0∞ :=
  (𝒟[ProbCompRuntime.probComp.evalSPMF mixed.keygen >>= fun ks =>
    mixed.accepts (fun _ : Fin 1 => ks.1) () () <$>
      Fin.mOfFn 1 (fun _ => ProbCompRuntime.probComp.evalSPMF (mixed.sign ks.2 () ()))]) {true}

/-- Averaging over the key generator hides half of the bad-key behavior. -/
theorem mixed_average : mixedAverage = 2⁻¹ := by
  simp [mixedAverage, mixed, SyncSignatureProbe.runtime_eval, Fin.mOfFn, accepts, List.ofFn_succ]

/-- An error allowance of one half at every count fails on the producible bad singleton. -/
theorem not_mixed_complete_half :
    ¬ mixed.Complete ProbCompRuntime.probComp (fun _ => 2⁻¹) := by
  intro h
  have hbad := h 1 (fun _ => (false, ())) (fun _ => mixed_generated false) () ()
  rw [mixed_bad] at hbad
  norm_num at hbad

/-- The singleton averaged bound holds while Definition 9's per-tuple bound fails. -/
theorem mixed_separates : (1 - (2⁻¹ : ℝ≥0∞) ≤ mixedAverage) ∧
    ¬ mixed.Complete ProbCompRuntime.probComp (fun _ => 2⁻¹) := by
  refine ⟨?_, not_mixed_complete_half⟩
  rw [mixed_average]
  norm_num

/-- Configuration is captured by signing and verification; aggregation preserves pair order. -/
@[expose] def ordered (E : Type) (cfg : Bool) :
    SyncMultiSignatureAlg ProbComp Unit Bool Bool Bool (List (Bool × Bool)) E where
  keygen := (fun b => (b, b)) <$> ($ᵗ Bool)
  sign sk _ _ := pure (some (cfg != sk))
  aggregate _ _ pairs := List.ofFn pairs
  verify pks _ _ agg := agg == List.ofFn (fun i => (pks i, cfg != pks i))

/-- Correctly aligned distinct keys verify for either constructor configuration. -/
theorem aligned_order (cfg : Bool) :
    (ordered Unit cfg).accepts ![false, true] () () ![some (cfg != false), some (cfg != true)] =
      true := by
  cases cfg <;> decide

/-- Swapping signatures while fixing the key order rejects. -/
theorem swapped_signatures (cfg : Bool) :
    (ordered Unit cfg).accepts ![false, true] () () ![some (cfg != true), some (cfg != false)] =
      false := by
  cases cfg <;> decide

/-- Repeated public keys are accepted when their signatures occupy the matching positions. -/
theorem repeated_keys (cfg : Bool) :
    (ordered Unit cfg).accepts ![true, true] () () ![some (cfg != true), some (cfg != true)] =
      true := by
  cases cfg <;> decide

/-- Empty aggregation is observed by the verifier at the same arbitrary epoch. -/
theorem ordered_empty (E : Type) (cfg : Bool) (ep : E) :
    (ordered E cfg).accepts (fun i : Fin 0 => i.elim0) ep ()
      (fun i : Fin 0 => i.elim0) = true := by
  simp [accepts, Fin.mOfFn, ordered, List.ofFn_zero]

/-- Returned-failure signing violates zero-error correctness at a producible singleton. -/
theorem not_alwaysFails_complete_zero :
    ¬ alwaysFails.Complete ProbCompRuntime.probComp (fun _ => 0) := by
  intro h
  have hkeys : alwaysFails.GeneratedTuple ProbCompRuntime.probComp
      (fun _ : Fin 1 => ((), ())) := by
    intro i
    simp [Generated, alwaysFails, SyncSignatureProbe.runtime_eval]
  have hbad := h 1 _ hkeys () ()
  simp [returned_failure] at hbad

/-- An empty tuple does not bypass an aggregate verifier that rejects it. -/
@[expose] def rejectsEmpty : SyncMultiSignatureAlg ProbComp Unit Unit Unit Unit ℕ Unit :=
  { honest Unit with verify := fun {k} _ _ _ _ => decide (0 < k) }

/-- Empty verification rejection has zero success mass despite making no signing calls. -/
theorem empty_rejection :
    rejectsEmpty.successMass ProbCompRuntime.probComp (fun i : Fin 0 => i.elim0) () () = 0 := by
  simp [successMass, verificationDist, rejectsEmpty, Fin.mOfFn, accepts]

/-- Producibility for the order-sensitive family requires matching public and secret bits. -/
theorem ordered_generated_iff (E : Type) (cfg : Bool) (ks : Bool × Bool) :
    (ordered E cfg).Generated ProbCompRuntime.probComp ks ↔ ks.1 = ks.2 := by
  rcases ks with ⟨pk, sk⟩
  cases pk <;> cases sk <;>
    simp [Generated, ordered, SyncSignatureProbe.runtime_eval, probOutput_map_eq_tsum_ite]

/-- Correctly generated tuples have full success mass for either fixed configuration. -/
theorem ordered_success (E : Type) (cfg : Bool) (k : ℕ) (keys : Fin k → Bool × Bool)
    (hkeys : ∀ i, (keys i).1 = (keys i).2) (ep : E) (msg : Unit) :
    (ordered E cfg).successMass ProbCompRuntime.probComp keys ep msg = 1 := by
  simp [successMass, verificationDist, ordered, SyncSignatureProbe.runtime_eval,
    sequence_pure, accepts_all_some, hkeys]

/-- Every configuration has zero error for every producible tuple and arbitrary epoch type. -/
theorem ordered_complete_zero (E : Type) :
    ∀ cfg, (ordered E cfg).Complete ProbCompRuntime.probComp (fun _ => 0) := by
  intro cfg k keys hkeys ep msg
  have heq : ∀ i, (keys i).1 = (keys i).2 :=
    fun i => (ordered_generated_iff E cfg (keys i)).mp (hkeys i)
  simp [ordered_success E cfg k keys heq]

/-- Repeated keys are a producible two-participant tuple. -/
theorem repeated_generated (cfg : Bool) :
    (ordered Unit cfg).GeneratedTuple ProbCompRuntime.probComp ![(true, true), (true, true)] := by
  intro i
  rw [ordered_generated_iff]
  fin_cases i <;> rfl

/-- Canonical surface observations satisfy the explicitly required pure-return factoring law. -/
theorem canonical_observation {M PK SK S A E : Type}
    (alg : SyncMultiSignatureAlg ProbComp M PK SK S A E) :
    alg.ObservesSigning ProbCompRuntime.probComp := by
  intro k keys ep msg
  exact ProbCompRuntime.probComp_evalSPMF_bind_pure _ _

/-- Canonical surface execution samples every signing invocation independently. -/
theorem canonical_independence {M PK SK S A E : Type}
    (alg : SyncMultiSignatureAlg ProbComp M PK SK S A E) :
    alg.IndependentSigning ProbCompRuntime.probComp := by
  intro k keys ep msg
  simp only [SyncSignatureProbe.runtime_eval]
  induction k with
  | zero => simp [Fin.mOfFn]
  | succ k ih => simp [Fin.mOfFn, ih]

end SyncMultiSignatureProbe

/-!
# Definition 10 distinguishing probes

Finite toy examples independently separate message freshness, challenger membership, tuple order,
multiplicity, returned failure and missing mass. The toy schemes are deliberately insecure.
-/


namespace SyncMultiSignatureSecurity.Probe

open OracleComp OracleSpec
open SyncSignatureSecurity (History emptyHistory signingSpec)

/-- Only key zero is generated; every aggregate is accepted. Signing `true` returns failure. -/
@[expose] def toy : SyncMultiSignatureAlg ProbComp Bool Nat Unit Bool Bool Bool where
  keygen := pure (0, ())
  sign _ _ msg := pure (if msg then none else some false)
  aggregate _ _ _ := false
  verify _ _ _ _ := true

/-- A successful first request at epoch `false`. -/
@[expose] def signed : History Bool Bool Bool :=
  fun ep => if ep then none else some (false, some false)

/-- A failed first request at epoch `false`. -/
@[expose] def failed : History Bool Bool Bool :=
  fun ep => if ep then none else some (true, none)

/-- A singleton candidate carrying the challenger key. -/
@[expose] def singleton (ep msg signature : Bool) : Forgery Nat Bool Bool Bool :=
  ⟨1, fun _ => 0, ep, msg, signature⟩

/-- Changing the aggregate on a previously requested message cannot satisfy freshness. -/
theorem same_message_changed_aggregate_loses :
    valid toy (0, singleton false false false, signed) = false ∧
    valid toy (0, singleton false false true, signed) = false := by
  decide

/-- A failed eligible request still excludes its message. -/
theorem failed_message_loses :
    valid toy (0, singleton false true true, failed) = false := by
  decide

/-- A different message at a used epoch remains fresh, after success or returned failure. -/
theorem changed_message_wins :
    valid toy (0, singleton false true false, signed) = true ∧
    valid toy (0, singleton false false false, failed) = true := by
  decide

/-- The same message at another epoch and any message at an unused epoch remain eligible. -/
theorem cross_epoch_and_unused_win :
    valid toy (0, singleton true false false, signed) = true ∧
    valid toy (0, singleton false true false, emptyHistory) = true := by
  decide

/-- An accepting verifier cannot rescue an empty tuple or omission of the challenger key. -/
theorem empty_and_omission_lose :
    valid toy (0, ⟨0, Fin.elim0, false, false, false⟩, emptyHistory) = false ∧
    valid toy (0, ⟨2, fun _ => 17, false, false, false⟩, emptyHistory) = false := by
  decide

/-- One challenger occurrence suffices among arbitrary keys, including repetitions. -/
theorem arbitrary_and_repeated_keys_win :
    valid toy (0, ⟨3, ![17, 0, 17], false, false, true⟩, emptyHistory) = true ∧
    valid toy (0, ⟨2, ![0, 0], false, false, true⟩, emptyHistory) = true := by
  decide

/-- A verifier sensitive to the exact ordered list, including repeated non-generated keys. -/
@[expose] def ordered : SyncMultiSignatureAlg ProbComp Bool Nat Unit Bool Bool Bool :=
  { toy with verify := fun pks _ _ _ => decide (List.ofFn pks = [17, 0, 17]) }

/-- Verification receives the original tuple: swapping or deleting entries changes acceptance. -/
theorem tuple_order_and_multiplicity :
    valid ordered (0, ⟨3, ![17, 0, 17], false, false, true⟩, emptyHistory) = true ∧
    valid ordered (0, ⟨3, ![0, 17, 17], false, false, true⟩, emptyHistory) = false ∧
    valid ordered (0, ⟨2, ![17, 0], false, false, true⟩, emptyHistory) = false := by
  decide

/-- The supplied aggregate need not equal the scheme's aggregation output. -/
theorem aggregate_supplied_directly :
    toy.aggregate false false (fun _ : Fin 1 => (0, false)) = false ∧
    valid toy (0, singleton false false true, emptyHistory) = true := by
  decide

/-- The first successful request records its successful answer. -/
theorem first_success :
    signingOracle toy () (false, false) emptyHistory = pure (some false, signed) := by
  change (pure (some false, Function.update emptyHistory false (some (false, some false))) :
    ProbComp _) = _
  congr 2
  funext ep
  cases ep <;> rfl

/-- The first failed request records the requested message. -/
theorem first_failure :
    signingOracle toy () (false, true) emptyHistory = pure (none, failed) := by
  change (pure (none, Function.update emptyHistory false (some (true, none))) : ProbComp _) = _
  congr 2
  funext ep
  cases ep <;> rfl

/-- A signer performs an observable ambient query on every invocation. -/
@[expose] def querying : SyncMultiSignatureAlg ProbComp Bool Nat Unit Bool Bool Bool :=
  { toy with sign := fun _ _ _ => some <$> ($ᵗ Bool) }

/-- Duplicate requests preserve both first successful and first failed records without signing. -/
theorem duplicates_preserve_without_signing :
    signingOracle querying () (false, true) signed = pure (none, signed) ∧
    signingOracle querying () (false, false) failed = pure (none, failed) := by
  constructor
  · exact signingOracle_used querying () signed false true false (some false) rfl
  · exact signingOracle_used querying () failed false false true none rfl

/-- Failure determines the branch; duplicate failure permits a subsequent successful request. -/
@[expose] def adaptive : Adversary unifSpec Nat Bool Bool Bool Bool where
  forge pk := do
    let first ← query (spec := unifSpec + signingSpec Bool Bool Bool) (Sum.inr (false, true))
    match first with
    | some sig => pure ⟨1, fun _ => pk, false, true, sig⟩
    | none =>
      let duplicate ← query (spec := unifSpec + signingSpec Bool Bool Bool)
        (Sum.inr (false, false))
      match duplicate with
      | some sig => pure ⟨1, fun _ => pk, false, true, sig⟩
      | none =>
        let last ← query (spec := unifSpec + signingSpec Bool Bool Bool)
          (Sum.inr (true, false))
        pure ⟨3, ![17, pk, 17], false, false, last.getD true⟩

/-- Final first-request history after the failed request and later successful request. -/
@[expose] def finalHistory : History Bool Bool Bool :=
  fun ep => if ep then some (false, some false) else some (true, none)

/-- The adaptive candidate has a fresh message and preserves the arbitrary ordered key tuple. -/
@[expose] def finalResult : ExperimentResult Nat Bool Bool Bool Bool :=
  (0, ⟨3, ![17, 0, 17], false, false, false⟩, finalHistory)

/-- The complete adaptive execution returns after failure, duplicate rejection and later success. -/
theorem adaptive_failure_duplicate_result :
    interaction toy adaptive = pure finalResult := by
  change (pure (0, (⟨3, ![17, 0, 17], false, false, false⟩ : Forgery Nat Bool Bool Bool),
    Function.update (Function.update emptyHistory false (some (true, none)))
      true (some (false, some false))) : ProbComp _) = _
  congr 4
  funext ep
  cases ep <;> rfl

/-- Returned signing failure can lead to unit winning mass under the canonical runtime. -/
theorem returned_failure_wins :
    advantage toy ProbCompRuntime.probComp adaptive = 1 := by
  simp only [advantage, unforgeableExp, outputMeasure, adaptive_failure_duplicate_result]
  change (evalDist (valid toy <$> (_root_.evalSPMF (pure finalResult : ProbComp _))))
    {true} = 1
  rw [evalSPMF_pure, map_pure]
  have hwin : valid toy finalResult = true := by decide
  rw [hwin]
  simp

/-- Missing interpreted execution mass gives zero advantage, unlike a returned signing failure. -/
theorem missing_execution_loses (runtime : ProbCompRuntime ProbComp)
    (h : runtime.evalSPMF (interaction toy adaptive) = failure) :
    advantage toy runtime adaptive = 0 :=
  outputMeasure_eq_zero_of_failure toy runtime adaptive (valid toy) h

/-- An explicit lossy observation runtime discards every execution result. -/
@[expose] noncomputable def missingRuntime : ProbCompRuntime ProbComp :=
  { ProbCompRuntime.probComp with toSPMFSemantics :=
      { ProbCompRuntime.probComp.toSPMFSemantics with observe := fun _ => failure } }

/-- Actual missing observation mass has zero advantage in this deliberately lossy runtime. -/
theorem missing_runtime_loses : advantage toy missingRuntime adaptive = 0 :=
  missing_execution_loses missingRuntime rfl


universe u

variable {ι : Type u} {spec : OracleSpec ι}
variable {M PK SK S A E : Type}

/-- The endpoint checks its winning predicate only after interpreting the shared interaction. -/
theorem unforgeableExp_post_runtime [DecidableEq E] [DecidableEq M] [DecidableEq PK]
    (alg : SyncMultiSignatureAlg (OracleComp spec) M PK SK S A E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S A) :
    unforgeableExp alg runtime adv =
      𝒟[valid alg <$> runtime.evalSPMF (interaction alg adv)] := rfl

end SyncMultiSignatureSecurity.Probe
