/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module

public import VCVio.CryptoFoundations.SyncMultiSignatureAlg.Security
public import VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# Definition 10 distinguishing probes

Finite toy examples independently separate message freshness, challenger membership, tuple order,
multiplicity, returned failure and missing mass. The toy schemes are deliberately insecure.
-/

public section

namespace SyncMultiSignatureUnforgeability.Probe

open OracleComp OracleSpec
open SyncSignatureUnforgeability (History emptyHistory signingSpec)

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
  rw [map_pure]
  have hwin : valid toy finalResult = true := by decide
  rw [hwin]
  simp

/-- Missing interpreted execution mass gives zero advantage, unlike a returned signing failure. -/
theorem missing_execution_loses (runtime : ProbCompRuntime ProbComp)
    (h : runtime.evalDist (valid toy <$> interaction toy adaptive) = 0) :
    advantage toy runtime adaptive = 0 :=
  outputMeasure_eq_zero_of_failure toy runtime adaptive (valid toy) h

/-- An explicit lossy observation runtime discards every execution result. -/
@[expose] noncomputable def missingRuntime : ProbCompRuntime ProbComp :=
  { ProbCompRuntime.probComp with
    toSemanticsVia :=
      { ProbCompRuntime.probComp.toSemanticsVia with
        observe := fun _ => 0
        observe_apply_univ_le_one := by simp }
    evalDist_map_eq := by simp [SemanticsVia.evalDist] }

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
      runtime.evalDist (valid alg <$> interaction alg adv) := rfl

end SyncMultiSignatureUnforgeability.Probe
