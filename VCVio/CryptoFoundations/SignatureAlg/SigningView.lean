/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.SignatureAlg

/-!
# Signing replies and candidate signatures

`SignatureAlg.SigningView` separates the response of the signing oracle from the signature
in a candidate forgery. A readback projects the successful request/signature pairs from the
raw reply log. The signing service retains every returned reply, including a rejected request
represented by an optional response. All algorithms execute over the same ambient oracle
specification; interpreting that specification is a separate outer operation.
-/

public section

open OracleSpec OracleComp

namespace SignatureAlg

universe v

/-- A signature interface with independent signing-reply and candidate-signature types. -/
structure SigningView (m : Type → Type v) [Monad m] (Request PK SK Sig Reply : Type) where
  /-- Generate the public and secret keys. -/
  keygen : m (PK × SK)
  /-- Return a signing response, which may encode a rejected request. -/
  sign : PK → SK → Request → m Reply
  /-- Check a candidate signature directly, without converting it to a signing response. -/
  verify : PK → Request → Sig → m Bool
  /-- Extract a returned signature when the response contains one. -/
  readback : Reply → Option Sig

namespace SigningView

variable {Request PK SK Sig Reply : Type}

/-- The request/signature pairs returned by the successful readbacks of a raw reply log. -/
@[expose] def returnedPairs (readback : Reply → Option Sig)
    (log : QueryLog (Request →ₒ Reply)) : List (Request × Sig) :=
  log.filterMap fun entry => (readback entry.2).map fun sig => (entry.1, sig)

/-- A forgery is fresh when no signing reply returned its exact request/signature pair. -/
@[expose] def Fresh (readback : Reply → Option Sig) (log : QueryLog (Request →ₒ Reply))
    (candidate : Request × Sig) : Prop :=
  candidate ∉ returnedPairs readback log

/-- Returned-pair membership needs no equality decision on the raw reply type. -/
theorem mem_returnedPairs_iff (readback : Reply → Option Sig)
    (log : QueryLog (Request →ₒ Reply)) (request : Request) (sig : Sig) :
    (request, sig) ∈ returnedPairs readback log ↔
      ∃ entry ∈ log, entry.1 = request ∧ readback entry.2 = some sig := by
  simp only [returnedPairs, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  aesop

/-- Readback preserves the chronological concatenation of raw reply logs. -/
@[simp] theorem returnedPairs_append (readback : Reply → Option Sig)
    (left right : QueryLog (Request →ₒ Reply)) :
    returnedPairs readback (left ++ right) =
      returnedPairs readback left ++ returnedPairs readback right := by
  simp [returnedPairs]

/-- There are no more returned signatures than raw responses. -/
theorem returnedPairs_length_le (readback : Reply → Option Sig)
    (log : QueryLog (Request →ₒ Reply)) :
    (returnedPairs readback log).length ≤ log.length :=
  List.length_filterMap_le _ _

/-- Optional replies retain exactly the successful-pair freshness predicate. -/
theorem optional_fresh_iff (log : QueryLog (Request →ₒ Option Sig))
    (request : Request) (sig : Sig) :
    Fresh id log (request, sig) ↔
      ¬∃ entry ∈ log, entry.1 = request ∧ entry.2 = some sig := by
  simp only [Fresh, mem_returnedPairs_iff, id_eq]

/-- Total responses have the same freshness predicate as the ordinary signature API. -/
theorem total_fresh_iff [DecidableEq Request] [DecidableEq Sig]
    (log : QueryLog (Request →ₒ Sig)) (request : Request) (sig : Sig) :
    Fresh some log (request, sig) ↔ signingLogContains log request sig = false := by
  have hmem : (∃ entry ∈ log, entry.1 = request ∧ entry.2 = sig) ↔
      ⟨request, sig⟩ ∈ log := by
    constructor
    · rintro ⟨entry, member, req, signed⟩
      cases entry
      cases req
      cases signed
      exact member
    · intro member
      exact ⟨⟨request, sig⟩, member, rfl, rfl⟩
  simpa only [Fresh, mem_returnedPairs_iff, Option.some.injEq,
    signingLogContains, decide_eq_false_iff_not] using not_congr hmem

/-- Regard every response of a total signature algorithm as a returned signature. -/
@[expose] def ofTotal {m : Type → Type v} [Monad m]
    (alg : SignatureAlg m Request PK SK Sig) : SigningView m Request PK SK Sig Sig where
  keygen := alg.keygen
  sign := alg.sign
  verify := alg.verify
  readback := some

/-- An experiment records the candidate, every raw signing response and verification result. -/
structure Outcome (Request Sig Reply : Type) where
  /-- The request and signature claimed by the adversary. -/
  forgery : Request × Sig
  /-- Every response returned by the signing service. -/
  rawLog : QueryLog (Request →ₒ Reply)
  /-- The final verifier's response. -/
  verified : Bool

/-- A verified candidate whose pair has not been returned by the signing service wins. -/
@[expose] def Wins (readback : Reply → Option Sig) (outcome : Outcome Request Sig Reply) : Prop :=
  outcome.verified = true ∧ Fresh readback outcome.rawLog outcome.forgery

section experiment

variable {ι : Type} {spec : OracleSpec ι}

/-- The signing service logs each response after its algorithm returns. -/
@[expose] def signingOracle (view : SigningView (OracleComp spec) Request PK SK Sig Reply)
    (pk : PK) (sk : SK) :
    QueryImpl (Request →ₒ Reply) (WriterT (QueryLog (Request →ₒ Reply)) (OracleComp spec)) :=
  QueryImpl.withLogging (view.sign pk sk)

/-- Run a client with ambient queries forwarded and raw signing replies logged. -/
@[expose] def runWithSigningOracle
    (view : SigningView (OracleComp spec) Request PK SK Sig Reply) (pk : PK) (sk : SK)
    {α : Type} (body : OracleComp (spec + (Request →ₒ Reply)) α) :
    OracleComp spec (α × QueryLog (Request →ₒ Reply)) :=
  (simulateQ (spec.passthrough + view.signingOracle pk sk) body).run

/-- A client that makes no query returns an empty raw reply log. -/
@[simp] theorem runWithSigningOracle_pure
    (view : SigningView (OracleComp spec) Request PK SK Sig Reply) (pk : PK) (sk : SK)
    {α : Type} (value : α) :
    view.runWithSigningOracle pk sk (pure value) = pure (value, []) := rfl

/-- Sequential clients concatenate their complete raw reply logs in execution order. -/
theorem runWithSigningOracle_bind
    (view : SigningView (OracleComp spec) Request PK SK Sig Reply) (pk : PK) (sk : SK)
    {α β : Type} (body : OracleComp (spec + (Request →ₒ Reply)) α)
    (next : α → OracleComp (spec + (Request →ₒ Reply)) β) :
    view.runWithSigningOracle pk sk (body >>= next) = (do
      let (a, left) ← view.runWithSigningOracle pk sk body
      let (b, right) ← view.runWithSigningOracle pk sk (next a)
      return (b, left ++ right)) := by
  simp [runWithSigningOracle, WriterT.run_bind]

/-- Mapping a client's output retains its complete raw reply log. -/
theorem runWithSigningOracle_map
    (view : SigningView (OracleComp spec) Request PK SK Sig Reply) (pk : PK) (sk : SK)
    {α β : Type} (f : α → β) (body : OracleComp (spec + (Request →ₒ Reply)) α) :
    view.runWithSigningOracle pk sk (f <$> body) =
      Prod.map f id <$> view.runWithSigningOracle pk sk body := by
  simp only [runWithSigningOracle, simulateQ_map, WriterT.run_map]
  rfl

/-- A signing request records the actual reply, including a value representing rejection. -/
theorem runWithSigningOracle_signingQuery
    (view : SigningView (OracleComp spec) Request PK SK Sig Reply) (pk : PK) (sk : SK)
    (request : Request) :
    view.runWithSigningOracle pk sk
      (liftM ((spec + (Request →ₒ Reply)).query (.inr request))) = (do
        let reply ← view.sign pk sk request
        return (reply, [⟨request, reply⟩])) := by
  simp [runWithSigningOracle, signingOracle, QueryImpl.withLogging_apply]

/-- A rejected request remains in the raw log and the client continues on its returned `none`. -/
theorem runWithSigningOracle_rejectedQuery_bind
    (view : SigningView (OracleComp spec) Request PK SK Sig (Option Sig)) (pk : PK) (sk : SK)
    (request : Request) (rejected : view.sign pk sk request = pure none)
    {α : Type} (next : Option Sig → OracleComp (spec + (Request →ₒ Option Sig)) α) :
    view.runWithSigningOracle pk sk
      (liftM ((spec + (Request →ₒ Option Sig)).query (.inr request)) >>= next) = (do
        let (a, log) ← view.runWithSigningOracle pk sk (next none)
        return (a, ⟨request, none⟩ :: log)) := by
  rw [runWithSigningOracle_bind, runWithSigningOracle_signingQuery, rejected]
  simp

/-- The complete free-oracle experiment, with no imposed budget or lifetime limit. -/
@[expose] def experiment (view : SigningView (OracleComp spec) Request PK SK Sig Reply)
    (adv : PK → OracleComp (spec + (Request →ₒ Reply)) (Request × Sig)) :
    OracleComp spec (Outcome Request Sig Reply) := do
  let (pk, sk) ← view.keygen
  let (forgery, rawLog) ← view.runWithSigningOracle pk sk (adv pk)
  let verified ← view.verify pk forgery.1 forgery.2
  return ⟨forgery, rawLog, verified⟩

open scoped Classical in
/-- Observe the strong-unforgeability bit of the full experiment. -/
@[expose] noncomputable def winningProgram
    (view : SigningView (OracleComp spec) Request PK SK Sig Reply)
    (adv : PK → OracleComp (spec + (Request →ₒ Reply)) (Request × Sig)) :
    OracleComp spec Bool :=
  (fun outcome => decide (Wins view.readback outcome)) <$> view.experiment adv

/-- A total signing service preserves the original response carrier and raw log exactly. -/
theorem ofTotal_runWithSigningOracle (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
    (pk : PK) (sk : SK) {α : Type} (body : OracleComp (spec + (Request →ₒ Sig)) α) :
    (ofTotal alg).runWithSigningOracle pk sk body = alg.runWithSigningOracle pk sk body := rfl

open scoped Classical in
/-- The total view's winning bit uses the exact returned-pair predicate of the signature API. -/
theorem ofTotal_decide_Wins (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
    (outcome : Outcome Request Sig Sig) :
    decide (Wins (ofTotal alg).readback outcome) =
      (!signingLogContains outcome.rawLog outcome.forgery.1 outcome.forgery.2 &&
        outcome.verified) := by
  rcases outcome with ⟨⟨request, sig⟩, log, verified⟩
  apply Bool.eq_iff_iff.mpr
  simp [Wins, ofTotal, total_fresh_iff, and_comm]

/-- The total view has exactly the original strong-unforgeability program for every adversary. -/
theorem ofTotal_winningProgram (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
    (adv : StrongUnforgeableAdversary alg) :
    (ofTotal alg).winningProgram adv.main = strongUnforgeableExperiment adv := by
  simp only [winningProgram, experiment, map_bind, map_pure, ofTotal_decide_Wins,
    ofTotal_runWithSigningOracle, strongUnforgeableExperiment]
  rfl

end experiment

end SigningView
end SignatureAlg
