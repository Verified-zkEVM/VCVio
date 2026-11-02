/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.SignatureAlg

/-!
# Returned-pair freshness from signing replies

A raw signing transcript retains every reply. A readback identifies the signatures returned
by replies, while candidate forgeries always contain signatures rather than optional replies.
-/

public section

open OracleSpec
namespace ReplyLogProbe

variable {Request Sig Reply : Type}

/-- The request and signature pairs returned by successful replies. -/
@[expose] def returnedPairs (readback : Reply → Option Sig)
    (log : QueryLog (Request →ₒ Reply)) : List (Request × Sig) :=
  log.filterMap fun entry => (readback entry.2).map fun sig => (entry.1, sig)

/-- A candidate pair is fresh when no reply returned that exact request and signature. -/
@[expose] def Fresh (readback : Reply → Option Sig) (log : QueryLog (Request →ₒ Reply))
    (candidate : Request × Sig) : Prop := candidate ∉ returnedPairs readback log

/-- Pair membership depends on readback, without requiring equality on raw replies. -/
theorem mem_returnedPairs_iff (readback : Reply → Option Sig)
    (log : QueryLog (Request →ₒ Reply)) (request : Request) (sig : Sig) :
    (request, sig) ∈ returnedPairs readback log ↔
      ∃ entry ∈ log, entry.1 = request ∧ readback entry.2 = some sig := by
  simp only [returnedPairs, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  aesop

/-- Optional replies retain precisely the ordinary successful-pair freshness predicate. -/
theorem optional_fresh_iff (log : QueryLog (Request →ₒ Option Sig))
    (request : Request) (sig : Sig) :
    Fresh id log (request, sig) ↔
      ¬∃ entry ∈ log, entry.1 = request ∧ entry.2 = some sig := by
  simp only [Fresh, mem_returnedPairs_iff, id_eq]

/-- Total signing replies preserve the existing signature experiment's exact log predicate. -/
theorem total_fresh_iff [DecidableEq Request] [DecidableEq Sig]
    (log : QueryLog (Request →ₒ Sig)) (request : Request) (sig : Sig) :
    Fresh some log (request, sig) ↔
      SignatureAlg.signingLogContains log request sig = false := by
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
    SignatureAlg.signingLogContains, decide_eq_false_iff_not] using not_congr hmem

/-- A rejected response followed by two successful responses on the same request. -/
@[expose] def fixture : QueryLog (Nat →ₒ Option Nat) := [⟨7, none⟩, ⟨7, some 11⟩, ⟨7, some 12⟩]

theorem fixture_raw_length : fixture.length = 3 := rfl

theorem fixture_returned_length : (returnedPairs id fixture).length = 2 := rfl

theorem fixture_replay_not_fresh : ¬Fresh id fixture (7, 11) := by simp [Fresh, returnedPairs, fixture]

theorem fixture_different_signature_fresh : Fresh id fixture (7, 13) := by simp [Fresh, returnedPairs, fixture]

#print axioms mem_returnedPairs_iff
#print axioms optional_fresh_iff
#print axioms total_fresh_iff
#print axioms fixture_replay_not_fresh
#print axioms fixture_different_signature_fresh
end ReplyLogProbe
