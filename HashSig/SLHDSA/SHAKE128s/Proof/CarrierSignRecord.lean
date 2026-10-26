/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierRecordings
public import HashSig.SLHDSA.SHAKE128s.Proof.SignerRightRecord
public import HashSig.SLHDSA.SHAKE128s.Proof.LateProvenance

/-!
# What a signing sub-run can file as a target, at the carrier

`SignerRightRecord` says this at the shared oracle's recorder. Here it is at the handler the
obligations are moving to, and it is assembly rather than argument: the cut is generic in the
handler (`run_signInternal_at`), the randomiser's answer is in the cache after its own query
(`Files.hashCached`), and every entry the rest files comes with the carrier it was filed at
(`run_right_suffix`), which extends the one that query left.

So every such carrier holds the randomiser's answer, with no ordering established and no step
named — the same escape as at the shared oracle, for the same reason: the lemma quantifies over
the states the rest reached instead of picking one.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.CarrierSignRecord

variable {α : Type}

open Security BracketedRun CarrierFiles CarrierRecordings SignerRightRecord CountedHandler
  CarriedWitness RecordedQueries

variable (pk : PublicKey)

/-- **A carrier run projects onto the shared oracle's**, by the equality the handler was given. -/
theorem mem_support_rom_of_carrier (rightKeep : Bytes → HandlerCarrier.State → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (state : CountedState)
    (result : α × CountedState)
    (hresult : result ∈ support ((simulateQ (countedCarrierRecorder pk rightKeep)
      computation).run state)) :
    (result.1, result.2.1.cache) ∈
      support ((simulateQ KeygenUniform.rom computation).run state.1.cache) := by
  have hforget := forgetsAlong_countedCarrierRecorder pk rightKeep computation state
  rw [show ((simulateQ KeygenUniform.rom computation).run state.1.cache) =
    (simulateQ KeygenUniform.rom computation).run
      ((fun state : CountedState =>
        RecorderView.CacheView.cacheOf (state.1, state.2.1).1) state) from rfl,
    ← hforget, support_map]
  exact ⟨result, hresult, rfl⟩

/-! ## The two outer phases

Each asks its question of the object that can answer it, as at the shared oracle — key
generation's is about an input's shape and the verifier's is about who asked, and both are the
shared oracle's to answer. The projection is **stronger** here than `SplitPrefix.mem_support_rom`
was: `ServingForget.ForgetsAlong` is an equality of computations, so the shared oracle's run is
not merely reachable from the carrier's but equal to its image. -/

end SLHDSA.SHAKE128s.CarrierSignRecord
