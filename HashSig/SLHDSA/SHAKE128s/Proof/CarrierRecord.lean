/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierSignRecord
public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierTail
public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierTailRecordings

/-!
# The key the carrier tail generates is the one the walk fixed

Key generation at the warm cache is a `pure`, so the key the carrier tail's run generates is
the walk's replayed key (`keys_eq_replay`) and its public key is `keyAt walk` (`keys_publicKey`),
with nothing to match against. -/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierRecord

open Security BracketedRun CarrierFiles CarrierRecordings CarrierSignRecord
  CarriedWitness CarrierTail RecordedQueries AnswerCarrier

set_option maxHeartbeats 1000000 in
theorem keys_eq_replay (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (hwalk : walk ∈ support WarmedGame.graphWalk)
    (keys : (SecretKey × PublicKey) × CountedState)
    (hkeys : keys ∈ support ((simulateQ (handlerAt rightKeep walk)
      (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)).run
        (startAt walk.2, (([], []), 0)))) :
    keys.1 = @Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery walk.2)
      walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 := by
  obtain ⟨outputs, hwarm⟩ := HonestGrowth.walk_cache_eq_warmCache hwalk
  have hrom := mem_support_rom_of_carrier (keyAt walk) (rightKeep walk) _
    (startAt walk.2, (([], []), 0)) keys hkeys
  rw [show (startAt walk.2, (([], []), (0 : Nat))).1.cache = walk.2 from rfl, hwarm,
    HonestProbes.run_keygenInternal_world_eq_pure, support_pure, Set.mem_singleton_iff] at hrom
  rw [hwarm]
  exact (Prod.ext_iff.mp hrom).1

theorem keys_publicKey (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (hwalk : walk ∈ support WarmedGame.graphWalk)
    (keys : (SecretKey × PublicKey) × CountedState)
    (hkeys : keys ∈ support ((simulateQ (handlerAt rightKeep walk)
      (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)).run
        (startAt walk.2, (([], []), 0)))) :
    keys.1.1.publicKey = keyAt walk := by
  rw [keys_eq_replay rightKeep walk hwalk keys hkeys]
  exact LateProvenance.keygen_publicKey walk.2 walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2

end SlhDsaSecurity.CarrierRecord
