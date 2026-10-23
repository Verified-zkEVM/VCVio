/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.BlockViews
public import HashSig.SLHDSA.SHAKE128s.Proof.ClassGrowth

/-!
# The shared oracle's run, at a general cache view

Two small facts about `KeygenUniform.rom` at a general `RecorderView.CacheView` state: a hit
returns the cached answer and leaves the carrier, and a miss draws a fresh uniform answer and
installs it. The carrier may carry whatever else it likes, such as a flag or a served set, and
stay invisible to every event about the result and the cache.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.CoverageCount

open Security DigestTape ClassGrowth

variable {σ : Type} [RecorderView.CacheView σ]

/-! ## The shared oracle's two branches -/

/-- The shared oracle's hit branch, at the type the world's query carries. -/
theorem rom_run_inr_some (input : Bytes) (cache : QueryCache HashSpec) (cached : HashOutput)
    (hcached : cache input = some cached) :
    (KeygenUniform.rom (Sum.inr input)).run cache =
      (pure (cached, cache) :
        ProbComp (OracleWorld.Range (Sum.inr input) × QueryCache HashSpec)) := by
  rw [DigestTape.rom_run_inr, QueryImpl.withCaching_run_some _ hcached]

/-- The shared oracle's miss branch, likewise. -/
theorem rom_run_inr_none (input : Bytes) (cache : QueryCache HashSpec)
    (hfresh : cache input = none) :
    (KeygenUniform.rom (Sum.inr input)).run cache =
      (((fun answer => (answer, cache.cacheQuery input answer)) <$>
        ($ᵗ HashOutput : ProbComp _)) :
          ProbComp (OracleWorld.Range (Sum.inr input) × QueryCache HashSpec)) := by
  rw [DigestTape.rom_run_inr, QueryImpl.withCaching_run_none _ hfresh]
  rfl

end SlhDsaSecurity.CoverageCount
