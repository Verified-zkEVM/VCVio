/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.ForsGraph
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Ordinary actual-byte consumers of the FORS traversal

The actual SHAKE-128s and SHAKE-192f components retain full observations under arbitrary outer
state and noncommutative additive cost. A separate arithmetic-valid instance with a two-byte
digest and hundred-byte nodes exercises canonical zero-padding without a prefix-fit premise.
-/

public section

universe u

open OracleComp OracleSpec SLHDSA SLHDSA.Graph SLHDSA.Security

namespace SLHDSA.Refactor.ForsGraphRecovery

local notation "vp128" => FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams
local notation "vp192" => FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams

/-- Arithmetic validity does not require a full digest to contain a complete node value. -/
@[expose] def shortParams : Params :=
  { n := 100, h := 1, d := 1, hp := 1, a := 1, k := 1, lgw := 1 }

/-- This actual canonical instance has two-byte digests and hundred-byte node values. -/
@[expose] def shortVp : ValidatedParams := ⟨shortParams, by decide⟩

/-- The actual byte-program theorem applies even though the prefix-fit inequality is false. -/
theorem short_digest_dimensions : shortVp.params.m = 2 ∧ shortVp.params.n = 100 := by decide

/-- Canonical prefix conversion retains the supplied bytes and zero-pads the final node byte. -/
theorem short_answer_padding :
    (prefixBytes 100 (#v[23, 42] : Bytes 2))[0] = 23 ∧
      (prefixBytes 100 (#v[23, 42] : Bytes 2))[1] = 42 ∧
      (prefixBytes 100 (#v[23, 42] : Bytes 2))[99] = 0 := by decide

/-- The shake128s actual byte component consumes the same all-parameter graph theorem. -/
theorem shake128s_program (pk sk : Bytes (vp128).params.n) (key : ForsKey (vp128).params)
    (md : List Byte) (cells : Node (vp128).params → Bytes (vp128).params.n)
    (seed : cells .secretSeed = sk) :
    simulateQ (encImpl (vp128))
      (forsSignWithSecretM (shakeCore (vp128))
        (oracleSecret (shakeCore (vp128)) (Equiv.refl _) pk sk) md pk key.address :
          OracleComp (unifSpec + hashSpec (shakeCore (vp128)))
            (ForsSigCore (vp128).params (shakeCore (vp128)))) =
      Fors.reconstruct (shakeCore (vp128)) key md <$>
        simulateQ (QueryImpl.ofLift (shakeSpec (vp128))
          (OracleComp (unifSpec + shakeSpec (vp128))))
          (RandomOracleTraversal.evaluate (GraphInput.input (vp128) pk)
            (fun node table answer => updateCell node table (prefixBytes (vp128).params.n answer))
            (ForsSchedule.signing key md) cells) :=
  forsSignWithSecretM_eq_graph (vp128) pk sk key md cells seed

/-- Every actual shake128s final cache/state and ordered additive cost is retained. -/
theorem shake128s_observation (pk sk : Bytes (vp128).params.n) (key : ForsKey (vp128).params)
    (md : List Byte) (cells : Node (vp128).params → Bytes (vp128).params.n)
    (seed : cells .secretSeed = sk)
    (m : Type → Type u) [Monad m] (Cache C : Type) [AddMonoid C]
    (handler : QueryImpl (unifSpec + shakeSpec (vp128)) (StateT Cache m))
    (cost : (unifSpec + shakeSpec (vp128)).Domain → C) (cache : Cache) :
    ((simulateQ (handler.withAddCost cost) (simulateQ (encImpl (vp128))
      (forsSignWithSecretM (shakeCore (vp128))
        (oracleSecret (shakeCore (vp128)) (Equiv.refl _) pk sk) md pk key.address :
          OracleComp (unifSpec + hashSpec (shakeCore (vp128)))
            (ForsSigCore (vp128).params (shakeCore (vp128)))))).runAdd).run cache =
      ((simulateQ (handler.withAddCost cost) (Fors.reconstruct (shakeCore (vp128)) key md <$>
        simulateQ (QueryImpl.ofLift (shakeSpec (vp128))
          (OracleComp (unifSpec + shakeSpec (vp128))))
          (RandomOracleTraversal.evaluate (GraphInput.input (vp128) pk)
            (fun node table answer => updateCell node table (prefixBytes (vp128).params.n answer))
            (ForsSchedule.signing key md) cells))).runAdd).run cache :=
  congrArg (fun program => ((simulateQ (handler.withAddCost cost) program).runAdd).run cache)
    (shake128s_program pk sk key md cells seed)

/-- The shake192f actual byte component consumes the same all-parameter graph theorem. -/
theorem shake192f_program (pk sk : Bytes (vp192).params.n) (key : ForsKey (vp192).params)
    (md : List Byte) (cells : Node (vp192).params → Bytes (vp192).params.n)
    (seed : cells .secretSeed = sk) :
    simulateQ (encImpl (vp192))
      (forsSignWithSecretM (shakeCore (vp192))
        (oracleSecret (shakeCore (vp192)) (Equiv.refl _) pk sk) md pk key.address :
          OracleComp (unifSpec + hashSpec (shakeCore (vp192)))
            (ForsSigCore (vp192).params (shakeCore (vp192)))) =
      Fors.reconstruct (shakeCore (vp192)) key md <$>
        simulateQ (QueryImpl.ofLift (shakeSpec (vp192))
          (OracleComp (unifSpec + shakeSpec (vp192))))
          (RandomOracleTraversal.evaluate (GraphInput.input (vp192) pk)
            (fun node table answer => updateCell node table (prefixBytes (vp192).params.n answer))
            (ForsSchedule.signing key md) cells) :=
  forsSignWithSecretM_eq_graph (vp192) pk sk key md cells seed

/-- Every actual shake192f final cache/state and ordered additive cost is retained. -/
theorem shake192f_observation (pk sk : Bytes (vp192).params.n) (key : ForsKey (vp192).params)
    (md : List Byte) (cells : Node (vp192).params → Bytes (vp192).params.n)
    (seed : cells .secretSeed = sk)
    (m : Type → Type u) [Monad m] (Cache C : Type) [AddMonoid C]
    (handler : QueryImpl (unifSpec + shakeSpec (vp192)) (StateT Cache m))
    (cost : (unifSpec + shakeSpec (vp192)).Domain → C) (cache : Cache) :
    ((simulateQ (handler.withAddCost cost) (simulateQ (encImpl (vp192))
      (forsSignWithSecretM (shakeCore (vp192))
        (oracleSecret (shakeCore (vp192)) (Equiv.refl _) pk sk) md pk key.address :
          OracleComp (unifSpec + hashSpec (shakeCore (vp192)))
            (ForsSigCore (vp192).params (shakeCore (vp192)))))).runAdd).run cache =
      ((simulateQ (handler.withAddCost cost) (Fors.reconstruct (shakeCore (vp192)) key md <$>
        simulateQ (QueryImpl.ofLift (shakeSpec (vp192))
          (OracleComp (unifSpec + shakeSpec (vp192))))
          (RandomOracleTraversal.evaluate (GraphInput.input (vp192) pk)
            (fun node table answer => updateCell node table (prefixBytes (vp192).params.n answer))
            (ForsSchedule.signing key md) cells))).runAdd).run cache :=
  congrArg (fun program => ((simulateQ (handler.withAddCost cost) program).runAdd).run cache)
    (shake192f_program pk sk key md cells seed)

/-- The short_digest actual byte component consumes the same all-parameter graph theorem. -/
theorem short_digest_program (pk sk : Bytes shortVp.params.n) (key : ForsKey shortVp.params)
    (md : List Byte) (cells : Node shortVp.params → Bytes shortVp.params.n)
    (seed : cells .secretSeed = sk) :
    simulateQ (encImpl shortVp)
      (forsSignWithSecretM (shakeCore shortVp)
        (oracleSecret (shakeCore shortVp) (Equiv.refl _) pk sk) md pk key.address :
          OracleComp (unifSpec + hashSpec (shakeCore shortVp))
            (ForsSigCore shortVp.params (shakeCore shortVp))) =
      Fors.reconstruct (shakeCore shortVp) key md <$>
        simulateQ (QueryImpl.ofLift (shakeSpec shortVp)
          (OracleComp (unifSpec + shakeSpec shortVp)))
          (RandomOracleTraversal.evaluate (GraphInput.input shortVp pk)
            (fun node table answer => updateCell node table (prefixBytes shortVp.params.n answer))
            (ForsSchedule.signing key md) cells) :=
  forsSignWithSecretM_eq_graph shortVp pk sk key md cells seed

end SLHDSA.Refactor.ForsGraphRecovery
