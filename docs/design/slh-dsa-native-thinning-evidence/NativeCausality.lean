/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import NativeCausalRun
import all NativeCausalState
import all HashSig.SLHDSA.Security.CoverageRun

/-! # Future forger-tape overwrite causality in the native role experiment -/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.Security.Coverage

/-- Overwriting an unread future forger cell preserves the probability of reaching its counter. -/
theorem prEvent_roleRun_forgerCnt_set_ge
    {vp : ValidatedParams} (core : CorePrimitives vp.params)
    [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.Y]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf]
    [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]
    (e : core.SkSeed ≃ core.Y)
    (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed)
    (adv : UnforgeableAdversary
      (romScheme core e (fun pk => pure (kappa pk)) (pure pkSeed)))
    (L : (j : TapeClass) → List (tapeClassRange core j)) (hL : L .other = [])
    (index cell : Nat) (value : Bytes vp.params.m) (horder : index ≤ cell) :
    Pr{let z ← (roleRun core adv pkSeed
      (Function.update L TapeClass.forger ((L TapeClass.forger).set cell value)))}[
        index < z.2.2.1.cnt TapeClass.forger] =
      Pr{let z ← roleRun core adv pkSeed L}[
        index < z.2.2.1.cnt TapeClass.forger] :=
 by
  classical
  have _ : L .other = [] := hL
  simpa only [roleRun, AnswerTape.ClassPos.init, Nat.zero_add] using
    NativeCausality.prEvent_cnt_overwrite core TapeClass.forger
      (roleExperiment core adv pkSeed)
      (((∅, L), (AnswerTape.ClassPos.init, ∅)) : RoleState core)
      index cell value horder

end SLHDSA.Security.Coverage

#print axioms SLHDSA.Security.Coverage.prEvent_roleRun_forgerCnt_set_ge
