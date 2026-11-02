/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import NativeThin1

/-! # Reach-conditioned actual-key pair-thinning proposition -/

public section
open OracleComp OracleSpec SignatureAlg
open scoped ENNReal
namespace SLHDSA.Security.Coverage

/-- The deterministic actual-key pair-thinning proposition at a fixed tape family. -/
noncomputable def nativeThin2Target
    {vp : ValidatedParams} (core : CorePrimitives vp.params)
    [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.Y]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf]
    [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]
    (e : core.SkSeed ≃ core.Y)
    (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed)
    (adv : UnforgeableAdversary
      (romScheme core e (fun pk => pure (kappa pk)) (pure pkSeed)))
    (L : (j : TapeClass) → List (tapeClassRange core j)) (_hL : L .other = [])
    (first second : Nat) (_horder : first < second) : Prop :=
    Pr{let z ← roleRun core adv pkSeed L}[
        second < z.2.2.1.cnt TapeClass.forger ∧
          FiredAtActualKey z first ∧ FiredAtActualKey z second] ≤
      ((Nat.card core.Y : ℝ≥0∞)⁻¹) ^ 2 *
        Pr{let z ← roleRun core adv pkSeed L}[
          first < z.2.2.1.cnt TapeClass.forger]

end SLHDSA.Security.Coverage
#check @SLHDSA.Security.Coverage.nativeThin2Target
#print axioms SLHDSA.Security.Coverage.nativeThin2Target
