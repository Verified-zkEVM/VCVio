/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.CoverageRun

/-!
# Actual-key firing and its deterministic thinning proposition

The proposition names the per-fixed-tape target without asserting a proof.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.Security.Coverage

/-- A forger-tape position at the generated public key is in the fresh-draw hit set. -/
def FiredAtActualKey
    {vp : ValidatedParams} {core : CorePrimitives vp.params}
    (z : DeriveOutcome core × RoleState core) (index : Nat) : Prop :=
  ∃ (R : core.Y) (M : List Byte),
    z.2.2.1.cls (hmsgPoint core z.1.pk R M) = some TapeClass.forger ∧
    z.2.2.1.pos (hmsgPoint core z.1.pk R M) = some index ∧
    hmsgPoint core z.1.pk R M ∈ z.2.2.2

/-- The fully quantified deterministic thinning proposition at a fixed tape family. -/
noncomputable def nativeThin1Target
    {vp : ValidatedParams} (core : CorePrimitives vp.params)
    [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.Y]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf]
    [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]
    (e : core.SkSeed ≃ core.Y)
    (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed)
    (adv : UnforgeableAdversary
      (romScheme core e (fun pk => pure (kappa pk)) (pure pkSeed)))
    (L : (j : TapeClass) → List (tapeClassRange core j)) (_hL : L .other = [])
    (index : Nat) : Prop :=
  Pr{let z ← roleRun core adv pkSeed L}[
      index < z.2.2.1.cnt TapeClass.forger ∧ FiredAtActualKey z index] ≤
    (Nat.card core.Y : ℝ≥0∞)⁻¹ *
      Pr{let z ← roleRun core adv pkSeed L}[
        index < z.2.2.1.cnt TapeClass.forger]

end SLHDSA.Security.Coverage

#check @SLHDSA.Security.Coverage.nativeThin1Target
#print axioms SLHDSA.Security.Coverage.nativeThin1Target
