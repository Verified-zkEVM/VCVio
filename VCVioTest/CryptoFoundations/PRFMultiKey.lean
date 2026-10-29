/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.PRF
public import VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# Independent instances of a PRF

`PRFScheme.multiKey` on a toy PRF on `Bool` with uniform keys: instance `i` evaluates under the
`i`-th key, the product keys are independent uniform keys, and the multi-instance advantage is
`prfAdvantage` of the product scheme.
-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace PRFMultiKeyTest

/-- A toy PRF on `Bool`: the key is added to the input. -/
@[expose]
def xorPRF : PRFScheme Bool Bool Bool where
  keygen := $ᵗ Bool
  eval k d := k ^^ d

lemma xorPRF_uniformKey : xorPRF.UniformKey := rfl

example (ks : Fin 3 → Bool) (i : Fin 3) (d : Bool) :
    (xorPRF.multiKey (Fin 3)).eval ks (i, d) = (ks i ^^ d) := by
  simp [xorPRF]

example : (xorPRF.multiKey Bool).eval id (true, false) = true := rfl

example : (xorPRF.multiKey Bool).eval id (false, true) = true := rfl

/-- The keys of two instances are independent uniform keys. -/
example : 𝒟[(xorPRF.multiKey (Fin 2)).keygen] = ProbabilityTheory.uniformOn Set.univ :=
  PRFScheme.evalDist_multiKey_keygen_of_uniformKey _ _ xorPRF_uniformKey

example : 𝒟[(xorPRF.multiKey (Fin 2)).keygen] = Measure.pi fun _ => 𝒟[$ᵗ Bool] :=
  PRFScheme.evalDist_multiKey_keygen _ _

/-- The two-instance PRF advantage of a distinguisher. -/
noncomputable example (adversary : PRFScheme.PRFAdversary (Fin 2 × Bool) Bool) : ℝ≥0∞ :=
  (xorPRF.multiKey (Fin 2)).prfAdvantage adversary

end PRFMultiKeyTest
