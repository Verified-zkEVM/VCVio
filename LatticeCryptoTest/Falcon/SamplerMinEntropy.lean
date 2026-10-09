/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import LatticeCrypto.Falcon.SamplerMinEntropy
public import LatticeCrypto.Falcon.Concrete.NTT
public import VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# Finite sampler witnesses and a modular point-mass counterexample

A fair bit gives a concrete finite leaf sampler with a nontrivial point-mass bound. The
resulting Falcon sampler satisfies the product bound without an exact Gaussian assumption.
A second fixture shows why a bound before modular reduction needs a fiber argument: two
distinct integers collapse to the same short residue, doubling its point mass.
-/

public section

open OracleComp OracleSpec MeasureTheory ProbabilityTheory Falcon
open scoped ENNReal

namespace LatticeCryptoTest.FalconSamplerMinEntropy

/-- A finite sampler with equal mass on zero and one. -/
def coinInt : ProbComp ℤ :=
  (fun bit : Bool => if bit then (1 : ℤ) else 0) <$> ($ᵗ Bool)

theorem coinInt_pointMass_le (v : ℤ) :
    Pr{let outcome ← coinInt}[outcome = v] ≤ (2 : ℝ≥0∞)⁻¹ := by
  rw [coinInt, prEvent_map, prEvent_eq_evalDist_of_discrete,
    SampleableType.evalDist_uniformSample, uniformOn_univ_apply_setOf]
  by_cases h0 : v = 0
  · subst v
    norm_num [Finset.filter_insert, Finset.filter_singleton]
  by_cases h1 : v = 1
  · subst v
    norm_num [Finset.filter_insert, Finset.filter_singleton]
  simp [Finset.filter_insert, Finset.filter_singleton, Ne.symm h0, Ne.symm h1]

/-- Only the leaf sampler is relevant to the product-bound theorem. -/
noncomputable def coinPrimitives : Primitives falcon512 where
  publicKeyBytes _ := default
  hashToPoint _ _ _ := 0
  samplerZ _ _ := coinInt
  fftTarget _ := 0
  fftInt _ := 0
  ifftRound _ := 0
  compress _ _ := none
  decompress _ _ := none
  nttOps := Falcon.Concrete.concreteNTTRingOps 9

/-- A concrete finite model satisfies the nontrivial product-bound hypotheses. -/
example (κ : ℕ) (target : FFTPair κ) (tree : FalconTree κ)
    (hleaves : tree.LeavesGE 0) (output : FFTPair κ) :
    Pr{let outcome ← coinPrimitives.ffSampling κ target tree}[outcome = output] ≤
      (2 : ℝ≥0∞)⁻¹ ^ (4 * 2 ^ κ) :=
  coinPrimitives.ffSampling_pointMass_le
    (fun _ _ _ v => coinInt_pointMass_le v) κ target tree hleaves output

/-- A fair draw from two distinct representatives of residue zero. -/
def modularRepresentatives : ProbComp ℤ :=
  (fun bit : Bool => if bit then (12289 : ℤ) else 0) <$> ($ᵗ Bool)

example : Pr{let x ← modularRepresentatives}[x = 0] = (2 : ℝ≥0∞)⁻¹ := by
  rw [modularRepresentatives, prEvent_map, prEvent_eq_evalDist_of_discrete,
    SampleableType.evalDist_uniformSample, uniformOn_univ_apply_setOf]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

/-- Modular reduction can increase point mass even when the output is the zero residue. -/
example : Pr{let x ← modularRepresentatives}[(x : ZMod 12289) = 0] = 1 := by
  rw [modularRepresentatives, prEvent_map, prEvent_eq_evalDist_of_discrete,
    SampleableType.evalDist_uniformSample]
  have hset : {bit : Bool | (((if bit then 12289 else 0) : ℤ) : ZMod 12289) = 0} =
      Set.univ := by
    ext bit
    cases bit <;> simp [show (12289 : ZMod 12289) = 0 from ZMod.natCast_self 12289]
  rw [hset]
  exact measure_univ

end LatticeCryptoTest.FalconSamplerMinEntropy
