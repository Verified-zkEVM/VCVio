/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.CryptoFoundations.SymmEncAlg.Defs
public import VCVio.EvalDist.Monad.Measure
public import VCVio.EvalDist.EvalDistEq
public import ToMathlib.Probability.UniformOn
public import ToMathlib.MeasureTheory.Measure.Option

/-!
# Symmetric Encryption Schemes

This file gives the correctness and perfect-secrecy predicates for `SymmEncAlg m M K C`, stated
with the output measures `𝒟[…]` of the ambient monad.

The struct follows the same pattern as `AsymmEncAlg`, `KEMScheme`, `MacAlg`, etc.: it is
parameterized by an ambient monad `m` and uses plain `Type` parameters. Asymptotic security
statements are expressed externally by quantifying over a family
`(sp : ℕ) → SymmEncAlg m (M sp) (K sp) (C sp)`.

Perfect secrecy has two forms. `ciphertextRowsEqualAt` is the channel form: every message induces
the same ciphertext measure. `perfectSecrecyAt` is the independence form: for every lossless
message sampler, the joint message/ciphertext measure is the product of its marginals. Equal rows
imply independence (`perfectSecrecyAt_of_ciphertextRowsEqualAt`), and Shannon's theorem
(`ciphertextRowsEqualAt_of_uniformKey_of_bijective`) derives equal, uniform rows from a uniform key
and deterministic encryption that is bijective in the key.
-/

@[expose] public section

universe u

open MeasureTheory ProbabilityTheory

namespace SymmEncAlg

variable {m : Type → Type u} [Monad m] [EvalDistSemantics m] {M K C : Type}

/-- An encryption scheme is complete if decryption recovers every message with
probability `1`: each round trip denotes the Dirac measure at the input message. Messages carry
the discrete measurable structure, so the round trip is determined on every event. -/
def Complete (encAlg : SymmEncAlg m M K C) : Prop :=
  letI : MeasurableSpace M := ⊤
  ∀ msg : M, 𝒟[encAlg.completenessExperiment msg] = Measure.dirac (some msg)

/-- Channel form of perfect secrecy: every message induces ciphertexts with the same
distribution. -/
def ciphertextRowsEqualAt [LawfulMonad m] [LawfulEvalDistSemantics m]
    (encAlg : SymmEncAlg m M K C) : Prop :=
  ∀ msg₀ msg₁ : M,
    encAlg.perfectSecrecyCipherGivenMsgExperiment msg₀ =ᵈ
      encAlg.perfectSecrecyCipherGivenMsgExperiment msg₁

/-- Standard perfect secrecy expressed as independence: for every lossless message sampler, the
joint message/ciphertext measure is the product of the message and ciphertext marginals.
Messages and ciphertexts carry the discrete measurable structure. -/
def perfectSecrecyAt (encAlg : SymmEncAlg m M K C) : Prop :=
  letI : MeasurableSpace M := ⊤
  let : MeasurableSpace C := ⊤
  ∀ mgen : m M, IsProbabilityMeasure 𝒟[mgen] →
    𝒟[encAlg.perfectSecrecyExperiment mgen] =
      𝒟[mgen].prod 𝒟[encAlg.perfectSecrecyCipherExperiment mgen]

variable [LawfulEvalDistSemantics m]

section rows

variable [LawfulMonad m] [MeasurableSpace M] [DiscreteMeasurableSpace M] [MeasurableSpace C]

/-- When every row is the same ciphertext measure, the ciphertext marginal of a lossless message
sampler is that row. -/
theorem evalDist_perfectSecrecyCipherExperiment_of_rows (encAlg : SymmEncAlg m M K C)
    (mgen : m M) [IsProbabilityMeasure 𝒟[mgen]] (row : Measure C)
    (hrow : ∀ msg, 𝒟[encAlg.perfectSecrecyCipherGivenMsgExperiment msg] = row) :
    𝒟[encAlg.perfectSecrecyCipherExperiment mgen] = row := by
  rw [encAlg.perfectSecrecyCipherExperiment_eq_bind mgen, evalDist_bind_of_discrete]
  simp only [hrow, Measure.bind_const, measure_univ, one_smul]

end rows

/-- Equal ciphertext rows imply perfect secrecy in the independence form. -/
theorem perfectSecrecyAt_of_ciphertextRowsEqualAt [LawfulMonad m] [Nonempty M]
    (encAlg : SymmEncAlg m M K C) (hrows : encAlg.ciphertextRowsEqualAt) :
    encAlg.perfectSecrecyAt := by
  let : MeasurableSpace M := ⊤
  let : MeasurableSpace C := ⊤
  intro mgen hmgen
  let row := 𝒟[encAlg.perfectSecrecyCipherGivenMsgExperiment (Classical.arbitrary M)]
  have hrow : ∀ msg, 𝒟[encAlg.perfectSecrecyCipherGivenMsgExperiment msg] = row :=
    fun msg ↦ (hrows msg _).evalDist_eq
  rw [evalDist_perfectSecrecyCipherExperiment_of_rows encAlg mgen row hrow,
    encAlg.perfectSecrecyExperiment_eq_bind mgen, evalDist_bind_of_discrete, Measure.prod_def]
  refine Measure.bind_congr_right (Filter.Eventually.of_forall fun msg ↦ ?_)
  dsimp only
  rw [evalDist_map _ measurable_prodMk_left, hrow]

/-- **Shannon's theorem.** If the key is uniform and encryption is deterministic and bijective in
the key for each message, then every ciphertext row is uniform. -/
theorem evalDist_perfectSecrecyCipherGivenMsgExperiment_of_uniformKey_of_bijective
    [MeasurableSpace K] [DiscreteMeasurableSpace K] [MeasurableSingletonClass K]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    [Finite K] [Finite C] [Nonempty K] [Nonempty C]
    (encAlg : SymmEncAlg m M K C) (enc : K → M → C)
    (hkey : 𝒟[encAlg.keygen] = uniformOn Set.univ)
    (henc : ∀ k msg, 𝒟[encAlg.encrypt k msg] = Measure.dirac (enc k msg))
    (hbij : ∀ msg, Function.Bijective fun k ↦ enc k msg) (msg : M) :
    𝒟[encAlg.perfectSecrecyCipherGivenMsgExperiment msg] = uniformOn Set.univ := by
  rw [perfectSecrecyCipherGivenMsgExperiment, evalDist_bind_of_discrete, hkey]
  simp only [henc]
  rw [Measure.bind_dirac_eq_map _ Measurable.of_discrete]
  exact map_uniformOn_univ_of_bijective Measurable.of_discrete (hbij msg)

/-- **Shannon's theorem**, channel form: a uniform key and deterministic encryption that is
bijective in the key give equal ciphertext rows. -/
theorem ciphertextRowsEqualAt_of_uniformKey_of_bijective [LawfulMonad m]
    [MeasurableSpace K] [DiscreteMeasurableSpace K] [MeasurableSingletonClass K]
    [hC : MeasurableSpace C] [DiscreteMeasurableSpace C]
    [Finite K] [Finite C] [Nonempty K] [Nonempty C]
    (encAlg : SymmEncAlg m M K C) (enc : K → M → C)
    (hkey : 𝒟[encAlg.keygen] = uniformOn Set.univ)
    (henc : ∀ k msg, 𝒟[encAlg.encrypt k msg] = Measure.dirac (enc k msg))
    (hbij : ∀ msg, Function.Bijective fun k ↦ enc k msg) :
    encAlg.ciphertextRowsEqualAt := by
  intro msg₀ msg₁
  refine EvalDistEq.of_evalDist_eq ?_
  rw [evalDist_perfectSecrecyCipherGivenMsgExperiment_of_uniformKey_of_bijective encAlg enc
      hkey henc hbij msg₀,
    evalDist_perfectSecrecyCipherGivenMsgExperiment_of_uniformKey_of_bijective encAlg enc
      hkey henc hbij msg₁]

end SymmEncAlg
