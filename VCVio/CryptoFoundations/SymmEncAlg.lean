/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.CryptoFoundations.SymmEncAlg.Defs
public import VCVio.EvalDist.Monad.Measure
public import VCVio.EvalDist.EvalDistEq
public import VCVio.EvalDist.ProbabilityBounds
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.Constructions.SampleableType.Measure
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
imply independence (`perfectSecrecyAt_of_ciphertextRowsEqualAt`). Independence gives back equal
rows once some lossless sampler draws any two given messages with positive probability
(`ciphertextRowsEqualAt_of_perfectSecrecyAt`); a uniform choice between two messages is such a
sampler in `ProbComp`, where the two forms are therefore equivalent
(`perfectSecrecyAt_iff_ciphertextRowsEqualAt`).

Shannon's theorem derives equal, uniform ciphertext rows from a uniform key and deterministic
encryption. `ciphertextRowsEqualAt_of_uniformKey_of_bijective` takes encryption bijective in the
key; `ciphertextRowsEqualAt_of_uniformKey_of_uniqueKey` takes a unique key carrying each message
to each ciphertext, with the hypotheses as point masses, and
`ciphertextRowsEqualAt_of_uniformKey_of_uniqueKey_support` states them as supports for oracle
computations under uniform oracle semantics.
-/

@[expose] public section

universe u

open MeasureTheory ProbabilityTheory
open scoped ENNReal

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

/-! ## Independence and equal rows -/

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

/-- The joint experiment gives a rectangle over one message the mass of that message times the
mass of the ciphertext event in that message's row. -/
theorem evalDist_perfectSecrecyExperiment_apply_singleton_prod (encAlg : SymmEncAlg m M K C)
    (mgen : m M) (msg : M) {s : Set C} (hs : MeasurableSet s) :
    𝒟[encAlg.perfectSecrecyExperiment mgen] ({msg} ×ˢ s) =
      𝒟[mgen] {msg} * 𝒟[encAlg.perfectSecrecyCipherGivenMsgExperiment msg] s := by
  classical
  have hrect : MeasurableSet ({msg} ×ˢ s) := (measurableSet_singleton msg).prod hs
  have hfiber : ∀ msg' : M,
      𝒟[(msg', ·) <$> encAlg.perfectSecrecyCipherGivenMsgExperiment msg'] ({msg} ×ˢ s) =
        ({msg} : Set M).indicator
          (fun _ => 𝒟[encAlg.perfectSecrecyCipherGivenMsgExperiment msg] s) msg' := by
    intro msg'
    rw [evalDist_map_apply _ measurable_prodMk_left hrect, Set.mk_preimage_prod_right_eq_if,
      Set.indicator_apply]
    split_ifs with hmsg
    · rw [Set.mem_singleton_iff] at hmsg
      rw [hmsg]
    · exact measure_empty
  rw [encAlg.perfectSecrecyExperiment_eq_bind mgen, evalDist_bind_of_discrete,
    Measure.bind_apply hrect Measurable.of_discrete.aemeasurable]
  simp_rw [hfiber]
  rw [lintegral_indicator_const (measurableSet_singleton msg), mul_comm]

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

/-- Perfect secrecy in the independence form implies equal ciphertext rows whenever some lossless
message sampler draws each of two given messages with positive probability: over such a message,
the joint law and the product law agree on every rectangle, and the message's mass cancels. A
generic monad need not supply such a sampler; with `m := Id` every message sampler is constant,
so identity encryption is independent of each of them although its rows differ. -/
theorem ciphertextRowsEqualAt_of_perfectSecrecyAt [LawfulMonad m] (encAlg : SymmEncAlg m M K C)
    (hsec : encAlg.perfectSecrecyAt)
    (hprior : ∀ msg₀ msg₁ : M, ∃ mgen : m M, Pr{let _ ← mgen}[True] = 1 ∧
      0 < Pr{let x ← mgen}[x = msg₀] ∧ 0 < Pr{let x ← mgen}[x = msg₁]) :
    encAlg.ciphertextRowsEqualAt := by
  let : MeasurableSpace M := ⊤
  let : MeasurableSpace C := ⊤
  intro msg₀ msg₁
  obtain ⟨mgen, hmass, hpos₀, hpos₁⟩ := hprior msg₀ msg₁
  have hprob : IsProbabilityMeasure 𝒟[mgen] :=
    ⟨(prEvent_true_eq_evalDist_apply_univ mgen).symm.trans hmass⟩
  have hrow : ∀ msg, 0 < Pr{let x ← mgen}[x = msg] →
      𝒟[encAlg.perfectSecrecyCipherGivenMsgExperiment msg] =
        𝒟[encAlg.perfectSecrecyCipherExperiment mgen] := by
    intro msg hpos
    rw [prEvent_eq_evalDist_singleton] at hpos
    ext s hs
    have hrect := congrArg (fun μ : Measure (M × C) => μ ({msg} ×ˢ s)) (hsec mgen hprob)
    rw [Measure.prod_prod,
      evalDist_perfectSecrecyExperiment_apply_singleton_prod encAlg mgen msg hs] at hrect
    exact (ENNReal.mul_right_inj hpos.ne' (measure_ne_top _ _)).1 hrect
  exact EvalDistEq.of_evalDist_eq ((hrow msg₀ hpos₀).trans (hrow msg₁ hpos₁).symm)

/-- In `ProbComp`, a uniform choice between two messages is a lossless sampler drawing each of
them with positive probability, so perfect secrecy in the independence form implies equal
ciphertext rows. -/
theorem ciphertextRowsEqualAt_of_perfectSecrecyAt_probComp (encAlg : SymmEncAlg ProbComp M K C)
    (hsec : encAlg.perfectSecrecyAt) : encAlg.ciphertextRowsEqualAt :=
  ciphertextRowsEqualAt_of_perfectSecrecyAt encAlg hsec fun msg₀ msg₁ =>
    ⟨(fun b : Bool => if b then msg₁ else msg₀) <$> ($ᵗ Bool), OracleComp.prEvent_true_eq_one _,
      by
        rw [prEvent_map]
        exact (SampleableType.prEvent_uniformSample_pos_iff _).2 ⟨false, by simp⟩,
      by
        rw [prEvent_map]
        exact (SampleableType.prEvent_uniformSample_pos_iff _).2 ⟨true, by simp⟩⟩

/-- In `ProbComp`, the independence and channel forms of perfect secrecy coincide. -/
theorem perfectSecrecyAt_iff_ciphertextRowsEqualAt [Nonempty M]
    (encAlg : SymmEncAlg ProbComp M K C) :
    encAlg.perfectSecrecyAt ↔ encAlg.ciphertextRowsEqualAt :=
  ⟨ciphertextRowsEqualAt_of_perfectSecrecyAt_probComp encAlg,
    perfectSecrecyAt_of_ciphertextRowsEqualAt encAlg⟩

/-! ## Shannon's theorem -/

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

/-- **Shannon's theorem**, unique-key form, at one ciphertext. When every key has the same mass,
encryption under each key returns some ciphertext with probability one, and a unique key with
positive mass carries each message to each ciphertext with positive probability, every row gives
every ciphertext the mass of one key. -/
theorem prEvent_perfectSecrecyCipherGivenMsgExperiment_eq_of_uniformKey_of_uniqueKey
    [LawfulMonad m] [Fintype K] (encAlg : SymmEncAlg m M K C)
    (hkey : ∀ k, Pr{let k' ← encAlg.keygen}[k' = k] = (Fintype.card K : ℝ≥0∞)⁻¹)
    (henc : ∀ k msg, ∃ c, Pr{let c' ← encAlg.encrypt k msg}[c' = c] = 1)
    (hunique : ∀ msg c, ∃! k, 0 < Pr{let k' ← encAlg.keygen}[k' = k] ∧
      0 < Pr{let c' ← encAlg.encrypt k msg}[c' = c]) (msg : M) (c : C) :
    Pr{let c' ← encAlg.perfectSecrecyCipherGivenMsgExperiment msg}[c' = c] =
      (Fintype.card K : ℝ≥0∞)⁻¹ := by
  obtain ⟨k₀, ⟨hk₀, hc⟩, huniq⟩ := hunique msg c
  have henc_one : Pr{let c' ← encAlg.encrypt k₀ msg}[c' = c] = 1 := by
    obtain ⟨c₀, hc₀⟩ := henc k₀ msg
    suffices hcc : c = c₀ by rw [hcc]; exact hc₀
    by_contra hcc
    have hnot : Pr{let c' ← encAlg.encrypt k₀ msg}[¬c' = c₀] = 0 := by
      have hsum := prEvent_add_prEvent_not_eq_prEvent_true (encAlg.encrypt k₀ msg) (· = c₀)
      rw [hc₀] at hsum
      exact nonpos_iff_eq_zero.1 ((ENNReal.add_le_add_iff_left ENNReal.one_ne_top).1
        (by rw [add_zero, hsum]; exact prEvent_le_one _))
    refine hc.ne' (le_antisymm ?_ zero_le)
    calc Pr{let c' ← encAlg.encrypt k₀ msg}[c' = c]
        ≤ Pr{let c' ← encAlg.encrypt k₀ msg}[¬c' = c₀] :=
          prEvent_mono _ _ _ fun c' hc' => by rw [hc']; exact hcc
      _ = 0 := hnot
  rw [perfectSecrecyCipherGivenMsgExperiment, prEvent_bind, prEvent_bind_eq_sum_fintype,
    Finset.sum_eq_single k₀, hkey k₀, henc_one, mul_one]
  · intro k _ hk
    by_contra hmul
    exact hk (huniq k ⟨pos_iff_ne_zero.2 (left_ne_zero_of_mul hmul),
      pos_iff_ne_zero.2 (right_ne_zero_of_mul hmul)⟩)
  · exact fun h => absurd (Finset.mem_univ k₀) h

/-- **Shannon's theorem**, unique-key channel form: a uniform key, deterministic encryption, and
a unique key carrying each message to each ciphertext give equal ciphertext rows. -/
theorem ciphertextRowsEqualAt_of_uniformKey_of_uniqueKey [LawfulMonad m] [Fintype K]
    [Countable C] (encAlg : SymmEncAlg m M K C)
    (hkey : ∀ k, Pr{let k' ← encAlg.keygen}[k' = k] = (Fintype.card K : ℝ≥0∞)⁻¹)
    (henc : ∀ k msg, ∃ c, Pr{let c' ← encAlg.encrypt k msg}[c' = c] = 1)
    (hunique : ∀ msg c, ∃! k, 0 < Pr{let k' ← encAlg.keygen}[k' = k] ∧
      0 < Pr{let c' ← encAlg.encrypt k msg}[c' = c]) :
    encAlg.ciphertextRowsEqualAt := fun msg₀ msg₁ =>
  evalDistEq_iff_forall_prEvent_eq_output.2 fun c => by
    rw [prEvent_perfectSecrecyCipherGivenMsgExperiment_eq_of_uniformKey_of_uniqueKey encAlg
        hkey henc hunique msg₀ c,
      prEvent_perfectSecrecyCipherGivenMsgExperiment_eq_of_uniformKey_of_uniqueKey encAlg
        hkey henc hunique msg₁ c]

/-- **Shannon's theorem**, unique-key independence form: a uniform key, deterministic encryption,
and a unique key carrying each message to each ciphertext give perfect secrecy. -/
theorem perfectSecrecyAt_of_uniformKey_of_uniqueKey [LawfulMonad m] [Nonempty M] [Fintype K]
    [Countable C] (encAlg : SymmEncAlg m M K C)
    (hkey : ∀ k, Pr{let k' ← encAlg.keygen}[k' = k] = (Fintype.card K : ℝ≥0∞)⁻¹)
    (henc : ∀ k msg, ∃ c, Pr{let c' ← encAlg.encrypt k msg}[c' = c] = 1)
    (hunique : ∀ msg c, ∃! k, 0 < Pr{let k' ← encAlg.keygen}[k' = k] ∧
      0 < Pr{let c' ← encAlg.encrypt k msg}[c' = c]) :
    encAlg.perfectSecrecyAt :=
  perfectSecrecyAt_of_ciphertextRowsEqualAt encAlg
    (ciphertextRowsEqualAt_of_uniformKey_of_uniqueKey encAlg hkey henc hunique)

/-- **Shannon's theorem** for oracle computations under uniform oracle semantics, with the
hypotheses in support form: encryption under each key has a single reachable ciphertext, and a
unique reachable key carries each message to each ciphertext. -/
theorem ciphertextRowsEqualAt_of_uniformKey_of_uniqueKey_support {ι : Type u}
    {spec : OracleSpec.{u, 0} ι} [OracleSpec.UniformAnswerMeasure spec] [Fintype K] [Countable C]
    (encAlg : SymmEncAlg (OracleComp spec) M K C)
    (deterministicEnc : ∀ k msg, ∃ c, support (encAlg.encrypt k msg) = {c})
    (hkey : ∀ k, Pr{let k' ← encAlg.keygen}[k' = k] = (Fintype.card K : ℝ≥0∞)⁻¹)
    (hunique : ∀ msg c, ∃! k, k ∈ support encAlg.keygen ∧ c ∈ support (encAlg.encrypt k msg)) :
    encAlg.ciphertextRowsEqualAt :=
  ciphertextRowsEqualAt_of_uniformKey_of_uniqueKey encAlg hkey
    (fun k msg => by
      obtain ⟨c, hc⟩ := deterministicEnc k msg
      exact ⟨c, (OracleComp.prEvent_eq_one_iff _ _).2 fun c' hc' =>
        Set.mem_singleton_iff.1 (hc ▸ hc')⟩)
    fun msg c => by
      obtain ⟨k, hk, huniq⟩ := hunique msg c
      exact ⟨k, ⟨pos_iff_ne_zero.2 (OracleComp.prEvent_ne_zero_of_mem_support hk.1),
        pos_iff_ne_zero.2 (OracleComp.prEvent_ne_zero_of_mem_support hk.2)⟩,
        fun k' hk' => huniq k' ⟨(OracleComp.mem_support_iff_prEvent_ne_zero _ _).2 hk'.1.ne',
          (OracleComp.mem_support_iff_prEvent_ne_zero _ _).2 hk'.2.ne'⟩⟩

end SymmEncAlg
