/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.Winternitz.Code
public import VCVio.CryptoFoundations.IncomparableEncoding.Error
public import VCVio.CryptoFoundations.TweakableHash

/-!
# Winternitz incomparable encoding

A tweakable message hash supplies bounded payloads. Appended checksum words use one global
code and always return successfully; explicit sampler laws determine their error observations.
-/

public section

namespace IncomparableEncoding.Winternitz

open IncomparableEncoding

/-- Parameters of the checksum-word encoding, including the tweakable message hash.
The hash bundle contains `seedGen`; this encoding takes an explicit public seed and imposes no
agreement between `seedGen` and any scheme-level public-seed sampling law. -/
structure Parameters (PP M R E Tweak : Type) (n₀ w : ℕ) where
  /-- The payload has positive length. -/
  payloadLengthPositive : 0 < n₀
  /-- The base `2^w` has at least two digits. -/
  digitWidthPositive : 0 < w
  /-- The tweakable message hash returns exactly `n₀` bounded payload digits. -/
  thf : TweakableHash PP Tweak (M × R) (Codeword n₀ (2 ^ w))
  /-- The public epoch-to-tweak map. -/
  epochToTweak : E → Tweak

/-- The global checksum-word code over every bounded payload. This code may contain words that
the particular message hash cannot output; its membership is independent of hash surjectivity. -/
@[expose] def code {PP M R E Tweak : Type} {n₀ w : ℕ}
    (p : Parameters PP M R E Tweak n₀ w) :
    Set (Codeword (n₀ + checksumWidth n₀ w) (2 ^ w)) :=
  checksumWordCode n₀ w p.digitWidthPositive

/-- The global checksum-word code is incomparable. -/
theorem code_incomparable {PP M R E Tweak : Type} {n₀ w : ℕ}
    (p : Parameters PP M R E Tweak n₀ w) : IncomparableCode (code p) := by
  exact checksumWordCode_incomparable n₀ w p.digitWidthPositive

/-- Positive payload length and digit width give two distinct global checksum words. -/
theorem two_codewords {PP M R E Tweak : Type} {n₀ w : ℕ}
    (p : Parameters PP M R E Tweak n₀ w) :
    ∃ x y : Codeword (n₀ + checksumWidth n₀ w) (2 ^ w),
      x ∈ code p ∧ y ∈ code p ∧ x ≠ y := by
  let zero : Codeword n₀ (2 ^ w) := fun _ => ⟨0, by positivity⟩
  let one : Codeword n₀ (2 ^ w) :=
    fun _ => ⟨1, one_lt_radix p.digitWidthPositive⟩
  refine ⟨word p.digitWidthPositive zero, word p.digitWidthPositive one,
    ⟨zero, rfl⟩, ⟨one, rfl⟩, ?_⟩
  intro heq
  have hcoord := congrFun heq (Fin.castAdd (checksumWidth n₀ w)
    (⟨0, p.payloadLengthPositive⟩ : Fin n₀))
  have hval := congrArg Fin.val hcoord
  simp only [word, Fin.append_left] at hval
  simp [zero, one] at hval

/-- The checksum-word encoding never returns failure and uses one global code. -/
@[expose] def encoding {PP M R E Tweak : Type} {n₀ w : ℕ}
    (p : Parameters PP M R E Tweak n₀ w) :
    IncomparableEncoding PP M R E (n₀ + checksumWidth n₀ w) (2 ^ w) where
  code := code p
  incomparable := code_incomparable p
  encode pp msg r ep :=
    some ⟨word p.digitWidthPositive (p.thf.eval pp (p.epochToTweak ep) (msg, r)),
      ⟨p.thf.eval pp (p.epochToTweak ep) (msg, r), rfl⟩⟩

/-- The returned word is exactly the payload with its canonical checksum. -/
theorem value_eq_some {PP M R E Tweak : Type} {n₀ w : ℕ}
    (p : Parameters PP M R E Tweak n₀ w)
    (pp : PP) (msg : M) (r : R) (ep : E) :
    (encoding p).value pp msg r ep =
      some (word p.digitWidthPositive (p.thf.eval pp (p.epochToTweak ep) (msg, r))) := rfl

/-- Every input has zero returned encoding failures. -/
theorem value_ne_none {PP M R E Tweak : Type} {n₀ w : ℕ}
    (p : Parameters PP M R E Tweak n₀ w)
    (pp : PP) (msg : M) (r : R) (ep : E) :
    (encoding p).value pp msg r ep ≠ none := by
  rw [value_eq_some]
  simp

/-- The returned-failure measure is zero even before imposing a sampling law. -/
theorem failureMass_zero {m : Type → Type} [Monad m]
    {PP M R E Tweak : Type} {n₀ w : ℕ}
    (p : Parameters PP M R E Tweak n₀ w)
    (runtime : ProbCompRuntime m) (sample : m R)
    (pp : PP) (msg : M) (ep : E) :
    (encoding p).failureMass runtime sample pp msg ep = 0 := by
  rw [IncomparableEncoding.failureMass_eq_probability]
  let : MeasurableSpace R := ⊤
  rw [runtime.evalDist_map ((encoding p).failed pp msg ep) Measurable.of_discrete sample]
  rw [MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true)]
  have hempty : ((encoding p).failed pp msg ep) ⁻¹' ({true} : Set Bool) = ∅ := by
    ext r
    simp [IncomparableEncoding.failed, value_eq_some]
  rw [hempty]
  simp

/-- Zero error under a named lossless uniform randomizer sampler (Lemma 5 of ePrint 2025/055). -/
theorem uniformErrorAtMost_zero {m : Type → Type} [Monad m]
    {PP M R E Tweak : Type} [Fintype R] {n₀ w : ℕ}
    (p : Parameters PP M R E Tweak n₀ w)
    (runtime : ProbCompRuntime m) (sample : m R)
    (hu : UniformSampler runtime sample) :
    (encoding p).UniformErrorAtMost runtime sample 0 := by
  exact ⟨hu, hu.1, fun pp msg ep => by simp [failureMass_zero p runtime sample pp msg ep]⟩

/-- Canonical pointwise failure is zero, independently of any public-seed distribution. -/
theorem canonicalErrorAtMost_zero
    {PP M R E Tweak : Type} [SampleableType R] {n₀ w : ℕ}
    (p : Parameters PP M R E Tweak n₀ w) :
    (encoding p).CanonicalErrorAtMost 0 := by
  intro pp msg ep
  rw [failureMass_zero]

/-- Lemma 5 specialized to VCVio's canonical finite uniform randomizer sampler. -/
theorem probComp_uniformErrorAtMost_zero
    {PP M R E Tweak : Type} [Fintype R] [SampleableType R] {n₀ w : ℕ}
    (p : Parameters PP M R E Tweak n₀ w) :
    (encoding p).UniformErrorAtMost ProbCompRuntime.probComp ($ᵗ R) 0 :=
  ((encoding p).uniformErrorAtMost_uniformSample_iff 0).2 (canonicalErrorAtMost_zero p)

end IncomparableEncoding.Winternitz
