/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Encoding.Error
public import VCVio.CryptoFoundations.TweakableHash
public import ToMathlib.Data.ENNReal.AbsDiff
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Tactic

/-!
# Target-sum Winternitz incomparable encoding

The target-sum encoding returns a hash word exactly when its digit sum is the target.
Its global code is independent of the public parameter, message, randomizer, and epoch.
This is Construction 6 of ePrint 2025/055. No concrete hash-output distribution is assumed.
-/

public section

namespace GXMSS.Encoding.TargetSum

open GXMSS.Encoding
open ENNReal

/-- Parameters for target-sum encoding. The hash-family seed sampler is part of the
THF interface; this encoding uses the supplied public parameter and does not assert
that the THF sampler agrees with any surrounding scheme's public-seed sampler.
Injectivity of the epoch map is needed by a later collision reduction, not correctness. -/
structure Parameters (PP M R E Tweak : Type) (v w target : ℕ) where
  /-- The tweakable message hash returns exactly `v` base-`2^w` digits. -/
  thf : TweakableHash PP Tweak (M × R) (Codeword v (2 ^ w))
  /-- The public epoch-to-tweak map. -/
  epochToTweak : E → Tweak

variable {PP M R E Tweak : Type} {v w target : ℕ}

/-- The complete, global target-sum code. -/
@[expose] def code (v w target : ℕ) : Set (Codeword v (2 ^ w)) :=
  {x | ∑ i : Fin v, (x i).val = target}

/-- Words in the same target-sum code are globally incomparable. -/
theorem code_incomparable (v w target : ℕ) :
    IncomparableCode (code v w target) := by
  intro x hx y hy hne
  exact incomparableWords_of_sum_eq hne (hx.trans hy.symm)

/-- Target-sum encoding with explicit returned failure on a sum mismatch. -/
@[expose] def encoding (p : Parameters PP M R E Tweak v w target) :
    IncomparableEncoding PP M R E v (2 ^ w) where
  code := code v w target
  incomparable := code_incomparable v w target
  encode pp msg r ep :=
    if h : (∑ i : Fin v, (p.thf.eval pp (p.epochToTweak ep) (msg, r) i).val) = target then
      some ⟨p.thf.eval pp (p.epochToTweak ep) (msg, r), h⟩
    else none

/-- Acceptance is exactly the target-sum predicate, including empty and impossible codes. -/
theorem value_eq_some_iff (p : Parameters PP M R E Tweak v w target)
    (pp : PP) (msg : M) (r : R) (ep : E) (x : Codeword v (2 ^ w)) :
    (encoding p).value pp msg r ep = some x ↔
      p.thf.eval pp (p.epochToTweak ep) (msg, r) = x ∧
      (∑ i : Fin v, (x i).val) = target := by
  by_cases h : (∑ i : Fin v, (p.thf.eval pp (p.epochToTweak ep) (msg, r) i).val) = target
  · constructor
    · intro hv
      have heq : p.thf.eval pp (p.epochToTweak ep) (msg, r) = x := by
        simpa [encoding, IncomparableEncoding.value, h] using hv
      exact ⟨heq, by rw [← heq]; exact h⟩
    · rintro ⟨heq, _⟩
      rw [← heq]
      simp [encoding, IncomparableEncoding.value, h]
  · constructor
    · intro hv
      simp [encoding, IncomparableEncoding.value, h] at hv
    · rintro ⟨heq, hsum⟩
      exact (h (by rw [heq]; exact hsum)).elim

/-- A returned failure is precisely a sum mismatch. -/
theorem value_eq_none_iff (p : Parameters PP M R E Tweak v w target)
    (pp : PP) (msg : M) (r : R) (ep : E) :
    (encoding p).value pp msg r ep = none ↔
      (∑ i : Fin v, (p.thf.eval pp (p.epochToTweak ep) (msg, r) i).val) ≠ target := by
  simp [encoding, IncomparableEncoding.value, code]

/-- Every successful output belongs to the same fixed-sum code. -/
theorem success_mem_code (p : Parameters PP M R E Tweak v w target)
    (pp : PP) (msg : M) (r : R) (ep : E) {x : Codeword v (2 ^ w)}
    (h : (encoding p).value pp msg r ep = some x) : x ∈ code v w target :=
  (encoding p).mem_code_of_value_eq_some pp msg r ep h

/-- The base-`2^w` digit polynomial `1 + X + ⋯ + X^(2^w-1)`. -/
@[expose] noncomputable def digitPolynomial (w : ℕ) : Polynomial ℕ :=
  ∑ d : Fin (2 ^ w), Polynomial.X ^ d.val

/-- The coefficient `η_T` in `(1 + X + ⋯ + X^(2^w-1))^v`. -/
@[expose] noncomputable def coefficient (v w target : ℕ) : ℕ :=
  Polynomial.coeff (digitPolynomial w ^ v) target

/-- The finite set of all target-sum words. -/
@[expose] def acceptedWords (v w target : ℕ) : Finset (Codeword v (2 ^ w)) :=
  Finset.univ.filter fun x => (∑ i : Fin v, (x i).val) = target

/-- The exact finite acceptance count, including empty and impossible codes. -/
@[expose] def acceptedCount (v w target : ℕ) : ℕ :=
  (acceptedWords v w target).card

/-- A parameter-only acceptance count of at least two supplies the generic code premise. -/
theorem two_codewords_of_acceptedCount (v w target : ℕ)
    (hcount : 2 ≤ acceptedCount v w target) :
    ∃ x y : Codeword v (2 ^ w),
      x ∈ code v w target ∧ y ∈ code v w target ∧ x ≠ y := by
  have hcard : 1 < (acceptedWords v w target).card := by
    dsimp only [acceptedCount] at hcount
    omega
  obtain ⟨x, y, hx, hy, hne⟩ := Finset.one_lt_card_iff.mp hcard
  exact ⟨x, y, by simpa [acceptedWords, code] using hx,
    by simpa [acceptedWords, code] using hy, hne⟩

/-- Two positions can hold a positive target digit in different coordinates. This gives a
simple arithmetic sufficient condition independent of hash-output surjectivity. -/
theorem two_codewords_of_small_target (v w target : ℕ)
    (hv : 2 ≤ v) (htarget : 0 < target) (hfit : target < 2 ^ w) :
    ∃ x y : Codeword v (2 ^ w),
      x ∈ code v w target ∧ y ∈ code v w target ∧ x ≠ y := by
  let zero : Fin v := ⟨0, by omega⟩
  let one : Fin v := ⟨1, by omega⟩
  let digit : Fin (2 ^ w) := ⟨target, hfit⟩
  let x : Codeword v (2 ^ w) := fun i => if i = zero then digit else 0
  let y : Codeword v (2 ^ w) := fun i => if i = one then digit else 0
  have hx : x ∈ code v w target := by
    change (∑ i, (x i).val) = target
    calc
      _ = ∑ i : Fin v, if i = zero then target else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = zero <;> simp [x, digit, hi]
      _ = target := by simp
  have hy : y ∈ code v w target := by
    change (∑ i, (y i).val) = target
    calc
      _ = ∑ i : Fin v, if i = one then target else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = one <;> simp [y, digit, hi]
      _ = target := by simp
  refine ⟨x, y, hx, hy, ?_⟩
  intro hxy
  have hzero := congrFun hxy zero
  have hne : zero ≠ one := by simp [zero, one]
  have : target = 0 := by simpa [x, y, hne, digit] using congrArg Fin.val hzero
  omega

/-- The simple two-position construction gives an explicit lower bound on the code size. -/
theorem acceptedCount_two_le_of_small_target (v w target : ℕ)
    (hv : 2 ≤ v) (htarget : 0 < target) (hfit : target < 2 ^ w) :
    2 ≤ acceptedCount v w target := by
  obtain ⟨x, y, hx, hy, hne⟩ :=
    two_codewords_of_small_target v w target hv htarget hfit
  have hcard : 1 < (acceptedWords v w target).card :=
    Finset.one_lt_card_iff.mpr ⟨x, y,
      by simpa [acceptedWords, code] using hx,
      by simpa [acceptedWords, code] using hy, hne⟩
  dsimp only [acceptedCount]
  omega

/-- The generating polynomial obtained by enumerating all bounded words. -/
private noncomputable def wordPolynomial (v w : ℕ) : Polynomial ℕ :=
  ∑ x : Codeword v (2 ^ w), Polynomial.X ^ (∑ i : Fin v, (x i).val)

/-- A generating-function monomial records the natural digit sum of a word. -/
private theorem coeff_wordPolynomial (v w target : ℕ) :
    Polynomial.coeff (wordPolynomial v w) target = acceptedCount v w target := by
  simp [wordPolynomial, acceptedCount, acceptedWords, Polynomial.coeff_X_pow, eq_comm]

/-- Enumerating all length-`v` words multiplies the digit polynomial `v` times. -/
private theorem wordPolynomial_eq_pow (v w : ℕ) :
    wordPolynomial v w = digitPolynomial w ^ v := by
  induction v with
  | zero =>
      simp [wordPolynomial]
  | succ v ih =>
      have hreindex :
          wordPolynomial (v + 1) w =
            ∑ pair : Fin (2 ^ w) × Codeword v (2 ^ w),
              Polynomial.X ^
                (∑ i : Fin (v + 1),
                  ((Fin.cons pair.1 pair.2 : Codeword (v + 1) (2 ^ w)) i).val) := by
        unfold wordPolynomial
        exact (Equiv.sum_comp (Fin.consEquiv fun _ : Fin (v + 1) => Fin (2 ^ w))
          (fun x : Codeword (v + 1) (2 ^ w) =>
            Polynomial.X ^ (∑ i : Fin (v + 1), (x i).val))).symm
      rw [hreindex, Fintype.sum_prod_type]
      simp_rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, pow_add]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      change digitPolynomial w * wordPolynomial v w = digitPolynomial w ^ v * digitPolynomial w ^ 1
      rw [ih, pow_one]
      exact mul_comm _ _

/-- The generating polynomial coefficient is exactly the cardinality of target-sum words. -/
theorem coefficient_eq_acceptedCount (v w target : ℕ) :
    coefficient v w target = acceptedCount v w target := by
  rw [coefficient, ← wordPolynomial_eq_pow]
  exact coeff_wordPolynomial v w target

/-- The finite complement of the accepted target-sum words. -/
@[expose] def rejectedWords (v w target : ℕ) : Finset (Codeword v (2 ^ w)) :=
  Finset.univ.filter fun x => (∑ i : Fin v, (x i).val) ≠ target

/-- Accepted and rejected words partition the full finite output alphabet. -/
theorem rejected_add_accepted_count (v w target : ℕ) :
    (rejectedWords v w target).card + acceptedCount v w target =
      Fintype.card (Codeword v (2 ^ w)) := by
  classical
  simpa [rejectedWords, acceptedWords, acceptedCount, eq_comm, add_comm] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Codeword v (2 ^ w))))
      (p := fun x => (∑ i : Fin v, (x i).val) ≠ target))

/-- Uniform mass of a finite output event. -/
@[expose] noncomputable def uniformEventMass (v w : ℕ)
    (event : Finset (Codeword v (2 ^ w))) : ℝ≥0∞ :=
  (event.card : ℝ≥0∞) * (Fintype.card (Codeword v (2 ^ w)) : ℝ≥0∞)⁻¹

/-- Uniform mass of words outside the target-sum code, expressed using the coefficient `η_T`. -/
@[expose] noncomputable def uniformRejectionMass (v w target : ℕ) : ℝ≥0∞ :=
  1 - (coefficient v w target : ℝ≥0∞) * (((2 ^ (w * v) : ℕ) : ℝ≥0∞))⁻¹

/-- The full output alphabet has cardinality `2^(wv)`. -/
theorem card_output (v w : ℕ) :
    Fintype.card (Codeword v (2 ^ w)) = 2 ^ (w * v) := by
  simp [Codeword, pow_mul]

/-- Counting rejection gives `1 - η_T / 2^(wv)`, as in Lemma 7 of ePrint 2025/055. -/
theorem uniformRejected_eq_uniformRejectionMass (v w target : ℕ) :
    uniformEventMass v w (rejectedWords v w target) =
      uniformRejectionMass v w target := by
  have hcount := rejected_add_accepted_count v w target
  have htotal : (Fintype.card (Codeword v (2 ^ w)) : ℝ≥0∞) ≠ 0 := by
    rw [card_output]
    simp
  have hmass : uniformEventMass v w (rejectedWords v w target) +
      uniformEventMass v w (acceptedWords v w target) = 1 := by
    unfold uniformEventMass
    rw [← add_mul, ← Nat.cast_add]
    change (↑((rejectedWords v w target).card + acceptedCount v w target) : ℝ≥0∞) *
      (Fintype.card (Codeword v (2 ^ w)) : ℝ≥0∞)⁻¹ = 1
    rw [hcount]
    exact ENNReal.mul_inv_cancel htotal (by simp)
  have hsub := ENNReal.eq_sub_of_add_eq' (by simp : (1 : ℝ≥0∞) ≠ ∞) hmass
  have hcoef : (acceptedWords v w target).card = coefficient v w target := by
    simpa [acceptedCount] using (coefficient_eq_acceptedCount v w target).symm
  unfold uniformEventMass at hsub
  rw [hcoef, card_output] at hsub
  simpa only [uniformEventMass, uniformRejectionMass, card_output] using hsub

/-- The returned mass of an arbitrary finite hash-output event at any tweak, under
an explicit randomizer sampler. The Boolean observation avoids conditioning on success. -/
@[expose] noncomputable def outputEventMass {m : Type → Type} [Monad m]
    {PP M R E Tweak : Type} {v w target : ℕ}
    (p : Parameters PP M R E Tweak v w target)
    (runtime : ProbCompRuntime m) (sample : m R)
    (pp : PP) (tw : Tweak) (msg : M)
    (event : Finset (Codeword v (2 ^ w))) : ℝ≥0∞ :=
  runtime.evalDist
    ((fun r => decide (p.thf.eval pp tw (msg, r) ∈ event)) <$> sample) {true}

/-- Every hash-output event differs from the corresponding uniform word event by at
most `ε`, for every public parameter, tweak, and message. This is the finite
statistical-distance premise of Definition 2 of ePrint 2025/055. It quantifies
over the entire output alphabet, including events beyond epoch-reachable tweaks. -/
@[expose] def EpsilonUniform {m : Type → Type} [Monad m]
    {PP M R E Tweak : Type} {v w target : ℕ}
    (p : Parameters PP M R E Tweak v w target)
    (runtime : ProbCompRuntime m) (sample : m R) (ε : ℝ≥0∞) : Prop :=
  ∀ pp tw msg (event : Finset (Codeword v (2 ^ w))),
    ENNReal.absDiff (outputEventMass p runtime sample pp tw msg event)
      (uniformEventMass v w event) ≤ ε

/-- The rejected-output event is exactly the encoding's returned-failure event. -/
theorem failureMass_eq_rejectedEventMass {m : Type → Type} [Monad m]
    {PP M R E Tweak : Type} {v w target : ℕ}
    (p : Parameters PP M R E Tweak v w target)
    (runtime : ProbCompRuntime m) (sample : m R)
    (pp : PP) (msg : M) (ep : E) :
    (encoding p).failureMass runtime sample pp msg ep =
      outputEventMass p runtime sample pp (p.epochToTweak ep) msg (rejectedWords v w target) := by
  rw [IncomparableEncoding.failureMass_eq_probability]
  have hobs : (encoding p).failed pp msg ep =
      fun r => decide (p.thf.eval pp (p.epochToTweak ep) (msg, r) ∈ rejectedWords v w target) := by
    funext r
    by_cases h : (∑ i : Fin v, (p.thf.eval pp (p.epochToTweak ep) (msg, r) i).val) = target
    · simp [IncomparableEncoding.failed, encoding, IncomparableEncoding.value,
        rejectedWords, h]
    · simp [IncomparableEncoding.failed, encoding, IncomparableEncoding.value,
        rejectedWords, h]
  rw [hobs]
  rfl

/-- Pointwise returned-failure bound from finite uniform randomness and epsilon
uniformity, corresponding to Lemma 7 of ePrint 2025/055. Missing randomizer
mass is separately zero by the lossless sampler law; there is no conditioning
or retry normalization. -/
theorem uniformErrorAtMost {m : Type → Type} [Monad m]
    {PP M R E Tweak : Type} [Fintype R] {v w target : ℕ}
    (p : Parameters PP M R E Tweak v w target)
    (runtime : ProbCompRuntime m) (sample : m R) (ε : ℝ≥0∞)
    (hu : UniformSampler runtime sample)
    (hε : EpsilonUniform p runtime sample ε) :
    (encoding p).UniformErrorAtMost runtime sample
      (ε + uniformRejectionMass v w target) := by
  refine ⟨hu, hu.1, ?_⟩
  intro pp msg ep
  rw [failureMass_eq_rejectedEventMass]
  calc
    outputEventMass p runtime sample pp (p.epochToTweak ep) msg (rejectedWords v w target) ≤
        uniformEventMass v w (rejectedWords v w target) + ε :=
      (ENNReal.absDiff_le_iff.mp
        (hε pp (p.epochToTweak ep) msg (rejectedWords v w target))).1
    _ = ε + uniformRejectionMass v w target := by
      rw [uniformRejected_eq_uniformRejectionMass]
      exact add_comm _ _

/-- The pointwise error bound with VCVio's canonical finite uniform randomizer
sampler. Hash-output uniformity remains an explicit premise. -/
theorem probComp_uniformErrorAtMost
    {PP M R E Tweak : Type} [Fintype R] [SampleableType R] {v w target : ℕ}
    (p : Parameters PP M R E Tweak v w target) (ε : ℝ≥0∞)
    (hε : EpsilonUniform p ProbCompRuntime.probComp ($ᵗ R) ε) :
    (encoding p).UniformErrorAtMost ProbCompRuntime.probComp ($ᵗ R)
      (ε + uniformRejectionMass v w target) :=
  uniformErrorAtMost p ProbCompRuntime.probComp ($ᵗ R) ε
    (uniformSampler_uniformSample R) hε

end GXMSS.Encoding.TargetSum
