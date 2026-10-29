/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Encoding.Error
public import VCVio.CryptoFoundations.TweakableHash
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic

/-!
# Classical Winternitz incomparable encoding

The checksum-word encoding appends the base-`2^w` digits of the
complementary payload checksum. Its width is
`⌊log_(2^w) (n₀(2^w - 1))⌋ + 1` (Construction 5 of ePrint 2025/055).
-/

public section

namespace GXMSS.Encoding.Winternitz

open GXMSS.Encoding

/-- The fixed width needed for the largest complementary checksum. -/
@[expose] def checksumWidth (n₀ w : ℕ) : ℕ :=
  Nat.log (2 ^ w) (n₀ * (2 ^ w - 1)) + 1

/-- The greatest possible sum of `n₀` base-`2^w` payload digits. -/
@[expose] def maximum (n₀ w : ℕ) : ℕ := n₀ * (2 ^ w - 1)

/-- A positive bit width makes the digit radix at least two. -/
theorem one_lt_radix {w : ℕ} (hw : 0 < w) : 1 < 2 ^ w :=
  Nat.one_lt_pow (Nat.ne_of_gt hw) (by decide)

/-- Every complementary checksum fits in the selected digit width. -/
theorem maximum_lt_pow_width (n₀ w : ℕ) (hw : 0 < w) :
    maximum n₀ w < (2 ^ w) ^ checksumWidth n₀ w := by
  exact Nat.lt_pow_succ_log_self (one_lt_radix hw) (maximum n₀ w)

/-- The natural-valued sum of the bounded payload digits. -/
@[expose] def payloadSum {n₀ w : ℕ} (payload : Codeword n₀ (2 ^ w)) : ℕ :=
  ∑ i : Fin n₀, (payload i).val

/-- A payload sum never exceeds the maximum complement minuend. -/
theorem payloadSum_le_maximum {n₀ w : ℕ} (payload : Codeword n₀ (2 ^ w)) :
    payloadSum payload ≤ maximum n₀ w := by
  unfold payloadSum maximum
  calc
    (∑ i : Fin n₀, (payload i).val) ≤ ∑ _i : Fin n₀, (2 ^ w - 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.le_sub_one_of_lt (payload i).isLt
    _ = n₀ * (2 ^ w - 1) := by simp

/-- The complementary checksum as an ordinary natural number. -/
@[expose] def complement {n₀ w : ℕ} (payload : Codeword n₀ (2 ^ w)) : ℕ :=
  maximum n₀ w - payloadSum payload

/-- The checksum is in the representable range for the selected width. -/
theorem complement_lt_pow_width {n₀ w : ℕ} (hw : 0 < w)
    (payload : Codeword n₀ (2 ^ w)) :
    complement payload < (2 ^ w) ^ checksumWidth n₀ w :=
  (Nat.sub_le _ _).trans_lt (maximum_lt_pow_width n₀ w hw)

/-- The low-first checksum digit at coordinate `i` is the corresponding quotient remainder. -/
@[expose] def checksum {n₀ w : ℕ} (_hw : 0 < w)
    (payload : Codeword n₀ (2 ^ w)) :
    Codeword (checksumWidth n₀ w) (2 ^ w) :=
  fun i => ⟨complement payload / (2 ^ w) ^ i.val % (2 ^ w),
    Nat.mod_lt _ (by positivity : 0 < 2 ^ w)⟩

/-- Appending zero digits does not change a digit's quotient-remainder value. -/
theorem digitsAppend_coordinate (b l n i : ℕ) (hb : 1 < b) (hn : n < b ^ l) :
    (Nat.digitsAppend b l n).getD i 0 = n / b ^ i % b := by
  let ds := Nat.digitsAppend b l n
  have hds := Nat.mapsTo_digitsAppend hb l hn
  have hrec : Nat.ofDigits b ds = n :=
    (Nat.setInvOn_digitsAppend_ofDigits hb l).2 hn
  have hmod : ds.getD i 0 % b = ds.getD i 0 := by
    by_cases hi : i < ds.length
    · exact Nat.mod_eq_of_lt (hds.2 _ (by
        rw [List.getD_eq_getElem ds 0 hi]
        exact List.getElem_mem hi))
    · simp [List.getD_eq_getElem?_getD, Nat.le_of_not_gt hi]
  have hdrop : ds.getD i 0 = (ds.drop i).head! := by
    simp [List.getD_eq_getElem?_getD, List.head!_eq_head?_getD]
  calc
    ds.getD i 0 = ds.getD i 0 % b := hmod.symm
    _ = (ds.drop i).head! % b := by rw [hdrop]
    _ = Nat.ofDigits b (ds.drop i) % b :=
      (Nat.ofDigits_mod_eq_head! b (ds.drop i)).symm
    _ = n / b ^ i % b := by
      rw [← hrec, Nat.ofDigits_div_pow_eq_ofDigits_drop i (by omega : 0 < b) ds hds.2]

/-- The explicit checksum coordinates agree with the canonical padded base digits. -/
theorem checksum_eq_padded_digits {n₀ w : ℕ} (hw : 0 < w)
    (payload : Codeword n₀ (2 ^ w)) (i : Fin (checksumWidth n₀ w)) :
    (checksum hw payload i).val =
      (Nat.digitsAppend (2 ^ w) (checksumWidth n₀ w) (complement payload)).getD i.val 0 := by
  exact (digitsAppend_coordinate _ _ _ _ (one_lt_radix hw)
    (complement_lt_pow_width hw payload)).symm

/-- The appended checksum digits decode to the exact complementary value. -/
theorem checksum_reconstruct {n₀ w : ℕ} (hw : 0 < w)
    (payload : Codeword n₀ (2 ^ w)) :
    Nat.ofDigits (2 ^ w)
        (List.ofFn fun i : Fin (checksumWidth n₀ w) => (checksum hw payload i).val) =
      complement payload := by
  let digits := Nat.digitsAppend (2 ^ w) (checksumWidth n₀ w) (complement payload)
  have hlen : digits.length = checksumWidth n₀ w :=
    Nat.length_digitsAppend (one_lt_radix hw) _ (complement_lt_pow_width hw payload)
  have hlist : (List.ofFn fun i : Fin (checksumWidth n₀ w) =>
      (checksum hw payload i).val) = digits := by
    apply List.ext_get
    · simp [hlen]
    · intro i h₁ h₂
      have hc := checksum_eq_padded_digits hw payload ⟨i, by simpa using h₁⟩
      rw [List.getD_eq_getElem digits 0 h₂] at hc
      simpa [digits] using hc
  rw [hlist]
  exact (Nat.setInvOn_digitsAppend_ofDigits (one_lt_radix hw)
    (checksumWidth n₀ w)).2 (complement_lt_pow_width hw payload)

/-- Appending the payload and its canonical complementary checksum. -/
@[expose] def word {n₀ w : ℕ} (hw : 0 < w)
    (payload : Codeword n₀ (2 ^ w)) :
    Codeword (n₀ + checksumWidth n₀ w) (2 ^ w) :=
  Fin.append payload (checksum hw payload)

/-- The checksum-word code over all bounded payloads. -/
@[expose] def checksumWordCode (n₀ w : ℕ) (hw : 0 < w) :
    Set (Codeword (n₀ + checksumWidth n₀ w) (2 ^ w)) :=
  Set.range (word (n₀ := n₀) hw)

/-- Coordinatewise larger digit lists have larger numerical values. -/
theorem ofDigits_le_of_forall₂ (b : ℕ) {xs ys : List ℕ}
    (h : List.Forall₂ (· ≤ ·) xs ys) : Nat.ofDigits b xs ≤ Nat.ofDigits b ys := by
  induction h with
  | nil => rfl
  | @cons _ _ _ _ hxy _ ih =>
    simpa only [Nat.ofDigits_cons] using Nat.add_le_add hxy (Nat.mul_le_mul_left b ih)

/-- Coordinatewise comparison of finite digit vectors compares their numerical values. -/
theorem ofDigits_le_of_pointwise {n b : ℕ} {xs ys : Fin n → Fin b}
    (hle : ∀ i, xs i ≤ ys i) :
    Nat.ofDigits b (List.ofFn fun i => (xs i).val) ≤
      Nat.ofDigits b (List.ofFn fun i => (ys i).val) := by
  apply ofDigits_le_of_forall₂
  apply List.forall₂_of_length_eq_of_get
  · simp
  · intro i h₁ h₂
    simpa using hle ⟨i, by simpa using h₁⟩

/-- Comparability of two output words forces equality of their payloads. -/
theorem word_eq_of_le {n₀ w : ℕ} (hw : 0 < w)
    (xs ys : Codeword n₀ (2 ^ w))
    (hle : ∀ i, word hw xs i ≤ word hw ys i) : word hw xs = word hw ys := by
  have hp : ∀ i, xs i ≤ ys i := by
    intro i
    simpa [word] using hle (Fin.castAdd (checksumWidth n₀ w) i)
  have hc : ∀ i, checksum hw xs i ≤ checksum hw ys i := by
    intro i
    simpa [word] using hle (Fin.natAdd n₀ i)
  have hsum : payloadSum xs ≤ payloadSum ys := by
    unfold payloadSum
    apply Finset.sum_le_sum
    intro i _
    exact hp i
  have hcomp : complement xs ≤ complement ys := by
    have hdigits := ofDigits_le_of_pointwise hc
    simpa [checksum_reconstruct hw] using hdigits
  have hsumEq : payloadSum xs = payloadSum ys := by
    have hxs := payloadSum_le_maximum xs
    have hys := payloadSum_le_maximum ys
    unfold complement at hcomp
    omega
  have hcoords : ∀ i ∈ Finset.univ, (xs i).val = (ys i).val :=
    (Finset.sum_eq_sum_iff_of_le fun i _ => show (xs i).val ≤ (ys i).val from hp i).mp hsumEq
  have : xs = ys := by
    funext i
    exact Fin.ext (hcoords i (Finset.mem_univ i))
  simp [this]

/-- All distinct checksum words from bounded payloads are incomparable. -/
theorem checksumWordCode_incomparable (n₀ w : ℕ) (hw : 0 < w) :
    IncomparableCode (checksumWordCode n₀ w hw) := by
  intro x hx y hy hne
  have strict : ∀ {a b : Codeword (n₀ + checksumWidth n₀ w) (2 ^ w)},
      a ∈ checksumWordCode n₀ w hw → b ∈ checksumWordCode n₀ w hw → a ≠ b →
        ∃ i, a i < b i := by
    intro a b ha hb hab
    by_contra h
    have hle : ∀ i, b i ≤ a i := by
      intro i
      exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
    rcases ha with ⟨pa, rfl⟩
    rcases hb with ⟨pb, rfl⟩
    exact hab (word_eq_of_le hw pb pa hle).symm
  exact ⟨strict hx hy hne, strict hy hx hne.symm⟩

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

/-- Lemma 5 specialized to VCVio's canonical finite uniform randomizer sampler. -/
theorem probComp_uniformErrorAtMost_zero
    {PP M R E Tweak : Type} [Fintype R] [SampleableType R] {n₀ w : ℕ}
    (p : Parameters PP M R E Tweak n₀ w) :
    (encoding p).UniformErrorAtMost ProbCompRuntime.probComp ($ᵗ R) 0 :=
  uniformErrorAtMost_zero p ProbCompRuntime.probComp ($ᵗ R)
    (uniformSampler_uniformSample R)

end GXMSS.Encoding.Winternitz
