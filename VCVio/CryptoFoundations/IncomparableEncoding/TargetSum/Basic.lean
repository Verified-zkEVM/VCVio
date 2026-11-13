/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.Basic
public import VCVio.CryptoFoundations.TweakableHash

/-!
# Target-sum incomparable encoding

The global fixed-sum code is independent of hash surjectivity. Encoding returns the hash word
exactly when its digit sum meets the target, including empty and impossible codes.
-/

public section

namespace IncomparableEncoding.TargetSum

open IncomparableEncoding

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

end IncomparableEncoding.TargetSum
