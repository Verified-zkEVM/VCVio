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

The target-sum encoding (Construction 6 of DKKW25) hashes the message and randomizer with a
tweakable hash to get a word of `v` base-`2^w` digits. It returns the word when the digit sum
equals `target`, and fails otherwise. Its code contains every word with digit sum `target`,
whether or not the hash can output it. The code may be empty.

## References

- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), Construction 6.
-/

public section

namespace IncomparableEncoding.TargetSum

open IncomparableEncoding

/-- Parameters of the target-sum encoding. The hash bundle contains `seedGen`. The encoding takes
the public seed as an argument and does not require `seedGen` to agree with how a surrounding
scheme samples its public seed. The collision reduction, not correctness, needs the epoch map to be
injective. -/
structure Parameters (PP M R E Tweak : Type) (v w target : ℕ) where
  /-- The tweakable message hash returns exactly `v` base-`2^w` digits. -/
  thf : TweakableHash PP Tweak (M × R) (Codeword v (2 ^ w))
  /-- The public epoch-to-tweak map. -/
  epochToTweak : E → Tweak

variable {PP M R E Tweak : Type} {v w target : ℕ}

/-- The sum of the digits of a word. -/
@[expose] def digitSum {v radix : ℕ} (x : Codeword v radix) : ℕ :=
  ∑ i : Fin v, (x i).val

/-- The target-sum test as a Boolean: the digit sum of `x` equals `target`. -/
@[expose] def accepts (target : ℕ) {v radix : ℕ} (x : Codeword v radix) : Bool :=
  decide (digitSum x = target)

/-- The code of all words with digit sum `target`. -/
@[expose] def code (v w target : ℕ) : Set (Codeword v (2 ^ w)) :=
  {x | digitSum x = target}

/-- Words with the same digit sum are incomparable. -/
theorem code_incomparable (v w target : ℕ) :
    IncomparableCode (code v w target) := by
  intro x hx y hy hne
  exact incomparableWords_of_sum_eq hne (hx.trans hy.symm)

/-- The target-sum encoding returns the hash word if its digit sum is `target`, and fails
otherwise. -/
@[expose] def encoding (p : Parameters PP M R E Tweak v w target) :
    IncomparableEncoding PP M R E v (2 ^ w) where
  code := code v w target
  incomparable := code_incomparable v w target
  encode pp msg r ep :=
    if digitSum (p.thf.eval pp (p.epochToTweak ep) (msg, r)) = target then
      some (p.thf.eval pp (p.epochToTweak ep) (msg, r))
    else none
  mem_code_of_encode_eq_some := by
    intro pp msg r ep x h
    split at h
    · cases h
      assumption
    · cases h

/-- The encoding returns `x` exactly when the hash outputs `x` and `x` has digit sum `target`. -/
theorem encode_eq_some_iff (p : Parameters PP M R E Tweak v w target)
    (pp : PP) (msg : M) (r : R) (ep : E) (x : Codeword v (2 ^ w)) :
    (encoding p).encode pp msg r ep = some x ↔
      p.thf.eval pp (p.epochToTweak ep) (msg, r) = x ∧ digitSum x = target := by
  simp only [encoding]
  split
  · constructor
    · rintro ⟨⟩
      exact ⟨rfl, ‹_›⟩
    · rintro ⟨rfl, -⟩
      rfl
  · simp only [reduceCtorEq, false_iff, not_and]
    rintro rfl
    assumption

/-- The encoding fails exactly when the hash output's digit sum is not `target`. -/
theorem encode_eq_none_iff (p : Parameters PP M R E Tweak v w target)
    (pp : PP) (msg : M) (r : R) (ep : E) :
    (encoding p).encode pp msg r ep = none ↔
      digitSum (p.thf.eval pp (p.epochToTweak ep) (msg, r)) ≠ target := by
  simp [encoding]

end IncomparableEncoding.TargetSum
