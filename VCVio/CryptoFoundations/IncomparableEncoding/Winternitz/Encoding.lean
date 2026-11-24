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

The Winternitz encoding (Construction 5 of DKKW25) hashes the message and randomizer with a
tweakable hash to get a payload, and returns the payload with its checksum digits appended. It
never fails, so `failureMass_zero` shows that its error is zero for every sampler (Lemma 5).

## References

- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), Construction 5 and Lemma 5.
-/

public section

namespace IncomparableEncoding.Winternitz

open IncomparableEncoding

/-- Parameters of the Winternitz encoding, including the tweakable message hash.
The hash bundle contains `seedGen`. The encoding takes the public seed as an argument and does not
require `seedGen` to agree with how a surrounding scheme samples its public seed. -/
structure Parameters (PP M R E Tweak : Type) (n₀ w : ℕ) where
  /-- The payload has positive length. -/
  payloadLengthPositive : 0 < n₀
  /-- The base `2^w` has at least two digits. -/
  digitWidthPositive : 0 < w
  /-- The tweakable message hash returns exactly `n₀` bounded payload digits. -/
  thf : TweakableHash PP Tweak (M × R) (Codeword n₀ (2 ^ w))
  /-- The public epoch-to-tweak map. -/
  epochToTweak : E → Tweak

variable {PP M R E Tweak : Type} {n₀ w : ℕ}

/-- Positive payload length and digit width give two distinct checksum words. -/
theorem two_codewords (p : Parameters PP M R E Tweak n₀ w) :
    ∃ x y : Codeword (n₀ + checksumWidth n₀ w) (2 ^ w),
      x ∈ checksumWordCode n₀ w ∧ y ∈ checksumWordCode n₀ w ∧ x ≠ y := by
  let zero : Codeword n₀ (2 ^ w) := fun _ => ⟨0, by positivity⟩
  let one : Codeword n₀ (2 ^ w) := fun _ => ⟨1, one_lt_radix p.digitWidthPositive⟩
  refine ⟨word zero, word one, ⟨zero, rfl⟩, ⟨one, rfl⟩, ?_⟩
  intro heq
  have hcoord := congrFun heq (Fin.castAdd (checksumWidth n₀ w)
    (⟨0, p.payloadLengthPositive⟩ : Fin n₀))
  have hval := congrArg Fin.val hcoord
  simp only [word, Fin.append_left] at hval
  simp [zero, one] at hval

/-- The Winternitz encoding: the hash payload followed by its checksum digits. It never fails.
Its code `checksumWordCode n₀ w` contains every checksum word, including words the hash never
outputs. -/
@[expose] def encoding (p : Parameters PP M R E Tweak n₀ w) :
    IncomparableEncoding PP M R E (n₀ + checksumWidth n₀ w) (2 ^ w) where
  code := checksumWordCode n₀ w
  incomparable := checksumWordCode_incomparable n₀ w p.digitWidthPositive
  encode pp msg r ep := some (word (p.thf.eval pp (p.epochToTweak ep) (msg, r)))
  mem_code_of_encode_eq_some := by
    intro pp msg r ep x h
    exact ⟨_, Option.some.inj h⟩

/-- Lemma 5 of DKKW25: the Winternitz encoding fails with probability zero, for every randomizer
sampler. -/
theorem failureMass_zero {m : Type → Type} [Monad m]
    (p : Parameters PP M R E Tweak n₀ w)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) :
    (encoding p).failureMass runtime sample pp msg ep = 0 := by
  rw [IncomparableEncoding.failureMass_eq_probability]
  let : MeasurableSpace R := ⊤
  rw [runtime.evalDist_map _ Measurable.of_discrete sample,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true)]
  have hempty : (fun r => ((encoding p).encode pp msg r ep).isNone) ⁻¹' ({true} : Set Bool) =
      ∅ := by
    ext r
    simp [encoding]
  rw [hempty]
  simp

end IncomparableEncoding.Winternitz
