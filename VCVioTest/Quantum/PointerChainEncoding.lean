/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Schemes.PointerChainPuzzle.QuantumEncoding

/-!
# Exact pointer-chain byte-window regressions

The finite raw register retains empty and malformed byte strings. The largest honest input
needs 86 bytes at the maximum link width. Equal-length inputs from different oracle families
remain distinct, and full-width masks retain their exact response with an empty tail.
-/

public section

open PointerChainPuzzle PointerChainPuzzle.LeanSeal

namespace VCVioTest.PointerChainEncoding

/-- A zero-length window contains exactly the empty byte string. -/
example (x : ByteArray.Bounded 0) : x.toByteArray = ByteArray.empty := by
  apply ByteArray.size_eq_zero_iff.mp
  exact Nat.eq_zero_of_le_zero x.property

/-- Enlarging a register changes no bytes and introduces no zero padding. -/
example (x : ByteArray.Bounded 0) :
    (x.widen (show 0 ≤ 86 by decide)).toByteArray = x.toByteArray := rfl

/-- An unencoded one-byte string is still a basis value of the raw query register. -/
@[expose, reducible]
def malformed : ByteArray.Bounded 86 := ⟨ByteArray.mk #[0xff], by decide⟩

private theorem malformed_not_encoded :
    malformed ∉ Set.range (hashInputWindow (n := 1) (show hashInputBound 32 ≤ 86 by decide)) := by
  rintro ⟨t, ht⟩
  have hs := congrArg (fun x : ByteArray.Bounded 86 ↦ x.toByteArray.size) ht
  change (hashInput t).size = 1 at hs
  rw [size_hashInput] at hs
  cases t <;> norm_num at hs

/-- The parser rejects malformed raw input without removing it from the input register. -/
example : route (b := 32) (n := 1) malformed.toByteArray = none ∧
    malformed ∉ Set.range (hashInputWindow (n := 1) (show hashInputBound 32 ≤ 86 by decide)) := by
  exact ⟨(route_eq_none_iff_not_mem_range_hashInputWindow
    (show hashInputBound 32 ≤ 86 by decide) (show 1 < 2 ^ 32 by decide) malformed).mpr
      malformed_not_encoded, malformed_not_encoded⟩

/-- Full-table completion preserves the full answer on malformed off-image inputs. -/
example (H : ByteArray.Bounded 86 → Bytes 32) :
    (windowTableEquiv (b := 32) (n := 1) (by decide) (by decide) (by decide) H).2
        ⟨malformed, malformed_not_encoded⟩ =
      H malformed := rfl

/-- The maximum-width start input. -/
@[expose, reducible]
def start32 : TypedPoint 32 1 := .start 0 0 0

/-- A window of 85 bytes excludes an honest maximum-width input; 86 bytes includes it. -/
example : (hashInput start32).size = 86 ∧ ¬ (hashInput start32).size ≤ 85 ∧
    (hashInputWindow (show hashInputBound 32 ≤ 86 by decide) start32).toByteArray =
      hashInput start32 := by
  have hs : (hashInput start32).size = 86 := by rw [size_hashInput]
  exact ⟨hs, by omega, rfl⟩

/-- A 29-byte-link start input has the same length as a commitment input. -/
@[expose, reducible]
def start29 : TypedPoint 29 1 := .start 0 0 0

/-- A commitment input at that same link width. -/
@[expose, reducible]
def commit29 : TypedPoint 29 1 := .commit 0 0

/-- Domain separation relies on the encoded family labels even when lengths coincide. -/
example : (hashInput start29).size = 83 ∧ (hashInput commit29).size = 83 ∧
    hashInput start29 ≠ hashInput commit29 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [size_hashInput]
  · rw [size_hashInput]
  · intro h
    have he := hashInput_injective (b := 29) (n := 1) (by decide) h
    cases he

/-- A full-width mask retains every byte of the raw oracle response. -/
example (H : ByteArray.Bounded 86 → Bytes 32) :
    (windowTableEquiv (b := 32) (n := 1) (by decide) (by decide) (by decide) H).1.1
        (.mask 0 0) =
      H (hashInputWindow (show hashInputBound 32 ≤ 86 by decide)
        (.mask 0 0 : TypedPoint 32 1)) := by
  rw [windowTableEquiv_apply_answer]
  exact Bytes.read_toList _

/-- The complementary tail of a full-width mask is exactly the empty zero-byte value. -/
example (H : ByteArray.Bounded 86 → Bytes 32) :
    (windowTableEquiv (b := 32) (n := 1) (by decide) (by decide) (by decide) H).1.2
      (.mask 0 0) = (0 : Bytes 0) := by
  apply Bytes.ext_getElem
  intro i hi
  omega

/-- Honest solver agreement holds for an arbitrary output measurable-space instance. Passing
that space to the chosen-space law preserves the same observation without requiring discreteness. -/
example {b n B : ℕ} (hB : hashInputBound b ≤ B)
    (H : ByteArray.Bounded B → Bytes 32) (m : ℕ) [NeZero n]
    [outputSpace : MeasurableSpace (Option (Bytes 32))] (puzzle : Puzzle b n) :
    (Quantum.parallelOracleRuntime H).evalDist₂ .instruments
        ((quantumWindowScheme hB m).solve puzzle) (Quantum.SubState.basis ()) =
      MeasureTheory.Measure.dirac (solve (extendWindowOracle H) m puzzle) := by
  exact evalDist_quantumWindowScheme_solve hB H m outputSpace puzzle

end VCVioTest.PointerChainEncoding
