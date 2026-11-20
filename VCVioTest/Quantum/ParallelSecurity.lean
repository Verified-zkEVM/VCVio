/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.ParallelSecurity
import VCVioTest.Quantum.ParallelPlantedPreimage

/-!
# Parallel security calibration regressions

Zero-width rounds do not improve the guessing term. A singleton-range no-query adversary
succeeds with probability one, so it has zero security bits and cannot satisfy a one-bit
claim. These checks use the fixed-target game's actual probability rather than an arbitrary
advantage function.
-/

public section

open Quantum
open scoped ENNReal

namespace VCVioTest.QuantumParallelSecurity

/-- Zero-width rounds keep the one-half guessing bound at one security bit. -/
example (D : ℕ) : parallelQROMBound 1 D 0 = 1 / 2 := by
  norm_num [parallelQROMBound]

/-- Non-power-of-two cardinalities retain fractional security bits. -/
example : parallelQROMBound (Real.logb 2 3) 0 17 = 1 / 3 := by
  rw [parallelQROMBound_logb 3 (by norm_num)]
  norm_num

/-- Return the sole input without consulting the oracle. -/
@[expose]
noncomputable def guessWithoutQueries :
    QuantumComp LocalSig.instruments.{0} (qromBatchSpec Unit (ZMod 1))
      (fun _ ↦ Unit) (QReg.of Unit) :=
  QuantumComp.pure ()

/-- The singleton-range game's actual guessing probability is one. -/
theorem singleton_guess_success :
    preimageSearchAdvantage (0 : ZMod 1) .instruments guessWithoutQueries
      (SubState.basis ()) (fun leaf ↦ leaf.2) = 1 := by
  rw [preimageSearchAdvantage_eq_of_isPointBound_zero_of_lossless
    (x := guessWithoutQueries) 0 .instruments
    (by simp [guessWithoutQueries]) (by simp [guessWithoutQueries])]
  norm_num [SubState.trace_basis]

/-- The named game's actual syntactic resource model certifies zero bits on a singleton range. -/
theorem singleton_zero_bits :
    ParallelQROMBits
      (fun x : QuantumComp LocalSig.instruments.{0} (qromBatchSpec Unit (ZMod 1))
        (fun _ ↦ Unit) (QReg.of Unit) ↦
        preimageSearchAdvantage 0 .instruments x (SubState.basis ()) (fun leaf ↦ leaf.2))
      (fun x D P ↦ x.IsTotalQueryBound D ∧ x.IsWidthBound P) 0 := by
  simpa using parallelQROMBits_preimageSearch (0 : ZMod 1) .instruments
    (W := fun _ ↦ Unit) (SubState.basis ()) (fun leaf ↦ leaf.2)

/-- A one-bit assertion would incorrectly bound the zero-query success by one half. -/
theorem singleton_not_one_bit :
    ¬ ParallelQROMBits
      (fun x : QuantumComp LocalSig.instruments.{0} (qromBatchSpec Unit (ZMod 1))
        (fun _ ↦ Unit) (QReg.of Unit) ↦
        preimageSearchAdvantage 0 .instruments x (SubState.basis ()) (fun leaf ↦ leaf.2))
      (fun x D P ↦ x.IsTotalQueryBound D ∧ x.IsWidthBound P) 1 := by
  intro h
  have hb := h 0 0 guessWithoutQueries
    ⟨by simp [guessWithoutQueries], by simp [guessWithoutQueries]⟩
  dsimp only at hb
  rw [singleton_guess_success] at hb
  norm_num [parallelQROMBound] at hb

/-- A secret input from a singleton domain is already known. Even with three possible
responses, its image-inversion game has zero bits, rather than the fixed-target `log₂ 3`. -/
example :
    ParallelQROMBits
      (plantedPreimageAdvantage (X := Unit) (Y := ZMod 3)
        (L := LocalSig.instruments.{0}) (W := fun _ ↦ Unit) (A := QReg.of Unit))
      (fun adv D P ↦ (∀ target, (adv.program target).IsTotalQueryBound D) ∧
        ∀ target, (adv.program target).IsWidthBound P) 0 := by
  simpa [ProbabilityTheory.plantedTargetDensity] using
    (parallelQROMBits_plantedPreimage (X := Unit) (Y := ZMod 3)
      (L := LocalSig.instruments.{0}) (W := fun _ ↦ Unit) (A := QReg.of Unit))

/-- The concrete 128-bit input and response spaces certify 127 bits for the actual
secret-input inversion game under syntactic round and width bounds. -/
example :
    ParallelQROMBits
      (plantedPreimageAdvantage (X := Fin (2 ^ 128)) (Y := ZMod (2 ^ 128))
        (L := LocalSig.instruments.{0}) (W := fun _ ↦ Fin (2 ^ 128)) (A := QReg.of Unit))
      (fun adv D P ↦ (∀ target, (adv.program target).IsTotalQueryBound D) ∧
        ∀ target, (adv.program target).IsWidthBound P) 127 :=
  parallelQROMBits_plantedPreimage_127 (by simp) (by simp)

/-- One additional bit in each space certifies 128 whole security bits. -/
example :
    ParallelQROMBits
      (plantedPreimageAdvantage (X := Fin (2 ^ 129)) (Y := ZMod (2 ^ 129))
        (L := LocalSig.instruments.{0}) (W := fun _ ↦ Fin (2 ^ 129)) (A := QReg.of Unit))
      (fun adv D P ↦ (∀ target, (adv.program target).IsTotalQueryBound D) ∧
        ∀ target, (adv.program target).IsWidthBound P) 128 :=
  parallelQROMBits_plantedPreimage_128 (by simp) (by simp)

/-- Lowering the advertised bit count preserves the same concrete game's certificate. -/
example :
    ParallelQROMBits
      (plantedPreimageAdvantage (X := Fin (2 ^ 128)) (Y := ZMod (2 ^ 128))
        (L := LocalSig.instruments.{0}) (W := fun _ ↦ Fin (2 ^ 128)) (A := QReg.of Unit))
      (fun adv D P ↦ (∀ target, (adv.program target).IsTotalQueryBound D) ∧
        ∀ target, (adv.program target).IsWidthBound P) 126 :=
  (parallelQROMBits_plantedPreimage_127 (by simp) (by simp)).mono (by norm_num)

/-- Actual zero-query inversion succeeds with probability two thirds on two inputs and three
responses, ruling out a one-bit certificate for that game's syntactic resource model. -/
theorem planted_not_one_bit :
    ¬ ParallelQROMBits
      (plantedPreimageAdvantage (X := Fin 2) (Y := ZMod 3)
        (L := LocalSig.instruments.{0}) (W := fun _ ↦ Fin 2) (A := QReg.of Unit))
      (fun adv D P ↦ (∀ target, (adv.program target).IsTotalQueryBound D) ∧
        ∀ target, (adv.program target).IsWidthBound P) 1 := by
  intro h
  have hb := h 0 0
    (QuantumParallelPlantedPreimage.noQuery (fun _ : ZMod 3 ↦ (0 : Fin 2))
      (SubState.basis ())) ⟨fun _ ↦ by simp, fun _ ↦ by simp⟩
  rw [QuantumParallelPlantedPreimage.no_query_density] at hb
  have hreal := ENNReal.toReal_mono (by norm_num [parallelQROMBound]) hb
  norm_num [parallelQROMBound] at hreal

end VCVioTest.QuantumParallelSecurity
