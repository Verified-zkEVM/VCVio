/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Graph.Fors.Dependencies

/-!
# Actual FORS schedules at two SHAKE parameter sets

The same natural-coordinate schedule supplies distinct calls, strict-prefix dependency reads,
and all returned signature cells for both actual SHAKE-128s and SHAKE-192f parameters. Short
digest inputs retain the actual parser's buffer behavior and global forest offsets.
-/

public section

open SLHDSA SLHDSA.Graph SLHDSA.Graph.ForsSchedule

namespace SLHDSA.Refactor.ForsScheduleTest

private theorem complete_schedule {p : Params} (valid : p.Valid) (key : ForsKey p)
    (md : List Byte) :
    (signing key md).Nodup ∧
    (∀ position : Fin (signing key md).length,
      ∀ child ∈ ((signing key md)[position]).children valid,
        child = .secretSeed ∨ ∃ earlier ∈ (signing key md).take position,
          child = .structural earlier) ∧
    (∀ tree, StructuralNode.forsPrf key (selected md tree) ∈ signing key md) ∧
    (∀ tree height, authentication key (selected md tree) height ∈ signing key md) := by
  refine ⟨signing_nodup key md, ?_, selected_mem_signing key md, authentication_mem_signing key md⟩
  intro position child member
  cases child with
  | secretSeed => exact Or.inl rfl
  | structural child =>
      exact Or.inr ⟨child, signing_children_before valid key md position child member, rfl⟩

local notation "vp128" => FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams
local notation "vp192" => FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams

/-- The actual 128s signer has distinct calls, earlier children and every returned cell. -/
theorem shake128s_complete (key : ForsKey (vp128).params) (md : List Byte) :
    (signing key md).Nodup ∧
    (∀ position : Fin (signing key md).length,
      ∀ child ∈ ((signing key md)[position]).children (vp128).valid,
        child = .secretSeed ∨ ∃ earlier ∈ (signing key md).take position,
          child = .structural earlier) ∧
    (∀ tree, StructuralNode.forsPrf key (selected md tree) ∈ signing key md) ∧
    (∀ tree height, authentication key (selected md tree) height ∈ signing key md) :=
  complete_schedule (vp128).valid key md

/-- The actual 192f signer consumes the same full schedule theorem at its different dimensions. -/
theorem shake192f_complete (key : ForsKey (vp192).params) (md : List Byte) :
    (signing key md).Nodup ∧
    (∀ position : Fin (signing key md).length,
      ∀ child ∈ ((signing key md)[position]).children (vp192).valid,
        child = .secretSeed ∨ ∃ earlier ∈ (signing key md).take position,
          child = .structural earlier) ∧
    (∀ tree, StructuralNode.forsPrf key (selected md tree) ∈ signing key md) ∧
    (∀ tree height, authentication key (selected md tree) height ∈ signing key md) :=
  complete_schedule (vp192).valid key md

/-- An underfilled 128s buffer retains the actual unshifted one-byte value. -/
theorem shake128s_short_digest :
    (selected (p := (vp128).params) [0x80] ⟨0, by decide⟩).val = 128 := by decide

/-- Two bytes supply the complete first twelve-bit 128s digit. -/
theorem shake128s_complete_digit :
    (selected (p := (vp128).params) [0x80, 0x10] ⟨0, by decide⟩).val = 2049 := by decide

/-- The 192f eight-bit digit uses the same actual parser at its different width. -/
theorem shake192f_short_digest :
    (selected (p := (vp192).params) [0x80] ⟨0, by decide⟩).val = 128 := by decide

/-- Empty-message fallback retains the global offset of the second actual 192f FORS tree. -/
theorem shake192f_second_tree :
    (selected (p := (vp192).params) [] ⟨1, by decide⟩).val = 256 := by decide

end SLHDSA.Refactor.ForsScheduleTest
