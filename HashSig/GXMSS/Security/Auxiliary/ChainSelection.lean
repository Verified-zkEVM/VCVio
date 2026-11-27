/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.Adversary
public import VCVio.CryptoFoundations.IncomparableEncoding.NonMaximum

/-!
# GXMSS chain position selectors

The finite selector retains positive chain positions and first-coordinate order. Conditional
nonmaximality belongs to the generic encoding interface; two-codeword positivity is derived there.
-/

public section
namespace GXMSS.Reductions
open IncomparableEncoding
variable {PP T X H M R : Type} {h w v : ℕ}

/-- The independently sampled epoch, chain and paper position used by the chain reduction. -/
abbrev Guess (h w v : ℕ) := Epoch h × Fin v × Fin (2 ^ w - 1)

/-- The actual finite chain guess space has one positive chain position fewer than `2 ^ w`. -/
theorem guess_cardinality (h w v : ℕ) :
    Fintype.card (Guess h w v) = 2 ^ h * v * (2 ^ w - 1) := by
  simp [Guess, Epoch, Fintype.card_prod, Nat.mul_assoc]

/-- The paper's looser coefficient bounds the exact size of the chain guess space. -/
theorem guess_cardinality_le_paper_coefficient (h w v : ℕ) :
    Fintype.card (Guess h w v) ≤ 2 ^ h * v * 2 ^ w := by
  rw [guess_cardinality]
  exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

private def guessedEpoch (guess : Guess h w v) : Epoch h := guess.1

private def guessedChain (guess : Guess h w v) : Fin v :=
  let coordinate := guess.2
  coordinate.1

private def guessedPosition (guess : Guess h w v) : Fin (2 ^ w - 1) :=
  let coordinate := guess.2
  coordinate.2

/-- Select the first emitted-word coordinate strictly below the maximum digit. -/
@[expose] def findNonMaximumCoordinate (word : Codeword v (2 ^ w)) : Option (Fin v) :=
  Fin.find? fun i => decide ((word i).val < 2 ^ w - 1)

/-- The selected coordinate has a legal final chain step after its digit. -/
theorem findNonMaximumCoordinate_sound (word : Codeword v (2 ^ w))
    {i : Fin v} (hi : findNonMaximumCoordinate word = some i) :
    (word i).val < 2 ^ w - 1 :=
  of_decide_eq_true (Fin.eq_true_of_find?_eq_some hi)

/-- The admitted pointwise encoding premise supplies a coordinate for every returned word. -/
theorem findNonMaximumCoordinate_isSome
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w))
    (hnonmax : enc.NoMaximumOutput) (pp : PP) (msg : M) (randomizer : R)
    (ep : Epoch h) (word : Codeword v (2 ^ w))
    (hword : enc.value pp msg randomizer ep = some word) :
    (findNonMaximumCoordinate word).isSome := by
  obtain ⟨i, hi⟩ := hnonmax pp msg randomizer ep word hword
  exact Fin.isSome_find?_of_eq_true (i := i) (decide_eq_true hi)

end GXMSS.Reductions
