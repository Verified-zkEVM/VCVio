/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.WeightedTrace
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Interaction

/-! # Extracting signing coefficients from heterogeneous traces

Hash and signing replies share chronological coefficient positions. Filtering the signing
occurrences therefore filters the coefficients in lockstep, rather than reindexing the
original vector by the signing-query count.
-/

public section

open GroupModel.Interaction

namespace GroupModel.LinearFunctional

/-- Select the explanation coefficients at signing-reply positions, padding absent entries
with zero in the same way as chronological evaluation. -/
@[expose] def signingCoefficients {F I M : Type} [Zero F] : List F → List (I ⊕ M) → List F
  | _, [] => []
  | coeff, .inl _ :: rest => signingCoefficients coeff.tail rest
  | coeff, .inr _ :: rest => coeff.headD 0 :: signingCoefficients coeff.tail rest

/-- The selected coefficients have exactly one entry per signing occurrence. -/
@[simp] theorem signingCoefficients_length {F I M : Type} [Zero F]
    (coeff : List F) (tr : List (I ⊕ M)) :
    (signingCoefficients coeff tr).length = (weightedSignedMessages tr).length := by
  induction tr generalizing coeff with
  | nil => rfl
  | cons q rest ih =>
    cases q <;> simp [signingCoefficients, weightedSignedMessages, List.filterMap_cons, ih]

/-- Zeroing hash-reply positions is exactly evaluation against the filtered signing list
and its corresponding coefficient vector. -/
theorem evaluate_signingCoefficients {F I M V : Type} [Semiring F]
    [AddCommMonoid V] [Module F V] (w : M → V) (coeff : List F) (tr : List (I ⊕ M)) :
    evaluate coeff (tr.map (Sum.elim (fun _ => 0) w)) =
      evaluate (signingCoefficients coeff tr) ((weightedSignedMessages tr).map w) := by
  induction tr generalizing coeff with
  | nil => simp [weightedSignedMessages, evaluate, signingCoefficients]
  | cons q rest ih =>
    cases q <;>
      simp [weightedSignedMessages, signingCoefficients, evaluate_cons, List.filterMap_cons, ih]

end GroupModel.LinearFunctional
