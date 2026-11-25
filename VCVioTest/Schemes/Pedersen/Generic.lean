/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.Pedersen.Generic
public import Mathlib.Algebra.Field.ZMod

/-!
# Concrete generic Pedersen binders

The public bound specializes to `37/5` and `37/101` for zero-operation binders.
An invalid-handle regression checks that verification does not reinterpret a missing
commitment as one of its newly appended entries.
-/

public section

open OracleComp OracleSpec CommitmentScheme GroupModel
open scoped ENNReal

namespace pedersenCommit

/-- The zero-operation binder returning the challenge handle has binding advantage at most
`37/5` over the field with five elements. -/
theorem binding_generic_zmod_five :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let A : OracleComp (genSpec (ZMod 5) groupSig) (Handle × ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5) :=
      pure (1, 0, 0, 1, 0)
    bindingAdvantage (pedersenCommit (1 : ZMod 5)) (BindingAdversary.ofGeneric 1 A) ≤
      (37 / 5 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  dsimp only
  have hg : Function.Bijective (· • (1 : ZMod 5) : ZMod 5 → ZMod 5) := by
    simpa only [smul_eq_mul, mul_one, Function.id_def] using Function.bijective_id
  apply (bindingAdvantage_ofGeneric_le hg
    (pure (1, 0, 0, 1, 0)) 0 (isQueryBoundP_pure _ _ _)).trans
  norm_num [ZMod.card, Nat.choose]

/-- Over the field with 101 elements the zero-operation binder has advantage at most
`37/101`, a bound strictly below one. -/
theorem binding_generic_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    let A : OracleComp (genSpec (ZMod 101) groupSig)
        (Handle × ZMod 101 × ZMod 101 × ZMod 101 × ZMod 101) := pure (1, 0, 0, 1, 0)
    bindingAdvantage (pedersenCommit (1 : ZMod 101)) (BindingAdversary.ofGeneric 1 A) ≤
      (37 / 101 : ℝ≥0∞) ∧ (37 / 101 : ℝ≥0∞) < 1 := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  dsimp only
  constructor
  · have hg : Function.Bijective (· • (1 : ZMod 101) : ZMod 101 → ZMod 101) := by
      simpa only [smul_eq_mul, mul_one, Function.id_def] using Function.bijective_id
    apply (bindingAdvantage_ofGeneric_le hg
      (pure (1, 0, 0, 1, 0)) 0 (isQueryBoundP_pure _ _ _)).trans
    norm_num [ZMod.card, Nat.choose]
  · rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num

/-- An initially invalid commitment handle keeps its zero value even when the first
verification query appends a nonzero entry at precisely that handle. -/
theorem dlogOfGeneric_invalid_handle :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let A : OracleComp (genSpec (ZMod 5) groupSig) (Handle × ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5) :=
      pure (2, 0, 1, 1, 0)
    DLogAdversary.ofGeneric (dlogOfGeneric A) (1 : ZMod 5) 1 = pure 0 := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  dsimp only
  rw [← dlogReduction_ofGeneric_eq]
  simp [dlogReduction, BindingAdversary.ofGeneric, runGen, run, lookup]

end pedersenCommit
