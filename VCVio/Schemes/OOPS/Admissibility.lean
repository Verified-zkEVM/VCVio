/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.OOPS.AGM.Adversary
public import VCVio.Schemes.OOPS.Weights

/-! # Target-topic degree admissibility for OOPS

Only distinct signed scalar messages on the final forgery's topic count toward the degree.
Repeated signatures and signatures on other topics do not consume this allowance. The
adversary predicate constrains the signing transcript of the existing signature game under
its random-oracle runtime; it introduces no separate EUF-CMA experiment.
-/

public section

open OracleComp OracleSpec

namespace OOPS

/-- At most `degree` distinct signed scalar messages lie on the final forgery's topic. -/
@[expose] def admissible {F T : Type} [DecidableEq F] [DecidableEq T]
    (degree : ℕ) (mt : F × T) (signed : List (F × T)) : Prop :=
  ((signed.filter fun q => q.2 = mt.2).map Prod.fst).toFinset.card ≤ degree

/-- The degree rule is decidable from the signed messages and the final topic. -/
instance {F T : Type} [DecidableEq F] [DecidableEq T]
    (degree : ℕ) (mt : F × T) (signed : List (F × T)) :
    Decidable (admissible degree mt signed) := by unfold admissible; infer_instance

/-- Indexed transcripts and the list-based degree rule count the same target messages. -/
theorem admissible_ofFn_iff {F T : Type} [DecidableEq F] [DecidableEq T]
    (degree : ℕ) {Q : ℕ} (v : Fin Q → F × T) (mt : F × T) :
    admissible degree mt (List.ofFn v) ↔ (targetMessages v mt.2).card ≤ degree := by
  rw [targetMessages_eq_ofFn]
  rfl

/-- The actual signing list yields a nonzero target coordinate for every explanation vector
when the final message is fresh and obeys the target-topic degree rule. -/
theorem exists_gapCoeff_ne_zero_of_admissible {F T : Type}
    [Field F] [DecidableEq F] [DecidableEq T] {degree : ℕ}
    (signed : List (F × T)) (mt : F × T) (coeff : Fin signed.length → F)
    (hdegree : admissible degree mt signed) (hfresh : mt ∉ signed) :
    ∃ j : Fin (degree + 1),
      GroupModel.LinearFunctional.gapCoeff (weight degree) mt signed.get coeff (mt.2, j) ≠ 0 := by
  apply exists_gapCoeff_ne_zero
  · simpa only [targetMessages_eq_ofFn, List.ofFn_get, admissible] using hdegree
  · intro q h
    exact hfresh (h ▸ List.get_mem signed q)

/-- Degree admissibility on every possible random-oracle execution of the ordinary signing
stage. The public key is generated from the same scalar used by the signing oracle. -/
@[expose] def AlgebraicAdversary.Admissible {F T G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [DecidableEq F] [DecidableEq T]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} {degree : ℕ}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂ degree) : Prop :=
  ∀ x z, z ∈ support ((simulateQ ((T × Fin (degree + 1)) →ₒ G₁).romImpl
    ((scheme e g₂ degree).runWithSigningOracle (x • g₂) x
      (A.toUnforgeableAdversary.main (x • g₂)))).run' ∅) →
    admissible degree z.1.1 (z.2.map fun q => q.1)

end OOPS
