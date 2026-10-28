/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.Proximity.Reductions
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Extraction

/-! # Proximity's fresh linear-collision event

The collision event compares the target vector with the linear combination of all signing
reply vectors, using their actual chronological explanation coefficients. Freshness is on the
full vector and slot. The event does not require verification and is not a rejection rule.
It differs from a collision between random-oracle outputs: an adversary can deliberately
choose such a linear relation. Noncollision supplies a nonzero weighted verification gap.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace Proximity

/-- The coefficient of an optional-coordinate base in a message's hash. -/
@[expose] def coordinateWeight {F Slot : Type} [Zero F] [One F] [DecidableEq Slot]
    {dimension : ℕ} (i : Index Slot dimension) (msg : Message F Slot dimension) : F :=
  if i.2 = msg.2 then (match i.1 with | none => 1 | some k => msg.1 k) else 0

/-- A finite-slot sum evaluates precisely the direct weighted list of bases. -/
theorem value_terms_eq_sum {F Slot V : Type} [Semiring F] [Fintype Slot] [DecidableEq Slot]
    [AddCommMonoid V] [Module F V] {dimension : ℕ}
    (table : Index Slot dimension → V) (msg : Message F Slot dimension) :
    Weighted.value table (terms msg) = ∑ i, coordinateWeight i msg • table i := by
  simp [Weighted.value, terms, coordinateWeight, List.map_ofFn, List.sum_ofFn,
    Fintype.sum_prod_type, Fintype.sum_option]

/-- Summing a coordinate's verification gaps over all slots recovers the vector discrepancy. -/
theorem sum_coordinate_gap {F Slot Q : Type} [CommRing F] [Fintype Slot] [DecidableEq Slot]
    [Fintype Q] {dimension : ℕ} (msg : Message F Slot dimension)
    (signed : Q → Message F Slot dimension) (coeff : Q → F) (k : Fin dimension) :
    ∑ slot, gapCoeff coordinateWeight msg signed coeff (some k, slot) =
      msg.1 k - ∑ q, coeff q * (signed q).1 k := by
  simp only [gapCoeff, coordinateWeight]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  simp

/-- A target vector outside the represented signing combination has a nonzero base gap. -/
theorem exists_gap_ne_zero {F Slot Q : Type} [CommRing F] [Finite Slot] [DecidableEq Slot]
    [Fintype Q] {dimension : ℕ} (msg : Message F Slot dimension)
    (signed : Q → Message F Slot dimension) (coeff : Q → F)
    (hnc : msg.1 ≠ fun k => ∑ q, coeff q * (signed q).1 k) :
    ∃ i, gapCoeff coordinateWeight msg signed coeff i ≠ 0 := by
  let := Fintype.ofFinite Slot
  by_contra h
  push Not at h
  apply hnc
  funext k
  have heq := sum_coordinate_gap msg signed coeff k
  simp only [h, Finset.sum_const_zero] at heq
  exact sub_eq_zero.mp heq.symm

namespace AGM

/-- The vector represented by the signing-reply coefficients. The generator and hash replies
contribute zero; the coefficient at every signing occurrence stays in its original position. -/
@[expose] def signingVector {F Slot : Type} [Semiring F] {dimension : ℕ}
    (coeff : List F)
    (tr : Weighted.Transcript (Index Slot dimension) (Proximity.Message F Slot dimension)) :
    Fin dimension → F :=
  evaluate coeff ([0] ++ tr.map (Sum.elim (fun _ => 0) (fun m => m.1)))

/-- A fresh vector-slot pair whose vector is the represented combination of signing replies. -/
@[expose] def FreshCollision {F Slot G₁ G₂ : Type} [Semiring F] {dimension : ℕ}
    (out : Explained F (Proximity.Message F Slot dimension) (Group G₁ G₂))
    (tr : Weighted.Transcript (Index Slot dimension) (Proximity.Message F Slot dimension)) : Prop :=
  out.value.data ∉ weightedSignedMessages tr ∧
    out.value.data.1 = signingVector (coefficients out) tr

/-- With no signing or hash replies the represented signing vector is zero. -/
@[simp] theorem signingVector_nil {F Slot : Type} [Semiring F] {dimension : ℕ}
    (coeff : List F) : signingVector (Slot := Slot) (dimension := dimension) coeff [] = 0 := by
  simp [signingVector, evaluate, List.mapIdx_cons]

end AGM

/-- Observe the source fresh-collision event under the direct scheme's shared lazy oracle.
The signing coefficient at each reply occurrence is obtained from the certified final output. -/
noncomputable def freshCollisionExperiment {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ}
    [Field F] [SampleableType F] [DecidableEq Slot]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂) : ProbComp Bool := by
  classical
  exact (simulateQ (Index Slot dimension →ₒ G₁).romImpl do
    let κ ← liftM ($ᵗ F)
    let (out, tr) ← (simulateQ (Weighted.oracle terms id (fun r : G₁ => κ • r))
      (A.rawMain (κ • g₂))).run []
    return decide (AGM.FreshCollision out tr)).run' ∅

end Proximity
