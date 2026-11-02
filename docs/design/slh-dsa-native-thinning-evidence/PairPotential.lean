/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import PairHeader
import all NativePotential

/-! # Native pair-watch step accounting -/

public section
open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal
namespace SLHDSA.Security.Coverage.NativeThin2
open NativeThin1
variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-- An assigned live watch whose fresh deterministic nonce cell is the current query. -/
def ActiveCandidate (pk : PublicKeyCore core) (kappa : PublicKeyCore core → core.Y)
    (s : RoleState core) (index : Nat) (t : (roleSpec core).Domain) : Prop :=
  ∃ R M,
    s.2.1.cls (hmsgPoint core pk R M) = some TapeClass.forger ∧
    s.2.1.pos (hmsgPoint core pk R M) = some index ∧
    ¬Fired core pk s index ∧ s.1.1 (.inr (.inr (kappa pk, M))) = none ∧
    (t = .inr (.inl (.inr (.inr (kappa pk, M)))) ∨ t = nonceQuery core pk kappa M)

/-- The two native slot watches share their actual-key product potential. -/
noncomputable def productPotential (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j)) (first second : Nat)
    (s : RoleState core) : ℝ≥0∞ :=
  potential core pk kappa L first s * potential core pk kappa L second s

variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.Y]
  [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]
  {t : (roleSpec core).Domain} {s : RoleState core}
  {y : (roleSpec core).Range t × RoleState core}

/-- Outside its active fresh nonce query a watch cannot increase pointwise. -/
theorem potential_after_not_active_le (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j)) (index : Nat)
    (good : GoodQuery core pk kappa t)
    (inactive : ¬ActiveCandidate core pk kappa s index t)
    (hy : y ∈ support ((roleRunImpl core t).run s)) :
    potential core pk kappa L index y.2 ≤ potential core pk kappa L index s := by
  classical
  by_cases hs : AnswerTape.HitInv (tapeClass core) L s
  swap
  · have eq : potential core pk kappa L index s = ⊤ := by
      simp only [potential, hs, ↓reduceIte]
    rw [eq]
    exact le_top
  have after := AnswerTape.hitInv_of_mem_support_classPosImplFwd_run
    (IsRandPoint core) (randRel core) (tapeClass core) (range_eq_tapeClassRange core) hs hy
  by_cases fired : Fired core pk s index
  · have fire := fired_persists core pk L hs hy fired
    simp only [potential, hs, after, fired, fire, ↓reduceIte, le_refl]
  by_cases slot : ActualSlot core pk s index
  swap
  · have eq : potential core pk kappa L index s = (Nat.card core.Y : ℝ≥0∞)⁻¹ := by
      simp only [potential, hs, fired, slot, ↓reduceIte, not_false_eq_true, true_or]
    rw [eq]
    exact potential_after_unassigned_le core pk kappa L hs hy index slot
  obtain ⟨R, M, hc, hp⟩ := slot
  by_cases fresh : s.1.1 (.inr (.inr (kappa pk, M))) = none
  · have live : Live core pk kappa s index := ⟨R, M, hc, hp, fresh⟩
    have nofire : ¬Fired core pk y.2 index := by
      intro post
      exact inactive ⟨R, M, hc, hp, fired, fresh,
        fired_requires_nonce core pk kappa L hs hy index R M hc hp fired good post⟩
    have eq : potential core pk kappa L index s = (Nat.card core.Y : ℝ≥0∞)⁻¹ := by
      simp only [potential, hs, fired, live, ↓reduceIte, or_true]
    rw [eq]
    simp only [potential, after, nofire, ↓reduceIte]
    split_ifs <;> simp
  · have notLive := not_live_of_cached core pk kappa L hs index R M hc hp fresh
    have eq : potential core pk kappa L index s = 0 := by
      have slot : ActualSlot core pk s index := ⟨R, M, hc, hp⟩
      simp only [potential, hs, fired, slot, notLive, ↓reduceIte, not_true_eq_false, or_self]
    rw [eq, potential_after_cached_eq_zero core pk kappa L hs hy index R M hc hp
      fresh fired good]

/-- Distinct actual-key slots sharing a fresh nonce query have disjoint firing outcomes. -/
theorem shared_fresh_candidate_zero (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j))
    (hs : AnswerTape.HitInv (tapeClass core) L s)
    (first second : Nat) (hne : first ≠ second) (leftR rightR : core.Y) (M : List Byte)
    (leftClass : s.2.1.cls (hmsgPoint core pk leftR M) = some TapeClass.forger)
    (leftPos : s.2.1.pos (hmsgPoint core pk leftR M) = some first)
    (rightClass : s.2.1.cls (hmsgPoint core pk rightR M) = some TapeClass.forger)
    (rightPos : s.2.1.pos (hmsgPoint core pk rightR M) = some second)
    (fresh : s.1.1 (.inr (.inr (kappa pk, M))) = none)
    (leftNotFired : ¬Fired core pk s first) (rightNotFired : ¬Fired core pk s second)
    (z : core.Y × RoleState core)
    (hz : z ∈ support ((roleRunImpl core (nonceQuery core pk kappa M)).run s)) :
    productPotential core pk kappa L first second z.2 = 0 := by
  classical
  have different : leftR ≠ rightR := by
    rintro rfl
    exact hne (Option.some.inj (leftPos.symm.trans rightPos))
  have leftBound := fresh_candidate_pointwise core pk kappa L hs first leftR M
    leftClass leftPos fresh leftNotFired z hz
  have rightBound := fresh_candidate_pointwise core pk kappa L hs second rightR M
    rightClass rightPos fresh rightNotFired z hz
  apply le_zero_iff.mp
  change potential core pk kappa L first z.2 * potential core pk kappa L second z.2 ≤ 0
  have bound := mul_le_mul' leftBound rightBound
  have zero : ({leftR} : Set core.Y).indicator (fun _ => (1 : ℝ≥0∞)) z.1 *
      ({rightR} : Set core.Y).indicator (fun _ => (1 : ℝ≥0∞)) z.1 = 0 := by
    by_cases h : z.1 = leftR
    · simp [h, different]
    · simp [h]
  exact bound.trans_eq zero

/-- A pointwise nonactive factor can be taken outside the other watch's expected step. -/
theorem product_step_of_not_active (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j)) (hL : L .other = [])
    (first second : Nat) (t : (roleSpec core).Domain) (s : RoleState core)
    (good : GoodQuery core pk kappa t)
    (inactive : ¬ActiveCandidate core pk kappa s first t) :
    ∫⁻ r, r ∂𝒟[(fun z => productPotential core pk kappa L first second z.2) <$>
      ((roleRunImpl core t).run s)] ≤ productPotential core pk kappa L first second s := by
  let _ : MeasurableSpace ((roleSpec core).Range t × RoleState core) := ⊤
  calc
    _ ≤ ∫⁻ r, r ∂𝒟[(fun z => potential core pk kappa L first s *
        potential core pk kappa L second z.2) <$> ((roleRunImpl core t).run s)] :=
      by
        rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map]
        apply lintegral_mono_ae
        exact evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete fun z hz =>
          mul_le_mul' (potential_after_not_active_le core pk kappa L first good inactive hz) le_rfl
    _ = potential core pk kappa L first s *
        (∫⁻ r, r ∂𝒟[(fun z => potential core pk kappa L second z.2) <$>
          ((roleRunImpl core t).run s)]) := by
      rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map,
        lintegral_const_mul _ Measurable.of_discrete]
    _ ≤ productPotential core pk kappa L first second s :=
      mul_le_mul' le_rfl (potential_step core pk kappa L hL second t good s)

/-- The product watch is a native supermartingale at distinct actual-key slots. -/
theorem product_potential_step (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j)) (hL : L .other = [])
    (first second : Nat) (hne : first ≠ second)
    (t : (roleSpec core).Domain) (good : GoodQuery core pk kappa t) (s : RoleState core) :
    ∫⁻ r, r ∂𝒟[(fun z => productPotential core pk kappa L first second z.2) <$>
      ((roleRunImpl core t).run s)] ≤ productPotential core pk kappa L first second s := by
  classical
  by_cases hs : AnswerTape.HitInv (tapeClass core) L s
  swap
  · have eq : productPotential core pk kappa L first second s = ⊤ := by
      simp only [productPotential, potential, hs, ↓reduceIte, ENNReal.top_mul_top]
    rw [eq]
    exact le_top
  by_cases leftActive : ActiveCandidate core pk kappa s first t
  swap
  · exact product_step_of_not_active core pk kappa L hL first second t s good leftActive
  by_cases rightActive : ActiveCandidate core pk kappa s second t
  swap
  · simpa only [productPotential, mul_comm] using
      product_step_of_not_active core pk kappa L hL second first t s good rightActive
  obtain ⟨leftR, leftM, leftClass, leftPos, leftNotFired, fresh, leftQuery⟩ := leftActive
  obtain ⟨rightR, rightM, rightClass, rightPos, rightNotFired, _, rightQuery⟩ := rightActive
  have sameMessage : leftM = rightM := by
    rcases leftQuery with leftQuery | leftQuery <;>
      rcases rightQuery with rightQuery | rightQuery
    · exact (Prod.mk.inj (Sum.inr.inj (Sum.inr.inj
        (Sum.inl.inj (Sum.inr.inj (leftQuery.symm.trans rightQuery)))))).2
    · cases leftQuery.symm.trans rightQuery
    · cases leftQuery.symm.trans rightQuery
    · exact (Prod.mk.inj (Sum.inr.inj (Sum.inr.inj
        (Sum.inr.inj (Sum.inr.inj (leftQuery.symm.trans rightQuery)))))).2
  subst rightM
  have zeroStep : ∫⁻ r, r ∂𝒟[(fun z => productPotential core pk kappa L first second z.2) <$>
      ((roleRunImpl core (nonceQuery core pk kappa leftM)).run s)] ≤ 0 :=
    lintegral_id_evalDist_map_le_of_le_of_mem_support _ fun z hz =>
      (shared_fresh_candidate_zero core pk kappa L hs first second hne leftR rightR leftM
        leftClass leftPos rightClass rightPos fresh leftNotFired rightNotFired z hz).le
  rcases leftQuery with rfl | rfl
  · rw [nonce_role_copies core pk kappa leftM]
    exact zeroStep.trans zero_le
  · exact zeroStep.trans zero_le

end SLHDSA.Security.Coverage.NativeThin2
#print axioms SLHDSA.Security.Coverage.NativeThin2.potential_after_not_active_le
#print axioms SLHDSA.Security.Coverage.NativeThin2.shared_fresh_candidate_zero

#print axioms SLHDSA.Security.Coverage.NativeThin2.product_step_of_not_active
#print axioms SLHDSA.Security.Coverage.NativeThin2.product_potential_step
