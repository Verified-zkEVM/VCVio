/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import PairPotential
import all PairPotential
import all NativePotential

/-! # Native pair-watch composition and terminal credit -/

public section
open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal
namespace SLHDSA.Security.Coverage.NativeThin2
open NativeThin1
variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-- Terminal credit for both hits and for an unreached first position. -/
noncomputable def pairTerminalValue (pk : PublicKeyCore core) (first second : Nat)
    (s : RoleState core) : ℝ≥0∞ := by
  classical
  exact (if Fired core pk s first ∧ Fired core pk s second then (1 : ℝ≥0∞) else 0) +
    (if ¬first < s.2.1.cnt TapeClass.forger then ((Nat.card core.Y : ℝ≥0∞)⁻¹)^2 else 0)

/-- The product watch pays for simultaneous hits and unused first-position credit. -/
theorem pair_terminal_credit (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j))
    (first second : Nat) (horder : first < second) (s : RoleState core) :
    pairTerminalValue core pk first second s ≤
      productPotential core pk kappa L first second s := by
  classical
  by_cases hs : AnswerTape.HitInv (tapeClass core) L s
  swap
  · simp only [productPotential, potential, hs, ↓reduceIte, ENNReal.top_mul_top, le_top]
  by_cases both : Fired core pk s first ∧ Fired core pk s second
  · have reach := fired_reached core pk L hs both.1
    simp [pairTerminalValue, productPotential, potential, hs, both.1, both.2, reach]
  by_cases reach : first < s.2.1.cnt TapeClass.forger
  · simp only [pairTerminalValue, both, reach, not_true_eq_false, ↓reduceIte, zero_add]
    exact zero_le
  · have noFirst : ¬ActualSlot core pk s first := fun slot =>
      reach (actualSlot_reached core pk L hs slot)
    have noSecond : ¬ActualSlot core pk s second := fun slot =>
      reach (horder.trans (actualSlot_reached core pk L hs slot))
    have notFirstFired : ¬Fired core pk s first := by
      rintro ⟨R, M, hc, hp, _⟩
      exact noFirst ⟨R, M, hc, hp⟩
    have notSecondFired : ¬Fired core pk s second := by
      rintro ⟨R, M, hc, hp, _⟩
      exact noSecond ⟨R, M, hc, hp⟩
    simp [pairTerminalValue, reach, productPotential, potential, hs, notFirstFired,
      notSecondFired, noFirst, noSecond, pow_two]

variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.Y]
  [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-- Zero disallowed-query budget composes the product potential through a program. -/
theorem product_potential_run (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j)) (hL : L .other = [])
    (first second : Nat) (hne : first ≠ second) {α : Type} (program : OracleComp (roleSpec core) α)
    (allowed : program.AllQueriesSatisfy (GoodQuery core pk kappa))
    (s : RoleState core) :
    ∫⁻ r, r ∂𝒟[(fun y => productPotential core pk kappa L first second y.2) <$>
      ((simulateQ (roleRunImpl core) program).run s)] ≤
        productPotential core pk kappa L first second s := by
  classical
  have bound := (isQueryBoundP_zero_iff program (GoodQuery core pk kappa)).mpr allowed
  let credit : Nat → RoleState core → ℝ≥0∞ :=
    fun n state => if n = 0 then productPotential core pk kappa L first second state else ⊤
  have monotone : ∀ state, Monotone fun n => credit n state := by
    intro state a b hab
    by_cases hb : b = 0
    · have ha : a = 0 := Nat.eq_zero_of_le_zero (hb ▸ hab)
      simp only [credit, ha, hb, ↓reduceIte, le_refl]
    · simp only [credit, hb, ↓reduceIte]
      exact le_top
  have step : ∀ t state n,
      ∫⁻ r, r ∂𝒟[(fun z => credit n z.2) <$> ((roleRunImpl core t).run state)] ≤
        credit (n + if ¬GoodQuery core pk kappa t then 1 else 0) state := by
    intro t state n
    by_cases hn : n = 0
    · subst n
      by_cases hg : GoodQuery core pk kappa t
      · simpa only [credit, hg, not_true_eq_false, ↓reduceIte, Nat.add_zero] using
          product_potential_step core pk kappa L hL first second hne t hg state
      · simp only [credit, hg, not_false_eq_true, ↓reduceIte, Nat.zero_add, Nat.one_ne_zero]
        exact le_top
    · have positive : n + (if ¬GoodQuery core pk kappa t then 1 else 0) ≠ 0 := by omega
      simp only [credit, positive, ↓reduceIte]
      exact le_top
  simpa only [credit, ↓reduceIte] using
    (lintegral_run_le_of_isQueryBoundP (roleRunImpl core)
      (fun t => ¬GoodQuery core pk kappa t) credit monotone step program 0 bound s)

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

/-- The original native role experiment has expected product credit at most epsilon squared. -/
theorem whole_product_potential (kappa : PublicKeyCore core → core.Y)
    (pkSeed : core.PkSeed) (e : core.SkSeed ≃ core.Y)
    (adv : UnforgeableAdversary
      (romScheme core e (fun pk => pure (kappa pk)) (pure pkSeed)))
    (L : (j : TapeClass) → List (tapeClassRange core j)) (hL : L .other = [])
    (first second : Nat) (hne : first ≠ second) :
    ∫⁻ r, r ∂𝒟[(fun z => productPotential core z.1.pk kappa L first second z.2) <$>
      roleRun core adv pkSeed L] ≤ ((Nat.card core.Y : ℝ≥0∞)⁻¹)^2 := by
  classical
  change ∫⁻ r, r ∂𝒟[(fun z => productPotential core z.1.pk kappa L first second z.2) <$>
    ((simulateQ (roleRunImpl core) (roleExperiment core adv pkSeed)).run
      ((∅, L), (AnswerTape.ClassPos.init, ∅)))] ≤ _
  rw [roleExperiment_eq_prefix_suffix core kappa pkSeed e adv, simulateQ_bind,
    StateT.run_bind, lintegral_id_evalDist_map_bind]
  apply lintegral_id_evalDist_map_le_of_le_of_mem_support
  intro z hz
  have leftInit := prefix_potential core kappa pkSeed L first z hz
  have rightInit := prefix_potential core kappa pkSeed L second z hz
  have init : productPotential core z.1.1 kappa L first second z.2 =
      ((Nat.card core.Y : ℝ≥0∞)⁻¹)^2 := by
    rw [productPotential, leftInit, rightInit, pow_two]
  have bound := product_potential_run core z.1.1 kappa L hL first second hne
    (suffix core kappa pkSeed e adv z.1.1 z.1.2)
    (allowed_suffix core kappa pkSeed e adv z.1.1 z.1.2) z.2
  rw [init] at bound
  convert bound using 1
  let _ : MeasurableSpace (DeriveOutcome core × RoleState core) := ⊤
  rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map]
  apply lintegral_congr_ae
  exact evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete fun y hy => by
    dsimp only
    rw [suffix_run_pk core kappa pkSeed e adv z.1.1 z.1.2 z.2 y hy]

end SLHDSA.Security.Coverage.NativeThin2
#print axioms SLHDSA.Security.Coverage.NativeThin2.pair_terminal_credit
#print axioms SLHDSA.Security.Coverage.NativeThin2.product_potential_run
#print axioms SLHDSA.Security.Coverage.NativeThin2.whole_product_potential
