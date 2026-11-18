/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.Programming

/-!
# Joint programmed-table coupling for the pointer-chain puzzle

A rank-ordered permutation moves a uniform raw oracle into a table programmed with independent
full path responses. Distinct path inputs make honest generation recover the corresponding
projected labels. The probability of a collision among those inputs is charged once.
The bounded observer retains the completed raw oracle, public puzzle and hidden key together.
All raw tails and outside-image oracle values remain available to its quantum continuation.

The programmed experiment averages unconditionally over its path responses. In particular,
its future labels are not conditioned on the absence of a collision.
-/

public section

open OracleSpec OracleComp Quantum MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PointerChainPuzzle.LeanSeal

variable {b n m B : ℕ} [NeZero n]

/-- Two distinct path values have the same typed oracle input. -/
@[expose]
def PathInputCollision (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (l : Labels n m (Bytes 32) (Bytes b)) : Prop :=
  ∃ v w : PathValue n m, v ≠ w ∧
    pathInput m (ctx b n m) id (labelPuzzle salt x z l) l v =
      pathInput m (ctx b n m) id (labelPuzzle salt x z l) l w

/-- Distinct typed path inputs remain distinct in the complete raw byte window. -/
theorem rawPathInput_injective_of_not_collision (hb : b ≤ 32) (hn : n < 2 ^ 32)
    (hB : hashInputBound b ≤ B) (salt : Bytes 16) (x : Bytes b)
    (z : Fin (n - 1) → Bytes b) (W : PathValue n m → Bytes 32)
    (hgood : ¬ PathInputCollision salt x z (pathLabels hb W)) :
    Function.Injective (fun v ↦ rawPathInput hb hB salt x z v W) := by
  intro v w he
  by_contra hvw
  exact hgood ⟨v, w, hvw, hashInputWindow_injective hB hn he⟩

/-- The honest source output for a first link and independently supplied masked links.
The remaining links are recovered through the source's bijective link map. -/
@[expose]
def maskedPathOutput (H : ByteArray.Bounded B → Bytes 32)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b) : Puzzle b n × Bytes 32 :=
  let O := oracles (b := b) (n := n) (extendWindowOracle H)
  let xs := (linkEquiv m (ctx b n m) O salt).symm (x, z)
  (honestPuzzle m (ctx b n m) id O salt xs, honestKey m (ctx b n m) id O salt xs)

/-- With distinct programmed inputs, the real masked-link generator returns the prescribed
public puzzle and hidden key. -/
theorem maskedPathOutput_programPath_of_injective (hb : b ≤ 32)
    (hB : hashInputBound b ≤ B) (salt : Bytes 16) (x : Bytes b)
    (z : Fin (n - 1) → Bytes b) (H : ByteArray.Bounded B → Bytes 32)
    (W : PathValue n m → Bytes 32)
    (hinj : Function.Injective (fun v ↦ rawPathInput hb hB salt x z v W)) :
    maskedPathOutput (m := m) (programPath hb hB salt x z H W) salt x z =
      (labelPuzzle salt x z (pathLabels hb W), (pathLabels hb W) .key) := by
  have ha := simulateQ_genMaskedWith
    (m := m) (mkCtx := ctx b n m) (initAcc := id)
    (oracles (b := b) (n := n) (extendWindowOracle (programPath hb hB salt x z H W)))
    salt (x, z)
  have hp := simulateQ_genMaskedWith_programPath_of_injective hb hB salt x z H W hinj
  exact (OracleComp.pure_inj _ _).mp (ha.symm.trans hp)

section LinkCoordinates

variable [MeasurableSpace (Bytes b)] [MeasurableSingletonClass (Bytes b)]

/-- For one fixed complete oracle and salt, uniform source links can be replaced by uniform
first and masked links inside any joint nonnegative observer. -/
theorem lintegral_honestOutput_eq_maskedPathOutput
    (H : ByteArray.Bounded B → Bytes 32) (salt : Bytes 16)
    (F : (ByteArray.Bounded B → Bytes 32) → Puzzle b n → Bytes 32 → ENNReal) :
    (∫⁻ xs : Fin n → Bytes b,
      F H (honestPuzzle m (ctx b n m) id (oracles (extendWindowOracle H)) salt xs)
        (honestKey m (ctx b n m) id (oracles (extendWindowOracle H)) salt xs)
      ∂(uniformOn Set.univ : Measure (Fin n → Bytes b))) =
      ∫⁻ p : Bytes b × (Fin (n - 1) → Bytes b),
        F H (maskedPathOutput (m := m) H salt p.1 p.2).1
          (maskedPathOutput (m := m) H salt p.1 p.2).2
        ∂(uniformOn Set.univ : Measure (Bytes b × (Fin (n - 1) → Bytes b))) := by
  have he := congrArg (fun μ : Measure (Fin n → Bytes b) ↦
      ∫⁻ xs, F H
        (honestPuzzle m (ctx b n m) id (oracles (extendWindowOracle H)) salt xs)
        (honestKey m (ctx b n m) id (oracles (extendWindowOracle H)) salt xs) ∂μ)
    (uniformOn_univ_map_equiv
      (linkEquiv m (ctx b n m) (oracles (extendWindowOracle H)) salt).symm)
  rw [lintegral_map Measurable.of_discrete Measurable.of_discrete] at he
  exact he.symm

end LinkCoordinates

section Uniform

variable [MeasurableSpace (Bytes 32)] [MeasurableSingletonClass (Bytes 32)]

/-- The input-collision probability under independent full raw path responses is at most
`solvePoints² / |Bytes 32|`. Only their typed projections determine the path inputs. -/
theorem uniformOn_pathInputCollision_le (hb : b ≤ 32)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b) :
    (uniformOn Set.univ : Measure (PathValue n m → Bytes 32))
      {W | PathInputCollision salt x z (pathLabels hb W)} ≤
      (solvePoints n m : ENNReal) ^ 2 / Fintype.card (Bytes 32) := by
  classical
  let : MeasurableSpace (Labels n m (Bytes 32) (Bytes b)) := ⊤
  have he := congrArg (fun μ : Measure (Labels n m (Bytes 32) (Bytes b)) ↦
    μ {l | PathInputCollision salt x z l}) (uniformOn_univ_map_pathLabels (n := n) (m := m) hb)
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete] at he
  change (uniformOn Set.univ : Measure (PathValue n m → Bytes 32))
    {W | PathInputCollision salt x z (pathLabels hb W)} =
      (uniformOn Set.univ : Measure (Labels n m (Bytes 32) (Bytes b)))
        {l | PathInputCollision salt x z l} at he
  rw [he]
  have hc := prEvent_collision_le (S := Bytes 32) (L := Bytes b) (m := m)
    (mkCtx := ctx b n m) (initAcc := id) salt x z
  rwa [prEvent_eq_evalDist_of_discrete, SampleableType.evalDist_uniformSample] at hc

/-- Rank-ordered raw programming preserves the complete uniform oracle marginal.
No distinctness assumption is imposed on the programmed inputs. -/
theorem lintegral_uniform_programPath (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (f : (ByteArray.Bounded B → Bytes 32) → ENNReal) :
    (∫⁻ H, ∫⁻ W, f (programPath hb hB salt x z H W)
      ∂(uniformOn Set.univ : Measure (PathValue n m → Bytes 32))
      ∂(uniformOn Set.univ : Measure (ByteArray.Bounded B → Bytes 32))) =
      ∫⁻ H, f H ∂(uniformOn Set.univ : Measure (ByteArray.Bounded B → Bytes 32)) := by
  have he := congrArg (fun μ : Measure
      ((ByteArray.Bounded B → Bytes 32) × (PathValue n m → Bytes 32)) ↦
      ∫⁻ p, f p.1 ∂μ)
    (uniformOn_univ_map_equiv (pathProgrammingEquiv (m := m) hb hB salt x z).symm)
  rw [lintegral_map Measurable.of_discrete Measurable.of_discrete,
    uniformOn_univ_prod, lintegral_prod _ Measurable.of_discrete.aemeasurable,
    lintegral_prod _ Measurable.of_discrete.aemeasurable] at he
  simp_rw [pathProgrammingEquiv_symm_fst] at he
  simpa only [lintegral_const, measure_univ, mul_one] using he

/-- With fixed public salt and masked links, replace the actual oracle by the named programmed
raw table inside any bounded joint observer. The independent path responses remain unconditional;
the single additive allowance is the path-input collision probability. -/
theorem masked_le_programmed_add_collision (hb : b ≤ 32) (hn : n < 2 ^ 32)
    (hB : hashInputBound b ≤ B) (salt : Bytes 16) (x : Bytes b)
    (z : Fin (n - 1) → Bytes b)
    (F : (ByteArray.Bounded B → Bytes 32) → Puzzle b n → Bytes 32 → ENNReal)
    (hF : ∀ H P K, F H P K ≤ 1) :
    (∫⁻ H, F H (maskedPathOutput (m := m) H salt x z).1 (maskedPathOutput (m := m) H salt x z).2
      ∂(uniformOn Set.univ : Measure (ByteArray.Bounded B → Bytes 32))) ≤
      (∫⁻ H, ∫⁻ W,
        F (programPath hb hB salt x z H W) (labelPuzzle salt x z (pathLabels hb W))
          ((pathLabels hb W) .key)
        ∂(uniformOn Set.univ : Measure (PathValue n m → Bytes 32))
        ∂(uniformOn Set.univ : Measure (ByteArray.Bounded B → Bytes 32))) +
      (solvePoints n m : ENNReal) ^ 2 / Fintype.card (Bytes 32) := by
  classical
  have hinner (H : ByteArray.Bounded B → Bytes 32) :
      (∫⁻ W,
        F (programPath hb hB salt x z H W)
          (maskedPathOutput (m := m) (programPath hb hB salt x z H W) salt x z).1
          (maskedPathOutput (m := m) (programPath hb hB salt x z H W) salt x z).2
        ∂(uniformOn Set.univ : Measure (PathValue n m → Bytes 32))) ≤
      (∫⁻ W,
        F (programPath hb hB salt x z H W) (labelPuzzle salt x z (pathLabels hb W))
          ((pathLabels hb W) .key)
        ∂(uniformOn Set.univ : Measure (PathValue n m → Bytes 32))) +
      (solvePoints n m : ENNReal) ^ 2 / Fintype.card (Bytes 32) := by
    calc
      _ ≤ ∫⁻ W,
          F (programPath hb hB salt x z H W) (labelPuzzle salt x z (pathLabels hb W))
            ((pathLabels hb W) .key) +
            {U | PathInputCollision salt x z (pathLabels hb U)}.indicator 1 W
          ∂(uniformOn Set.univ : Measure (PathValue n m → Bytes 32)) := by
        apply lintegral_mono
        intro W
        dsimp only
        by_cases hc : PathInputCollision salt x z (pathLabels hb W)
        · simpa [hc] using (hF (programPath hb hB salt x z H W) _ _).trans
            (le_add_left le_rfl : (1 : ENNReal) ≤
              F (programPath hb hB salt x z H W) (labelPuzzle salt x z (pathLabels hb W))
                ((pathLabels hb W) .key) + 1)
        · rw [maskedPathOutput_programPath_of_injective hb hB salt x z H W
            (rawPathInput_injective_of_not_collision hb hn hB salt x z W hc)]
          simp [hc]
      _ = (∫⁻ W,
          F (programPath hb hB salt x z H W) (labelPuzzle salt x z (pathLabels hb W))
            ((pathLabels hb W) .key)
          ∂(uniformOn Set.univ : Measure (PathValue n m → Bytes 32))) +
            (uniformOn Set.univ : Measure (PathValue n m → Bytes 32))
              {W | PathInputCollision salt x z (pathLabels hb W)} := by
        rw [lintegral_add_left Measurable.of_discrete,
          lintegral_indicator_one MeasurableSet.of_discrete]
      _ ≤ _ := add_le_add le_rfl (uniformOn_pathInputCollision_le (m := m) hb salt x z)
  calc
    _ = ∫⁻ H, ∫⁻ W,
        F (programPath hb hB salt x z H W)
          (maskedPathOutput (m := m) (programPath hb hB salt x z H W) salt x z).1
          (maskedPathOutput (m := m) (programPath hb hB salt x z H W) salt x z).2
        ∂(uniformOn Set.univ : Measure (PathValue n m → Bytes 32))
        ∂(uniformOn Set.univ : Measure (ByteArray.Bounded B → Bytes 32)) :=
      (lintegral_uniform_programPath hb hB salt x z
        (fun H ↦ F H (maskedPathOutput (m := m) H salt x z).1
          (maskedPathOutput (m := m) H salt x z).2)).symm
    _ ≤ ∫⁻ H, (∫⁻ W,
        F (programPath hb hB salt x z H W) (labelPuzzle salt x z (pathLabels hb W))
          ((pathLabels hb W) .key)
        ∂(uniformOn Set.univ : Measure (PathValue n m → Bytes 32))) +
          (solvePoints n m : ENNReal) ^ 2 / Fintype.card (Bytes 32)
        ∂(uniformOn Set.univ : Measure (ByteArray.Bounded B → Bytes 32)) :=
      lintegral_mono hinner
    _ = _ := by
      rw [lintegral_add_left Measurable.of_discrete, lintegral_const, measure_univ, mul_one]

section Coins

variable [MeasurableSpace (Bytes b)] [MeasurableSingletonClass (Bytes b)]
  [MeasurableSpace (Bytes 16)] [MeasurableSingletonClass (Bytes 16)]

/-- Couple the real honest challenge with independent full raw path responses and the named
rank-programmed oracle. The observer sees the same completed oracle, puzzle and hidden key.
The additive collision allowance is charged once, after averaging all fresh challenge coins.
Neither side conditions on collision-freedom or assumes an adversary query budget. -/
theorem real_le_programmed_add_collision (hb : b ≤ 32) (hn : n < 2 ^ 32)
    (hB : hashInputBound b ≤ B)
    (F : (ByteArray.Bounded B → Bytes 32) → Puzzle b n → Bytes 32 → ENNReal)
    (hF : ∀ H P K, F H P K ≤ 1) :
    (∫⁻ H, ∫⁻ salt, ∫⁻ xs : Fin n → Bytes b,
      F H (honestPuzzle m (ctx b n m) id (oracles (extendWindowOracle H)) salt xs)
        (honestKey m (ctx b n m) id (oracles (extendWindowOracle H)) salt xs)
      ∂(uniformOn Set.univ : Measure (Fin n → Bytes b))
      ∂(uniformOn Set.univ : Measure (Bytes 16))
      ∂(uniformOn Set.univ : Measure (ByteArray.Bounded B → Bytes 32))) ≤
    (∫⁻ salt, ∫⁻ p : Bytes b × (Fin (n - 1) → Bytes b), ∫⁻ H, ∫⁻ W,
      F (programPath hb hB salt p.1 p.2 H W)
        (labelPuzzle salt p.1 p.2 (pathLabels hb W)) ((pathLabels hb W) .key)
      ∂(uniformOn Set.univ : Measure (PathValue n m → Bytes 32))
      ∂(uniformOn Set.univ : Measure (ByteArray.Bounded B → Bytes 32))
      ∂(uniformOn Set.univ : Measure (Bytes b × (Fin (n - 1) → Bytes b)))
      ∂(uniformOn Set.univ : Measure (Bytes 16))) +
        (solvePoints n m : ENNReal) ^ 2 / Fintype.card (Bytes 32) := by
  calc
    _ = ∫⁻ H, ∫⁻ salt, ∫⁻ p : Bytes b × (Fin (n - 1) → Bytes b),
        F H (maskedPathOutput (m := m) H salt p.1 p.2).1
          (maskedPathOutput (m := m) H salt p.1 p.2).2
        ∂(uniformOn Set.univ : Measure (Bytes b × (Fin (n - 1) → Bytes b)))
        ∂(uniformOn Set.univ : Measure (Bytes 16))
        ∂(uniformOn Set.univ : Measure (ByteArray.Bounded B → Bytes 32)) := by
      congr 1
      funext H
      congr 1
      funext salt
      exact lintegral_honestOutput_eq_maskedPathOutput H salt F
    _ = ∫⁻ salt, ∫⁻ p : Bytes b × (Fin (n - 1) → Bytes b), ∫⁻ H,
        F H (maskedPathOutput (m := m) H salt p.1 p.2).1
          (maskedPathOutput (m := m) H salt p.1 p.2).2
        ∂(uniformOn Set.univ : Measure (ByteArray.Bounded B → Bytes 32))
        ∂(uniformOn Set.univ : Measure (Bytes b × (Fin (n - 1) → Bytes b)))
        ∂(uniformOn Set.univ : Measure (Bytes 16)) := by
      rw [lintegral_lintegral_swap Measurable.of_discrete.aemeasurable]
      congr 1
      funext salt
      exact lintegral_lintegral_swap Measurable.of_discrete.aemeasurable
    _ ≤ ∫⁻ salt, ∫⁻ p : Bytes b × (Fin (n - 1) → Bytes b),
        (∫⁻ H, ∫⁻ W,
          F (programPath hb hB salt p.1 p.2 H W)
            (labelPuzzle salt p.1 p.2 (pathLabels hb W)) ((pathLabels hb W) .key)
          ∂(uniformOn Set.univ : Measure (PathValue n m → Bytes 32))
          ∂(uniformOn Set.univ : Measure (ByteArray.Bounded B → Bytes 32))) +
            (solvePoints n m : ENNReal) ^ 2 / Fintype.card (Bytes 32)
        ∂(uniformOn Set.univ : Measure (Bytes b × (Fin (n - 1) → Bytes b)))
        ∂(uniformOn Set.univ : Measure (Bytes 16)) := by
      apply lintegral_mono
      intro salt
      apply lintegral_mono
      intro p
      exact masked_le_programmed_add_collision hb hn hB salt p.1 p.2 F hF
    _ = _ := by
      simp_rw [lintegral_add_left Measurable.of_discrete, lintegral_const,
        measure_univ, mul_one]

end Coins

end Uniform
end PointerChainPuzzle.LeanSeal
