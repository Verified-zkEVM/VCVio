/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.OfflineOldEstimate
public import VCVio.Quantum.VC.Proof.OfflineOldCollision
public import VCVio.CryptoFoundations.MerkleTree.Salted.Conditions
import all VCVio.Quantum.VC.Proof.CheckerComparison

/-!
# The old offline challenger's retained accepting branches

Rejected check/extraction transcripts contribute zero to the mismatch event. The remaining
sum keeps the opening instrument attached to its measured extraction outcome.
-/

public section

open Matrix MeasureTheory
open scoped ComplexOrder Kronecker ENNReal Matrix.Norms.L2Operator
namespace Quantum

variable {k : ℕ} {X Y Msg Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z]
  [DecidableEq Z] {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)}
  (io : ∀ i, (VC i).CheckIOForm)
  (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) (Fin k → Database X Y))

/-- The mismatch branch vanishes unless both checks accept and extraction decodes. -/
theorem run₂_offlineFinish_reject
    (R : QuantumRuntime (EmulatedOracle.cohSpec (extIn k X Y Cm Z)))
    (hk : 1 ≤ k) (qs : ℕ) (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    (r : Bool × Option (TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) × Bool)
    (hr : ¬ ∃ tdm, r = (true, some tdm, true)) :
    (R.run₂ .instruments (offlineFinish (VC := VC) (Z := Z) hk qs c B r)).branch true = 0 := by
  rcases r with ⟨a, v, b⟩
  cases v with
  | none =>
    simp only [offlineFinish, QuantumRuntime.run₂_pure,
      SubInstrument.branch_pure_of_ne (by decide : true ≠ false)]
  | some tdm =>
    have hb : a = false ∨ b = false := by cases a <;> cases b <;> simp_all
    ext ρ : 1
    rw [offlineFinish, QuantumRuntime.run₂_bind, SubInstrument.branch_bind_apply]
    simp only [LinearMap.zero_apply]
    refine (tsum_congr fun pf ↦ ?_).trans tsum_zero
    rcases hb with rfl | rfl <;>
      simp [QuantumRuntime.run₂_pure, SubInstrument.branch_pure_of_ne]

/-- The finishing mismatch branch vanishes when the claim exceeds its opening budget. -/
theorem run₂_offlineFinish_over_budget
    (R : QuantumRuntime (EmulatedOracle.cohSpec (extIn k X Y Cm Z)))
    (hk : 1 ≤ k) (qs : ℕ) (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    (hq : ¬ ∑ i, (c.ans i).dom.card ≤ qs)
    (r : Bool × Option (TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) × Bool) :
    (R.run₂ .instruments (offlineFinish (VC := VC) (Z := Z) hk qs c B r)).branch true = 0 := by
  rcases r with ⟨a, v, b⟩
  cases v with
  | none =>
    simp only [offlineFinish, QuantumRuntime.run₂_pure,
      SubInstrument.branch_pure_of_ne (by decide : true ≠ false)]
  | some tdm =>
    ext ρ : 1
    rw [offlineFinish, QuantumRuntime.run₂_bind, SubInstrument.branch_bind_apply]
    simp only [LinearMap.zero_apply]
    refine (tsum_congr fun pf ↦ ?_).trans tsum_zero
    simp [hq, QuantumRuntime.run₂_pure, SubInstrument.branch_pure_of_ne]

variable [AddCommGroup Y] [AddGroup Z] [∀ i, DecidableEq (DmOf ℓ Msg Td i)]

/-- The actual challenger's mismatch probability is exactly the sum of the retained
accepting check/extract/check branches followed by their opening/decision instruments. -/
theorem offlineChallenger_weight_eq_retained
    (code : TpDCode k (DmOf ℓ Msg Td) Z) (hk : 1 ≤ k) (qs : ℕ)
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    (ρ : SubState (B × (Fin k → Database X Y))) :
    let R := ((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime
    (R.run₂ .instruments (offlineChallenger VC code hk qs c B)).outcomeMeasure ρ {true} =
      ∑' tdm, ENNReal.ofReal (((R.run₂ .instruments
        (offlineFinish (VC := VC) (Z := Z) hk qs c B (true, some tdm, true))).branch true)
          (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
            (actualBatch io c.Wᶜ c * extractProj ME (TpIC.full hk c.idx c.cm) tdm *
              actualBatch io c.W c)) ρ.matrix)).trace.re := by
  classical
  let R := ((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime
  change (R.run₂ .instruments _).outcomeMeasure ρ {true} = _
  rw [offlineChallenger_eq_bind_offlineChecks code, QuantumRuntime.run₂_bind]
  change ((R.run₂ .instruments (offlineChecks (VC := VC) code hk c B)).bind
    (fun r ↦ R.run₂ .instruments (offlineFinish (VC := VC) (Z := Z) hk qs c B r))).outcomeMeasure
      ρ {true} = _
  erw [SubInstrument.outcomeMeasure_bind,
    Measure.sum_apply _ (measurableSet_singleton true)]
  simp only [SubInstrument.outcomeMeasure_apply_singleton]
  let f := fun r ↦ ENNReal.ofReal (((R.run₂ .instruments
    (offlineFinish (VC := VC) (Z := Z) hk qs c B r)).branch true)
      (((R.run₂ .instruments (offlineChecks (VC := VC) code hk c B)).branch r)
        ρ.matrix)).trace.re
  let g := fun tdm : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk) ↦ (true, some tdm, true)
  have hg : Function.Injective g := by
    intro a b h
    exact Option.some.inj (congrArg (fun r ↦ r.2.1) h)
  have hs : Function.support f ⊆ Set.range g := by
    intro r hr
    by_contra hn
    have hz := run₂_offlineFinish_reject (VC := VC) R hk qs c B r (by
      simpa only [Set.mem_range, g, eq_comm] using hn)
    exact hr (by simp [f, hz])
  change (∑' r, f r) = _
  rw [← hg.tsum_eq hs]
  apply tsum_congr
  intro tdm
  dsimp only [f, g]
  erw [run₂_offlineChecks_accept io code ME hk c B tdm]
  rfl

omit [∀ i, DecidableEq (DmOf ℓ Msg Td i)] in
include io in
/-- Claims exceeding the opening budget have zero mismatch probability. -/
theorem offlineChallenger_over_budget
    (code : TpDCode k (DmOf ℓ Msg Td) Z) (hk : 1 ≤ k) (qs : ℕ)
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    (ρ : SubState (B × (Fin k → Database X Y))) (hq : ¬ ∑ i, (c.ans i).dom.card ≤ qs) :
    let R := ((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime
    (R.run₂ .instruments (offlineChallenger VC code hk qs c B)).outcomeMeasure ρ {true} = 0 := by
  classical
  dsimp only
  rw [offlineChallenger_weight_eq_retained io ME code hk qs c B ρ]
  refine (tsum_congr fun tdm ↦ ?_).trans tsum_zero
  have hz := run₂_offlineFinish_over_budget (VC := VC)
    ((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime hk qs c B hq
    (true, some tdm, true)
  erw [hz]
  change ENNReal.ofReal (0 : Matrix (B × (Fin k → Database X Y)) _ ℂ).trace.re = 0
  simp

/-- The challenger comparison keeps every measured extraction result and its finishing map.
The three discrepancies are charged on the original substate. -/
theorem offlineChallenger_le_bad_add_distances
    (tdBot : ∀ i, Td i) (Pgood : Set (Database X Y)) [DecidablePred (· ∈ Pgood)]
    (hC : Conditions VC io ME tdBot Pgood)
    (code : TpDCode k (DmOf ℓ Msg Td) Z) (hk : 1 ≤ k) (qs : ℕ)
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    (ρ : SubState (B × (Fin k → Database X Y))) :
    let R := ((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime
    let P := fun W ↦ (1 : Matrix B B ℂ) ⊗ₖ checkPassProjector io W c.idx c.cm c.ans c.pf
    let Q := fun W ↦ (1 : Matrix B B ℂ) ⊗ₖ filledBatch io W c
    let G := diagonal (fun D : Fin k → Database X Y ↦
      if ∀ i, D i ∈ Pgood then (1 : ℂ) else 0)
    ((R.run₂ .instruments (offlineChallenger VC code hk qs c B)).outcomeMeasure ρ {true}) ^
        (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (1 - G)) ρ.matrix).trace.re ^
          (2⁻¹ : ℝ) +
        (ENNReal.ofReal (‖Q c.W - P c.W‖ ^ 2) * ENNReal.ofReal ρ.matrix.trace.re) ^
          (2⁻¹ : ℝ) +
        (ENNReal.ofReal (‖Q c.Wᶜ - P c.Wᶜ‖ ^ 2) * ENNReal.ofReal ρ.matrix.trace.re) ^
          (2⁻¹ : ℝ) +
        (∑' tdm, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
          (actualBatch io c.Wᶜ c * extractProj ME (TpIC.full hk c.idx c.cm) tdm *
              actualBatch io c.W c - filledBatch io c.Wᶜ c *
                extractProj ME (TpIC.full hk c.idx c.cm) tdm * filledBatch io c.W c))
                  ρ.matrix).trace.re) ^ (2⁻¹ : ℝ) := by
  classical
  let R := ((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime
  let Φ : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk) →
      MatrixMap (B × (Fin k → Database X Y)) (B × (Fin k → Database X Y)) := fun tdm ↦
    (R.run₂ .instruments
    (offlineFinish (VC := VC) (Z := Z) hk qs c B (true, some tdm, true))).branch true
  let K := fun tdm ↦ (1 : Matrix B B ℂ) ⊗ₖ
    (actualBatch io c.Wᶜ c * extractProj ME (TpIC.full hk c.idx c.cm) tdm * actualBatch io c.W c)
  let J := fun tdm ↦ (1 : Matrix B B ℂ) ⊗ₖ
    (filledBatch io c.Wᶜ c * extractProj ME (TpIC.full hk c.idx c.cm) tdm * filledBatch io c.W c)
  have hh := MatrixMap.finish_comparison Φ
    (fun tdm ↦ (R.run₂ .instruments (offlineFinish (VC := VC) (Z := Z)
      hk qs c B (true, some tdm, true))).isCP_branch true)
    (fun tdm ↦ (R.run₂ .instruments (offlineFinish (VC := VC) (Z := Z)
      hk qs c B (true, some tdm, true))).isCPTNIFamily.isTNI true) ρ.posSemidef K J
  have hb := offlineFinish_filled_le_bad_add_distance io ME tdBot Pgood hC
    code hk qs c B ρ.posSemidef
  have hd (tdm) : K tdm - J tdm = (1 : Matrix B B ℂ) ⊗ₖ
      (actualBatch io c.Wᶜ c * extractProj ME (TpIC.full hk c.idx c.cm) tdm *
          actualBatch io c.W c - filledBatch io c.Wᶜ c *
            extractProj ME (TpIC.full hk c.idx c.cm) tdm * filledBatch io c.W c) := by
    ext a b
    simp only [K, J, Matrix.sub_apply, kroneckerMap_apply, mul_sub]
  dsimp only
  rw [offlineChallenger_weight_eq_retained io ME code hk qs c B ρ]
  refine hh.trans (add_le_add ?_ ?_)
  · convert hb using 1
    congr 2
    funext tdm
    congr 4
    simp only [J, ← mul_kronecker_mul, Matrix.one_mul]
    erw [← mul_kronecker_mul, Matrix.one_mul]
    rfl
  · apply le_of_eq
    congr 1
    apply tsum_congr
    intro tdm
    exact congrArg (fun M ↦ ENNReal.ofReal (MatrixMap.conj M ρ.matrix).trace.re) (hd tdm)

end Quantum
