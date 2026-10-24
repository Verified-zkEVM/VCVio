/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T1.ProbBounds
public import VCVio.ProgramLogic.Library.T1.UpperRanked

/-!
# Probability bounds: usage tests

Fresh draws, exact averages, and bad-event bounds composed across the phases of a stateful
simulation.
-/

@[expose] public section

open ENNReal OracleSpec OracleComp OracleComp.ProgramLogic

namespace VCVioTest.ProgramLogic.Library.ProbBounds

/-- Two fresh draws: the first is charged for its one bad value, the second for its hit. -/
example : Pr{let x ← ($ᵗ (Fin 4) : ProbComp (Fin 4)); let y ← $ᵗ (Fin 4)}[x = 0 ∨ y = 0] ≤
    1 / 4 + 4⁻¹ := by
  refine (prEvent_uniformSample_bind_le_add _ (· = 0) (d := 1) (by decide) (ε := 4⁻¹)
    fun x hx => ?_).trans (by simp)
  simp only [hx, false_or]
  exact (SampleableType.prEvent_uniformSample_eq_singleton 0).le

/-- An exact probability by averaging over the first draw. -/
example : Pr{let x ← ($ᵗ Bool : ProbComp Bool); let y ← $ᵗ Bool}[y = x] = 2⁻¹ := by
  rw [prEvent_uniformSample_bind_eq]
  simp only [SampleableType.prEvent_uniformSample_eq_singleton, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Fintype.card_bool]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp), one_div, Nat.cast_ofNat]

/-- A draw that raises a flag on `true`. -/
def flag : StateT Bool ProbComp Bool := StateT.mk fun s => (fun b => (b, s || b)) <$> ($ᵗ Bool)

lemma prEvent_flag_run_false : Pr{let w ← flag.run false}[w.2 = true] = 2⁻¹ := by
  simp [flag, StateT.run_mk, SampleableType.prEvent_uniformSample_eq_singleton]

/-- A union bound through a stateful bind: each phase raises the flag with probability `1/2`. -/
example : Pr{let w ← (flag >>= fun _ => flag).run false}[w.2 = true] ≤ 2⁻¹ + 2⁻¹ := by
  refine (prEvent_run_bind_le_add_of_support flag _ false (fun z => z.2 = true) _
    fun z _ hz => ?_).trans (by rw [prEvent_flag_run_false])
  simp only [Bool.not_eq_true] at hz
  rw [hz, prEvent_flag_run_false]

/-- A coin answered by a draw from `Fin 4` that raises the bad flag on `0`. -/
def hitCoin : QueryImpl coinSpec (StateT Bool ProbComp) := fun _ => StateT.mk fun bad =>
  (fun x : Fin 4 => (decide (x = 0), bad || decide (x = 0))) <$> ($ᵗ (Fin 4))

lemma prEvent_hitCoin_bad (t : Unit) :
    Pr{let z ← (hitCoin t).run false}[z.2 = true] ≤ 4⁻¹ := by
  simp [hitCoin, StateT.run_mk, SampleableType.prEvent_uniformSample_eq_singleton]

/-- Composing two phase bounds of a simulation: the first phase within `n` queries and every
continuation within `m` queries. -/
example {α β : Type} (oa : OracleComp coinSpec α) (f : α → OracleComp coinSpec β) (n m : ℕ)
    (hn : IsTotalQueryBound oa n) (hm : ∀ a, IsTotalQueryBound (f a) m) :
    Pr{let w ← (simulateQ hitCoin (oa >>= f)).run false}[w.2 = true] ≤ n * 4⁻¹ + m * 4⁻¹ := by
  have hstep : ∀ t s, ¬s = true → Pr{let z ← (hitCoin t).run s}[z.2 = true] ≤ 4⁻¹ :=
    fun t s hs => by simp only [Bool.not_eq_true] at hs; subst hs; exact prEvent_hitCoin_bad t
  refine (prEvent_simulateQ_run_bind_le_add_of_support hitCoin oa f false (fun z => z.2 = true) _
    fun z _ hz => prEvent_simulateQ_run_bad_le_of_step hitCoin (· = true) 4⁻¹ hstep _ m (hm _) _
      hz).trans (add_le_add ?_ le_rfl)
  exact prEvent_simulateQ_run_bad_le_of_step hitCoin (· = true) 4⁻¹ hstep oa n hn false (by simp)

/-- Reordering a state-independent draw past a stateful one. -/
example (s : Bool) :
    (do let a ← (liftM ($ᵗ Bool : ProbComp Bool) : StateT Bool ProbComp Bool)
        let b ← flag
        pure (a && b)).run s =ᵈ
      (do let b ← flag
          let a ← (liftM ($ᵗ Bool : ProbComp Bool) : StateT Bool ProbComp Bool)
          pure (a && b)).run s :=
  evalDistEq_run_liftM_bind_swap _ _ (fun a b => pure (a && b)) s

/-- A union bound with the worst good continuation. -/
example (mx : ProbComp ℕ) (f : ℕ → ProbComp Bool) :
    Pr{let x ← mx; let y ← f x}[y = true ∧ 3 < x] ≤
      Pr{let x ← mx}[x ≤ 3] + ⨆ x ∈ support mx, ⨆ (_ : ¬x ≤ 3), Pr{let y ← f x}[y = true] :=
  (prEvent_bind_le_add_iSup mx _ (· ≤ 3)).trans (add_le_add le_rfl (iSup₂_mono fun _ _ =>
    iSup_mono fun _ => prEvent_mono _ _ _ fun _ h => h.1))

end VCVioTest.ProgramLogic.Library.ProbBounds
