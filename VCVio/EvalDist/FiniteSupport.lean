/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

module

public import ToMathlib.MeasureTheory.Integral.Countable
public import ToMathlib.MeasureTheory.Measure.Coupling.Maximal
public import VCVio.EvalDist.EvalDistEq
public import VCVio.EvalDist.Monad.Measure
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Finitely supported denotations and their singleton masses

A computation whose support is finite denotes, under the discrete σ-algebra, a measure
concentrated on a finite set. Its event masses are finite sums of singleton masses, so
singleton comparisons `Pr{let y ← mx}[y = x]` determine measure comparisons. Oracle computations
with finite answer types, and their `OptionT` wrappers, have finite support.
-/

public section

open MeasureTheory
open scoped ENNReal

section FiniteSupport

universe v

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] [MonadAttach m] [WeaklyLawfulMonadAttach m] {α : Type}

/-- A computation has no discrete mass outside a finite superset of its support. -/
theorem evalDist_compl_eq_zero_of_support_subset (mx : m α) (F : Finset α)
    (hF : support mx ⊆ F) :
    (letI : MeasurableSpace α := ⊤; 𝒟[mx] (↑F)ᶜ) = 0 := by
  let : MeasurableSpace α := ⊤
  exact evalDist.apply_eq_zero_of_disjoint_support mx MeasurableSet.of_discrete
    fun x hx hxF => hxF (hF hx)

/-- Singleton domination by a finitely supported computation gives discrete measure
domination. The dominating computation may have infinite support. -/
theorem evalDist_le_of_prEvent_eq_le (mx my : m α) (hfin : (support mx).Finite)
    (h : ∀ x, Pr{let y ← mx}[y = x] ≤ Pr{let y ← my}[y = x]) :
    (letI : MeasurableSpace α := ⊤; 𝒟[mx] ≤ 𝒟[my]) := by
  let : MeasurableSpace α := ⊤
  refine Measure.le_of_singleton_le_of_compl_null hfin.toFinset
    (evalDist_compl_eq_zero_of_support_subset mx _ (by simp)) fun x _ => ?_
  simpa only [prEvent_eq_evalDist_singleton] using h x

/-- Equal singleton masses of finitely supported computations give equal discrete measures. -/
theorem evalDist_eq_of_prEvent_eq_eq (mx my : m α) (hx : (support mx).Finite)
    (hy : (support my).Finite)
    (h : ∀ x, Pr{let y ← mx}[y = x] = Pr{let y ← my}[y = x]) :
    (letI : MeasurableSpace α := ⊤; 𝒟[mx] = 𝒟[my]) :=
  le_antisymm (evalDist_le_of_prEvent_eq_le mx my hx fun x => (h x).le)
    (evalDist_le_of_prEvent_eq_le my mx hy fun x => (h x).ge)

/-- Equal singleton masses on an event give equal discrete measures restricted to it. -/
theorem evalDist_restrict_eq_of_prEvent_eq_eq (mx my : m α) (hx : (support mx).Finite)
    (hy : (support my).Finite) (good : α → Prop)
    (h : ∀ x, good x → Pr{let y ← mx}[y = x] = Pr{let y ← my}[y = x]) :
    (letI : MeasurableSpace α := ⊤;
      (𝒟[mx]).restrict {x | good x} = (𝒟[my]).restrict {x | good x}) := by
  classical
  let : MeasurableSpace α := ⊤
  have hnull : ∀ mz : m α, support mz ⊆ ↑(hx.toFinset ∪ hy.toFinset) →
      ((𝒟[mz]).restrict {x | good x}) (↑(hx.toFinset ∪ hy.toFinset))ᶜ = 0 := fun mz hz =>
    nonpos_iff_eq_zero.mp <| (Measure.le_iff'.mp Measure.restrict_le_self _).trans_eq
      (evalDist_compl_eq_zero_of_support_subset mz _ hz)
  refine Measure.ext_of_compl_eq_zero (F := hx.toFinset ∪ hy.toFinset)
    (hnull mx fun x h => by simp [h]) (hnull my fun x h => by simp [h]) ?_
  · intro x _
    rw [Measure.restrict_apply MeasurableSet.of_discrete,
      Measure.restrict_apply MeasurableSet.of_discrete]
    by_cases hgx : good x
    · rw [show ({x} : Set α) ∩ {x | good x} = {x} from
        Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hgx)]
      simpa only [prEvent_eq_evalDist_singleton] using h x hgx
    · rw [show ({x} : Set α) ∩ {x | good x} = ∅ from
        Set.eq_empty_of_forall_notMem fun y hy => hgx (hy.1 ▸ hy.2)]
      simp

/-- Integration against a finitely supported discrete denotation is a sum over its
singleton masses. -/
theorem lintegral_evalDist_eq_tsum_of_support_finite (mx : m α) (hfin : (support mx).Finite)
    (f : α → ℝ≥0∞) :
    (letI : MeasurableSpace α := ⊤; ∫⁻ a, f a ∂𝒟[mx]) =
      ∑' a, Pr{let x ← mx}[x = a] * f a := by
  let : MeasurableSpace α := ⊤
  simp only [prEvent_eq_evalDist_singleton]
  exact lintegral_eq_tsum_mul_of_ae_mem_countable hfin.countable
    (evalDist.ae_of_forall_mem_support mx _ MeasurableSet.of_discrete fun _ h => h) f

end FiniteSupport

/-- An optional computation has finite support when its underlying run does. -/
theorem OptionT.support_finite_of_run {m : Type → Type*} [Monad m] [MonadAttach m] {α : Type}
    (mx : OptionT m α) (h : (support mx.run).Finite) :
    (support mx).Finite :=
  h.preimage (Option.some_injective α).injOn
