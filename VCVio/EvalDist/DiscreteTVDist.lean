/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

module

public import VCVio.EvalDist.EvalDistEq
public import VCVio.EvalDist.MeasureTVDist.Basic
public import VCVio.EvalDist.MeasureTVDist.Bind
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Total variation under the discrete σ-algebra

`measureTVDist` compares the successful-output measures of two computations and needs a
`MeasurableSpace` on the output type. `discreteTVDist` fixes the discrete σ-algebra `⊤`, selected
locally by `letI : MeasurableSpace α := ⊤`, so statements about it carry no measurable-space
hypothesis. Every set of outputs is then an event, and every continuation is measurable.

Failure mass is counted. Output measures may have total mass below one, and on such measures the
distance equals the total variation after adding the missing mass as an explicit failure outcome
(see `ToMathlib.MeasureTheory.Measure.TotalVariation`): a computation that always fails is at
distance one from a computation that never fails.

An event's probability under one computation is at most its probability under another plus the
discrete total-variation distance between them: `μ(E) ≤ ν(E) + d_TV(μ, ν)`.

## References

* A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*, Definition 1.2.9
  (statistical distance).
-/

public section

open MeasureTheory
open scoped ENNReal

universe u v

variable {m : Type u → Type v} {α β : Type u}

/-- Real total variation between the output measures of two computations, with every set of
outputs measurable. For finitely supported outputs this is the statistical distance. -/
@[expose] noncomputable def discreteTVDist [EvalDistSemantics m] (mx my : m α) : ℝ :=
  letI : MeasurableSpace α := ⊤
  measureTVDist mx my

namespace discreteTVDist

variable [EvalDistSemantics m]

/-- On a discrete measurable space, choosing the discrete σ-algebra does not change TV. -/
theorem eq_measureTVDist [MeasurableSpace α] [DiscreteMeasurableSpace α] (mx my : m α) :
    discreteTVDist mx my = measureTVDist mx my := by
  have h : ‹MeasurableSpace α› = ⊤ := top_unique fun _ _ => MeasurableSet.of_discrete
  cases h
  rfl

@[simp]
theorem self (mx : m α) : discreteTVDist mx mx = 0 := by
  let : MeasurableSpace α := ⊤
  exact measureTVDist_self mx

theorem comm (mx my : m α) : discreteTVDist mx my = discreteTVDist my mx := by
  let : MeasurableSpace α := ⊤
  exact measureTVDist_comm mx my

theorem nonneg (mx my : m α) : 0 ≤ discreteTVDist mx my := by
  let : MeasurableSpace α := ⊤
  exact measureTVDist_nonneg mx my

theorem triangle (mx my mz : m α) :
    discreteTVDist mx mz ≤ discreteTVDist mx my + discreteTVDist my mz := by
  let : MeasurableSpace α := ⊤
  exact measureTVDist_triangle mx my mz

theorem le_one (mx my : m α) : discreteTVDist mx my ≤ 1 := by
  let : MeasurableSpace α := ⊤
  exact measureTVDist_le_one mx my

/-- A common continuation contracts the distance. -/
theorem bind_le [Monad m] [LawfulEvalDistSemantics m] (mx my : m α) (f : α → m β) :
    discreteTVDist (mx >>= f) (my >>= f) ≤ discreteTVDist mx my := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  exact measureTVDist_bind_le mx my f (fun _ _ => trivial)

/-- A common map contracts the distance. -/
theorem map_le [Monad m] [LawfulMonad m] [LawfulEvalDistSemantics m]
    (mx my : m α) (f : α → β) :
    discreteTVDist (f <$> mx) (f <$> my) ≤ discreteTVDist mx my := by
  simpa only [map_eq_bind_pure_comp] using bind_le mx my (pure ∘ f)

/-- Two `pure` computations are at distance zero when they return the same value and at distance
one otherwise. -/
theorem pure_pure [Monad m] [LawfulPureEvalDistSemantics m] (a b : α) [Decidable (a = b)] :
    discreteTVDist (pure a : m α) (pure b) = if a = b then 0 else 1 := by
  let : MeasurableSpace α := ⊤
  exact measureTVDist_pure_pure a b

end discreteTVDist

section eventTransfer

open scoped NNReal

variable {m : Type → Type v} [EvalDistSemantics m] {β : Type}

/-- The real distance's `ofReal` is the extended total-variation distance. -/
theorem ofReal_discreteTVDist_eq (p q : m β) :
    ENNReal.ofReal (discreteTVDist p q) = (letI : MeasurableSpace β := ⊤; measureETVDist p q) := by
  let : MeasurableSpace β := ⊤
  unfold discreteTVDist measureTVDist
  exact ENNReal.ofReal_toReal (Measure.etvDist_ne_top _ _
    (EvalDistSemantics.apply_univ_le_one _) (EvalDistSemantics.apply_univ_le_one _))

variable [Monad m] [LawfulMonad m] [LawfulEvalDistSemantics m]

/-- Computations equal in distribution are at distance zero. -/
theorem discreteTVDist.eq_zero_of_evalDistEq {mx my : m β} (h : mx =ᵈ my) :
    discreteTVDist mx my = 0 := by
  let : MeasurableSpace β := ⊤
  unfold discreteTVDist measureTVDist
  rw [h.evalDist_eq]
  exact Measure.tvDist_self _

/-- **Probability transfer across total variation.** For any event `p`, its probability under
`mx` is at most its probability under `my` plus `discreteTVDist mx my`. -/
theorem prEvent_le_prEvent_add_ofReal_discreteTVDist (mx my : m β)
    (p : β → Prop) :
    Pr{let x ← mx}[p x] ≤ Pr{let x ← my}[p x] + ENNReal.ofReal (discreteTVDist mx my) := by
  let : MeasurableSpace β := ⊤
  rw [prEvent_eq_evalDist mx p measurable_from_top, prEvent_eq_evalDist my p measurable_from_top,
    discreteTVDist, measureTVDist, Measure.tvDist, ENNReal.ofReal_toReal
      (Measure.etvDist_ne_top _ _ (EvalDistSemantics.apply_univ_le_one _)
        (EvalDistSemantics.apply_univ_le_one _))]
  calc 𝒟[mx] {x | p x} ≤ 𝒟[my] {x | p x} + (𝒟[mx] {x | p x} - 𝒟[my] {x | p x}) := le_add_tsub
    _ ≤ _ := by
      gcongr; exact le_self_add.trans (measure_absDiff_apply_le_measureETVDist mx my trivial)

/-- Transfer an endpoint event bound across a supplied total-variation bound. -/
theorem prEvent_le_of_discreteTVDist_le (mx my : m β) (p : β → Prop)
    {d : ℝ} {ε : ℝ≥0∞} (hTV : discreteTVDist mx my ≤ d)
    (hEvent : Pr{let x ← my}[p x] ≤ ε) :
    Pr{let x ← mx}[p x] ≤ ε + ENNReal.ofReal d :=
  (prEvent_le_prEvent_add_ofReal_discreteTVDist mx my p).trans
    (add_le_add hEvent (ENNReal.ofReal_le_ofReal hTV))

/-- Transfer a completeness lower bound across total variation, adding the statistical loss
to the original error. Truncated subtraction also covers errors greater than one. -/
theorem one_sub_le_prEvent_of_discreteTVDist_le (mx my : m β) (p : β → Prop)
    {ε δ : ℝ≥0} (hTV : discreteTVDist mx my ≤ (δ : ℝ))
    (hEvent : 1 - (ε : ℝ≥0∞) ≤ Pr{let x ← mx}[p x]) :
    1 - ((ε + δ : ℝ≥0) : ℝ≥0∞) ≤ Pr{let x ← my}[p x] := by
  have h := hEvent.trans ((prEvent_le_prEvent_add_ofReal_discreteTVDist mx my p).trans
    (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hTV)))
  rw [ENNReal.ofReal_coe_nnreal] at h
  rw [ENNReal.coe_add, ← tsub_tsub]
  exact tsub_le_iff_right.mpr h

end eventTransfer
