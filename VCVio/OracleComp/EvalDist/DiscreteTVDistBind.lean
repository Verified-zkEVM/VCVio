/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

module

public import VCVio.EvalDist.DiscreteTVDist
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.ProbComp

/-!
# Sequential laws for `discreteTVDist`

Event-level congruence, conditional majorants after a common prefix, and the independent-pair
bound for `discreteTVDist`.
-/

public section

open MeasureTheory
open scoped ENNReal

universe v

namespace discreteTVDist

section Generic

variable {m : Type → Type v} [EvalDistSemantics m] {α β : Type}

/-- The distance only depends on the laws of the two computations. -/
theorem congr_evalDistEq [Monad m] [LawfulMonad m] [LawfulEvalDistSemantics m]
    {mx mx' my my' : m α} (hx : mx =ᵈ mx') (hy : my =ᵈ my') :
    discreteTVDist mx my = discreteTVDist mx' my' := by
  let : MeasurableSpace α := ⊤
  unfold discreteTVDist measureTVDist
  rw [hx.evalDist_eq, hy.evalDist_eq]

/-- A uniform bound on the continuations bounds the distance after a common prefix. -/
theorem bind_bind_le_of_forall_le [Monad m] [LawfulEvalDistSemantics m]
    (mx : m α) (f g : α → m β) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ a, discreteTVDist (f a) (g a) ≤ ε) :
    discreteTVDist (mx >>= f) (mx >>= g) ≤ ε := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  have hle : ∀ a, measureETVDist (f a) (g a) ≤ ENNReal.ofReal ε := fun a => by
    have hne : measureETVDist (f a) (g a) ≠ ⊤ :=
      Measure.etvDist_ne_top _ _ (evalDist_apply_univ_le_one _) (evalDist_apply_univ_le_one _)
    rw [← ENNReal.ofReal_toReal hne]
    exact ENNReal.ofReal_le_ofReal (h a)
  have hfinite : (∫⁻ _, ENNReal.ofReal ε ∂𝒟[mx]) ≠ ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top (evalDist_apply_univ_le_one _))
  refine (measureTVDist_bind_bind_le_lintegral mx f g (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ => ENNReal.ofReal ε) (Filter.Eventually.of_forall hle) hfinite).trans ?_
  rw [lintegral_const]
  calc (ENNReal.ofReal ε * 𝒟[mx] Set.univ).toReal
      ≤ (ENNReal.ofReal ε).toReal := by
        refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
        exact mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)
    _ = ε := ENNReal.toReal_ofReal hε

end Generic

section OracleComp

variable {ι : Type} {spec : OracleSpec ι}
  [∀ t, Countable (spec.Range t)] [OracleSpec.AnswerMeasure spec] {α β : Type}

/-- Independent pairs are at distance at most the sum of the coordinate distances. -/
theorem pair_le (ma na : OracleComp spec α) (mb nb : OracleComp spec β) :
    discreteTVDist
        (do let a ← ma; let b ← mb; pure (a, b))
        (do let a ← na; let b ← nb; pure (a, b)) ≤
      discreteTVDist ma na + discreteTVDist mb nb := by
  refine (triangle _ (do let a ← na; let b ← mb; pure (a, b)) _).trans (add_le_add ?_ ?_)
  · exact bind_le ma na _
  · let : MeasurableSpace (α × β) := ⊤
    rw [congr_evalDistEq (my' := do let b ← nb; let a ← na; pure (a, b))
      (mx' := do let b ← mb; let a ← na; pure (a, b))
      (evalDistEq_iff_evalDist_eq.mpr (OracleComp.evalDist_bind_bind_swap na mb _))
      (evalDistEq_iff_evalDist_eq.mpr (OracleComp.evalDist_bind_bind_swap na nb _))]
    exact bind_le mb nb _

end OracleComp

section Mixtures

variable {A B : Type}

open OracleComp

/-- A uniform pointwise TV bound on the outer support bounds the entire mixture of total
kernels. No finite-support assumption is used. -/
theorem bind_bind_le_of_support (d : ProbComp A) (f g : A → ProbComp B) (ε : ℝ)
    (h : ∀ a ∈ support d, discreteTVDist (f a) (g a) ≤ ε) :
    discreteTVDist (d >>= f) (d >>= g) ≤ ε := by
  obtain ⟨a₀, ha₀⟩ := OracleComp.support_nonempty d
  have hε : 0 ≤ ε := (discreteTVDist.nonneg _ _).trans (h a₀ ha₀)
  rw [bind_eq_attach_bind d f, bind_eq_attach_bind d g]
  exact bind_bind_le_of_forall_le _ _ _ hε (fun a => h a.1 a.2)

/-- Conditional event bounds on continuation distances integrate under the same actual
prefix distribution, without a pointwise worst-case replacement of its bad probability. -/
lemma ofReal_bind_bind_le_prEvent {A B C : Type} (worlds : ProbComp A)
    (left right : A → ProbComp B) (failure : A → ProbComp C) (bad : C → Prop)
    (bound : ∀ a, ENNReal.ofReal (discreteTVDist (left a) (right a)) ≤
      Pr{let c ← failure a}[bad c]) :
    ENNReal.ofReal (discreteTVDist (worlds >>= left) (worlds >>= right)) ≤
      Pr{let c ← worlds >>= failure}[bad c] := by
  let : MeasurableSpace A := ⊤
  let : MeasurableSpace B := ⊤
  rw [ofReal_discreteTVDist_eq, prEvent_bind_eq_lintegral_of_discrete]
  exact measureETVDist_bind_bind_le_lintegral worlds left right
    (fun _ _ => trivial) (fun _ _ => trivial) _
    (Filter.Eventually.of_forall (fun a => (ofReal_discreteTVDist_eq _ _).symm.trans_le (bound a)))

end Mixtures

end discreteTVDist
