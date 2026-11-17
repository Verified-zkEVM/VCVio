/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.UntilBad
import ToMathlib.MeasureTheory.Measure.Coupling.Bind

/-!
# A common random continuation after domination until bad

Whole-run domination retains the result and the complete service state.
A common random continuation may inspect both before choosing its output.
The original bad event remains an alternative after that continuation.
Its mass is retained because `ProbComp` continuations are lossless, including when an error is
returned as ordinary data.
-/

public section

open OracleComp MeasureTheory

namespace QueryImpl.DominatedUntilBad

/-- After the same lossless random continuation, an event in the second run is bounded by
that event or the original bad final state in the first run.
The continuation may inspect the complete returned result and mapped service state.
-/
theorem prEvent_simulateQ_run_bind_le_map_or_bad
    {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ α γ : Type}
    {impl₁ : QueryImpl spec (StateT σ₁ ProbComp)}
    {impl₂ : QueryImpl spec (StateT σ₂ ProbComp)}
    {f : σ₁ → σ₂} {inv bad : σ₁ → Prop}
    (h : DominatedUntilBad impl₁ impl₂ f inv bad)
    (hinv : PreservesInv impl₁ inv) (hbad : PreservesInv impl₁ bad)
    (oa : OracleComp spec α) (s : σ₁) (hs : inv s)
    (F : (α × σ₂) → ProbComp γ) (P : γ → Prop) :
    Pr{let z ← (simulateQ impl₂ oa).run (f s); let y ← F z}[P y] ≤
      Pr{let z ← (simulateQ impl₁ oa).run s; let y ← F (z.1, f z.2)}[P y ∨ bad z.2] := by
  -- Choose the discrete structure on each WHOLE joint type, including any function-valued cache.
  let _ : MeasurableSpace (α × σ₁) := ⊤
  let _ : MeasurableSpace (α × σ₂) := ⊤
  let _ : MeasurableSpace γ := ⊤
  let first := (simulateQ impl₁ oa).run s
  let second := (simulateQ impl₂ oa).run (f s)
  let φ : α × σ₁ → α × σ₂ := fun z => (z.1, f z.2)
  let good : Set (α × σ₁) := {z | ¬bad z.2}
  -- The existing theorem supplies domination for every event of the entire joint state.
  have hμ : Measure.map φ ((𝒟[first]).restrict good) ≤ 𝒟[second] := by
    refine Measure.le_iff.2 fun A _ => ?_
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
      Measure.restrict_apply MeasurableSet.of_discrete]
    simpa only [first, second, φ, good, prEvent_eq_evalDist_of_discrete, Set.inter_def,
      Set.mem_ofPred_eq, Set.mem_preimage, Set.ofPred_mem_eq] using
        h.prEvent_simulateQ_run_map_and_not_bad_le hinv hbad oa s hs (· ∈ A)
  -- Bind this restricted joint measure through exactly the same measurable continuation.
  have hpost : ((𝒟[first]).restrict good).bind (fun z => 𝒟[F (φ z)]) ≤
      (𝒟[second]).bind (fun z => 𝒟[F z]) := by
    have hb := Measure.bind_mono_left hμ (Measurable.of_discrete (f := fun z => 𝒟[F z]))
    rw [Measure.bind_map Measurable.of_discrete.aemeasurable
      Measurable.of_discrete.aemeasurable] at hb
    exact hb
  have hcore : Pr{let z ← first; let y ← F (φ z)}[¬P y ∧ ¬bad z.2] ≤
      Pr{let z ← second; let y ← F z}[¬P y] := by
    rw [prEvent_bind_bind_eq_lintegral_of_discrete,
      prEvent_bind_bind_eq_lintegral_of_discrete]
    have hsupp : (fun z : α × σ₁ =>
        Pr{let y ← F (φ z)}[¬P y ∧ ¬bad z.2]).support ⊆ good := by
      intro z hz
      by_contra hb
      exact hz (by simp [good] at hb; simp [hb])
    calc
      _ = ∫⁻ z in good, Pr{let y ← F (φ z)}[¬P y ∧ ¬bad z.2] ∂𝒟[first] :=
        (setLIntegral_eq_of_support_subset hsupp).symm
      _ ≤ ∫⁻ z in good, Pr{let y ← F (φ z)}[¬P y] ∂𝒟[first] :=
        setLIntegral_mono_ae Measurable.of_discrete.aemeasurable
          (Filter.Eventually.of_forall fun z _ => prEvent_and_le_left _ _ _)
      _ = (((𝒟[first]).restrict good).bind (fun z => 𝒟[F (φ z)])) {y | ¬P y} := by
        rw [Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
        simp only [prEvent_eq_evalDist_of_discrete]
      _ ≤ ((𝒟[second]).bind (fun z => 𝒟[F z])) {y | ¬P y} :=
        Measure.le_iff.mp hpost _ MeasurableSet.of_discrete
      _ = ∫⁻ z, Pr{let y ← F z}[¬P y] ∂𝒟[second] := by
        rw [Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
        simp only [prEvent_eq_evalDist_of_discrete]
  -- Keep the original bad flag beside the sampled output until taking complements.
  let left : ProbComp (γ × σ₁) := do
    let z ← first
    let y ← F (φ z)
    pure (y, z.2)
  let right : ProbComp γ := second >>= F
  have hnot : Pr{let z ← left}[¬(P z.1 ∨ bad z.2)] ≤
      Pr{let y ← right}[¬P y] := by
    simpa only [left, right, prEvent_norm, not_or] using hcore
  have e₁ := prEvent_add_prEvent_not_eq_prEvent_true right P
  have e₂ := prEvent_add_prEvent_not_eq_prEvent_true left fun z => P z.1 ∨ bad z.2
  rw [prEvent_true_eq_one] at e₁ e₂
  have hfinal : Pr{let y ← right}[P y] ≤ Pr{let z ← left}[P z.1 ∨ bad z.2] := by
    refine ENNReal.le_of_add_le_add_right
      (prEvent_ne_top ((fun y => ¬P y) <$> right)) ?_
    rw [e₁, ← e₂]
    exact add_le_add le_rfl hnot
  simpa only [left, right, first, second, φ, prEvent_norm] using hfinal

end QueryImpl.DominatedUntilBad
