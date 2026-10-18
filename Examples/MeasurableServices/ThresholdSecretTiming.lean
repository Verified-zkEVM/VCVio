/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.MeasurableServices.ThresholdTiming
public import VCVio.ProgramLogic.Relational.ConditionalView
public import ToMathlib.Probability.UniformOn

/-!
# Threshold timing with the secret retained

A secret bit selects threshold `1/4` or `1/2`. The answer is public; whether the
sampler finished after its first bit is leakage. The actual chunk/resume program
returns within two bits, and its full joint law agrees with a three-bit finite
experiment. No kernel given only the public answer can simulate its timing while
retaining the secret. The contradiction compares positive-probability atoms
with the same public answer and different secret thresholds.
-/

public section

open MeasureTheory ProbabilityTheory UniformThreshold
open scoped ENNReal

namespace ThresholdSecretTiming

/-- A secret selector and two independent fair bits. -/
abbrev Tape := Bool × Bool × Bool

/-- The private selector chooses a half or a quarter threshold. -/
def threshold (secret : Bool) : ℚ := if secret then 1 / 2 else 1 / 4

/-- The returned Boolean as a function of the finite secret/bit experiment. -/
def answer (t : Tape) : Bool := if t.1 then !t.2.1 else !t.2.1 && !t.2.2

/-- Whether the actual threshold machine returns after its first bit. -/
def early (t : Tape) : Bool := t.1 || t.2.1

/-- Uniform independent secret and tape bits, including an unused second bit on early return. -/
noncomputable def law : Measure Tape := uniformOn Set.univ

instance : IsProbabilityMeasure law := by unfold law; infer_instance

/-- The first-bit classifier agrees with the early-completion observation. -/
theorem classify_first (t : Tape) :
    classify (threshold t.1) (Prefix.empty.push t.2.1) =
      if early t then some (answer t) else none := by
  rcases t with ⟨s, b, c⟩
  cases s <;> cases b <;> cases c <;>
    norm_num [threshold, answer, early, classify, Prefix.empty, Prefix.push,
      Prefix.lower, Prefix.upper]

/-- Both selected thresholds resolve within two bits. -/
theorem classify_second (t : Tape) :
    classify (threshold t.1) ((Prefix.empty.push t.2.1).push t.2.2) = some (answer t) := by
  rcases t with ⟨s, b, c⟩
  cases s <;> cases b <;> cases c <;>
    norm_num [threshold, answer, early, classify, Prefix.empty, Prefix.push,
      Prefix.lower, Prefix.upper]

/-- Observe completion after one bit, then resume the same retained chunk for one further bit. -/
def observed (secret : Bool) : PFunctor.FreeM coinSpec.toPFunctor
    (Option (Bool × Prefix) × Bool) := do
  let first ← (machine (threshold secret)).unrollChunk 1 Prefix.empty
  let last ← (machine (threshold secret)).resumeChunk 1 first
  pure (last.result, first.result.isSome)

/-- The half-threshold implementation returns after exactly one bit. -/
theorem observed_true : observed true = PFunctor.FreeM.liftBind () (fun b =>
    pure (some (!b, Prefix.empty.push b), true)) := by
  have hc : classify (threshold true) Prefix.empty = none := by
    norm_num [threshold, classify, Prefix.empty, Prefix.lower, Prefix.upper]
  unfold observed
  rw [PFunctor.DynSystem.DynComputation.unrollChunk_succ, machine_view, hc]
  simp only [← PFunctor.FreeM.bind_eq_bind]
  apply congrArg (PFunctor.FreeM.liftBind (P := coinSpec.toPFunctor) ())
  funext b
  cases b <;> norm_num [PFunctor.DynSystem.DynComputation.unrollChunk_zero,
    machine_view, threshold, classify, Prefix.empty, Prefix.push, Prefix.lower, Prefix.upper,
    PFunctor.FreeM.pure_bind, PFunctor.DynSystem.DynComputation.resumeChunk,
    PFunctor.DynSystem.DynComputation.Chunk.result]

/-- The quarter-threshold implementation uses a second bit only on the lower-half branch. -/
theorem observed_false : observed false = PFunctor.FreeM.liftBind () (fun b =>
    if b then pure (some (false, Prefix.empty.push true), true)
    else PFunctor.FreeM.liftBind () (fun c =>
      pure (some (!c, (Prefix.empty.push false).push c), false))) := by
  have hc : classify (threshold false) Prefix.empty = none := by
    norm_num [threshold, classify, Prefix.empty, Prefix.lower, Prefix.upper]
  unfold observed
  rw [PFunctor.DynSystem.DynComputation.unrollChunk_succ, machine_view, hc]
  simp only [← PFunctor.FreeM.bind_eq_bind]
  apply congrArg (PFunctor.FreeM.liftBind (P := coinSpec.toPFunctor) ())
  funext b
  cases b with
  | true =>
      norm_num [PFunctor.DynSystem.DynComputation.unrollChunk_zero,
        machine_view, threshold, classify, Prefix.empty, Prefix.push, Prefix.lower, Prefix.upper,
        PFunctor.FreeM.pure_bind, PFunctor.DynSystem.DynComputation.resumeChunk,
        PFunctor.DynSystem.DynComputation.Chunk.result]
  | false =>
      norm_num [PFunctor.DynSystem.DynComputation.unrollChunk,
        machine_view, threshold, classify, Prefix.empty, Prefix.push, Prefix.lower, Prefix.upper,
        PFunctor.FreeM.pure_bind, PFunctor.DynSystem.DynComputation.resumeChunk,
        PFunctor.DynSystem.DynComputation.Chunk.result]
      apply congrArg (PFunctor.FreeM.liftBind (P := coinSpec.toPFunctor) ())
      funext c
      cases c <;> norm_num [classify, Prefix.push, Prefix.lower, Prefix.upper,
        PFunctor.FreeM.pure_bind, PFunctor.DynSystem.DynComputation.Chunk.result]

attribute [local instance] coinAnswerMeasurableSpace

private theorem fair_query {X : Type} [MeasurableSpace X]
    (next : Bool → PFunctor.FreeM coinSpec.toPFunctor X) :
    𝒟[PFunctor.FreeM.liftBind (P := coinSpec.toPFunctor) () next] =
      (2 : ℝ≥0∞)⁻¹ • (𝒟[next false] + 𝒟[next true]) := by
  simp only [PFunctor.FreeM.evalDist_eq_denote]
  rw [PFunctor.FreeM.denote_liftBind _ _ Measurable.of_discrete.aemeasurable,
    show PFunctor.AnswerMeasure.toMeasure (P := coinSpec.toPFunctor) () =
      uniformOn (Set.univ : Set Bool) from
        OracleSpec.AnswerMeasure.toMeasure_eq_uniformOn (spec := coinSpec) (),
    Measure.bind_uniformOn_bool]

private theorem map_fair {X : Type} [MeasurableSpace X] (f : Bool → X) :
    (uniformOn (Set.univ : Set Bool)).map f =
      (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (f false) + Measure.dirac (f true)) := by
  rw [← Measure.bind_dirac_eq_map _ Measurable.of_discrete, Measure.bind_uniformOn_bool]

/-- The joint answer/timing law of the actual resumed machine equals the finite-bit model. -/
theorem observed_law (secret : Bool) :
    (𝒟[observed secret]).map (fun out => (out.1.map Prod.fst, out.2)) =
      (uniformOn (Set.univ : Set Bool)).bind (fun b =>
        (uniformOn (Set.univ : Set Bool)).map (fun c =>
          (some (answer (secret, b, c)), early (secret, b, c)))) := by
  cases secret with
  | false =>
      rw [observed_false, fair_query]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [fair_query, Measure.bind_uniformOn_bool]
      simp only [PFunctor.FreeM.evalDist_eq_denote, PFunctor.FreeM.denote_pure,
        Measure.map_smul _ Measurable.of_discrete.aemeasurable,
        Measure.map_add _ _ Measurable.of_discrete,
        Measure.map_dirac, Option.map_some,
        answer, early, Bool.false_eq_true, Bool.not_false, Bool.not_true,
        Bool.false_or, Bool.true_and, ↓reduceIte]
      rw [map_fair, map_fair]
      simp only [Bool.not_false, Bool.not_true, Bool.false_and,
        ← two_smul ℝ≥0∞, smul_smul]
      norm_num [ENNReal.inv_mul_cancel]
  | true =>
      rw [observed_true, fair_query, Measure.bind_uniformOn_bool]
      simp only [PFunctor.FreeM.evalDist_eq_denote, PFunctor.FreeM.denote_pure,
        Measure.map_smul _ Measurable.of_discrete.aemeasurable,
        Measure.map_add _ _ Measurable.of_discrete,
        Measure.map_dirac, Option.map_some,
        answer, early, Bool.true_or, Bool.not_false, Bool.not_true, ↓reduceIte]
      rw [map_fair, map_fair]
      simp only [← two_smul ℝ≥0∞, smul_smul]
      norm_num [ENNReal.inv_mul_cancel]

/-- The finite source law is three independent fair choices under any output map. -/
theorem map_law {X : Type} [MeasurableSpace X] (f : Tape → X) :
    law.map f = (uniformOn (Set.univ : Set Bool)).bind (fun secret =>
      (uniformOn (Set.univ : Set Bool)).bind (fun b =>
        (uniformOn (Set.univ : Set Bool)).map (fun c => f (secret, b, c)))) := by
  rw [law, uniformOn_univ_prod, Measure.prod_eq_of_sfinite,
    Measure.map_bind Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
  apply congrArg (Measure.bind (uniformOn (Set.univ : Set Bool)))
  funext secret
  rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete,
    uniformOn_univ_prod, Measure.prod_eq_of_sfinite,
    Measure.map_bind Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
  apply congrArg (Measure.bind (uniformOn (Set.univ : Set Bool)))
  funext b
  rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  rfl

/-- Sample a secret threshold and execute the observed machine, retaining the secret separately. -/
def experiment : PFunctor.FreeM coinSpec.toPFunctor ((Option Bool × Bool) × Bool) := do
  let secret ← PFunctor.FreeM.lift ()
  let out ← observed secret
  pure ((out.1.map Prod.fst, secret), out.2)

/-- Exact joint law of the executable secret, public answer and timing experiment. -/
theorem experiment_law :
    𝒟[experiment] = law.map (fun t => ((some (answer t), t.1), early t)) := by
  rw [map_law]
  unfold experiment
  change 𝒟[PFunctor.FreeM.liftBind (P := coinSpec.toPFunctor) () (fun secret =>
    (observed secret).bind (fun out => pure ((out.1.map Prod.fst, secret), out.2)))] = _
  rw [(PFunctor.FreeM.evalDist_eq_denote (P := coinSpec.toPFunctor)),
    PFunctor.FreeM.denote_liftBind (P := coinSpec.toPFunctor) _ _
      Measurable.of_discrete.aemeasurable,
    show PFunctor.AnswerMeasure.toMeasure (P := coinSpec.toPFunctor) () =
      uniformOn (Set.univ : Set Bool) from
        OracleSpec.AnswerMeasure.toMeasure_eq_uniformOn (spec := coinSpec) ()]
  apply congrArg (Measure.bind (uniformOn (Set.univ : Set Bool)))
  funext secret
  change PFunctor.FreeM.denote (PFunctor.FreeM.bind (observed secret)
    (Pure.pure ∘ (fun out : Option (Bool × Prefix) × Bool =>
      ((out.1.map Prod.fst, secret), out.2)))) = _
  rw [PFunctor.FreeM.bind_pure_comp]
  rw [PFunctor.FreeM.denote_map_of_measurable (P := coinSpec.toPFunctor)
    (α := Option (Bool × Prefix) × Bool) _ _ Measurable.of_discrete]
  rw [← (PFunctor.FreeM.evalDist_eq_denote (P := coinSpec.toPFunctor))]
  have hmap := congrArg (Measure.map (fun out : Option Bool × Bool => ((out.1, secret), out.2)))
    (observed_law secret)
  rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete,
    Measure.map_bind Measurable.of_discrete.aemeasurable
      Measurable.of_discrete.aemeasurable] at hmap
  simpa only [Measure.map_map Measurable.of_discrete Measurable.of_discrete, Function.comp_def]
    using hmap

/-- Early completion reveals secret information beyond the permitted public answer. -/
theorem no_simulator (sim : Kernel (Option Bool) Bool) [IsSFiniteKernel sim] :
    ¬ SimulatesView (fun t : Tape => t.1) (fun t => some (answer t)) early sim law := by
  intro hs
  have hfalse := hs.measure_atom_inter Measurable.of_discrete Measurable.of_discrete
    Measurable.of_discrete false (some true) (measurableSet_singleton true)
  have htrue := hs.measure_atom_inter Measurable.of_discrete Measurable.of_discrete
    Measurable.of_discrete true (some true) (measurableSet_singleton true)
  simp only [Option.some.injEq] at hfalse htrue
  have hfe : {t : Tape | answer t = true ∧ t.1 = false ∧ early t ∈ ({true} : Set Bool)} =
      ∅ := by
    ext ⟨s, b, c⟩
    cases s <;> cases b <;> cases c <;> decide
  have hf : {t : Tape | answer t = true ∧ t.1 = false} = {(false, false, false)} := by
    ext ⟨s, b, c⟩
    cases s <;> cases b <;> cases c <;> decide
  have hte : {t : Tape | answer t = true ∧ t.1 = true ∧ early t ∈ ({true} : Set Bool)} =
      {(true, false, false), (true, false, true)} := by
    ext ⟨s, b, c⟩
    cases s <;> cases b <;> cases c <;> decide
  have ht : {t : Tape | answer t = true ∧ t.1 = true} =
      {(true, false, false), (true, false, true)} := by
    ext ⟨s, b, c⟩
    cases s <;> cases b <;> cases c <;> decide
  rw [hfe, hf] at hfalse
  rw [hte, ht] at htrue
  norm_num [law, uniformOn_univ] at hfalse htrue
  have hzero : ({(true, false, false), (true, false, true)} : Set Tape) = ∅ := by
    simpa [hfalse] using htrue
  have hm : (true, false, false) ∈ ({(true, false, false), (true, false, true)} : Set Tape) :=
    by simp
  rw [hzero] at hm
  exact hm

/-- No public-answer simulator reproduces timing for the actual executable experiment. -/
theorem no_experiment_simulator (sim : Kernel (Option Bool) Bool) [IsSFiniteKernel sim] :
    ¬ SimulatesView (fun out : (Option Bool × Bool) × Bool => out.1.2)
      (fun out => out.1.1) Prod.snd sim 𝒟[experiment] := by
  intro h
  rw [experiment_law] at h
  have hp := h.of_map Measurable.of_discrete Measurable.of_discrete
    Measurable.of_discrete Measurable.of_discrete
  exact no_simulator sim hp

end ThresholdSecretTiming
