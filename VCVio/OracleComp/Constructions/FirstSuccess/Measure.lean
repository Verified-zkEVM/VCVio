/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.Algorithms.FirstSuccess.Basic
public import VCVio.OracleComp.ProbComp.SamplingLaws
public import ToMathlib.MeasureTheory.Measure.Bool
public import Mathlib.Algebra.Ring.GeomSum

/-!
# First-success output and missing-mass laws

Returned failure and returned success partition the mass of a draw; its missing execution mass
is a separate observation. Bounded retries multiply returned exhaustion probabilities and sum
success or missing mass along the prefixes of returned failures. Runtime sampling laws are
explicit, and none of these observations condition on termination.
-/

public section

namespace VCVio.Algorithms.FirstSuccess

open ENNReal

universe v

variable {m : Type → Type v} [Monad m] {R α : Type}

/-- Interpret the Boolean returned-failure classifier after drawing a value. -/
@[expose] noncomputable def failureIndicatorDist (runtime : ProbCompRuntime m)
    (sample : m R) (accept : R → Option α) : MeasureTheory.Measure Bool :=
  runtime.evalDist ((fun draw => (accept draw).isNone) <$> sample)

/-- Unconditional mass of returned failure. -/
@[expose] noncomputable def failureMass (runtime : ProbCompRuntime m)
    (sample : m R) (accept : R → Option α) : ℝ≥0∞ :=
  failureIndicatorDist runtime sample accept {true}

/-- Unconditional mass of returned success. -/
@[expose] noncomputable def successMass (runtime : ProbCompRuntime m)
    (sample : m R) (accept : R → Option α) : ℝ≥0∞ :=
  failureIndicatorDist runtime sample accept {false}

/-- Missing execution mass, observed through the constant Boolean map. -/
@[expose] noncomputable def missingMass (runtime : ProbCompRuntime m) (sample : m R) : ℝ≥0∞ :=
  1 - runtime.evalDist ((fun _ => true) <$> sample) {true}

/-- Returned failure, missing execution and returned success partition probability one. -/
theorem failureMass_add_missingMass_add_successMass (runtime : ProbCompRuntime m)
    (sample : m R) (accept : R → Option α) :
    failureMass runtime sample accept + missingMass runtime sample +
      successMass runtime sample accept = 1 := by
  let : MeasurableSpace R := ⊤
  unfold failureMass successMass failureIndicatorDist missingMass
  rw [add_right_comm,
    runtime.evalDist_map (fun draw => (accept draw).isNone) Measurable.of_discrete,
    MeasureTheory.Measure.apply_true_add_apply_false,
    runtime.evalDist_map (fun _ : R => true) Measurable.of_discrete]
  simp only [MeasureTheory.Measure.map_apply Measurable.of_discrete MeasurableSet.univ,
    Set.preimage_univ,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true)]
  have hpreimage : (fun _ : R => true) ⁻¹' ({true} : Set Bool) = Set.univ := by ext; simp
  rw [hpreimage, add_comm]
  exact tsub_add_cancel_of_le (runtime.evalDist_apply_univ_le_one _)

/-- Returned failure is precisely the event that classification returns `none`. -/
theorem failureMass_eq_probability (runtime : ProbCompRuntime m)
    (sample : m R) (accept : R → Option α) :
    failureMass runtime sample accept =
      runtime.evalDist ((fun draw => accept draw = none) <$> sample) {True} := by
  let : MeasurableSpace R := ⊤
  rw [failureMass, failureIndicatorDist,
    runtime.evalDist_map (fun draw => (accept draw).isNone) Measurable.of_discrete,
    runtime.evalDist_map (fun draw => accept draw = none) Measurable.of_discrete]
  rw [MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true),
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton True)]
  congr 1
  ext draw
  cases accept draw <;> simp

/-- Returned success is precisely the event that classification is not `none`. -/
theorem successMass_eq_probability (runtime : ProbCompRuntime m)
    (sample : m R) (accept : R → Option α) :
    successMass runtime sample accept =
      runtime.evalDist ((fun draw => (accept draw).isNone = false) <$> sample) {True} := by
  let : MeasurableSpace R := ⊤
  rw [successMass, failureIndicatorDist,
    runtime.evalDist_map (fun draw => (accept draw).isNone) Measurable.of_discrete,
    runtime.evalDist_map (fun draw => (accept draw).isNone = false) Measurable.of_discrete]
  rw [MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton false),
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton True)]
  congr 1
  ext draw
  cases accept draw <;> simp

/-- Zero retries return exhaustion with unit mass and perform no draw. -/
theorem failureMass_runWith_zero (runtime : ProbCompRuntime m)
    (laws : runtime.SamplingLaws) (sample : m R) (accept : R → Option α) :
    failureMass runtime (runWith sample accept 0) id = 1 := by
  let : MeasurableSpace (Option α) := ⊤
  rw [failureMass_eq_probability, runWith_zero,
    runtime.evalDist_map (fun o : Option α => id o = none) Measurable.of_discrete, laws.pure_eq]
  simp

/-- Zero retries have no missing execution mass. -/
theorem missingMass_runWith_zero (runtime : ProbCompRuntime m)
    (laws : runtime.SamplingLaws) (sample : m R) (accept : R → Option α) :
    missingMass runtime (runWith sample accept 0) = 0 := by
  let : MeasurableSpace (Option α) := ⊤
  rw [missingMass, runWith_zero,
    runtime.evalDist_map (fun _ : Option α => true) Measurable.of_discrete, laws.pure_eq]
  simp

/-- Zero retries have no returned successful output. -/
theorem successMass_runWith_zero (runtime : ProbCompRuntime m)
    (laws : runtime.SamplingLaws) (sample : m R) (accept : R → Option α) :
    successMass runtime (runWith sample accept 0) id = 0 := by
  let : MeasurableSpace (Option α) := ⊤
  rw [successMass, failureIndicatorDist, runWith_zero,
    runtime.evalDist_map (fun o : Option α => (id o).isNone) Measurable.of_discrete, laws.pure_eq]
  simp

/-- Each attempt multiplies exhaustion mass by one-draw returned failure mass. -/
theorem failureMass_runWith_succ (runtime : ProbCompRuntime m)
    (laws : runtime.SamplingLaws) (sample : m R) (accept : R → Option α) (k : ℕ) :
    failureMass runtime (runWith sample accept (k + 1)) id =
      failureMass runtime sample accept * failureMass runtime (runWith sample accept k) id := by
  classical
  let : MeasurableSpace R := ⊤
  let : MeasurableSpace (Option α) := ⊤
  rw [failureMass_eq_probability, runWith_succ, laws.bind_eq]
  rw [failureMass, failureIndicatorDist,
    runtime.evalDist_map (fun draw => (accept draw).isNone) Measurable.of_discrete,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true)]
  have hpoint (draw : R) :
      runtime.evalDist ((fun o : Option α => id o = none) <$>
        match accept draw with
        | some value => pure (some value)
        | none => runWith sample accept k) {True} =
        if (accept draw).isNone then failureMass runtime (runWith sample accept k) id else 0 := by
    cases h : accept draw with
    | none => simp [failureMass_eq_probability]
    | some value =>
      rw [runtime.evalDist_map (fun o : Option α => id o = none)
        Measurable.of_discrete, laws.pure_eq]
      simp
  trans ∫⁻ draw, if (accept draw).isNone then
    failureMass runtime (runWith sample accept k) id else 0 ∂runtime.evalDist sample
  · apply MeasureTheory.lintegral_congr
    intro draw
    exact hpoint draw
  let s : Set R := (fun draw => (accept draw).isNone) ⁻¹' {true}
  calc
    (∫⁻ draw, if (accept draw).isNone then
        failureMass runtime (runWith sample accept k) id else 0 ∂runtime.evalDist sample) =
        ∫⁻ draw, s.indicator
          (fun _ => failureMass runtime (runWith sample accept k) id) draw
          ∂runtime.evalDist sample := by
      apply MeasureTheory.lintegral_congr
      intro draw
      cases h : accept draw <;> simp [s, h]
    _ = failureMass runtime (runWith sample accept k) id * runtime.evalDist sample s :=
      MeasureTheory.lintegral_indicator_const MeasurableSet.of_discrete _
    _ = runtime.evalDist sample s * failureMass runtime (runWith sample accept k) id := mul_comm _ _

/-- Exhaustion is the exact power of the one-draw returned failure mass. -/
theorem failureMass_runWith_eq_pow (runtime : ProbCompRuntime m)
    (laws : runtime.SamplingLaws) (sample : m R) (accept : R → Option α) (k : ℕ) :
    failureMass runtime (runWith sample accept k) id = (failureMass runtime sample accept) ^ k := by
  induction k with
  | zero => simpa only [pow_zero] using failureMass_runWith_zero runtime laws sample accept
  | succ k ih => rw [failureMass_runWith_succ runtime laws, ih, pow_succ']

/-- A further attempt either succeeds immediately or succeeds after returned failure. -/
theorem successMass_runWith_succ (runtime : ProbCompRuntime m)
    (laws : runtime.SamplingLaws) (sample : m R) (accept : R → Option α) (k : ℕ) :
    successMass runtime (runWith sample accept (k + 1)) id = successMass runtime sample accept +
      failureMass runtime sample accept * successMass runtime (runWith sample accept k) id := by
  classical
  let : MeasurableSpace R := ⊤
  let : MeasurableSpace (Option α) := ⊤
  rw [successMass_eq_probability, runWith_succ, laws.bind_eq]
  rw [successMass, failureMass, failureIndicatorDist,
    runtime.evalDist_map (fun draw => (accept draw).isNone) Measurable.of_discrete]
  rw [MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton false),
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true)]
  have hpoint (draw : R) :
      runtime.evalDist ((fun o : Option α => (id o).isNone = false) <$>
        match accept draw with
        | some value => pure (some value)
        | none => runWith sample accept k) {True} =
        if (accept draw).isNone then successMass runtime (runWith sample accept k) id else 1 := by
    cases h : accept draw with
    | none => simpa using (successMass_eq_probability runtime (runWith sample accept k) id).symm
    | some value =>
      rw [runtime.evalDist_map (fun o : Option α => (id o).isNone = false)
        Measurable.of_discrete, laws.pure_eq]
      simp
  trans ∫⁻ draw, if (accept draw).isNone then
    successMass runtime (runWith sample accept k) id else 1 ∂runtime.evalDist sample
  · apply MeasureTheory.lintegral_congr
    intro draw
    exact hpoint draw
  let st : Set R := (fun draw => (accept draw).isNone) ⁻¹' {true}
  let sf : Set R := (fun draw => (accept draw).isNone) ⁻¹' {false}
  calc
    (∫⁻ draw, if (accept draw).isNone then
        successMass runtime (runWith sample accept k) id else 1 ∂runtime.evalDist sample) =
        ∫⁻ draw, sf.indicator (fun _ => 1) draw +
          st.indicator (fun _ => successMass runtime (runWith sample accept k) id) draw
          ∂runtime.evalDist sample := by
      apply MeasureTheory.lintegral_congr
      intro draw
      cases h : accept draw <;> simp [st, sf, h]
    _ = (∫⁻ draw, sf.indicator (fun _ => 1) draw ∂runtime.evalDist sample) +
        ∫⁻ draw, st.indicator (fun _ => successMass runtime (runWith sample accept k) id) draw
          ∂runtime.evalDist sample := by
      rw [MeasureTheory.lintegral_add_left
        (measurable_const.indicator MeasurableSet.of_discrete)]
    _ = runtime.evalDist sample sf + runtime.evalDist sample st *
        successMass runtime (runWith sample accept k) id := by
      rw [MeasureTheory.lintegral_indicator_const MeasurableSet.of_discrete,
        MeasureTheory.lintegral_indicator_const MeasurableSet.of_discrete]
      simp [mul_comm]

/-- Missing mass is missing the first draw, or returning failure then missing a later draw. -/
theorem missingMass_runWith_succ (runtime : ProbCompRuntime m)
    (laws : runtime.SamplingLaws) (sample : m R) (accept : R → Option α) (k : ℕ) :
    missingMass runtime (runWith sample accept (k + 1)) = missingMass runtime sample +
      failureMass runtime sample accept * missingMass runtime (runWith sample accept k) := by
  have hnext := failureMass_add_missingMass_add_successMass runtime
    (runWith sample accept (k + 1)) id
  have hprev := failureMass_add_missingMass_add_successMass runtime (runWith sample accept k) id
  have hone := failureMass_add_missingMass_add_successMass runtime sample accept
  rw [failureMass_runWith_succ runtime laws, successMass_runWith_succ runtime laws] at hnext
  let common :=
    failureMass runtime sample accept * failureMass runtime (runWith sample accept k) id +
    successMass runtime sample accept +
    failureMass runtime sample accept * successMass runtime (runWith sample accept k) id
  have hleft : common + missingMass runtime (runWith sample accept (k + 1)) = 1 := by
    simpa [common, add_assoc, add_left_comm, add_comm] using hnext
  have hright : common + (missingMass runtime sample +
      failureMass runtime sample accept * missingMass runtime (runWith sample accept k)) = 1 := by
    calc
      _ = failureMass runtime sample accept *
            (failureMass runtime (runWith sample accept k) id +
              missingMass runtime (runWith sample accept k) +
              successMass runtime (runWith sample accept k) id) +
          missingMass runtime sample + successMass runtime sample accept := by dsimp [common]; ring
      _ = 1 := by rw [hprev]; simpa using hone
  have hcommon_le : common ≤ 1 := (le_add_right le_rfl).trans (le_of_eq hleft)
  have hcommon_ne_top : common ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hcommon_le
  apply (ENNReal.add_left_inj hcommon_ne_top).mp
  simpa [add_comm] using hleft.trans hright.symm

/-- Missing mass accumulates along prefixes of returned failures. -/
theorem missingMass_runWith_eq_mul_sum (runtime : ProbCompRuntime m)
    (laws : runtime.SamplingLaws) (sample : m R) (accept : R → Option α) (k : ℕ) :
    missingMass runtime (runWith sample accept k) = missingMass runtime sample *
      ∑ j ∈ Finset.range k, (failureMass runtime sample accept) ^ j := by
  induction k with
  | zero =>
    simpa only [Finset.range_zero, Finset.sum_empty, mul_zero] using
      missingMass_runWith_zero runtime laws sample accept
  | succ k ih =>
    rw [missingMass_runWith_succ runtime laws, ih, geom_sum_succ]
    simp [mul_add, mul_left_comm, add_comm]

/-- Successful output mass accumulates along the same returned-failure prefixes. -/
theorem successMass_runWith_eq_mul_sum (runtime : ProbCompRuntime m)
    (laws : runtime.SamplingLaws) (sample : m R) (accept : R → Option α) (k : ℕ) :
    successMass runtime (runWith sample accept k) id = successMass runtime sample accept *
      ∑ j ∈ Finset.range k, (failureMass runtime sample accept) ^ j := by
  induction k with
  | zero =>
    simpa only [Finset.range_zero, Finset.sum_empty, mul_zero] using
      successMass_runWith_zero runtime laws sample accept
  | succ k ih =>
    rw [successMass_runWith_succ runtime laws, ih, geom_sum_succ]
    simp [mul_add, mul_left_comm, add_comm]

/-- A sampler with no missing mass gives retries with no missing mass. -/
theorem missingMass_runWith_eq_zero (runtime : ProbCompRuntime m)
    (laws : runtime.SamplingLaws) (sample : m R) (accept : R → Option α)
    (hl : missingMass runtime sample = 0) (k : ℕ) :
    missingMass runtime (runWith sample accept k) = 0 := by
  rw [missingMass_runWith_eq_mul_sum runtime laws, hl, zero_mul]

/-- Under losslessness, success has one minus the exact exhaustion mass. -/
theorem successMass_runWith_eq_one_sub_pow (runtime : ProbCompRuntime m)
    (laws : runtime.SamplingLaws) (sample : m R) (accept : R → Option α)
    (hl : missingMass runtime sample = 0) (k : ℕ) :
    successMass runtime (runWith sample accept k) id =
      1 - (failureMass runtime sample accept) ^ k := by
  have h := failureMass_add_missingMass_add_successMass runtime (runWith sample accept k) id
  rw [missingMass_runWith_eq_zero runtime laws sample accept hl, add_zero,
    failureMass_runWith_eq_pow runtime laws] at h
  exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top
    (le_of_add_le_left (le_of_eq h))) (add_comm _ _ |>.trans h)

/-- A one-draw failure bound yields its power bound on returned exhaustion. -/
theorem failureMass_runWith_le_pow (runtime : ProbCompRuntime m)
    (laws : runtime.SamplingLaws) (sample : m R) (accept : R → Option α)
    (δ : ℝ≥0∞) (h : failureMass runtime sample accept ≤ δ) (k : ℕ) :
    failureMass runtime (runWith sample accept k) id ≤ δ ^ k := by
  rw [failureMass_runWith_eq_pow runtime laws]
  exact pow_le_pow_left' h k

end VCVio.Algorithms.FirstSuccess
