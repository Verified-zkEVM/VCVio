/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.Retry
public import VCVio.CryptoFoundations.IncomparableEncoding.NonMaximum
public import VCVio.EvalDist.Instances.OptionT

/-!
# Encoding retry foundation probes

Finite controls pin first-success stopping, retry exhaustion and the ordered consumed prefix.
-/

public section

namespace VCVioTest.IncomparableEncodingRetry

open IncomparableEncoding VCVio.Algorithms

/-- A singleton one-digit word. -/
@[expose] def word : Codeword 1 2 := fun _ => 0

/-- The false randomizer fails and the true randomizer returns the singleton word. -/
@[expose] def enc : IncomparableEncoding Unit Unit Bool Unit 1 2 where
  code := {word}
  incomparable := by
    intro x hx y hy hne
    exact (hne ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm)).elim
  encode _ _ r _ := if r then some word else none
  mem_code_of_encode_eq_some := by
    intro _ _ r _ x h
    cases r <;> simp_all [eq_comm]

/-- A stream sampler exposes precisely which draws are consumed. -/
@[expose] def draw : StateM (List Bool) Bool := fun s =>
  match s with
  | [] => (false, [])
  | r :: rest => (r, rest)

/-- A zero budget leaves even a successful first draw unconsumed. -/
theorem zero_draws :
    (enc.retry draw () () () 0).run [true] = (none, [true]) := rfl

/-- One attempt returns its successful randomizer without consuming the tail. -/
theorem one_draw :
    (enc.retry draw () () () 1).run [true, false] = (some (word, true), [false]) := rfl

/-- Early success stops despite a remaining budget. -/
theorem early_success :
    (enc.retry draw () () () 3).run [true, false] = (some (word, true), [false]) := rfl

/-- Returned failure consumes one draw before the next draw succeeds. -/
theorem failure_then_success :
    (enc.retry draw () () () 3).run [false, true, false] =
      (some (word, true), [false]) := rfl

/-- The indexed sampler reaches its second value, then stops before the third. -/
theorem indexed_second_attempt_trace :
    enc.retryIndexed (m := Id) () () () 3 (fun i => i.val == 1) =
      FirstSuccess.Result.success (word, true) 2 [false, true] := rfl

/-- The result proves both the one-based attempt and ordered consumed prefix are nontrivial. -/
theorem indexed_second_attempt_not_first :
    enc.retryIndexed (m := Id) () () () 3 (fun i => i.val == 1) ≠
      FirstSuccess.Result.success (word, true) 1 [true] := by
  intro equality
  have impossible : (2 : ℕ) = 1 := by
    simpa only [indexed_second_attempt_trace] using
      congrArg (fun result : FirstSuccess.Result Bool (Codeword 1 2 × Bool) =>
        match result with
        | .success _ attempt _ => attempt
        | .exhausted _ => 0) equality
  omega

/-- Zero budget never evaluates the indexed sampler. -/
theorem indexed_zero_trace :
    enc.retryIndexed (m := Id) () () () 0 (fun i => nomatch i) =
      FirstSuccess.Result.exhausted [] := rfl

/-- An always-failing finite sampler returns the complete ordered consumed list. -/
theorem indexed_exhaustion_trace :
    enc.retryIndexed (m := Id) () () () 3 (fun i => (i.val == 0) && false) =
      FirstSuccess.Result.exhausted [false, false, false] := rfl

/-- The stateful fixed sampler is the exact output observation of the indexed operation with a
constant sampler. -/
theorem fixed_sampler_specialization :
    (enc.retry draw () () () 3).run [false, true, false] =
      (FirstSuccess.Result.output <$>
        enc.retryIndexed () () () 3 (fun _ => draw)).run [false, true, false] := by
  rw [enc.retry_eq_indexed_constant draw () () () 3]

/-- Canonical uniform randomizers are uniform (`uniformSampler_uniformSample`). -/
theorem uniform_randomizers : UniformSampler ProbCompRuntime.probComp ($ᵗ Bool) :=
  uniformSampler_uniformSample Bool

/-- Boolean and proposition-valued constant observations retain the same returned mass. -/
theorem constant_observation_mass_eq {m : Type → Type*} [Monad m] {α : Type}
    (runtime : ProbCompRuntime m) (sample : m α) :
    runtime.evalDist ((fun _ => true) <$> sample) {true} =
      runtime.evalDist ((fun _ => True) <$> sample) {True} := by
  let : MeasurableSpace α := ⊤
  rw [runtime.evalDist_map (fun _ : α => true) Measurable.of_discrete sample,
    runtime.evalDist_map (fun _ : α => True) Measurable.of_discrete sample]
  rw [MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true),
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton True)]
  congr 1
  ext x
  simp

/-- An optional probabilistic computation observes aborts as missing output mass. -/
@[expose] noncomputable def optionalRuntime : ProbCompRuntime (OptionT ProbComp) where
  toSemanticsVia := SemanticsVia.ofEvalDistSemantics (OptionT ProbComp)
  toProbCompLift := ProbCompLift.ofMonadLift (OptionT ProbComp)
  evalDist_map_eq _f hf mx := evalDist_map mx hf

/-- The optional runtime satisfies the same sampling laws as the canonical runtime. -/
theorem optional_sampling_laws : optionalRuntime.SamplingLaws where
  pure_eq x := by
    simp [optionalRuntime, ProbCompRuntime.evalDist,
      SemanticsVia.ofEvalDistSemantics_evalDist, evalDist_pure]
  bind_eq {α} {β} c f p := by
    let : MeasurableSpace α := ⊤
    simp only [optionalRuntime, ProbCompRuntime.evalDist,
      SemanticsVia.ofEvalDistSemantics_evalDist]
    simpa only [← prEvent_eq_evalDist_map] using
      prEvent_bind_eq_lintegral_of_discrete c f p

/-- An explicit optional abort has missing mass one. No operational divergence is asserted. -/
theorem abort_missing_mass :
    VCVio.Algorithms.FirstSuccess.missingMass optionalRuntime
      (failure : OptionT ProbComp Bool) = 1 := by
  simp [VCVio.Algorithms.FirstSuccess.missingMass, optionalRuntime, ProbCompRuntime.evalDist,
    SemanticsVia.ofEvalDistSemantics_evalDist]

/-- Zero retries return exhaustion without evaluating the always-aborting sampler. -/
theorem retry_zero_abort_missing_mass :
    FirstSuccess.missingMass optionalRuntime
      (enc.retry (failure : OptionT ProbComp Bool) () () () 0) = 0 :=
  FirstSuccess.missingMass_runWith_zero optionalRuntime optional_sampling_laws
    (failure : OptionT ProbComp Bool) (enc.attempt () () ())

/-- A nonempty retry budget preserves the missing mass of an always-aborting sampler. -/
theorem retry_abort_missing_mass :
    FirstSuccess.missingMass optionalRuntime
      (enc.retry (failure : OptionT ProbComp Bool) () () () 1) = 1 := by
  rw [retry, FirstSuccess.missingMass_runWith_eq_mul_sum optionalRuntime optional_sampling_laws]
  simp [abort_missing_mass]

/-- A singleton nonmaximum code satisfies the conditional output premise without two words. -/
theorem singleton_nonMaximum : enc.NoMaximumOutput := by
  intro pp msg r ep result hresult
  have hmem := enc.mem_code_of_encode_eq_some hresult
  have heq : result = word := by simpa [enc] using hmem
  subst result
  exact ⟨0, by decide⟩

/-- The conditional output premise does not imply two global codewords. -/
theorem singleton_not_two :
    ¬ ∃ x y : Codeword 1 2, x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y := by
  rintro ⟨x, y, hx, hy, hne⟩
  have hx' : x = word := by simpa [enc] using hx
  have hy' : y = word := by simpa [enc] using hy
  exact hne (hx'.trans hy'.symm)

/-- One canonical draw fails to encode with probability exactly one half. -/
theorem canonical_failureMass (pp : Unit) (msg : Unit) (ep : Unit) :
    enc.failureMass ProbCompRuntime.probComp ($ᵗ Bool) pp msg ep = 2⁻¹ := by
  have hclass : (fun r : Bool => (enc.encode pp msg r ep).isNone) = fun r => !r := by
    funext r
    cases r <;> rfl
  rw [failureMass_eq_probability, hclass, ProbCompRuntime.probComp_evalDist,
    evalDist_map _ Measurable.of_discrete,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true)]
  have hpre : (fun r : Bool => !r) ⁻¹' ({true} : Set Bool) = {false} := by
    ext r
    cases r <;> simp
  rw [hpre]
  simp

/-- Canonical randomizers have pointwise returned encoding failure at most one half. -/
theorem canonical_half : enc.CanonicalErrorAtMost (2⁻¹) := fun pp msg ep =>
  (canonical_failureMass pp msg ep).le

/-- The uniform presentation is exactly the canonical pointwise error bound. -/
theorem uniform_half : enc.UniformErrorAtMost ProbCompRuntime.probComp ($ᵗ Bool) (2⁻¹) :=
  (enc.uniformErrorAtMost_uniformSample_iff (2⁻¹)).2 canonical_half

/-- Canonical pointwise error bounds retry exhaustion without an extra uniformity argument. -/
theorem canonical_retry_bound (k : ℕ) :
    Retry.exhaustionMass enc ProbCompRuntime.probComp ($ᵗ Bool) () () () k ≤ (2⁻¹) ^ k := by
  rw [Retry.exhaustionMass_eq_pow enc _ ProbCompRuntime.samplingLaws_probComp]
  exact pow_le_pow_left' (canonical_half () () ()) k

/-- Two canonical retries are both exhausted with probability exactly one quarter. -/
theorem canonical_exhaustion_two :
    Retry.exhaustionMass enc ProbCompRuntime.probComp ($ᵗ Bool) () () () 2 = 4⁻¹ := by
  rw [Retry.exhaustionMass_eq_pow enc _ ProbCompRuntime.samplingLaws_probComp,
    canonical_failureMass, ← ENNReal.inv_pow]
  norm_num

/-- Two canonical retries succeed with probability exactly three quarters. -/
theorem canonical_success_two :
    Retry.successMass enc ProbCompRuntime.probComp ($ᵗ Bool) () () () 2 = 1 - 4⁻¹ := by
  rw [Retry.successMass_eq_one_sub_pow enc _ ProbCompRuntime.samplingLaws_probComp _
    (uniformSampler_uniformSample Bool).1, canonical_failureMass, ← ENNReal.inv_pow]
  norm_num

end VCVioTest.IncomparableEncodingRetry
