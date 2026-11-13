/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Encoding.Retry
public import VCVio.EvalDist.Instances.OptionT

/-!
# Encoding retry foundation probes

Finite controls pin first-success stopping, retry exhaustion and the ordered consumed prefix.
-/

public section

namespace GXMSS.Encoding.RetryProbe

open IncomparableEncoding

/-- A singleton one-digit word. -/
@[expose] def word : Codeword 1 2 := fun _ => 0

/-- The false randomizer fails and the true randomizer returns the singleton word. -/
@[expose] def enc : IncomparableEncoding Unit Unit Bool Unit 1 2 where
  code := {word}
  incomparable := by
    intro x hx y hy hne
    exact (hne ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm)).elim
  encode _ _ r _ := if r then some ⟨word, by simp⟩ else none

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
      IncomparableEncoding.IndexedResult.success word true 2 [false, true] := rfl

/-- The result proves both the one-based attempt and ordered consumed prefix are nontrivial. -/
theorem indexed_second_attempt_not_first :
    enc.retryIndexed (m := Id) () () () 3 (fun i => i.val == 1) ≠
      IncomparableEncoding.IndexedResult.success word true 1 [true] := by
  intro equality
  have impossible : (2 : ℕ) = 1 := by
    simpa only [indexed_second_attempt_trace] using
      congrArg (fun result : IncomparableEncoding.IndexedResult Bool 1 2 =>
        match result with
        | .success _ _ attempt _ => attempt
        | .exhausted _ => 0) equality
  omega

/-- Zero budget never evaluates the indexed sampler. -/
theorem indexed_zero_trace :
    enc.retryIndexed (m := Id) () () () 0 (fun i => nomatch i) =
      IncomparableEncoding.IndexedResult.exhausted [] := rfl

/-- An always-failing finite sampler returns the complete ordered consumed list. -/
theorem indexed_exhaustion_trace :
    enc.retryIndexed (m := Id) () () () 3 (fun i => (i.val == 0) && false) =
      IncomparableEncoding.IndexedResult.exhausted [false, false, false] := rfl

/-- The existing stateful fixed sampler is the exact output observation of the
shared indexed operation with a constant sampler. -/
theorem fixed_sampler_specialization :
    (enc.retry draw () () () 3).run [false, true, false] =
      (IncomparableEncoding.IndexedResult.output <$>
        enc.retryIndexed () () () 3 (fun _ => draw)).run [false, true, false] := by
  rw [enc.retry_eq_indexed_constant draw () () () 3]

/-- Canonical uniform randomizers reuse the established uniform sampler theorem. -/
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
theorem optional_sampling_laws : SamplingLaws optionalRuntime where
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
    IncomparableEncoding.missingMass optionalRuntime (failure : OptionT ProbComp Bool) = 1 := by
  simp [IncomparableEncoding.missingMass, optionalRuntime, ProbCompRuntime.evalDist,
    SemanticsVia.ofEvalDistSemantics_evalDist]

/-- Zero retries return exhaustion without evaluating the always-aborting sampler. -/
theorem retry_zero_abort_missing_mass :
    Retry.missingMass enc optionalRuntime (failure : OptionT ProbComp Bool) () () () 0 = 0 :=
  Retry.missingMass_zero enc optionalRuntime optional_sampling_laws
    (failure : OptionT ProbComp Bool) () () ()

/-- A nonempty retry budget preserves the missing mass of an always-aborting sampler. -/
theorem retry_abort_missing_mass :
    Retry.missingMass enc optionalRuntime (failure : OptionT ProbComp Bool) () () () 1 = 1 := by
  rw [Retry.missingMass_eq_mul_sum enc optionalRuntime optional_sampling_laws]
  simp [abort_missing_mass]

end GXMSS.Encoding.RetryProbe
