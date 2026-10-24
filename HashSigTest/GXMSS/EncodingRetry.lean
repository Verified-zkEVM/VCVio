/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Encoding.Retry
import VCVio.EvalDist.Instances.OptionT

/-!
# Encoding retry foundation probes

Registered audit root for the corresponding deterministic or probability foundations.
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

/-- Canonical uniform randomizers reuse the established uniform sampler theorem. -/
theorem uniform_randomizers : UniformSampler ProbCompRuntime.probComp ($ᵗ Bool) :=
  uniformSampler_uniformSample Bool

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

/-- A nonempty retry budget preserves the missing mass of an always-aborting sampler. -/
theorem retry_abort_missing_mass :
    Retry.missingMass enc optionalRuntime (failure : OptionT ProbComp Bool) () () () 1 = 1 := by
  rw [Retry.missingMass_eq_mul_sum enc optionalRuntime optional_sampling_laws]
  simp [abort_missing_mass]

end GXMSS.Encoding.RetryProbe
