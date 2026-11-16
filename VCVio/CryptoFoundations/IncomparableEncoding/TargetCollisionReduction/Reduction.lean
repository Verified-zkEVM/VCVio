/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetCollisionReduction.Simulation

/-!
# Encoding collision advantage transport

The named hash adversary preserves the actual public-seed draw and both resource capacities.
Its Boolean observation on the common returned sample bounds the source winning mass.
-/

public section

namespace IncomparableEncoding.TargetCollisionReduction

open OracleComp OracleSpec TargetCollisionResistance TweakableHash

variable {PP M R E Tweak Y : Type} {n radix : ℕ}

/-- The hash adversary runs the source adversary under the translated challenge oracle, then
reports the first successful source target's index and the same candidate pair. -/
@[expose] def reduction [SampleableType R] [DecidableEq M] [DecidableEq R] [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary (encodingProblem bridge p K)) :
    SM_DT_RTCR_Adversary (hashProblem bridge p K) where
  main pp := do
    let (collision, transcript) ←
      (simulateQ (liftedOracles bridge p) (source.find pp)).run []
    return (witnessIndex bridge pp transcript collision, collision.1, collision.2.1)


/-- The common returned sample keeps both ordered histories without conditioning on termination. -/
@[expose] def runCoupled [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary (encodingProblem bridge p K)) :
    ProbComp (PP × ((M × R × E) ×
      (TargetCollisionResistance.Transcript M R E n radix × SM_DT_RTCR_State Tweak M R))) := do
  let pp ← bridge.th.seedGen
  let output ← (simulateQ (sourceCoupledOracles bridge p K pp) (source.find pp)).run ([], [])
  return (pp, output)

/-- Boolean source observation on the common returned sample. -/
@[expose] def sourceObservation [DecidableEq M] [DecidableEq R] [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix)
    (result : PP × ((M × R × E) ×
      (TargetCollisionResistance.Transcript M R E n radix × SM_DT_RTCR_State Tweak M R))) : Bool :=
  let (pp, output) := result
  let (collision, state) := output
  TargetCollisionResistance.valid bridge.enc pp state.1 collision

/-- Boolean VCVio observation on the same sample and first witnessing index. -/
@[expose] def targetObservation [DecidableEq M] [DecidableEq R] [DecidableEq E]
    [DecidableEq Y]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (result : PP × ((M × R × E) ×
      (TargetCollisionResistance.Transcript M R E n radix × SM_DT_RTCR_State Tweak M R))) : Bool :=
  let (pp, output) := result
  let (collision, state) := output
  SM_DT_RTCR_IsCollision (hashProblem bridge p K) pp state.2
    (witnessIndex bridge pp state.1 collision, collision.1, collision.2.1)

/-- Every returned source win is a target win at the selected issue index. False results and
missing mass are unrestricted, which is sufficient for the native measure inequality. -/
theorem sourceObservation_implies_targetObservation
    [DecidableEq M] [DecidableEq R] [DecidableEq E] [DecidableEq Y]
    [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary (encodingProblem bridge p K))
    (result : PP × ((M × R × E) ×
      (TargetCollisionResistance.Transcript M R E n radix × SM_DT_RTCR_State Tweak M R)))
    (hresult : result ∈ support (runCoupled bridge p K source))
    (hwin : sourceObservation bridge result = true) :
    targetObservation bridge p K result = true := by
  unfold runCoupled at hresult
  obtain ⟨pp, _, hrest⟩ := support_bind_exists hresult
  obtain ⟨output, hrun, hpure⟩ := support_bind_exists hrest
  have heq := (mem_support_pure_iff _ _).mp hpure
  subst result
  have hinv := sourceCoupled_run_preserves_inv bridge p K pp
    (source.find pp) ([], []) (coupledInv_empty bridge pp) output hrun
  have htarget := valid_implies_hash_collision bridge p K pp output.2.1 output.1
    hinv.2 (by simpa [sourceObservation] using hwin)
  simpa [targetObservation, hinv.1] using htarget

/-- The source Boolean experiment is the first-history observation of the common sample. -/
theorem source_experiment_eq_coupled
    [DecidableEq M] [DecidableEq R] [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary (encodingProblem bridge p K)) :
    TargetCollisionResistance.experiment source =
      sourceObservation bridge <$> runCoupled bridge p K source := by
  unfold TargetCollisionResistance.experiment runCoupled sourceObservation
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  apply congrArg (fun (f : PP → ProbComp Bool) => bridge.th.seedGen >>= f)
  funext pp
  rw [← sourceCoupled_run_proj bridge p K pp (source.find pp) ([], [])]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  rfl

/-- The VCVio experiment of the constructed adversary observes the same common sample. -/
theorem target_experiment_eq_coupled
    [DecidableEq M] [DecidableEq R] [DecidableEq E] [DecidableEq Tweak]
    [DecidableEq Y] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary (encodingProblem bridge p K)) :
    SM_DT_RTCR_Experiment (reduction bridge p K source) =
      targetObservation bridge p K <$> runCoupled bridge p K source := by
  unfold SM_DT_RTCR_Experiment reduction runCoupled targetObservation
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind,
    map_eq_bind_pure_comp, Function.comp_def]
  apply congrArg (fun (f : PP → ProbComp Bool) => bridge.th.seedGen >>= f)
  funext pp
  rw [nested_run_eq_source bridge p K pp (source.find pp)]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  rfl

/-- The unconditional native returned-mass bound for any capacities, including zero. Both games
sample the same public seed and use the canonical randomizer sampler; no mass is normalized. -/
theorem advantage_le_hash
    [DecidableEq M] [DecidableEq R] [DecidableEq E] [DecidableEq Tweak]
    [DecidableEq Y] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary (encodingProblem bridge p K)) :
    TargetCollisionResistance.advantage source ≤
      SM_DT_RTCR_Advantage (reduction bridge p K source) := by
  unfold TargetCollisionResistance.advantage TargetCollisionResistance.outputMeasure
    SM_DT_RTCR_Advantage
  rw [source_experiment_eq_coupled bridge p K source,
    target_experiment_eq_coupled bridge p K source]
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply OracleComp.evalDist_bind_apply_mono_of_support
    (runCoupled bridge p K source)
    (fun result => pure (sourceObservation bridge result))
    (fun result => pure (targetObservation bridge p K result))
    (measurableSet_singleton true)
  intro result hresult
  by_cases hwin : sourceObservation bridge result = true
  · have htarget := sourceObservation_implies_targetObservation
      bridge p K source result hresult hwin
    simp [hwin, htarget]
  · have hlose : sourceObservation bridge result = false := by
      cases h : sourceObservation bridge result <;> simp_all
    simp [hlose]

end IncomparableEncoding.TargetCollisionReduction
