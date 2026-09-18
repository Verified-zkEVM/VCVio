/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import HashSig.SLHDSA.Security.CanonicalGames

/-!
# Ordinary-import consumers of final-validity conversions

Conversion equations identify hash data, samplers, target caps, and the canonical SLH-DSA
compression games without opening the conversion implementation. Whole-experiment equalities
remain available for the named adversary conversion.
-/

public section

open TweakableHash SLHDSA SLHDSA.Security

namespace HashSigTest.ModuleAPI.FinalValidity

variable {ι PkSeed Tweak M M' Y : Type}

example (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) :
    prob.toSourceFinalValidity.th = prob.th := by
  fail_if_success rfl
  rw [SM_DT_TCR_Problem.toSourceFinalValidity_th]

example (prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) (message : M') :
    prob.toSourceFinalValidity.emb message = prob.emb message := by simp

example (prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y) :
    prob.toSourceFinalValidity.inputGen = prob.inputGen ∧
      prob.toSourceFinalValidity.outputGen = prob.outputGen := by simp

example (prob : SM_DT_DSPR_Problem ι PkSeed Tweak M Y) :
    prob.toSourceFinalValidity.numTargets = prob.numTargets := by simp

example [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (adv : SM_DT_TCR_Adversary prob) :
    SM_DT_TCR_SourceFinalValidity.Experiment adv.toSourceFinalValidity =
      SM_DT_TCR_Experiment adv := SM_DT_TCR_experiment_toSourceFinalValidity adv

variable {p : Params} (prims : Primitives p) [SampleableType prims.PkSeed]

example : CanonicalGames.forsTlTcrCProblem prims =
    (prims.thashTcrProblem p.k (targetCount p .forsTl)).toSourceFinalValidity := by
  rw [CanonicalGames.forsTlTcrCProblem_eq_toSourceFinalValidity]

example : CanonicalGames.wotsTlTcrCProblem prims =
    (prims.thashTcrProblem p.len (targetCount p .wotsTl)).toSourceFinalValidity := by
  rw [CanonicalGames.wotsTlTcrCProblem_eq_toSourceFinalValidity]

end HashSigTest.ModuleAPI.FinalValidity
