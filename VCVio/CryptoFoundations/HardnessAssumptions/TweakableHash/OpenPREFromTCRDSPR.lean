/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTOpenPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTDSPR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR

/-!
# Reduction adversaries from SM-DT-OpenPRE to DSPR and TCR

This file formalizes the two concrete adversaries used by the EasyCrypt reduction
`OpenPRE_From_TCR_DSPR_THF.eca`. Both run the OpenPRE adversary's commitment phase, keep precisely
the bounded prefix of committed tweaks, sample the source problem's input distribution, and route
the resulting targets through the assumption game's challenge oracle.

The TCR reduction forwards the OpenPRE adversary's final index and candidate. The DSPR reduction
guesses that a second preimage exists exactly when that candidate differs from the sampled target
or when the selected target was opened. These are executable reductions, not just existential
adversary placeholders. The quantitative inequality

`OpenPRE ≤ (DSPR success - SPprob) + 3 · TCR`

still requires the source proof's finite-preimage counting argument and is intentionally not
asserted here without that proof.
-/

@[expose] public section

namespace TweakableHash

open OracleComp OracleSpec

variable {ι PkSeed Tweak M Y : Type}

/-- Route commitment-phase randomness and collection queries into an assumption game's larger
selection interface, leaving its challenge oracle unavailable to the wrapped OpenPRE adversary. -/
def SM_DT_OpenPRE_liftPick
    (prob : SM_DT_OpenPRE_Problem ι PkSeed Tweak M Y) :
    QueryImpl (unifSpec + finalValidityCollectionSpec prob.thColl)
      (OracleComp (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y +
        finalValidityCollectionSpec prob.thColl)))
  | .inl q => liftM ((unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y +
      finalValidityCollectionSpec prob.thColl)).query (.inl q))
  | .inr q => liftM ((unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y +
      finalValidityCollectionSpec prob.thColl)).query (.inr (.inr q)))

/-! ## Assumption problems induced by an OpenPRE problem -/

/-- The TCR problem attacked by the OpenPRE-to-TCR reduction. -/
def SM_DT_OpenPRE_Problem.toTCR (prob : SM_DT_OpenPRE_Problem ι PkSeed Tweak M Y) :
    SM_DT_TCR_Problem ι PkSeed Tweak M Y where
  th := prob.th
  thColl := prob.thColl
  numTargets := prob.numTargets

/-- The DSPR problem attacked by the OpenPRE-to-DSPR reduction. -/
def SM_DT_OpenPRE_Problem.toDSPR (prob : SM_DT_OpenPRE_Problem ι PkSeed Tweak M Y) :
    SM_DT_DSPR_Problem ι PkSeed Tweak M Y where
  th := prob.th
  thColl := prob.thColl
  numTargets := prob.numTargets

/-! ## Shared target setup -/

/-- In an assumption game's selection phase, sample OpenPRE target inputs and submit them to that
game's challenge oracle. The input list is already the bounded prefix. Returned data contains the
sampled `(tweak, input)` targets needed to implement `open`, and the images shown to OpenPRE. -/
noncomputable def SM_DT_OpenPRE_reductionInitialize
    (prob : SM_DT_OpenPRE_Problem ι PkSeed Tweak M Y) :
    List Tweak → OracleComp
      (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y +
        finalValidityCollectionSpec prob.thColl)) (List (Tweak × M) × List Y)
  | [] => pure ([], [])
  | t :: ts => do
      let x ← liftM prob.inputGen
      let y ← liftM ((unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y +
        finalValidityCollectionSpec prob.thColl)).query (.inr (.inl (t, x))))
      let (targets, ys) ← SM_DT_OpenPRE_reductionInitialize prob ts
      return ((t, x) :: targets, y :: ys)

/-! ## Concrete TCR reduction -/

/-- Concrete reduction from an OpenPRE adversary to a TCR adversary. Opening queries are simulated
from the sampled target inputs; the reduction then forwards the selected index and candidate. -/
noncomputable def SM_DT_OpenPRE_toTCR [Inhabited M]
    {prob : SM_DT_OpenPRE_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_OpenPRE_Adversary prob) : SM_DT_TCR_Adversary prob.toTCR where
  State := adv.State × List (Tweak × M) × List Y
  choose := do
    let (privateState, tweaks) ← simulateQ (SM_DT_OpenPRE_liftPick prob) adv.pick
    let (targets, ys) ←
      SM_DT_OpenPRE_reductionInitialize prob (tweaks.take prob.numTargets)
    return (privateState, targets, ys)
  forge state pk := do
    let (privateState, targets, ys) := state
    let ((j, m), _) ←
      (simulateQ (SM_DT_OpenPRE_findOracles targets) (adv.find privateState pk ys)).run []
    return (j, m)

/-! ## Concrete DSPR reduction -/

/-- Concrete reduction from an OpenPRE adversary to a DSPR adversary. It predicts that the selected
target has a second preimage iff the candidate differs from the sampled input or the selected target
was opened. An invalid index uses the fixed witness, matching the source oracle's `nth witness`. -/
noncomputable def SM_DT_OpenPRE_toDSPR [Inhabited M] [DecidableEq M]
    {prob : SM_DT_OpenPRE_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_OpenPRE_Adversary prob) : SM_DT_DSPR_Adversary prob.toDSPR where
  State := adv.State × List (Tweak × M) × List Y
  choose := do
    let (privateState, tweaks) ← simulateQ (SM_DT_OpenPRE_liftPick prob) adv.pick
    let (targets, ys) ←
      SM_DT_OpenPRE_reductionInitialize prob (tweaks.take prob.numTargets)
    return (privateState, targets, ys)
  guess state pk := do
    let (privateState, targets, ys) := state
    let ((j, m), opened) ←
      (simulateQ (SM_DT_OpenPRE_findOracles targets) (adv.find privateState pk ys)).run []
    let sampled := (targets[j]?.map Prod.snd).getD default
    return (j, decide (sampled ≠ m ∨ j ∈ opened))

end TweakableHash
