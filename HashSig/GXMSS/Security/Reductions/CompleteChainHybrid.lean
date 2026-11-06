/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Completeness
import all HashSig.GXMSS.Completeness
public import HashSig.GXMSS.Security.Auxiliary.ChainSplicing
import all HashSig.GXMSS.Security.Auxiliary.ChainSplicing
public import HashSig.GXMSS.Security.Reductions.ChainPreimage
import all HashSig.GXMSS.Security.Reductions.ChainPreimage
public import HashSig.GXMSS.Security.Auxiliary.ChainSourceMass
import all HashSig.GXMSS.Security.Auxiliary.ChainSourceMass
public import HashSig.GXMSS.Security.Auxiliary.ChainTelescope
import all HashSig.GXMSS.Security.Auxiliary.ChainTelescope
public import HashSig.GXMSS.Security.Auxiliary.ChainSelection
import all HashSig.GXMSS.Security.Auxiliary.ChainSelection
public import HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
import all HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
public import HashSig.GXMSS.Security.Auxiliary.Encoding
import all HashSig.GXMSS.Security.Auxiliary.Encoding
public import HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
import all HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
public import HashSig.GXMSS.Security.Auxiliary.SourceGames
import all HashSig.GXMSS.Security.Auxiliary.SourceGames
public import HashSig.GXMSS.Security.Reductions.ChainUndetectability
import all HashSig.GXMSS.Security.Reductions.ChainUndetectability
public import HashSig.GXMSS.Security.Reductions.EncodingCollision
import all HashSig.GXMSS.Security.Reductions.EncodingCollision
public import HashSig.GXMSS.Security.Reductions.Problems
import all HashSig.GXMSS.Security.Reductions.Problems
public import HashSig.GXMSS.Security.Reductions.TargetCollision
import all HashSig.GXMSS.Security.Reductions.TargetCollision
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Monadic
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.EvalDist.Monad.UniformTable
public import VCVio.OracleComp.EvalDist.Sum

/-!
# Complete-tree chain hybrid composition

The native returned-measure telescope charges the complete selected chain event to the
named joint undetectability and preimage reductions.
-/

public section
namespace GXMSS.Reductions
open Encoding ENNReal OracleComp OracleSpec GXMSS.Security TweakableHash
variable {PP T X H M R E S : Type} {h w v n radix : ℕ}
/-- The one joint returned-measure identity across the entire seed, selector, start and cut
sampling law. All four terms retain returned false and unreturned mass. -/
private theorem joint_fixed_selector_returned_measure_telescope
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
     [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v) :
    let n := 2 ^ w - 1
    let ep := guessedEpoch guess
    let i := guessedChain guess
    let g := (guessedPosition guess).val
    let cut : ℕ → Guess h w v := fun j => (ep, i, Fin.ofNat n j)
    let event : Option (Result PP H M R h v) → Bool := fun out => out.elim false
      (fun result => jointChainObservation hash enc K (guess, result))
    let source : ProbComp Bool := do
      let starts ← GXMSS.sampleStarts H h v
      let x ← ($ᵗ H : ProbComp H)
      let out ← runFilteredSpliced hash enc K adv pp guess (cut 0)
        (hash.chain pp ep i 0 1 x) starts
      return event out
    let terminal : ProbComp Bool := do
      let starts ← GXMSS.sampleStarts H h v
      let x ← ($ᵗ H : ProbComp H)
      let out ← runFilteredSpliced hash enc K adv pp guess guess
        (hash.chain pp ep i g 1 x) starts
      return event out
    let selected : SM_DT_UD_World → ProbComp Bool := fun world => do
      let j ← ($ᵗ (Fin n) : ProbComp (Fin n))
      let starts ← GXMSS.sampleStarts H h v
      let x ← ($ᵗ H : ProbComp H)
      let answer := match world with
        | .real => hash.chain pp ep i j.val 1 x
        | .ideal => x
      if j.val < g then
        let out ← runFilteredSpliced hash enc K adv pp guess (cut j.val) answer starts
        return event out
      else return false
    𝒟[source] {true} + (n : ℝ≥0∞) * 𝒟[selected .ideal] {true} =
      𝒟[terminal] {true} + (n : ℝ≥0∞) * 𝒟[selected .real] {true} := by
  exact context_fixed_selector_returned_measure_telescope hash enc K (completeChainContext hash)
    adv pp guess (fun result => jointChainObservation hash enc K (guess, result))

private theorem joint_outer_returned_measure_telescope
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    𝒟[jointZeroRealProgram hash enc K adv] {true} +
      (↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) *
        𝒟[jointUDChainCutProgram hash enc K adv .ideal] {true} =
    𝒟[jointTerminalFilteredProgram hash enc K adv] {true} +
      (↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) *
        𝒟[jointUDChainCutProgram hash enc K adv .real] {true} := by
  let : MeasurableSpace PP := ⊤
  rw [jointZeroRealProgram_eq_normalized hash enc K adv]
  unfold jointZeroRealNormalized jointTerminalFilteredProgram jointUDChainCutProgram
  let sourcePP (pp : PP) : ProbComp Bool := do
    let guess ← $ᵗ (Guess h w v)
    let starts ← GXMSS.sampleStarts H h v
    let x ← ($ᵗ H : ProbComp H)
    let zero : Guess h w v :=
      (guessedEpoch guess, guessedChain guess,
        ⟨0, Nat.pos_of_ne_zero (NeZero.ne (2 ^ w - 1))⟩)
    let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0 1 x
    let out ← runFilteredSpliced hash enc K adv pp guess zero answer starts
    return out.elim false
      (fun result => jointChainObservation hash enc K (guess, result))
  let selectedPP (world : SM_DT_UD_World) (pp : PP) : ProbComp Bool := do
    let guess ← $ᵗ (Guess h w v)
    let j ← $ᵗ (Fin (2 ^ w - 1))
    let starts ← GXMSS.sampleStarts H h v
    let x ← ($ᵗ H : ProbComp H)
    let answer := match world with
      | .real => hash.chain pp (guessedEpoch guess) (guessedChain guess) j.val 1 x
      | .ideal => x
    if j.val < (guessedPosition guess).val then
      let spliceGuess : Guess h w v :=
        (guessedEpoch guess, guessedChain guess, j)
      let out ← runFilteredSpliced hash enc K adv pp guess spliceGuess answer starts
      return out.elim false
        (fun result => jointChainObservation hash enc K (guess, result))
    else return false
  let terminalPP (pp : PP) : ProbComp Bool := do
    let guess ← $ᵗ (Guess h w v)
    let starts ← GXMSS.sampleStarts H h v
    let hidden ← $ᵗ H
    let answer := hash.thf.eval pp
      (hash.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess))
      (hash.digestInput hidden)
    let out ← runFilteredSpliced hash enc K adv pp guess guess answer starts
    return out.elim false
      (fun result => jointChainObservation hash enc K (guess, result))
  change 𝒟[hash.thf.seedGen >>= sourcePP] {true} +
    (↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) *
      𝒟[hash.thf.seedGen >>= selectedPP .ideal] {true} =
    𝒟[hash.thf.seedGen >>= terminalPP] {true} +
      (↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) *
        𝒟[hash.thf.seedGen >>= selectedPP .real] {true}
  apply bind_true_mass_telescope hash.thf.seedGen sourcePP (selectedPP .ideal)
    terminalPP (selectedPP .real) (2 ^ w - 1)
  intro pp
  apply bind_true_mass_telescope
    ($ᵗ (Guess h w v) : ProbComp (Guess h w v)) _ _ _ _ (2 ^ w - 1)
  intro guess
  have hfin (j : Fin (2 ^ w - 1)) : Fin.ofNat (2 ^ w - 1) j.val = j := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt j.isLt
  have hzero : Fin.ofNat (2 ^ w - 1) 0 =
      (⟨0, Nat.pos_of_ne_zero (NeZero.ne (2 ^ w - 1))⟩ : Fin (2 ^ w - 1)) := by
    apply Fin.ext
    simp [Fin.ofNat]
  simpa only [jointPRE_terminal_answer_eq_chain hash pp guess, hfin, hzero] using
    joint_fixed_selector_returned_measure_telescope hash enc K adv pp guess
/-- The joint finite-index returned-measure bridge. The theorem below proves this proposition
from the zero-real source law, filtered UD worlds, terminal PRE selected mass, and the finite
hybrid telescope. -/
@[expose] def JointChainHybridReturnedMeasureBridge
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) : Prop :=
  jointChainAdvantage hash enc K hv hw adv ≤
    (↑(2 ^ w - 1) : ℝ≥0∞) *
      SM_DT_UD_Advantage (jointUndetectabilityReduction hash enc K hv hw adv) +
      𝒟[jointPRESelectedProgram hash enc K adv] {true}
/-- The native returned-mass telescope charges all selected Game 4 histories to one joint UD
distance and the exact selected mass of the one joint PRE experiment. -/
theorem jointChainAdvantage_le_jointUD_add_jointPRESelected
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    jointChainAdvantage hash enc K hv hw adv ≤
      (↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) *
        SM_DT_UD_Advantage (jointUndetectabilityReduction hash enc K hv hw adv) +
        𝒟[jointPRESelectedProgram hash enc K adv] {true} := by
  let n := 2 ^ w - 1
  let ud := jointUndetectabilityReduction hash enc K hv hw adv
  have hreal :
      𝒟[SM_DT_UD_Experiment .real ud] {true} =
        𝒟[jointUDChainCutProgram hash enc K adv .real] {true} :=
    jointUDExperiment_true_eq_chainCut hash enc K hv hw adv .real
  have hideal :
      𝒟[SM_DT_UD_Experiment .ideal ud] {true} =
        𝒟[jointUDChainCutProgram hash enc K adv .ideal] {true} :=
    jointUDExperiment_true_eq_chainCut hash enc K hv hw adv .ideal
  have hdist :
      𝒟[jointUDChainCutProgram hash enc K adv .real] {true} ≤
        𝒟[jointUDChainCutProgram hash enc K adv .ideal] {true} +
          SM_DT_UD_Advantage ud := by
    have h := MeasureTheory.Measure.apply_true_le_add_boolDist
      𝒟[SM_DT_UD_Experiment .real ud] 𝒟[SM_DT_UD_Experiment .ideal ud]
    rw [hreal, hideal] at h
    simpa only [SM_DT_UD_Advantage] using h
  have hfinite : (n : ℝ≥0∞) *
      𝒟[jointUDChainCutProgram hash enc K adv .ideal] {true} ≠ ∞ := by
    have hle : (n : ℝ≥0∞) *
        𝒟[jointUDChainCutProgram hash enc K adv .ideal] {true} ≤ n := by
      calc
        _ ≤ (n : ℝ≥0∞) * 1 := by
          gcongr
          exact evalDist_apply_le_one (jointUDChainCutProgram hash enc K adv .ideal) {true}
        _ = n := mul_one _
    exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) hle
  have hselected := finite_hybrid_boolDist_bound
    (𝒟[jointZeroRealProgram hash enc K adv] {true})
    (𝒟[jointTerminalFilteredProgram hash enc K adv] {true})
    (𝒟[jointUDChainCutProgram hash enc K adv .real] {true})
    (𝒟[jointUDChainCutProgram hash enc K adv .ideal] {true})
    (SM_DT_UD_Advantage ud) n hfinite
    (joint_outer_returned_measure_telescope hash enc K adv) hdist
  calc
    jointChainAdvantage hash enc K hv hw adv =
        𝒟[jointZeroRealProgram hash enc K adv] {true} :=
      jointChainAdvantage_eq_zeroReal hash enc K hv hw adv
    _ ≤ 𝒟[jointTerminalFilteredProgram hash enc K adv] {true} +
          (n : ℝ≥0∞) * SM_DT_UD_Advantage ud := hselected
    _ = 𝒟[jointPRESelectedProgram hash enc K adv] {true} +
          (n : ℝ≥0∞) * SM_DT_UD_Advantage ud := by
      rw [jointPRESelected_mass_eq_terminalFiltered hash enc K adv]
    _ = _ := by
      ac_rfl
/-- The previously stated hybrid bridge follows from the native returned-mass equality. -/
theorem jointChainHybridReturnedMeasureBridge
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    JointChainHybridReturnedMeasureBridge hash enc K hv hw adv := by
  unfold JointChainHybridReturnedMeasureBridge
  have hcoeff : (↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) = (2 ^ w - 1 : ℝ≥0∞) := by
    simp only [ENNReal.natCast_sub, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  simpa only [hcoeff] using
    jointChainAdvantage_le_jointUD_add_jointPRESelected hash enc K hv hw adv
/-- One joint UD charge and one joint PRE charge pay every selected returned Game 4 history,
including successful, unused and failed-consumed epochs. -/
theorem jointChainAdvantage_le_jointUD_add_jointPRE
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    jointChainAdvantage hash enc K hv hw adv ≤
      (↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) *
        SM_DT_UD_Advantage (jointUndetectabilityReduction hash enc K hv hw adv) +
        SM_DT_PRE_Advantage (jointPreimageReduction hash enc K hv hw adv) := by
  calc
    jointChainAdvantage hash enc K hv hw adv ≤
        (↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (jointUndetectabilityReduction hash enc K hv hw adv) +
          𝒟[jointPRESelectedProgram hash enc K adv] {true} :=
      jointChainAdvantage_le_jointUD_add_jointPRESelected hash enc K hv hw adv
    _ ≤ _ := by
      gcongr
      exact jointPRESelectedMass_le_preimageAdvantage hash enc K hv hw adv

end GXMSS.Reductions
