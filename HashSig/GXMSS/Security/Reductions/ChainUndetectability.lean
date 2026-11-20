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
public import HashSig.GXMSS.Security.Auxiliary.ChainSourceMass
import all HashSig.GXMSS.Security.Auxiliary.ChainSourceMass
public import HashSig.GXMSS.Security.Auxiliary.ChainSelection
import all HashSig.GXMSS.Security.Auxiliary.ChainSelection
public import HashSig.GXMSS.Security.Auxiliary.ChainTelescope
import all HashSig.GXMSS.Security.Auxiliary.ChainTelescope
public import HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
import all HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
public import HashSig.GXMSS.Security.Auxiliary.Encoding
import all HashSig.GXMSS.Security.Auxiliary.Encoding
public import HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
import all HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
public import HashSig.GXMSS.Security.Auxiliary.SourceGames
import all HashSig.GXMSS.Security.Auxiliary.SourceGames
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
# Original-domain chain undetectability

One selected original-domain chain challenge simulates the complete adaptive continuation
in both real and ideal undetectability worlds.
-/

public section
namespace GXMSS.Reductions
open Encoding ENNReal OracleComp OracleSpec GXMSS.Security TweakableHash
variable {PP T X H M R E S : Type} {h w v n radix : ℕ}
private noncomputable def udPick [NeZero v] [NeZero (2 ^ w - 1)] [SampleableType H]
    (hash : HashInstance PP T X H h w v) :
    OracleComp (unifSpec + (SM_DT_UD_challengeSpec T H +
      collectionSpec (chainUDProblem hash).thColl)) (UDTargetState H h w v) := do
  let guess ← OracleComp.liftComp ($ᵗ (Guess h w v)) _
  let hybrid ← OracleComp.liftComp ($ᵗ (Fin (2 ^ w - 1))) _
  let starts ← OracleComp.liftComp (GXMSS.sampleStarts H h v) _
  let answer ← liftM ((unifSpec + (SM_DT_UD_challengeSpec T H +
    collectionSpec (chainUDProblem hash).thColl)).query (.inr (.inl
      (hash.chainTweak (guessedEpoch guess, guessedChain guess, hybrid)))))
  return ⟨guess, hybrid, answer, starts⟩
/-- Executable one-target undetectability reduction driven by the fixed source adversary. -/
noncomputable def undetectabilityReduction [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (advGXMSS : SchemeAdversary PP H M R h v) :
    SM_DT_UD_Adversary (chainUDProblem hash) := by
  letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
  letI : NeZero (2 ^ w - 1) := ⟨by have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
  exact {
  State := UDTargetState H h w v
  pick := udPick hash
  distinguish state pp := do
    match state.answer with
    | none => return false
    | some answer =>
      let spliceGuess : Guess h w v :=
        (guessedEpoch state.guess, guessedChain state.guess, state.hybrid)
      let out ← runSpliced hash enc K advGXMSS pp spliceGuess answer state.starts
      return gameFiveObservation hash enc K (state.guess, out) }
/-- One undetectability adversary observes the enlarged selected event across successful,
unused, and failed-consumed forged epochs. It issues one challenge before seed reveal. -/
noncomputable def jointUndetectabilityReduction [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (advGXMSS : SchemeAdversary PP H M R h v) :
    SM_DT_UD_Adversary (chainUDProblem hash) := by
  letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
  letI : NeZero (2 ^ w - 1) := ⟨by have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
  exact {
  State := UDTargetState H h w v
  pick := udPick hash
  distinguish state pp := do
    if state.hybrid.val < (guessedPosition state.guess).val then
      match state.answer with
      | none => return false
      | some answer =>
        let spliceGuess : Guess h w v :=
          (guessedEpoch state.guess, guessedChain state.guess, state.hybrid)
        let out ← runSpliced hash enc K advGXMSS pp spliceGuess answer state.starts
        return jointChainObservation hash enc K (state.guess, out)
    else return false }
private noncomputable def jointUDExplicitProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (world : SM_DT_UD_World) : ProbComp Bool := do
  let pp ← hash.thf.seedGen
  let guess ← $ᵗ (Guess h w v)
  let j ← $ᵗ (Fin (2 ^ w - 1))
  let starts ← GXMSS.sampleStarts H h v
  let answer ← SM_DT_UD_response world (chainUDProblem hash) pp
    (hash.chainTweak (guessedEpoch guess, guessedChain guess, j))
  if j.val < (guessedPosition guess).val then
    let spliceGuess : Guess h w v :=
      (guessedEpoch guess, guessedChain guess, j)
    let out ← runSpliced hash enc K adv pp spliceGuess answer starts
    return jointChainObservation hash enc K (guess, out)
  else return false
private noncomputable def jointUDFilteredProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (world : SM_DT_UD_World) : ProbComp Bool := do
  let pp ← hash.thf.seedGen
  let guess ← $ᵗ (Guess h w v)
  let j ← $ᵗ (Fin (2 ^ w - 1))
  let starts ← GXMSS.sampleStarts H h v
  let answer ← SM_DT_UD_response world (chainUDProblem hash) pp
    (hash.chainTweak (guessedEpoch guess, guessedChain guess, j))
  if j.val < (guessedPosition guess).val then
    let spliceGuess : Guess h w v :=
      (guessedEpoch guess, guessedChain guess, j)
    let out ← runFilteredSpliced hash enc K adv pp guess spliceGuess answer starts
    return out.elim false
      (fun result => jointChainObservation hash enc K (guess, result))
  else return false
/-- Filtering the one joint UD experiment preserves its returned true mass in either world. -/
private theorem jointUDExplicit_mass_eq_filtered
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (world : SM_DT_UD_World) :
    𝒟[jointUDExplicitProgram hash enc K adv world] {true} =
      𝒟[jointUDFilteredProgram hash enc K adv world] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  unfold jointUDExplicitProgram jointUDFilteredProgram
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro pp
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro guess
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro j
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro starts
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro answer
  by_cases hj : j.val < (guessedPosition guess).val
  · simp only [hj, ↓reduceIte]
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using
      runSpliced_selectedMass_eq_filtered hash enc K adv pp guess
        (guessedEpoch guess, guessedChain guess, j) answer starts
  · simp only [hj, ↓reduceIte]
/-- The authoritative real UD response is exactly one sampled positive chain step. -/
private theorem jointUD_real_response_eq_chain
    [SampleableType H]
    (hash : HashInstance PP T X H h w v)
    (pp : PP) (ep : Epoch h) (i : Fin v) (j : Fin (2 ^ w - 1)) :
    SM_DT_UD_response .real (chainUDProblem hash) pp
      (hash.chainTweak (ep, i, j)) =
    (fun x => hash.chain pp ep i j.val 1 x) <$> ($ᵗ H : ProbComp H) := by
  unfold SM_DT_UD_response chainUDProblem SM_DT_UD_Problem.standalone
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply bind_congr
  intro x
  congr 1
  have hstep := hash.chain_succ pp ep i j.val 0 x (by omega)
  simpa only [Nat.add_zero, zero_add, hash.chain_zero] using hstep.symm
/-- The authoritative ideal UD response samples the digest domain uniformly. -/
private theorem jointUD_ideal_response_eq_uniform
    [SampleableType H]
    (hash : HashInstance PP T X H h w v)
    (pp : PP) (ep : Epoch h) (i : Fin v) (j : Fin (2 ^ w - 1)) :
    SM_DT_UD_response .ideal (chainUDProblem hash) pp
      (hash.chainTweak (ep, i, j)) = ($ᵗ H : ProbComp H) := by
  rfl
private def jointUDChainCutProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (world : SM_DT_UD_World) : ProbComp Bool := do
  let pp ← hash.thf.seedGen
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
/-- The single authoritative UD challenge has the explicit chain-cut law in both worlds. -/
private theorem jointUDFiltered_eq_chainCut
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (world : SM_DT_UD_World) :
    jointUDFilteredProgram hash enc K adv world =
      jointUDChainCutProgram hash enc K adv world := by
  unfold jointUDFilteredProgram jointUDChainCutProgram
  apply bind_congr
  intro pp
  apply bind_congr
  intro guess
  apply bind_congr
  intro j
  apply bind_congr
  intro starts
  cases world with
  | real =>
    rw [jointUD_real_response_eq_chain hash pp (guessedEpoch guess)
      (guessedChain guess) j]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  | ideal =>
    rw [jointUD_ideal_response_eq_uniform hash pp (guessedEpoch guess)
      (guessedChain guess) j]
private theorem jointUDOracles_liftComp
    [SampleableType H] [DecidableEq T]
    (hash : HashInstance PP T X H h w v)
    (world : SM_DT_UD_World) (pp : PP) (oa : ProbComp S)
    (state : SM_DT_UD_State T) :
    (simulateQ (SM_DT_UD_oracles world (chainUDProblem hash) pp)
      (OracleComp.liftComp oa _)).run state =
        (fun x => (x, state)) <$> oa := by
  rw [SM_DT_UD_oracles, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  simp
private theorem jointUDOracles_challenge
    [SampleableType H] [DecidableEq T]
    (hash : HashInstance PP T X H h w v)
    (world : SM_DT_UD_World) (pp : PP) (t : T) :
    (simulateQ (SM_DT_UD_oracles world (chainUDProblem hash) pp)
      (liftM ((unifSpec + (SM_DT_UD_challengeSpec T H +
        collectionSpec (chainUDProblem hash).thColl)).query (.inr (.inl t))))).run
      (([], []) : SM_DT_UD_State T) =
      (fun answer => (some answer, ([t], []))) <$>
        SM_DT_UD_response world (chainUDProblem hash) pp t := by
  rw [SM_DT_UD_oracles, QueryImpl.simulateQ_add_query_right,
    QueryImpl.add_apply_inl]
  simp [SM_DT_UD_challengeOracle, TweakFresh, TweakReserved, chainUDProblem,
    SM_DT_UD_Problem.standalone, StateT.run_bind, map_eq_bind_pure_comp]
private theorem jointUDExperiment_eq_explicit
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v)
    (world : SM_DT_UD_World) :
    SM_DT_UD_Experiment world (jointUndetectabilityReduction hash enc K hv hw adv) =
      (letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
       letI : NeZero (2 ^ w - 1) :=
         ⟨by have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
       jointUDExplicitProgram hash enc K adv world) := by
  unfold SM_DT_UD_Experiment jointUndetectabilityReduction jointUDExplicitProgram udPick
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    pure_bind, bind_assoc]
  simp only [jointUDOracles_liftComp, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  simp only [jointUDOracles_challenge, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  rfl
/-- The authoritative one-target UD game's returned true mass is the explicit filtered chain
cut, with one pre-seed challenge and the original adaptive signing law. -/
private theorem jointUDExperiment_true_eq_chainCut
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v)
    (world : SM_DT_UD_World) :
    𝒟[SM_DT_UD_Experiment world
      (jointUndetectabilityReduction hash enc K hv hw adv)] {true} =
    𝒟[jointUDChainCutProgram hash enc K adv world] {true} := by
  rw [jointUDExperiment_eq_explicit hash enc K hv hw adv world]
  exact (jointUDExplicit_mass_eq_filtered hash enc K adv world).trans
    (congrArg (fun mx : ProbComp Bool => 𝒟[mx] {true})
      (jointUDFiltered_eq_chainCut hash enc K adv world))

end GXMSS.Reductions
