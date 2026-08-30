/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.FinalValidity
public import VCVio.OracleComp.SimSemantics.Append

/-!
# Single-function, distinct-tweak, multi-target undetectability in a collection

SM-DT-UD-C asks an adversary to distinguish sampled images of one tweakable hash from samples of
an explicit output distribution. The public seed is sampled by the experiment and withheld while
the adversary selects target tweaks through the challenge oracle and evaluates the shared hash
collection. The seed is revealed only after those oracles have been removed.

In the real world, a challenge at `t` samples `m ← inputGen` and returns `th.eval pk t m`. In the
ideal world it returns `y ← outputGen`. Both worlds answer and record every query. The sticky
final-validity monitor checks the target cap, distinct target tweaks, and target/collection
disjointness only in the experiment's final conjunction; repeated collection-only tweaks remain
valid.

The exported advantage is the symmetric ENNReal gap
`max (realSuccess - idealSuccess) (idealSuccess - realSuccess)`. This avoids coercing the game to
`ℝ` merely to express an absolute difference and does not inherit the repository's older asymmetric
PRF convention.

## References

- Barbosa, Dupressoir, Grégoire, Hülsing, Meijers and Strub, *Machine-Checked Security for XMSS as
  in RFC 8391 and SPHINCS+*, [ePrint 2023/408](https://eprint.iacr.org/2023/408), Figs. 5, 6 and 9,
  and `TweakableHashFunctions.Collection.SMDTUDC` in the accompanying EasyCrypt development.
- Hülsing and Kudinov, *Recovering the Tight Security Proof of SPHINCS+*,
  [ePrint 2022/346](https://eprint.iacr.org/2022/346).
-/

@[expose] public section

namespace TweakableHash

open OracleComp OracleSpec ENNReal

variable {ι PkSeed Tweak M Y : Type}

/-! ## The game -/

/-- Which response distribution the challenge oracle uses. -/
inductive SM_DT_UD_C_World
  /-- Sample a hidden input and evaluate the attacked tweakable hash. -/
  | real
  /-- Sample directly from the problem's output distribution. -/
  | ideal
deriving DecidableEq, Repr

/-- The challenge oracle takes a target tweak and returns a digest in both worlds. -/
abbrev SM_DT_UD_C_challengeSpec (Tweak Y : Type) : OracleSpec Tweak := Tweak →ₒ Y

/-- An SM-DT-UD-C problem: attacked hash, explicit real and ideal sampling distributions, shared
collection, and target cap. -/
structure SM_DT_UD_C_Problem (ι PkSeed Tweak M Y : Type) where
  /-- The tweakable hash whose sampled images should be indistinguishable from `outputGen`. -/
  th : TweakableHash PkSeed Tweak M Y
  /-- Distribution of hidden inputs in the real challenge world. -/
  inputGen : ProbComp M
  /-- Distribution of direct challenge outputs in the ideal world. -/
  outputGen : ProbComp Y
  /-- The rest of the collection, available during target selection at the same hidden seed. -/
  thColl : TweakableHashCollection ι PkSeed Tweak Y
  /-- The maximum number of challenge queries allowed by final validity. -/
  numTargets : ℕ

/-- The stand-alone SM-DT-UD problem, whose collection oracle is unqueryable. -/
def SM_DT_UD_C_Problem.standalone (th : TweakableHash PkSeed Tweak M Y)
    (inputGen : ProbComp M) (outputGen : ProbComp Y) (numTargets : ℕ) :
    SM_DT_UD_C_Problem Empty PkSeed Tweak M Y where
  th := th
  inputGen := inputGen
  outputGen := outputGen
  thColl := .empty PkSeed Tweak Y
  numTargets := numTargets

/-- Target tweaks, collection tweaks, and the sticky final-validity bit. -/
abbrev SM_DT_UD_C_State (Tweak : Type) : Type := FinalValidityState Tweak Tweak

/-- An SM-DT-UD-C adversary split exactly at the public-seed reveal. -/
structure SM_DT_UD_C_Adversary (prob : SM_DT_UD_C_Problem ι PkSeed Tweak M Y) where
  /-- Private state passed from target selection to the distinguishing phase. -/
  State : Type
  /-- Select target tweaks with private randomness and collection access, but without the seed. -/
  pick : OracleComp
    (unifSpec +
      (SM_DT_UD_C_challengeSpec Tweak Y + finalValidityCollectionSpec prob.thColl)) State
  /-- After the seed is revealed and both oracles are removed, return the distinguishing bit. -/
  distinguish : State → PkSeed → ProbComp Bool

/-- One challenge response. Only this distribution differs between the real and ideal worlds. -/
def SM_DT_UD_C_response (world : SM_DT_UD_C_World)
    (prob : SM_DT_UD_C_Problem ι PkSeed Tweak M Y) (pk : PkSeed) (t : Tweak) : ProbComp Y :=
  match world with
  | .real => do
      let m ← prob.inputGen
      return prob.th.eval pk t m
  | .ideal => prob.outputGen

/-- The always-answering challenge oracle. Every query is appended to the target history; a cap,
duplicate-target, or collection clash poisons final validity without changing the response. -/
def SM_DT_UD_C_challengeOracle [DecidableEq Tweak] (world : SM_DT_UD_C_World)
    (prob : SM_DT_UD_C_Problem ι PkSeed Tweak M Y) (pk : PkSeed) :
    QueryImpl (SM_DT_UD_C_challengeSpec Tweak Y)
      (StateT (SM_DT_UD_C_State Tweak) ProbComp) :=
  fun t => do
    let y ← (SM_DT_UD_C_response world prob pk t :
      StateT (SM_DT_UD_C_State Tweak) ProbComp Y)
    let st ← get
    set (st.recordTarget prob.numTargets id t)
    return y

/-- Challenge and collection access over one final-validity state and one hidden seed. -/
def SM_DT_UD_C_oracles [DecidableEq Tweak] (world : SM_DT_UD_C_World)
    (prob : SM_DT_UD_C_Problem ι PkSeed Tweak M Y) (pk : PkSeed) :
    QueryImpl
      (unifSpec +
        (SM_DT_UD_C_challengeSpec Tweak Y + finalValidityCollectionSpec prob.thColl))
      (StateT (SM_DT_UD_C_State Tweak) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (SM_DT_UD_C_State Tweak) ProbComp) +
    (SM_DT_UD_C_challengeOracle world prob pk +
      finalValidityCollectionOracle (Q := Tweak) id prob.thColl pk)

/-- The source-final-validity SM-DT-UD-C experiment. The seed is hidden during `pick`, revealed to
`distinguish`, and success is the adversary's bit conjoined with the final validity monitor. -/
noncomputable def SM_DT_UD_C_Experiment [DecidableEq Tweak]
    (world : SM_DT_UD_C_World) {prob : SM_DT_UD_C_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_UD_C_Adversary prob) : ProbComp Bool := do
  let pk ← prob.th.seedGen
  let (privateState, gameState) ←
    (simulateQ (SM_DT_UD_C_oracles world prob pk) adv.pick).run .initial
  let b ← adv.distinguish privateState pk
  return gameState.valid && b

/-- Success probability when challenges are sampled hash images. -/
noncomputable def SM_DT_UD_C_RealSuccess [DecidableEq Tweak]
    {prob : SM_DT_UD_C_Problem ι PkSeed Tweak M Y} (adv : SM_DT_UD_C_Adversary prob) : ℝ≥0∞ :=
  Pr[= true | SM_DT_UD_C_Experiment .real adv]

/-- Success probability when challenges are sampled directly from `outputGen`. -/
noncomputable def SM_DT_UD_C_IdealSuccess [DecidableEq Tweak]
    {prob : SM_DT_UD_C_Problem ι PkSeed Tweak M Y} (adv : SM_DT_UD_C_Adversary prob) : ℝ≥0∞ :=
  Pr[= true | SM_DT_UD_C_Experiment .ideal adv]

/-- SM-DT-UD-C advantage as the symmetric gap of the two ENNReal success probabilities. -/
noncomputable def SM_DT_UD_C_Advantage [DecidableEq Tweak]
    {prob : SM_DT_UD_C_Problem ι PkSeed Tweak M Y} (adv : SM_DT_UD_C_Adversary prob) : ℝ≥0∞ :=
  max (SM_DT_UD_C_RealSuccess adv - SM_DT_UD_C_IdealSuccess adv)
    (SM_DT_UD_C_IdealSuccess adv - SM_DT_UD_C_RealSuccess adv)

/-! ## Canonical collection-parametric API

The collection is already an explicit field of the problem, as for the repository's TCR, PRE, and
DSPR interfaces. These names therefore omit the redundant `_C` while remaining definitionally the
same source SM-DT-UD-C game. -/

abbrev SM_DT_UD_World := SM_DT_UD_C_World

abbrev SM_DT_UD_challengeSpec (Tweak Y : Type) : OracleSpec Tweak :=
  SM_DT_UD_C_challengeSpec Tweak Y

abbrev SM_DT_UD_Problem (ι PkSeed Tweak M Y : Type) :=
  SM_DT_UD_C_Problem ι PkSeed Tweak M Y

/-- Canonical stand-alone SM-DT-UD problem at the empty collection. -/
def SM_DT_UD_Problem.standalone (th : TweakableHash PkSeed Tweak M Y)
    (inputGen : ProbComp M) (outputGen : ProbComp Y) (numTargets : ℕ) :
    SM_DT_UD_Problem Empty PkSeed Tweak M Y :=
  SM_DT_UD_C_Problem.standalone th inputGen outputGen numTargets

abbrev SM_DT_UD_State (Tweak : Type) := SM_DT_UD_C_State Tweak

abbrev SM_DT_UD_Adversary {ι PkSeed Tweak M Y : Type}
    (prob : SM_DT_UD_Problem ι PkSeed Tweak M Y) := SM_DT_UD_C_Adversary prob

/-- Canonically named real/ideal SM-DT-UD experiment. -/
noncomputable def SM_DT_UD_Experiment [DecidableEq Tweak] (world : SM_DT_UD_World)
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M Y} (adv : SM_DT_UD_Adversary prob) :
    ProbComp Bool :=
  SM_DT_UD_C_Experiment world adv

/-- Canonically named real-world success probability. -/
noncomputable def SM_DT_UD_RealSuccess [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M Y} (adv : SM_DT_UD_Adversary prob) : ℝ≥0∞ :=
  SM_DT_UD_C_RealSuccess adv

/-- Canonically named ideal-world success probability. -/
noncomputable def SM_DT_UD_IdealSuccess [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M Y} (adv : SM_DT_UD_Adversary prob) : ℝ≥0∞ :=
  SM_DT_UD_C_IdealSuccess adv

/-- SM-DT-UD-C advantage in the repository's canonical naming: the same symmetric ENNReal gap. -/
noncomputable def SM_DT_UD_Advantage [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M Y} (adv : SM_DT_UD_Adversary prob) : ℝ≥0∞ :=
  SM_DT_UD_C_Advantage adv

/-! ## Oracle behavior pins -/

variable [DecidableEq Tweak] {world : SM_DT_UD_C_World}
  {prob : SM_DT_UD_C_Problem ι PkSeed Tweak M Y} {pk : PkSeed} {t : Tweak}
  {st : SM_DT_UD_C_State Tweak}

/-- Every challenge is answered and recorded, including challenges that poison final validity. -/
theorem SM_DT_UD_C_challengeOracle_run :
    (SM_DT_UD_C_challengeOracle world prob pk t).run st =
      (fun y => (y, st.recordTarget prob.numTargets id t)) <$>
        SM_DT_UD_C_response world prob pk t := by
  simp [SM_DT_UD_C_challengeOracle, Functor.map_map]

end TweakableHash
