/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.FinalValidity
public import VCVio.OracleComp.SimSemantics.Append
public import ToMathlib.Data.ENNReal.AbsDiff

/-!
# Source-final-validity SM-DT-UD

SM-DT-UD asks an adversary to distinguish sampled images of one tweakable hash from samples of
an explicit output distribution. The public seed is sampled by the experiment and withheld while
the adversary selects target tweaks through the challenge oracle and evaluates the shared hash
collection. The seed is revealed only after those oracles have been removed.

In the real world, a challenge at `t` samples `m ← inputGen` and returns `th.eval pk t m`. In the
ideal world it returns `y ← outputGen`. Both worlds answer and record every query. The sticky
final-validity monitor checks the target cap, distinct target tweaks, and target/collection
disjointness only in the experiment's final conjunction; repeated collection-only tweaks remain
valid. These declarations live in `TweakableHash.SM_DT_UD_SourceFinalValidity` so that the
winning semantics are visible at every public use site.

The source security quantity is oriented: `DirectedAdvantage` is the signed real gap
`Pr[real = true] - Pr[ideal = true]`. It can be negative, so swapping the real and ideal worlds is
observable. `AbsoluteAdvantage` separately provides the symmetric ENNReal magnitude used by
orientation-independent bounds, with a proved bridge between the two views.

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

namespace SM_DT_UD_SourceFinalValidity

/-! ## The game -/

/-- Which response distribution the challenge oracle uses. -/
inductive World
  /-- Sample a hidden input and evaluate the attacked tweakable hash. -/
  | real
  /-- Sample directly from the problem's output distribution. -/
  | ideal
deriving DecidableEq, Repr

/-- The challenge oracle takes a target tweak and returns a digest in both worlds. -/
abbrev challengeSpec (Tweak Y : Type) : OracleSpec Tweak := Tweak →ₒ Y

/-- An SM-DT-UD problem: attacked hash, explicit real and ideal sampling distributions, shared
collection, and target cap. -/
structure Problem (ι PkSeed Tweak M Y : Type) where
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
def Problem.standalone (th : TweakableHash PkSeed Tweak M Y)
    (inputGen : ProbComp M) (outputGen : ProbComp Y) (numTargets : ℕ) :
    Problem Empty PkSeed Tweak M Y where
  th := th
  inputGen := inputGen
  outputGen := outputGen
  thColl := .empty PkSeed Tweak Y
  numTargets := numTargets

/-- Target tweaks, collection tweaks, and the sticky final-validity bit. -/
abbrev State (Tweak : Type) : Type := SourceFinalValidity.State Tweak Tweak

/-- An SM-DT-UD adversary split exactly at the public-seed reveal. -/
structure Adversary (prob : Problem ι PkSeed Tweak M Y) where
  /-- Private state passed from target selection to the distinguishing phase. -/
  State : Type
  /-- Select target tweaks with private randomness and collection access, but without the seed. -/
  pick : OracleComp
    (unifSpec +
      (challengeSpec Tweak Y + SourceFinalValidity.collectionSpec prob.thColl)) State
  /-- After the seed is revealed and both oracles are removed, return the distinguishing bit. -/
  distinguish : State → PkSeed → ProbComp Bool

/-- One challenge response. Only this distribution differs between the real and ideal worlds. -/
def response (world : World)
    (prob : Problem ι PkSeed Tweak M Y) (pk : PkSeed) (t : Tweak) : ProbComp Y :=
  match world with
  | .real => do
      let m ← prob.inputGen
      return prob.th.eval pk t m
  | .ideal => prob.outputGen

/-- The always-answering challenge oracle. Every query is appended to the target history; a cap,
duplicate-target, or collection clash poisons final validity without changing the response. -/
def challengeOracle [DecidableEq Tweak] (world : World)
    (prob : Problem ι PkSeed Tweak M Y) (pk : PkSeed) :
    QueryImpl (challengeSpec Tweak Y)
      (StateT (State Tweak) ProbComp) :=
  fun t => do
    let y ← (response world prob pk t :
      StateT (State Tweak) ProbComp Y)
    let st ← get
    set (st.recordTarget prob.numTargets id t)
    return y

/-- Challenge and collection access over one final-validity state and one hidden seed. -/
def oracles [DecidableEq Tweak] (world : World)
    (prob : Problem ι PkSeed Tweak M Y) (pk : PkSeed) :
    QueryImpl
      (unifSpec +
        (challengeSpec Tweak Y + SourceFinalValidity.collectionSpec prob.thColl))
      (StateT (State Tweak) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (State Tweak) ProbComp) +
    (challengeOracle world prob pk +
      SourceFinalValidity.collectionOracle (Q := Tweak) id prob.thColl pk)

/-- The source-final-validity SM-DT-UD experiment. The seed is hidden during `pick`, revealed to
`distinguish`, and success is the adversary's bit conjoined with the final validity monitor. -/
noncomputable def Experiment [DecidableEq Tweak]
    (world : World) {prob : Problem ι PkSeed Tweak M Y}
    (adv : Adversary prob) : ProbComp Bool := do
  let pk ← prob.th.seedGen
  let (privateState, gameState) ←
    (simulateQ (oracles world prob pk) adv.pick).run .initial
  let b ← adv.distinguish privateState pk
  return gameState.valid && b

/-- Success probability when challenges are sampled hash images. -/
noncomputable def RealSuccess [DecidableEq Tweak]
    {prob : Problem ι PkSeed Tweak M Y} (adv : Adversary prob) : ℝ≥0∞ :=
  Pr[= true | Experiment .real adv]

/-- Success probability when challenges are sampled directly from `outputGen`. -/
noncomputable def IdealSuccess [DecidableEq Tweak]
    {prob : Problem ι PkSeed Tweak M Y} (adv : Adversary prob) : ℝ≥0∞ :=
  Pr[= true | Experiment .ideal adv]

/-- Source SM-DT-UD advantage: the directed signed gap from the real world to the ideal world. -/
noncomputable def DirectedAdvantage [DecidableEq Tweak]
    {prob : Problem ι PkSeed Tweak M Y} (adv : Adversary prob) : ℝ :=
  (RealSuccess adv).toReal - (IdealSuccess adv).toReal

/-- Orientation-independent magnitude of the SM-DT-UD advantage in `ℝ≥0∞`. This is
deliberately separate from the source game's signed `DirectedAdvantage`. -/
noncomputable def AbsoluteAdvantage [DecidableEq Tweak]
    {prob : Problem ι PkSeed Tweak M Y} (adv : Adversary prob) : ℝ≥0∞ :=
  ENNReal.absDiff (RealSuccess adv) (IdealSuccess adv)

/-- The ENNReal absolute gap is exactly the absolute value of the source directed advantage. -/
theorem absoluteAdvantage_toReal_eq_abs_directedAdvantage [DecidableEq Tweak]
    {prob : Problem ι PkSeed Tweak M Y} (adv : Adversary prob) :
    (AbsoluteAdvantage adv).toReal = |DirectedAdvantage adv| := by
  exact ENNReal.absDiff_toReal probOutput_ne_top probOutput_ne_top

/-- Forgetting orientation gives a sound upper bound on the directed source advantage. -/
theorem directedAdvantage_le_absoluteAdvantage_toReal [DecidableEq Tweak]
    {prob : Problem ι PkSeed Tweak M Y} (adv : Adversary prob) :
    DirectedAdvantage adv ≤ (AbsoluteAdvantage adv).toReal := by
  rw [absoluteAdvantage_toReal_eq_abs_directedAdvantage]
  exact le_abs_self _

/-! ## Oracle behavior pins -/

variable [DecidableEq Tweak] {world : World}
  {prob : Problem ι PkSeed Tweak M Y} {pk : PkSeed} {t : Tweak}
  {st : State Tweak}

/-- Every challenge is answered and recorded, including challenges that poison final validity. -/
theorem challengeOracle_run :
    (challengeOracle world prob pk t).run st =
      (fun y => (y, st.recordTarget prob.numTargets id t)) <$>
        response world prob pk t := by
  simp [challengeOracle, Functor.map_map]

end SM_DT_UD_SourceFinalValidity

end TweakableHash
