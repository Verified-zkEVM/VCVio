/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.DataEncapMech
public import VCVio.EvalDist.Monad.Bool

/-!
# Real-or-random one-time IND-CPA for DEMs

This file defines the real-or-random (ROR) one-time IND-CPA game for a `DEMScheme` and relates
it to the left-or-right (LOR) game `DEMScheme.IND_CPA_Game` (Bellare, Desai, Jokipii, Rogaway,
FOCS 1997).

In the ROR game the adversary chooses one message; the challenger encrypts either that message
or an independent uniform message. Both advantages are `Measure.boolBias` of a fair hidden-bit
game, which equals the distance `|Pr[1 | b = true] - Pr[1 | b = false]|` between its two
branches (`Measure.boolBias_bind_coin`). Under this normalization:

* `DEMScheme.realOrRandomAdvantage_eq_IND_CPA_Advantage`: every ROR adversary gives a LOR
  adversary with exactly the same advantage, which pairs the chosen message with a fresh
  uniform one.
* `DEMScheme.IND_CPA_Advantage_le_realOrRandomAdvantage_add`: the LOR advantage is at most the
  sum of the ROR advantages of the two adversaries that forward the left or the right message,
  through the hybrid that encrypts a uniform message.
  `DEMScheme.IND_CPA_Advantage_le_two_mul_max_realOrRandomAdvantage` states the same bound as
  twice the larger ROR advantage.

The ROR definitions use lowerCamelCase names, following the naming linter, while the LOR
definitions in `VCVio.CryptoFoundations.DataEncapMech` keep their `IND_CPA_*` names.
-/

public section

open OracleSpec OracleComp MeasureTheory ENNReal

namespace DEMScheme

variable {K M C : Type} {ι : Type} {spec : OracleSpec ι}

/-- Two-phase one-time real-or-random IND-CPA adversary for a DEM. The key is hidden, so the
message-selection phase receives no public input. -/
structure RealOrRandomAdversary (_dem : DEMScheme (OracleComp spec) K M C) where
  /-- State passed from message selection to the distinguisher. -/
  State : Type
  /-- Choose the challenge message and the state for the distinguisher. -/
  chooseMessage : OracleComp spec (M × State)
  /-- Guess from the state and the challenge ciphertext whether the chosen message was
  encrypted. -/
  distinguish : State → C → OracleComp spec Bool

section Games

variable [SampleableType K] [SampleableType M]

/-- Fixed-branch one-time real-or-random IND-CPA experiment for a DEM. The branch `true`
encrypts the adversary's message and the branch `false` encrypts an independent uniform message.
The uniform message is sampled in both branches, after message selection. -/
@[expose]
noncomputable def realOrRandomExperiment {dem : DEMScheme (OracleComp spec) K M C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : dem.RealOrRandomAdversary) (b : Bool) : OracleComp spec Bool := do
  let k ← runtime.liftProbComp ($ᵗ K)
  let (m, st) ← adversary.chooseMessage
  let m' ← runtime.liftProbComp ($ᵗ M)
  let c ← dem.encrypt k (if b then m else m')
  adversary.distinguish st c

/-- Game-form one-time real-or-random IND-CPA experiment for a DEM. -/
@[expose]
noncomputable def realOrRandomGame {dem : DEMScheme (OracleComp spec) K M C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : dem.RealOrRandomAdversary) : OracleComp spec Bool := do
  let b ← runtime.liftProbComp ($ᵗ Bool)
  let k ← runtime.liftProbComp ($ᵗ K)
  let (m, st) ← adversary.chooseMessage
  let m' ← runtime.liftProbComp ($ᵗ M)
  let c ← dem.encrypt k (if b then m else m')
  let b' ← adversary.distinguish st c
  return (b == b')

/-- One-time real-or-random IND-CPA advantage for a DEM: the bias of the single game. -/
@[expose]
noncomputable def realOrRandomAdvantage {dem : DEMScheme (OracleComp spec) K M C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : dem.RealOrRandomAdversary) : ℝ≥0∞ :=
  (runtime.evalDist (realOrRandomGame runtime adversary)).boolBias

end Games

/-! ## Reductions -/

section Reductions

variable {dem : DEMScheme (OracleComp spec) K M C}

/-- ROR adversary forwarding one side of a LOR adversary's message pair: the right message `m₁`
when `side = true` and the left message `m₀` otherwise. -/
def RealOrRandomAdversary.ofLeftOrRight (adversary : dem.IND_CPA_Adversary) (side : Bool) :
    dem.RealOrRandomAdversary where
  State := adversary.State
  chooseMessage := do
    let (m₀, m₁, st) ← adversary.chooseMessages
    return (if side then m₁ else m₀, st)
  distinguish := adversary.distinguish

/-- LOR adversary built from a ROR adversary: the right message is the ROR adversary's message
and the left message is a fresh uniform message, sampled through the runtime's public
randomness. -/
def RealOrRandomAdversary.toLeftOrRight [SampleableType M]
    (runtime : ProbCompRuntime (OracleComp spec)) (adversary : dem.RealOrRandomAdversary) :
    dem.IND_CPA_Adversary where
  State := adversary.State
  chooseMessages := do
    let (m, st) ← adversary.chooseMessage
    let m' ← runtime.liftProbComp ($ᵗ M)
    return (m', m, st)
  distinguish := adversary.distinguish

end Reductions

/-! ## ROR to LOR -/

section RORToLOR

variable [SampleableType K] [SampleableType M] {dem : DEMScheme (OracleComp spec) K M C}

/-- Each fixed-branch ROR experiment is the corresponding fixed-branch LOR experiment of
`RealOrRandomAdversary.toLeftOrRight`. -/
theorem realOrRandomExperiment_eq_IND_CPA_Experiment (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : dem.RealOrRandomAdversary) (b : Bool) :
    realOrRandomExperiment runtime adversary b =
      IND_CPA_Experiment runtime (adversary.toLeftOrRight runtime) b := by
  simp only [realOrRandomExperiment, IND_CPA_Experiment, RealOrRandomAdversary.toLeftOrRight,
    bind_assoc, pure_bind]

/-- The ROR game is the LOR game of `RealOrRandomAdversary.toLeftOrRight`. -/
theorem realOrRandomGame_eq_IND_CPA_Game (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : dem.RealOrRandomAdversary) :
    realOrRandomGame runtime adversary =
      IND_CPA_Game runtime (adversary.toLeftOrRight runtime) := by
  simp only [realOrRandomGame, IND_CPA_Game, RealOrRandomAdversary.toLeftOrRight, bind_assoc,
    pure_bind]

/-- ROR security follows from LOR security with no loss: the ROR advantage of an adversary equals
the LOR advantage of `RealOrRandomAdversary.toLeftOrRight`. No runtime coherence hypotheses are
needed, because the two games coincide as computations. -/
theorem realOrRandomAdvantage_eq_IND_CPA_Advantage
    (runtime : ProbCompRuntime (OracleComp spec)) (adversary : dem.RealOrRandomAdversary) :
    dem.realOrRandomAdvantage runtime adversary =
      dem.IND_CPA_Advantage runtime (adversary.toLeftOrRight runtime) := by
  rw [realOrRandomAdvantage, IND_CPA_Advantage, realOrRandomGame_eq_IND_CPA_Game]

end RORToLOR

/-! ## LOR to ROR -/

section LORToROR

variable [SampleableType K] [SampleableType M] {dem : DEMScheme (OracleComp spec) K M C}

/-- LOR security follows from ROR security with a factor-two loss (sum form): the LOR advantage of
an adversary is at most the sum of the ROR advantages of the two adversaries
`RealOrRandomAdversary.ofLeftOrRight` that forward its left and its right message. The proof is the
hybrid through the experiment that encrypts a uniform message.

The runtime coherence hypotheses are those of the KEM+DEM composition theorem in
`VCVio.CryptoFoundations.KEMDEM`: runtime measures preserve `pure` and measurable binds, agree
with the canonical `ProbComp` measure on lifted public randomness, and are total on Boolean
computations. Totality is used by `Measure.boolBias_bind_coin`, which distinguishes missing
mass from the output `false`. -/
theorem IND_CPA_Advantage_le_realOrRandomAdvantage_add
    (runtime : ProbCompRuntime (OracleComp spec)) (adversary : dem.IND_CPA_Adversary)
    (heval_pure : ∀ {α : Type} [MeasurableSpace α] (a : α),
        runtime.evalDist (pure a : OracleComp spec α) = Measure.dirac a)
    (heval_bind : ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
        (mx : OracleComp spec α) (f : α → OracleComp spec β),
        Measurable (fun a => runtime.evalDist (f a)) →
        runtime.evalDist (mx >>= f) =
          Measure.bind (runtime.evalDist mx) fun a => runtime.evalDist (f a))
    (heval_liftProbComp : ∀ {α : Type} [MeasurableSpace α] (pc : ProbComp α),
        runtime.evalDist (runtime.liftProbComp pc) = 𝒟[pc])
    (hno_fail : ∀ (mx : OracleComp spec Bool),
        runtime.evalDist mx {true} + runtime.evalDist mx {false} = 1) :
    dem.IND_CPA_Advantage runtime adversary ≤
      dem.realOrRandomAdvantage runtime (.ofLeftOrRight adversary false) +
      dem.realOrRandomAdvantage runtime (.ofLeftOrRight adversary true) := by
  let : MeasurableSpace M := ⊤
  let : EvalDistSemantics (OracleComp spec) := {
    denote mx := runtime.evalDist mx
    apply_univ_le_one mx := runtime.evalDist_apply_univ_le_one mx }
  let : LawfulEvalDistSemantics (OracleComp spec) := {
    denote_pure a := heval_pure a
    denote_bind mx f hf := heval_bind mx f hf }
  have evalDist_eq_runtime {α : Type} [MeasurableSpace α] (mx : OracleComp spec α) :
      𝒟[mx] = runtime.evalDist mx := rfl
  have hprob (mx : OracleComp spec Bool) : IsProbabilityMeasure 𝒟[mx] :=
    ⟨by rw [← Measure.apply_true_add_apply_false]; exact hno_fail mx⟩
  let coin := runtime.liftProbComp ($ᵗ Bool)
  let key := runtime.liftProbComp ($ᵗ K)
  let unif := runtime.liftProbComp ($ᵗ M)
  let lor (b : Bool) : OracleComp spec Bool := do
    let k ← key
    let (m₀, m₁, st) ← adversary.chooseMessages
    let c ← dem.encrypt k (if b then m₁ else m₀)
    adversary.distinguish st c
  let real (side : Bool) : OracleComp spec Bool := do
    let k ← key
    let (m₀, m₁, st) ← adversary.chooseMessages
    let _ ← unif
    let c ← dem.encrypt k (if side then m₁ else m₀)
    adversary.distinguish st c
  let rnd : OracleComp spec Bool := do
    let k ← key
    let (_, _, st) ← adversary.chooseMessages
    let m' ← unif
    let c ← dem.encrypt k m'
    adversary.distinguish st c
  have hcoin (b : Bool) : 𝒟[coin] {b} = 1 / 2 := by
    rw [evalDist_eq_runtime, heval_liftProbComp, SampleableType.evalDist_uniformSample,
      ProbabilityTheory.uniformOn_univ_apply_singleton]
    simp [Fintype.card_bool]
  have hunif : 𝒟[unif] Set.univ = 1 := by
    rw [evalDist_eq_runtime, heval_liftProbComp, SampleableType.evalDist_uniformSample]
    simp
  have hreal (side : Bool) : 𝒟[real side] = 𝒟[lor side] := by
    refine evalDist_bind_congr _ _ _ fun k => ?_
    refine evalDist_bind_congr _ _ _ fun ⟨m₀, m₁, st⟩ => ?_
    rw [_root_.evalDist_bind_const, hunif, one_smul]
  have hlor : runtime.evalDist (IND_CPA_Game runtime adversary) =
      𝒟[do
        let b ← coin
        let z ← if b then lor true else lor false
        pure (b == z)] := by
    rw [evalDist_eq_runtime, IND_CPA_Game]
    congr 1
    refine bind_congr fun b => ?_
    cases b <;> simp only [lor, key, bind_assoc, Bool.false_eq_true, ite_true, ite_false]
  have hror (side : Bool) :
      runtime.evalDist (realOrRandomGame runtime (.ofLeftOrRight adversary side)) =
      𝒟[do
        let b ← coin
        let z ← if b then real side else rnd
        pure (b == z)] := by
    rw [evalDist_eq_runtime, realOrRandomGame]
    congr 1
    refine bind_congr fun b => ?_
    cases b <;> simp only [real, rnd, key, unif, RealOrRandomAdversary.ofLeftOrRight, bind_assoc,
      pure_bind, Bool.false_eq_true, ite_true, ite_false]
  rw [IND_CPA_Advantage, realOrRandomAdvantage, realOrRandomAdvantage, hlor, hror, hror,
    evalDist_boolBias_bind_coin coin _ _ (hcoin true) (hcoin false),
    evalDist_boolBias_bind_coin coin _ _ (hcoin true) (hcoin false),
    evalDist_boolBias_bind_coin coin _ _ (hcoin true) (hcoin false), hreal, hreal,
    Measure.boolDist_comm 𝒟[lor false], add_comm]
  exact Measure.boolDist_triangle _ _ _

/-- Factor-two form of `IND_CPA_Advantage_le_realOrRandomAdvantage_add`: the LOR advantage is at
most twice the larger ROR advantage of the two forwarding adversaries. -/
theorem IND_CPA_Advantage_le_two_mul_max_realOrRandomAdvantage
    (runtime : ProbCompRuntime (OracleComp spec)) (adversary : dem.IND_CPA_Adversary)
    (heval_pure : ∀ {α : Type} [MeasurableSpace α] (a : α),
        runtime.evalDist (pure a : OracleComp spec α) = Measure.dirac a)
    (heval_bind : ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
        (mx : OracleComp spec α) (f : α → OracleComp spec β),
        Measurable (fun a => runtime.evalDist (f a)) →
        runtime.evalDist (mx >>= f) =
          Measure.bind (runtime.evalDist mx) fun a => runtime.evalDist (f a))
    (heval_liftProbComp : ∀ {α : Type} [MeasurableSpace α] (pc : ProbComp α),
        runtime.evalDist (runtime.liftProbComp pc) = 𝒟[pc])
    (hno_fail : ∀ (mx : OracleComp spec Bool),
        runtime.evalDist mx {true} + runtime.evalDist mx {false} = 1) :
    dem.IND_CPA_Advantage runtime adversary ≤
      2 * max (dem.realOrRandomAdvantage runtime (.ofLeftOrRight adversary false))
        (dem.realOrRandomAdvantage runtime (.ofLeftOrRight adversary true)) :=
  (IND_CPA_Advantage_le_realOrRandomAdvantage_add runtime adversary heval_pure heval_bind
    heval_liftProbComp hno_fail).trans <|
      (add_le_add (le_max_left _ _) (le_max_right _ _)).trans_eq (two_mul _).symm

end LORToROR

end DEMScheme
