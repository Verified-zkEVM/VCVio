/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.SecExp.Measure
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.ProbCompLift
public import VCVio.CryptoFoundations.LeftOrRight
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# Data Encapsulation Mechanisms

This file defines data encapsulation mechanisms (DEMs), their correctness notion, and two
left-or-right IND-CPA games under a uniform key.

* The one-time game `DEMScheme.IND_CPA_OneTime_Game`, used by the KEM+DEM composition theorem:
  a two-phase adversary chooses two messages and receives the encryption of one of them.
* The multi-query game `DEMScheme.IND_CPA_Game`: the adversary keeps the DEM's own oracles and
  gains the left-or-right challenge oracle `LeftOrRight.oracle` of
  `VCVio.CryptoFoundations.LeftOrRight`, which encrypts under the hidden key every admissible
  pair it is asked, and a leakage function decides which pairs are admissible. Query budgets are
  predicates on the adversary (`DEMScheme.IND_CPA_Adversary.MakesAtMostQueries`).

`DEMScheme.IND_CPA_OneTime_Advantage_eq_IND_CPA_Advantage` relates the two: the one-time
advantage of an adversary is the multi-query advantage, without leakage, of
`DEMScheme.IND_CPA_OneTime_Adversary.toMultiQuery`, which makes a single challenge query.
-/

@[expose] public section

universe u v

open OracleSpec OracleComp ENNReal

/-- A data encapsulation mechanism with key space `K`, message space `M`, and ciphertext space
`C`. The key is supplied externally, matching the proof-ladders DEM model. -/
structure DEMScheme (m : Type → Type u) [Monad m] (K M C : Type) where
  /-- Encrypt a message under a symmetric key. -/
  encrypt : K → M → m C
  /-- Decrypt a ciphertext under a symmetric key. -/
  decrypt : K → C → m M

namespace DEMScheme
variable {m : Type → Type v} [Monad m] {K M C : Type}
  (dem : DEMScheme m K M C)

section Correct

variable [DecidableEq M]

/-- Correctness experiment for a DEM under an externally supplied key. -/
def correctnessExperiment (k : K) (msg : M) : m Bool :=
  do
    let c ← dem.encrypt k msg
    let msg' ← dem.decrypt k c
    return decide (msg' = msg)

/-- Perfect correctness for a DEM: every externally supplied key decrypts honest ciphertexts
correctly with probability `1`. -/
def PerfectlyCorrect (runtime : ProbCompRuntime m) : Prop :=
  ∀ k : K, ∀ msg : M, runtime.evalDist (dem.correctnessExperiment k msg) {true} = 1

end Correct

section IND_CPA_OneTime

variable {ι : Type} {spec : OracleSpec ι} [SampleableType K]

/-- Two-phase one-time IND-CPA adversary for a DEM. The key is hidden, so the message-selection
phase receives no public input. -/
structure IND_CPA_OneTime_Adversary (_dem : DEMScheme (OracleComp spec) K M C) where
  /-- The state the adversary carries from the message-choice phase to the guessing phase. -/
  State : Type
  /-- Choose the two challenge messages together with the state to pass to `distinguish`. -/
  chooseMessages : OracleComp spec (M × M × State)
  /-- Given the saved state and the challenge ciphertext, guess which challenge message was
  encrypted. -/
  distinguish : State → C → OracleComp spec Bool

/-- Fixed-branch one-time IND-CPA experiment for a DEM, matching the source proof-ladders
`DEM_1CPA_Exp.run(b)` presentation. -/
noncomputable def IND_CPA_OneTime_Experiment {dem : DEMScheme (OracleComp spec) K M C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : dem.IND_CPA_OneTime_Adversary) (b : Bool) : OracleComp spec Bool := do
  let k ← runtime.liftProbComp ($ᵗ K)
  let (m₀, m₁, st) ← adversary.chooseMessages
  let c ← dem.encrypt k (if b then m₁ else m₀)
  adversary.distinguish st c

/-- Game-form one-time IND-CPA experiment for a DEM. -/
noncomputable def IND_CPA_OneTime_Game {dem : DEMScheme (OracleComp spec) K M C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : dem.IND_CPA_OneTime_Adversary) : OracleComp spec Bool := do
  let b ← runtime.liftProbComp ($ᵗ Bool)
  let k ← runtime.liftProbComp ($ᵗ K)
  let (m₀, m₁, st) ← adversary.chooseMessages
  let c ← dem.encrypt k (if b then m₁ else m₀)
  let b' ← adversary.distinguish st c
  return (b == b')

/-- One-time IND-CPA advantage for a DEM, defined canonically as the bias of the single game. -/
noncomputable def IND_CPA_OneTime_Advantage {dem : DEMScheme (OracleComp spec) K M C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : dem.IND_CPA_OneTime_Adversary) : ℝ≥0∞ :=
  (runtime.evalDist (IND_CPA_OneTime_Game runtime adversary)).boolBias

/-- The canonical one-time IND-CPA advantage is definitionally the bias of the single game. -/
theorem IND_CPA_OneTime_Advantage_eq_game_bias {dem : DEMScheme (OracleComp spec) K M C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : dem.IND_CPA_OneTime_Adversary) :
    dem.IND_CPA_OneTime_Advantage runtime adversary =
      (runtime.evalDist (dem.IND_CPA_OneTime_Game runtime adversary)).boolBias := rfl

end IND_CPA_OneTime

section IND_CPA

variable {ι : Type} {spec : OracleSpec ι}

/-- Multi-query IND-CPA adversary for a DEM: a computation with the DEM's own oracles `spec` and
the left-or-right challenge oracle `LeftOrRight.spec M C`, returning a guess of the hidden bit.
The key is hidden, so the adversary receives no input. -/
abbrev IND_CPA_Adversary (_dem : DEMScheme (OracleComp spec) K M C) :=
  OracleComp (spec + LeftOrRight.spec M C) Bool

/-- A multi-query IND-CPA adversary `MakesAtMostQueries q` when it makes at most `q` queries to
the challenge oracle. Queries to the DEM's own oracles are unrestricted. -/
def IND_CPA_Adversary.MakesAtMostQueries {dem : DEMScheme (OracleComp spec) K M C}
    (adversary : dem.IND_CPA_Adversary) (q : ℕ) : Prop :=
  OracleComp.IsQueryBoundP adversary (· matches .inr _) q

variable [SampleableType K] {Λ : Type} [DecidableEq Λ]

/-- Fixed-branch multi-query IND-CPA experiment for a DEM at hidden bit `b`, for the leakage
function `leak`: sample a uniform key `k`, then run the adversary with its queries to `spec`
forwarded and its challenge queries answered by `LeftOrRight.oracle (dem.encrypt k) leak b`. -/
noncomputable def IND_CPA_Experiment (dem : DEMScheme (OracleComp spec) K M C)
    (runtime : ProbCompRuntime (OracleComp spec)) (leak : M → Λ)
    (adversary : dem.IND_CPA_Adversary) (b : Bool) : OracleComp spec Bool := do
  let k ← runtime.liftProbComp ($ᵗ K)
  simulateQ (QueryImpl.id' spec + LeftOrRight.oracle (dem.encrypt k) leak b) adversary

/-- Game-form multi-query IND-CPA experiment for a DEM: sample a hidden bit, run the
fixed-branch experiment at that bit, and return whether the adversary guessed it. -/
noncomputable def IND_CPA_Game (dem : DEMScheme (OracleComp spec) K M C)
    (runtime : ProbCompRuntime (OracleComp spec)) (leak : M → Λ)
    (adversary : dem.IND_CPA_Adversary) : OracleComp spec Bool := do
  let b ← runtime.liftProbComp ($ᵗ Bool)
  let b' ← dem.IND_CPA_Experiment runtime leak adversary b
  return (b == b')

/-- Multi-query IND-CPA advantage for a DEM, defined canonically as the bias of the single
game. -/
noncomputable def IND_CPA_Advantage (dem : DEMScheme (OracleComp spec) K M C)
    (runtime : ProbCompRuntime (OracleComp spec)) (leak : M → Λ)
    (adversary : dem.IND_CPA_Adversary) : ℝ≥0∞ :=
  (runtime.evalDist (dem.IND_CPA_Game runtime leak adversary)).boolBias

/-- The canonical multi-query IND-CPA advantage is definitionally the bias of the single game. -/
theorem IND_CPA_Advantage_eq_game_bias (dem : DEMScheme (OracleComp spec) K M C)
    (runtime : ProbCompRuntime (OracleComp spec)) (leak : M → Λ)
    (adversary : dem.IND_CPA_Adversary) :
    dem.IND_CPA_Advantage runtime leak adversary =
      (runtime.evalDist (dem.IND_CPA_Game runtime leak adversary)).boolBias := rfl

end IND_CPA

/-! ## One-time adversaries as multi-query adversaries -/

section OneTimeToMultiQuery

variable {ι : Type} {spec : OracleSpec ι} {dem : DEMScheme (OracleComp spec) K M C}

/-- The multi-query adversary that runs a one-time adversary: it chooses the two messages, makes
one challenge query on them, and distinguishes on the answer. A `none` answer, which the
challenge oracle without leakage never gives, is met with the guess `false`. -/
def IND_CPA_OneTime_Adversary.toMultiQuery (adversary : dem.IND_CPA_OneTime_Adversary) :
    dem.IND_CPA_Adversary := do
  let (m₀, m₁, st) ← liftM adversary.chooseMessages
  let c? : Option C ← (spec + LeftOrRight.spec M C).query (.inr (m₀, m₁))
  match c? with
  | some c => liftM (adversary.distinguish st c)
  | none => pure false

/-- `IND_CPA_OneTime_Adversary.toMultiQuery` makes one challenge query. -/
theorem IND_CPA_OneTime_Adversary.toMultiQuery_makesAtMostQueries
    (adversary : dem.IND_CPA_OneTime_Adversary) :
    adversary.toMultiQuery.MakesAtMostQueries 1 := by
  have hlift {α : Type} (oa : OracleComp spec α) :
      OracleComp.IsQueryBoundP (liftM oa : OracleComp (spec + LeftOrRight.spec M C) α)
        (· matches .inr _) 0 := by
    rw [← OracleComp.liftComp_eq_liftM]
    exact OracleComp.IsQueryBoundP.liftComp_subSpec (p := fun _ => False)
      (fun t => by simp [SubSpec.onQuery]) (OracleComp.isQueryBoundP_false oa 0)
  rw [IND_CPA_Adversary.MakesAtMostQueries, toMultiQuery, ← zero_add 1]
  refine OracleComp.isQueryBoundP_bind (hlift _) fun ⟨m₀, m₁, st⟩ _ => ?_
  refine (OracleComp.isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inr Nat.one_pos, ?_⟩
  rintro (_ | c)
  · exact OracleComp.isQueryBoundP_pure _ _ _
  · exact hlift _

/-- Simulating `IND_CPA_OneTime_Adversary.toMultiQuery` against the challenge oracle without
leakage runs the one-time adversary on the encryption of the message that the hidden bit
selects. -/
theorem IND_CPA_OneTime_Adversary.simulateQ_toMultiQuery
    (adversary : dem.IND_CPA_OneTime_Adversary) (k : K) (b : Bool) :
    simulateQ (QueryImpl.id' spec + LeftOrRight.oracle (dem.encrypt k) (fun _ => ()) b)
        adversary.toMultiQuery = (do
      let (m₀, m₁, st) ← adversary.chooseMessages
      let c ← dem.encrypt k (if b then m₁ else m₀)
      adversary.distinguish st c) := by
  rw [toMultiQuery, simulateQ_bind, QueryImpl.simulateQ_add_liftM_left, simulateQ_id']
  refine bind_congr fun ⟨m₀, m₁, st⟩ => ?_
  rw [QueryImpl.simulateQ_add_query_bind_right]
  simp [QueryImpl.simulateQ_add_liftM_left]

variable [SampleableType K]

/-- The fixed-branch multi-query experiment of `IND_CPA_OneTime_Adversary.toMultiQuery` without
leakage is the fixed-branch one-time experiment. -/
theorem IND_CPA_Experiment_toMultiQuery (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : dem.IND_CPA_OneTime_Adversary) (b : Bool) :
    dem.IND_CPA_Experiment runtime (fun _ => ()) adversary.toMultiQuery b =
      IND_CPA_OneTime_Experiment runtime adversary b := by
  simp only [IND_CPA_Experiment, IND_CPA_OneTime_Adversary.simulateQ_toMultiQuery,
    IND_CPA_OneTime_Experiment]

/-- The multi-query game of `IND_CPA_OneTime_Adversary.toMultiQuery` without leakage is the
one-time game. -/
theorem IND_CPA_Game_toMultiQuery (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : dem.IND_CPA_OneTime_Adversary) :
    dem.IND_CPA_Game runtime (fun _ => ()) adversary.toMultiQuery =
      IND_CPA_OneTime_Game runtime adversary := by
  simp only [IND_CPA_Game, IND_CPA_Experiment_toMultiQuery, IND_CPA_OneTime_Experiment,
    IND_CPA_OneTime_Game, bind_assoc]

/-- The one-time IND-CPA advantage of an adversary is the multi-query IND-CPA advantage, without
leakage, of `IND_CPA_OneTime_Adversary.toMultiQuery`, which makes one challenge query
(`IND_CPA_OneTime_Adversary.toMultiQuery_makesAtMostQueries`). No runtime hypotheses are needed,
because the two games coincide as computations. -/
theorem IND_CPA_OneTime_Advantage_eq_IND_CPA_Advantage
    (runtime : ProbCompRuntime (OracleComp spec)) (adversary : dem.IND_CPA_OneTime_Adversary) :
    dem.IND_CPA_OneTime_Advantage runtime adversary =
      dem.IND_CPA_Advantage runtime (fun _ => ()) adversary.toMultiQuery := by
  rw [IND_CPA_OneTime_Advantage, IND_CPA_Advantage, IND_CPA_Game_toMultiQuery]

end OneTimeToMultiQuery

end DEMScheme
