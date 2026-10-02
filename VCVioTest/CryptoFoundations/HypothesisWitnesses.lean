/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio

/-!
# Hypothesis bundles with kernel-checked witnesses

The security-hypothesis structures of `VCVio.CryptoFoundations` that carry a reduction, simulator,
extractor or generator as data, one example per row of the ledger in `docs/agents/crypto.md`: each
projects the witness out as a program or function, so a consumer can run it and a theorem can
name it, where an existential would only assert that one exists.
-/

public section

open OracleComp

namespace VCVioTest.CryptoFoundations.HypothesisWitnesses

/-- A generable relation carries its generator; `gen_sound` checks every generated pair. -/
example {X W : Type} {r : X → W → Bool} (hr : GenerableRelation X W r) : ProbComp (X × W) :=
  hr.gen

/-- A Σ-protocol carries its simulator and its witness extractor; `SigmaProtocol.SpeciallySound`
checks the extractor on accepting transcripts. -/
example {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel) (ω₁ ω₂ : Chal) (p₁ p₂ : Resp) :
    ProbComp Wit :=
  σ.extract ω₁ p₁ ω₂ p₂

/-- A trapdoor extractor carries its trapdoor setup and its extraction program;
`CommitmentScheme.TrapdoorExtractor.SetupConsistent` and `CommitmentScheme.extractExperiment`
check them. -/
example {PP TD C M : Type} (ext : CommitmentScheme.TrapdoorExtractor PP TD C M) (td : TD)
    (c : C) : ProbComp M :=
  ext.extract td c

/-- A preimage sampleable function carries its trapdoor sampler;
`PreimageSampleableFunction.Correct` checks its preimages. -/
example {PK SK Domain Range : Type} (psf : PreimageSampleableFunction PK SK Domain Range)
    (pk : PK) (sk : SK) (t : Range) : ProbComp Domain :=
  psf.trapdoorSample pk sk t

/-- A trapdoor permutation carries its key generator and its inverse;
`OneWay.TrapdoorPermutation.Correct` checks the inverse on generated keys. -/
example {PK SK X : Type} (tdp : OneWay.TrapdoorPermutation PK SK X) (sk : SK) : X → X :=
  tdp.inverse sk

/-- A knowledge-transition family carries its pre-challenge extractor;
`RoundByRound.KnowledgeTransitionFamily.IsBounded` checks the bad-transition probability. -/
example {Round : Type} {Context : Round → Type}
    (games : RoundByRound.KnowledgeTransitionFamily Round Context) (round : Round)
    (context : Context round) (challenge : games.Challenge round)
    (witness : games.WitnessAfter round) : games.WitnessBefore round :=
  games.extractBefore round context challenge witness

/-- A knowledge-extraction family carries its total candidate-witness extractor;
`RoundByRound.KnowledgeExtractionFamily.ExtractionCondition` checks its output when the escape
trigger fires. -/
example {rounds : ℕ} (games : RoundByRound.KnowledgeExtractionFamily rounds) (round : Fin rounds)
    (context : games.Context round.castSucc) (message : games.Message round) : games.Witness :=
  games.extract round context message

/-- A reduction with cost carries the reduction as a function; `cost_bound` checks its cost
against the transform. -/
example {Adv Adv' σ σ' : Type} {cost : Adv → ℕ → σ} {cost' : Adv' → ℕ → σ'} [Preorder σ]
    [Preorder σ']
    (R : SecurityGame.ReductionWithCost cost cost') : Adv → Adv' :=
  R.reduce

end VCVioTest.CryptoFoundations.HypothesisWitnesses
