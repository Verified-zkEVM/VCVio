/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import VCVio.CryptoFoundations.TweakableHash
public import VCVio.OracleComp.SimSemantics.Append
public import ToMathlib.Control.StateT

/-!
# Multi-target security games for tweakable-hash collections

This file formalizes the classical single-function, multi-target, distinct-tweak target-collision
and preimage games for a member of a tweakable-hash collection (SM-DT-TCR-C and SM-DT-PRE-C).
The games enforce the security-critical order of information:

1. the challenger samples a public seed but does not reveal it;
2. the adversary places challenges through a member-specific oracle and may evaluate the rest of
   the collection under that same hidden seed;
3. only after challenge placement is the public seed revealed to the adversary's `find` phase.

Winning executions must use distinct challenge tweaks, must place at most `maxTargets`
challenges, and must not reuse any challenge tweak in the collection oracle.  The challenge and
collection transcripts are maintained by the experiment and are not trusted adversary output.
For PRE challenges the challenger samples and retains the hidden preimage at each query.

These are bounded-target games: `maxTargets` is an upper bound, matching the `t`-bounded
presentation of Barbosa--Dupressoir--Hülsing--Meijers--Strub.  They deliberately do not yet define
SM-DT-DSPR, SM-DT-UD-C, or SM-DT-OpenPRE; those notions require distinct winning predicates and
are follow-up work rather than aliases of preimage resistance.

The adversaries here are classical probabilistic `OracleComp` computations. This module does not
model quantum internal computation and therefore does not, by itself, establish the
post-quantum/QPT assumptions or reductions in Hülsing--Kudinov.

## References

- Hülsing and Kudinov, "Recovering the Tight Security Proof of SPHINCS+", Definitions 2, 3,
  and 7.
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified", Figures 5--7.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace MultiTarget

variable {PkSeed Tweak Digest : Type}

/-- A target member of a tweakable-hash collection together with the maximum number of
challenge queries. -/
structure CollectionProblem (PkSeed Tweak Digest : Type) where
  /-- The collection sharing one public-seed, tweak, and digest space. -/
  collection : TweakableHashCollection PkSeed Tweak Digest
  /-- The collection member challenged by the game. -/
  target : collection.Index
  /-- Upper bound on challenge queries made during target placement. -/
  maxTargets : ℕ

namespace CollectionProblem

variable (prob : CollectionProblem PkSeed Tweak Digest)

/-- Message space of the challenged collection member. -/
abbrev Message := prob.collection.Message prob.target

/-- The oracle that records target messages for SM-DT-TCR-C. -/
abbrev tcrChallengeSpec := (Tweak × prob.Message) →ₒ Digest

/-- The oracle that creates hidden random-preimage targets for SM-DT-PRE-C. -/
abbrev preimageChallengeSpec (_prob : CollectionProblem PkSeed Tweak Digest) := Tweak →ₒ Digest

/-- Oracle access during SM-DT-TCR-C target placement: private randomness, the challenge
member, and the entire collection under the same hidden public seed. -/
abbrev tcrPickSpec := unifSpec +
  (prob.tcrChallengeSpec + prob.collection.oracleSpec)

/-- Oracle access during SM-DT-PRE-C target placement. -/
abbrev preimagePickSpec := unifSpec +
  (prob.preimageChallengeSpec + prob.collection.oracleSpec)

end CollectionProblem

/-- Challenger-owned transcript of the target-placement phase.  `targets` retains the messages
hidden by PRE challenges and the messages explicitly submitted to TCR challenges;
`collectionTweaks` records every tweak used through the collection oracle. -/
structure Transcript (prob : CollectionProblem PkSeed Tweak Digest) where
  /-- Challenge tweaks and their underlying target messages, in query order. -/
  targets : List (Tweak × prob.Message)
  /-- Tweaks queried through the collection oracle, in query order. -/
  collectionTweaks : List Tweak

namespace Transcript

variable (prob : CollectionProblem PkSeed Tweak Digest)

/-- Empty transcript before target placement. -/
def empty : Transcript prob := ⟨[], []⟩

/-- Whether the transcript obeys the bounded, distinct-tweak, and collection-separation rules.
The selected target index is checked separately by the experiment's safe list lookup. -/
def Valid [DecidableEq Tweak] (transcript : Transcript prob) : Prop :=
  transcript.targets.length ≤ prob.maxTargets ∧
    (transcript.targets.map Prod.fst).Nodup ∧
    ∀ tweak ∈ transcript.targets.map Prod.fst, tweak ∉ transcript.collectionTweaks

instance [DecidableEq Tweak] (transcript : Transcript prob) : Decidable transcript.Valid :=
  by dsimp only [Valid]; infer_instance

end Transcript

/-! ## SM-DT-TCR-C -/

/-- A two-stage SM-DT-TCR-C adversary.  `pick` places targets without receiving the sampled public
seed, using the challenge and collection oracles under that hidden seed.  `find` receives the seed
and returns a target index together with a distinct colliding message. -/
structure TcrCAdversary (prob : CollectionProblem PkSeed Tweak Digest) where
  /-- Private state carried from target placement to collision finding. -/
  State : Type
  /-- Target-placement computation. -/
  pick : OracleComp prob.tcrPickSpec State
  /-- Collision-finding phase after the public seed is revealed. -/
  find : State → PkSeed → ProbComp (ℕ × prob.Message)

/-- Implementation of the TCR challenge oracle, recording every submitted target. -/
def tcrCChallengeImpl (prob : CollectionProblem PkSeed Tweak Digest) (pkSeed : PkSeed) :
    QueryImpl prob.tcrChallengeSpec (StateT (Transcript prob) ProbComp) := fun target => do
  modify fun transcript => { transcript with targets := transcript.targets ++ [target] }
  return prob.collection.eval prob.target pkSeed target.1 target.2

/-- Implementation of the collection oracle, recording tweaks so challenge/collection separation
can be checked after target placement. -/
def collectionImpl (prob : CollectionProblem PkSeed Tweak Digest) (pkSeed : PkSeed) :
    QueryImpl prob.collection.oracleSpec (StateT (Transcript prob) ProbComp) := fun query => do
  modify fun transcript =>
    { transcript with collectionTweaks := transcript.collectionTweaks ++ [query.tweak] }
  return prob.collection.eval query.index pkSeed query.tweak query.message

/-- Combined target-placement interpreter for SM-DT-TCR-C. -/
def tcrCPickImpl (prob : CollectionProblem PkSeed Tweak Digest) (pkSeed : PkSeed) :
    QueryImpl prob.tcrPickSpec (StateT (Transcript prob) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Transcript prob) ProbComp) +
    (tcrCChallengeImpl prob pkSeed + collectionImpl prob pkSeed)

/-- The SM-DT-TCR-C experiment. -/
def tcrCExperiment {prob : CollectionProblem PkSeed Tweak Digest}
    [SampleableType PkSeed] [DecidableEq Tweak] [DecidableEq prob.Message] [DecidableEq Digest]
    (adv : TcrCAdversary prob) : ProbComp Bool := do
  let pkSeed ← $ᵗ PkSeed
  let (state, transcript) ←
    (simulateQ (tcrCPickImpl prob pkSeed) adv.pick).run (Transcript.empty prob)
  let (i, message') ← adv.find state pkSeed
  match transcript.targets[i]? with
  | none => return false
  | some (tweak, message) =>
      return decide (transcript.Valid ∧ message' ≠ message ∧
        prob.collection.eval prob.target pkSeed tweak message' =
          prob.collection.eval prob.target pkSeed tweak message)

/-- SM-DT-TCR-C success probability. -/
noncomputable def tcrCAdvantage {prob : CollectionProblem PkSeed Tweak Digest}
    [SampleableType PkSeed] [DecidableEq Tweak] [DecidableEq prob.Message] [DecidableEq Digest]
    (adv : TcrCAdversary prob) : ℝ≥0∞ :=
  Pr[= true | tcrCExperiment adv]

/-! ## SM-DT-PRE-C -/

/-- A two-stage SM-DT-PRE-C adversary.  Each challenge query supplies a tweak; the challenger
samples and hides a fresh target preimage and returns its digest. -/
structure PreimageCAdversary (prob : CollectionProblem PkSeed Tweak Digest) where
  /-- Private state carried from target placement to inversion. -/
  State : Type
  /-- Target-placement computation under the hidden public seed. -/
  pick : OracleComp prob.preimagePickSpec State
  /-- Inversion phase after the public seed is revealed. -/
  find : State → PkSeed → ProbComp (ℕ × prob.Message)

/-- Implementation of the PRE challenge oracle.  The sampled preimage is retained only in the
challenger-owned transcript; the adversary receives its hash. -/
def preimageCChallengeImpl (prob : CollectionProblem PkSeed Tweak Digest)
    [SampleableType prob.Message]
    (pkSeed : PkSeed) :
    QueryImpl prob.preimageChallengeSpec (StateT (Transcript prob) ProbComp) := fun tweak => do
  let message ← $ᵗ prob.Message
  modify fun transcript => { transcript with targets := transcript.targets ++ [(tweak, message)] }
  return prob.collection.eval prob.target pkSeed tweak message

/-- Combined target-placement interpreter for SM-DT-PRE-C. -/
def preimageCPickImpl (prob : CollectionProblem PkSeed Tweak Digest)
    [SampleableType prob.Message]
    (pkSeed : PkSeed) :
    QueryImpl prob.preimagePickSpec (StateT (Transcript prob) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Transcript prob) ProbComp) +
    (preimageCChallengeImpl prob pkSeed + collectionImpl prob pkSeed)

/-- The SM-DT-PRE-C experiment. -/
def preimageCExperiment {prob : CollectionProblem PkSeed Tweak Digest}
    [SampleableType PkSeed] [SampleableType prob.Message]
    [DecidableEq Tweak] [DecidableEq Digest]
    (adv : PreimageCAdversary prob) : ProbComp Bool := do
  let pkSeed ← $ᵗ PkSeed
  let (state, transcript) ←
    (simulateQ (preimageCPickImpl prob pkSeed) adv.pick).run (Transcript.empty prob)
  let (i, message') ← adv.find state pkSeed
  match transcript.targets[i]? with
  | none => return false
  | some (tweak, message) =>
      return decide (transcript.Valid ∧
        prob.collection.eval prob.target pkSeed tweak message' =
          prob.collection.eval prob.target pkSeed tweak message)

/-- SM-DT-PRE-C success probability. -/
noncomputable def preimageCAdvantage {prob : CollectionProblem PkSeed Tweak Digest}
    [SampleableType PkSeed] [SampleableType prob.Message]
    [DecidableEq Tweak] [DecidableEq Digest]
    (adv : PreimageCAdversary prob) : ℝ≥0∞ :=
  Pr[= true | preimageCExperiment adv]

end MultiTarget
