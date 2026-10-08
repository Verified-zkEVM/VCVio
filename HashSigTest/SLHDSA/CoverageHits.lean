/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.CoverageHits
public import HashSigTest.SLHDSA.Target

/-!
# Hits of fresh randomizer draws in the role-tagged SLH-DSA experiment, checked

* **The hit relation.** A randomizer draw `u` at `(addrnd, M)` hits the `H_msg` point with
  randomizer `u` and message `M` at any public key, and misses a point with another message, a
  tweakable-hash point and every point when the draw is not a randomizer derivation.
* **The bound at a concrete forger.** `replayForger` asks for one signature, so its role
  experiment hits every designated forger-tape position with probability at most
  `(1 / |Y|) ^ P.card`.
-/

public section

open OracleComp OracleSpec SignatureAlg AnswerTape
open scoped ENNReal

namespace SLHDSA.Security.CoverageHitsTest

open Coverage TargetTest

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-! ## The hit relation -/

example (a u : core.Y) (s : core.PkSeed) (root : core.Y) (msg : List Byte) :
    randRel core (.inr (.inr (a, msg))) u (.inl (.inl (.hmsg u s root msg))) :=
  ⟨rfl, rfl⟩

example (a u : core.Y) (s : core.PkSeed) (root : core.Y) (msg msg' : List Byte)
    (h : msg' ≠ msg) :
    ¬ randRel core (.inr (.inr (a, msg))) u (.inl (.inl (.hmsg u s root msg'))) :=
  fun hr => h hr.2

example (a u : core.Y) (msg : List Byte) (s : core.PkSeed) (k : core.AdrsKey)
    (xs : List core.Y) :
    ¬ randRel core (.inr (.inr (a, msg))) u (.inl (.inl (.thash s k xs))) :=
  id

example (k : PrfKey core) (u : core.Y) (t : (jointSpec core).Domain) :
    ¬ randRel core (.inr (.inl k)) u t :=
  id

/-! ## The bound at a concrete forger -/

variable [SampleableType core.Y] [DecidableEq core.Y] [SampleableType core.SkSeed]
  [SampleableType core.SkPrf] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]
  [DecidableEq core.SkPrf] (optRand : PublicKeyCore core → ProbComp core.Y)
  (pkSeed : core.PkSeed) (e : core.SkSeed ≃ core.Y) (pkSeedDist : ProbComp core.PkSeed)

/-- The replay forger asks for one signature, so a single randomizer draw is available to hit
the designated positions. -/
example (L : (j : TapeClass) → List (tapeClassRange core j)) (hL : L .other = [])
    (P : Finset ℕ) :
    Pr{let z ← (simulateQ (classPosImplFwd (tapeClassRange core) (tapeClass core)
        (range_eq_tapeClassRange core) (freshHitAux (IsRandPoint core) (randRel core)))
        (roleExperiment core (replayForger core e optRand pkSeedDist) pkSeed)).run
        ((∅, L), (ClassPos.init, ∅))}[HitAll (randRel core) TapeClass.forger P z.2] ≤
      ((1 : ℕ) / Nat.card core.Y : ℝ≥0∞) ^ P.card :=
  prEvent_roleExperiment_hitAll_le core (romQueryBound_replayForger core e optRand pkSeedDist)
    pkSeed L hL P

end SLHDSA.Security.CoverageHitsTest
