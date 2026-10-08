/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.RomSchemeBridge
public import VCVio.EvalDist.ProbabilityBounds

/-!
# The union bound over the random-oracle bad events of SLH-DSA

The three events of `HashSig.SLHDSA.Security.RomDescentSecret`, read at a point of
`romSchemeRun` (an outcome and the final cache) at the run's own oracle-backed provider and
public seed, each conjoined with freshness of the forged message for the signing log:
`RunTargetCollision`, `RunHiddenHit` and `RunItsrCovered`.  They are exactly the disjuncts of
`bad_event_of_wins_romSchemeRun`, so the forging advantage against `romScheme` in the
random-oracle runtime is at most the sum of their probabilities under `romSchemeRun`
(`unforgeableAdvantage_romScheme_le_add`), and at most the probability of a target collision or a
hidden-value hit plus that of interleaved-target coverage
(`unforgeableAdvantage_romScheme_le_or_add`).  It is also at most the probability of the
disjunction (`unforgeableAdvantage_romScheme_le_prEvent_or`), to which a game hop can be applied
before the union is split.  At a point mass `pkSeedDist = pure pkSeed` the bounds are per public
seed, the shape of `SecurityTarget`.

## Scope

* No event probability is bounded here.
* No query budget appears.
* Nothing here is quantum: the bound is a classical random-oracle statement.

## Labels

*The events*: `RunFresh`, `RunTargetCollision`, `RunHiddenHit`, `RunItsrCovered`.

*The union bound*: `unforgeableAdvantage_romScheme_le_prEvent_or`,
`unforgeableAdvantage_romScheme_le_or_add`, `unforgeableAdvantage_romScheme_le_add`.
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec SignatureAlg

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-! ## The events -/

/-- The forged message of a run point is not the message of any logged signature. -/
@[expose] def RunFresh (z : RomOutcome vp core × (hashSpec core).QueryCache) : Prop :=
  z.1.msg ∉ z.1.log.map (fun e => e.1)

/-- A run point exhibits a same-address target collision at its own oracle-backed provider and
public seed, in the public-hash part of its cache, and its forged message is fresh. -/
@[expose] def RunTargetCollision (e : core.SkSeed ≃ core.Y)
    (z : RomOutcome vp core × (hashSpec core).QueryCache) : Prop :=
  TargetCollision (oracleSecret core e z.1.pk.pkSeed z.1.sk.skSeed) z.1.pk.pkSeed
    z.2.fst ∧ RunFresh core z

/-- A run point exhibits a hidden-value hit at its own oracle-backed provider, in the public-hash
part of its cache, and its forged message is fresh. -/
@[expose] def RunHiddenHit (e : core.SkSeed ≃ core.Y)
    (z : RomOutcome vp core × (hashSpec core).QueryCache) : Prop :=
  HiddenHit (oracleSecret core e z.1.pk.pkSeed z.1.sk.skSeed) z.1 z.2.fst ∧
    RunFresh core z

/-- A run point exhibits interleaved-target coverage in the public-hash part of its cache, and
its forged message is fresh. -/
@[expose] def RunItsrCovered (z : RomOutcome vp core × (hashSpec core).QueryCache) : Prop :=
  ItsrCovered z.1 z.2.fst ∧ RunFresh core z

/-! ## The union bound -/

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf] [DecidableEq core.Y]
  [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-- **The forging advantage is at most the probability of a bad event.**  The forging advantage
against `romScheme` in the random-oracle runtime is at most the probability that `romSchemeRun`
fires a target collision or a hidden-value hit, or interleaved-target coverage, each with a fresh
forged message. -/
theorem unforgeableAdvantage_romScheme_le_prEvent_or (laws : core.ByteLaws)
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeedDist : ProbComp core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec core)) adv ≤
      Pr{let z ← romSchemeRun core e optRand pkSeedDist adv}[
        (RunTargetCollision core e z ∨ RunHiddenHit core e z) ∨ RunItsrCovered core z] := by
  rw [unforgeableAdvantage_romScheme_eq]
  exact prEvent_mono_of_support _ _ _ fun z hz hw ↦ or_assoc.2
    (bad_event_of_wins_romSchemeRun laws e optRand pkSeedDist adv hz hw)

/-- **The union bound, with the first two events grouped.**  The forging advantage against
`romScheme` in the random-oracle runtime is at most the probability of a target collision or a
hidden-value hit, plus that of interleaved-target coverage, each with a fresh forged message, under
`romSchemeRun`. -/
theorem unforgeableAdvantage_romScheme_le_or_add (laws : core.ByteLaws)
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeedDist : ProbComp core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec core)) adv ≤
      Pr{let z ← romSchemeRun core e optRand pkSeedDist adv}[
        RunTargetCollision core e z ∨ RunHiddenHit core e z] +
      Pr{let z ← romSchemeRun core e optRand pkSeedDist adv}[RunItsrCovered core z] :=
  (unforgeableAdvantage_romScheme_le_prEvent_or core laws e optRand pkSeedDist adv).trans
    (prEvent_or_le _ _ _)

/-- **The union bound.**  The forging advantage against `romScheme` in the random-oracle runtime
is at most the probability of a target collision, plus that of a hidden-value hit, plus that of
interleaved-target coverage, each with a fresh forged message, under `romSchemeRun`. -/
theorem unforgeableAdvantage_romScheme_le_add (laws : core.ByteLaws) (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeedDist : ProbComp core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec core)) adv ≤
      Pr{let z ← romSchemeRun core e optRand pkSeedDist adv}[RunTargetCollision core e z] +
      Pr{let z ← romSchemeRun core e optRand pkSeedDist adv}[RunHiddenHit core e z] +
      Pr{let z ← romSchemeRun core e optRand pkSeedDist adv}[RunItsrCovered core z] := by
  calc _ ≤ _ := unforgeableAdvantage_romScheme_le_or_add core laws e optRand pkSeedDist adv
    _ ≤ _ := by
      gcongr
      exact prEvent_or_le _ _ _

end SLHDSA.Security
