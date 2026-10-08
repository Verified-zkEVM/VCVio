/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.CoverageRoles
public import VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape.HitPotential
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Hits of fresh randomizer draws in the role-tagged SLH-DSA experiment

The role-tagged experiment `roleExperiment core adv pkSeed` runs over the duplicated joint
interface, and `AnswerTape.classPosImplFwd` runs it on a family of class-indexed tapes with the
position of every `H_msg` answer recorded. Beside it, `AnswerTape.freshHitAux` records a hit set:
`randRel core` makes a fresh randomizer draw `u` at `(addrnd, M)` hit every `H_msg` point cached
before it whose randomizer is `u` and whose message is `M`, whatever its public key.

`prEvent_roleExperiment_hitAll_le` instantiates `AnswerTape.prEvent_hitAll_le` at that run. With
the tape of class `other` empty, so that every randomizer derivation is drawn fresh and uniformly,
and a forger making at most `qs` signing queries, the probability that every position of a set
`P` of positions on the forger's `H_msg` tape ends up holding a hit point, with no draw hitting
two of them, is at most `(qs / |Y|) ^ P.card`. The two scheme-specific inputs are that a uniform
randomizer satisfies `randRel` at a given point with probability at most `1 / |Y|`
(`prEvent_randRel_le`), and that the role experiment makes at most `qs` randomizer derivations
(`isQueryBoundP_roleExperiment_rand`).

## Scope

* The statement is per public seed `pkSeed` and per tape family `L`.
* The designated positions are given as a set of naturals on the tape of class `forger`; the
  coverers of a target digest are one such set.
-/

public section

open OracleComp OracleSpec SignatureAlg AnswerTape
open scoped ENNReal

namespace SLHDSA.Security.Coverage

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-- A fresh randomizer draw `u` at `(addrnd, M)` hits the `H_msg` points with randomizer `u` and
message `M`, at any public key. -/
@[expose] def randRel : (x : (jointSpec core).Domain) → (jointSpec core).Range x →
    (jointSpec core).Domain → Prop
  | .inr (.inr (_, M)), u, .inl (.inl (.hmsg R _ _ M')) => R = u ∧ M' = M
  | _, _, _ => False

/-- A uniform answer at a point satisfies `randRel` at a given point with probability at most
`1 / |Y|`: only the randomizer of that point qualifies. -/
theorem prEvent_randRel_le [SampleableType core.Y] (x t : (jointSpec core).Domain) :
    Pr{let u ← ($ᵗ (jointSpec core).Range x : ProbComp _)}[randRel core x u t] ≤
      (Nat.card core.Y : ℝ≥0∞)⁻¹ := by
  have h0 : ∀ y : (jointSpec core).Domain, (∀ u, ¬ randRel core y u t) →
      Pr{let u ← ($ᵗ (jointSpec core).Range y : ProbComp _)}[randRel core y u t] ≤
        (Nat.card core.Y : ℝ≥0∞)⁻¹ := fun y hy =>
    (prEvent_eq_zero_of_forall_not _ _ hy).trans_le zero_le
  rcases x with ((x | x) | (k | ⟨a, M⟩))
  iterate 3 exact h0 _ fun _ h => h
  rcases t with ((⟨s, r, xs⟩ | ⟨R, s, r, M'⟩) | t) | t
  · exact h0 _ fun _ h => h
  · exact (prEvent_mono _ _ _ fun u h => h.1.symm).trans
      (SampleableType.prEvent_uniformSample_eq_singleton_natCard R).le
  all_goals exact h0 _ fun _ h => h

variable [SampleableType core.Y] [DecidableEq core.Y] [SampleableType core.SkSeed]
  [SampleableType core.SkPrf] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]
  [DecidableEq core.SkPrf]

/-- **Hitting every designated forger-tape position.** On the instrumented run of the role
experiment over a tape family whose tape of class `other` is empty, every position of `P` on the
forger's `H_msg` tape holds a point hit by a fresh randomizer draw, with no draw hitting two of
them, with probability at most `(qs / |Y|) ^ P.card`. -/
theorem prEvent_roleExperiment_hitAll_le {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    {adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) (pkSeed : core.PkSeed)
    (L : (j : TapeClass) → List (tapeClassRange core j)) (hL : L .other = [])
    (P : Finset ℕ) :
    Pr{let z ← (simulateQ (classPosImplFwd (tapeClassRange core) (tapeClass core)
        (range_eq_tapeClassRange core) (freshHitAux (IsRandPoint core) (randRel core)))
        (roleExperiment core adv pkSeed)).run ((∅, L), (ClassPos.init, ∅))}[
        HitAll (randRel core) TapeClass.forger P z.2] ≤
      ((qs : ℝ≥0∞) / Nat.card core.Y) ^ P.card := by
  rw [div_eq_mul_inv]
  refine prEvent_hitAll_le (IsRandPoint core) (randRel core) (tapeClass core)
    (range_eq_tapeClassRange core) L TapeClass.forger P _ ?_
    (fun x _ t => prEvent_randRel_le core x t) (IsRoleRandQuery core) (fun x hx => ⟨hx, hx⟩) _ qs
    (isQueryBoundP_roleExperiment_rand core hadv pkSeed)
  rintro ((t | t) | (k | x)) hx <;> first | exact hx.elim | exact ⟨hL, hL⟩

end SLHDSA.Security.Coverage
