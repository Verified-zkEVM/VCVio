/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.SchemeGames

/-!
# Strong unforgeability and the same-message residual

VCVio partitions the strong-unforgeability advantage exactly,
`strongUnforgeableAdvantage = unforgeableAdvantage + sameMessageStrongUnforgeableAdvantage`
(`strongAdvantage_eq_advantage_add_sameMessage`), and `HashSig.SLHDSA.Security.SchemeGames` splits
the same-message residual against `generalAlg` into a fresh-randomizer half and a same-randomizer
half. This module states what that partition implies for bounds on the strong advantage.

## Main statements

* `strongAdvantage_le_add_sameMessage_iff`: for every `ε`,
  `strongUnforgeableAdvantage _ sadv ≤ ε + sameMessageStrongUnforgeableAdvantage _ sadv` holds
  exactly when `unforgeableAdvantage _ sadv.toUnforgeableAdversary ≤ ε`. The residual is a
  probability, so it is finite and cancels; a bound of this shape on the strong advantage says no
  more than the same bound on the existential advantage.
* `strongAdvantage_le_add_arms_iff`: the same equivalence with the residual written as the two arms
  of the instrumented same-message experiment, at every selector.
* `freshRandomizerHalf_le_strongAdvantage`, `sameRandomizerHalf_le_strongAdvantage`: each half of
  the residual is at most the strong advantage.
* `sameMessageAdvantage_eq_halves_of_unfoldings`: explicit defining equations of the two halves
  identify the residual with their sum.

## The same-randomizer half

The same-randomizer half has no counterpart in the EasyCrypt development of Barbosa et al. Its
message key `op mkg : mseed -> msg -> mkey` (`SPHINCS_PLUS.ec:409`) is a function of the master
seed and the message, and after the `MKG` hop the signing oracle memoizes on the message
(`SPHINCS_PLUS.ec:2082-2086`), so a transcript there carries one randomizer per message. Its game
also tests freshness on the message alone. FIPS 205 Algorithm 19 instead sets `opt_rand ← addrnd`
and §9.2 makes that hedged variant the default, and `SchemeGames.generalAlg` samples `addrnd` per
signature, so `SufResidual.loggedRandomizers` at one message can hold several values. Deterministic
signing (`opt_rand ← PK.seed`) narrows that list without emptying the same-randomizer case: a
second signature reusing a logged randomizer is still in it.

On the same-randomizer branch the two signatures split to one digest against one public key
(`SufResidual.schemeParts_eq_of_randomizer_eq`) and differ in the FORS half or in the hypertree half
(`SufResidual.components_ne_of_ne_of_randomizer_eq`). The `H_msg` route is unavailable there:
the forged pair is one of the embedded targets
(`SufResidual.mem_embedTargets_of_mem_loggedRandomizers`), so the `H_msg` winning condition fails
on its freshness conjunct
(`not_wins_of_mem_loggedRandomizers`). The fresh half reaches it through
`SchemeGames.freshRandomizer_notMem_embedTargets` and `freshRandomizer_wins_or_uncovered`. Neither
half is bounded in this module.

## References

- NIST FIPS 205, §9.2 and Algorithm 19 (the hedged and deterministic variants)
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified" (`SPHINCS_PLUS.ec`)
-/

public section

namespace SLHDSA.Security

open MeasureTheory OracleComp OracleSpec ENNReal SignatureAlg TweakableHash Security.CanonicalGames

universe u

/-! ## The same-message advantage is exactly the sum of the two arms -/

section Generic

variable {ι : Type u} {spec : OracleSpec ι} {M PK SK S : Type}

/-- The same-message advantage is a probability, so it is finite.  This is what makes the residual
cancel in `strongAdvantage_le_add_sameMessage_iff`: in `ℝ≥0∞` a summand may be added to both sides
of a `≤` and removed again only when it is not `⊤`.

*Experiment split.* -/
theorem sameMessageAdvantage_le_one {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : StrongUnforgeableAdversary sigAlg) :
    sameMessageStrongUnforgeableAdvantage runtime adv ≤ 1 :=
  MeasureTheory.measure_le_one _ _

end Generic

/-! ## The residual cancels

Each equivalence below says that an inequality with the residual added on the right is the *same
statement* as the existential inequality without it, so no bound on the strong advantage of this
form is stronger than the corresponding bound on the existential advantage. -/

section Cancel

variable {vp : ValidatedParams} {prims : Primitives vp.params}
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
  [SampleableType prims.Y] [DecidableEq prims.Y]

/-- **The residual carries no information.**  Bounding the strong advantage by anything *plus the
same-message advantage* is equivalent to bounding the existential advantage by that thing alone.

Forward and backward, so there is no reading on which the left-hand side is the weaker claim.  The
mechanism is VCVio's partition, which is an equality, together with the residual's finiteness: the
term added on the right is the term already inside the left.

*Experiment split.* -/
theorem strongAdvantage_le_add_sameMessage_iff
    (sadv : StrongUnforgeableAdversary (generalAlg prims)) (ε : ℝ≥0∞) :
    strongUnforgeableAdvantage ProbCompRuntime.probComp sadv ≤
        ε + sameMessageStrongUnforgeableAdvantage ProbCompRuntime.probComp sadv ↔
      unforgeableAdvantage ProbCompRuntime.probComp sadv.toUnforgeableAdversary ≤ ε := by
  rw [strongAdvantage_eq_advantage_add_sameMessage sadv]
  exact ENNReal.add_le_add_iff_right
    (ne_top_of_le_ne_top one_ne_top (sameMessageAdvantage_le_one _ sadv))

/-- **Instrumenting the residual recovers nothing either.**  At every selector the two arms sum to
the same-message advantage, so the equivalence above holds verbatim with the residual split in two.

So no instrumentation of the residual makes a bound of this shape say more; only a bound on one of
the halves themselves could.

*Experiment split.* -/
theorem strongAdvantage_le_add_arms_iff (sadv : StrongUnforgeableAdversary (generalAlg prims))
    (ε : ℝ≥0∞) (sel : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core) →
      List Byte → GeneralScheme.SignatureCore vp prims.core → Bool) :
    strongUnforgeableAdvantage ProbCompRuntime.probComp sadv ≤ ε +
        (𝒟[instrumentedSameMessageExperiment sadv sel]
          {x | x.1 = true ∧ x.2 = false} +
          𝒟[instrumentedSameMessageExperiment sadv sel]
            {x | x.1 = true ∧ x.2 = true}) ↔
      unforgeableAdvantage ProbCompRuntime.probComp sadv.toUnforgeableAdversary ≤ ε := by
  have h := sameMessageAdvantage_eq_arms ProbCompRuntime.probComp sadv sel
  rw [ProbCompRuntime.probComp_evalDist] at h
  rw [← h]
  exact strongAdvantage_le_add_sameMessage_iff sadv ε

/-- The fresh-randomizer half is at most the strong advantage it is a piece of.  Together with
`SchemeGames.freshRandomizerHalf_le_sameMessageAdvantage` and `freshRandomizerHalf_le_branch` this
pins it from above by the residual, by its branch and by the strong advantage.

*Experiment split.* -/
theorem freshRandomizerHalf_le_strongAdvantage
    (sadv : StrongUnforgeableAdversary (generalAlg prims)) :
    freshRandomizerHalf sadv ≤ strongUnforgeableAdvantage ProbCompRuntime.probComp sadv := by
  rw [strongAdvantage_eq_advantage_add_sameMessage sadv]
  exact le_add_left (freshRandomizerHalf_le_sameMessageAdvantage sadv)

/-- The same-randomizer half is at most the strong advantage it is a piece of.

*Experiment split.* -/
theorem sameRandomizerHalf_le_strongAdvantage
    (sadv : StrongUnforgeableAdversary (generalAlg prims)) :
    sameRandomizerHalf sadv ≤ strongUnforgeableAdvantage ProbCompRuntime.probComp sadv := by
  rw [strongAdvantage_eq_advantage_add_sameMessage sadv]
  exact le_add_left (sameRandomizerHalf_le_sameMessageAdvantage sadv)

end Cancel

/-! ## Exact randomizer partition

The named halves partition the same-message success event. The defining equations of the halves
also support proofs phrased explicitly through their event masses. -/

section Exactness

variable {vp : ValidatedParams} {prims : Primitives vp.params}
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
  [SampleableType prims.Y] [DecidableEq prims.Y]

/-- Explicit defining equations of the two halves transport the Boolean partition to their sum. -/
theorem sameMessageAdvantage_eq_halves_of_unfoldings
    (sadv : StrongUnforgeableAdversary (generalAlg prims))
    (hfresh : freshRandomizerHalf sadv =
      𝒟[instrumentedSameMessageExperiment sadv
          (randomizerLogged (prims := prims))] {x | x.1 = true ∧ x.2 = false})
    (hsame : sameRandomizerHalf sadv =
      𝒟[instrumentedSameMessageExperiment sadv
          (randomizerLogged (prims := prims))] {x | x.1 = true ∧ x.2 = true}) :
    sameMessageStrongUnforgeableAdvantage ProbCompRuntime.probComp sadv =
      freshRandomizerHalf sadv + sameRandomizerHalf sadv := by
  rw [hfresh, hsame]
  exact sameMessageAdvantage_eq_arms ProbCompRuntime.probComp
    sadv
    (randomizerLogged (prims := prims))

end Exactness

end SLHDSA.Security
