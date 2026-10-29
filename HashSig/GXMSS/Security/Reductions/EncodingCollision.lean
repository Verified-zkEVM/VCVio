/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.CollisionReductions
import all HashSig.GXMSS.Security.Reductions.SourceGames
import all HashSig.GXMSS.Security.Reductions.CollisionReductions

/-!
# Successful encoding target-collision bound

Returned Game 1 wins lost at Game 2 are bounded by the encoding target-collision reduction.
The signing-query bound counts repeated and failed calls and preserves missing mass.
-/

public section

namespace GXMSS.Reductions

open Encoding ENNReal OracleComp OracleSpec TweakableHash

variable {PP T X H M R : Type} {h w v : ℕ}

/-- Native winning mass of the successful-record Game 1 to Game 2 difference is bounded by
the exact authoritative target-collision experiment. The unused and failed-consumed cases
contribute no mass to this event; any unreturned mass remains unconditioned. -/
theorem successfulEncodingDifferenceMass_le_encodingTargetCollisionAdvantage
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (hbound : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    successfulEncodingDifferenceMass hash enc K adv ≤
      TargetCollisionResistance.advantage
        (encodingTargetCollisionReduction hash enc qs K adv) := by
  have hprogram :
      (successfulEncodingDifference hash enc K <$> sourceProgram hash enc K adv) =
        (fun z => successfulEncodingDifference hash enc K z.1) <$>
          encodingSourceCoupledProgram hash enc K adv := by
    rw [← encodingSourceCoupledProgram_proj hash enc K adv]
    simp only [Functor.map_map]
  unfold successfulEncodingDifferenceMass TargetCollisionResistance.advantage
    TargetCollisionResistance.outputMeasure
  rw [hprogram, encodingTargetExperiment_eq_coupled hash enc qs K adv hbound]
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply OracleComp.evalDist_bind_apply_mono_of_support
    (encodingSourceCoupledProgram hash enc K adv)
    (fun z => pure (successfulEncodingDifference hash enc K z.1))
    (encodingTargetTail hash enc qs K) (measurableSet_singleton true)
  intro out hout
  by_cases hdiff : successfulEncodingDifference hash enc K out.1 = true
  · obtain ⟨hseed, hrecords⟩ :=
      encodingSourceCoupledProgram_support hash enc K adv out hout
    rw [encodingTargetTail_successfulDifference hash enc qs K out hseed hrecords hdiff]
    simp [hdiff]
  · have hfalse : successfulEncodingDifference hash enc K out.1 = false := by
      cases h : successfulEncodingDifference hash enc K out.1 <;> simp_all
    simp [hfalse]

end GXMSS.Reductions

namespace GXMSS.Unforgeability

open Encoding ENNReal OracleComp OracleSpec TweakableHash

variable {PP T X H M R : Type} {h w v : ℕ}

/-- The successful-record Game 1 to Game 2 hop using the fixed target-collision reduction.
The pathwise signing bound counts repeated and failed queries. The inequality compares returned
native mass without conditioning on termination or on successful retries. -/
@[expose]
def SuccessfulEncodingTargetCollisionBound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K : ℕ)
    (adv : Reductions.SchemeAdversary PP H M R h v) : Prop :=
  (∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) →
    Reductions.gameOneAdvantage hash enc K adv ≤
      Reductions.gameTwoAdvantage hash enc K adv +
        Encoding.TargetCollisionResistance.advantage
          (Reductions.encodingTargetCollisionReduction hash enc qs K adv)

/-- Returned Game 1 wins lost at Game 2 are charged to the successful recorded encoding target
in the authoritative collision game. -/
theorem successful_encoding_target_collision_bound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K : ℕ)
    (adv : Reductions.SchemeAdversary PP H M R h v) :
    SuccessfulEncodingTargetCollisionBound hash enc qs K adv := by
  intro hbound
  exact (Reductions.gameOneAdvantage_le_gameTwo_add_successfulDifference
    hash enc K adv).trans (add_le_add_right
      (Reductions.successfulEncodingDifferenceMass_le_encodingTargetCollisionAdvantage
        hash enc qs K adv hbound) _)

end GXMSS.Unforgeability
