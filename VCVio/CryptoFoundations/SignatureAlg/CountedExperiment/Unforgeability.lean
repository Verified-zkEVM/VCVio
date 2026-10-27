/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment

/-!
# Unforgeability observations of counted total signatures

Message freshness and returned-pair freshness observe the same counted experiment and its
unconditional final verification. Each observation recovers the original total-signature
experiment under every declared additive policy and the same independently quantified runtime.
-/

public section

open OracleComp OracleSpec

universe i r

namespace SignatureAlg.SigningView

open scoped Classical in
/-- The message-freshness observation recovers the original ordinary experiment. -/
theorem ofTotal_countedUnforgeableProgram :
    ∀ {ι : Type i} {spec : OracleSpec.{i, 0} ι}
      {Request PK SK Sig C : Type} [AddMonoid C]
      (policy : Event spec Request → C)
      (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
      (adv : SignatureAlg.UnforgeableAdversary alg),
      (fun observed => !observed.rawLog.wasQueried observed.forgery.1 && observed.verified) <$>
          countedExperiment policy (ofTotal alg) adv.main =
        SignatureAlg.unforgeableExperiment adv := by
  intro ι spec Request PK SK Sig C _ policy alg adv
  calc
    _ = (fun outcome : Outcome Request Sig Sig =>
        !outcome.rawLog.wasQueried outcome.forgery.1 && outcome.verified) <$>
          (erase <$> countedExperiment policy (ofTotal alg) adv.main) := by
      rw [Functor.map_map]
      rfl
    _ = _ := by
      rw [countedExperiment_erases]
      simp only [experiment, map_bind, map_pure,
        ofTotal_runWithSigningOracle, SignatureAlg.unforgeableExperiment]
      rfl

open scoped Classical in
/-- The same runtime preserves the ordinary success probability of the counted observation. -/
theorem ofTotal_countedUnforgeableAdvantage :
    ∀ {ι : Type i} {spec : OracleSpec.{i, 0} ι}
      {Request PK SK Sig C : Type} [AddMonoid C]
      (policy : Event spec Request → C)
      (runtime : ProbCompRuntime.{i, r} (OracleComp spec))
      (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
      (adv : SignatureAlg.UnforgeableAdversary alg),
      runtime.evalDist
          ((fun observed => !observed.rawLog.wasQueried observed.forgery.1 && observed.verified) <$>
            countedExperiment policy (ofTotal alg) adv.main) {true} =
        SignatureAlg.unforgeableAdvantage runtime adv := by
  intro ι spec Request PK SK Sig C _ policy runtime alg adv
  change runtime.evalDist _ {true} =
    runtime.evalDist (SignatureAlg.unforgeableExperiment adv) {true}
  rw [ofTotal_countedUnforgeableProgram]

open scoped Classical in
/-- The same runtime preserves strong success probability through the existing winning program. -/
theorem ofTotal_countedStrongUnforgeableAdvantage :
    ∀ {ι : Type i} {spec : OracleSpec.{i, 0} ι}
      {Request PK SK Sig C : Type} [AddMonoid C]
      (policy : Event spec Request → C)
      (runtime : ProbCompRuntime.{i, r} (OracleComp spec))
      (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
      (adv : SignatureAlg.StrongUnforgeableAdversary alg),
      runtime.evalDist
          ((fun observed => decide (Wins (ofTotal alg).readback (erase observed))) <$>
            countedExperiment policy (ofTotal alg) adv.main) {true} =
        SignatureAlg.strongUnforgeableAdvantage runtime adv := by
  intro ι spec Request PK SK Sig C _ policy runtime alg adv
  change runtime.evalDist _ {true} =
    runtime.evalDist (SignatureAlg.strongUnforgeableExperiment adv) {true}
  rw [ofTotal_countedWinningProgram]

end SignatureAlg.SigningView
