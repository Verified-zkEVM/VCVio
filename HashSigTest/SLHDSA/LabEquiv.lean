/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.LabEquiv.Experiment
public import HashSig.SLHDSA.Security.KeyDiscipline
public import HashSigTest.SLHDSA.Bundles

/-!
# The lab experiment in the eager game at the shipped bundles

At every SHAKE bundle whose address fields fit, the bundle satisfies the key discipline, so in the
eager game of its canonical graph, from the empty state, the lifted transcript experiment of the
secret-free scheme and the lab experiment have the same output-and-state measure under the
discrete measurable structure, and every event on the output and the final state has the same
probability under both.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.LabEquivTest

open Security BundleTest

/-- At every SHAKE bundle whose address fields fit, the lifted experiment and the lab experiment
have the same measure from the empty state, under the discrete measurable structure. -/
example (vp : ValidatedParams) (hb : CanonicalAddressBounds vp.params)
    (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed)
    (adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand (pure pkSeed))) :
    (letI : MeasurableSpace (DeriveOutcome (shakeCore vp) × LabState (shakeCore vp)) := ⊤
     𝒟[(simulateQ (slhGraph (shakeCore vp) pkSeed).eagerImpl
        (liftComp (unforgeableTranscriptExperiment (deriveAdversary (shakeCore vp) adv pkSeed))
          (labSpec (shakeCore vp)))).run (∅, ∅)] =
      𝒟[(simulateQ (slhGraph (shakeCore vp) pkSeed).eagerImpl
          (labExperiment (shakeCore vp) adv pkSeed)).run (∅, ∅)]) :=
  letI : MeasurableSpace (DeriveOutcome (shakeCore vp) × LabState (shakeCore vp)) := ⊤
  evalDist_eagerImpl_liftComp_eq_labExperiment _ (Concrete.keyDiscipline_shakePrimitives vp hb)
    pkSeed adv (∅, ∅)

/-- At every SHAKE bundle whose address fields fit, every event on the output and the final state
has the same probability under the lifted experiment and the lab experiment from the empty
state. -/
example (vp : ValidatedParams) (hb : CanonicalAddressBounds vp.params)
    (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed)
    (adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand (pure pkSeed)))
    (P : DeriveOutcome (shakeCore vp) × LabState (shakeCore vp) → Prop) :
    Pr{let z ← (simulateQ (slhGraph (shakeCore vp) pkSeed).eagerImpl
        (liftComp (unforgeableTranscriptExperiment (deriveAdversary (shakeCore vp) adv pkSeed))
          (labSpec (shakeCore vp)))).run (∅, ∅)}[P z] =
      Pr{let z ← (simulateQ (slhGraph (shakeCore vp) pkSeed).eagerImpl
          (labExperiment (shakeCore vp) adv pkSeed)).run (∅, ∅)}[P z] :=
  prEvent_eagerImpl_liftComp_eq_labExperiment _ (Concrete.keyDiscipline_shakePrimitives vp hb)
    pkSeed adv (∅, ∅) P

end SLHDSA.LabEquivTest
