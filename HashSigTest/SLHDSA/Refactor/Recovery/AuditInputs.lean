/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment

/-!
# Total-interface unforgeability observers

Both observers evaluate the one counted experiment and its unconditional final verification.
Ordinary EUF checks message membership; strong EUF checks exact returned-pair membership.
These contract types assert no equivalence theorem or optional-service EUF convention.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace P5Continuation.F4

open scoped Classical in
/-- Ordinary message freshness observes a total reply carrier after final verification. -/
@[expose] noncomputable def totalEufProgram {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {Request PK SK Sig C : Type} [AddMonoid C] (policy : SigningView.Event spec Request → C)
    (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
    (adversary : UnforgeableAdversary alg) : OracleComp spec Bool :=
  (fun observed => !observed.rawLog.wasQueried observed.forgery.1 && observed.verified) <$>
    SigningView.countedExperiment policy (SigningView.ofTotal alg) adversary.main

/-- The original runtime evaluates only the ordinary observer of the shared program. -/
@[expose] noncomputable def totalEufAdvantage {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {Request PK SK Sig C : Type} [AddMonoid C] (policy : SigningView.Event spec Request → C)
    (runtime : ProbCompRuntime.{0, 0} (OracleComp spec))
    (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
    (adversary : UnforgeableAdversary alg) : ℝ≥0∞ :=
  runtime.evalDist (totalEufProgram policy alg adversary) {true}

open scoped Classical in
/-- Strong pair freshness observes the same total experiment and raw reply carrier. -/
@[expose] noncomputable def totalSufProgram {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {Request PK SK Sig C : Type} [AddMonoid C] (policy : SigningView.Event spec Request → C)
    (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
    (adversary : StrongUnforgeableAdversary alg) : OracleComp spec Bool :=
  (fun observed => decide (SigningView.Wins (SigningView.ofTotal alg).readback
    (SigningView.erase observed))) <$>
      SigningView.countedExperiment policy (SigningView.ofTotal alg) adversary.main

/-- The original runtime evaluates the strong observer without changing any budget. -/
@[expose] noncomputable def totalSufAdvantage {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {Request PK SK Sig C : Type} [AddMonoid C] (policy : SigningView.Event spec Request → C)
    (runtime : ProbCompRuntime.{0, 0} (OracleComp spec))
    (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
    (adversary : StrongUnforgeableAdversary alg) : ℝ≥0∞ :=
  runtime.evalDist (totalSufProgram policy alg adversary) {true}

/-- Exact ordinary free-program recovery; no probability or budget premise is introduced. -/
def TotalEufProgramContract : Prop :=
  ∀ {ι : Type} {spec : OracleSpec.{0, 0} ι} {Request PK SK Sig C : Type} [AddMonoid C]
    (policy : SigningView.Event spec Request → C)
    (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
    (adversary : UnforgeableAdversary alg),
    totalEufProgram policy alg adversary = unforgeableExperiment adversary

/-- Exact ordinary-advantage recovery under the same arbitrary original runtime. -/
def TotalEufAdvantageContract : Prop :=
  ∀ {ι : Type} {spec : OracleSpec.{0, 0} ι} {Request PK SK Sig C : Type} [AddMonoid C]
    (policy : SigningView.Event spec Request → C)
    (runtime : ProbCompRuntime.{0, 0} (OracleComp spec))
    (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
    (adversary : UnforgeableAdversary alg),
    totalEufAdvantage policy runtime alg adversary = unforgeableAdvantage runtime adversary

/-- Exact strong free-program recovery, with pair freshness distinct from message freshness. -/
def TotalSufProgramContract : Prop :=
  ∀ {ι : Type} {spec : OracleSpec.{0, 0} ι} {Request PK SK Sig C : Type} [AddMonoid C]
    (policy : SigningView.Event spec Request → C)
    (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
    (adversary : StrongUnforgeableAdversary alg),
    totalSufProgram policy alg adversary = strongUnforgeableExperiment adversary

/-- Exact strong-advantage recovery under the same runtime and arbitrary declared policy. -/
def TotalSufAdvantageContract : Prop :=
  ∀ {ι : Type} {spec : OracleSpec.{0, 0} ι} {Request PK SK Sig C : Type} [AddMonoid C]
    (policy : SigningView.Event spec Request → C)
    (runtime : ProbCompRuntime.{0, 0} (OracleComp spec))
    (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
    (adversary : StrongUnforgeableAdversary alg),
    totalSufAdvantage policy runtime alg adversary = strongUnforgeableAdvantage runtime adversary

end P5Continuation.F4
