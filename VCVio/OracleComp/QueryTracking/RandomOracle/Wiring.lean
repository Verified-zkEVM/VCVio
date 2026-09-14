/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.SimSemantics.Wiring
public import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-!
# Cached and eager random oracles behind recursive wiring

Any finite recursive polynomial wiring exposing a single random-oracle service has the same
output measure under lazy caching and eager full-table sampling. The cache can be initialized
arbitrarily. Several ports referring to the external input share one cache and one eager table.
The equality averages over that initial table law, including its hidden randomness.
-/

public section

open OracleComp OracleSpec PFunctor

namespace OracleComp

variable {D R Boxes : Type} [DecidableEq D] [Finite D] [Finite R] [Nonempty R]
  [SampleableType R] [SampleableType (D → R)]
  {Arity : Boxes → Type} {Dom : (b : Boxes) → Arity b → PFunctor}
  {Cod : Boxes → PFunctor}

/-- Cached/eager equivalence is preserved by recursive polynomial wiring with a shared service.
The result may be any measurable observation returned by the wired handler. -/
theorem evalDist_randomOracle_wiring_eq_tableExtending
    (implementation : (b : Boxes) → (a : (Cod b).A) →
      FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    {output : PFunctor}
    (wiring : Wiring Boxes Arity Dom Cod Unit (fun _ => (D →ₒ R).toPFunctor) output)
    (a : output.A) [MeasurableSpace (output.B a)] (cache : (D →ₒ R).QueryCache) :
    𝒟[(simulateQ randomOracle (wiring.oracleProgram implementation a)).run' cache] =
      𝒟[do
        let table ← $ᵗ (D → R)
        pure (evalWithAnswerFn (QueryImpl.ofFn (tableExtending cache table))
          (wiring.oracleProgram implementation a))] :=
  evalDist_simulateQ_randomOracle_run'_eq_tableExtending _ cache

end OracleComp
