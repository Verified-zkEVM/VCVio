/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Wiring

/-!
# Adaptive and repeated calls to a shared wired random oracle

Two input ports of one box refer to the same random-oracle service. The box queries its input,
uses that answer as its next query on the other port, then repeats its original input. The lazy
cache and eager table laws agree, including any preloaded cache. In particular the first and
third answers are the same table cell, rather than independent samples on separate wires.
-/

public section

open OracleComp OracleSpec PFunctor

namespace Examples.RandomOracleWiring

-- The sigma constructor's fibres are used explicitly by the concrete box implementation.
attribute [local implicit_reducible] PFunctor.sigma

/-- The shared Boolean random-oracle interface. -/
abbrev spec : OracleSpec Bool := Bool →ₒ Bool

/-- A box returns its initial, adaptive, and repeated responses. -/
abbrev output : PFunctor := ⟨Bool, fun _ => Bool × Bool × Bool⟩

/-- Two ports share the same external service. -/
@[expose] def network :
    Wiring Unit (fun _ => Bool) (fun _ _ => spec.toPFunctor) (fun _ => output)
      Unit (fun _ => spec.toPFunctor) output := .box () (fun _ => .input ())

/-- An adaptive query between two requests for the same cell. -/
@[expose] def implementation (_ : Unit) (input : Bool) :
    FreeM (PFunctor.sigma fun _ : Bool => spec.toPFunctor) (Bool × Bool × Bool) := do
  let first ← FreeM.lift (P := PFunctor.sigma fun _ : Bool => spec.toPFunctor) ⟨true, input⟩
  let adaptive ← FreeM.lift (P := PFunctor.sigma fun _ : Bool => spec.toPFunctor) ⟨false, first⟩
  let repeated ← FreeM.lift (P := PFunctor.sigma fun _ : Bool => spec.toPFunctor) ⟨true, input⟩
  pure (first, adaptive, repeated)

/-- The compiled program uses one shared interface at all three calls. -/
theorem oracleProgram_eq (input : Bool) :
    network.oracleProgram implementation input = (do
      let first ← (query (spec := spec) input : OracleComp spec Bool)
      let adaptive ← (query (spec := spec) first : OracleComp spec Bool)
      let repeated ← (query (spec := spec) input : OracleComp spec Bool)
      pure (first, adaptive, repeated)) := by
  rfl

/-- A deterministic table sends the repeated query back to its original cell. -/
theorem evalWithAnswerFn_eq (input : Bool) (table : Bool → Bool) :
    evalWithAnswerFn (QueryImpl.ofFn table) (network.oracleProgram implementation input) =
      (table input, table (table input), table input) := by
  rw [oracleProgram_eq]
  rfl

/-- The complete lazy-cache law agrees with a single eager table shared by both ports.
The explicit table draw retains hidden randomness under its initial law. -/
theorem evalDist_cached_eq (input : Bool) (cache : spec.QueryCache) :
    𝒟[(simulateQ randomOracle (network.oracleProgram implementation input)).run' cache] =
      𝒟[(fun table : Bool → Bool =>
        let answer := tableExtending cache table
        (answer input, answer (answer input), answer input)) <$> ($ᵗ (Bool → Bool))] := by
  rw [evalDist_randomOracle_wiring_eq_tableExtending implementation network input cache]
  simp only [bind_pure_comp]
  rfl

end Examples.RandomOracleWiring
