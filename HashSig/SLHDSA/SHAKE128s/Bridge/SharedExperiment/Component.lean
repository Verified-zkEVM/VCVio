/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Defs
public import VCVio.OracleComp.QueryTracking.WriterCost.Compose
public import VCVio.OracleComp.QueryTracking.WriterCost.Map
import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Exact source counts of signature components

Each keygen, direct, signer or verification component contributes its actual old hash count
at its single source coordinate. Private samples contribute zero, and repeated hash calls
retain their full charge before an outer cache interprets the program.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment

/-- The shared component records exactly the original all-hash counter at its actual source. -/
theorem costed_eq_countAllHashes {Output α : Type} (phase : SigningView.Phase)
    (body : OracleComp (Game.World Output) α) :
    (SigningView.costed sourcePolicy phase body).runAdd =
      (fun result => (result.1, Pi.single (sourceKind phase) result.2)) <$>
        Game.countAllHashes body := by
  let singleton : Nat →+ SourceCounts :=
    AddMonoidHom.single (fun _ : Unforgeability.QueryKind => Nat) (sourceKind phase)
  have equality := QueryImpl.mapCostHom_simulateQ_withAddCost singleton
    (QueryImpl.id' (Game.World Output)) Game.hashCost body
  have observed := congrArg (fun computation => computation.runAdd) equality
  rw [AddWriterT.runAdd_mapCostHom] at observed
  simpa [singleton, SigningView.costed, sourcePolicy, Game.countAllHashes,
    addCostOracle, QueryImpl.ofLift_eq_id', AddWriterT.runAdd, Prod.map] using observed.symm

/-- Verification and outer hash observers retain the same actual hash count on every path. -/
theorem countAllHashes_countQueries_verification {Output α : Type}
    (body : OracleComp (Game.World Output) α) :
    Game.countAllHashes (Game.countQueries
      (fun input => Game.Counts.single .verification (Game.hashCost input)) body) =
      (fun result => ((result.1, Game.Counts.single .verification result.2), result.2)) <$>
        Game.countAllHashes body := by
  let both : Nat →+ (Game.Counts × Nat) :=
    (AddMonoidHom.single (fun _ : Game.QueryKind => Nat) .verification).prod
      (AddMonoidHom.id Nat)
  have composition := OracleComp.simulateQ_withAddCost_runAdd (Game.World Output)
    (fun input => Game.Counts.single .verification (Game.hashCost input)) Game.hashCost body
  have equality := QueryImpl.mapCostHom_simulateQ_withAddCost both
    (QueryImpl.id' (Game.World Output)) Game.hashCost body
  have observed := congrArg (fun computation => computation.runAdd) equality
  rw [AddWriterT.runAdd_mapCostHom] at observed
  change _ = (fun result => ((result.1, result.2.1), result.2.2)) <$>
    (simulateQ ((QueryImpl.id' (Game.World Output)).withAddCost
      (fun input => both (Game.hashCost input))) body).runAdd at composition
  rw [← observed] at composition
  simpa [both, Game.countAllHashes, Game.countQueries, addCostOracle,
    QueryImpl.ofLift_eq_id', AddWriterT.runAdd, Functor.map_map, Game.Counts.single,
    Prod.map] using composition

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
