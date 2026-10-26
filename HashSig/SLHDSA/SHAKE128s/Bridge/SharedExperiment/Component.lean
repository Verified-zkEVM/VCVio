/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Defs
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

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
