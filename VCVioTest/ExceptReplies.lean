/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module
public import VCVio.OracleComp.SimSemantics.ExceptT.Basic
public import VCVio.OracleComp.QueryTracking.Structures
public import VCVio.OracleComp.ProbComp.Basic
import Mathlib.Tactic.NormNum

/-!
# Total exceptional replies retain prefix effects

The first request charges three and the second charges five before returning an error.
Both requests change a cache and a decimal trace, including the error-producing request.
The stopped tail would charge 101 and write a third cache entry.
A separate optional reply returns `ok none`, which allows the next request to run.
-/

public section

open OracleComp OracleSpec OracleComp.ExceptReplies

namespace ExceptRepliesTest

/-- The three request inputs have unit successful replies. -/
abbrev spec : OracleSpec (Fin 3) := Fin 3 →ₒ Unit

/-- A concrete cache records which requests the backend has processed. -/
abbrev Cache := QueryCache spec

/-- Charges distinguish the two-request prefix from its stopped tail. -/
@[expose] def charge (q : Fin 3) : ℕ :=
  match q.val with
  | 0 => 3
  | 1 => 5
  | _ => 101

/-- Both successful and exceptional calls append their input to the trace and cache. -/
@[expose] def nextState (q : Fin 3) (s : ℕ × Cache) : ℕ × Cache :=
  (10 * s.1 + q.val + 1, s.2.cacheQuery q ())

/-- The second request errors after recording its own cost and state changes. -/
@[expose] def request :
    QueryImpl spec (ExceptT Unit (AddWriterT ℕ (StateT (ℕ × Cache) ProbComp))) :=
  fun q => ExceptT.mk <| WriterT.mk <| StateT.mk fun s =>
    pure ((if q = 1 then .error () else .ok (), Multiplicative.ofAdd (charge q)), nextState q s)

/-- The source client contains a third request after the error-producing second request. -/
@[expose] def client : OracleComp spec Unit := do
  let _ ← liftM (spec.query 0)
  let _ ← liftM (spec.query 1)
  let _ ← liftM (spec.query 2)
  pure ()

/-- Prefix cost is `3 + 5`, the trace is `7 -> 71 -> 712`, and both cache entries remain. -/
theorem prefix_joint :
    (simulateQ (spec := spec.exceptReplies Unit) (fun q => (request q).run)
      (compile Unit client)).runAdd.run (7, ∅) =
      pure ((Except.error (), 8), (712, ((∅ : Cache).cacheQuery 0 ()).cacheQuery 1 ())) := by
  rw [runAdd_run_simulateQ_compile]
  norm_num [client, simulateQ_bind, simulateQ_spec_query, ExceptT.run_bind,
    request, AddWriterT.runAdd, WriterT.run_bind, StateT.run_bind, StateT.run_map,
    bind_map_left, map_bind, bind_assoc, Prod.map, nextState, charge, OracleQuery.input_query]
  rfl

/-- The stopped tail leaves its cache entry absent despite its presence in the source client. -/
theorem stopped_cache_entry :
    (fun z => z.2.2 2) <$>
      (simulateQ (spec := spec.exceptReplies Unit) (fun q => (request q).run)
        (compile Unit client)).runAdd.run (7, ∅) = pure none := by
  rw [prefix_joint]
  simp

/-- A normal optional reply can be absent without being an outer exception. -/
@[expose] def optionalRequest :
    QueryImpl (Bool →ₒ Option Bool) (ExceptT Unit (StateT ℕ ProbComp)) :=
  fun q => ExceptT.mk <| StateT.mk fun used =>
    pure (.ok (if q then some false else none), used + 1)

/-- An absent first reply causes the client to ask its second request. -/
@[expose] def optionalClient : OracleComp (Bool →ₒ Option Bool) (Option Bool) := do
  let first ← liftM ((Bool →ₒ Option Bool).query false)
  if first.isNone then liftM ((Bool →ₒ Option Bool).query true) else pure first

/-- `ok none` continues to a second normal reply and increments the state twice. -/
theorem ok_none_continues :
    (simulateQ (spec := (Bool →ₒ Option Bool).exceptReplies Unit)
      (fun q => (optionalRequest q).run) (compile Unit optionalClient)).run 0 =
      pure (Except.ok (some false), 2) := by
  rw [simulateQ_compile]
  simp [optionalClient, simulateQ_bind, ExceptT.run_bind,
    optionalRequest, StateT.run_bind]

end ExceptRepliesTest
