/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.LoggingOracle.History

/-!
# Coherent logged-history controls

Saved primitive paths retain full replies even when the service returns only their low halves.
A stateful service can complete without a primitive query and still change the shared state.
The error example uses nested `Except` replies as data and stops by branching on that data.
It does not execute `ExceptT` or establish an aborted-prefix theorem.
-/

public section

open OracleComp OracleSpec PFunctor.FreeM QueryImpl

namespace VCVioTest.LoggedHistory

private abbrev rawSpec := Nat →ₒ BitVec 256
private abbrev serviceSpec := (Nat × Bool) →ₒ Option (BitVec 128)

private abbrev runLogged {ι κ τ : Type} {spec : OracleSpec.{0, 0} ι}
    {sig : OracleSpec.{0, 0} κ} {target : OracleSpec.{0, 0} τ} {σ α : Type}
    (ambient : QueryImpl spec (StateT σ (OracleComp target)))
    (service : QueryImpl sig (StateT σ (OracleComp target)))
    (client : OracleComp (spec + sig) α) (initial : σ) :=
  ((simulateQ (ambient.liftTarget (WriterT (QueryLog sig) (StateT σ (OracleComp target))) +
    service.withLogging) client).run).run initial

private noncomputable def ambient :
    QueryImpl rawSpec (StateT Nat (OracleComp rawSpec)) := fun request =>
  StateT.mk fun n => do
    let word ← rawSpec.query request
    pure (word, n + 10)

private noncomputable def service :
    QueryImpl serviceSpec (StateT Nat (OracleComp rawSpec)) := fun request =>
  StateT.mk fun n => do
    let word ← rawSpec.query request.1
    pure (some (word.extractLsb' 0 128), n + 1)

private noncomputable def client (key : Nat) : OracleComp (rawSpec + serviceSpec)
    (Option (BitVec 128) × Option (BitVec 128)) := do
  let first ← (rawSpec + serviceSpec).query (.inr (key, false))
  let _ ← (rawSpec + serviceSpec).query (.inl 99)
  let second ← (rawSpec + serviceSpec).query (.inr (key, true))
  pure (first, second)

private noncomputable def primitiveProgram (key initial : Nat) :
    OracleComp rawSpec (((Option (BitVec 128) × Option (BitVec 128)) ×
      QueryLog serviceSpec) × Nat) := do
  let first ← rawSpec.query key
  let _ ← rawSpec.query 99
  let second ← rawSpec.query key
  pure (((some (first.extractLsb' 0 128), some (second.extractLsb' 0 128)),
    [⟨(key, false), some (first.extractLsb' 0 128)⟩,
      ⟨(key, true), some (second.extractLsb' 0 128)⟩]), initial + 12)

private theorem run_eq_primitive (key initial : Nat) :
    runLogged ambient service (client key) initial = primitiveProgram key initial := by
  simp [runLogged, client, primitiveProgram, ambient, service,
    simulateQ_bind, StateT.run_bind, StateT.run_map, bind_assoc]

private theorem trace_cast {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {left right : OracleComp spec α} (eqn : left = right) (path : Path right) :
    Path.trace left ((Equiv.cast (congrArg (fun p : OracleComp spec α => Path p) eqn)).symm
      path) = Path.trace right path := by
  cases eqn
  rfl

private theorem output_cast {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {left right : OracleComp spec α} (eqn : left = right) (path : Path right) :
    output left ((Equiv.cast (congrArg (fun p : OracleComp spec α => Path p) eqn)).symm
      path) = output right path := by
  cases eqn
  rfl

/-- Equal low halves do not erase the exact HIGH answers in the saved primitive history. -/
private theorem retains_full_high_trace :
    ∃ h : LoggedHistory ambient service (client 7) 0,
      Path.trace _ h.fullPath =
        ([⟨7, (0 : BitVec 256)⟩, ⟨99, BitVec.ofNat 256 (2^128)⟩,
          ⟨7, BitVec.ofNat 256 (2^128)⟩] : QueryLog rawSpec) ∧
      output _ h.fullPath =
        (((some (0 : BitVec 128), some (0 : BitVec 128)),
          [⟨(7, false), some (0 : BitVec 128)⟩, ⟨(7, true), some (0 : BitVec 128)⟩]), 12) ∧
      h.checkpoints.map LoggedHistory.Checkpoint.entry =
        [⟨(7, false), some (0 : BitVec 128)⟩, ⟨(7, true), some (0 : BitVec 128)⟩] := by
  let high : BitVec 256 := BitVec.ofNat 256 (2^128)
  let primitive : Path (primitiveProgram 7 0) := ⟨0, ⟨high, ⟨high, ⟨⟩⟩⟩⟩
  let saved : LoggedRunPath ambient service (client 7) 0 :=
    (Equiv.cast (congrArg (fun p => Path p) (run_eq_primitive 7 0))).symm primitive
  obtain ⟨h, same⟩ := LoggedHistory.fullPath_surjective ambient service (client 7) 0 saved
  have traceSaved : Path.trace _ saved =
      ([⟨7, (0 : BitVec 256)⟩, ⟨99, high⟩, ⟨7, high⟩] : QueryLog rawSpec) := by
    rw [trace_cast (run_eq_primitive 7 0) primitive]
    rfl
  have outputSaved : output _ saved =
      (((some (0 : BitVec 128), some (0 : BitVec 128)),
          [⟨(7, false), some (0 : BitVec 128)⟩, ⟨(7, true), some (0 : BitVec 128)⟩]), 12) := by
    rw [output_cast (run_eq_primitive 7 0) primitive]
    decide
  have sameOutput : output _ h.fullPath =
      (((some (0 : BitVec 128), some (0 : BitVec 128)),
          [⟨(7, false), some (0 : BitVec 128)⟩, ⟨(7, true), some (0 : BitVec 128)⟩]), 12) := by
    rw [same]
    exact outputSaved
  refine ⟨h, ?_, sameOutput,
    h.checkpoints_log.trans (congrArg (fun z => z.1.2) sameOutput)⟩
  rw [same]
  exact traceSaved

private noncomputable def zeroService :
    QueryImpl (Nat →ₒ Option Nat) (StateT Nat (OracleComp rawSpec)) :=
  fun request => StateT.mk fun n => pure (if n % 2 = 0 then none else some n, n + request)

/-- A zero-query stateful service changes state and still completes one logged request. -/
private theorem zero_query_completion (initial : Nat) :
    ∃ h : LoggedHistory ambient zeroService
        (liftM ((rawSpec + (Nat →ₒ Option Nat)).query (.inr 6))) initial,
      h.checkpoints.length = 1 ∧ Path.trace _ h.fullPath = [] ∧
      output _ h.fullPath =
        (((if initial % 2 = 0 then none else some initial),
          [⟨6, if initial % 2 = 0 then none else some initial⟩]), initial + 6) := by
  have eqn : runLogged ambient zeroService
      (liftM ((rawSpec + (Nat →ₒ Option Nat)).query (.inr 6))) initial =
      pure (((if initial % 2 = 0 then none else some initial),
        [⟨6, if initial % 2 = 0 then none else some initial⟩]), initial + 6) := by
    simp [runLogged, zeroService]
  have supported : (((if initial % 2 = 0 then none else some initial),
      [⟨6, if initial % 2 = 0 then none else some initial⟩]), initial + 6) ∈ support
      (runLogged ambient zeroService
        (liftM ((rawSpec + (Nat →ₒ Option Nat)).query (.inr 6))) initial) := by
    rw [eqn]
    exact Set.mem_singleton _
  obtain ⟨h, same, logs⟩ := exists_indexed_history_of_mem_support ambient zeroService
    (liftM ((rawSpec + (Nat →ₒ Option Nat)).query (.inr 6))) initial _ supported
  have count := congrArg List.length logs
  simp only [List.length_map, List.length_cons, List.length_nil] at count
  have noPrimitive : Path.trace _ h.fullPath = [] := by
    let changePath := Equiv.cast (congrArg (fun p => Path p) eqn)
    have transfer := trace_cast eqn (changePath h.fullPath)
    simpa only [changePath, Equiv.symm_apply_apply, Path.trace_pure] using transfer
  exact ⟨h, count, noPrimitive, same⟩

-- A pure free service cannot change state without making a source query.
private theorem stateful_not_free_pure (request : Nat) (hrequest : request ≠ 0)
    (outer : QueryImpl rawSpec (StateT Nat (OracleComp rawSpec))) :
    (simulateQ outer (pure none : OracleComp rawSpec (Option Nat))).run 0 ≠
      (zeroService request).run 0 := by
  rw [simulateQ_pure, StateT.run_pure]
  change (pure (none, 0) : OracleComp rawSpec (Option Nat × Nat)) ≠ pure (none, 0 + request)
  rw [Nat.zero_add]
  intro same
  injection same with result
  exact hrequest (congrArg Prod.snd result).symm

/-- Ordinary public APIs retain a supplied path through dependent, adaptive service calls. -/
theorem adaptive_dependent_history {ι τ σ : Type} {spec : OracleSpec.{0, 0} ι}
    {target : OracleSpec.{0, 0} τ}
    (ambient : QueryImpl spec (StateT σ (OracleComp target)))
    (service : QueryImpl (fun flag : Bool => if flag then Nat else Option Nat)
      (StateT σ (OracleComp target))) (initial : σ) :
    let sig : OracleSpec Bool := fun flag => if flag then Nat else Option Nat
    let body : OracleComp (spec + sig) Nat := do
      let first ← (spec + sig).query (.inr false)
      match first with
      | none => pure 0
      | some _ => (spec + sig).query (.inr true)
    ∀ path : LoggedRunPath ambient service body initial,
      ∃ h : LoggedHistory ambient service body initial,
        h.fullPath = path ∧
        h.checkpoints.map LoggedHistory.Checkpoint.entry = (output _ path).1.2 := by
  dsimp only
  intro path
  obtain ⟨h, same⟩ := LoggedHistory.fullPath_surjective ambient service _ initial path
  refine ⟨h, same, ?_⟩
  rw [h.checkpoints_log, same]

private abbrev ErrorReply := Except Nat (Except Bool Unit)
private abbrev ErrorSpec := Nat →ₒ ErrorReply
private noncomputable def errorService :
    QueryImpl ErrorSpec (StateT Nat (OracleComp rawSpec)) := fun request =>
  pure (if request = 0 then .ok (.error false) else .error 7)
private noncomputable def errorClient (first : Nat) :
    OracleComp (rawSpec + ErrorSpec) ErrorReply := do
  let a ← (rawSpec + ErrorSpec).query (.inr first)
  match a with
  | .error e => pure (.error e)
  | .ok _ =>
    let b ← (rawSpec + ErrorSpec).query (.inr 1)
    match b with
    | .error e => pure (.error e)
    | .ok _ => (rawSpec + ErrorSpec).query (.inr 2)

/-- Nested error replies remain chronological data; the client manually stops before request 2. -/
private theorem compiled_style_error_data (initial : Nat) :
    ∃ h : LoggedHistory ambient errorService (errorClient 0) initial,
      output _ h.fullPath =
        ((.error 7, [⟨0, .ok (.error false)⟩, ⟨1, .error 7⟩]), initial) ∧
      h.checkpoints.length = 2 := by
  have eqn : runLogged ambient errorService (errorClient 0) initial =
      pure ((.error 7, [⟨0, .ok (.error false)⟩, ⟨1, .error 7⟩]), initial) := by
    simp [runLogged, errorClient, errorService, simulateQ_bind, StateT.run_pure]
  have supported : ((.error 7, [⟨0, .ok (.error false)⟩, ⟨1, .error 7⟩]), initial) ∈ support
      (runLogged ambient errorService (errorClient 0) initial) := by
    rw [eqn]
    exact Set.mem_singleton _
  obtain ⟨h, same, logs⟩ := exists_indexed_history_of_mem_support ambient errorService
    (errorClient 0) initial _ supported
  have count := congrArg List.length logs
  simp only [List.length_map, List.length_cons, List.length_nil] at count
  exact ⟨h, same, count⟩

end VCVioTest.LoggedHistory
