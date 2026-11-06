/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.SimSemantics.StateT.Basic

/-!
# Coherent histories of logged service calls

One history retains every ambient and service path of an existing logged simulation.
Each saved head determines the reply and full state at which the next history begins.
Its service checkpoints therefore belong to the same complete primitive path.
Their dependent entries recover the chronological service log.

A checkpoint position counts completed service requests, including those with no primitive queries.
It is not a primitive-query ordinal or a probability on histories.
The target is `OracleComp targetSpec`, with all carriers in `Type`.
-/

public section

namespace QueryImpl

open PFunctor.FreeM

private def bindEquiv {P : PFunctor.{0, 0}} {α β : Type}
    (body : PFunctor.FreeM P α) (next : α → PFunctor.FreeM P β) :
    Path (body >>= next) ≃ ((head : Path body) × Path (next (output body head))) := by
  let suffix := fun head : Path body => next (output body head)
  let appendEquiv : Path (PFunctor.FreeM.append body suffix) ≃
      ((head : Path body) × Path (suffix head)) := {
    toFun := Path.split body suffix
    invFun := fun h => Path.append body suffix h.1 h.2
    left_inv := Path.append_split body suffix
    right_inv := by intro h; exact Path.split_append body suffix h.1 h.2 }
  exact (Equiv.cast (congrArg (fun p : PFunctor.FreeM P β => Path p)
    (PFunctor.FreeM.append_output_eq_bind body next).symm)).trans appendEquiv

private def pushMap {P : PFunctor.{0, 0}} {α β : Type} (f : α → β) :
    (body : PFunctor.FreeM P α) → Path body → Path (f <$> body)
  | .pure _, _ => ⟨⟩
  | .liftBind _ next, ⟨answer, tail⟩ => ⟨answer, pushMap f (next answer) tail⟩

private theorem pushMap_pullMap {P : PFunctor.{0, 0}} {α β : Type} (f : α → β) :
    (body : PFunctor.FreeM P α) → (path : Path (f <$> body)) →
      pushMap f body (Path.pullMap f body path) = path
  | .pure _, _ => rfl
  | .liftBind _ next, ⟨answer, tail⟩ => by
    change (⟨answer, pushMap f (next answer) (Path.pullMap f (next answer) tail)⟩ :
      Path (f <$> PFunctor.FreeM.liftBind _ next)) = ⟨answer, tail⟩
    rw [pushMap_pullMap]

open OracleComp OracleSpec
variable {ι κ τ : Type} {spec : OracleSpec.{0, 0} ι} {sig : OracleSpec.{0, 0} κ}
  {targetSpec : OracleSpec.{0, 0} τ} {σ α : Type}

private abbrev loggedRun (ambient : QueryImpl spec (StateT σ (OracleComp targetSpec)))
    (service : QueryImpl sig (StateT σ (OracleComp targetSpec)))
    (body : OracleComp (spec + sig) α) (s : σ) :=
  ((simulateQ
    (ambient.liftTarget (WriterT (QueryLog sig) (StateT σ (OracleComp targetSpec))) +
      service.withLogging) body).run).run s

/-- Paths of the existing logged simulation, including its complete target-state endpoint.

The client uses an ambient oracle and a logged service.
Both handlers return target free programs over the same state.
All input, answer, result and state carriers are in `Type`.
-/
abbrev LoggedRunPath (ambient : QueryImpl spec (StateT σ (OracleComp targetSpec)))
    (service : QueryImpl sig (StateT σ (OracleComp targetSpec)))
    (body : OracleComp (spec + sig) α) (s : σ) : Type :=
  Path (((simulateQ
    (ambient.liftTarget (WriterT (QueryLog sig) (StateT σ (OracleComp targetSpec))) +
      service.withLogging) body).run).run s)

/-- Coherent paths of every ambient step and completed service request.

Each successor starts at the reply and entire state returned by its saved head path.
Ambient paths are retained even though they emit no service-log entry.
-/
inductive LoggedHistory
    (ambient : QueryImpl spec (StateT σ (OracleComp targetSpec)))
    (service : QueryImpl sig (StateT σ (OracleComp targetSpec))) :
    OracleComp (spec + sig) α → σ → Type
  | done (value : α) (s : σ) : LoggedHistory ambient service (pure value) s
  | ambient (request : spec.Domain)
      (next : spec.Range request → OracleComp (spec + sig) α) (s : σ)
      (head : Path ((ambient request).run s))
      (tail : LoggedHistory ambient service
        (next (output ((ambient request).run s) head).1)
        (output ((ambient request).run s) head).2) :
      LoggedHistory ambient service (OracleComp.queryBind (.inl request) next) s
  | service (request : sig.Domain)
      (next : sig.Range request → OracleComp (spec + sig) α) (s : σ)
      (head : Path ((service request).run s))
      (tail : LoggedHistory ambient service
        (next (output ((service request).run s) head).1)
        (output ((service request).run s) head).2) :
      LoggedHistory ambient service (OracleComp.queryBind (.inr request) next) s

private theorem ambient_step
    (ambient : QueryImpl spec (StateT σ (OracleComp targetSpec)))
    (service : QueryImpl sig (StateT σ (OracleComp targetSpec))) (request : spec.Domain)
    (next : spec.Range request → OracleComp (spec + sig) α) (s : σ) :
    loggedRun ambient service (liftM ((spec + sig).query (.inl request)) >>= next) s =
      (ambient request).run s >>= fun z => loggedRun ambient service (next z.1) z.2 := by
  unfold loggedRun
  rw [QueryImpl.simulateQ_add_query_bind_left]
  simp only [QueryImpl.liftTarget_apply, WriterT.run_bind', WriterT.run_monadLift',
    StateT.run_bind, StateT.run_map, bind_map_left, List.empty_eq, List.nil_append]
  apply bind_congr
  intro z
  change id <$> _ = _
  exact PFunctor.FreeM.id_map _

private theorem service_step
    (ambient : QueryImpl spec (StateT σ (OracleComp targetSpec)))
    (service : QueryImpl sig (StateT σ (OracleComp targetSpec))) (request : sig.Domain)
    (next : sig.Range request → OracleComp (spec + sig) α) (s : σ) :
    loggedRun ambient service (liftM ((spec + sig).query (.inr request)) >>= next) s =
      (service request).run s >>= fun z =>
        (fun result : (α × QueryLog sig) × σ =>
          ((result.1.1, [⟨request, z.1⟩] ++ result.1.2), result.2)) <$>
            loggedRun ambient service (next z.1) z.2 := by
  unfold loggedRun
  rw [QueryImpl.simulateQ_add_query_bind_right]
  simp only [WriterT.run_bind', QueryImpl.run_withLogging_apply, StateT.run_bind,
    StateT.run_pure, StateT.run_map, bind_assoc]
  apply bind_congr
  intro z
  rfl

/-- Assemble the saved heads into a path of the exact existing logged run. -/
def LoggedHistory.fullPath
    {ambient : QueryImpl spec (StateT σ (OracleComp targetSpec))}
    {service : QueryImpl sig (StateT σ (OracleComp targetSpec))}
    {body : OracleComp (spec + sig) α} {s : σ} :
    LoggedHistory ambient service body s → LoggedRunPath ambient service body s
  | .done value initial => by
    change Path (pure ((value, []), initial) : OracleComp targetSpec _)
    exact ⟨⟩
  | .ambient request next initial head tail => by
    change Path (loggedRun ambient service
      (liftM ((spec + sig).query (.inl request)) >>= next) initial)
    let transport := Equiv.cast (congrArg
      (fun p : OracleComp targetSpec ((α × QueryLog sig) × σ) => Path p)
      (ambient_step ambient service request next initial))
    exact transport.symm ((bindEquiv ((ambient request).run initial)
      (fun z => loggedRun ambient service (next z.1) z.2)).symm ⟨head, tail.fullPath⟩)
  | .service request next initial head tail => by
    change Path (loggedRun ambient service
      (liftM ((spec + sig).query (.inr request)) >>= next) initial)
    let transport := Equiv.cast (congrArg
      (fun p : OracleComp targetSpec ((α × QueryLog sig) × σ) => Path p)
      (service_step ambient service request next initial))
    exact transport.symm ((bindEquiv ((service request).run initial)
      (fun z => (fun result : (α × QueryLog sig) × σ =>
        ((result.1.1, [⟨request, z.1⟩] ++ result.1.2), result.2)) <$>
          loggedRun ambient service (next z.1) z.2)).symm
      ⟨head, pushMap _ _ tail.fullPath⟩)

/-- Every supplied primitive path is retained by some coherent history.

The equality preserves the whole path, rather than only its terminal value.
-/
theorem LoggedHistory.fullPath_surjective
    (ambient : QueryImpl spec (StateT σ (OracleComp targetSpec)))
    (service : QueryImpl sig (StateT σ (OracleComp targetSpec)))
    (body : OracleComp (spec + sig) α) :
    ∀ s (path : LoggedRunPath ambient service body s),
      ∃ h : LoggedHistory ambient service body s, h.fullPath = path := by
  induction body using OracleComp.inductionOn with
  | pure value =>
    intro s path
    cases path
    exact ⟨.done value s, rfl⟩
  | query_bind input next ih =>
    intro s path
    cases input with
    | inl request =>
      let headProgram := (ambient request).run s
      let suffix := fun z : spec.Range request × σ => loggedRun ambient service (next z.1) z.2
      let equation := ambient_step ambient service request next s
      let castPath := Equiv.cast (congrArg
        (fun p : OracleComp targetSpec ((α × QueryLog sig) × σ) => Path p) equation)
      let path' := castPath path
      let pieces := bindEquiv headProgram suffix path'
      obtain ⟨tail, htail⟩ :=
        ih (output headProgram pieces.1).1 (output headProgram pieces.1).2 pieces.2
      refine ⟨.ambient request next s pieces.1 tail, ?_⟩
      apply castPath.injective
      change castPath (castPath.symm
        ((bindEquiv headProgram suffix).symm ⟨pieces.1, tail.fullPath⟩)) = path'
      rw [Equiv.apply_symm_apply]
      rw [htail]
      exact (bindEquiv headProgram suffix).symm_apply_apply path'
    | inr request =>
      let headProgram := (service request).run s
      let suffix := fun z : sig.Range request × σ => (fun result : (α × QueryLog sig) × σ =>
        ((result.1.1, [⟨request, z.1⟩] ++ result.1.2), result.2)) <$>
          loggedRun ambient service (next z.1) z.2
      let equation := service_step ambient service request next s
      let castPath := Equiv.cast (congrArg
        (fun p : OracleComp targetSpec ((α × QueryLog sig) × σ) => Path p) equation)
      let path' := castPath path
      let pieces := bindEquiv headProgram suffix path'
      let returned := output headProgram pieces.1
      let erase := fun result : (α × QueryLog sig) × σ =>
        ((result.1.1, [⟨request, returned.1⟩] ++ result.1.2), result.2)
      let remainder := loggedRun ambient service (next returned.1) returned.2
      let tailPath := Path.pullMap erase remainder pieces.2
      obtain ⟨tail, htail⟩ := ih returned.1 returned.2 tailPath
      refine ⟨.service request next s pieces.1 tail, ?_⟩
      apply castPath.injective
      change castPath (castPath.symm ((bindEquiv headProgram suffix).symm
        ⟨pieces.1, pushMap erase remainder tail.fullPath⟩)) = path'
      rw [Equiv.apply_symm_apply]
      rw [htail, pushMap_pullMap]
      exact (bindEquiv headProgram suffix).symm_apply_apply path'

/-- One completed service request with its exact entry state and primitive target path. -/
structure LoggedHistory.Checkpoint
    (service : QueryImpl sig (StateT σ (OracleComp targetSpec))) where
  /-- The service request whose actual target path is saved. -/
  request : sig.Domain
  /-- The entire state at entry to this service request. -/
  before : σ
  /-- The saved path determines both the reply and the entire after-state. -/
  path : Path ((service request).run before)

/-- Chronological service checkpoints from the same history.

A service with no primitive queries still contributes one checkpoint.
Intervening ambient steps can change the state between two service checkpoints.
-/
@[expose] def LoggedHistory.checkpoints
    {ambient : QueryImpl spec (StateT σ (OracleComp targetSpec))}
    {service : QueryImpl sig (StateT σ (OracleComp targetSpec))}
    {body : OracleComp (spec + sig) α} {s : σ} :
    LoggedHistory ambient service body s → List (LoggedHistory.Checkpoint service)
  | .done _ _ => []
  | .ambient _ _ _ _ tail => tail.checkpoints
  | .service request _ initial head tail => ⟨request, initial, head⟩ :: tail.checkpoints

private theorem output_cast_symm {P : PFunctor.{0, 0}} {a : Type}
    {left right : PFunctor.FreeM P a} (eqn : left = right) (path : Path right) :
    output left ((Equiv.cast (congrArg (fun p : PFunctor.FreeM P a => Path p) eqn)).symm path) =
      output right path := by
  cases eqn
  rfl

private theorem output_append {P : PFunctor.{0, 0}} {a b : Type} :
    (body : PFunctor.FreeM P a) → (next : Path body → PFunctor.FreeM P b) →
    (head : Path body) → (tail : Path (next head)) →
      output (PFunctor.FreeM.append body next) (Path.append body next head tail) =
        output (next head) tail
  | .pure _, _, _, _ => rfl
  | .liftBind _ next, suffix, ⟨answer, head⟩, tail =>
    output_append (next answer) (fun p => suffix ⟨answer, p⟩) head tail

private theorem output_bindEquiv {P : PFunctor.{0, 0}} {a b : Type}
    (body : PFunctor.FreeM P a) (next : a → PFunctor.FreeM P b)
    (head : Path body) (tail : Path (next (output body head))) :
    output (body >>= next) ((bindEquiv body next).symm ⟨head, tail⟩) =
      output (next (output body head)) tail := by
  change output (body >>= next)
    ((Equiv.cast (congrArg (fun p : PFunctor.FreeM P b => Path p)
      (PFunctor.FreeM.append_output_eq_bind body next).symm)).symm
      (Path.append body (fun p => next (output body p)) head tail)) = _
  rw [output_cast_symm]
  · exact output_append body (fun p => next (output body p)) head tail
  · exact (PFunctor.FreeM.append_output_eq_bind body next).symm

private theorem output_pushMap {P : PFunctor.{0, 0}} {a b : Type} (f : a → b) :
    (body : PFunctor.FreeM P a) → (path : Path body) →
      output (f <$> body) (pushMap f body path) = f (output body path)
  | .pure _, _ => rfl
  | .liftBind _ next, ⟨answer, tail⟩ => output_pushMap f (next answer) tail

/-- The dependent log entry reads the reply from this checkpoint's own saved path. -/
@[expose] def LoggedHistory.Checkpoint.entry
    {service : QueryImpl sig (StateT σ (OracleComp targetSpec))}
    (c : LoggedHistory.Checkpoint service) :
    (request : sig.Domain) × sig.Range request :=
  ⟨c.request, (output ((service c.request).run c.before) c.path).1⟩

/-- Checkpoint readback is the exact chronological log of this history's full path. -/
theorem LoggedHistory.checkpoints_log
    {ambient : QueryImpl spec (StateT σ (OracleComp targetSpec))}
    {service : QueryImpl sig (StateT σ (OracleComp targetSpec))} :
    {body : OracleComp (spec + sig) α} → {s : σ} → (h : LoggedHistory ambient service body s) →
      h.checkpoints.map LoggedHistory.Checkpoint.entry =
        (output _ h.fullPath).1.2
  | _, _, .done _ _ => rfl
  | _, _, .ambient request next initial head tail => by
    change tail.checkpoints.map LoggedHistory.Checkpoint.entry =
      (output _ ((Equiv.cast (congrArg
        (fun p : OracleComp targetSpec ((α × QueryLog sig) × σ) => Path p)
        (ambient_step ambient service request next initial))).symm _)).1.2
    rw [output_cast_symm, output_bindEquiv]
    · exact tail.checkpoints_log
    · exact ambient_step ambient service request next initial
  | _, _, .service request next initial head tail => by
    change LoggedHistory.Checkpoint.entry
      (⟨request, initial, head⟩ : LoggedHistory.Checkpoint service) ::
      tail.checkpoints.map LoggedHistory.Checkpoint.entry =
      (output _ ((Equiv.cast (congrArg
        (fun p : OracleComp targetSpec ((α × QueryLog sig) × σ) => Path p)
        (service_step ambient service request next initial))).symm _)).1.2
    rw [output_cast_symm, output_bindEquiv, output_pushMap]
    · change _ :: _ = _ :: _
      rw [tail.checkpoints_log]
      rfl
    · exact service_step ambient service request next initial

/-- A supported joint result, log and final state come from one coherent history.

This is a statement about possible paths, not a distribution on histories.
-/
theorem exists_indexed_history_of_mem_support
    (ambient : QueryImpl spec (StateT σ (OracleComp targetSpec)))
    (service : QueryImpl sig (StateT σ (OracleComp targetSpec)))
    (body : OracleComp (spec + sig) α) (s : σ)
    (z : (α × QueryLog sig) × σ)
    (hz : z ∈ support (((simulateQ
      (ambient.liftTarget (WriterT (QueryLog sig) (StateT σ (OracleComp targetSpec))) +
        service.withLogging) body).run).run s)) :
    ∃ h : LoggedHistory ambient service body s,
      output _ h.fullPath = z ∧
      h.checkpoints.map LoggedHistory.Checkpoint.entry = z.1.2 := by
  rw [PFunctor.FreeM.support_eq_range_output] at hz
  obtain ⟨path, hpath⟩ := hz
  obtain ⟨h, samePath⟩ := LoggedHistory.fullPath_surjective ambient service body s path
  have same : output _ h.fullPath = z := by rw [samePath]; exact hpath
  exact ⟨h, same, h.checkpoints_log.trans (congrArg (fun p => p.1.2) same)⟩

end QueryImpl
