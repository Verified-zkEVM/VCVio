/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import ToMathlib.Control.Except
public import ToMathlib.Control.WriterT

/-!
# Exceptional replies as total free programs

Wrapping each answer type in `Except` keeps the same query inputs.
The compiled client stops its continuation on an error reply and returns that error as data.
Its backend supplies the existing effects; this construction chooses no response measure.

The simulation law preserves the fully run result in any lawful target monad.
Putting `ExceptT` outside an additive writer retains all prefix charges on error.
The joint writer/state law observes `((Except result, charge), final state)` without discarding
the error branch through successful-output semantics.
-/

public section

universe u v

namespace OracleSpec

/-- Keep every input and wrap its reply in a typed error alternative.

The reply family reduces during elaboration of dependent handler types.
-/
@[reducible, expose]
def exceptReplies {ι : Type u} (spec : OracleSpec.{u, u} ι) (ε : Type u) : OracleSpec ι :=
  ofFn fun t => Except ε (spec.Range t)

/-- An exceptional reply carries either the error or the original answer at the same input. -/
@[simp]
theorem exceptReplies_apply {ι : Type u} (spec : OracleSpec.{u, u} ι) (ε : Type u)
    (t : spec.Domain) : (spec.exceptReplies ε).Range t = Except ε (spec.Range t) := rfl

end OracleSpec

namespace OracleComp.ExceptReplies

open OracleSpec

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {ε α β : Type u}

/-- Ask for an exceptional reply and let `ExceptT` suppress the tail on an error. -/
@[expose]
def queryImpl (spec : OracleSpec.{u, u} ι) (ε : Type u) :
    QueryImpl spec (ExceptT ε (OracleComp (spec.exceptReplies ε))) :=
  fun t => ExceptT.mk (liftM ((spec.exceptReplies ε).query t))

/-- Reify the exceptional run as a total free program with the same query inputs. -/
@[expose]
def compile (ε : Type u) (client : OracleComp spec α) :
    OracleComp (spec.exceptReplies ε) (Except ε α) :=
  (simulateQ (queryImpl spec ε) client).run

/-- A pure client returns a successful result without asking a query. -/
@[simp]
theorem compile_pure (a : α) : compile ε (pure a : OracleComp spec α) = pure (.ok a) := rfl

/-- A single query becomes the same input with an exceptional reply. -/
@[simp]
theorem compile_query (t : spec.Domain) :
    compile ε (liftM (spec.query t) : OracleComp spec (spec.Range t)) =
      liftM ((spec.exceptReplies ε).query t) := by
  rw [compile, simulateQ_spec_query]
  rfl

/-- A compiled bind runs its tail only after a successful prefix. -/
theorem compile_bind (client : OracleComp spec α) (tail : α → OracleComp spec β) :
    compile ε (client >>= tail) = (do
      let reply ← compile ε client
      match reply with
      | .error error => pure (.error error)
      | .ok a => compile ε (tail a)) := by
  rw [compile, simulateQ_bind, ExceptT.run_bind]
  apply bind_congr
  intro reply
  cases reply <;> rfl

/-- An error reply stops the whole query continuation before any later query can run. -/
theorem compile_query_bind (t : spec.Domain) (tail : spec.Range t → OracleComp spec α) :
    compile ε (liftM (spec.query t) >>= tail) = (do
      let reply ← liftM ((spec.exceptReplies ε).query t)
      match reply with
      | .error error => pure (.error error)
      | .ok a => compile ε (tail a)) := by
  rw [compile_bind, compile_query]
  apply bind_congr
  intro reply
  cases reply <;> rfl

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

/-- Interpreting exceptional replies agrees exactly with the original exceptional simulation.

The equality concerns the full run, including errors and all effects in `m`.
-/
theorem simulateQ_compile (impl : QueryImpl spec (ExceptT ε m))
    (client : OracleComp spec α) :
    simulateQ (spec := spec.exceptReplies ε) (fun t => (impl t).run)
      (compile ε client) = (simulateQ impl client).run := by
  induction client using OracleComp.inductionOn with
  | pure a => rw [compile_pure, simulateQ_pure, simulateQ_pure, ExceptT.run_pure]
  | query_bind t tail ih =>
    simp only [compile_query_bind, simulateQ_bind, simulateQ_spec_query, ExceptT.run_bind]
    apply bind_congr
    intro reply
    cases reply <;> simp [ih]

/-- An error preserves the handler's final state and suppresses every later query. -/
theorem run_compile_query_bind_of_error {σ : Type u}
    (backend : QueryImpl (spec.exceptReplies ε) (StateT σ m))
    (t : spec.Domain) (tail : spec.Range t → OracleComp spec α)
    (s final : σ) (error : ε)
    (h : (backend t).run s = pure (.error error, final)) :
    (simulateQ backend (compile ε (liftM (spec.query t) >>= tail))).run s =
      pure (.error error, final) := by
  rw [compile_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, h]
  simp

/-- Outer exceptions preserve the result, prefix writer charge and final state jointly. -/
theorem runAdd_run_simulateQ_compile {σ ω : Type u} [AddMonoid ω]
    (impl : QueryImpl spec (ExceptT ε (AddWriterT ω (StateT σ m))))
    (client : OracleComp spec α) (s : σ) :
    (simulateQ (spec := spec.exceptReplies ε) (fun t => (impl t).run)
      (compile ε client)).runAdd.run s =
      ((simulateQ impl client).run).runAdd.run s := by
  rw [simulateQ_compile]

end OracleComp.ExceptReplies
