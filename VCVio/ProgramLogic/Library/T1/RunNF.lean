/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.Monad.Support
public import VCVio.OracleComp.SimSemantics.Append.Core
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.ProgramLogic.Library.T1.Attr
public import ToMathlib.Control.WriterT

/-!
# Members of the `simulateQ_nf` simp set

`simp only [simulateQ_nf]` runs a simulated program into its base monad. The set has five
layers, made of existing equations and the run equations of conditionals stated here:

* *Simulation*: `simulateQ` distributes over `pure`, `>>=`, `<$>`, `<*>`, `if` and `dite`, and a
  query becomes the handler call (`simulateQ_spec_query`, `simulateQ_HasQuery_query`; the general
  `simulateQ_query` at low priority, since it leaves an `id <$>` behind on primitive queries).
* *Sum handlers*: `(impl₁ + impl₂) (.inl t)` is `impl₁ t`, a query or computation lifted from a
  summand runs under its summand handler, and a `HasQuery` query through a lift is the lifted
  primitive query.
* *Transformer runs*: the `StateT` and `WriterT` run equations, including `get`, `set`,
  `modifyGet`, `modify`, lifts, `tell` and conditionals (`StateT.run_ite`, `StateT.run_dite`,
  `WriterT.run_ite`, stated here); `run'` becomes a map of `Prod.fst`.
* *Monad laws*: binds are reassociated, `pure` is cancelled and maps are pushed into binds, with
  the units of the writer logs (`* 1`, `++ ∅`) dropped.
* *Support*: membership in the support of a bind, `pure` or map is unfolded, so a hypothesis
  `z ∈ support ((simulateQ impl oa).run s)` becomes a chain of existentials over the one-step
  runs, ready for `obtain`.
-/

public section

universe u v

/-! ## Conditionals in transformer runs -/

namespace StateT

variable {m : Type u → Type v} {σ α : Type u} (c : Prop) [Decidable c]

/-- Running a conditional `StateT` computation runs the selected branch. -/
@[simulateQ_nf]
theorem run_ite (x y : StateT σ m α) (s : σ) :
    (if c then x else y).run s = if c then x.run s else y.run s := by
  split <;> rfl

/-- Running a dependent conditional `StateT` computation runs the selected branch. -/
@[simulateQ_nf]
theorem run_dite (x : c → StateT σ m α) (y : ¬c → StateT σ m α) (s : σ) :
    (if h : c then x h else y h).run s = if h : c then (x h).run s else (y h).run s := by
  split <;> rfl

end StateT

namespace WriterT

variable {m : Type u → Type v} {ω α : Type u} (c : Prop) [Decidable c]

/-- Running a conditional `WriterT` computation runs the selected branch. -/
@[simulateQ_nf]
theorem run_ite (x y : WriterT ω m α) : (if c then x else y).run = if c then x.run else y.run := by
  split <;> rfl

end WriterT

/-! ## Existing members -/

attribute [simulateQ_nf] simulateQ_pure simulateQ_bind simulateQ_map simulateQ_spec_query
  simulateQ_HasQuery_query simulateQ_seq simulateQ_seqLeft simulateQ_seqRight simulateQ_ite
  simulateQ_dite OracleQuery.input_query OracleQuery.cont_query

attribute [simulateQ_nf low] simulateQ_query

attribute [simulateQ_nf] QueryImpl.add_apply_inl QueryImpl.add_apply_inr
  QueryImpl.simulateQ_add_liftM_query_left QueryImpl.simulateQ_add_liftM_query_right
  QueryImpl.simulateQ_add_liftM_left QueryImpl.simulateQ_add_liftM_right
  QueryImpl.simulateQ_add_liftComp_left QueryImpl.simulateQ_add_liftComp_right
  QueryImpl.liftTarget_apply HasQuery.instOfMonadLift_query

attribute [simulateQ_nf] StateT.run_bind StateT.run_pure StateT.run_map StateT.run_get
  StateT.run_set StateT.run_modifyGet StateT.run_modify StateT.run_monadLift StateT.run_lift
  StateT.run_seq StateT.run_seqLeft StateT.run_seqRight StateT.run'_eq monadLift_self

attribute [simulateQ_nf] WriterT.run_bind WriterT.run_pure WriterT.run_map WriterT.run_mk
  WriterT.run_tell WriterT.run_monadLift WriterT.run_monadLift' AddWriterT.run_addTell

attribute [simulateQ_nf] pure_bind bind_pure bind_assoc map_pure map_bind bind_map_left
  Functor.map_map id_map mul_one one_mul LawfulAppend.empty_append LawfulAppend.append_empty

attribute [simulateQ_nf] mem_support_bind_iff mem_support_pure_iff support_map Set.mem_image
  Prod.mk.injEq
