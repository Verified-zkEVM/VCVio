/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

/-!
# Comparing computations from a known cache

A partial cache can determine an output without specifying answers for every query.
Two computations can also give the same joint output and final cache from every extension
of the known cache. This relation composes across adaptive continuations.
-/

public section

open OracleComp OracleSpec

namespace OracleSpec.QueryCache

variable {ι α β : Type} {spec : OracleSpec ι} {cache : QueryCache spec}

/-- The partial cache answers all queries on this execution path. -/
@[expose] def Resolves (cache : QueryCache spec) (program : OracleComp spec α)
    (answer : α) : Prop :=
  simulateQ cache.toPartialImpl program = some answer

namespace Resolves

/-- A pure result is already determined by an empty sequence of queries. -/
protected theorem pure (x : α) : Resolves cache (Pure.pure x) x := rfl

/-- A pure computation can resolve only to its own result. -/
theorem pure_inv {x y : α} (h : Resolves cache (Pure.pure x) y) : x = y :=
  Option.some.inj h

/-- Knowing the first result determines which continuation to replay. -/
theorem bind {p : OracleComp spec α} {k : α → OracleComp spec β} {x y}
    (hp : Resolves cache p x) (hk : Resolves cache (k x) y) : Resolves cache (p >>= k) y := by
  unfold Resolves at *
  rw [simulateQ_bind, hp]
  exact hk

/-- A successful replay of a bind determines both results. -/
theorem of_bind {p : OracleComp spec α} {k : α → OracleComp spec β} {y}
    (h : Resolves cache (p >>= k) y) : ∃ x, Resolves cache p x ∧ Resolves cache (k x) y := by
  unfold Resolves at *
  rw [simulateQ_bind] at h
  exact Option.bind_eq_some_iff.mp h

/-- Mapping the output preserves a successful cache reading. -/
theorem map {p : OracleComp spec α} {x} (h : Resolves cache p x) (f : α → β) :
    Resolves cache (f <$> p) (f x) := by
  rw [map_eq_bind_pure_comp]
  exact h.bind (.pure _)

/-- Adding cache entries preserves every successful reading. -/
theorem mono {p : OracleComp spec α} {x} (h : Resolves cache p x) {c : QueryCache spec}
    (le : cache ≤ c) : Resolves c p x := simulateQ_toPartialImpl_mono le p h

/-- A total answer function agreeing with the cache produces the replayed output. -/
theorem eval {p : OracleComp spec α} {x} (h : Resolves cache p x) (f : QueryImpl spec Id)
    (hf : cache.AgreesWithFn f) : evalWithAnswerFn f p = x :=
  evalWithAnswerFn_eq_of_agreesWithFn hf p h

end Resolves

variable [DecidableEq ι]

/-- Each extension gives the same joint law of the output and the final cache. -/
@[expose] def ReplayEq (cache : QueryCache spec) (left right : OracleComp spec α) : Prop :=
  ∀ (sampler : QueryImpl spec ProbComp) (c : QueryCache spec), cache ≤ c →
    (simulateQ sampler.withCaching left).run c =ᵈ (simulateQ sampler.withCaching right).run c

namespace ReplayEq

/-- Each computation agrees with itself on every extension. -/
protected theorem refl (cache : QueryCache spec) (p : OracleComp spec α) : ReplayEq cache p p :=
  fun _ _ _ => .refl _

/-- Returning the same value preserves the cache. -/
protected theorem pure (a : α) : ReplayEq cache (Pure.pure a) (Pure.pure a) := .refl _ _

/-- The first computation grows the cache, so corresponding continuations still agree. -/
theorem bind {p q : OracleComp spec α} (h : ReplayEq cache p q) (f g : α → OracleComp spec β)
    (k : ∀ x, ReplayEq cache (f x) (g x)) : ReplayEq cache (p >>= f) (q >>= g) := by
  intro sampler c hc
  simp only [simulateQ_bind, StateT.run_bind]
  refine (EvalDistEq.bind_left (h sampler c hc) _).trans ?_
  refine EvalDistEq.bind_congr_of_support _ fun z hz => ?_
  have grows := QueryImpl.le_snd_of_mem_support_run_simulateQ_withCaching sampler q hz
  exact k z.1 sampler z.2 (hc.trans grows)

/-- A computation determined by the known cache can be replaced by its output in a bind. -/
theorem bind_known {p : OracleComp spec α} {a : α} (h : Resolves cache p a)
    (f : α → OracleComp spec β) (q : OracleComp spec β) (k : ReplayEq cache (f a) q) :
    ReplayEq cache (p >>= f) q := by
  intro sampler c hc
  rw [simulateQ_bind, StateT.run_bind,
    QueryImpl.run_simulateQ_withCaching_eq_pure_of_toPartialImpl sampler p (h.mono hc), pure_bind]
  exact k sampler c hc

end ReplayEq
end OracleSpec.QueryCache
