/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose

/-!
# Tagged oracle specifications

`spec.tagged K` is the specification `spec` with every query carrying an extra tag `k : K`
beside its input; the answer type ignores the tag. `QueryImpl.tagWith k` issues each query of a
program with the tag `k`, and `QueryImpl.untag` forgets the tags again. Tagging and then
forgetting is the identity (`QueryImpl.untag_comp_tagWith`, `simulateQ_untag_tagWith`).

A tag records which party issued a query. Tagging the parties of a composed program with
different tags, and interpreting the result through `untag`, leaves the program's behaviour
unchanged while making a per-party query budget a statement about queries whose tag is fixed:
the budget lemmas are in `VCVio.OracleComp.QueryTracking.QueryBound.Tagged`.

It is the non-dependent, product-indexed form of `OracleSpec.sigma`: every tag carries a copy of
the same specification. It is a separate, reducible definition rather than an instance of
`OracleSpec.sigma` because the answer type of a tagged query `(k, t)` must reduce to
`spec.Range t` for instance search and for the handler `tagWith` itself.
-/

public section

universe u v w

namespace OracleSpec

/-- The specification `spec` with every query carrying a tag `k : K` beside its input. The answer
to the query `(k, t)` is an answer to `t`, whatever the tag. -/
@[expose, reducible] def tagged {ι : Type u} (spec : OracleSpec.{u, v} ι) (K : Type w) :
    OracleSpec.{max w u, v} (K × ι) :=
  fun kt => spec kt.2

end OracleSpec

namespace QueryImpl

open OracleSpec OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {K : Type w}

/-- The handler answering each query `t` of `spec` by the query `(k, t)` of `spec.tagged K`. -/
def tagWith (k : K) : QueryImpl spec (OracleComp (spec.tagged K)) :=
  fun t => liftM ((spec.tagged K).query (k, t))

/-- The handler answering each tagged query `(k, t)` by the query `t` of `spec`. -/
def untag : QueryImpl (spec.tagged K) (OracleComp spec) :=
  fun kt => liftM (spec.query kt.2)

@[simp]
lemma tagWith_apply (k : K) (t : spec.Domain) :
    tagWith k t = liftM ((spec.tagged K).query (k, t)) := by
  unfold tagWith; rfl

@[simp]
lemma untag_apply (kt : (spec.tagged K).Domain) :
    (untag : QueryImpl (spec.tagged K) (OracleComp spec)) kt = liftM (spec.query kt.2) := by
  unfold untag; rfl

/-- Tagging every query with `k` and then forgetting the tag is the identity handler. -/
@[simp]
theorem untag_comp_tagWith (k : K) :
    (untag : QueryImpl (spec.tagged K) (OracleComp spec)) ∘ₛ tagWith k = QueryImpl.id' spec := by
  ext t
  simp only [apply_compose, tagWith_apply, simulateQ_spec_query, untag_apply, id'_apply]

end QueryImpl

namespace OracleComp

open OracleSpec QueryImpl

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {K : Type w}

/-- Tagging every query of a computation with `k` and then forgetting the tags gives back the
computation. -/
@[simp]
theorem simulateQ_untag_tagWith (k : K) {α : Type v} (oa : OracleComp spec α) :
    simulateQ (untag : QueryImpl (spec.tagged K) (OracleComp spec)) (simulateQ (tagWith k) oa) =
      oa := by
  rw [← QueryImpl.simulateQ_compose, untag_comp_tagWith, simulateQ_id']

end OracleComp
