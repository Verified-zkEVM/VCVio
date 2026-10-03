/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Relational.Basic
public import VCVio.ProgramLogic.Unary.WP.Necessary

/-!
# Lifting unary triples to relational couplings

Two `OracleComp` computations that are independently correct, each satisfying a core triple of
the necessary reading (the global instance of `OracleComp`), can always be paired by the
product coupling, since every `OracleComp` output measure is a probability measure.

This file provides the "unary → relational" bridge:

* `relTriple_prod_of_triple` — two unary triples with precondition `True` give a relational
  triple on the product postcondition.
* `relTriple_of_triple_of_implies` — the same coupling, weakened to any relation implied by the
  conjunction of the two postconditions.

Both specialize `relTriple_prod`, which takes `support`-style postconditions: under the necessary
reading, `⦃ True ⦄ oa ⦃ P ⦄` says that every possible output of `oa` satisfies `P`
(`OracleComp.Necessary.wp_iff_forall_support`). Unary facts proved with core `vcgen` compose
into relational arguments (e.g. game-hopping reductions) without redoing the underlying analysis.
-/

@[expose] public section

open ENNReal OracleSpec OracleComp
open scoped Std.WP

universe u

namespace OracleComp.ProgramLogic.Relational

variable {ι₁ : Type u} {ι₂ : Type u}
variable {spec₁ : OracleSpec.{u, 0} ι₁} {spec₂ : OracleSpec.{u, 0} ι₂}
variable [OracleSpec.AnswerMeasure spec₁] [OracleSpec.AnswerMeasure spec₂]
  [∀ t, Finite (spec₁.Range t)] [∀ t, Finite (spec₂.Range t)]
variable {α β : Type}

/-- Two independent unary triples with precondition `True` combine into a `RelTriple` over the
product postcondition. -/
theorem relTriple_prod_of_triple {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {P : α → Prop} {Q : β → Prop} (hP : ⦃ True ⦄ oa ⦃ P ⦄) (hQ : ⦃ True ⦄ ob ⦃ Q ⦄) :
    RelTriple oa ob (fun a b => P a ∧ Q b) :=
  relTriple_prod ((OracleComp.Necessary.wp_iff_forall_support oa P).1 (hP.le_wp trivial))
    ((OracleComp.Necessary.wp_iff_forall_support ob Q).1 (hQ.le_wp trivial))

/-- Relational triples are monotone in the postcondition, so a product coupling can be
weakened to any relation implied by the conjunction of independent postconditions. -/
theorem relTriple_of_triple_of_implies {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {P : α → Prop} {Q : β → Prop} {R : RelPost α β}
    (hP : ⦃ True ⦄ oa ⦃ P ⦄) (hQ : ⦃ True ⦄ ob ⦃ Q ⦄)
    (hImp : ∀ a b, P a → Q b → R a b) :
    RelTriple oa ob R :=
  relTriple_post_mono (relTriple_prod_of_triple hP hQ) (fun _ _ ⟨hp, hq⟩ => hImp _ _ hp hq)

/-! ## Smoke tests -/

/-- Smoke test: two independent pure computations compose into a product relational
triple, without touching any coupling machinery by hand. -/
private example (x : α) (y : β) :
    RelTriple (pure x : OracleComp spec₁ α) (pure y : OracleComp spec₂ β)
      (fun a b => a = x ∧ b = y) :=
  relTriple_prod_of_triple
    ⟨fun _ => (OracleComp.Necessary.wp_iff_forall_support _ _).2 (by simp)⟩
    ⟨fun _ => (OracleComp.Necessary.wp_iff_forall_support _ _).2 (by simp)⟩

/-- Smoke test: using `relTriple_of_triple_of_implies` to project a product coupling onto
any logically weaker relation. -/
private example (x : α) :
    RelTriple (pure x : OracleComp spec₁ α) (pure x : OracleComp spec₁ α) (EqRel α) :=
  relTriple_of_triple_of_implies (P := fun a => a = x) (Q := fun a => a = x)
    ⟨fun _ => (OracleComp.Necessary.wp_iff_forall_support _ _).2 (by simp)⟩
    ⟨fun _ => (OracleComp.Necessary.wp_iff_forall_support _ _).2 (by simp)⟩
    (fun _ _ hP hQ => by dsimp [EqRel]; rw [hP, hQ])

end OracleComp.ProgramLogic.Relational
