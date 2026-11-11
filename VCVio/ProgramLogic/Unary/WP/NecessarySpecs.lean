/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Unary.WP.Necessary
public import VCVio.OracleComp.Constructions.Replicate
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.Coercions.SubSpec.Basic

/-!
# Core `vcgen` rules for the necessary reading

Under the necessary reading (`open scoped OracleComp.Necessary`), a triple
`⦃ pre ⦄ oa ⦃ post ⦄` says that every possible output of `oa` satisfies `post` when `pre` holds.
These `@[spec]` rules let core's `vcgen` step through the primitives of oracle computations in
that reading; the query rules `Spec.query` and `Spec.monadLift_query` are in
`VCVio.ProgramLogic.Unary.WP.Necessary`.

* `Spec.uniformSample`: a uniform draw `$ᵗ β` may return any value. A uniform index `$[0..n]`
  is a query of `unifSpec`, and `ProbComp.uniformFin` is registered as an unfolding rule so that
  `vcgen` reaches the query.
* `Spec.replicate`: `oa.replicate n` returns `n` possible outputs of `oa`.
* `Spec.liftComp`, `Spec.monadLift_liftComp`: lifting to a larger oracle world, written
  `liftComp oa superSpec` or `liftM oa`, keeps the possible outputs, and `vcgen` continues into
  the lifted program.

`Spec.ofSupport` states that every program meets a postcondition holding on its support. It fits
every program, so it is not registered; passing it for an opaque sub-program, as in
`vcgen [Spec.ofSupport keygen]`, exposes the support hypothesis in the verification condition.
-/

public section

universe u u'

open Std.WP

attribute [spec] ProbComp.uniformFin

namespace OracleComp.Necessary

variable {ι : Type u} {spec : OracleSpec ι} {α : Type}

open scoped OracleComp.Necessary

/-- A uniform sample may return any element. -/
@[spec]
theorem Spec.uniformSample (β : Type) [SampleableType β] (post : β → Prop)
    {epost : EStack⟨⟩} : ⦃ ∀ x, post x ⦄ ($ᵗ β) ⦃ post; epost ⦄ :=
  ⟨fun h x _ => h x⟩

/-- Every program meets a postcondition that holds on its support. Not registered, since it fits
every program; pass it for an opaque sub-program to expose its support. -/
theorem Spec.ofSupport (oa : OracleComp spec α) (post : α → Prop) {epost : EStack⟨⟩} :
    ⦃ ∀ a ∈ support oa, post a ⦄ oa ⦃ post; epost ⦄ :=
  ⟨id⟩

/-- `oa.replicate n` returns lists of `n` possible outputs of `oa`. -/
@[spec]
theorem Spec.replicate (n : ℕ) (oa : OracleComp spec α) (post : List α → Prop)
    {epost : EStack⟨⟩} :
    ⦃ ∀ xs : List α, xs.length = n → (∀ x ∈ xs, x ∈ support oa) → post xs ⦄
      oa.replicate n ⦃ post; epost ⦄ :=
  ⟨fun h xs hxs => by
    have hxs : xs ∈ support (oa.replicate n) := hxs
    rw [support_replicate] at hxs
    exact h xs hxs.1 hxs.2⟩

/-- Lifting to a larger oracle world keeps the possible outputs. The precondition is the
necessary weakest precondition of the lifted program, so `vcgen` continues into it. -/
@[spec]
theorem Spec.liftComp {τ : Type u'} {superSpec : OracleSpec τ}
    [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec] (oa : OracleComp spec α) (post : α → Prop)
    {epost : EStack⟨⟩} :
    ⦃ wp oa post epost ⦄ liftComp oa superSpec ⦃ post; epost ⦄ :=
  ⟨fun h a ha => h a ((mem_support_liftComp_iff oa a).mp ha)⟩

/-- `Spec.liftComp` for the lift written as `liftM oa`, the form a `do` block produces when it
uses `oa` in the larger oracle world. -/
@[spec]
theorem Spec.monadLift_liftComp {τ : Type u'} {superSpec : OracleSpec τ}
    [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec] (oa : OracleComp spec α) (post : α → Prop)
    {epost : EStack⟨⟩} :
    ⦃ wp oa post epost ⦄ (MonadLift.monadLift oa : OracleComp superSpec α) ⦃ post; epost ⦄ :=
  Spec.liftComp oa post

end OracleComp.Necessary
