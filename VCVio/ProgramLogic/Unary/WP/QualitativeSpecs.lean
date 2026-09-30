/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Unary.WP.Qualitative
public import VCVio.OracleComp.Constructions.Replicate
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.Coercions.SubSpec.Basic

/-!
# `vcgen` rules for the structural reading of oracle computations

Under `open scoped OracleComp.Qualitative` a triple `⦃ pre ⦄ oa ⦃ post ⦄` says that every
structurally reachable output of `oa` satisfies `post` when `pre` holds. The rules below let core's
`vcgen` step through the common primitives of oracle computations in that reading:

* `Spec.uniformSample` and `Spec.uniformFin`: a uniform draw (`$ᵗ β`, `$[0..n]`) may return any
  value;
* `Spec.replicate`: `oa.replicate n` returns `n` possible outputs of `oa`;
* `Spec.liftComp`: lifting to a larger oracle world keeps the possible outputs, and `vcgen`
  continues into the lifted program.

`Spec.ofSupport` states that every program meets a postcondition holding on its support. It
applies to every program, so it is not registered; passing it for an opaque sub-program, as in
`vcgen [Spec.ofSupport keygen]`, exposes the support hypothesis in the verification condition.

The query rules `Spec.query` and `Spec.monadLift_query` are in
`VCVio.ProgramLogic.Unary.WP.Qualitative`. The bridges between structural triples and events of
probability one or zero are in `VCVio.ProgramLogic.Unary.WP.Coherence`.
-/

public section

universe u u'

open Std.WP

namespace OracleComp.Qualitative

open scoped OracleComp.Qualitative

variable {ι : Type u} {spec : OracleSpec ι} {α : Type}

/-- A uniform sample may return any element. -/
@[spec]
theorem Spec.uniformSample (β : Type) [SampleableType β] (post : β → Prop)
    {epost : EStack⟨⟩} : Triple ($ᵗ β) (∀ x, post x) post epost :=
  ⟨fun h x _ => h x⟩

/-- A uniform index `$[0..n]` may be any element of `Fin (n + 1)`. -/
@[spec]
theorem Spec.uniformFin (n : ℕ) (post : Fin (n + 1) → Prop) {epost : EStack⟨⟩} :
    Triple ($[0..n]) (∀ i, post i) post epost :=
  ⟨fun h i _ => h i⟩

/-- Every program meets a postcondition that holds on its support. Not registered, since it
applies to every program; pass it for an opaque sub-program to expose its support. -/
theorem Spec.ofSupport (oa : OracleComp spec α) (post : α → Prop) {epost : EStack⟨⟩} :
    Triple oa (∀ a ∈ support oa, post a) post epost :=
  ⟨id⟩

/-- `oa.replicate n` returns lists of `n` possible outputs of `oa`. -/
@[spec]
theorem Spec.replicate (n : ℕ) (oa : OracleComp spec α) (post : List α → Prop)
    {epost : EStack⟨⟩} :
    Triple (oa.replicate n)
      (∀ xs : List α, xs.length = n → (∀ x ∈ xs, x ∈ support oa) → post xs) post epost :=
  ⟨fun h xs hxs => by
    have hxs : xs ∈ support (oa.replicate n) := hxs
    rw [support_replicate] at hxs
    exact h xs hxs.1 hxs.2⟩

/-- Lifting to a larger oracle world keeps the possible outputs. The precondition is the
structural weakest precondition of the lifted program, so `vcgen` continues into it. -/
@[spec]
theorem Spec.liftComp {τ : Type u'} {superSpec : OracleSpec τ}
    [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec] (oa : OracleComp spec α) (post : α → Prop)
    {epost : EStack⟨⟩} :
    Triple (liftComp oa superSpec) (wp oa post epost) post epost :=
  ⟨fun h a ha => h a ((mem_support_liftComp_iff oa a).mp ha)⟩

end OracleComp.Qualitative
