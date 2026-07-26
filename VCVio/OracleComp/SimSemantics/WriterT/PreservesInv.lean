/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.SimSemantics.WriterT.Basic

/-!
# `WriterT ω` Invariant Theory

Support-based invariant reasoning for query-implementations that accumulate a writer
log in a monoid `ω` (as opposed to threading state through `StateT`). Typical
use-cases include `countingOracle` (with `ω = QueryCount ι`) and `costOracle`
(with an arbitrary `Monoid ω`).

These statements mirror `QueryImpl.PreservesInv` /
`OracleComp.simulateQ_run_preservesInv` from
`SimSemantics/StateT/PreservesInv.lean`, with the writer log playing the role of
the threaded state.

## Main definitions

- `QueryImpl.WriterPreservesInv` — every oracle query implementation step preserves
  an invariant `Inv : ω → Prop` on the accumulated writer output (for `WriterT ω`
  handlers with `[Monoid ω]`)
- `OracleComp.simulateQ_run_writerPreservesInv` — simulating any oracle computation
  with a writer-invariant-preserving implementation preserves `Inv` on the final
  accumulated writer value
-/

noncomputable section

open OracleComp OracleSpec

open scoped OracleSpec.PrimitiveQuery

namespace QueryImpl

/-- `WriterPreservesInv impl Inv` means every oracle query implementation step preserves
`Inv` on the accumulated writer: starting from any `s₀` satisfying `Inv`, every reachable
post-writer `s₀ * w` (for `(a, w)` in the support of `(impl t).run`) also satisfies `Inv`. -/
def WriterPreservesInv {ι : Type} {spec : OracleSpec ι} [IsUniformSpec spec] {ω : Type} [Monoid ω]
    (impl : QueryImpl spec (WriterT ω (OracleComp spec))) (Inv : ω → Prop) : Prop :=
  ∀ t s₀, Inv s₀ → ∀ z ∈ support (impl t).run, Inv (s₀ * z.2)

lemma WriterPreservesInv.trivial {ι : Type} {spec : OracleSpec ι} [IsUniformSpec spec] {ω : Type}
    [Monoid ω] (impl : QueryImpl spec (WriterT ω (OracleComp spec))) :
    WriterPreservesInv impl (fun _ => True) :=
  fun _ _ _ _ _ => True.intro

lemma WriterPreservesInv.and
    {ι : Type} {spec : OracleSpec ι} [IsUniformSpec spec] {ω : Type} [Monoid ω]
    {impl : QueryImpl spec (WriterT ω (OracleComp spec))} {P Q : ω → Prop}
    (hP : WriterPreservesInv impl P) (hQ : WriterPreservesInv impl Q) :
    WriterPreservesInv impl (fun s => P s ∧ Q s) :=
  fun t s₀ ⟨hp, hq⟩ z hz => ⟨hP t s₀ hp z hz, hQ t s₀ hq z hz⟩

/-- `WriterPreservesInv` from an unconditional per-query witness. Analogous
to `PreservesInv.of_forall`: if every reachable increment `z.2` satisfies
`Inv (s₀ * z.2)` for *any* starting `s₀` regardless of whether `Inv s₀`
holds, then `Inv` is preserved. -/
lemma WriterPreservesInv.of_forall
    {ι : Type} {spec : OracleSpec ι} [IsUniformSpec spec] {ω : Type} [Monoid ω]
    {impl : QueryImpl spec (WriterT ω (OracleComp spec))} {Inv : ω → Prop}
    (h : ∀ t s₀ z, z ∈ support (impl t).run → Inv (s₀ * z.2)) :
    WriterPreservesInv impl Inv :=
  fun t s₀ _ z hz => h t s₀ z hz

/-- `WriterPreservesInv` from a multiplicatively-closed predicate.

If `Inv` holds on every writer increment `w` produced by a single query
(`hPerQuery`) and is closed under `*` (`hClosed`), then `Inv` is
preserved across the whole simulation. This is the canonical builder for
writer invariants: pick a submonoid-like predicate, show every per-query
increment lands in it, and you're done. -/
lemma WriterPreservesInv.of_mul_closed {ι : Type} {spec : OracleSpec ι} [IsUniformSpec spec]
    {ω : Type} [Monoid ω] {impl : QueryImpl spec (WriterT ω (OracleComp spec))} {Inv : ω → Prop}
    (hClosed : ∀ a b, Inv a → Inv b → Inv (a * b))
    (hPerQuery : ∀ t z, z ∈ support (impl t).run → Inv z.2) :
    WriterPreservesInv impl Inv :=
  fun t s₀ hs₀ z hz => hClosed s₀ z.2 hs₀ (hPerQuery t z hz)

/-! Note on composition. Unlike `PreservesInv.compose`, we do not provide a
compose analogue for `WriterPreservesInv`: the definition is keyed to a
single `spec` appearing both as the source of queries and as the inner
`OracleComp spec` monad of the writer. Composition via `∘ₛ` changes the
query spec but not the inner writer monad, so the composite signature no
longer matches `WriterPreservesInv`'s. The intended idiom is to compose
on the underlying `OracleComp` layer (e.g. via `simulateQ_compose`) and
then apply `simulateQ_run_writerPreservesInv` to the composite computation. -/

end QueryImpl

namespace OracleComp

open QueryImpl

/-- If `impl` preserves the writer invariant `Inv`, then simulating *any* oracle computation
with `simulateQ impl` preserves `Inv` on the final accumulated writer (support-wise). -/
theorem simulateQ_run_writerPreservesInv
    {ι : Type} {spec : OracleSpec ι} [IsUniformSpec spec] {ω α : Type} [Monoid ω]
    (impl : QueryImpl spec (WriterT ω (OracleComp spec))) (Inv : ω → Prop)
    (himpl : QueryImpl.WriterPreservesInv impl Inv) :
    ∀ oa : OracleComp spec α,
    ∀ s₀, Inv s₀ →
      ∀ z ∈ support (simulateQ impl oa).run, Inv (s₀ * z.2) := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s₀ hs₀ z hz
      obtain rfl : z = (a, (1 : ω)) := by simpa [simulateQ_pure, WriterT.run_pure] using hz
      simpa only [mul_one] using hs₀
  | query_bind t oa ih =>
      intro s₀ hs₀ z hz
      simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, support_bind,
        support_map, Set.mem_iUnion, Set.mem_image, Prod.exists, exists_prop] at hz
      obtain ⟨u, w, hus, v, w', hvs, rfl⟩ := hz
      simpa only [mul_assoc] using ih u (s₀ * w) (himpl t s₀ hs₀ (u, w) hus) (v, w') hvs

end OracleComp
