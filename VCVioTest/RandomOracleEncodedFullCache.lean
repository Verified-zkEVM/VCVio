/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Encoded

/-!
# Ordinary consumers of full-cache encoded-oracle transport

The full raw reply and its cache remain together through adaptive and repeated queries.
-/

public section

namespace EncodedFullConsumer

open OracleComp OracleSpec

/-- Two reads keep the full reply, including the part omitted by a typed answer. -/
def repeatedRaw {ι D M : Type} (spec : OracleSpec ι) (input : D) :
    OracleComp (unifSpec + (spec + (D →ₒ M))) (M × M) := do
  let first ← query (spec := unifSpec + (spec + (D →ₒ M))) (.inr (.inr input))
  let second ← query (spec := unifSpec + (spec + (D →ₒ M))) (.inr (.inr input))
  pure (first, second)

/-- Each next query may depend on the full reply of the preceding query. -/
def adaptive {ι D M α : Type} (spec : OracleSpec ι) (first : ι)
    (rawInput : spec.Range first → D) (nextPoint : M → ι)
    (continuation : (word : M) → spec.Range (nextPoint word) →
      OracleComp (unifSpec + (spec + (D →ₒ M))) α) :
    OracleComp (unifSpec + (spec + (D →ₒ M))) α := do
  let answer ← query (spec := unifSpec + (spec + (D →ₒ M))) (.inr (.inl first))
  let word ← query (spec := unifSpec + (spec + (D →ₒ M))) (.inr (.inr (rawInput answer)))
  let next ← query (spec := unifSpec + (spec + (D →ₒ M))) (.inr (.inl (nextPoint word)))
  continuation word next

/-- A typed answer is followed by the full raw reply at that same encoded point. -/
def typedThenRaw {ι D M : Type} {spec : OracleSpec ι} [SampleableType M]
    [∀ point, SampleableType (spec.Range point)] (E : RandomOracleEncoding spec D M)
    (point : ι) : OracleComp (unifSpec + (spec + (D →ₒ M))) (spec.Range point × M) := do
  let answer ← query (spec := unifSpec + (spec + (D →ₒ M))) (.inr (.inl point))
  let word ← query (spec := unifSpec + (spec + (D →ₒ M))) (.inr (.inr (E.encode point)))
  pure (answer, word)

variable {ι D M : Type} {spec : OracleSpec ι} [DecidableEq ι] [DecidableEq D]
  [SampleableType M] [∀ point, SampleableType (spec.Range point)]
  (E : RandomOracleEncoding spec D M)

omit [DecidableEq ι] in
/-- A repeated raw query has one sampled full reply and one matching final cache cell. -/
theorem repeatedRaw_single (input : D) :
    (simulateQ E.singleImpl (repeatedRaw spec input)).run ∅ = (do
      let word ← $ᵗ M
      pure ((word, word), (∅ : (D →ₒ M).QueryCache).cacheQuery input word)) := by
  simp [repeatedRaw, simulateQ_bind, StateT.run_bind,
    RandomOracleEncoding.singleImpl, RandomOracleEncoding.singleHashImpl,
    QueryImpl.add_apply_inr]

/-- Completion keeps the repeated full reply correlated with the filled cache. -/
theorem repeatedRaw_typed_filled (injective : Function.Injective E.encode) (input : D) :
    (do
      let z ← (simulateQ E.typedImpl (repeatedRaw spec input)).run (∅, ∅)
      let fullCache ← E.fill z.2
      pure (z.1, fullCache)) =ᵈ (do
      let word ← $ᵗ M
      pure ((word, word), (∅ : (D →ₒ M).QueryCache).cacheQuery input word)) := by
  exact (E.singleImpl_run_evalDistEq_typedImpl_fill_of_injective injective
    (repeatedRaw spec input)).symm.trans (by rw [repeatedRaw_single E input])

omit [DecidableEq ι] in
/-- The raw reply retains the tail correlated with the typed answer at the same point. -/
theorem typedThenRaw_single (point : ι) :
    (simulateQ E.singleImpl (typedThenRaw E point)).run ∅ = (do
      let word ← $ᵗ M
      pure ((E.trunc point word, word),
        (∅ : (D →ₒ M).QueryCache).cacheQuery (E.encode point) word)) := by
  simp [typedThenRaw, simulateQ_bind, StateT.run_bind,
    RandomOracleEncoding.singleImpl, RandomOracleEncoding.singleHashImpl,
    RandomOracleEncoding.truncatedImpl, StateT.run_map, bind_map_left]

/-- Filling a typed execution restores the same full reply, rather than an unrelated tail. -/
theorem typedThenRaw_typed_filled (injective : Function.Injective E.encode) (point : ι) :
    (do
      let z ← (simulateQ E.typedImpl (typedThenRaw E point)).run (∅, ∅)
      let fullCache ← E.fill z.2
      pure (z.1, fullCache)) =ᵈ (do
      let word ← $ᵗ M
      pure ((E.trunc point word, word),
        (∅ : (D →ₒ M).QueryCache).cacheQuery (E.encode point) word)) := by
  exact (E.singleImpl_run_evalDistEq_typedImpl_fill_of_injective injective
    (typedThenRaw E point)).symm.trans (by rw [typedThenRaw_single E point])

/-- Adaptive queries and an arbitrary continuation keep their complete joint endpoint. -/
theorem adaptive_joint (injective : Function.Injective E.encode) {α : Type} (first : ι)
    (rawInput : spec.Range first → D) (nextPoint : M → ι)
    (continuation : (word : M) → spec.Range (nextPoint word) →
      OracleComp (unifSpec + (spec + (D →ₒ M))) α) :
    (simulateQ E.singleImpl (adaptive spec first rawInput nextPoint continuation)).run ∅ =ᵈ (do
      let z ← (simulateQ E.typedImpl (adaptive spec first rawInput nextPoint continuation)).run
        (∅, ∅)
      let fullCache ← E.fill z.2
      pure (z.1, fullCache)) :=
  E.singleImpl_run_evalDistEq_typedImpl_fill_of_injective injective _


end EncodedFullConsumer
