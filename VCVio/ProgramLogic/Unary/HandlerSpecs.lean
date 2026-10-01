/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Unary.SimulateQSpecs
public import VCVio.OracleComp.QueryTracking.CachingLoggingOracle
public import VCVio.OracleComp.QueryTracking.CachingOracle
public import VCVio.OracleComp.QueryTracking.CountingOracle.Core
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.SeededOracle

/-!
# Handler specifications for `OracleComp` simulators

Core `Std.WP` Hoare triples for the query-tracking handlers `cachingOracle`, `seededOracle`,
`loggingOracle`, `countingOracle`, `costOracle`, and `cachingLoggingOracle`, under the
necessary reading of `OracleComp` (the global instance): a triple
`⦃ pre ⦄ handler t ⦃ post ⦄` says that from every state satisfying `pre`, every reachable
result and final state satisfy `post`. Core's `StateT` interpretation lifts the structural
reading to the stateful handlers. The writer handlers read their log as accumulated state:
`WriterT.MonoidWP` for the monoid logs of `countingOracle` and `costOracle`, and
`WriterT.AppendWP` for the list log of `loggingOracle`.

## Proof style

* *Per-query specifications* are proved by core's `vcgen`, which walks each handler body
  (`get`, `match`, the underlying query, `modifyGet`, `tell`) with the query rules of
  `VCVio.ProgramLogic.Unary.WP.Necessary` and core's transformer rules. The verification
  conditions it leaves are first-order facts about caches, seeds, logs, and counts, closed by
  `grind`. Specifications with a single canonical postcondition are `@[spec]`-tagged.
* *Composite programs* are handled by `vcgen` from the per-query specifications: the worked
  examples below compose two-, three-, and four-query bind chains.
* *Whole simulations* go through the generic layer `VCVio.ProgramLogic.Unary.SimulateQSpecs`:
  `Spec.simulateQ` with a handler invariant, the whole-program lifts
  `simulateQ_triple_preserves_invariant` and their `WriterT` analogues, the ranked
  `simulateQ_triple_ranked`, the sum-handler rules and the readings of a triple against the
  support of its run.

## Ghost parameters

Most specifications fix the incoming state through an equational precondition
(`seed = seed₀`, `log = log₀`), and `vcgen` instantiates the ghost value by unification when it
composes calls. `cachingOracle_triple` and `cachingLoggingOracle_triple` bound the incoming
cache from below (`cache₀ ≤ cache`), which leaves `cache₀` undetermined at a call site, so
compositions instantiate it explicitly, as in `vcgen [cachingOracle_triple _ cache₀]`.

## Stacked handlers

`cachingLoggingOracle` keeps a cache and a log in a single
`StateT (QueryCache spec × QueryLog spec)` layer. Its per-query specification is the
conjunction of the cache invariant and the log invariant, and
`simulateQ_triple_preserves_invariant` lifts each component invariant to whole simulations.
The product-state representation matches the Fiat-Shamir and forking proofs in
`VCVio/CryptoFoundations`.

## Limitations

* `seededOracle` is defined with `StateT.mk`, for which core registers no `vcgen` rule;
  `Std.WP.Spec.mk_StateT` supplies it.
* `seededOracle_triple_of_cons` and `seededOracle_triple_of_nil` are not `@[spec]`-tagged.
  `vcgen` applies the highest-priority registered rule that fits a program, and these rules
  fit every call of `seededOracle` while holding only under their seed hypothesis, so
  compositions pass them explicitly (`vcgen [seededOracle_triple_of_nil]`).
-/

@[expose] public section

open OracleSpec OracleComp Std.WP

open scoped WriterT.MonoidWP WriterT.AppendWP

namespace OracleComp.ProgramLogic

/- The handlers' state types (caches, seeds, logs, counts) live in `Type (max u v)` for
`spec : OracleSpec.{u, v} ι`, and `StateT` / `WriterT` over `OracleComp spec : Type v → Type _`
needs them in `Type v`; both universes are pinned to `Type`. -/
variable {ι : Type}
variable {spec : OracleSpec.{0, 0} ι}


section cachingOracle

variable [DecidableEq ι]

/-- Cache-monotonicity specification for `cachingOracle t`: if the cache on entry is
`≥ cache₀`, then after a single call the updated cache is still `≥ cache₀` and contains the
returned value at key `t`. -/
@[spec]
theorem cachingOracle_triple (t : spec.Domain) (cache₀ : QueryCache spec) :
    ⦃ fun cache => cache₀ ≤ cache ⦄
      (cachingOracle t : StateT (QueryCache spec) (OracleComp spec) (spec.Range t))
    ⦃ fun v cache' => cache₀ ≤ cache' ∧ cache' t = some v ⦄ := by
  rw [cachingOracle.apply_eq]
  vcgen with finish

/-- `vcgen` example: two sequential `cachingOracle` queries preserve cache monotonicity. The
ghost cache `cache₀` is instantiated once for both calls. -/
example (t₁ t₂ : spec.Domain) (cache₀ : QueryCache spec) :
    ⦃ fun cache => cache₀ ≤ cache ⦄
      (do let _ ← cachingOracle t₁; cachingOracle t₂ :
        StateT (QueryCache spec) (OracleComp spec) (spec.Range t₂))
    ⦃ fun v cache' => cache₀ ≤ cache' ∧ cache' t₂ = some v ⦄ := by
  vcgen [cachingOracle_triple _ cache₀] with finish

/-- `vcgen` example: a three-query `cachingOracle` block preserves cache monotonicity. -/
example (t₁ t₂ t₃ : spec.Domain) (cache₀ : QueryCache spec) :
    ⦃ fun cache => cache₀ ≤ cache ⦄
      (do
        let _ ← cachingOracle t₁
        let _ ← cachingOracle t₂
        cachingOracle t₃ :
        StateT (QueryCache spec) (OracleComp spec) (spec.Range t₃))
    ⦃ fun v cache' => cache₀ ≤ cache' ∧ cache' t₃ = some v ⦄ := by
  vcgen [cachingOracle_triple _ cache₀] with finish

/-- `vcgen` example: a four-query `cachingOracle` block preserves cache monotonicity. The chain
length does not change the proof: `vcgen` walks the bind tree and `grind` closes the
remaining conditions. -/
example (t₁ t₂ t₃ t₄ : spec.Domain) (cache₀ : QueryCache spec) :
    ⦃ fun cache => cache₀ ≤ cache ⦄
      (do
        let _ ← cachingOracle t₁
        let _ ← cachingOracle t₂
        let _ ← cachingOracle t₃
        cachingOracle t₄ :
        StateT (QueryCache spec) (OracleComp spec) (spec.Range t₄))
    ⦃ fun v cache' => cache₀ ≤ cache' ∧ cache' t₄ = some v ⦄ := by
  vcgen [cachingOracle_triple _ cache₀] with finish

/-- Global cache monotonicity for `simulateQ cachingOracle`: an arbitrary `OracleComp`
simulated under caching never shrinks the cache. Derived via the generic
`simulateQ_triple_preserves_invariant`. -/
theorem simulateQ_cachingOracle_preserves_cache_le {α : Type}
    (cache₀ : QueryCache spec) (oa : OracleComp spec α) :
    ⦃ fun cache => cache₀ ≤ cache ⦄
      (simulateQ cachingOracle oa : StateT (QueryCache spec) (OracleComp spec) α)
    ⦃ fun _ cache' => cache₀ ≤ cache' ⦄ :=
  simulateQ_triple_preserves_invariant cachingOracle (fun cache => cache₀ ≤ cache)
    (fun t => by vcgen [cachingOracle_triple t cache₀] with finish) oa

end cachingOracle

section seededOracle

variable [DecidableEq ι]

/-- Specification for `seededOracle t`: the call consumes at most one value at index `t`.
Either the seed was empty at `t` (state unchanged, returned value fresh) or the seed started
with a value `v` at `t` that is returned and popped from the state. -/
@[spec]
theorem seededOracle_triple (t : spec.Domain) (seed₀ : QuerySeed spec) :
    ⦃ fun seed => seed = seed₀ ⦄
      (seededOracle t : StateT (QuerySeed spec) (OracleComp spec) (spec.Range t))
    ⦃ fun v seed' => (seed₀ t = [] ∧ seed' = seed₀) ∨
        ∃ us, seed₀ t = v :: us ∧ seed' = Function.update seed₀ t us ⦄ := by
  rw [seededOracle.apply_eq]
  vcgen <;> grind [QuerySeed.update]

/-- Specialized specification: if the seed has at least one value at `t`, `seededOracle t`
deterministically pops the head and updates the state. -/
theorem seededOracle_triple_of_cons (t : spec.Domain)
    (u : spec.Range t) (us : List (spec.Range t)) (seed₀ : QuerySeed spec)
    (h : seed₀ t = u :: us) :
    ⦃ fun seed => seed = seed₀ ⦄
      (seededOracle t : StateT (QuerySeed spec) (OracleComp spec) (spec.Range t))
    ⦃ fun v seed' => v = u ∧ seed' = seed₀.update t us ⦄ := by
  rw [seededOracle.apply_eq]
  vcgen with finish

/-- Specialized specification: if the seed is empty at `t`, `seededOracle t` makes a live
query and leaves the state untouched. -/
theorem seededOracle_triple_of_nil (t : spec.Domain) (seed₀ : QuerySeed spec)
    (h : seed₀ t = []) :
    ⦃ fun seed => seed = seed₀ ⦄
      (seededOracle t : StateT (QuerySeed spec) (OracleComp spec) (spec.Range t))
    ⦃ fun _ seed' => seed' = seed₀ ⦄ := by
  rw [seededOracle.apply_eq]
  vcgen with finish

/-- `vcgen` example: two consecutive `seededOracle` calls from a seed that is empty at both
indices fall through to live queries, leaving the seed unchanged. The two hypotheses on the
seed discharge the side conditions of `seededOracle_triple_of_nil`. -/
example (t₁ t₂ : spec.Domain) (seed₀ : QuerySeed spec)
    (h₁ : seed₀ t₁ = []) (h₂ : seed₀ t₂ = []) :
    ⦃ fun seed => seed = seed₀ ⦄
      (do let _ ← seededOracle t₁; seededOracle t₂ :
        StateT (QuerySeed spec) (OracleComp spec) (spec.Range t₂))
    ⦃ fun _ seed' => seed' = seed₀ ⦄ := by
  vcgen [seededOracle_triple_of_nil] with finish

end seededOracle

section loggingOracle

/-- Specification for `loggingOracle t` over `WriterT (QueryLog spec) (OracleComp spec)`: the
log accumulates the query / response pair `⟨t, v⟩`. -/
@[spec]
theorem loggingOracle_triple (t : spec.Domain) (log₀ : QueryLog spec) :
    ⦃ fun log => log = log₀ ⦄
      (loggingOracle t : WriterT (QueryLog spec) (OracleComp spec) (spec.Range t))
    ⦃ fun v log' => log' = log₀ ++ [⟨t, v⟩] ⦄ := by
  vcgen [loggingOracle, QueryImpl.withLogging_apply, QueryImpl.ofLift_apply] with finish

/-- Log monotonicity: the log only grows, as a list prefix. -/
theorem loggingOracle_triple_prefix (t : spec.Domain) (log₀ : QueryLog spec) :
    ⦃ fun log => log = log₀ ⦄
      (loggingOracle t : WriterT (QueryLog spec) (OracleComp spec) (spec.Range t))
    ⦃ fun _ log' => log₀ <+: log' ⦄ := by
  vcgen [loggingOracle_triple] with finish

/-- `vcgen` example: two consecutive logged queries extend the log with both entries in
order. -/
example (t₁ t₂ : spec.Domain) (log₀ : QueryLog spec) :
    ⦃ fun log => log = log₀ ⦄
      (do let u₁ ← loggingOracle t₁; let u₂ ← loggingOracle t₂; pure (u₁, u₂) :
        WriterT (QueryLog spec) (OracleComp spec) (spec.Range t₁ × spec.Range t₂))
    ⦃ fun p log' => log' = log₀ ++ [⟨t₁, p.1⟩, ⟨t₂, p.2⟩] ⦄ := by
  vcgen [loggingOracle_triple] with finish

end loggingOracle

section countingOracle

variable [DecidableEq ι]

/-- A counting query adds one at its index. The writer log uses Mathlib's multiplicative tag,
and the predicates observe the additive count through `toAdd`. -/
@[spec]
theorem countingOracle_triple (t : spec.Domain) (qc₀ : QueryCount ι) :
    ⦃ fun qc => Multiplicative.toAdd qc = qc₀ ⦄
      (countingOracle t : AddWriterT (QueryCount ι) (OracleComp spec) (spec.Range t))
    ⦃ fun _ qc' => Multiplicative.toAdd qc' = qc₀ + QueryCount.single t ⦄ := by
  vcgen [countingOracle_apply, AddWriterT.addTell]
  grind [toAdd_mul, toAdd_ofAdd]

/-- `vcgen` example: two consecutive `countingOracle` calls increment the count by
`QueryCount.single t₁ + QueryCount.single t₂`, in that order. -/
example (t₁ t₂ : spec.Domain) (qc₀ : QueryCount ι) :
    ⦃ fun qc => Multiplicative.toAdd qc = qc₀ ⦄
      (do let _ ← countingOracle t₁; countingOracle t₂ :
        AddWriterT (QueryCount ι) (OracleComp spec) (spec.Range t₂))
    ⦃ fun _ qc' =>
        Multiplicative.toAdd qc' = qc₀ + QueryCount.single t₁ + QueryCount.single t₂ ⦄ := by
  vcgen [countingOracle_triple] with finish

/-- Whole-program monotonicity for `countingOracle`: the accumulated query count under
`simulateQ countingOracle oa` only grows. Derived from the generic
`simulateQ_writerT_triple_preserves_invariant` with invariant `I qc := qc₀ ≤ qc`. -/
theorem simulateQ_countingOracle_preserves_le {α : Type}
    (qc₀ : QueryCount ι) (oa : OracleComp spec α) :
    ⦃ fun qc => qc₀ ≤ Multiplicative.toAdd qc ⦄
      (simulateQ countingOracle oa : AddWriterT (QueryCount ι) (OracleComp spec) α)
    ⦃ fun _ qc' => qc₀ ≤ Multiplicative.toAdd qc' ⦄ :=
  simulateQ_writerT_triple_preserves_invariant countingOracle
    (fun qc => qc₀ ≤ Multiplicative.toAdd qc) (fun t => by
      vcgen [countingOracle_triple]
      rename_i hle _ _ hqc
      exact hqc ▸ le_add_right hle) oa

end countingOracle

section costOracle

variable {ω : Type} [Monoid ω]

/-- Specification for `costOracle costFn t` over `WriterT ω (OracleComp spec)`: the cost
accumulates by exactly `costFn t`. Generalizes `countingOracle_triple` to arbitrary monoidal
cost functions. -/
@[spec]
theorem costOracle_triple (costFn : spec.Domain → ω) (t : spec.Domain) (s₀ : ω) :
    ⦃ fun s => s = s₀ ⦄
      (costOracle costFn t : WriterT ω (OracleComp spec) (spec.Range t))
    ⦃ fun _ s' => s' = s₀ * costFn t ⦄ := by
  vcgen [costOracle_apply] with finish

/-- `vcgen` example: two consecutive `costOracle` calls accumulate costs
`costFn t₁ * costFn t₂` in order. -/
example (costFn : spec.Domain → ω) (t₁ t₂ : spec.Domain) (s₀ : ω) :
    ⦃ fun s => s = s₀ ⦄
      (do let _ ← costOracle costFn t₁; costOracle costFn t₂ :
        WriterT ω (OracleComp spec) (spec.Range t₂))
    ⦃ fun _ s' => s' = s₀ * costFn t₁ * costFn t₂ ⦄ := by
  vcgen [costOracle_triple] with finish

/-- Whole-program submonoid closure for `costOracle`: if `costFn t ∈ S` for every query `t`,
then the accumulated cost of `simulateQ (costOracle costFn) oa` stays in `S` starting from any
`s₀ ∈ S`. Derived from the generic `simulateQ_writerT_triple_preserves_invariant` with
`I s := s ∈ S`. -/
theorem simulateQ_costOracle_preserves_submonoid {α : Type}
    (costFn : spec.Domain → ω) (S : Submonoid ω)
    (hcost : ∀ t, costFn t ∈ S)
    (oa : OracleComp spec α) :
    ⦃ fun s => s ∈ S ⦄
      (simulateQ (costOracle costFn) oa : WriterT ω (OracleComp spec) α)
    ⦃ fun _ s' => s' ∈ S ⦄ :=
  simulateQ_writerT_triple_preserves_invariant (costOracle costFn) (fun s => s ∈ S)
    (fun t => by
      vcgen [costOracle_triple]
      rename_i hs _ _ hs'
      exact hs' ▸ S.mul_mem hs (hcost t)) oa

end costOracle

/-! ## Stacked handlers

`cachingLoggingOracle` combines two state-tracking handlers in one
`StateT (QueryCache spec × QueryLog spec)` layer: on every query it logs the query / response
pair in the right component and caches the response in the left component, querying the
underlying oracle only on a cache miss. Its per-query specification is the conjunction of the
cache invariant (`cache₀ ≤ cache' ∧ cache' t = some v`) and the log invariant
(`log' = log₀ ++ [⟨t, v⟩]`); `vcgen` composes it exactly as it composes the single-state
handlers. -/

section stackedHandlers

variable [DecidableEq ι]

/-- Per-call specification for `cachingLoggingOracle t`: the log is extended by exactly one
entry `⟨t, v⟩`, the cache only grows, and the returned value is now cached at `t`. -/
@[spec]
theorem cachingLoggingOracle_triple
    (t : spec.Domain) (cache₀ : QueryCache spec) (log₀ : QueryLog spec) :
    ⦃ fun s => cache₀ ≤ s.1 ∧ s.2 = log₀ ⦄
      (cachingLoggingOracle t :
        StateT (QueryCache spec × QueryLog spec) (OracleComp spec) (spec.Range t))
    ⦃ fun v s' => cache₀ ≤ s'.1 ∧ s'.1 t = some v ∧ s'.2 = log₀ ++ [⟨t, v⟩] ⦄ := by
  rw [cachingLoggingOracle.apply_eq]
  vcgen with finish

/-- `vcgen` example: two consecutive `cachingLoggingOracle` calls extend the log with both
query / response entries in order, while the cache continues to grow monotonically. -/
example (t₁ t₂ : spec.Domain)
    (cache₀ : QueryCache spec) (log₀ : QueryLog spec) :
    ⦃ fun s => cache₀ ≤ s.1 ∧ s.2 = log₀ ⦄
      (do
        let v₁ ← cachingLoggingOracle t₁
        let v₂ ← cachingLoggingOracle t₂
        pure (v₁, v₂) :
        StateT (QueryCache spec × QueryLog spec) (OracleComp spec)
          (spec.Range t₁ × spec.Range t₂))
    ⦃ fun p s' => cache₀ ≤ s'.1 ∧ s'.2 = log₀ ++ [⟨t₁, p.1⟩, ⟨t₂, p.2⟩] ⦄ := by
  vcgen [cachingLoggingOracle_triple _ cache₀] with finish

/-- Whole-program lift: `simulateQ cachingLoggingOracle oa` preserves cache monotonicity for any
`oa`. Derived via the generic `simulateQ_triple_preserves_invariant`. -/
theorem simulateQ_cachingLoggingOracle_preserves_cache_le {α : Type}
    (cache₀ : QueryCache spec) (oa : OracleComp spec α) :
    ⦃ fun s => cache₀ ≤ s.1 ⦄
      (simulateQ cachingLoggingOracle oa :
        StateT (QueryCache spec × QueryLog spec) (OracleComp spec) α)
    ⦃ fun _ s' => cache₀ ≤ s'.1 ⦄ :=
  simulateQ_triple_preserves_invariant cachingLoggingOracle (fun s => cache₀ ≤ s.1)
    (fun t => by vcgen [cachingLoggingOracle_triple t cache₀] with finish) oa

/-- Whole-program lift: `simulateQ cachingLoggingOracle oa` preserves the log-prefix invariant
(the log only grows). The cache bound of `cachingLoggingOracle_triple` is instantiated at the
empty cache `⊥`, which bounds every cache. -/
theorem simulateQ_cachingLoggingOracle_preserves_log_prefix {α : Type}
    (log₀ : QueryLog spec) (oa : OracleComp spec α) :
    ⦃ fun s => log₀ <+: s.2 ⦄
      (simulateQ cachingLoggingOracle oa :
        StateT (QueryCache spec × QueryLog spec) (OracleComp spec) α)
    ⦃ fun _ s' => log₀ <+: s'.2 ⦄ :=
  simulateQ_triple_preserves_invariant cachingLoggingOracle (fun s => log₀ <+: s.2)
    (fun t => by vcgen [cachingLoggingOracle_triple t ⊥] <;> grind [bot_le]) oa

end stackedHandlers

end OracleComp.ProgramLogic
