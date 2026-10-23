/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.GrowthCharge

/-!
# Replaying a run against its own final cache

This is the threading step the forgery decomposition needs, and the reason it is available
at all is that the scheme's operations are written against `[HasQuery HashSpec m]` for an
arbitrary monad: the extraction chain's `(m := Id)` statements hold for *any* hash function,
so they may be instantiated at the function the game itself produced.

`replay` turns a finished cache into such a function, and `run_eq_replay` says a hash-only
computation's oracle result is exactly what `replay` of the *final* cache computes. Both
directions of the threading follow: every value the verifier computed is reproduced by the
final cache, and every input it consulted is therefore present in that cache — which is what
`StructuralTerm.DeviatingCollision` and `GrowthCharge.Bad` quantify over.

The restriction to `OracleComp HashSpec` is essential rather than cosmetic. A computation that
also flips coins cannot be replayed from a cache, because the coins leave no trace in it; the
verifier is hash-only, which is why the statement is about it and not about the whole game.
-/

@[expose] public section

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.CacheReplay

/-- A finished cache, read as a total hash function. -/
def replay (cache : QueryCache HashSpec) : QueryImpl HashSpec Id :=
  fun input => ((cache input).getD default : Id HashOutput)

/-- The oracle step either returns a cached value and leaves the cache alone, or samples and
installs one. -/
theorem step_shape (input : Bytes) (initialCache : QueryCache HashSpec)
    (step : HashOutput × QueryCache HashSpec)
    (hstep : step ∈ support ((randomOracle input).run initialCache)) :
    step.2 = initialCache.cacheQuery input step.1 ∨ step.2 = initialCache := by
  cases hcached : initialCache input with
  | some cached =>
    right
    have hrun : (randomOracle input).run initialCache =
        (pure (cached, initialCache) :
          ProbComp (HashOutput × QueryCache HashSpec)) := by
      rw [QueryImpl.withCaching_run_some _ hcached]
    rw [hrun, support_pure, Set.mem_singleton_iff] at hstep
    exact congrArg Prod.snd hstep
  | none =>
    left
    have hrun : (randomOracle input).run initialCache =
        (fun value => (value, initialCache.cacheQuery input value)) <$>
          ($ᵗ HashOutput : ProbComp HashOutput) := by
      rw [QueryImpl.withCaching_run_none _ hcached]
      simp [uniformSampleImpl]
    rw [hrun, support_map] at hstep
    obtain ⟨value, -, hpair⟩ := hstep
    rw [← congrArg Prod.snd hpair, ← congrArg Prod.fst hpair]

/-- The step's answer is what its cache then holds. -/
theorem step_cached (input : Bytes) (initialCache : QueryCache HashSpec)
    (step : HashOutput × QueryCache HashSpec)
    (hstep : step ∈ support ((randomOracle input).run initialCache)) :
    step.2 input = some step.1 := by
  rcases step_shape input initialCache step hstep with hshape | hshape
  · rw [hshape, QueryCache.cacheQuery_self]
  · cases hcached : initialCache input with
    | some cached =>
      have hrun : (randomOracle input).run initialCache =
          (pure (cached, initialCache) :
            ProbComp (HashOutput × QueryCache HashSpec)) := by
        rw [QueryImpl.withCaching_run_some _ hcached]
      rw [hrun, support_pure, Set.mem_singleton_iff] at hstep
      rw [hshape, hcached, congrArg Prod.fst hstep]
    | none =>
      exfalso
      have hrun : (randomOracle input).run initialCache =
          (fun value => (value, initialCache.cacheQuery input value)) <$>
            ($ᵗ HashOutput : ProbComp HashOutput) := by
        rw [QueryImpl.withCaching_run_none _ hcached]
        simp [uniformSampleImpl]
      rw [hrun, support_map] at hstep
      obtain ⟨value, -, hpair⟩ := hstep
      have hcache : initialCache.cacheQuery input value = initialCache :=
        (congrArg Prod.snd hpair).trans hshape
      have := congrFun hcache input
      rw [QueryCache.cacheQuery_self, hcached] at this
      simp at this

/-- Entries already present persist through a hash-only run. -/
theorem cache_value_persists {α : Type} (computation : OracleComp HashSpec α)
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hmem : (result, finalCache) ∈
      support ((simulateQ randomOracle computation).run initialCache))
    (input : Bytes) (output : HashOutput) (hentry : initialCache input = some output) :
    finalCache input = some output := by
  induction computation using OracleComp.inductionOn generalizing initialCache result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    simp only [Prod.mk.injEq] at hmem
    obtain ⟨-, rfl⟩ := hmem
    exact hentry
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rcases eq_or_ne input queried with rfl | hne
    · -- The queried input was already present, so the step returns it unchanged.
      have hrun : (randomOracle input).run initialCache =
          (pure (output, initialCache) :
            ProbComp (HashOutput × QueryCache HashSpec)) := by
        rw [QueryImpl.withCaching_run_some _ hentry]
      rw [hrun, support_pure, Set.mem_singleton_iff] at hstep
      refine ih step.1 step.2 result hrest ?_
      rw [congrArg Prod.snd hstep]
      exact hentry
    · refine ih step.1 step.2 result hrest ?_
      rcases step_shape queried initialCache step hstep with hshape | hshape
      · rw [hshape, QueryCache.cacheQuery_of_ne initialCache step.1 hne]
        exact hentry
      · rw [hshape]
        exact hentry

/-- **A hash-only run is reproduced by its own final cache.** -/
theorem run_eq_replay {α : Type} (computation : OracleComp HashSpec α)
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hmem : (result, finalCache) ∈
      support ((simulateQ randomOracle computation).run initialCache)) :
    result = simulateQ (replay finalCache) computation := by
  induction computation using OracleComp.inductionOn generalizing initialCache result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    simp only [Prod.mk.injEq] at hmem
    obtain ⟨rfl, -⟩ := hmem
    rw [simulateQ_pure]
    rfl
  | query_bind input next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    have hfinal : finalCache input = some step.1 :=
      cache_value_persists (next step.1) step.2 finalCache result hrest input step.1
        (step_cached input initialCache step hstep)
    rw [ih step.1 step.2 result hrest, simulateQ_bind, simulateQ_spec_query]
    have hreplay : replay finalCache input = step.1 := by simp [replay, hfinal]
    rw [hreplay]
    rfl

/-! ## Reading the extraction chain's `Id`-level hashes out of the cache

The extraction chain states its collisions with `Hashing.tweakable (m := Id)`, under the
`[HasQuery HashSpec Id]` the development carries as a variable. `replayQuery` is the instance
that answers from a finished cache, and the two lemmas below say what that answers with: a
hash call is the cache's value, and a tweakable call is its truncation.

With these, every `Id`-level equation the extraction produces becomes a statement about cache
entries, which is what the structural charge quantifies over — so an accepted forgery's
collisions can be read off the cache the game itself left behind. -/

/-- The `HasQuery` instance that answers from a finished cache. -/
@[reducible] def replayQuery (cache : QueryCache HashSpec) : HasQuery HashSpec Id :=
  ⟨fun input => ((cache input).getD default : Id HashOutput)⟩

theorem hash_replayQuery (cache : QueryCache HashSpec) (input : Bytes) (output : HashOutput)
    (hentry : cache input = some output) :
    @Hashing.hash Id (replayQuery cache) input = output := by
  simp [Hashing.hash, hentry]

/-- A tweakable call reads the truncation of the cached answer at its own byte input. -/
theorem tweakable_replayQuery (cache : QueryCache HashSpec) (publicSeed : Digest)
    (address : Address) (payload : Bytes) (output : HashOutput)
    (hentry : cache (Hashing.tweakableInput publicSeed address payload) = some output) :
    @Hashing.tweakable Id _ (replayQuery cache) publicSeed address payload =
      Hashing.truncate output := by
  simp only [Hashing.tweakable, Hashing.shortHash, Hashing.hash
    ]
  simp [Functor.map, hentry]

/-- The same for a bare `shortHash`, which the FORS compression collision is stated with. -/
theorem shortHash_replayQuery (cache : QueryCache HashSpec) (input : Bytes)
    (output : HashOutput) (hentry : cache input = some output) :
    @Hashing.shortHash Id _ (replayQuery cache) input = Hashing.truncate output := by
  simp only [Hashing.shortHash, Hashing.hash]
  simp [Functor.map, hentry]

/-! ## Which inputs a replayed run has cached

`run_eq_replay` says what a run *computed*; the structural charge also needs to know that the
inputs it consulted are *present* in the cache, since `StructuralTerm.DeviatingCollision` and
`GrowthCharge.Bad` both quantify over cache entries. Value correspondence does not give that
on its own: `replay` answers `default` at an absent input, so an equation could in principle
hold with nothing cached.

`QueriesUnder` names the inputs a hash-only computation consults when its answers come from a
given cache — the head query of each bind, and then whatever the continuation consults once
that answer is fixed. `cached_of_queriesUnder` then says every such input really is in the
final cache. Together with `run_eq_replay` this is the full threading: the verifier's computed
values are cache values, and the inputs behind them are cache entries.
-/

/-- The inputs a hash-only computation consults when answered from `cache`. -/
inductive QueriesUnder (cache : QueryCache HashSpec) :
    {α : Type} → OracleComp HashSpec α → Bytes → Prop where
  | head {α : Type} (input : Bytes) (next : HashOutput → OracleComp HashSpec α) :
      QueriesUnder cache (query (spec := HashSpec) input >>= next) input
  | tail {α : Type} (input probe : Bytes) (next : HashOutput → OracleComp HashSpec α) :
      QueriesUnder cache (next (replay cache input)) probe →
        QueriesUnder cache (query (spec := HashSpec) input >>= next) probe

/-- **Every input a replayed run consults is in its final cache.** -/
theorem cached_of_queriesUnder {α : Type} (computation : OracleComp HashSpec α)
    (initialCache finalCache : QueryCache HashSpec) (result : α) (probe : Bytes)
    (hquery : QueriesUnder finalCache computation probe)
    (hmem : (result, finalCache) ∈
      support ((simulateQ randomOracle computation).run initialCache)) :
    finalCache probe ≠ none := by
  induction hquery generalizing initialCache result with
  | head input next =>
    rw [simulateQ_bind, show simulateQ randomOracle
        (query (spec := HashSpec) input) = randomOracle input from by simp,
      StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    have hentry : finalCache input = some step.1 :=
      cache_value_persists (next step.1) step.2 finalCache result hrest input step.1
        (step_cached input initialCache step hstep)
    rw [hentry]
    simp
  | tail input probe next _ ih =>
    rw [simulateQ_bind, show simulateQ randomOracle
        (query (spec := HashSpec) input) = randomOracle input from by simp,
      StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    -- The answer the run took is the one `replay` reproduces, so the continuations agree.
    have hentry : finalCache input = some step.1 :=
      cache_value_persists (next step.1) step.2 finalCache result hrest input step.1
        (step_cached input initialCache step hstep)
    have hreplay : replay finalCache input = step.1 := by simp [replay, hentry]
    exact ih step.2 result (by rw [hreplay]; exact hrest)

/-! ## Peeling a verification one call at a time

To use `cached_of_queriesUnder` on the verifier one has to show that a particular byte input
is among those it consults. The verifier is a fold of hash calls, so two closure properties
suffice: a hash call consults its own input, and anything the prefix of a bind consults the
whole bind consults too. Peeling a fold with these recovers each step's input in turn. -/

theorem queriesUnder_hash {α : Type} (cache : QueryCache HashSpec) (input : Bytes)
    (next : HashOutput → OracleComp HashSpec α) :
    QueriesUnder cache
      ((Hashing.hash (m := OracleComp HashSpec) input) >>= next) input :=
  QueriesUnder.head input next

/-- What a prefix consults, the whole computation consults. -/
theorem queriesUnder_bind {α β : Type} (cache : QueryCache HashSpec)
    (computation : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) (probe : Bytes)
    (hquery : QueriesUnder cache computation probe) :
    QueriesUnder cache (computation >>= next) probe := by
  induction hquery with
  | head input continuation =>
    rw [bind_assoc]
    exact QueriesUnder.head input _
  | tail input probe continuation _ ih =>
    rw [bind_assoc]
    exact QueriesUnder.tail input probe _ ih

/-- A `shortHash` consults its own input. -/
theorem queriesUnder_shortHash {α : Type} (cache : QueryCache HashSpec) (input : Bytes)
    (next : Digest → OracleComp HashSpec α) :
    QueriesUnder cache
      ((Hashing.shortHash (m := OracleComp HashSpec) input) >>= next) input := by
  rw [show (Hashing.shortHash (m := OracleComp HashSpec) input) >>= next =
      (Hashing.hash (m := OracleComp HashSpec) input) >>=
        (fun answer => next (Hashing.truncate answer)) from by
    simp [Hashing.shortHash]]
  exact queriesUnder_hash cache input _

/-- A tweakable call consults the byte input it is built from. -/
theorem queriesUnder_tweakable {α : Type} (cache : QueryCache HashSpec) (publicSeed : Digest)
    (address : Address) (payload : Bytes) (next : Digest → OracleComp HashSpec α) :
    QueriesUnder cache
      ((Hashing.tweakable (m := OracleComp HashSpec) publicSeed address payload) >>= next)
      (Hashing.tweakableInput publicSeed address payload) :=
  queriesUnder_shortHash cache _ next

/-! ## Peeling a fold

The closure lemmas above make each individual peel possible, but a verification step deep in a
fold needs the running value at that point, which under `replay` is determined. These two
lemmas are that walk: the head step consults its input at the fold's current value, and a step
in the tail is reached by advancing the value to the truncation of the replayed answer.

The truncation is where `shortHash` shows through: a tweakable call hashes and then keeps the
first sixteen bytes, so the value the fold carries forward is `Hashing.truncate` of the raw
oracle answer, not the answer itself. -/

theorem queriesUnder_foldlM_head {ι : Type} (cache : QueryCache HashSpec)
    (inputOf : Digest → ι → Bytes) (x : ι) (xs : List ι) (init : Digest) :
    QueriesUnder cache
      ((x :: xs).foldlM (m := OracleComp HashSpec)
        (fun value i => Hashing.shortHash (inputOf value i)) init)
      (inputOf init x) := by
  rw [List.foldlM_cons]
  exact queriesUnder_shortHash cache (inputOf init x) _

theorem queriesUnder_foldlM_tail {ι : Type} (cache : QueryCache HashSpec)
    (inputOf : Digest → ι → Bytes) (x : ι) (xs : List ι) (init : Digest) (probe : Bytes)
    (hquery : QueriesUnder cache
      (xs.foldlM (m := OracleComp HashSpec)
        (fun value i => Hashing.shortHash (inputOf value i))
        (Hashing.truncate (replay cache (inputOf init x)))) probe) :
    QueriesUnder cache
      ((x :: xs).foldlM (m := OracleComp HashSpec)
        (fun value i => Hashing.shortHash (inputOf value i)) init) probe := by
  rw [List.foldlM_cons,
    show (Hashing.shortHash (m := OracleComp HashSpec) (inputOf init x)) >>=
        (fun value => xs.foldlM (fun v i => Hashing.shortHash (inputOf v i)) value) =
      (Hashing.hash (m := OracleComp HashSpec) (inputOf init x)) >>=
        (fun answer => xs.foldlM (fun v i => Hashing.shortHash (inputOf v i))
          (Hashing.truncate answer)) from by simp [Hashing.shortHash]]
  exact QueriesUnder.tail (inputOf init x) probe _ hquery

/-! ## Peeling to arbitrary depth

The head and tail lemmas walk a fold one step at a time; this names where that walk arrives.
`replayFold` is the Id-level fold the oracle run is replayed as — each step advancing the
running value to the truncation of the cached answer — and `queriesUnder_foldlM_get` says the
`k`-th step of the fold consults its input at the value `replayFold` has reached after the
first `k`.

This is what makes the peeling usable on the verifier, whose Merkle path is a fold of
`subtreeHeight` steps and whose collision sits at an arbitrary one of them. -/

/-- The Id-level fold a replayed hash-fold performs. -/
def replayFold {ι : Type} (cache : QueryCache HashSpec) (inputOf : Digest → ι → Bytes) :
    List ι → Digest → Digest
  | [], value => value
  | x :: xs, value =>
      replayFold cache inputOf xs (Hashing.truncate (replay cache (inputOf value x)))

/-- **The `k`-th step of a fold consults its input at the replayed running value.** -/
theorem queriesUnder_foldlM_get {ι : Type} (cache : QueryCache HashSpec)
    (inputOf : Digest → ι → Bytes) :
    ∀ (xs : List ι) (init : Digest) (k : Nat) (hk : k < xs.length),
      QueriesUnder cache
        (xs.foldlM (m := OracleComp HashSpec)
          (fun value i => Hashing.shortHash (inputOf value i)) init)
        (inputOf (replayFold cache inputOf (xs.take k) init) xs[k]) := by
  intro xs
  induction xs with
  | nil => intro _ k hk; exact absurd hk (by simp)
  | cons x rest ih =>
    intro init k hk
    cases k with
    | zero =>
      simpa [replayFold] using queriesUnder_foldlM_head cache inputOf x rest init
    | succ k =>
      refine queriesUnder_foldlM_tail cache inputOf x rest init _ ?_
      have hrest : k < rest.length := by simpa using hk
      simpa [replayFold] using ih (Hashing.truncate (replay cache (inputOf init x))) k hrest

/-- `replayFold` is an ordinary left fold, which is the vocabulary the extraction speaks:
`Extraction.BinaryPath.value_eq_fold` identifies exactly such a fold with
`Extraction.BinaryPath.value`, so the running value `queriesUnder_foldlM_get` names is the one
the collision is stated about. -/
theorem replayFold_eq_foldl {ι : Type} (cache : QueryCache HashSpec)
    (inputOf : Digest → ι → Bytes) (xs : List ι) (init : Digest) :
    replayFold cache inputOf xs init =
      xs.foldl (fun value x => Hashing.truncate (replay cache (inputOf value x))) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x rest ih => exact ih _

/-- The step `replayFold` takes is a tweakable call answered from the cache — the form
`Extraction.BinaryPath.value`'s `combine` has when the extraction is instantiated at
`replayQuery`. -/
theorem replayFold_step_eq_tweakable (cache : QueryCache HashSpec) (publicSeed : Digest)
    (address : Address) (payload : Bytes) :
    Hashing.truncate (replay cache (Hashing.tweakableInput publicSeed address payload)) =
      @Hashing.tweakable Id _ (replayQuery cache) publicSeed address payload := by
  simp [Hashing.tweakable, Hashing.shortHash, Hashing.hash, replay, Functor.map]

/-! ## Matching the two folds' index types

`queriesUnder_foldlM_get` arrives at a value folded over `(List.finRange n).take k`, whose
elements are `Fin n`, while `Extraction.BinaryPath.value` recurses on a bare `Nat` height and
`value_eq_fold` folds over `List.finRange k`, whose elements are `Fin k`. The two lists carry
different types but the same indices, and every step here uses only `Fin.val`, so the folds
agree once both are pushed through to `List.range`. -/

theorem foldl_finRange_take {α : Type} (n k : Nat) (hk : k ≤ n) (step : α → Nat → α)
    (init : α) :
    (((List.finRange n).take k).foldl (fun value j => step value j.val) init) =
      ((List.finRange k).foldl (fun value j => step value j.val) init) := by
  rw [← List.foldl_map (f := Fin.val) (g := step),
    ← List.foldl_map (f := Fin.val) (g := step), List.map_take,
    List.map_coe_finRange_eq_range, List.map_coe_finRange_eq_range, List.take_range,
    Nat.min_eq_left hk]

/-! ## Reaching a call that comes after a prefix

`queriesUnder_bind` goes into a bind's prefix. The two compression nodes sit the other way
round: their hash is the last call, after the chains or the trees have been computed. Reaching
it needs the opposite direction — what the continuation consults once the prefix has run, the
whole bind consults — and the prefix's result under replay is exactly `simulateQ (replay cache)`
applied to it, which is what `run_eq_replay` identifies with the oracle run's result.

So this closes the remaining direction, and with it any call in a hash-only computation is
reachable: `queriesUnder_bind` to descend into a prefix, this to step over one. -/

theorem queriesUnder_bind_right {α β : Type} (cache : QueryCache HashSpec)
    (computation : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) (probe : Bytes)
    (hquery : QueriesUnder cache (next (simulateQ (replay cache) computation)) probe) :
    QueriesUnder cache (computation >>= next) probe := by
  induction computation using OracleComp.inductionOn generalizing probe with
  | pure value =>
    rw [pure_bind]
    rwa [simulateQ_pure] at hquery
  | query_bind input continuation ih =>
    rw [show (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput) >>= continuation =
        query (spec := HashSpec) input >>= continuation from rfl, bind_assoc]
    refine QueriesUnder.tail input probe _ (ih (replay cache input) probe ?_)
    rw [show simulateQ (replay cache)
        ((liftM (HashSpec.query input) : OracleComp HashSpec HashOutput) >>= continuation) =
          simulateQ (replay cache) (continuation (replay cache input)) from by
      rw [simulateQ_bind, simulateQ_spec_query]; rfl] at hquery
    exact hquery

/-- A tweakable call on its own consults its byte input — the compression nodes end their
computation with exactly this, with nothing bound after. -/
theorem queriesUnder_tweakable_self (cache : QueryCache HashSpec) (publicSeed : Digest)
    (address : Address) (payload : Bytes) :
    QueriesUnder cache
      (Hashing.tweakable (m := OracleComp HashSpec) publicSeed address payload)
      (Hashing.tweakableInput publicSeed address payload) := by
  rw [show (Hashing.tweakable (m := OracleComp HashSpec) publicSeed address payload) =
      (Hashing.hash (m := OracleComp HashSpec)
        (Hashing.tweakableInput publicSeed address payload)) >>=
        (fun answer => pure (Hashing.truncate answer)) from rfl]
  exact QueriesUnder.head _ _

/-- **A compression node consults its own input.** Both compression nodes of the scheme have
this shape: run a prefix, then hash one payload built from its result. The payload is
determined by the prefix's replayed result, so nothing about the prefix's internals is
needed — those are the business of the prefix's own entry lemma. -/
theorem queriesUnder_compression {α : Type} (cache : QueryCache HashSpec)
    (prefixComputation : OracleComp HashSpec α) (publicSeed : Digest) (address : Address)
    (payloadOf : α → Bytes) :
    QueriesUnder cache
      (prefixComputation >>= fun result =>
        Hashing.tweakable (m := OracleComp HashSpec) publicSeed address (payloadOf result))
      (Hashing.tweakableInput publicSeed address
        (payloadOf (simulateQ (replay cache) prefixComputation))) :=
  queriesUnder_bind_right cache prefixComputation _ _
    (queriesUnder_tweakable_self cache publicSeed address _)

/-! ## A replay reads the cache only where it asks

`QueriesUnder` names the inputs a replayed run consults. This is the other half of what that
naming is for: the run's value depends on the cache **only** through those inputs, so two caches
agreeing there give the same value.

It is the fact a quantity recomputed at a different cache needs. `cached_of_queriesUnder` and
its handler-side twin say every such input is in the run's own cache; this says that is enough.
Between them, a replay at a smaller cache and a replay at a larger one that extends it agree,
without any statement about what the larger one holds elsewhere. -/

/-- **A replay is determined by the cache on the inputs it asks.** -/
theorem simulateQ_replay_congr {α : Type} (computation : OracleComp HashSpec α) :
    ∀ (left right : QueryCache HashSpec),
      (∀ probe : Bytes, QueriesUnder left computation probe → left probe = right probe) →
        (simulateQ (replay left) computation : Id α) =
          (simulateQ (replay right) computation : Id α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => intro left right _; rfl
  | query_bind input next ih =>
    intro left right hagree
    have hhead : left input = right input :=
      hagree input (QueriesUnder.head (cache := left) input next)
    have hanswer : replay left input = replay right input := by
      rw [replay, replay, hhead]
    show (simulateQ (replay left) (next (replay left input)) : Id α) =
      (simulateQ (replay right) (next (replay right input)) : Id α)
    rw [← hanswer]
    exact ih (replay left input) left right fun probe hprobe =>
      hagree probe (QueriesUnder.tail input probe next hprobe)

end SlhDsaSecurity.CacheReplay
