/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CachedRun
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Correspondence
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Programming
public import HashSig.SLHDSA.SHAKE128s.Proof.Correctness.Naturality
public import HashSig.SLHDSA.SHAKE128s.Proof.KeygenFresh

/-!
# Key generation consults only canonical inputs

`CacheReplay.QueriesUnder` exhibits an input a computation consults. Bounding *every* input it
consults needs the opposite reading: an inversion principle saying a query's probes are its own
input and whatever its continuation goes on to consult. `Probes cache computation predicate`
packages the resulting universal statement, and `probes_bind`, `probes_tweakable`,
`probes_foldlM` and `probes_pathFold` let it compose along `>>=`, tweakable calls, hash folds and
binary authentication paths.

With that in place, the walk down key generation follows the recursion of the honest
evaluation: a WOTS chain step is a `.wotsHash` node, its starting secret a `.wotsPrf` node, a
chain's compression a `.wotsPk` node, and an XMSS node a `.tree` node or a WOTS public key. At
each step the payload is built from values the replay has already determined, and
`CanonicalGraph.value_wotsPosition` and `CanonicalGraph.value_merkleChild` identify those with
the cells of the very nodes whose inputs are being matched. The main result is
`probes_keygenInternal`: every input key generation consults is `Canonical`.

The signing side, and the consequences for the walk's cache, are in `HonestProbes`.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.HonestProbes

open CacheReplay CanonicalGraph

/-! ## Reading `QueriesUnder` as a universal statement

`CacheReplay.QueriesUnder` was built to *exhibit* an input a computation consults. Bounding
the inputs it consults needs the opposite reading, and the only extra ingredient is the
inversion principle below: a bind on a query consults its own input and nothing beyond what
the continuation consults at the replayed answer. -/

/-- A computation that consults anything is a query bound to a continuation, and what it
consults is that query's input or something the continuation consults. -/
theorem queriesUnder_shape {α : Type} {cache : QueryCache HashSpec}
    {computation : OracleComp HashSpec α} {probe : Bytes}
    (hquery : QueriesUnder cache computation probe) :
    ∃ (input : Bytes) (next : HashOutput → OracleComp HashSpec α),
      computation = query (spec := HashSpec) input >>= next ∧
        (probe = input ∨ QueriesUnder cache (next (replay cache input)) probe) := by
  induction hquery with
  | head input next => exact ⟨input, next, rfl, Or.inl rfl⟩
  | tail input probe next hrest _ => exact ⟨input, next, rfl, Or.inr hrest⟩

/-- A query bound to a continuation determines both. -/
theorem query_bind_injective {α : Type} {left right : Bytes}
    {next next' : HashOutput → OracleComp HashSpec α}
    (hshape : (query (spec := HashSpec) left >>= next) =
      (query (spec := HashSpec) right >>= next')) :
    left = right ∧ next = next' := by
  injection hshape with hinput hnext
  exact ⟨hinput, funext fun answer => congrFun hnext answer⟩

/-- **A query's probes are its input and its continuation's.** -/
theorem queriesUnder_query_bind_cases {α : Type} {cache : QueryCache HashSpec}
    {input probe : Bytes} {next : HashOutput → OracleComp HashSpec α}
    (hquery : QueriesUnder cache (query (spec := HashSpec) input >>= next) probe) :
    probe = input ∨ QueriesUnder cache (next (replay cache input)) probe := by
  obtain ⟨other, continuation, hshape, hcase⟩ := queriesUnder_shape hquery
  obtain ⟨rfl, rfl⟩ := query_bind_injective hshape
  exact hcase

/-- Every input `computation` consults, answered from `cache`, satisfies `predicate`. -/
@[expose]
def Probes (cache : QueryCache HashSpec) {α : Type} (computation : OracleComp HashSpec α)
    (predicate : Bytes → Prop) : Prop :=
  ∀ probe, QueriesUnder cache computation probe → predicate probe

/-- A pure computation consults nothing. -/
theorem probes_pure {α : Type} (cache : QueryCache HashSpec) (value : α)
    (predicate : Bytes → Prop) : Probes cache (pure value) predicate := by
  intro probe hprobe
  cases hprobe

/-- A query bound to a continuation satisfies a predicate on its probes when its own input does
and the continuation does at the replayed answer. -/
theorem probes_query_bind {α : Type} (cache : QueryCache HashSpec) (input : Bytes)
    (next : HashOutput → OracleComp HashSpec α) (predicate : Bytes → Prop)
    (hinput : predicate input)
    (hnext : Probes cache (next (replay cache input)) predicate) :
    Probes cache (query (spec := HashSpec) input >>= next) predicate := by
  intro probe hprobe
  rcases queriesUnder_query_bind_cases hprobe with rfl | hrest
  · exact hinput
  · exact hnext probe hrest

/-- **Probes compose along a bind.** The continuation is taken at the value the replay gives
the prefix, which `CacheReplay.run_eq_replay` identifies with the value the oracle run
produced; naming that value separately keeps it in whatever form the caller already has it. -/
theorem probes_bind {α β : Type} (cache : QueryCache HashSpec)
    (computation : OracleComp HashSpec α) (next : α → OracleComp HashSpec β)
    (predicate : Bytes → Prop) (value : α)
    (hvalue : (simulateQ (replay cache) computation : Id α) = value)
    (hcomputation : Probes cache computation predicate)
    (hnext : Probes cache (next value) predicate) :
    Probes cache (computation >>= next) predicate := by
  induction computation using OracleComp.inductionOn with
  | pure result =>
      rw [pure_bind]
      have hresult : result = value := hvalue
      rw [hresult]
      exact hnext
  | query_bind input continuation ih =>
      rw [bind_assoc]
      refine probes_query_bind cache input _ predicate
        (hcomputation input (QueriesUnder.head input continuation)) ?_
      exact ih (replay cache input) hvalue
        (fun probe hprobe =>
          hcomputation probe (QueriesUnder.tail input probe continuation hprobe))

/-- `probes_bind` with the prefix's value left as the replay computes it. -/
theorem probes_bind_replay {α β : Type} (cache : QueryCache HashSpec)
    (computation : OracleComp HashSpec α) (next : α → OracleComp HashSpec β)
    (predicate : Bytes → Prop) (hcomputation : Probes cache computation predicate)
    (hnext : Probes cache (next (simulateQ (replay cache) computation)) predicate) :
    Probes cache (computation >>= next) predicate :=
  probes_bind cache computation next predicate _ rfl hcomputation hnext

/-- `probes_query_bind` for a full-width hash call. -/
theorem probes_hash {α : Type} (cache : QueryCache HashSpec) (input : Bytes)
    (next : HashOutput → OracleComp HashSpec α) (predicate : Bytes → Prop)
    (hinput : predicate input)
    (hnext : Probes cache (next (replay cache input)) predicate) :
    Probes cache (Hashing.hash (m := OracleComp HashSpec) input >>= next) predicate :=
  probes_query_bind cache input next predicate hinput hnext

/-- A truncated hash call consults its own input and continues at the truncated replayed
answer. -/
theorem probes_shortHash {α : Type} (cache : QueryCache HashSpec) (input : Bytes)
    (next : Digest → OracleComp HashSpec α) (predicate : Bytes → Prop)
    (hinput : predicate input)
    (hnext : Probes cache (next (Hashing.truncate (replay cache input))) predicate) :
    Probes cache (Hashing.shortHash (m := OracleComp HashSpec) input >>= next) predicate := by
  rw [show (Hashing.shortHash (m := OracleComp HashSpec) input) >>= next =
      (Hashing.hash (m := OracleComp HashSpec) input) >>=
        (fun answer => next (Hashing.truncate answer)) from by
    simp [Hashing.shortHash]]
  exact probes_hash cache input _ predicate hinput hnext

/-- A truncated hash call on its own consults only its input. -/
theorem probes_shortHash_self (cache : QueryCache HashSpec) (input : Bytes)
    (predicate : Bytes → Prop) (hinput : predicate input) :
    Probes cache (Hashing.shortHash (m := OracleComp HashSpec) input) predicate := by
  rw [show (Hashing.shortHash (m := OracleComp HashSpec) input) =
      (Hashing.hash (m := OracleComp HashSpec) input) >>=
        (fun answer => pure (Hashing.truncate answer)) from rfl]
  exact probes_hash cache input _ predicate hinput (probes_pure cache _ predicate)

/-- A tweakable call consults its own byte input and continues at the value the cache gives
it — which is the `Id`-level tweakable call under `CacheReplay.replayQuery`. -/
theorem probes_tweakable {α : Type} (cache : QueryCache HashSpec) (publicSeed : Digest)
    (address : Address) (payload : Bytes) (next : Digest → OracleComp HashSpec α)
    (predicate : Bytes → Prop)
    (hinput : predicate (Hashing.tweakableInput publicSeed address payload))
    (hnext : Probes cache
      (next (@Hashing.tweakable Id _ (replayQuery cache) publicSeed address payload))
      predicate) :
    Probes cache
      (Hashing.tweakable (m := OracleComp HashSpec) publicSeed address payload >>= next)
      predicate := by
  refine probes_shortHash cache _ next predicate hinput ?_
  rwa [replayFold_step_eq_tweakable]

/-- A tweakable call on its own consults only its byte input. -/
theorem probes_tweakable_self (cache : QueryCache HashSpec) (publicSeed : Digest)
    (address : Address) (payload : Bytes) (predicate : Bytes → Prop)
    (hinput : predicate (Hashing.tweakableInput publicSeed address payload)) :
    Probes cache
      (Hashing.tweakable (m := OracleComp HashSpec) publicSeed address payload) predicate :=
  probes_shortHash_self cache _ predicate hinput

/-- A sequence of computations consults only what its parts consult. -/
theorem probes_sequenceFin {α : Type} (cache : QueryCache HashSpec)
    (predicate : Bytes → Prop) :
    ∀ (size : Nat) (parts : Fin size → OracleComp HashSpec α),
      (∀ index, Probes cache (parts index) predicate) →
        Probes cache (sequenceFin size parts) predicate := by
  intro size
  induction size with
  | zero => intro parts _; exact probes_pure cache _ predicate
  | succ size ih =>
      intro parts hparts
      refine probes_bind_replay cache (parts 0) _ predicate (hparts 0) ?_
      exact probes_bind_replay cache _ _ predicate (ih _ fun index => hparts index.succ)
        (probes_pure cache _ predicate)

/-- **Every step of a hash fold consults its input at the replayed running value.** This is the
universal companion of `CacheReplay.queriesUnder_foldlM_get`, which exhibits one such step. -/
theorem probes_foldlM {ι : Type} (cache : QueryCache HashSpec)
    (inputOf : Digest → ι → Bytes) (predicate : Bytes → Prop) :
    ∀ (items : List ι) (initial : Digest),
      (∀ (k : Nat) (hk : k < items.length),
        predicate (inputOf (replayFold cache inputOf (items.take k) initial) (items[k]'hk))) →
        Probes cache
          (items.foldlM (m := OracleComp HashSpec)
            (fun value item => Hashing.shortHash (inputOf value item)) initial) predicate := by
  intro items
  induction items with
  | nil => intro initial _; exact probes_pure cache _ predicate
  | cons item rest ih =>
      intro initial hsteps
      rw [List.foldlM_cons]
      refine probes_shortHash cache (inputOf initial item) _ predicate ?_ ?_
      · exact hsteps 0 (by simp)
      · exact ih _ fun k hk => hsteps (k + 1) (by simpa using hk)

/-! ## Binary path folds

Both authentication paths the scheme recomputes — a FORS tree's and an XMSS subtree's — are a
fold of one tweakable call per level, combining the running value with the level's sibling in
the order the index dictates. `pathInput` names the byte input such a step hashes when the
siblings are the honest ones, `replayFold_pathInput` says the running value after `k` levels
is the honest node at height `k`, and `probes_pathFold` concludes that every step's input is
the input of the parent node it computes. -/

/-- The byte input the `step`-th level of a binary path fold hashes, with the honest siblings
of the path at `index`. -/
@[expose]
def pathInput (publicSeed : Digest) (addressOf : Nat → Nat → Address)
    (nodes : Nat → Nat → Digest) (index : Nat) (value : Digest) (step : Nat) : Bytes :=
  Hashing.tweakableInput publicSeed (addressOf (step + 1) (index / 2 ^ (step + 1)))
    (if index / 2 ^ step % 2 = 0 then
      bytesBE n value ++ bytesBE n (nodes step (Nat.xor (index / 2 ^ step) 1))
     else bytesBE n (nodes step (Nat.xor (index / 2 ^ step) 1)) ++ bytesBE n value)

/-- A path step's two operands, in order, are the parent node's two children. -/
theorem ordered_bytes_eq_children (nodes : Nat → Nat → Digest) (index step : Nat) :
    (if index / 2 ^ step % 2 = 0 then
      bytesBE n (nodes step (index / 2 ^ step)) ++
        bytesBE n (nodes step (Nat.xor (index / 2 ^ step) 1))
     else bytesBE n (nodes step (Nat.xor (index / 2 ^ step) 1)) ++
        bytesBE n (nodes step (index / 2 ^ step))) =
      bytesBE n (nodes step (2 * (index / 2 ^ (step + 1)))) ++
        bytesBE n (nodes step (2 * (index / 2 ^ (step + 1)) + 1)) := by
  rw [Correctness.div_pow_succ]
  generalize index / 2 ^ step = position
  by_cases heven : position % 2 = 0
  · have hxor : Nat.xor position 1 = position + 1 :=
      Nat.xor_one_of_even (Nat.even_iff.mpr heven)
    rw [ite_eq_left heven, hxor, show 2 * (position / 2) = position from by omega]
  · have hxor : Nat.xor position 1 = position - 1 :=
      Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega : position % 2 = 1))
    rw [ite_eq_right heven, hxor, show 2 * (position / 2) = position - 1 from by omega,
      show position - 1 + 1 = position from by omega]

/-- **A path fold's running value after `k` levels is the honest node at height `k`.** -/
theorem replayFold_pathInput (cache : QueryCache HashSpec) (publicSeed : Digest)
    (addressOf : Nat → Nat → Address) (nodes : Nat → Nat → Digest) (index : Nat)
    (hnodes : ∀ level parent : Nat, nodes (level + 1) parent =
      @Hashing.tweakable Id _ (replayQuery cache) publicSeed (addressOf (level + 1) parent)
        (bytesBE n (nodes level (2 * parent)) ++ bytesBE n (nodes level (2 * parent + 1))))
    (height k : Nat) (hk : k ≤ height) :
    replayFold cache
        (fun value (step : Fin height) =>
          pathInput publicSeed addressOf nodes index value step.val)
        ((List.finRange height).take k) (nodes 0 index) =
      nodes k (index / 2 ^ k) := by
  rw [replayFold_eq_foldl,
    foldl_finRange_take height k hk
      (fun value level => Hashing.truncate
        (replay cache (pathInput publicSeed addressOf nodes index value level)))
      (nodes 0 index),
    show nodes 0 index = nodes 0 (index / 2 ^ 0) from by simp]
  refine Correctness.finRange_foldl k (fun level => nodes level (index / 2 ^ level)) _ ?_
  intro step
  simp only [pathInput, replayFold_step_eq_tweakable, ordered_bytes_eq_children]
  exact (hnodes step.val (index / 2 ^ (step.val + 1))).symm

/-- A replayed hash fold is the `Id`-level fold `CacheReplay.replayFold` performs. -/
theorem simulateQ_replay_foldlM {ι : Type} (cache : QueryCache HashSpec)
    (inputOf : Digest → ι → Bytes) :
    ∀ (items : List ι) (initial : Digest),
      (simulateQ (replay cache)
          (items.foldlM (m := OracleComp HashSpec)
            (fun value item => Hashing.shortHash (inputOf value item)) initial) : Id Digest) =
        replayFold cache inputOf items initial := by
  intro items
  induction items with
  | nil => intro initial; rfl
  | cons item rest ih => intro initial; rw [List.foldlM_cons, simulateQ_bind]; exact ih _

/-- **Every step of a path fold consults the input of the node it computes.** -/
theorem probes_pathFold (cache : QueryCache HashSpec) (publicSeed : Digest)
    (addressOf : Nat → Nat → Address) (nodes : Nat → Nat → Digest) (index : Nat)
    (hnodes : ∀ level parent : Nat, nodes (level + 1) parent =
      @Hashing.tweakable Id _ (replayQuery cache) publicSeed (addressOf (level + 1) parent)
        (bytesBE n (nodes level (2 * parent)) ++ bytesBE n (nodes level (2 * parent + 1))))
    (height : Nat) (predicate : Bytes → Prop)
    (hsteps : ∀ level < height,
      predicate (Hashing.tweakableInput publicSeed
        (addressOf (level + 1) (index / 2 ^ (level + 1)))
        (bytesBE n (nodes level (2 * (index / 2 ^ (level + 1)))) ++
          bytesBE n (nodes level (2 * (index / 2 ^ (level + 1)) + 1))))) :
    Probes cache
      ((List.finRange height).foldlM (m := OracleComp HashSpec)
        (fun value (step : Fin height) =>
          Hashing.shortHash (pathInput publicSeed addressOf nodes index value step.val))
        (nodes 0 index))
      predicate := by
  refine probes_foldlM cache _ predicate (List.finRange height) (nodes 0 index) ?_
  intro k hk
  have hklt : k < height := by simpa using hk
  rw [show ((List.finRange height)[k]'hk) = (⟨k, hklt⟩ : Fin height) from by apply Fin.ext; simp,
    replayFold_pathInput cache publicSeed addressOf nodes index hnodes height k
      (le_of_lt hklt)]
  simp only [pathInput, ordered_bytes_eq_children]
  exact hsteps k hklt

/-- `probes_pathFold`, with the fold's step and starting value matched only up to equality —
the form in which the scheme's two path folds actually appear. -/
theorem probes_pathFold_of_eq (cache : QueryCache HashSpec) (publicSeed : Digest)
    (addressOf : Nat → Nat → Address) (nodes : Nat → Nat → Digest) (index : Nat)
    (hnodes : ∀ level parent : Nat, nodes (level + 1) parent =
      @Hashing.tweakable Id _ (replayQuery cache) publicSeed (addressOf (level + 1) parent)
        (bytesBE n (nodes level (2 * parent)) ++ bytesBE n (nodes level (2 * parent + 1))))
    (height : Nat) (predicate : Bytes → Prop)
    (combine : Digest → Fin height → OracleComp HashSpec Digest) (initial : Digest)
    (hcombine : ∀ value step, combine value step =
      Hashing.shortHash (pathInput publicSeed addressOf nodes index value step.val))
    (hinitial : initial = nodes 0 index)
    (hsteps : ∀ level < height,
      predicate (Hashing.tweakableInput publicSeed
        (addressOf (level + 1) (index / 2 ^ (level + 1)))
        (bytesBE n (nodes level (2 * (index / 2 ^ (level + 1)))) ++
          bytesBE n (nodes level (2 * (index / 2 ^ (level + 1)) + 1))))) :
    Probes cache
      ((List.finRange height).foldlM (m := OracleComp HashSpec) combine initial) predicate := by
  rw [show combine = fun value step =>
      Hashing.shortHash (pathInput publicSeed addressOf nodes index value step.val) from by
    funext value step; exact hcombine value step, hinitial]
  exact probes_pathFold cache publicSeed addressOf nodes index hnodes height predicate hsteps

/-- The same fold, replayed: it arrives at the honest node the path leads to. -/
theorem replay_pathFold_of_eq (cache : QueryCache HashSpec) (publicSeed : Digest)
    (addressOf : Nat → Nat → Address) (nodes : Nat → Nat → Digest) (index : Nat)
    (hnodes : ∀ level parent : Nat, nodes (level + 1) parent =
      @Hashing.tweakable Id _ (replayQuery cache) publicSeed (addressOf (level + 1) parent)
        (bytesBE n (nodes level (2 * parent)) ++ bytesBE n (nodes level (2 * parent + 1))))
    (height : Nat) (combine : Digest → Fin height → OracleComp HashSpec Digest)
    (initial : Digest)
    (hcombine : ∀ value step, combine value step =
      Hashing.shortHash (pathInput publicSeed addressOf nodes index value step.val))
    (hinitial : initial = nodes 0 index) :
    (simulateQ (replay cache)
        ((List.finRange height).foldlM (m := OracleComp HashSpec) combine initial)
      : Id Digest) =
      nodes height (index / 2 ^ height) := by
  rw [show combine = fun value step =>
      Hashing.shortHash (pathInput publicSeed addressOf nodes index value step.val) from by
    funext value step; exact hcombine value step, hinitial, simulateQ_replay_foldlM,
    show List.finRange height =
      (List.finRange height).take height from by simp]
  exact replayFold_pathInput cache publicSeed addressOf nodes index hnodes height height le_rfl

/-! ## The canonical inputs of a cache

A probe is accounted for when it is some structural node's own byte input, read at the cells
the cache itself determines. `CanonicalGraph.Programming.full_cache_lookup` then puts it in a
completed walk's cache. -/

/-- The honest cells, as a finished cache computes them. -/
@[expose]
def replayCells (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest) : Cells :=
  @value (replayQuery cache) secretSeed publicSeed

/-- An input is canonical when it is some structural node's own byte input. -/
@[expose]
def Canonical (publicSeed : Digest) (cells : Cells) (probe : Bytes) : Prop :=
  ∃ parent : StructuralNode, probe = canonicalInput publicSeed cells parent

/-- The child encoding of a one-child node is the child's cell bytes. -/
theorem childBytes_singleton (cells : Cells) (child : Node) :
    childBytes cells [child] = bytesBE n (cells child) := by
  simp [childBytes]

/-- The child encoding of a two-child node is the concatenation of the children's cell bytes. -/
theorem childBytes_pair (cells : Cells) (left right : Node) :
    childBytes cells [left, right] = bytesBE n (cells left) ++ bytesBE n (cells right) := by
  simp [childBytes]

/-! ## Replaying the honest algorithms

A hash-only computation's replayed value is the same algorithm at `Id` under
`CacheReplay.replayQuery`, which is what `Correctness.Naturality` proves for an arbitrary
faithful implementation. These are the instances of that at a cache. -/

/-- A replayed secret derivation is the `Id`-level derivation under the replay instance. -/
theorem derive_replay (cache : QueryCache HashSpec) (publicSeed secretSeed : Digest)
    (address : Address) :
    (simulateQ (replay cache)
        (Hashing.derive (m := OracleComp HashSpec) publicSeed secretSeed address) : Id Digest) =
      @Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed address :=
  @Correctness.Naturality.derive_simulate Id _ _ (replay cache) (replayQuery cache)
    (fun _ => rfl) publicSeed secretSeed address

/-- A replayed tweakable call is the `Id`-level call under the replay instance. -/
theorem tweakable_replay (cache : QueryCache HashSpec) (publicSeed : Digest)
    (address : Address) (payload : Bytes) :
    (simulateQ (replay cache)
        (Hashing.tweakable (m := OracleComp HashSpec) publicSeed address payload) : Id Digest) =
      @Hashing.tweakable Id _ (replayQuery cache) publicSeed address payload :=
  @VerifierNaturality.tweakable_simulate Id _ _ (replay cache) (replayQuery cache)
    (fun _ => rfl) publicSeed address payload

/-- A replayed WOTS chain is the `Id`-level chain under the replay instance. -/
theorem chain_replay (cache : QueryCache HashSpec) (publicSeed : Digest) (address : Address)
    (start steps : Nat) (value : Digest) :
    (simulateQ (replay cache)
        (Wots.chain (m := OracleComp HashSpec) publicSeed address start steps value)
      : Id Digest) =
      @Wots.chain Id _ (replayQuery cache) publicSeed address start steps value :=
  @VerifierNaturality.chain_simulate Id _ _ (replay cache) (replayQuery cache)
    (fun _ => rfl) publicSeed address start steps value

/-- A replayed XMSS node computation is the `Id`-level one under the replay instance. -/
theorem merkle_node_replay (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (address : Address) (height index : Nat) :
    (simulateQ (replay cache)
        (Merkle.node (m := OracleComp HashSpec) secretSeed publicSeed address height index)
      : Id Digest) =
      @Merkle.node Id _ (replayQuery cache) secretSeed publicSeed address height index :=
  @Correctness.Naturality.merkle_node_simulate Id _ _ (replay cache) (replayQuery cache)
    (fun _ => rfl) secretSeed publicSeed address height index

/-- Replayed key generation is `Id`-level key generation under the replay instance. -/
theorem keygenInternal_replay (cache : QueryCache HashSpec)
    (secretSeed prfSeed publicSeed : Digest) :
    (simulateQ (replay cache)
        (Scheme.keygenInternal (m := OracleComp HashSpec) secretSeed prfSeed publicSeed)
      : Id (SecretKey × PublicKey)) =
      @Scheme.keygenInternal Id _ (replayQuery cache) secretSeed prfSeed publicSeed :=
  @Correctness.Naturality.keygenInternal_simulate Id _ _ (replay cache) (replayQuery cache)
    (fun _ => rfl) secretSeed prfSeed publicSeed

/-! ## The WOTS side of key generation -/

/-- The single child of a chain step is the chain value one position below it. -/
theorem children_wotsHash (key : WotsKey) (chain : Fin chains) (step : Fin (w - 1))
    (hstep : step.val < w) :
    (StructuralNode.wotsHash key chain step).children =
      [Node.structural (wotsPosition key chain ⟨step.val, hstep⟩)] := by
  by_cases hzero : step.val = 0 <;>
    simp [StructuralNode.children, wotsPosition, hzero]

/-- The cell at a chain position is the chain run that far from the derived secret. -/
theorem replayCells_wotsPosition (cache : QueryCache HashSpec)
    (secretSeed publicSeed : Digest) (key : WotsKey) (chain : Fin chains) (position : Fin w) :
    replayCells cache secretSeed publicSeed (.structural (wotsPosition key chain position)) =
      @Wots.chain Id _ (replayQuery cache) publicSeed
        { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 position.val
        (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
          (Wots.secretAddress key.address chain)) :=
  @value_wotsPosition (replayQuery cache) secretSeed publicSeed key chain position

/-- The canonical input of a WOTS secret node is the PRF input on the secret seed. -/
theorem canonicalInput_wotsPrf (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (key : WotsKey) (chain : Fin chains) :
    canonicalInput publicSeed (replayCells cache secretSeed publicSeed)
        (.wotsPrf key chain) =
      Hashing.tweakableInput publicSeed (Wots.secretAddress key.address chain)
        (bytesBE n secretSeed) := by
  simp only [canonicalInput,
    show (StructuralNode.wotsPrf key chain).children = [Node.secretSeed] from rfl,
    childBytes_singleton]
  rfl

/-- The canonical input of a chain step is the tweakable input on the chain value below it. -/
theorem canonicalInput_wotsHash (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (key : WotsKey) (chain : Fin chains) (step : Fin (w - 1)) (hstep : step.val < w) :
    canonicalInput publicSeed (replayCells cache secretSeed publicSeed)
        (.wotsHash key chain step) =
      Hashing.tweakableInput publicSeed
        { key.address with
          chainOrHeight := BitVec.ofNat 32 chain.val
          hashOrIndex := BitVec.ofNat 32 step.val }
        (bytesBE n (@Wots.chain Id _ (replayQuery cache) publicSeed
          { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 step.val
          (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
            (Wots.secretAddress key.address chain)))) := by
  simp only [canonicalInput, children_wotsHash key chain step hstep, childBytes_singleton,
    replayCells_wotsPosition]
  rfl

/-- The canonical input of a WOTS public-key node is the compression input on the chain
endpoints. -/
theorem canonicalInput_wotsPk (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (key : WotsKey) :
    canonicalInput publicSeed (replayCells cache secretSeed publicSeed) (.wotsPk key) =
      Hashing.tweakableInput publicSeed (Wots.publicKeyAddress key.address)
        (digestArrayBytes fun chain : Fin chains =>
          @Wots.chain Id _ (replayQuery cache) publicSeed
            { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 (w - 1)
            (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
              (Wots.secretAddress key.address chain))) := by
  simp only [canonicalInput,
    show (StructuralNode.wotsPk key).children =
      List.ofFn (fun chain : Fin chains =>
        Node.structural (.wotsHash key chain ⟨w - 2, by decide⟩)) from rfl,
    childBytes_ofFn]
  rfl

/-- **Every step of a WOTS chain consults a canonical input.** -/
theorem probes_chain (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (key : WotsKey) (chain : Fin chains) :
    ∀ (steps start : Nat), start + steps ≤ w - 1 →
      Probes cache
        (Wots.chain (m := OracleComp HashSpec) publicSeed
          { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } start steps
          (@Wots.chain Id _ (replayQuery cache) publicSeed
            { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 start
            (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
              (Wots.secretAddress key.address chain))))
        (Canonical publicSeed (replayCells cache secretSeed publicSeed)) := by
  intro steps
  induction steps with
  | zero => intro start _; exact probes_pure cache _ _
  | succ steps ih =>
      intro start hbound
      have hstep : start < w - 1 := by simp only [w, winternitzBits] at *; omega
      have hstart : start < w := by simp only [w, winternitzBits] at *; omega
      refine probes_tweakable cache publicSeed
        { key.address with
          chainOrHeight := BitVec.ofNat 32 chain.val
          hashOrIndex := BitVec.ofNat 32 start }
        (bytesBE n (@Wots.chain Id _ (replayQuery cache) publicSeed
          { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 start
          (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
            (Wots.secretAddress key.address chain)))) _ _ ?_ ?_
      · exact ⟨.wotsHash key chain ⟨start, hstep⟩,
          (canonicalInput_wotsHash cache secretSeed publicSeed key chain ⟨start, hstep⟩
            hstart).symm⟩
      · have hchain : (@Wots.chain Id _ (replayQuery cache) publicSeed
            { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 (start + 1)
            (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
              (Wots.secretAddress key.address chain))) =
            @Hashing.tweakable Id _ (replayQuery cache) publicSeed
              { key.address with
                chainOrHeight := BitVec.ofNat 32 chain.val
                hashOrIndex := BitVec.ofNat 32 start }
              (bytesBE n (@Wots.chain Id _ (replayQuery cache) publicSeed
                { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 start
                (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
                  (Wots.secretAddress key.address chain)))) := by
          rw [@Correctness.Wots.chain_add (replayQuery cache) publicSeed
            { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 start 1
            (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
              (Wots.secretAddress key.address chain)), Nat.zero_add]
          rfl
        change Probes cache
            (Wots.chain (m := OracleComp HashSpec) publicSeed
              { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } (start + 1) steps
              (@Hashing.tweakable Id _ (replayQuery cache) publicSeed
                { key.address with
                  chainOrHeight := BitVec.ofNat 32 chain.val
                  hashOrIndex := BitVec.ofNat 32 start }
                (bytesBE n (@Wots.chain Id _ (replayQuery cache) publicSeed
                  { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 start
                  (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
                    (Wots.secretAddress key.address chain))))))
            (Canonical publicSeed (replayCells cache secretSeed publicSeed))
        rw [← hchain]
        exact ih (start + 1) (by omega)

/-- **A WOTS public key's queries are all canonical.** -/
theorem probes_wots_publicKey (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (key : WotsKey) :
    Probes cache
      (Wots.publicKey (m := OracleComp HashSpec) secretSeed publicSeed key.address)
      (Canonical publicSeed (replayCells cache secretSeed publicSeed)) := by
  refine probes_bind cache _ _ _
    (fun index : Fin chains =>
      @Wots.chain Id _ (replayQuery cache) publicSeed
        { key.address with chainOrHeight := BitVec.ofNat 32 index.val } 0 (w - 1)
        (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
          (Wots.secretAddress key.address index))) ?_ ?_ ?_
  · rw [VerifierNaturality.sequenceFin_simulate]
    simp only [Correctness.sequenceFin_id, simulateQ_bind, derive_replay, chain_replay]
    rfl
  · refine probes_sequenceFin cache _ chains _ ?_
    intro index
    refine probes_tweakable cache publicSeed (Wots.secretAddress key.address index)
      (bytesBE n secretSeed) _ _ ?_ ?_
    · exact ⟨.wotsPrf key index,
        (canonicalInput_wotsPrf cache secretSeed publicSeed key index).symm⟩
    · exact probes_chain cache secretSeed publicSeed key index (w - 1) 0 (by omega)
  · exact probes_tweakable_self cache publicSeed _ _ _
      ⟨.wotsPk key, (canonicalInput_wotsPk cache secretSeed publicSeed key).symm⟩

/-! ## The XMSS side of key generation -/

/-- The canonical input of an XMSS tree node is the tweakable input on its two children's
nodes. -/
theorem canonicalInput_tree (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (tree : Tree) (height : Fin subtreeHeight)
    (index : Fin (2 ^ (subtreeHeight - (height.val + 1)))) :
    canonicalInput publicSeed (replayCells cache secretSeed publicSeed)
        (.tree tree height index) =
      Hashing.tweakableInput publicSeed
        (Merkle.nodeAddress tree.address (height.val + 1) index.val)
        (bytesBE n (@Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address
            height.val (2 * index.val)) ++
          bytesBE n (@Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address
            height.val (2 * index.val + 1))) := by
  simp only [canonicalInput,
    show (StructuralNode.tree tree height index).children =
      [Node.structural (merkleChild tree height index 0),
        Node.structural (merkleChild tree height index 1)] from rfl,
    childBytes_pair,
    show replayCells cache secretSeed publicSeed
        (.structural (merkleChild tree height index 0)) =
      @Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address height.val
        (2 * index.val + 0) from
      @value_merkleChild (replayQuery cache) secretSeed publicSeed tree height index 0,
    show replayCells cache secretSeed publicSeed
        (.structural (merkleChild tree height index 1)) =
      @Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address height.val
        (2 * index.val + 1) from
      @value_merkleChild (replayQuery cache) secretSeed publicSeed tree height index 1,
    Nat.add_zero]
  rfl

/-- **Every node of an XMSS subtree consults only canonical inputs.** -/
theorem probes_merkle_node (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (tree : Tree) :
    ∀ (height : Nat), height ≤ subtreeHeight →
      ∀ index : Fin (2 ^ (subtreeHeight - height)),
      Probes cache
        (Merkle.node (m := OracleComp HashSpec) secretSeed publicSeed tree.address height
          index.val)
        (Canonical publicSeed (replayCells cache secretSeed publicSeed)) := by
  intro height
  induction height with
  | zero =>
      intro _ index
      exact probes_wots_publicKey cache secretSeed publicSeed
        ⟨tree, ⟨index.val, index.isLt⟩⟩
  | succ height ih =>
      intro hheight index
      have hleft : 2 * index.val + 0 < 2 ^ (subtreeHeight - height) := by
        have := child_index_lt subtreeHeight height 1 (by omega)
          ⟨index.val, by simp⟩ 0
        simpa using this
      have hright : 2 * index.val + 1 < 2 ^ (subtreeHeight - height) := by
        have := child_index_lt subtreeHeight height 1 (by omega)
          ⟨index.val, by simp⟩ 1
        simpa using this
      refine probes_bind cache _ _ _
        (@Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address height
          (2 * index.val))
        (merkle_node_replay cache secretSeed publicSeed tree.address height (2 * index.val))
        (ih (by omega) ⟨2 * index.val, by simpa using hleft⟩) ?_
      refine probes_bind cache _ _ _
        (@Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address height
          (2 * index.val + 1))
        (merkle_node_replay cache secretSeed publicSeed tree.address height (2 * index.val + 1))
        (ih (by omega) ⟨2 * index.val + 1, hright⟩) ?_
      refine probes_tweakable_self cache publicSeed _ _ _
        ⟨.tree tree ⟨height, by omega⟩ ⟨index.val, index.isLt⟩, ?_⟩
      rw [canonicalInput_tree]

/-! ## Key generation

Key generation is one XMSS node: the root of the top layer's only subtree. Every input it
consults is therefore canonical. -/

/-- The top subtree, whose root is the public key. -/
@[expose]
def topTree : Tree := ⟨⟨layers - 1, by decide⟩, ⟨0, by decide⟩⟩

/-- **Key generation consults only canonical inputs.** -/
theorem probes_keygenInternal (cache : QueryCache HashSpec)
    (secretSeed prfSeed publicSeed : Digest) :
    Probes cache
      (Scheme.keygenInternal (m := OracleComp HashSpec) secretSeed prfSeed publicSeed)
      (Canonical publicSeed (replayCells cache secretSeed publicSeed)) :=
  probes_bind cache _ _ _
    (@Merkle.node Id _ (replayQuery cache) secretSeed publicSeed topTree.address
      subtreeHeight 0)
    (merkle_node_replay cache secretSeed publicSeed topTree.address subtreeHeight 0)
    (probes_merkle_node cache secretSeed publicSeed topTree subtreeHeight le_rfl
      ⟨0, by decide⟩)
    (probes_pure cache _ _)

end SLHDSA.SHAKE128s.HonestProbes
