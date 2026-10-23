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
# The honest parties ask nothing new

`WarmedGame.graphWalk` evaluates the whole canonical graph before the adversary runs, leaving
a cache that holds an entry at `CanonicalGraph.canonicalInput` of every structural node and at
nothing else. `CachedRun.run_eq_pure_of_cached` turns that into a statement about an honest
party's run — *provided* every input the party consults is one of those canonical inputs.

This file proves that for key generation, and the corresponding statement for signing. The
argument is the mirror image of the one the verifier entry lemmas make: there, a particular
byte input had to be exhibited among those a computation consults; here, *every* input it
consults has to be accounted for. So the first thing needed is the missing direction of
`CacheReplay.QueriesUnder` — an inversion principle saying a query's probes are its own input
and whatever its continuation goes on to consult — and `Probes` packages the resulting
universal statement so that it composes along `>>=`.

With that in place, the walk down an honest computation follows the same recursion the honest
evaluation itself follows: a WOTS chain step is a `.wotsHash` node, its starting secret a
`.wotsPrf` node, a chain's compression a `.wotsPk` node, an XMSS node a `.tree` node or a WOTS
public key, and the FORS trees the `.forsPrf`, `.forsTree` and `.forsRoots` coordinates. At
each step the payload is built from values the replay has already determined, and
`CanonicalGraph.value_wotsPosition` and `CanonicalGraph.value_merkleChild` identify those with
the cells of the very nodes whose inputs are being matched.

Key generation consults nothing else, so running it from the walk's cache is a `pure`
computation. Signing consults exactly two further inputs, and both are message-dependent: the
randomizer `PRF_msg(SK.prf, PK.seed, M)` and the message digest `H_msg(R, PK, M)`. Those the
walk cannot have installed, since the message is the adversary's, so they are named
explicitly rather than claimed cached.

Everything is stated for the hash-only monad, where `CacheReplay.QueriesUnder` lives; the last
section carries it to the game's own monad, where the honest parties are lifts of these very
computations.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.HonestProbes

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
def Probes (cache : QueryCache HashSpec) {α : Type} (computation : OracleComp HashSpec α)
    (predicate : Bytes → Prop) : Prop :=
  ∀ probe, QueriesUnder cache computation probe → predicate probe

theorem probes_pure {α : Type} (cache : QueryCache HashSpec) (value : α)
    (predicate : Bytes → Prop) : Probes cache (pure value) predicate := by
  intro probe hprobe
  cases hprobe

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

theorem probes_hash {α : Type} (cache : QueryCache HashSpec) (input : Bytes)
    (next : HashOutput → OracleComp HashSpec α) (predicate : Bytes → Prop)
    (hinput : predicate input)
    (hnext : Probes cache (next (replay cache input)) predicate) :
    Probes cache (Hashing.hash (m := OracleComp HashSpec) input >>= next) predicate :=
  probes_query_bind cache input next predicate hinput hnext

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

theorem probes_tweakable_self (cache : QueryCache HashSpec) (publicSeed : Digest)
    (address : Address) (payload : Bytes) (predicate : Bytes → Prop)
    (hinput : predicate (Hashing.tweakableInput publicSeed address payload)) :
    Probes cache
      (Hashing.tweakable (m := OracleComp HashSpec) publicSeed address payload) predicate :=
  probes_shortHash_self cache _ predicate hinput

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
    rw [if_pos heven, hxor, show 2 * (position / 2) = position from by omega]
  · have hxor : Nat.xor position 1 = position - 1 :=
      Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega : position % 2 = 1))
    rw [if_neg heven, hxor, show 2 * (position / 2) = position - 1 from by omega,
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
def replayCells (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest) : Cells :=
  @value (replayQuery cache) secretSeed publicSeed

/-- An input is canonical when it is some structural node's own byte input. -/
def Canonical (publicSeed : Digest) (cells : Cells) (probe : Bytes) : Prop :=
  ∃ parent : StructuralNode, probe = canonicalInput publicSeed cells parent

theorem childBytes_singleton (cells : Cells) (child : Node) :
    childBytes cells [child] = bytesBE n (cells child) := by
  simp [childBytes]

theorem childBytes_pair (cells : Cells) (left right : Node) :
    childBytes cells [left, right] = bytesBE n (cells left) ++ bytesBE n (cells right) := by
  simp [childBytes]

/-! ## Replaying the honest algorithms

A hash-only computation's replayed value is the same algorithm at `Id` under
`CacheReplay.replayQuery`, which is what `Correctness.Naturality` proves for an arbitrary
faithful implementation. These are the instances of that at a cache. -/

theorem derive_replay (cache : QueryCache HashSpec) (publicSeed secretSeed : Digest)
    (address : Address) :
    (simulateQ (replay cache)
        (Hashing.derive (m := OracleComp HashSpec) publicSeed secretSeed address) : Id Digest) =
      @Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed address :=
  @Correctness.Naturality.derive_simulate Id _ _ (replay cache) (replayQuery cache)
    (fun _ => rfl) publicSeed secretSeed address

theorem tweakable_replay (cache : QueryCache HashSpec) (publicSeed : Digest)
    (address : Address) (payload : Bytes) :
    (simulateQ (replay cache)
        (Hashing.tweakable (m := OracleComp HashSpec) publicSeed address payload) : Id Digest) =
      @Hashing.tweakable Id _ (replayQuery cache) publicSeed address payload :=
  @VerifierNaturality.tweakable_simulate Id _ _ (replay cache) (replayQuery cache)
    (fun _ => rfl) publicSeed address payload

theorem chain_replay (cache : QueryCache HashSpec) (publicSeed : Digest) (address : Address)
    (start steps : Nat) (value : Digest) :
    (simulateQ (replay cache)
        (Wots.chain (m := OracleComp HashSpec) publicSeed address start steps value)
      : Id Digest) =
      @Wots.chain Id _ (replayQuery cache) publicSeed address start steps value :=
  @VerifierNaturality.chain_simulate Id _ _ (replay cache) (replayQuery cache)
    (fun _ => rfl) publicSeed address start steps value

theorem merkle_node_replay (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (address : Address) (height index : Nat) :
    (simulateQ (replay cache)
        (Merkle.node (m := OracleComp HashSpec) secretSeed publicSeed address height index)
      : Id Digest) =
      @Merkle.node Id _ (replayQuery cache) secretSeed publicSeed address height index :=
  @Correctness.Naturality.merkle_node_simulate Id _ _ (replay cache) (replayQuery cache)
    (fun _ => rfl) secretSeed publicSeed address height index

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
        show Probes cache
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

/-! ## The FORS side of signing

A FORS tree is the same shape as an XMSS subtree — a PRF-derived secret under each leaf, a
binary tree above — so its nodes are `.forsPrf`, `.forsTree` and `.forsRoots` coordinates and
the same two lemmas suffice: the canonical input of a leaf node and of an inner one. The
index of a node carries the offset of its own tree among the fourteen, which is what keeps
the fourteen trees' coordinates apart. -/

theorem xor_one_lt (position level : Nat) (hlevel : 0 < level)
    (hposition : position < 2 ^ level) : Nat.xor position 1 < 2 ^ level := by
  rcases Nat.even_or_odd position with heven | hodd
  · have hxor : Nat.xor position 1 = position + 1 := Nat.xor_one_of_even heven
    have hparity : position % 2 = 0 := Nat.even_iff.mp heven
    have hpower : 2 ^ level % 2 = 0 := by
      obtain ⟨below, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : level ≠ 0)
      simp [pow_succ, Nat.mul_mod_left]
    omega
  · have hxor : Nat.xor position 1 = position - 1 := Nat.xor_one_of_odd hodd
    omega

theorem fors_node_replay (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (address : Address) (height index : Nat) :
    (simulateQ (replay cache)
        (Fors.node (m := OracleComp HashSpec) secretSeed publicSeed address height index)
      : Id Digest) =
      @Fors.node Id _ (replayQuery cache) secretSeed publicSeed address height index :=
  @Correctness.Naturality.fors_node_simulate Id _ _ (replay cache) (replayQuery cache)
    (fun _ => rfl) secretSeed publicSeed address height index

theorem fors_sign_replay (cache : QueryCache HashSpec) (indices : Fors.Indices)
    (secretSeed publicSeed : Digest) (address : Address) :
    (simulateQ (replay cache)
        (Fors.sign (m := OracleComp HashSpec) indices secretSeed publicSeed address)
      : Id ForsSignature) =
      @Fors.sign Id _ (replayQuery cache) indices secretSeed publicSeed address :=
  @Correctness.Naturality.fors_sign_simulate Id _ _ (replay cache) (replayQuery cache)
    (fun _ => rfl) indices secretSeed publicSeed address

/-- A FORS secret's derivation consults its own canonical input. -/
theorem canonical_forsSecret (cache : QueryCache HashSpec)
    (secretSeed publicSeed : Digest) (key : ForsKey) (index : Nat)
    (hindex : index < forsTrees * 2 ^ forsHeight) :
    Canonical publicSeed (replayCells cache secretSeed publicSeed)
      (Hashing.tweakableInput publicSeed (Fors.secretAddress key.address index)
        (bytesBE n secretSeed)) := by
  refine ⟨.forsPrf key ⟨index, hindex⟩, ?_⟩
  simp only [canonicalInput,
    show (StructuralNode.forsPrf key ⟨index, hindex⟩).children = [Node.secretSeed] from rfl,
    childBytes_singleton]
  rfl

/-- A FORS leaf node's hash consults its own canonical input. -/
theorem canonical_forsLeaf (cache : QueryCache HashSpec)
    (secretSeed publicSeed : Digest) (key : ForsKey) (index : Nat)
    (hindex : index < forsTrees * 2 ^ forsHeight) :
    Canonical publicSeed (replayCells cache secretSeed publicSeed)
      (Hashing.tweakableInput publicSeed (Fors.nodeAddress key.address 0 index)
        (bytesBE n (@Fors.secret Id _ (replayQuery cache) secretSeed publicSeed
          key.address index))) := by
  refine ⟨.forsTree key ⟨0, by decide⟩ ⟨index, hindex⟩, ?_⟩
  simp only [canonicalInput,
    show (StructuralNode.forsTree key ⟨0, by decide⟩ ⟨index, hindex⟩).children =
      [Node.structural (.forsPrf key ⟨index, hindex⟩)] from rfl,
    childBytes_singleton]
  rfl

/-- An inner FORS node's hash consults its own canonical input. -/
theorem canonical_forsNode (cache : QueryCache HashSpec)
    (secretSeed publicSeed : Digest) (key : ForsKey) (level index : Nat)
    (hlevel : level < forsHeight)
    (hindex : index < forsTrees * 2 ^ (forsHeight - (level + 1))) :
    Canonical publicSeed (replayCells cache secretSeed publicSeed)
      (Hashing.tweakableInput publicSeed (Fors.nodeAddress key.address (level + 1) index)
        (bytesBE n (@Fors.node Id _ (replayQuery cache) secretSeed publicSeed key.address
            level (2 * index)) ++
          bytesBE n (@Fors.node Id _ (replayQuery cache) secretSeed publicSeed key.address
            level (2 * index + 1)))) := by
  refine ⟨.forsTree key ⟨level + 1, by omega⟩ ⟨index, hindex⟩, ?_⟩
  simp only [canonicalInput,
    show (StructuralNode.forsTree key ⟨level + 1, by omega⟩ ⟨index, hindex⟩).children =
      [Node.structural
          (forsChild key ⟨level + 1, by omega⟩ (Nat.succ_pos level) ⟨index, hindex⟩ 0),
        Node.structural
          (forsChild key ⟨level + 1, by omega⟩ (Nat.succ_pos level) ⟨index, hindex⟩ 1)]
      from rfl,
    childBytes_pair]
  rfl

/-- **Every node of a FORS tree consults only canonical inputs.** -/
theorem probes_fors_node (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (key : ForsKey) :
    ∀ (level : Nat), level ≤ forsHeight →
      ∀ (index : Nat), index < forsTrees * 2 ^ (forsHeight - level) →
        Probes cache
          (Fors.node (m := OracleComp HashSpec) secretSeed publicSeed key.address level index)
          (Canonical publicSeed (replayCells cache secretSeed publicSeed)) := by
  intro level
  induction level with
  | zero =>
      intro _ index hindex
      refine probes_tweakable cache publicSeed (Fors.secretAddress key.address index)
        (bytesBE n secretSeed) _ _
        (canonical_forsSecret cache secretSeed publicSeed key index (by simpa using hindex)) ?_
      exact probes_tweakable_self cache publicSeed _ _ _
        (canonical_forsLeaf cache secretSeed publicSeed key index (by simpa using hindex))
  | succ level ih =>
      intro hlevel index hindex
      have hleft : 2 * index + 0 < forsTrees * 2 ^ (forsHeight - level) :=
        child_index_lt forsHeight level forsTrees (by omega) ⟨index, hindex⟩ 0
      have hright : 2 * index + 1 < forsTrees * 2 ^ (forsHeight - level) :=
        child_index_lt forsHeight level forsTrees (by omega) ⟨index, hindex⟩ 1
      refine probes_bind cache _ _ _
        (@Fors.node Id _ (replayQuery cache) secretSeed publicSeed key.address level
          (2 * index))
        (fors_node_replay cache secretSeed publicSeed key.address level (2 * index))
        (ih (by omega) (2 * index) (by omega)) ?_
      refine probes_bind cache _ _ _
        (@Fors.node Id _ (replayQuery cache) secretSeed publicSeed key.address level
          (2 * index + 1))
        (fors_node_replay cache secretSeed publicSeed key.address level (2 * index + 1))
        (ih (by omega) (2 * index + 1) hright) ?_
      exact probes_tweakable_self cache publicSeed _ _ _
        (canonical_forsNode cache secretSeed publicSeed key level index (by omega) hindex)

/-- **Signing a FORS message consults only canonical inputs.** -/
theorem probes_fors_sign (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (key : ForsKey) (indices : Fors.Indices) :
    Probes cache
      (Fors.sign (m := OracleComp HashSpec) indices secretSeed publicSeed key.address)
      (Canonical publicSeed (replayCells cache secretSeed publicSeed)) := by
  refine probes_sequenceFin cache _ forsTrees _ fun tree => ?_
  have hsecret : tree.val * 2 ^ forsHeight + (indices tree).val < forsTrees * 2 ^ forsHeight := by
    have := (indices tree).isLt
    have := tree.isLt
    calc tree.val * 2 ^ forsHeight + (indices tree).val
        < tree.val * 2 ^ forsHeight + 2 ^ forsHeight := by omega
      _ = (tree.val + 1) * 2 ^ forsHeight := by ring
      _ ≤ forsTrees * 2 ^ forsHeight := Nat.mul_le_mul_right _ (by omega)
  refine probes_tweakable cache publicSeed
    (Fors.secretAddress key.address (tree.val * 2 ^ forsHeight + (indices tree).val))
    (bytesBE n secretSeed) _ _
    (canonical_forsSecret cache secretSeed publicSeed key _ hsecret) ?_
  refine probes_bind_replay cache _ _ _ ?_ (probes_pure cache _ _)
  refine probes_sequenceFin cache _ forsHeight _ fun level => ?_
  refine probes_fors_node cache secretSeed publicSeed key level.val (le_of_lt level.isLt) _ ?_
  have hlevel := level.isLt
  have hsibling : Nat.xor ((indices tree).val / 2 ^ level.val) 1 <
      2 ^ (forsHeight - level.val) := by
    refine xor_one_lt _ _ (by omega) (Nat.div_lt_of_lt_mul ?_)
    rw [← pow_add, Nat.add_sub_cancel' (le_of_lt level.isLt)]
    exact (indices tree).isLt
  have htree := tree.isLt
  calc tree.val * 2 ^ (forsHeight - level.val) +
        Nat.xor ((indices tree).val / 2 ^ level.val) 1
      < tree.val * 2 ^ (forsHeight - level.val) + 2 ^ (forsHeight - level.val) := by omega
    _ = (tree.val + 1) * 2 ^ (forsHeight - level.val) := by ring
    _ ≤ forsTrees * 2 ^ (forsHeight - level.val) := Nat.mul_le_mul_right _ (by omega)

/-! ## Recovering the FORS public key

Signing recomputes the FORS public key from the signature it has just produced, which is the
verifier's computation run on an honest signature. Its queries are the leaves of the fourteen
trees, their authentication paths, and the final compression — all canonical, because the
signature discloses exactly the honest cells. -/

/-- The honest FORS signature of one tree, entry by entry. -/
theorem fors_sign_entry (cache : QueryCache HashSpec) (indices : Fors.Indices)
    (secretSeed publicSeed : Digest) (address : Address) (tree : Fin forsTrees) :
    @Fors.sign Id _ (replayQuery cache) indices secretSeed publicSeed address tree =
      { secret := @Fors.secret Id _ (replayQuery cache) secretSeed publicSeed address
          (tree.val * 2 ^ forsHeight + (indices tree).val)
        authentication := fun level =>
          @Fors.node Id _ (replayQuery cache) secretSeed publicSeed address level.val
            (tree.val * 2 ^ (forsHeight - level.val) +
              Nat.xor ((indices tree).val / 2 ^ level.val) 1) } := by
  simp only [Fors.sign, Correctness.sequenceFin_id, bind, pure]

/-! ## The entries a FORS signature discloses are cells

A signature is not a computation to be redone; it is a tuple of cells. Each entry of an honest
FORS signature is named here: the secret at the selected leaf, and the sibling at each level of
its authentication path. The bounds are the ones `probes_fors_sign` already establishes for the
same coordinates, carried in the nodes themselves so the statements stay free of them.

This is what a signer that reads rather than recomputes answers with, and all of it is
available once the signature is issued: the secret because its index is signed, the path
because `forsTree` nodes are unprotected. -/

/-- The leaf an honest FORS signature opens, as a coordinate of the whole key. -/
def forsSecretIndex (indices : Fors.Indices) (tree : Fin forsTrees) :
    Fin (forsTrees * 2 ^ forsHeight) :=
  ⟨tree.val * 2 ^ forsHeight + (indices tree).val, by
    have hindex := (indices tree).isLt
    have htree := tree.isLt
    calc tree.val * 2 ^ forsHeight + (indices tree).val
        < tree.val * 2 ^ forsHeight + 2 ^ forsHeight := by omega
      _ = (tree.val + 1) * 2 ^ forsHeight := by ring
      _ ≤ forsTrees * 2 ^ forsHeight := Nat.mul_le_mul_right _ (by omega)⟩

/-- The node an honest FORS signature's secret discloses. -/
def forsSecretNode (key : ForsKey) (indices : Fors.Indices) (tree : Fin forsTrees) :
    StructuralNode :=
  .forsPrf key (forsSecretIndex indices tree)

/-- The node an honest FORS signature's authentication path discloses at one level. -/
def forsAuthNode (key : ForsKey) (indices : Fors.Indices) (tree : Fin forsTrees)
    (level : Fin forsHeight) : StructuralNode :=
  .forsTree key ⟨level.val, by have := level.isLt; omega⟩
    ⟨tree.val * 2 ^ (forsHeight - level.val) +
      Nat.xor ((indices tree).val / 2 ^ level.val) 1, by
        have hlevel := level.isLt
        have htree := tree.isLt
        have hsibling : Nat.xor ((indices tree).val / 2 ^ level.val) 1 <
            2 ^ (forsHeight - level.val) := by
          refine xor_one_lt _ _ (by omega) (Nat.div_lt_of_lt_mul ?_)
          rw [← pow_add, Nat.add_sub_cancel' (le_of_lt level.isLt)]
          exact (indices tree).isLt
        calc tree.val * 2 ^ (forsHeight - level.val) +
              Nat.xor ((indices tree).val / 2 ^ level.val) 1
            < tree.val * 2 ^ (forsHeight - level.val) + 2 ^ (forsHeight - level.val) := by omega
          _ = (tree.val + 1) * 2 ^ (forsHeight - level.val) := by ring
          _ ≤ forsTrees * 2 ^ (forsHeight - level.val) := Nat.mul_le_mul_right _ (by omega)⟩

/-- **An honest FORS signature's secret is the cell at its own node.** -/
theorem fors_sign_secret_cell (cache : QueryCache HashSpec) (indices : Fors.Indices)
    (secretSeed publicSeed : Digest) (key : ForsKey) (tree : Fin forsTrees) :
    (@Fors.sign Id _ (replayQuery cache) indices secretSeed publicSeed key.address tree).secret =
      replayCells cache secretSeed publicSeed (.structural (forsSecretNode key indices tree)) := by
  rw [fors_sign_entry]
  exact @fors_secret_cell (replayQuery cache) secretSeed publicSeed key
    (forsSecretIndex indices tree)

/-- **An honest FORS signature's authentication path is cells.** -/
theorem fors_sign_authentication_cell (cache : QueryCache HashSpec) (indices : Fors.Indices)
    (secretSeed publicSeed : Digest) (key : ForsKey) (tree : Fin forsTrees)
    (level : Fin forsHeight) :
    (@Fors.sign Id _ (replayQuery cache) indices secretSeed publicSeed
        key.address tree).authentication level =
      replayCells cache secretSeed publicSeed
        (.structural (forsAuthNode key indices tree level)) := by
  rw [fors_sign_entry]
  rfl

/-- The compression of the fourteen roots consults its own canonical input. -/
theorem canonical_forsRoots (cache : QueryCache HashSpec)
    (secretSeed publicSeed : Digest) (key : ForsKey) :
    Canonical publicSeed (replayCells cache secretSeed publicSeed)
      (Hashing.tweakableInput publicSeed
        { key.address.setTypeAndClear .forsRoots with keyPair := key.address.keyPair }
        (digestArrayBytes fun tree : Fin forsTrees =>
          @Fors.node Id _ (replayQuery cache) secretSeed publicSeed key.address forsHeight
            tree.val)) := by
  refine ⟨.forsRoots key, ?_⟩
  simp only [canonicalInput,
    show (StructuralNode.forsRoots key).children =
      List.ofFn (fun tree : Fin forsTrees =>
        Node.structural (.forsTree key ⟨forsHeight, by omega⟩ ⟨tree.val, by simp⟩))
      from rfl,
    childBytes_ofFn]
  rfl

/-- One honest FORS tree's recomputation is a path fold over that tree's honest nodes. -/
theorem fors_combine_eq (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (key : ForsKey) (indices : Fors.Indices) (signature : ForsSignature)
    (hauth : ∀ (tree : Fin forsTrees) (level : Fin forsHeight),
      (signature tree).authentication level =
        @Fors.node Id _ (replayQuery cache) secretSeed publicSeed key.address level.val
          (tree.val * 2 ^ (forsHeight - level.val) +
            Nat.xor ((indices tree).val / 2 ^ level.val) 1))
    (tree : Fin forsTrees) (value : Digest) (step : Fin forsHeight) :
    (Hashing.tweakable (m := OracleComp HashSpec) publicSeed
        (Fors.nodeAddress key.address (step.val + 1)
          ((tree.val * 2 ^ forsHeight + (indices tree).val) / 2 ^ (step.val + 1)))
        (if (indices tree).val / 2 ^ step.val % 2 = 0 then
          bytesBE n value ++ bytesBE n ((signature tree).authentication step)
         else bytesBE n ((signature tree).authentication step) ++ bytesBE n value)) =
      Hashing.shortHash (pathInput publicSeed (Fors.nodeAddress key.address)
        (@Fors.node Id _ (replayQuery cache) secretSeed publicSeed key.address)
        (tree.val * 2 ^ forsHeight + (indices tree).val) value step.val) := by
  have hstep := step.isLt
  have hdiv : (tree.val * 2 ^ forsHeight + (indices tree).val) / 2 ^ step.val =
      tree.val * 2 ^ (forsHeight - step.val) + (indices tree).val / 2 ^ step.val :=
    Correctness.offset_div_pow _ _ _ _ (le_of_lt hstep)
  have heven : (tree.val * 2 ^ (forsHeight - step.val)) % 2 = 0 :=
    Correctness.offset_even tree.val forsHeight step.val hstep
  have hxor : Nat.xor ((tree.val * 2 ^ forsHeight + (indices tree).val) / 2 ^ step.val) 1 =
      tree.val * 2 ^ (forsHeight - step.val) +
        Nat.xor ((indices tree).val / 2 ^ step.val) 1 := by
    rw [hdiv]; exact Correctness.xor_add_even _ _ heven
  have hparity : (tree.val * 2 ^ forsHeight + (indices tree).val) / 2 ^ step.val % 2 =
      (indices tree).val / 2 ^ step.val % 2 := by
    rw [hdiv]; simp [Nat.add_mod, heven]
  simp only [pathInput, Hashing.tweakable, hparity, hxor, hauth]

/-- The index of the leaf an honest FORS signature opens, within its own tree. -/
theorem fors_leaf_lt (indices : Fors.Indices) (tree : Fin forsTrees) :
    tree.val * 2 ^ forsHeight + (indices tree).val < forsTrees * 2 ^ forsHeight := by
  have := (indices tree).isLt
  have := tree.isLt
  calc tree.val * 2 ^ forsHeight + (indices tree).val
      < tree.val * 2 ^ forsHeight + 2 ^ forsHeight := by omega
    _ = (tree.val + 1) * 2 ^ forsHeight := by ring
    _ ≤ forsTrees * 2 ^ forsHeight := Nat.mul_le_mul_right _ (by omega)

theorem fors_leaf_div (indices : Fors.Indices) (tree : Fin forsTrees) :
    (tree.val * 2 ^ forsHeight + (indices tree).val) / 2 ^ forsHeight = tree.val := by
  rw [Correctness.offset_div_pow _ _ _ _ (Nat.le_refl _), Nat.sub_self, pow_zero,
    Nat.mul_one, Nat.div_eq_of_lt (indices tree).isLt, Nat.add_zero]

set_option maxRecDepth 8000 in
/-- **Recovering the FORS public key from an honest signature consults only canonical
inputs.** -/
theorem probes_fors_publicKeyFromSignature (cache : QueryCache HashSpec)
    (secretSeed publicSeed : Digest) (key : ForsKey) (indices : Fors.Indices)
    (signature : ForsSignature)
    (hsecret : ∀ tree : Fin forsTrees, (signature tree).secret =
      @Fors.secret Id _ (replayQuery cache) secretSeed publicSeed key.address
        (tree.val * 2 ^ forsHeight + (indices tree).val))
    (hauth : ∀ (tree : Fin forsTrees) (level : Fin forsHeight),
      (signature tree).authentication level =
        @Fors.node Id _ (replayQuery cache) secretSeed publicSeed key.address level.val
          (tree.val * 2 ^ (forsHeight - level.val) +
            Nat.xor ((indices tree).val / 2 ^ level.val) 1)) :
    Probes cache
      (Fors.publicKeyFromSignature (m := OracleComp HashSpec) signature indices publicSeed
        key.address)
      (Canonical publicSeed (replayCells cache secretSeed publicSeed)) := by
  refine probes_bind cache _ _ _
    (fun tree : Fin forsTrees => @Fors.node Id _ (replayQuery cache) secretSeed publicSeed
      key.address forsHeight tree.val) ?_ ?_ ?_
  · rw [VerifierNaturality.sequenceFin_simulate]
    simp only [Correctness.sequenceFin_id, simulateQ_bind]
    funext tree
    refine (replay_pathFold_of_eq cache publicSeed (Fors.nodeAddress key.address)
      (@Fors.node Id _ (replayQuery cache) secretSeed publicSeed key.address)
      (tree.val * 2 ^ forsHeight + (indices tree).val) (fun _ _ => rfl) forsHeight _ _
      (fors_combine_eq cache secretSeed publicSeed key indices signature hauth tree)
      (by rw [hsecret tree, tweakable_replay]; rfl)).trans ?_
    rw [fors_leaf_div]
  · refine probes_sequenceFin cache _ forsTrees _ fun tree => ?_
    refine probes_tweakable cache publicSeed
      (Fors.nodeAddress key.address 0 (tree.val * 2 ^ forsHeight + (indices tree).val))
      (bytesBE n ((signature tree).secret)) _ _ ?_ ?_
    · rw [hsecret tree]
      exact canonical_forsLeaf cache secretSeed publicSeed key _ (fors_leaf_lt indices tree)
    refine probes_pathFold_of_eq cache publicSeed (Fors.nodeAddress key.address)
      (@Fors.node Id _ (replayQuery cache) secretSeed publicSeed key.address)
      (tree.val * 2 ^ forsHeight + (indices tree).val) (fun _ _ => rfl) forsHeight _ _ _
      (fors_combine_eq cache secretSeed publicSeed key indices signature hauth tree)
      (by rw [hsecret tree]; rfl) ?_
    intro level hlevel
    refine canonical_forsNode cache secretSeed publicSeed key level _ hlevel ?_
    have hdiv : (tree.val * 2 ^ forsHeight + (indices tree).val) / 2 ^ (level + 1) =
        tree.val * 2 ^ (forsHeight - (level + 1)) +
          (indices tree).val / 2 ^ (level + 1) :=
      Correctness.offset_div_pow _ _ _ _ hlevel
    have hinner : (indices tree).val / 2 ^ (level + 1) < 2 ^ (forsHeight - (level + 1)) := by
      refine Nat.div_lt_of_lt_mul ?_
      rw [← pow_add, Nat.add_sub_cancel' hlevel]
      exact (indices tree).isLt
    have htree := tree.isLt
    rw [hdiv]
    calc tree.val * 2 ^ (forsHeight - (level + 1)) + (indices tree).val / 2 ^ (level + 1)
        < tree.val * 2 ^ (forsHeight - (level + 1)) +
            2 ^ (forsHeight - (level + 1)) := by omega
      _ = (tree.val + 1) * 2 ^ (forsHeight - (level + 1)) := by ring
      _ ≤ forsTrees * 2 ^ (forsHeight - (level + 1)) := Nat.mul_le_mul_right _ (by omega)
  · exact probes_tweakable_self cache publicSeed _ _ _
      (canonical_forsRoots cache secretSeed publicSeed key)

/-! ## The hypertree side of signing

Each of the seven layers signs the root below it with one XMSS subtree, and — except at the
top — recovers that subtree's root again to feed the layer above. Both halves consult only
canonical inputs: an authentication node is a `.tree` or `.wotsPk` coordinate, a disclosed
chain value a `.wotsHash` one, and the recovery walks the very same coordinates back up.

The message a layer signs chooses *which* chain values are disclosed, through the checksum
digits, but never which coordinates exist — so the probe argument needs nothing about the
message, and the root a layer recovers is the subtree's own cell whatever was signed. -/

theorem wots_publicKeyFromSignature_replay (cache : QueryCache HashSpec)
    (signature : WotsSignature) (message publicSeed : Digest) (address : Address) :
    (simulateQ (replay cache)
        (Wots.publicKeyFromSignature (m := OracleComp HashSpec) signature message publicSeed
          address) : Id Digest) =
      @Wots.publicKeyFromSignature Id _ (replayQuery cache) signature message publicSeed
        address :=
  @VerifierNaturality.wots_simulate Id _ _ (replay cache) (replayQuery cache) (fun _ => rfl)
    signature message publicSeed address

theorem merkle_sign_replay (cache : QueryCache HashSpec)
    (message secretSeed publicSeed : Digest) (address : Address)
    (leaf : Fin (2 ^ subtreeHeight)) :
    (simulateQ (replay cache)
        (Merkle.sign (m := OracleComp HashSpec) message secretSeed publicSeed address leaf)
      : Id XmssSignature) =
      @Merkle.sign Id _ (replayQuery cache) message secretSeed publicSeed address leaf :=
  @Correctness.Naturality.merkle_sign_simulate Id _ _ (replay cache) (replayQuery cache)
    (fun _ => rfl) message secretSeed publicSeed address leaf

theorem merkle_publicKeyFromSignature_replay (cache : QueryCache HashSpec)
    (leaf : Fin (2 ^ subtreeHeight)) (signature : XmssSignature)
    (message publicSeed : Digest) (address : Address) :
    (simulateQ (replay cache)
        (Merkle.publicKeyFromSignature (m := OracleComp HashSpec) leaf signature message
          publicSeed address) : Id Digest) =
      @Merkle.publicKeyFromSignature Id _ (replayQuery cache) leaf signature message publicSeed
        address :=
  @VerifierNaturality.merkle_simulate Id _ _ (replay cache) (replayQuery cache) (fun _ => rfl)
    leaf signature message publicSeed address

/-- One entry of an honest WOTS signature. -/
theorem wots_sign_entry (cache : QueryCache HashSpec) (message secretSeed publicSeed : Digest)
    (address : Address) (chain : Fin chains) :
    @Wots.sign Id _ (replayQuery cache) message secretSeed publicSeed address chain =
      @Wots.chain Id _ (replayQuery cache) publicSeed
        { address with chainOrHeight := BitVec.ofNat 32 chain.val } 0
        (Checksum.encode message chain).val
        (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
          (Wots.secretAddress address chain)) := by
  simp only [Wots.sign, Correctness.sequenceFin_id, bind]

/-- The WOTS half of an honest XMSS signature. -/
theorem merkle_sign_wots (cache : QueryCache HashSpec)
    (message secretSeed publicSeed : Digest) (address : Address)
    (leaf : Fin (2 ^ subtreeHeight)) :
    (@Merkle.sign Id _ (replayQuery cache) message secretSeed publicSeed address leaf).wots =
      @Wots.sign Id _ (replayQuery cache) message secretSeed publicSeed
        (Merkle.wotsAddress address leaf.val) := by
  simp only [Merkle.sign, Correctness.sequenceFin_id, bind, pure]

/-- The authentication half of an honest XMSS signature. -/
theorem merkle_sign_authentication (cache : QueryCache HashSpec)
    (message secretSeed publicSeed : Digest) (address : Address)
    (leaf : Fin (2 ^ subtreeHeight)) (level : Fin subtreeHeight) :
    (@Merkle.sign Id _ (replayQuery cache) message secretSeed publicSeed address
        leaf).authentication level =
      @Merkle.node Id _ (replayQuery cache) secretSeed publicSeed address level.val
        (Nat.xor (leaf.val / 2 ^ level.val) 1) := by
  simp only [Merkle.sign, Correctness.sequenceFin_id, bind, pure]

theorem checksum_digit_le (message : Digest) (chain : Fin chains) :
    (Checksum.encode message chain).val ≤ w - 1 := by
  have := (Checksum.encode message chain).isLt
  simp only [w, winternitzBits] at *
  omega

/-- The sibling an authentication path discloses stays inside its own level. -/
theorem sibling_lt (height level index : Nat) (hlevel : level < height)
    (hindex : index < 2 ^ height) : Nat.xor (index / 2 ^ level) 1 < 2 ^ (height - level) := by
  refine xor_one_lt _ _ (by omega) (Nat.div_lt_of_lt_mul ?_)
  rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hlevel)]
  exact hindex

/-- **Signing a WOTS message consults only canonical inputs.** -/
theorem probes_wots_sign (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (key : WotsKey) (message : Digest) :
    Probes cache
      (Wots.sign (m := OracleComp HashSpec) message secretSeed publicSeed key.address)
      (Canonical publicSeed (replayCells cache secretSeed publicSeed)) := by
  refine probes_sequenceFin cache _ chains _ fun chain => ?_
  refine probes_tweakable cache publicSeed (Wots.secretAddress key.address chain)
    (bytesBE n secretSeed) _ _
    ⟨.wotsPrf key chain, (canonicalInput_wotsPrf cache secretSeed publicSeed key chain).symm⟩ ?_
  exact probes_chain cache secretSeed publicSeed key chain
    (Checksum.encode message chain).val 0 (by simpa using checksum_digit_le message chain)

/-- **Recovering a WOTS public key from an honest signature consults only canonical
inputs.** -/
theorem probes_wots_publicKeyFromSignature (cache : QueryCache HashSpec)
    (secretSeed publicSeed : Digest) (key : WotsKey) (message : Digest)
    (signature : WotsSignature)
    (hsignature : ∀ chain : Fin chains, signature chain =
      @Wots.chain Id _ (replayQuery cache) publicSeed
        { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0
        (Checksum.encode message chain).val
        (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
          (Wots.secretAddress key.address chain))) :
    Probes cache
      (Wots.publicKeyFromSignature (m := OracleComp HashSpec) signature message publicSeed
        key.address)
      (Canonical publicSeed (replayCells cache secretSeed publicSeed)) := by
  refine probes_bind cache _ _ _
    (fun chain : Fin chains => @Wots.chain Id _ (replayQuery cache) publicSeed
      { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 (w - 1)
      (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
        (Wots.secretAddress key.address chain))) ?_ ?_ ?_
  · rw [VerifierNaturality.sequenceFin_simulate]
    simp only [Correctness.sequenceFin_id, chain_replay]
    funext chain
    rw [hsignature chain]
    have hdigit := checksum_digit_le message chain
    simpa only [Nat.zero_add, Nat.add_sub_of_le hdigit] using
      (@Correctness.Wots.chain_add (replayQuery cache) publicSeed
        { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0
        (Checksum.encode message chain).val (w - 1 - (Checksum.encode message chain).val)
        (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
          (Wots.secretAddress key.address chain))).symm
  · refine probes_sequenceFin cache _ chains _ fun chain => ?_
    rw [hsignature chain]
    exact probes_chain cache secretSeed publicSeed key chain
      (w - 1 - (Checksum.encode message chain).val) (Checksum.encode message chain).val
      (by have := checksum_digit_le message chain; omega)
  · exact probes_tweakable_self cache publicSeed _ _ _
      ⟨.wotsPk key, (canonicalInput_wotsPk cache secretSeed publicSeed key).symm⟩

/-- An inner XMSS node's hash consults its own canonical input. -/
theorem canonical_merkleNode (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (tree : Tree) (level index : Nat) (hlevel : level < subtreeHeight)
    (hindex : index < 2 ^ (subtreeHeight - (level + 1))) :
    Canonical publicSeed (replayCells cache secretSeed publicSeed)
      (Hashing.tweakableInput publicSeed (Merkle.nodeAddress tree.address (level + 1) index)
        (bytesBE n (@Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address
            level (2 * index)) ++
          bytesBE n (@Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address
            level (2 * index + 1)))) :=
  ⟨.tree tree ⟨level, hlevel⟩ ⟨index, hindex⟩,
    (canonicalInput_tree cache secretSeed publicSeed tree ⟨level, hlevel⟩
      ⟨index, hindex⟩).symm⟩

/-- **Signing with an XMSS subtree consults only canonical inputs.** -/
theorem probes_merkle_sign (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (tree : Tree) (message : Digest) (leaf : Fin (2 ^ subtreeHeight)) :
    Probes cache
      (Merkle.sign (m := OracleComp HashSpec) message secretSeed publicSeed tree.address leaf)
      (Canonical publicSeed (replayCells cache secretSeed publicSeed)) := by
  refine probes_bind_replay cache _ _ _ ?_ ?_
  · refine probes_sequenceFin cache _ subtreeHeight _ fun level => ?_
    exact probes_merkle_node cache secretSeed publicSeed tree level.val (le_of_lt level.isLt)
      ⟨Nat.xor (leaf.val / 2 ^ level.val) 1,
        sibling_lt subtreeHeight level.val leaf.val level.isLt leaf.isLt⟩
  · exact probes_bind_replay cache _ _ _
      (probes_wots_sign cache secretSeed publicSeed ⟨tree, leaf⟩ message)
      (probes_pure cache _ _)

/-! ## The entries an XMSS signature discloses are cells

The same for a subtree. A signature's authentication path is the sibling at each level, which
is that node's own cell — a WOTS public key at the bottom of the subtree and a subtree node
above it, which `merkleNode` already distinguishes. Its WOTS half is the chain value at the
digit the message encodes, which is `wotsPosition`'s cell.

The WOTS entry is the one that forces the signer to read rather than ask: the value at the
digit is available, because the signature discloses it, while the value one step below it is
not, so no query answers for it. -/

/-- The sibling an honest XMSS signature discloses at one level. -/
def merkleAuthIndex (leaf : Fin (2 ^ subtreeHeight)) (level : Fin subtreeHeight) :
    Fin (2 ^ (subtreeHeight - level.val)) :=
  ⟨Nat.xor (leaf.val / 2 ^ level.val) 1,
    sibling_lt subtreeHeight level.val leaf.val level.isLt leaf.isLt⟩

/-- The node an honest XMSS signature's authentication path discloses at one level. -/
def merkleAuthNode (tree : Tree) (leaf : Fin (2 ^ subtreeHeight)) (level : Fin subtreeHeight) :
    StructuralNode :=
  merkleNode tree level.val (le_of_lt level.isLt) (merkleAuthIndex leaf level)

/-- **An honest XMSS signature's authentication path is cells.** -/
theorem merkle_sign_authentication_cell (cache : QueryCache HashSpec)
    (message secretSeed publicSeed : Digest) (tree : Tree) (leaf : Fin (2 ^ subtreeHeight))
    (level : Fin subtreeHeight) :
    (@Merkle.sign Id _ (replayQuery cache) message secretSeed publicSeed tree.address
        leaf).authentication level =
      replayCells cache secretSeed publicSeed
        (.structural (merkleAuthNode tree leaf level)) := by
  rw [merkle_sign_authentication]
  exact (@value_merkleNode (replayQuery cache) secretSeed publicSeed tree level.val
    (le_of_lt level.isLt) (merkleAuthIndex leaf level)).symm

/-- **An honest XMSS signature's WOTS half is cells**, one chain value apiece, at the digit the
message encodes. -/
theorem merkle_sign_wots_cell (cache : QueryCache HashSpec)
    (message secretSeed publicSeed : Digest) (tree : Tree) (leaf : Fin (2 ^ subtreeHeight))
    (chain : Fin chains) :
    (@Merkle.sign Id _ (replayQuery cache) message secretSeed publicSeed tree.address
        leaf).wots chain =
      replayCells cache secretSeed publicSeed
        (.structural (wotsPosition ⟨tree, leaf⟩ chain (Checksum.encode message chain))) := by
  rw [merkle_sign_wots,
    show Merkle.wotsAddress tree.address leaf.val = (⟨tree, leaf⟩ : WotsKey).address from rfl,
    @wots_sign_cells (replayQuery cache)]
  rfl

/-! ## The hypertree's layers, one peel at a time

The signer climbs the hypertree: it signs the incoming message with the subtree it is standing
in, recovers that subtree's root, and signs *that* at the layer above. So the layers are not
indexed by a closed-form coordinate; they are a recursion, and the statements below are the
recursion rather than a solution of it — the head layer's entries, and the tail as the same
climb one layer up with the recovered root as its message.

The recovered root is the subtree's own cell, so the message each layer signs is a cell too,
and an unprotected one: a `tree` node's children are subtree cells and WOTS public keys. The
only protected cell in sight is the chain value the WOTS half discloses, which is available
because the signature discloses it. -/

/-- The node an honest subtree's root is the cell at. -/
def subtreeRootNode (tree : Tree) : StructuralNode :=
  merkleNode tree subtreeHeight (le_refl subtreeHeight) ⟨0, by simp⟩

/-- **A subtree's root is the cell at its top node.** -/
theorem subtree_root_cell (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (tree : Tree) :
    @Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address subtreeHeight 0 =
      replayCells cache secretSeed publicSeed (.structural (subtreeRootNode tree)) :=
  (@value_merkleNode (replayQuery cache) secretSeed publicSeed tree subtreeHeight
    (le_refl subtreeHeight) ⟨0, by simp⟩).symm

/-- **One layer peeled off the climb.** -/
theorem signLayers_succ_eq (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (remaining layer tree : Nat) (leaf : Hypertree.LeafIndex) (message : Digest) :
    @Hypertree.signLayers Id _ (replayQuery cache) secretSeed publicSeed (remaining + 1) layer
        tree leaf message =
      Fin.cases (@Merkle.sign Id _ (replayQuery cache) message secretSeed publicSeed
          (Hypertree.address layer tree) leaf)
        (@Hypertree.signLayers Id _ (replayQuery cache) secretSeed publicSeed remaining
          (layer + 1) (tree / 2 ^ subtreeHeight) (Hypertree.nextLeaf tree)
          (@Merkle.publicKeyFromSignature Id _ (replayQuery cache) leaf
            (@Merkle.sign Id _ (replayQuery cache) message secretSeed publicSeed
              (Hypertree.address layer tree) leaf)
            message publicSeed (Hypertree.address layer tree))) := by
  cases remaining <;> rfl

/-- **The layer the signer is standing in** is the subtree signature it writes there. -/
theorem signLayers_head (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (remaining layer tree : Nat) (leaf : Hypertree.LeafIndex) (message : Digest) :
    @Hypertree.signLayers Id _ (replayQuery cache) secretSeed publicSeed (remaining + 1) layer
        tree leaf message 0 =
      @Merkle.sign Id _ (replayQuery cache) message secretSeed publicSeed
        (Hypertree.address layer tree) leaf := by
  rw [signLayers_succ_eq]
  simp only [Fin.cases_zero]

/-- **The layers above it** are the same climb, one layer up, with the subtree's own root as
the message. -/
theorem signLayers_tail (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (remaining layer tree : Nat) (leaf : Hypertree.LeafIndex) (message : Digest)
    (level : Fin remaining) :
    @Hypertree.signLayers Id _ (replayQuery cache) secretSeed publicSeed (remaining + 1) layer
        tree leaf message level.succ =
      @Hypertree.signLayers Id _ (replayQuery cache) secretSeed publicSeed remaining (layer + 1)
        (tree / 2 ^ subtreeHeight) (Hypertree.nextLeaf tree)
        (@Merkle.node Id _ (replayQuery cache) secretSeed publicSeed
          (Hypertree.address layer tree) subtreeHeight 0) level := by
  rw [signLayers_succ_eq]
  simp only [Fin.cases_succ]
  rw [@Correctness.Merkle.publicKeyFromSignature_sign (replayQuery cache) message
    secretSeed publicSeed (Hypertree.address layer tree) leaf]

/-- An honest XMSS path step, as a path fold over the subtree's honest nodes. -/
theorem merkle_combine_eq (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (tree : Tree) (leaf : Fin (2 ^ subtreeHeight)) (signature : XmssSignature)
    (hauth : ∀ level : Fin subtreeHeight, signature.authentication level =
      @Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address level.val
        (Nat.xor (leaf.val / 2 ^ level.val) 1))
    (value : Digest) (step : Fin subtreeHeight) :
    (Hashing.tweakable (m := OracleComp HashSpec) publicSeed
        (Merkle.nodeAddress tree.address (step.val + 1) (leaf.val / 2 ^ (step.val + 1)))
        (if leaf.val / 2 ^ step.val % 2 = 0 then
          bytesBE n value ++ bytesBE n (signature.authentication step)
         else bytesBE n (signature.authentication step) ++ bytesBE n value)) =
      Hashing.shortHash (pathInput publicSeed (Merkle.nodeAddress tree.address)
        (@Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address) leaf.val
        value step.val) := by
  simp only [pathInput, Hashing.tweakable, hauth]

set_option maxRecDepth 8000 in
/-- **Recovering an XMSS subtree's root from an honest signature consults only canonical
inputs.** -/
theorem probes_merkle_publicKeyFromSignature (cache : QueryCache HashSpec)
    (secretSeed publicSeed : Digest) (tree : Tree) (message : Digest)
    (leaf : Fin (2 ^ subtreeHeight)) (signature : XmssSignature)
    (hsignature : signature =
      @Merkle.sign Id _ (replayQuery cache) message secretSeed publicSeed tree.address leaf) :
    Probes cache
      (Merkle.publicKeyFromSignature (m := OracleComp HashSpec) leaf signature message
        publicSeed tree.address)
      (Canonical publicSeed (replayCells cache secretSeed publicSeed)) := by
  have hwots : ∀ chain : Fin chains, signature.wots chain =
      @Wots.chain Id _ (replayQuery cache) publicSeed
        { (WotsKey.mk tree leaf).address with chainOrHeight := BitVec.ofNat 32 chain.val } 0
        (Checksum.encode message chain).val
        (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
          (Wots.secretAddress (WotsKey.mk tree leaf).address chain)) := by
    intro chain
    rw [hsignature, merkle_sign_wots]
    exact wots_sign_entry cache message secretSeed publicSeed _ chain
  have hauth : ∀ level : Fin subtreeHeight, signature.authentication level =
      @Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address level.val
        (Nat.xor (leaf.val / 2 ^ level.val) 1) := by
    intro level
    rw [hsignature]
    exact merkle_sign_authentication cache message secretSeed publicSeed tree.address leaf level
  refine probes_bind cache _ _ _
    (@Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address 0 leaf.val)
    ?_ ?_ ?_
  · rw [wots_publicKeyFromSignature_replay, hsignature, merkle_sign_wots,
      @Correctness.Wots.publicKeyFromSignature_sign (replayQuery cache) message secretSeed
        publicSeed (Merkle.wotsAddress tree.address leaf.val)]
    rfl
  · exact probes_wots_publicKeyFromSignature cache secretSeed publicSeed ⟨tree, leaf⟩ message
      signature.wots hwots
  · refine probes_pathFold_of_eq cache publicSeed (Merkle.nodeAddress tree.address)
      (@Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address) leaf.val
      (fun _ _ => rfl) subtreeHeight _ _ _
      (merkle_combine_eq cache secretSeed publicSeed tree leaf signature hauth) rfl ?_
    intro level hlevel
    refine canonical_merkleNode cache secretSeed publicSeed tree level _ hlevel ?_
    exact Nat.div_lt_of_lt_mul (by rw [← pow_add, Nat.add_sub_cancel' hlevel]; exact leaf.isLt)

set_option maxRecDepth 8000 in
/-- **Signing down the hypertree consults only canonical inputs.** -/
theorem probes_hypertree_signLayers (cache : QueryCache HashSpec)
    (secretSeed publicSeed : Digest) :
    ∀ (remaining layer tree : Nat) (leaf : Hypertree.LeafIndex) (message : Digest),
      layer + remaining ≤ layers → tree < 2 ^ (totalHeight - subtreeHeight) →
        Probes cache
          (Hypertree.signLayers (m := OracleComp HashSpec) secretSeed publicSeed remaining
            layer tree leaf message)
          (Canonical publicSeed (replayCells cache secretSeed publicSeed)) := by
  intro remaining
  induction remaining with
  | zero => intro _ _ _ _ _ _; exact probes_pure cache _ _
  | succ remaining ih =>
      intro layer tree leaf message hbound htree
      have hlayer : layer < layers := by omega
      have hdiv : tree / 2 ^ subtreeHeight < 2 ^ (totalHeight - subtreeHeight) :=
        lt_of_le_of_lt (Nat.div_le_self _ _) htree
      rw [Hypertree.signLayers]
      refine probes_bind cache _ _ _
        (@Merkle.sign Id _ (replayQuery cache) message secretSeed publicSeed
          (Hypertree.address layer tree) leaf)
        (merkle_sign_replay cache message secretSeed publicSeed
          (Hypertree.address layer tree) leaf)
        (probes_merkle_sign cache secretSeed publicSeed ⟨⟨layer, hlayer⟩, ⟨tree, htree⟩⟩
          message leaf) ?_
      cases remaining with
      | zero => exact probes_pure cache _ _
      | succ below =>
          refine probes_bind cache _ _ _
            (@Merkle.node Id _ (replayQuery cache) secretSeed publicSeed
              (Hypertree.address layer tree) subtreeHeight 0) ?_ ?_ ?_
          · rw [merkle_publicKeyFromSignature_replay,
              @Correctness.Merkle.publicKeyFromSignature_sign (replayQuery cache) message
                secretSeed publicSeed (Hypertree.address layer tree) leaf]
          · exact probes_merkle_publicKeyFromSignature cache secretSeed publicSeed
              ⟨⟨layer, hlayer⟩, ⟨tree, htree⟩⟩ message leaf _ rfl
          · exact probes_bind_replay cache _ _ _
              (ih (layer + 1) (tree / 2 ^ subtreeHeight) (Hypertree.nextLeaf tree) _
                (by omega) hdiv)
              (probes_pure cache _ _)

/-! ## Signing

Signing makes exactly two hash calls that are not graph coordinates, and both are
message-dependent: the randomizer `PRF_msg(SK.prf, PK.seed, M)` and the message digest
`H_msg(R, PK, M)`. Everything after them is the FORS signature at the coordinate the digest
selects, that signature's public key, and the hypertree path to the root — all canonical.

The two exceptions are determined by the secret key, the message, and the randomizer value the
cache gives, so `MessageProbe` names them without quantifying over anything. -/

/-- Every probe satisfying a stronger condition satisfies a weaker one. -/
theorem Probes.mono {α : Type} {cache : QueryCache HashSpec}
    {computation : OracleComp HashSpec α} {predicate stronger : Bytes → Prop}
    (hprobes : Probes cache computation stronger)
    (himplies : ∀ probe, stronger probe → predicate probe) :
    Probes cache computation predicate :=
  fun probe hprobe => himplies probe (hprobes probe hprobe)

/-- The randomizer the cache gives a signing request. -/
def replayRandomizer (cache : QueryCache HashSpec) (sk : SecretKey) (message : Bytes) :
    Digest :=
  Hashing.truncate (replay cache (Hashing.randomizerInput sk.prf sk.publicKey.seed message))

/-- The FORS key a message digest selects. -/
def forsKeyOf (digest : HashOutput) : ForsKey :=
  ⟨⟨(MessageDigest.treeIndex digest).toNat, (MessageDigest.treeIndex digest).isLt⟩,
    ⟨(MessageDigest.leafIndex digest).toNat, (MessageDigest.leafIndex digest).isLt⟩⟩

/-- The two message-dependent inputs signing consults that are not graph coordinates: the
randomizer's and the message digest's. -/
def MessageProbe (cache : QueryCache HashSpec) (sk : SecretKey) (message : Bytes)
    (probe : Bytes) : Prop :=
  probe = Hashing.randomizerInput sk.prf sk.publicKey.seed message ∨
    probe = Hashing.messageInput (replayRandomizer cache sk message) sk.publicKey message

set_option maxRecDepth 8000 in
/-- **Every input signing consults is canonical or one of its two message-dependent ones.** -/
theorem probes_signInternal (cache : QueryCache HashSpec) (sk : SecretKey) (message : Bytes) :
    Probes cache (Scheme.signInternal (m := OracleComp HashSpec) sk message)
      (fun probe =>
        Canonical sk.publicKey.seed (replayCells cache sk.seed sk.publicKey.seed) probe ∨
          MessageProbe cache sk message probe) := by
  refine probes_shortHash cache (Hashing.randomizerInput sk.prf sk.publicKey.seed message) _ _
    (Or.inr (Or.inl rfl)) ?_
  refine probes_hash cache
    (Hashing.messageInput (replayRandomizer cache sk message) sk.publicKey message) _ _
    (Or.inr (Or.inr rfl)) ?_
  generalize (replay cache
    (Hashing.messageInput (replayRandomizer cache sk message) sk.publicKey message)) = digest
  refine probes_bind cache _ _ _
    (@Fors.sign Id _ (replayQuery cache) (MessageDigest.forsIndices digest) sk.seed
      sk.publicKey.seed (forsKeyOf digest).address)
    (fors_sign_replay cache (MessageDigest.forsIndices digest) sk.seed sk.publicKey.seed
      (forsKeyOf digest).address)
    (Probes.mono (probes_fors_sign cache sk.seed sk.publicKey.seed (forsKeyOf digest)
      (MessageDigest.forsIndices digest)) fun _ hprobe => Or.inl hprobe) ?_
  refine probes_bind_replay cache _ _ _
    (Probes.mono (probes_fors_publicKeyFromSignature cache sk.seed sk.publicKey.seed
      (forsKeyOf digest) (MessageDigest.forsIndices digest) _
      (fun _ => by rw [fors_sign_entry]) (fun _ _ => by rw [fors_sign_entry]))
      fun _ hprobe => Or.inl hprobe) ?_
  refine probes_bind_replay cache _ _ _
    (Probes.mono (probes_hypertree_signLayers cache sk.seed sk.publicKey.seed layers 0
      (MessageDigest.treeIndex digest).toNat (MessageDigest.leafIndex digest).toFin _
      (by omega) (MessageDigest.treeIndex digest).isLt)
      fun _ hprobe => Or.inl hprobe) ?_
  exact probes_pure cache _ _

/-! ## The request, not the frame

The oracle is asked about a *request*; the signer works on its frame, which is partial. An
overlong context is rejected before any query, and a served request consults only what signing
its own frame consults. Keeping the two apart is what lets a cached probe be traced back to a
request rather than to a byte string. -/

/-- **A rejected request makes no query at all.** -/
theorem probes_sign_none (cache : QueryCache HashSpec) (sk : SecretKey) (request : Message)
    (hframe : request.frame = none) (predicate : Bytes → Prop) :
    Probes cache (Scheme.sign (m := OracleComp HashSpec) sk request) predicate := by
  rw [Scheme.sign, hframe]
  exact probes_pure cache _ _

/-- **A served request consults only canonical inputs and the two its own frame names.** -/
theorem probes_sign (cache : QueryCache HashSpec) (sk : SecretKey) (request : Message)
    (message : Bytes) (hframe : request.frame = some message) :
    Probes cache (Scheme.sign (m := OracleComp HashSpec) sk request)
      (fun probe =>
        Canonical sk.publicKey.seed (replayCells cache sk.seed sk.publicKey.seed) probe ∨
          MessageProbe cache sk message probe) := by
  rw [Scheme.sign, hframe]
  exact probes_bind_replay cache _ _ _ (probes_signInternal cache sk message)
    (probes_pure cache _ _)

/-! ## In the walk's cache

The walk leaves `CanonicalGraph.Programming.cacheFrom` at the cells its own outputs determine.
Those are the cells the cache itself computes, so the canonical inputs key generation consults
are exactly entries the walk installed — and running key generation from that cache samples
nothing and changes nothing. -/

/-- The cache a completed graph walk leaves behind. -/
noncomputable def warmCache (publicSeed secretSeed : Digest)
    (outputs : Programming.Outputs) : QueryCache HashSpec :=
  Programming.cacheFrom publicSeed (Programming.cellsOfOutputs secretSeed outputs) outputs
    Programming.order ∅

/-- The walk's cache computes the cells the walk itself produced. -/
theorem replayCells_warmCache (publicSeed secretSeed : Digest)
    (outputs : Programming.Outputs) :
    replayCells (warmCache publicSeed secretSeed outputs) secretSeed publicSeed =
      Programming.cellsOfOutputs secretSeed outputs :=
  @Programming.value_eq_of_cache_agreement
    (replayQuery (warmCache publicSeed secretSeed outputs)) publicSeed secretSeed outputs
    (fun input output hentry =>
      hash_replayQuery (warmCache publicSeed secretSeed outputs) input output hentry)

/-- **A canonical input is in the walk's cache.** -/
theorem warmCache_ne_none (publicSeed secretSeed : Digest)
    (outputs : Programming.Outputs) (probe : Bytes)
    (hprobe : Canonical publicSeed
      (replayCells (warmCache publicSeed secretSeed outputs) secretSeed publicSeed) probe) :
    warmCache publicSeed secretSeed outputs probe ≠ none := by
  obtain ⟨parent, rfl⟩ := hprobe
  rw [replayCells_warmCache]
  show Programming.cacheFrom publicSeed (Programming.cellsOfOutputs secretSeed outputs) outputs
      Programming.order ∅
      (canonicalInput publicSeed (Programming.cellsOfOutputs secretSeed outputs) parent) ≠ none
  rw [Programming.full_cache_lookup]
  exact Option.some_ne_none _

/-- **Every input key generation consults is in the walk's cache.** -/
theorem keygenInternal_probes_cached (publicSeed secretSeed prfSeed : Digest)
    (outputs : Programming.Outputs) (probe : Bytes)
    (hprobe : QueriesUnder (warmCache publicSeed secretSeed outputs)
      (Scheme.keygenInternal (m := OracleComp HashSpec) secretSeed prfSeed publicSeed) probe) :
    warmCache publicSeed secretSeed outputs probe ≠ none :=
  warmCache_ne_none publicSeed secretSeed outputs probe
    (probes_keygenInternal (warmCache publicSeed secretSeed outputs) secretSeed prfSeed
      publicSeed probe hprobe)

/-- **Key generation, run from the walk's cache, is a pure computation.** It returns the keys
the cache already determines and leaves the cache exactly as it found it. -/
theorem run_keygenInternal_eq_pure (publicSeed secretSeed prfSeed : Digest)
    (outputs : Programming.Outputs) :
    (simulateQ randomOracle
        (Scheme.keygenInternal (m := OracleComp HashSpec) secretSeed prfSeed publicSeed)).run
        (warmCache publicSeed secretSeed outputs) =
      (pure (@Scheme.keygenInternal Id _
          (replayQuery (warmCache publicSeed secretSeed outputs)) secretSeed prfSeed publicSeed,
        warmCache publicSeed secretSeed outputs) :
        ProbComp ((SecretKey × PublicKey) × QueryCache HashSpec)) := by
  rw [CachedRun.run_eq_pure_of_cached _ _
    (keygenInternal_probes_cached publicSeed secretSeed prfSeed outputs), keygenInternal_replay]

/-! ## In the game's monad

The game's honest phase runs in `OracleComp OracleWorld`, which carries the coin oracle
alongside the hash. Key generation and signing flip no coins, so each is the lift of the
hash-only computation the statements above are about, and `KeygenUniform.rom` answers a
right-lifted computation through `randomOracle` alone. -/

theorem keygenInternal_lift (secretSeed prfSeed publicSeed : Digest) :
    (Scheme.keygenInternal (m := OracleComp OracleWorld) secretSeed prfSeed publicSeed) =
      OracleComp.liftComp
        (Scheme.keygenInternal (m := OracleComp HashSpec) secretSeed prfSeed publicSeed)
        OracleWorld :=
  (Correctness.Naturality.keygenInternal_simulate
    (fun input => query (spec := HashSpec) input : QueryImpl HashSpec (OracleComp OracleWorld))
    (fun _ => rfl) secretSeed prfSeed publicSeed).symm

/-- **Key generation in the game's monad, run from the walk's cache, is a pure computation.** -/
theorem run_keygenInternal_world_eq_pure (publicSeed secretSeed prfSeed : Digest)
    (outputs : Programming.Outputs) :
    (simulateQ KeygenUniform.rom
        (Scheme.keygenInternal (m := OracleComp OracleWorld) secretSeed prfSeed publicSeed)).run
        (warmCache publicSeed secretSeed outputs) =
      (pure (@Scheme.keygenInternal Id _
          (replayQuery (warmCache publicSeed secretSeed outputs)) secretSeed prfSeed publicSeed,
        warmCache publicSeed secretSeed outputs) :
        ProbComp ((SecretKey × PublicKey) × QueryCache HashSpec)) := by
  rw [keygenInternal_lift,
    show KeygenUniform.rom = unifFwdImpl HashSpec +
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) from rfl,
    QueryImpl.simulateQ_add_liftComp_right]
  exact run_keygenInternal_eq_pure publicSeed secretSeed prfSeed outputs

end SlhDsaSecurity.HonestProbes
