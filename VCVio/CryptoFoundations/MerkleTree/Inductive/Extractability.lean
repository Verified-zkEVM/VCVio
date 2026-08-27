/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Bolton Bailey
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Inductive.QueryBound
public import VCVio.OracleComp.QueryTracking.Collision
public import ToMathlib.Data.IndexedBinaryTree.Lemmas
import VCVio.OracleComp.QueryTracking.CachingLoggingOracle
import VCVio.OracleComp.QueryTracking.Unpredictability

/-!
# Inductive Merkle Tree Extractability

This file develops the deterministic extraction kernel for the inductive Merkle tree
commitment scheme and its random-oracle experiment. The extractor reconstructs a partial
tree from the committing adversary's query log and the opened root. The experiment runs
the committing, opening, and verification phases against one shared lazy random function.

## Main definitions

We make several definitions to set up and analyze the extractability game
under namespace `InductiveMerkleTree`:

* `Adversary`: a two-phase Merkle tree adversary, bundling an auxiliary state type, a
  committing phase producing a claimed root and state, and an opening phase producing a
  (leaf index, leaf value, authentication path) triple from that state.
* `extractor`: builds a `FullData (Option α) s` from a query log, root, and skeleton by
  walking down from the root and pulling each node's children from the unique log entry
  whose response matches.
* `extractabilityInner`: the oracle syntax running an `Adversary` against the extractor
  and verifier, before choosing random-oracle semantics.
* `extractabilityGame`: the random-oracle experiment obtained by interpreting
  `extractabilityInner` through one shared `cachingOracle` from the empty cache.
* `extractabilityROMErrorNumerator`: the unrelaxed finite maximum over the possible number
  of fresh commit inputs.
* `extractability_rom_bound`: the corresponding unconditional stopping-time ROM bound.
* `extractability_rom_bound_coarse`: the two-endpoint relaxation
  `(max(Tq, choose(q,2)) + T·depth)/|α|`, where `T = 2·leafCount - 1`.
* `extractability_rom_bound_birthday_dominates` and
  `extractability_rom_bound_quadratic`: source-shaped corollaries once the birthday term
  dominates the stopping branch.
* `ChainInLog`: structural predicate witnessing that a query log contains the hash chain
  from `root` down to `leaf` along the path determined by `idx`.

## Current proof boundary

This file proves deterministic extraction and collision lemmas, total-query bounds, and a
probabilistic extractability theorem for the shared-cache experiment. The ROM proof maintains
one combined cache/log state and inducts directly on the still-running commit computation.
For `m` remaining total adversary queries, `k` populated cache keys, and `c` future fresh
commit inputs, its per-branch energy is

`c·k + choose(c,2) + min(T, 2(k+c)+1)·(m-c+depth)`.

The potential is the finite supremum over `0 ≤ c ≤ m`. A cache miss pays the `k` collision
hazard and increments both `k` and `c`; a hit only consumes remaining budget. When commit
execution stops, the `c=0` branch pays the opening/verifier fresh-target hazard. Thus the proof
tracks fresh inputs directly and does not condition a birthday bound on an adaptively chosen
commit-trace length.

## Comparison with Chiesa–Yogev, Version 1.2

Lemma 18.5.1 of the official Version 1.2 source considers a perfect tree with `L` leaves,
`d = log₂ L`, a range of size `N`, and `q` total adversary queries across commit and opening;
checker queries are excluded from `q`. Its displayed bound is

`choose(q,2)/N + 2L(d+1)/N`,

with a further `q²/(2N)` simplification under `q ≥ 4L(d+1)`. The source proof first fixes
realized phase counts `q₁,q₂`, then bounds collision and fresh-hit events, obtaining the
intermediate maximum

`max(2L(q+d+1), choose(q,2)+2L(d+1))/N`.

The proof discards the first branch using `q ≥ 4L+1`. Version 1.1 stated this hypothesis;
Version 1.2's displayed lemma appears to omit it while retaining that proof step. More
fundamentally, applying the fixed-`q₁` birthday estimate after conditioning on an adaptively
chosen stopping time is not valid without an additional argument. The stopping-time induction
here supplies that argument. Its unrelaxed numerator has the same numerical form as the
source's pre-relaxation expression after aligning the raw-leaf model, but tracks fresh commit
inputs rather than treating a conditioned realized phase length as fixed. The machine-checked
coarse corollary keeps the necessary two-endpoint maximum unconditionally.

Every full binary `Skeleton` in this formalization has `T = 2L-1` nodes. Specializing to a
perfect skeleton, without a query hypothesis the finite maximum is not uniformly bounded by
Version 1.2's displayed single birthday endpoint; that is precisely the hypothesis omitted
from the v1.2 statement but retained in its proof. Under `q ≥ 2T+1 = 4L-1`, our coarse bound
becomes

`choose(q,2)/|α| + T·d/|α|`,

which is no weaker numerically than the source expression after aligning the models. The
constant difference is explained by the games: this file treats leaves as raw labels and the
verifier makes `d` internal-node hash calls, whereas the source hashes salted leaves and counts
`d+1` checker calls. Our quadratic corollary additionally assumes `2T·d ≤ q`; for a perfect
tree its two hypotheses are `q ≥ 4L-1` and `q ≥ (4L-2)d`. The source's single condition
`q ≥ 4L(d+1)` implies both, so the Lean corollary is no weaker in the aligned model.

This file also supports arbitrary full binary skeletons but formalizes a single-leaf opening
and deterministic `OracleComp` adversaries; the source permits randomized adversaries, subset
openings, and additionally states total-extractor and runtime guarantees. Those are model-scope
differences, not consequences of the probability proof established here.

## TODO

- The lemmas here all specialize to `(m := OracleComp (spec α))` because the proofs rely
  on `OracleComp`-specific machinery — `withQueryLog`, `simulateQ` support lemmas, and the
  `ChainInLog log` predicate over a concrete `QueryLog`. Generalizing them to an arbitrary
  monad `m` (so they apply to e.g. `SimulateQ` without re-proving) would first require a
  generic "computation-with-query-log" interface at the framework level,
  but might be good at some point.

## References

* [Chiesa–Yogev, *Building Cryptographic Proofs from Hash Functions*, Version 1.2,
  Lemma 18.5.1](https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L13186-L13211)
  and its [proof](https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L13264-L13455).
* [Version 1.1 statement carrying the `q ≥ 4L+1`
  hypothesis](https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/92deb71d65d4c75a34c98d2280d513c959b0ea35/snargs-book.tex#L11763-L11787).

-/

@[expose] public section

namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable {α : Type}

/-! ## Adversary -/

section Adversary

/-- An adversary in the Merkle tree extractability game, packaged as a single
two-phase object: a committing phase that produces a claimed root together with
auxiliary state, and an opening phase that consumes the auxiliary state to
produce a (leaf index, leaf value, authentication path) triple. -/
structure Adversary (α : Type) (s : Skeleton) where
  /-- Auxiliary state carried from the committing phase to the opening phase. -/
  AuxState : Type
  /-- Committing phase: produce a claimed root and auxiliary state. -/
  commit : OracleComp (spec α) (α × AuxState)
  /-- Opening phase: given the auxiliary state, produce a leaf index, claimed
  leaf value, and authentication path. -/
  opening : AuxState → OracleComp (spec α)
      ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth)

/-- The combined two-phase execution of `𝒜` has total query bound `qb`. -/
def Adversary.IsTwoPhaseTotalQueryBound {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ) : Prop :=
  IsTotalQueryBound
    (do
      let (_root, aux) ← 𝒜.commit
      let ⟨_idx, _leaf, _proof⟩ ← 𝒜.opening aux
      pure ())
    qb

end Adversary

/-! ## Extractability game -/

section ExtractabilityGame

variable [DecidableEq α]

/--
The child-decomposition function used by the Merkle-tree `extractor`. Given a `cache`
and a node value `a`, look up the first query in `cache` whose response is `a` and return
its input pair; if no such entry exists, return `none`.
-/
def extractorChildren (cache : (spec α).QueryLog) (a : α) : Option (α × α) :=
  match cache.find? (fun ⟨_, r⟩ => r == a) with
  | none => none
  | some ⟨(x, y), _⟩ => some (x, y)

/--
The extraction algorithm for Merkle trees: from a query log `cache`, a `root`, and a
skeleton `s`, build a partial tree of type `FullData (Option α) s` by walking down from
`root`. A node with value `some a` looks up the unique log entry whose response is `a`
and uses its input pair as the children's values; in every other case (no matching entry,
or the parent is already `none`) both children are `none`. Implemented as
`optionPopulateDown` driven by `extractorChildren`.
-/
def extractor (s : Skeleton) (cache : (spec α).QueryLog) (root : α) : FullData (Option α) s :=
  optionPopulateDown s (extractorChildren cache) root

/-- The labels of the non-dummy nodes that the extractor actually reconstructs. Unlike
the full query log, this list follows only response links reachable from the claimed root. -/
private def extractedTargets : (s : Skeleton) → (spec α).QueryLog → α → List α
  | .leaf, _, root => [root]
  | .internal sl sr, log, root =>
      root :: match extractorChildren log root with
        | none => []
        | some (left, right) =>
            extractedTargets sl log left ++ extractedTargets sr log right

/-- A full binary skeleton with `L` leaves has `2L - 1` nodes, so the extractor can
reconstruct at most that many non-dummy labels, independently of the query-log length. -/
private lemma extractedTargets_length_le (s : Skeleton)
    (log : (spec α).QueryLog) (root : α) :
    (extractedTargets s log root).length ≤ 2 * s.leafCount - 1 := by
  induction s generalizing root with
  | leaf => simp [extractedTargets]
  | internal sl sr ihl ihr =>
      simp only [extractedTargets, List.length_cons]
      cases hchildren : extractorChildren log root with
      | none =>
          simp only [List.length_nil]
          have hl := Skeleton.leafCount_pos sl
          have hr := Skeleton.leafCount_pos sr
          simp only [Skeleton.leafCount_internal]
          omega
      | some children =>
          obtain ⟨left, right⟩ := children
          simp only [List.length_append]
          have hl := ihl left
          have hr := ihr right
          have hsl := Skeleton.leafCount_pos sl
          have hsr := Skeleton.leafCount_pos sr
          simp only [Skeleton.leafCount_internal]
          omega

/-- Every extracted label is either the claimed root or one component of a logged hash
input. The statement tracks reachability, while forgetting the particular ancestor chain. -/
private lemma mem_extractedTargets_root_or_log_input (s : Skeleton)
    (log : (spec α).QueryLog) (root : α) {target : α}
    (htarget : target ∈ extractedTargets s log root) :
    target = root ∨ ∃ entry ∈ log, target = entry.1.1 ∨ target = entry.1.2 := by
  induction s generalizing root with
  | leaf =>
      simp only [extractedTargets, List.mem_singleton] at htarget
      exact Or.inl htarget
  | internal sl sr ihl ihr =>
      simp only [extractedTargets, List.mem_cons] at htarget
      rcases htarget with hroot | htarget
      · exact Or.inl hroot
      · cases hchildren : extractorChildren log root with
        | none => simp [hchildren] at htarget
        | some children =>
            obtain ⟨left, right⟩ := children
            simp only [hchildren, List.mem_append] at htarget
            unfold extractorChildren at hchildren
            cases hfind : log.find? (fun ⟨_, response⟩ => response == root) with
            | none => simp [hfind] at hchildren
            | some entry =>
                obtain ⟨⟨left', right'⟩, response⟩ := entry
                simp only [hfind, Option.some.injEq, Prod.mk.injEq] at hchildren
                obtain ⟨hleft, hright⟩ := hchildren
                subst left'
                subst right'
                have hentry : (⟨(left, right), response⟩ : (_ : α × α) × α) ∈ log :=
                  List.mem_of_find?_eq_some hfind
                rcases htarget with htarget | htarget
                · rcases ihl left htarget with hroot | hdeeper
                  · exact Or.inr ⟨⟨(left, right), response⟩, hentry, Or.inl hroot⟩
                  · exact Or.inr hdeeper
                · rcases ihr right htarget with hroot | hdeeper
                  · exact Or.inr ⟨⟨(left, right), response⟩, hentry, Or.inr hroot⟩
                  · exact Or.inr hdeeper

/-- If all logged inputs are populated in a finite key set, the distinct extracted labels
fit in the root plus the two coordinate images of that key set. -/
private lemma extractedTargets_toFinset_card_le_cacheKeys
    (s : Skeleton) (log : (spec α).QueryLog) (root : α)
    {cache : (spec α).QueryCache} (keys : Finset (α × α))
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hkeys : ∀ input, cache input ≠ none → input ∈ keys) :
    (extractedTargets s log root).toFinset.card ≤ 2 * keys.card + 1 := by
  let candidates : Finset α :=
    insert root (keys.image Prod.fst ∪ keys.image Prod.snd)
  have hsubset : (extractedTargets s log root).toFinset ⊆ candidates := by
    intro target htarget
    have htarget' : target ∈ extractedTargets s log root := by simpa using htarget
    rcases mem_extractedTargets_root_or_log_input s log root htarget' with rfl | hinput
    · exact Finset.mem_insert_self _ _
    · obtain ⟨entry, hentry, hside⟩ := hinput
      have hkey : entry.1 ∈ keys := hkeys entry.1 (by
        rw [hlogCache entry hentry]
        exact Option.some_ne_none _)
      rcases hside with hleft | hright
      · subst target
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨entry.1, hkey, rfl⟩))
      · subst target
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨entry.1, hkey, rfl⟩))
  calc
    (extractedTargets s log root).toFinset.card ≤ candidates.card :=
      Finset.card_le_card hsubset
    _ ≤ (keys.image Prod.fst ∪ keys.image Prod.snd).card + 1 := by
      simpa only [candidates, Nat.add_comm] using
        Finset.card_insert_le root (keys.image Prod.fst ∪ keys.image Prod.snd)
    _ ≤ (keys.image Prod.fst).card + (keys.image Prod.snd).card + 1 := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ 2 * keys.card + 1 := by
      have hfst := Finset.card_image_le (s := keys) (f := Prod.fst)
      have hsnd := Finset.card_image_le (s := keys) (f := Prod.snd)
      omega

/--
The oracle syntax underlying the extractability experiment. It runs the committing
adversary, snapshots that phase's query log for the extractor, runs the opening adversary,
and finally verifies the opening. Random-function consistency is supplied separately by
`extractabilityGame`.
-/
def extractabilityInner {s : Skeleton} (𝒜 : Adversary α s) :
    OracleComp (spec α) (α × 𝒜.AuxState ×
        ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
         FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) :=
  do
    let ((root, aux), queryLog) ← 𝒜.commit.withQueryLog
    let extractedTree := extractor s queryLog root
    let ⟨idx, leaf, proof⟩ ← 𝒜.opening aux
    let extractedProof := generateProof extractedTree idx
    let verified ← verifyProof idx leaf root proof
    return (root, aux, ⟨idx, leaf, proof, extractedTree, extractedProof, verified⟩)

/-- The opening-and-verification suffix after fixing a logged commit outcome. This is the
actual cached continuation used in the ROM proof; it does not resample or reset the oracle. -/
private def extractabilityRest {s : Skeleton} (𝒜 : Adversary α s)
    (root : α) (aux : 𝒜.AuxState) (queryLog : (spec α).QueryLog) :
    OracleComp (spec α) (α × 𝒜.AuxState ×
        ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
         FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) :=
  do
    let extractedTree := extractor s queryLog root
    let ⟨idx, leaf, proof⟩ ← 𝒜.opening aux
    let extractedProof := generateProof extractedTree idx
    let verified ← verifyProof idx leaf root proof
    return (root, aux, ⟨idx, leaf, proof, extractedTree, extractedProof, verified⟩)

/-- Execute a still-running commit computation with a combined cache/log state, then run the
opening-and-verification suffix from the resulting state. This is the induction object for the
stopping-time proof: its query budget decreases structurally, without conditioning on a
realized commit length. -/
private def extractabilityRunFrom {s : Skeleton} (𝒜 : Adversary α s)
    (commit : OracleComp (spec α) (α × 𝒜.AuxState))
    (cache : (spec α).QueryCache) (log : (spec α).QueryLog) :=
  (simulateQ (spec α).cachingLoggingOracle commit).run (cache, log) >>= fun z =>
    (simulateQ (spec α).cachingOracle
      (extractabilityRest 𝒜 z.1.1 z.1.2 z.2.2)).run z.2.1

/-- Exact stopping-time contribution after `commitMisses` further fresh commit inputs:
collision hazard against the `cached` previous keys, birthday collisions among the new cache
entries, and the remaining opening/verifier fresh-target hazard. Cache hits consume the
remaining total-query budget without increasing `commitMisses`. -/
private def extractabilityEnergy (treeTargetCount depth remaining cached commitMisses : ℕ) : ℕ :=
  commitMisses * cached + commitMisses.choose 2 +
    min treeTargetCount (2 * (cached + commitMisses) + 1) *
      (remaining - commitMisses + depth)

/-- Finite maximum over every possible number of further fresh commit inputs/cache misses. -/
private def extractabilityExactPotential
  (treeTargetCount depth remaining cached : ℕ) : ℕ :=
  (Finset.range (remaining + 1)).sup fun commitMisses =>
    extractabilityEnergy treeTargetCount depth remaining cached commitMisses

private lemma extractabilityEnergy_zero
    (treeTargetCount depth remaining cached : ℕ) :
    extractabilityEnergy treeTargetCount depth remaining cached 0 =
      min treeTargetCount (2 * cached + 1) * (remaining + depth) := by
  simp [extractabilityEnergy]

private lemma extractabilityEnergy_hit_le
    (treeTargetCount depth remaining cached commitMisses : ℕ) :
    extractabilityEnergy treeTargetCount depth (remaining - 1) cached commitMisses ≤
      extractabilityEnergy treeTargetCount depth remaining cached commitMisses := by
  unfold extractabilityEnergy
  gcongr
  omega

private lemma extractabilityEnergy_miss_eq
    (treeTargetCount depth remaining cached commitMisses : ℕ)
    (hcommit : commitMisses < remaining) :
    cached + extractabilityEnergy treeTargetCount depth (remaining - 1) (cached + 1)
        commitMisses =
      extractabilityEnergy treeTargetCount depth remaining cached (commitMisses + 1) := by
  have hcap :
      min treeTargetCount (2 * (cached + 1 + commitMisses) + 1) =
        min treeTargetCount (2 * (cached + (commitMisses + 1)) + 1) := by
    congr 2
    omega
  have hremaining' : remaining - 1 - commitMisses = remaining - (commitMisses + 1) := by
    omega
  have hchoose : (commitMisses + 1).choose 2 =
      commitMisses + commitMisses.choose 2 := by
    rw [show commitMisses + 1 = commitMisses.succ by omega, Nat.choose_succ_succ]
    simp
  unfold extractabilityEnergy
  rw [hcap, hremaining', hchoose]
  simp only [Nat.mul_succ, Nat.succ_mul]
  omega

private lemma extractabilityExactPotential_terminal_le
    (treeTargetCount depth remaining cached : ℕ) :
    min treeTargetCount (2 * cached + 1) * (remaining + depth) ≤
      extractabilityExactPotential treeTargetCount depth remaining cached := by
  rw [← extractabilityEnergy_zero]
  exact Finset.le_sup (by simp)

private lemma extractabilityExactPotential_hit_le
    (treeTargetCount depth remaining cached : ℕ) :
    extractabilityExactPotential treeTargetCount depth (remaining - 1) cached ≤
      extractabilityExactPotential treeTargetCount depth remaining cached := by
  unfold extractabilityExactPotential
  apply Finset.sup_le
  intro commitMisses hcommit
  apply (extractabilityEnergy_hit_le treeTargetCount depth remaining cached commitMisses).trans
  apply Finset.le_sup
  simp only [Finset.mem_range] at hcommit ⊢
  omega

private lemma extractabilityExactPotential_miss_le
    (treeTargetCount depth remaining cached : ℕ) (hremaining : 0 < remaining) :
    cached + extractabilityExactPotential treeTargetCount depth (remaining - 1) (cached + 1) ≤
      extractabilityExactPotential treeTargetCount depth remaining cached := by
  unfold extractabilityExactPotential
  rw [Finset.add_sup (by simp)]
  apply Finset.sup_le
  intro commitMisses hcommit
  rw [extractabilityEnergy_miss_eq treeTargetCount depth remaining cached commitMisses
    (by
      simp only [Finset.mem_range] at hcommit
      omega)]
  apply Finset.le_sup
  simp only [Finset.mem_range] at hcommit ⊢
  omega

private lemma extractabilityInner_eq_commit_bind_rest {s : Skeleton} (𝒜 : Adversary α s) :
    extractabilityInner 𝒜 =
      𝒜.commit.withQueryLog >>= fun x => extractabilityRest 𝒜 x.1.1 x.1.2 x.2 := by
  simp [extractabilityInner, extractabilityRest]

/--
The extraction-failure event on an `extractabilityInner` transcript: verification passes
but the extracted leaf or authentication proof does not match the adversary's opening. This
is the single-leaf specialization of Merkle extractability, and compares the full authentication
path at that leaf.
-/
def AdversaryWinsExtractabilityInner {s : Skeleton} {AuxState : Type} :
    α × AuxState ×
      ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
       FullData (Option α) s × List.Vector (Option α) idx.depth × Bool) → Prop
  | (_, _, ⟨idx, leaf, proof, extractedTree, extractedProof, verified⟩) =>
    verified = true ∧
      (some leaf ≠ extractedTree.get idx.toNodeIndex ∨
        proof.toList.map some ≠ extractedProof.toList)

/-- The Merkle-tree extractability experiment in the random-oracle model. All queries made
by the committing adversary, opening adversary, and verifier are interpreted through one
shared cache, so repeated equal inputs receive the same answer. -/
def extractabilityGame {s : Skeleton} (𝒜 : Adversary α s) :
    OracleComp (spec α) (α × 𝒜.AuxState ×
        ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
         FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) :=
  (spec α).withCacheOverlay ∅ (extractabilityInner 𝒜)

/-- The extraction-failure event for `extractabilityGame`. -/
def AdversaryWinsExtractabilityGame {s : Skeleton} {AuxState : Type} :
    α × AuxState ×
      ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
       FullData (Option α) s × List.Vector (Option α) idx.depth × Bool) → Prop :=
  AdversaryWinsExtractabilityInner

/-- If the query log's first entry with response `root` is the pair `⟨(x, y), root⟩`,
then the extractor at an internal skeleton unfolds to that node's two children using
`x` and `y` as the new "ancestor" values for the left and right subtrees. -/
private lemma extractor_internal_eq_of_find?_eq
    (sl sr : Skeleton) (log : (spec α).QueryLog) (root x y : α)
    (h_find : log.find? (fun ⟨_, r⟩ => r == root) = some ⟨(x, y), root⟩) :
    extractor (Skeleton.internal sl sr) log root =
      FullData.internal (some root) (extractor sl log x) (extractor sr log y) := by
  simp only [extractor, optionPopulateDown_internal, extractorChildren, h_find]
  rfl

/--
Unfold `extractabilityInner` into a nested `bind` whose outer prefix logs the committing
adversary's queries alongside the opening adversary's output, and whose continuation runs
`verifyProof` and assembles the transcript. This is the definitional rearrangement used to
expose the prefix as a target for query-bound reasoning.
-/
private lemma extractabilityInner_eq_bind_verifyProof
    {s : Skeleton} (𝒜 : Adversary α s) :
    extractabilityInner 𝒜 =
      (𝒜.commit.withQueryLog >>= fun ((root, aux), queryLog) =>
        𝒜.opening aux >>= fun q => pure (((root, aux), queryLog), q)) >>=
      fun (⟨⟨root, aux⟩, queryLog⟩, ⟨idx, leaf, proof⟩) =>
        verifyProof idx leaf root proof >>= fun verified =>
          pure (root, aux,
                ⟨idx, leaf, proof,
                 extractor s queryLog root,
                 generateProof (extractor s queryLog root) idx,
                 verified⟩) := by
  simp only [extractabilityInner, bind_assoc, pure_bind]

omit [DecidableEq α] in
/--
Project the logged-prefix of `extractabilityInner` onto `Unit`: discarding both the
committed root/aux and the query log of the committing adversary recovers the plain
measurement used to express the combined query bound.
-/
private lemma extractabilityInner_logged_prefix_map_unit_eq
    {s : Skeleton} (𝒜 : Adversary α s) :
    (fun _ => ()) <$>
        (𝒜.commit.withQueryLog >>= fun ((root, aux), queryLog) =>
          𝒜.opening aux >>= fun q => pure (((root, aux), queryLog), q)) =
      (do let (_root, aux) ← 𝒜.commit
          let ⟨_idx, _leaf, _proof⟩ ← 𝒜.opening aux
          pure ()) := by
  change ((fun _ => ()) <$> ((simulateQ loggingOracle 𝒜.commit).run >>= fun x =>
    𝒜.opening x.1.2 >>= fun q => pure ((x.1, x.2), q))) = _
  simpa [map_bind, map_pure] using
    loggingOracle.run_simulateQ_bind_fst 𝒜.commit
    (fun (_, aux) => 𝒜.opening aux >>= fun _ => pure ())

/--
If the adversary `𝒜` has two-phase total query bound `qb`, then the full extractability
game has total query bound `qb + s.depth`.

The extra `s.depth` accounts for the `verifyProof` step, which traverses the path from the
queried leaf to the root, making at most `s.depth` oracle queries.
-/
theorem extractabilityInner_isTotalQueryBound {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    IsTotalQueryBound (extractabilityInner 𝒜) (qb + s.depth) := by
  rw [extractabilityInner_eq_bind_verifyProof]
  exact isTotalQueryBound_bind (n₁ := qb) (n₂ := s.depth)
    ((isQueryBound_iff_of_map_eq (extractabilityInner_logged_prefix_map_unit_eq 𝒜)
      (fun _ b => 0 < b) (fun _ b => b - 1)).mpr h)
    fun (⟨⟨root, _aux⟩, _queryLog⟩, ⟨idx, leaf, proof⟩) =>
      isTotalQueryBound_bind (n₁ := s.depth) (n₂ := 0)
        (verifyProof_isTotalQueryBound_skeleton_depth idx leaf root proof) fun _ => trivial

/-- The shared-cache random-oracle experiment makes at most as many underlying fresh
queries as `extractabilityInner`. Cache hits skip the underlying query, so the implication
is intentionally one-way. -/
theorem extractabilityGame_isTotalQueryBound [IsUniformSpec (spec α)]
    {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    IsTotalQueryBound (extractabilityGame 𝒜) (qb + s.depth) := by
  apply (isQueryBound_map_iff _ _ (qb + s.depth) _ _).mpr
  exact IsTotalQueryBound.simulateQ_run_withCaching _
    (extractabilityInner_isTotalQueryBound 𝒜 qb h)
    (fun t => (isQueryBound_query_iff t 1 _ _).mpr Nat.one_pos) ∅

private lemma extractorChildren_eq_none_of_find?_eq_none
    {log_c : (spec α).QueryLog} {a : α} (hf : log_c.find? (fun ⟨_, r⟩ => r == a) = none) :
    extractorChildren log_c a = none := by
  simp only [extractorChildren, hf]

/--
If a particular transcript is in the support of the extractability game with the query log,
then the log has subsets `log_c` (containing the committing adversary's queries)
and `log_v` (containing the verifier's queries),
such that the proof verification step passes emitting `log_v`,
and the extractor and proof generation steps `log_c`
yield the same extracted tree and proof as the transcript.
-/
private lemma extractabilityInner_support_decompose
    {s : Skeleton} (𝒜 : Adversary α s) {root : α} {aux : 𝒜.AuxState} {idx : SkeletonLeafIndex s}
    {leaf : α} {proof : List.Vector α idx.depth} {extractedTree : FullData (Option α) s}
    {extractedProof : List.Vector (Option α) idx.depth} {log : (spec α).QueryLog}
    (hsup : ((root, aux, ⟨idx, leaf, proof, extractedTree, extractedProof, true⟩),
                  log) ∈
      support (extractabilityInner 𝒜).withQueryLog) :
    ∃ log_c log_v : (spec α).QueryLog,
      (true, log_v) ∈ support
          (verifyProof (m := OracleComp (spec α)) idx leaf root proof).withQueryLog ∧
      (∀ q, q ∈ log_v → q ∈ log) ∧
      (∀ q, q ∈ log_c → q ∈ log) ∧
      extractedTree = extractor s log_c root ∧
      extractedProof = generateProof (extractor s log_c root) idx := by
  unfold extractabilityInner at hsup
  simp only [OracleComp.withQueryLog_bind, mem_support_bind_iff, support_map,
    Set.mem_image] at hsup
  obtain ⟨⟨⟨root_c, aux_c⟩, log_c⟩, h_c, ⟨_, _⟩,
    ⟨⟨⟨idx_o, leaf_o, proof_o⟩, _⟩, _, ⟨_, _⟩,
      ⟨⟨_, log_v⟩, h_vp, ⟨_, _⟩, h_p, h_eq_p⟩, h_eq_v⟩, h_eq_co⟩ := hsup
  rw [OracleComp.withQueryLog_pure, mem_support_pure_iff, Prod.mk.injEq] at h_p
  obtain ⟨h_p1, rfl⟩ := h_p
  simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at h_eq_co h_eq_v h_eq_p
  obtain ⟨h_eq_co1, h_eq_co2⟩ := h_eq_co
  obtain ⟨h_eq_v1, h_eq_v2⟩ := h_eq_v
  obtain ⟨h_eq_p1, h_eq_p2⟩ := h_eq_p
  rw [← h_eq_v1, ← h_eq_p1, h_p1] at h_eq_co1
  simp only [Prod.mk.injEq] at h_eq_co1
  obtain ⟨rfl, rfl, h_sigma_eq⟩ := h_eq_co1
  obtain ⟨rfl, h_rest_eq⟩ := Sigma.mk.inj h_sigma_eq
  simp only [heq_eq_eq, Prod.mk.injEq] at h_rest_eq
  obtain ⟨rfl, rfl, h_tree_eq, h_proof_ext_eq, rfl⟩ := h_rest_eq
  rw [OracleComp.withQueryLog_self_log_eq 𝒜.commit h_c] at h_tree_eq h_proof_ext_eq
  refine ⟨log_c, log_v, h_vp, fun q hq => ?_, fun q hq => ?_,
    h_tree_eq.symm, h_proof_ext_eq.symm⟩ <;>
    rw [← h_eq_co2, ← h_eq_v2, ← h_eq_p2] <;>
    grind [List.mem_append_right, List.mem_append_left]

/--
If `root` is not the response of any query in `log`,
then the extractor at an internal skeleton is `none`.
-/
private lemma extractor_internal_get_eq_none_of_find?_eq_none
    (sl sr : Skeleton) (log : (spec α).QueryLog) (root : α)
    (idx : SkeletonNodeIndex sl ⊕ SkeletonNodeIndex sr)
    (hf : log.find? (fun ⟨_, r⟩ => r == root) = none) :
    (extractor (Skeleton.internal sl sr) log root).get
        (idx.elim SkeletonNodeIndex.ofLeft SkeletonNodeIndex.ofRight) = none := by
  simp only [extractor, optionPopulateDown_internal, extractorChildren_eq_none_of_find?_eq_none hf]
  cases idx <;>
    exact populateDown_none_get_eq_none (Option.bindPair (extractorChildren log)) rfl _

end ExtractabilityGame

private lemma singleHash_withQueryLog (a b : α) :
    (singleHash (m := OracleComp (spec α)) a b).withQueryLog =
      (liftM ((spec α).query (a, b)) : OracleComp (spec α) α) >>=
        fun u => pure (u, ([⟨(a, b), u⟩] : (spec α).QueryLog)) := by
  simp [singleHash, OracleComp.withQueryLog_query]

private lemma getPutativeRoot_step_withQueryLog_decompose
    (prog : OracleComp (spec α) α) (mkPair : α → α × α)
    (r : α) (log_v : (spec α).QueryLog)
    (hmem : (r, log_v) ∈ support
      (prog >>= fun a => let (l, r') := mkPair a; singleHash l r').withQueryLog) :
    ∃ a log_a, (a, log_a) ∈ support prog.withQueryLog
      ∧ log_v = log_a ++ [⟨mkPair a, r⟩] := by
  simp only [OracleComp.withQueryLog_bind, singleHash_withQueryLog] at hmem
  grind

/--
Predicate stating that `log` contains a hash chain from `leaf` (combined with the
sibling values in `proof`) up to `root` along the path determined by `idx`.
-/
def ChainInLog {s : Skeleton} (log : (spec α).QueryLog) (leaf root : α) :
    (idx : SkeletonLeafIndex s) → List.Vector α idx.depth → Prop
  | .ofLeaf, _ => leaf = root
  | .ofLeft idxLeft, proof =>
      ∃ ancestor : α,
        (⟨(ancestor, proof.head), root⟩ : (_i : (α × α)) × α) ∈ log ∧
        ChainInLog log leaf ancestor idxLeft proof.tail
  | .ofRight idxRight, proof =>
      ∃ ancestor : α,
        (⟨(proof.head, ancestor), root⟩ : (_i : (α × α)) × α) ∈ log ∧
        ChainInLog log leaf ancestor idxRight proof.tail

/-- A hash chain interpreted in a shared random-oracle cache. Unlike `ChainInLog`,
this predicate records only the final function graph and therefore identifies cache hits
and cache misses with the same response. -/
private def ChainInCache {s : Skeleton} (cache : (spec α).QueryCache) (leaf root : α) :
    (idx : SkeletonLeafIndex s) → List.Vector α idx.depth → Prop
  | .ofLeaf, _ => leaf = root
  | .ofLeft idxLeft, proof =>
      ∃ ancestor : α,
        cache (ancestor, proof.head) = some root ∧
        ChainInCache cache leaf ancestor idxLeft proof.tail
  | .ofRight idxRight, proof =>
      ∃ ancestor : α,
        cache (proof.head, ancestor) = some root ∧
        ChainInCache cache leaf ancestor idxRight proof.tail

/-- The later phase added a previously uncached query whose answer is `target`. -/
private def CacheAddsValue (cache₀ cache₁ : (spec α).QueryCache) (target : α) : Prop :=
  ∃ input : α × α, cache₁ input = some target ∧ cache₀ input = none

private lemma chainInCache_mono {s : Skeleton} (idx : SkeletonLeafIndex s)
    {cache₁ cache₂ : (spec α).QueryCache} {root leaf : α}
    {proof : List.Vector α idx.depth}
    (hle : cache₁ ≤ cache₂) (hchain : ChainInCache cache₁ leaf root idx proof) :
    ChainInCache cache₂ leaf root idx proof := by
  induction idx generalizing root with
  | ofLeaf => exact hchain
  | @ofLeft sl sr idxLeft ih | @ofRight sl sr idxRight ih =>
    obtain ⟨ancestor, hentry, hrec⟩ := hchain
    exact ⟨ancestor, hle hentry, ih hrec⟩

private lemma chainInCache_of_mem_support_getPutativeRoot
    [DecidableEq α]
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (leaf : α) (proof : List.Vector α idx.depth) (root : α)
    (cache₀ cache₁ : (spec α).QueryCache)
    (hmem : (root, cache₁) ∈ support
      ((simulateQ (spec α).cachingOracle
        (getPutativeRoot (m := OracleComp (spec α)) idx leaf proof)).run cache₀)) :
    ChainInCache cache₁ leaf root idx proof := by
  induction idx generalizing root cache₀ cache₁ with
  | ofLeaf =>
    simp only [getPutativeRoot, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff, Prod.mk.injEq] at hmem
    exact hmem.1.symm
  | @ofLeft sl sr idxLeft ih =>
    rw [show getPutativeRoot (m := OracleComp (spec α)) (.ofLeft idxLeft) leaf proof =
      getPutativeRoot idxLeft leaf proof.tail >>= fun ancestor =>
        singleHash ancestor proof.head from rfl,
      simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨ancestor, cacheMid⟩, hrec, hhash⟩ := hmem
    have hentry : cache₁ (ancestor, proof.head) = some root := by
      exact cachingOracle_query_caches (ancestor, proof.head) cacheMid root cache₁ (by
        simpa only [singleHash, HasQuery.instOfMonadLift_query,
          cachingOracle.simulateQ_query] using hhash)
    have hmono : cacheMid ≤ cache₁ :=
      simulateQ_cachingOracle_cache_le (singleHash ancestor proof.head) cacheMid _ hhash
    exact ⟨ancestor, hentry, chainInCache_mono idxLeft hmono
      (ih proof.tail ancestor cache₀ cacheMid hrec)⟩
  | @ofRight sl sr idxRight ih =>
    rw [show getPutativeRoot (m := OracleComp (spec α)) (.ofRight idxRight) leaf proof =
      getPutativeRoot idxRight leaf proof.tail >>= fun ancestor =>
        singleHash proof.head ancestor from rfl,
      simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨ancestor, cacheMid⟩, hrec, hhash⟩ := hmem
    have hentry : cache₁ (proof.head, ancestor) = some root := by
      exact cachingOracle_query_caches (proof.head, ancestor) cacheMid root cache₁ (by
        simpa only [singleHash, HasQuery.instOfMonadLift_query,
          cachingOracle.simulateQ_query] using hhash)
    have hmono : cacheMid ≤ cache₁ :=
      simulateQ_cachingOracle_cache_le (singleHash proof.head ancestor) cacheMid _ hhash
    exact ⟨ancestor, hentry, chainInCache_mono idxRight hmono
      (ih proof.tail ancestor cache₀ cacheMid hrec)⟩

private lemma chainInCache_of_mem_support_verifyProof
    [DecidableEq α]
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (leaf root : α) (proof : List.Vector α idx.depth)
    (cache₀ cache₁ : (spec α).QueryCache)
    (hmem : (true, cache₁) ∈ support
      ((simulateQ (spec α).cachingOracle
        (verifyProof (m := OracleComp (spec α)) idx leaf root proof)).run cache₀)) :
    ChainInCache cache₁ leaf root idx proof := by
  unfold verifyProof at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨putativeRoot, cacheMid⟩, hroot, hfinal⟩ := hmem
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
    Prod.mk.injEq] at hfinal
  obtain ⟨hroot_eq, rfl⟩ := hfinal
  have hputative : putativeRoot = root := by
    simpa only [beq_iff_eq] using hroot_eq.symm
  subst root
  exact chainInCache_of_mem_support_getPutativeRoot
    idx leaf proof putativeRoot cache₀ cache₁ hroot

private lemma fresh_extractedTarget_of_extractor_disagreement
    [DecidableEq α]
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (log : (spec α).QueryLog) (cacheCommit cacheFinal : (spec α).QueryCache)
    (root leaf : α) (proof : List.Vector α idx.depth)
    (hlogCache : ∀ entry ∈ log, cacheCommit entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cacheCommit input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hno : ¬ CacheHasCollision cacheCommit)
    (hmono : cacheCommit ≤ cacheFinal)
    (hchain : ChainInCache cacheFinal leaf root idx proof)
    (hdisagree :
      some leaf ≠ (extractor s log root).get idx.toNodeIndex ∨
      proof.toList.map some ≠ (generateProof (extractor s log root) idx).toList) :
    ∃ target ∈ extractedTargets s log root,
      CacheAddsValue cacheCommit cacheFinal target := by
  induction idx generalizing root with
  | ofLeaf =>
    simp only [ChainInCache] at hchain
    subst root
    have hleaf :
        some leaf ≠ (extractor .leaf log leaf).get SkeletonLeafIndex.ofLeaf.toNodeIndex :=
      hdisagree.resolve_right (by simp [generateProof])
    exact (hleaf rfl).elim
  | @ofLeft sl sr idxLeft ih =>
    obtain ⟨ancestor, hquery, hchainTail⟩ := hchain
    cases hfind : log.find? (fun ⟨_, response⟩ => response == root) with
    | none =>
        have hfresh : cacheCommit (ancestor, proof.head) = none := by
          by_contra hne
          obtain ⟨value, hvalue⟩ := Option.ne_none_iff_exists'.mp hne
          have hvalueFinal := hmono hvalue
          rw [hquery] at hvalueFinal
          obtain rfl := Option.some.inj hvalueFinal
          obtain ⟨entry, hentry, _, hresponse⟩ :=
            hcacheLog (ancestor, proof.head) root hvalue
          have hsome :
              (log.find? (fun ⟨_, response⟩ => response == root)).isSome = true := by
            rw [List.find?_isSome]
            exact ⟨entry, hentry, by simp [hresponse]⟩
          simp [hfind] at hsome
        exact ⟨root, by simp [extractedTargets], ⟨(ancestor, proof.head), hquery, hfresh⟩⟩
    | some entry =>
        obtain ⟨⟨left, right⟩, response⟩ := entry
        have hresponse : response = root := by
          have := List.find?_some hfind
          simpa only [beq_iff_eq] using this
        subst response
        have hentry : (⟨(left, right), root⟩ : (_ : α × α) × α) ∈ log :=
          List.mem_of_find?_eq_some hfind
        have hcached : cacheCommit (left, right) = some root := hlogCache _ hentry
        cases hqueryCommit : cacheCommit (ancestor, proof.head) with
        | none =>
            exact ⟨root, by simp [extractedTargets],
              ⟨(ancestor, proof.head), hquery, hqueryCommit⟩⟩
        | some value =>
            have hvalueFinal := hmono hqueryCommit
            rw [hquery] at hvalueFinal
            obtain rfl := Option.some.inj hvalueFinal
            have hinputs : (left, right) = (ancestor, proof.head) :=
              cache_lookup_eq_of_noCollision hno hcached
                ⟨root, hqueryCommit, HEq.rfl⟩
            have hleft : left = ancestor := congrArg Prod.fst hinputs
            have hright : right = proof.head := congrArg Prod.snd hinputs
            subst left
            subst right
            have hchildDisagree :
                some leaf ≠ (extractor sl log ancestor).get idxLeft.toNodeIndex ∨
                proof.tail.toList.map some ≠
                  (generateProof (extractor sl log ancestor) idxLeft).toList := by
              rw [extractor_internal_eq_of_find?_eq sl sr log root ancestor proof.head hfind]
                at hdisagree
              rcases hdisagree with hleaf | hproof
              · exact Or.inl (by
                  simpa [SkeletonLeafIndex.toNodeIndex, FullData.get] using hleaf)
              · refine Or.inr fun htail => hproof ?_
                have hsibling : (extractor sr log proof.head).getRootValue = some proof.head :=
                  optionPopulateDown_getRootValue _ _
                have hproofList : proof.toList = proof.head :: proof.tail.toList := by
                  rw [← proof.cons_head_tail]
                  rfl
                rw [hproofList, List.map_cons]
                change some proof.head :: proof.tail.toList.map some =
                  (extractor sr log proof.head).getRootValue ::
                    (generateProof (extractor sl log ancestor) idxLeft).toList
                rw [hsibling, htail]
            obtain ⟨target, htarget, hfresh⟩ :=
              ih ancestor proof.tail hchainTail hchildDisagree
            exact ⟨target, by
              simp [extractedTargets, extractorChildren, hfind, htarget], hfresh⟩
  | @ofRight sl sr idxRight ih =>
    obtain ⟨ancestor, hquery, hchainTail⟩ := hchain
    cases hfind : log.find? (fun ⟨_, response⟩ => response == root) with
    | none =>
        have hfresh : cacheCommit (proof.head, ancestor) = none := by
          by_contra hne
          obtain ⟨value, hvalue⟩ := Option.ne_none_iff_exists'.mp hne
          have hvalueFinal := hmono hvalue
          rw [hquery] at hvalueFinal
          obtain rfl := Option.some.inj hvalueFinal
          obtain ⟨entry, hentry, _, hresponse⟩ :=
            hcacheLog (proof.head, ancestor) root hvalue
          have hsome :
              (log.find? (fun ⟨_, response⟩ => response == root)).isSome = true := by
            rw [List.find?_isSome]
            exact ⟨entry, hentry, by simp [hresponse]⟩
          simp [hfind] at hsome
        exact ⟨root, by simp [extractedTargets], ⟨(proof.head, ancestor), hquery, hfresh⟩⟩
    | some entry =>
        obtain ⟨⟨left, right⟩, response⟩ := entry
        have hresponse : response = root := by
          have := List.find?_some hfind
          simpa only [beq_iff_eq] using this
        subst response
        have hentry : (⟨(left, right), root⟩ : (_ : α × α) × α) ∈ log :=
          List.mem_of_find?_eq_some hfind
        have hcached : cacheCommit (left, right) = some root := hlogCache _ hentry
        cases hqueryCommit : cacheCommit (proof.head, ancestor) with
        | none =>
            exact ⟨root, by simp [extractedTargets],
              ⟨(proof.head, ancestor), hquery, hqueryCommit⟩⟩
        | some value =>
            have hvalueFinal := hmono hqueryCommit
            rw [hquery] at hvalueFinal
            obtain rfl := Option.some.inj hvalueFinal
            have hinputs : (left, right) = (proof.head, ancestor) :=
              cache_lookup_eq_of_noCollision hno hcached
                ⟨root, hqueryCommit, HEq.rfl⟩
            have hleft : left = proof.head := congrArg Prod.fst hinputs
            have hright : right = ancestor := congrArg Prod.snd hinputs
            subst left
            subst right
            have hchildDisagree :
                some leaf ≠ (extractor sr log ancestor).get idxRight.toNodeIndex ∨
                proof.tail.toList.map some ≠
                  (generateProof (extractor sr log ancestor) idxRight).toList := by
              rw [extractor_internal_eq_of_find?_eq sl sr log root proof.head ancestor hfind]
                at hdisagree
              rcases hdisagree with hleaf | hproof
              · exact Or.inl (by
                  simpa [SkeletonLeafIndex.toNodeIndex, FullData.get] using hleaf)
              · refine Or.inr fun htail => hproof ?_
                have hsibling : (extractor sl log proof.head).getRootValue = some proof.head :=
                  optionPopulateDown_getRootValue _ _
                have hproofList : proof.toList = proof.head :: proof.tail.toList := by
                  rw [← proof.cons_head_tail]
                  rfl
                rw [hproofList, List.map_cons]
                change some proof.head :: proof.tail.toList.map some =
                  (extractor sl log proof.head).getRootValue ::
                    (generateProof (extractor sr log ancestor) idxRight).toList
                rw [hsibling, htail]
            obtain ⟨target, htarget, hfresh⟩ :=
              ih ancestor proof.tail hchainTail hchildDisagree
            exact ⟨target, by
              simp [extractedTargets, extractorChildren, hfind, htarget], hfresh⟩

/-- Pointwise deterministic reduction for the cached suffix: once the commit cache is
collision-free, a winning opening must add a fresh cache entry whose answer is one of the
labels fixed by the logged commit. -/
private lemma extractability_rest_win_implies_fresh_target_of_invariants
    [DecidableEq α]
    {s : Skeleton} (𝒜 : Adversary α s)
    {root : α} {aux : 𝒜.AuxState} {log : (spec α).QueryLog}
    {cacheCommit : (spec α).QueryCache}
    (hlogCache : ∀ entry ∈ log, cacheCommit entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cacheCommit input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hno : ¬ CacheHasCollision cacheCommit) :
    ∀ z ∈ support ((simulateQ (spec α).cachingOracle
        (extractabilityRest 𝒜 root aux log)).run cacheCommit),
      AdversaryWinsExtractabilityGame z.1 →
      ∃ target ∈ extractedTargets s log root,
        CacheAddsValue cacheCommit z.2 target := by
  intro z hz hwin
  have hmono : cacheCommit ≤ z.2 :=
    simulateQ_cachingOracle_cache_le (extractabilityRest 𝒜 root aux log)
      cacheCommit z hz
  unfold extractabilityRest at hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨⟨idx, leaf, proof⟩, cacheOpen⟩, hopen, hz⟩ := hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨verified, cacheFinal⟩, hverify, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hz
  have hcacheFinal : z.2 = cacheFinal := congrArg Prod.snd hz
  rw [hz] at hwin
  simp only [AdversaryWinsExtractabilityGame, AdversaryWinsExtractabilityInner] at hwin
  obtain ⟨hverified, hdisagree⟩ := hwin
  subst verified
  have hchain : ChainInCache cacheFinal leaf root idx proof :=
    chainInCache_of_mem_support_verifyProof idx leaf root proof cacheOpen cacheFinal hverify
  rw [hcacheFinal] at hmono
  rw [hcacheFinal]
  exact fresh_extractedTarget_of_extractor_disagreement idx log cacheCommit cacheFinal
    root leaf proof hlogCache hcacheLog hno hmono hchain hdisagree

/-- Pointwise suffix bound in terms of the actual extracted-tree size and the residual
opening budget. Its hypotheses are precisely the log/cache invariants maintained by the
combined caching-and-logging interpreter used in the stopping-time proof below. -/
private lemma extractability_rest_noCollision_le_of_opening_bound
    [DecidableEq α] [Finite α] [Inhabited α] [IsUniformSpec (spec α)]
    {s : Skeleton} (𝒜 : Adversary α s) (openingBound targetBound : ℕ)
    {root : α} {aux : 𝒜.AuxState} {log : (spec α).QueryLog}
    {cacheCommit : (spec α).QueryCache}
    (hopening : IsTotalQueryBound (𝒜.opening aux) openingBound)
    (hlogCache : ∀ entry ∈ log, cacheCommit entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cacheCommit input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (htargets : (extractedTargets s log root).toFinset.card ≤ targetBound)
    (hno : ¬ CacheHasCollision cacheCommit) :
    Pr[fun z => AdversaryWinsExtractabilityGame z.1 |
      (simulateQ (spec α).cachingOracle
        (extractabilityRest 𝒜 root aux log)).run cacheCommit] ≤
      ((targetBound * (openingBound + s.depth) : ℕ) : ENNReal) *
        (@Fintype.card ((spec α).Range default)
          (OracleSpec.instFintypeRangeOfFintype default) : ENNReal)⁻¹ := by
  let targets := (extractedTargets s log root).toFinset
  have hrest : IsTotalQueryBound
      (extractabilityRest 𝒜 root aux log) (openingBound + s.depth) := by
    unfold extractabilityRest
    exact isTotalQueryBound_bind (n₁ := openingBound) (n₂ := s.depth)
      hopening fun ⟨idx, leaf, proof⟩ =>
        isTotalQueryBound_bind (n₁ := s.depth) (n₂ := 0)
          (verifyProof_isTotalQueryBound_skeleton_depth idx leaf root proof)
          fun _ => trivial
  calc
    Pr[fun z => AdversaryWinsExtractabilityGame z.1 |
        (simulateQ (spec α).cachingOracle
          (extractabilityRest 𝒜 root aux log)).run cacheCommit]
      ≤ Pr[fun z => ∃ target ∈ targets, ∃ input : α × α, ∃ value : α,
            z.2 input = some value ∧ cacheCommit input = none ∧ HEq value target |
          (simulateQ (spec α).cachingOracle
            (extractabilityRest 𝒜 root aux log)).run cacheCommit] := by
        apply probEvent_mono
        intro z hz hwin
        obtain ⟨target, htarget, input, hfinal, hinitial⟩ :=
          extractability_rest_win_implies_fresh_target_of_invariants
            𝒜 hlogCache hcacheLog hno z hz hwin
        exact ⟨target, by simpa [targets] using htarget,
          input, target, hfinal, hinitial, HEq.rfl⟩
    _ ≤ ((targets.card * (openingBound + s.depth) : ℕ) : ENNReal) *
          (@Fintype.card ((spec α).Range default)
            (OracleSpec.instFintypeRangeOfFintype default) : ENNReal)⁻¹ := by
        exact OracleComp.probEvent_cache_hits_targets_le_of_noCollision
          (extractabilityRest 𝒜 root aux log) (openingBound + s.depth) hrest
          (fun input => by
            apply Nat.le_of_eq
            exact @Fintype.card_congr
              ((spec α).Range default) ((spec α).Range input)
              (OracleSpec.instFintypeRangeOfFintype default)
              (OracleSpec.instFintypeRangeOfFintype input) (Equiv.refl α))
          targets cacheCommit hno
    _ ≤ ((targetBound * (openingBound + s.depth) : ℕ) : ENNReal) *
          (@Fintype.card ((spec α).Range default)
            (OracleSpec.instFintypeRangeOfFintype default) : ENNReal)⁻¹ := by
        gcongr

/-- Stopping-time induction for the shared ROM experiment. The induction follows the syntax
of the still-running commit computation. A cache hit consumes one unit of the remaining
combined adversary budget; a miss additionally pays for the at most `cached` responses that
would create a collision. When the commit stops, the suffix theorem pays for at most
`targetCount * (remaining + depth)` fresh-target opportunities. -/
private lemma extractabilityRunFrom_le_potential
    [DecidableEq α] [Finite α] [Inhabited α] [IsUniformSpec (spec α)]
    {s : Skeleton} (𝒜 : Adversary α s)
    (commit : OracleComp (spec α) (α × 𝒜.AuxState))
    (remaining cached : ℕ)
    (hbound : IsTotalQueryBound
      (commit >>= fun x => 𝒜.opening x.2 >>= fun _ => pure ()) remaining)
    (cache : (spec α).QueryCache) (log : (spec α).QueryLog)
    (hno : ¬ CacheHasCollision cache)
    (hcacheBound : ∃ keys : Finset (α × α), keys.card ≤ cached ∧
      ∀ input, cache input ≠ none → input ∈ keys)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value) :
    Pr[fun z => AdversaryWinsExtractabilityGame z.1 |
      extractabilityRunFrom 𝒜 commit cache log] ≤
      (extractabilityExactPotential (2 * s.leafCount - 1) s.depth remaining cached : ENNReal) *
        (@Fintype.card ((spec α).Range default)
          (OracleSpec.instFintypeRangeOfFintype default) : ENNReal)⁻¹ := by
  let treeTargetCount := 2 * s.leafCount - 1
  let C := (@Fintype.card ((spec α).Range default)
    (OracleSpec.instFintypeRangeOfFintype default) : ENNReal)
  induction commit using OracleComp.inductionOn generalizing remaining cached cache log with
  | pure x =>
      let targetCount := min treeTargetCount (2 * cached + 1)
      have hopening : IsTotalQueryBound (𝒜.opening x.2) remaining := by
        have hmapped : IsTotalQueryBound ((fun _ => ()) <$> 𝒜.opening x.2) remaining := by
          simpa using hbound
        exact (isQueryBound_map_iff (𝒜.opening x.2) (fun _ => ()) remaining _ _).mp
          hmapped
      have htargets : (extractedTargets s log x.1).toFinset.card ≤ targetCount := by
        obtain ⟨keys, hkeysCard, hkeysMem⟩ := hcacheBound
        have htree : (extractedTargets s log x.1).toFinset.card ≤ treeTargetCount := by
          calc
            (extractedTargets s log x.1).toFinset.card ≤
                (extractedTargets s log x.1).length := List.toFinset_card_le _
            _ ≤ treeTargetCount := extractedTargets_length_le s log x.1
        have hcache : (extractedTargets s log x.1).toFinset.card ≤ 2 * cached + 1 :=
          (extractedTargets_toFinset_card_le_cacheKeys s log x.1 keys hlogCache hkeysMem).trans
            (by omega)
        exact le_min htree hcache
      have hsuffix := extractability_rest_noCollision_le_of_opening_bound
        𝒜 remaining targetCount (root := x.1) (aux := x.2)
        hopening hlogCache hcacheLog htargets hno
      simp only [extractabilityRunFrom, simulateQ_pure, StateT.run_pure, pure_bind]
      refine hsuffix.trans ?_
      change ((targetCount * (remaining + s.depth) : ℕ) : ENNReal) * C⁻¹ ≤
        (extractabilityExactPotential treeTargetCount s.depth remaining cached : ENNReal) * C⁻¹
      gcongr
      exact extractabilityExactPotential_terminal_le
        treeTargetCount s.depth remaining cached
  | query_bind t next ih =>
      have hqueryBound : IsTotalQueryBound
          ((liftM ((spec α).query t) : OracleComp (spec α) _) >>= fun u =>
            next u >>= fun x => 𝒜.opening x.2 >>= fun _ => pure ()) remaining := by
        simpa only [bind_assoc] using hbound
      rw [isTotalQueryBound_query_bind_iff] at hqueryBound
      obtain ⟨hremaining, hnext⟩ := hqueryBound
      by_cases hhit : ∃ value, cache t = some value
      · obtain ⟨value, hvalue⟩ := hhit
        have hrun : extractabilityRunFrom 𝒜
            ((liftM ((spec α).query t) : OracleComp (spec α) _) >>= next) cache log =
            extractabilityRunFrom 𝒜 (next value) cache
              (log ++ [⟨t, value⟩]) := by
          simp only [extractabilityRunFrom, OracleComp.run_simulateQ_query_bind,
            cachingLoggingOracle.run_some hvalue, pure_bind]
        rw [hrun]
        have hlogCache' : ∀ entry ∈ log ++ [⟨t, value⟩],
            cache entry.1 = some entry.2 := by
          intro entry hentry
          rw [List.mem_append] at hentry
          rcases hentry with hentry | hentry
          · exact hlogCache entry hentry
          · rw [List.mem_singleton] at hentry
            subst entry
            exact hvalue
        have hcacheLog' : ∀ input output, cache input = some output →
            ∃ entry ∈ log ++ [⟨t, value⟩], entry.1 = input ∧ entry.2 = output := by
          intro input output hcached
          obtain ⟨entry, hentry, hi, ho⟩ := hcacheLog input output hcached
          exact ⟨entry, List.mem_append_left _ hentry, hi, ho⟩
        have hrec := ih value (remaining := remaining - 1) (cached := cached)
          (hnext value) (cache := cache) (log := log ++ [⟨t, value⟩])
          hno hcacheBound hlogCache' hcacheLog'
        refine hrec.trans ?_
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast extractabilityExactPotential_hit_le
            treeTargetCount s.depth remaining cached
        · exact zero_le
      · push Not at hhit
        have hnone : cache t = none := Option.eq_none_iff_forall_ne_some.mpr hhit
        have hrun : extractabilityRunFrom 𝒜
            ((liftM ((spec α).query t) : OracleComp (spec α) _) >>= next) cache log =
            (liftM ((spec α).query t) : OracleComp (spec α) _) >>= fun value =>
              extractabilityRunFrom 𝒜 (next value) (cache.cacheQuery t value)
                (log ++ [⟨t, value⟩]) := by
          simp only [extractabilityRunFrom, OracleComp.run_simulateQ_query_bind,
            cachingLoggingOracle.run_none hnone]
          rfl
        rw [hrun]
        have hcollision : Pr[fun value => CacheHasCollision (cache.cacheQuery t value) |
            (liftM ((spec α).query t) : OracleComp (spec α) _)] ≤
              (cached : ENNReal) * C⁻¹ := by
          classical
          obtain ⟨keys, hkeysCard, hkeysMem⟩ := hcacheBound
          rw [probEvent_query]
          have hbad := (OracleComp.card_responses_creating_cacheCollision_le
            (t := t) hno hkeysMem).trans hkeysCard
          have hcard : @Fintype.card ((spec α).Range t)
              (OracleSpec.instFintypeRangeOfFintype t) =
              @Fintype.card ((spec α).Range default)
                (OracleSpec.instFintypeRangeOfFintype default) :=
            @Fintype.card_congr ((spec α).Range t) ((spec α).Range default)
              (OracleSpec.instFintypeRangeOfFintype t)
              (OracleSpec.instFintypeRangeOfFintype default) (Equiv.refl α)
          calc
            ((Finset.univ.filter
                (fun value => CacheHasCollision (cache.cacheQuery t value))).card : ENNReal) /
                @Fintype.card ((spec α).Range t)
                  (OracleSpec.instFintypeRangeOfFintype t)
              ≤ (cached : ENNReal) / @Fintype.card ((spec α).Range t)
                  (OracleSpec.instFintypeRangeOfFintype t) :=
                ENNReal.div_le_div_right (by exact_mod_cast hbad) _
            _ = (cached : ENNReal) * C⁻¹ := by
              rw [hcard, ENNReal.div_eq_inv_mul, mul_comm]
        have hcontinuation : ∀ value ∈ support
            (liftM ((spec α).query t) : OracleComp (spec α) _),
            ¬ CacheHasCollision (cache.cacheQuery t value) →
            Pr[fun z => AdversaryWinsExtractabilityGame z.1 |
              extractabilityRunFrom 𝒜 (next value) (cache.cacheQuery t value)
                (log ++ [⟨t, value⟩])] ≤
              (extractabilityExactPotential treeTargetCount s.depth
                (remaining - 1) (cached + 1) : ENNReal) * C⁻¹ := by
          intro value _ hno'
          have hcacheBound' : ∃ keys : Finset (α × α), keys.card ≤ cached + 1 ∧
              ∀ input, (cache.cacheQuery t value) input ≠ none → input ∈ keys := by
            obtain ⟨keys, hkeysCard, hkeysMem⟩ := hcacheBound
            refine ⟨insert t keys, (Finset.card_insert_le t keys).trans (by omega), ?_⟩
            intro input hinput
            by_cases hi : input = t
            · exact hi ▸ Finset.mem_insert_self _ _
            · rw [QueryCache.cacheQuery_of_ne cache value hi] at hinput
              exact Finset.mem_insert_of_mem (hkeysMem input hinput)
          have hlogCache' : ∀ entry ∈ log ++ [⟨t, value⟩],
              (cache.cacheQuery t value) entry.1 = some entry.2 := by
            rintro ⟨input, output⟩ hentry
            rw [List.mem_append] at hentry
            rcases hentry with hentry | hentry
            · by_cases hi : input = t
              · subst input
                have := hlogCache ⟨t, output⟩ hentry
                simp [hnone] at this
              · rw [QueryCache.cacheQuery_of_ne cache value hi]
                exact hlogCache ⟨input, output⟩ hentry
            · rw [List.mem_singleton] at hentry
              have hinput : input = t := congrArg Sigma.fst hentry
              subst input
              have houtput : output = value := eq_of_heq (Sigma.mk.inj_iff.mp hentry).2
              subst output
              exact QueryCache.cacheQuery_self cache t value
          have hcacheLog' : ∀ input output,
              (cache.cacheQuery t value) input = some output →
              ∃ entry ∈ log ++ [⟨t, value⟩], entry.1 = input ∧ entry.2 = output := by
            intro input output hcached
            by_cases hi : input = t
            · subst input
              rw [QueryCache.cacheQuery_self] at hcached
              obtain rfl := Option.some.inj hcached
              exact ⟨⟨t, value⟩, by simp, rfl, rfl⟩
            · rw [QueryCache.cacheQuery_of_ne cache value hi] at hcached
              obtain ⟨entry, hentry, heqInput, heqOutput⟩ :=
                hcacheLog input output hcached
              exact ⟨entry, List.mem_append_left _ hentry, heqInput, heqOutput⟩
          have hrec := ih value (remaining := remaining - 1) (cached := cached + 1)
            (hnext value) (cache := cache.cacheQuery t value)
            (log := log ++ [⟨t, value⟩]) hno' hcacheBound' hlogCache' hcacheLog'
          exact hrec
        have hcombined := probEvent_bind_le_add
          (mx := (liftM ((spec α).query t) : OracleComp (spec α) _))
          (my := fun value => extractabilityRunFrom 𝒜 (next value)
            (cache.cacheQuery t value) (log ++ [⟨t, value⟩]))
          (p := fun value => ¬ CacheHasCollision (cache.cacheQuery t value))
          (q := fun z => ¬ AdversaryWinsExtractabilityGame z.1)
          (ε₁ := (cached : ENNReal) * C⁻¹)
          (ε₂ := (extractabilityExactPotential treeTargetCount s.depth
            (remaining - 1) (cached + 1) : ENNReal) * C⁻¹)
          (by simpa [not_not] using hcollision)
          (by simpa [not_not] using hcontinuation)
        simp only [not_not] at hcombined
        refine hcombined.trans ?_
        rw [← add_mul]
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast extractabilityExactPotential_miss_le
            treeTargetCount s.depth remaining cached hremaining
        · exact zero_le

/-- Initialize the stopping-time induction at the empty cache and empty log, then transport
the combined caching/logging semantics back to `extractabilityGame`. -/
private lemma extractability_win_le_stopping_bound
    [DecidableEq α] [Finite α] [Inhabited α] [IsUniformSpec (spec α)]
    {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    Pr[AdversaryWinsExtractabilityGame | extractabilityGame 𝒜] ≤
      (extractabilityExactPotential (2 * s.leafCount - 1) s.depth qb 0 : ENNReal) *
        (@Fintype.card ((spec α).Range default)
          (OracleSpec.instFintypeRangeOfFintype default) : ENNReal)⁻¹ := by
  have hmain : Pr[fun z => AdversaryWinsExtractabilityGame z.1 |
      extractabilityRunFrom 𝒜 𝒜.commit ∅ []] ≤
      (extractabilityExactPotential (2 * s.leafCount - 1) s.depth qb 0 : ENNReal) *
        (@Fintype.card ((spec α).Range default)
          (OracleSpec.instFintypeRangeOfFintype default) : ENNReal)⁻¹ := by
    apply extractabilityRunFrom_le_potential 𝒜 𝒜.commit qb 0 h ∅ []
    · intro hcollision
      obtain ⟨_, _, _, _, _, hcached, _, _⟩ := hcollision
      simp at hcached
    · exact ⟨∅, by simp, fun input hinput => absurd (by simp : (∅ :
        (spec α).QueryCache) input = none) hinput⟩
    · simp
    · simp
  rw [extractabilityRunFrom,
    cachingLoggingOracle.run_simulateQ_eq_map_run_simulateQ_withQueryLog] at hmain
  simp only [List.nil_append] at hmain
  rw [extractabilityGame, OracleSpec.withCacheOverlay, StateT.run'_eq,
    extractabilityInner_eq_commit_bind_rest, simulateQ_bind, StateT.run_bind,
    probEvent_map]
  simpa [Function.comp_def] using hmain

/-- Unrelaxed stopping-time error numerator for Merkle extractability in the shared ROM.
The finite maximum ranges over the number `commitMisses` of fresh, distinct commit inputs.
Repeated commit queries consume the total budget but do not increase `commitMisses` or the
cache size. -/
def extractabilityROMErrorNumerator (s : Skeleton) (qb : ℕ) : ℕ :=
  (Finset.range (qb + 1)).sup fun commitMisses =>
    commitMisses.choose 2 +
      min (2 * s.leafCount - 1) (2 * commitMisses + 1) *
        (qb - commitMisses + s.depth)

/-- **Unrelaxed finite-maximum ROM extractability bound for inductive Merkle trees.**

For a two-phase adversary with structural total query bound `qb`, extraction failure in the
single shared lazy random function is at most `extractabilityROMErrorNumerator s qb / |α|`.
The finite maximum tracks fresh commit inputs rather than conditioning on a realized phase
length. The proof is therefore valid when the adversary adaptively decides when to stop its
commit phase and when it repeats cached queries. -/
theorem extractability_rom_bound
    [DecidableEq α] [Fintype α] [Inhabited α] [IsUniformSpec (spec α)]
    {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    Pr[AdversaryWinsExtractabilityGame | extractabilityGame 𝒜] ≤
      (extractabilityROMErrorNumerator s qb : ENNReal) *
        (Fintype.card α : ENNReal)⁻¹ := by
  have hbound := extractability_win_le_stopping_bound 𝒜 qb h
  have hcard :
      @Fintype.card ((spec α).Range default)
          (OracleSpec.instFintypeRangeOfFintype default) = Fintype.card α :=
    @Fintype.card_congr ((spec α).Range default) α
      (OracleSpec.instFintypeRangeOfFintype default) inferInstance (Equiv.refl α)
  simpa only [extractabilityExactPotential, extractabilityEnergy,
    extractabilityROMErrorNumerator, Nat.mul_zero, Nat.zero_add, hcard] using hbound

private lemma target_mul_sub_add_choose_le_choose
    (targetCount qb commitMisses : ℕ)
    (hqb : 2 * targetCount + 1 ≤ qb) (hmisses : commitMisses ≤ qb) :
    targetCount * (qb - commitMisses) + commitMisses.choose 2 ≤ qb.choose 2 := by
  rw [Nat.choose_two_right qb, Nat.le_div_iff_mul_le (by omega : 0 < 2)]
  have hchoose : 2 * commitMisses.choose 2 ≤ commitMisses * (commitMisses - 1) := by
    rw [Nat.choose_two_right]
    simpa [mul_comm] using
      Nat.div_mul_le_self (commitMisses * (commitMisses - 1)) 2
  have hqbPred : qb - 1 + 1 = qb := by omega
  have hqbMisses : qb - commitMisses + commitMisses = qb := by omega
  by_cases hzero : commitMisses = 0
  · subst commitMisses
    norm_num
    nlinarith
  have hmissesPred : commitMisses - 1 + 1 = commitMisses := by omega
  have hpoly : 2 * targetCount * (qb - commitMisses) +
      commitMisses * (commitMisses - 1) ≤ qb * (qb - 1) := by
    nlinarith
  nlinarith

private lemma choose_le_target_mul
    (targetCount commitMisses : ℕ) (hmisses : commitMisses ≤ 2 * targetCount + 1) :
    commitMisses.choose 2 ≤ targetCount * commitMisses := by
  rw [Nat.choose_two_right]
  apply Nat.div_le_of_le_mul
  have hpred : commitMisses - 1 ≤ 2 * targetCount := by omega
  have hmul := Nat.mul_le_mul_left commitMisses hpred
  nlinarith

private lemma extractabilityROMErrorNumerator_le_coarse (s : Skeleton) (qb : ℕ) :
    extractabilityROMErrorNumerator s qb ≤
      max ((2 * s.leafCount - 1) * qb) (qb.choose 2) +
        (2 * s.leafCount - 1) * s.depth := by
  let targetCount := 2 * s.leafCount - 1
  unfold extractabilityROMErrorNumerator
  apply Finset.sup_le
  intro commitMisses hcommitMisses
  have hmisses : commitMisses ≤ qb := by
    simp only [Finset.mem_range] at hcommitMisses
    omega
  by_cases hlarge : 2 * targetCount + 1 ≤ qb
  · have hcap : min targetCount (2 * commitMisses + 1) ≤ targetCount := min_le_left _ _
    calc
      commitMisses.choose 2 + min targetCount (2 * commitMisses + 1) *
            (qb - commitMisses + s.depth)
        ≤ commitMisses.choose 2 + targetCount * (qb - commitMisses + s.depth) := by
          gcongr
      _ = (targetCount * (qb - commitMisses) + commitMisses.choose 2) +
            targetCount * s.depth := by ring
      _ ≤ qb.choose 2 + targetCount * s.depth :=
        Nat.add_le_add_right
          (target_mul_sub_add_choose_le_choose targetCount qb commitMisses hlarge hmisses) _
      _ ≤ max (targetCount * qb) (qb.choose 2) + targetCount * s.depth :=
        Nat.add_le_add_right (le_max_right _ _) _
  · have hcap : min targetCount (2 * commitMisses + 1) ≤ targetCount := min_le_left _ _
    have hchoose : commitMisses.choose 2 ≤ targetCount * commitMisses :=
      choose_le_target_mul targetCount commitMisses (by omega)
    calc
      commitMisses.choose 2 + min targetCount (2 * commitMisses + 1) *
            (qb - commitMisses + s.depth)
        ≤ targetCount * commitMisses + targetCount * (qb - commitMisses + s.depth) :=
          Nat.add_le_add hchoose (by gcongr)
      _ = targetCount * (qb + s.depth) := by
        rw [Nat.mul_add, Nat.mul_add, ← Nat.add_assoc, ← Nat.mul_add]
        congr 2
        omega
      _ = targetCount * qb + targetCount * s.depth := by rw [Nat.mul_add]
      _ ≤ max (targetCount * qb) (qb.choose 2) + targetCount * s.depth :=
        Nat.add_le_add_right (le_max_left _ _) _

/-- Unconditional two-endpoint relaxation of the unrelaxed finite maximum. This is the direct
counterpart of the maximum appearing before the final case split in the source proof. -/
theorem extractability_rom_bound_coarse
    [DecidableEq α] [Fintype α] [Inhabited α] [IsUniformSpec (spec α)]
    {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    Pr[AdversaryWinsExtractabilityGame | extractabilityGame 𝒜] ≤
      ((max ((2 * s.leafCount - 1) * qb) (qb.choose 2) +
        (2 * s.leafCount - 1) * s.depth : ℕ) : ENNReal) *
        (Fintype.card α : ENNReal)⁻¹ := by
  refine (extractability_rom_bound 𝒜 qb h).trans ?_
  gcongr
  exact_mod_cast extractabilityROMErrorNumerator_le_coarse s qb

/-- Once `qb ≥ 2T + 1`, the birthday endpoint dominates the other coarse endpoint. -/
theorem extractability_rom_bound_birthday_dominates
    [DecidableEq α] [Fintype α] [Inhabited α] [IsUniformSpec (spec α)]
    {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb)
    (hqb : 2 * (2 * s.leafCount - 1) + 1 ≤ qb) :
    Pr[AdversaryWinsExtractabilityGame | extractabilityGame 𝒜] ≤
      ((qb.choose 2 + (2 * s.leafCount - 1) * s.depth : ℕ) : ENNReal) *
        (Fintype.card α : ENNReal)⁻¹ := by
  let targetCount := 2 * s.leafCount - 1
  have htwice : 2 * targetCount ≤ qb - 1 := by omega
  have hmul : qb * (2 * targetCount) ≤ qb * (qb - 1) :=
    Nat.mul_le_mul_left qb htwice
  have hdominates : targetCount * qb ≤ qb.choose 2 := by
    rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by omega : 0 < 2)]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul
  simpa only [targetCount, max_eq_right hdominates] using
    extractability_rom_bound_coarse 𝒜 qb h

/-- Textbook-shaped quadratic corollary. Besides birthday dominance, it suffices that
`2·T·depth ≤ qb`; these two explicit conditions are weaker than the convenient single
condition used in the Chiesa–Yogev presentation. -/
theorem extractability_rom_bound_quadratic
    [DecidableEq α] [Fintype α] [Inhabited α] [IsUniformSpec (spec α)]
    {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb)
    (hdominance : 2 * (2 * s.leafCount - 1) + 1 ≤ qb)
    (hdepth : 2 * (2 * s.leafCount - 1) * s.depth ≤ qb) :
    Pr[AdversaryWinsExtractabilityGame | extractabilityGame 𝒜] ≤
      (qb : ENNReal) ^ 2 / (2 * Fintype.card α) := by
  let targetCount := 2 * s.leafCount - 1
  let numerator := qb.choose 2 + targetCount * s.depth
  have hchoose : 2 * qb.choose 2 ≤ qb * (qb - 1) := by
    rw [Nat.choose_two_right]
    simpa only [mul_comm] using Nat.div_mul_le_self (qb * (qb - 1)) 2
  have hqbpos : 0 < qb := by omega
  have hnat : 2 * numerator ≤ qb ^ 2 := by
    calc
      2 * numerator = 2 * qb.choose 2 + 2 * targetCount * s.depth := by
        simp only [numerator]
        ring
      _ ≤ qb * (qb - 1) + qb := Nat.add_le_add hchoose (by
        simpa only [targetCount] using hdepth)
      _ = qb * ((qb - 1) + 1) := by ring
      _ = qb ^ 2 := by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hqbpos.ne')]; ring
  have hbase := extractability_rom_bound_birthday_dominates 𝒜 qb h hdominance
  refine hbase.trans ?_
  change (numerator : ENNReal) * (Fintype.card α : ENNReal)⁻¹ ≤
    (qb : ENNReal) ^ 2 / (2 * Fintype.card α)
  calc
    (numerator : ENNReal) * (Fintype.card α : ENNReal)⁻¹ =
        (numerator : ENNReal) / Fintype.card α := by
      rw [ENNReal.div_eq_inv_mul, mul_comm]
    _ = ((2 : ENNReal) * numerator) / (2 * Fintype.card α) := by
      symm
      exact ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)
    _ ≤ (qb : ENNReal) ^ 2 / (2 * Fintype.card α) := by
      apply ENNReal.div_le_div_right
      exact_mod_cast hnat

private lemma chainInLog_mono {s : Skeleton} (idx : SkeletonLeafIndex s)
    {log1 log2 : (spec α).QueryLog} {root leaf : α}
    {proof : List.Vector α idx.depth}
    (h_sub : ∀ q, q ∈ log1 → q ∈ log2)
    (h_chain : ChainInLog log1 leaf root idx proof) :
    ChainInLog log2 leaf root idx proof := by
  induction idx generalizing root with
  | ofLeaf => exact h_chain
  | @ofLeft sl sr idxLeft ih | @ofRight sl sr idxRight ih =>
    obtain ⟨ancestor, h_mem, h_rec⟩ := h_chain
    exact ⟨ancestor, h_sub _ h_mem, ih h_rec⟩

private lemma chainInLog_of_mem_support_getPutativeRoot
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (leaf : α) (proof : List.Vector α idx.depth) (r : α)
    (log_v : (spec α).QueryLog)
    (hmem : (r, log_v) ∈ support
        (getPutativeRoot (m := OracleComp (spec α)) idx leaf proof).withQueryLog) :
    ChainInLog log_v leaf r idx proof := by
  induction idx generalizing r log_v with
  | ofLeaf =>
    rw [show (getPutativeRoot (m := OracleComp (spec α))
        SkeletonLeafIndex.ofLeaf leaf proof) = pure leaf from rfl,
      OracleComp.withQueryLog_pure, mem_support_pure_iff] at hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
    rfl
  | @ofLeft sl sr idxLeft ih =>
    obtain ⟨a, log_a, h_rec, rfl⟩ :=
      getPutativeRoot_step_withQueryLog_decompose
        (getPutativeRoot (m := OracleComp (spec α)) idxLeft leaf proof.tail)
        (fun a => (a, proof.head)) r log_v hmem
    exact ⟨a, by simp, chainInLog_mono _ (fun _ => List.mem_append_left _)
      (ih proof.tail a log_a h_rec)⟩
  | @ofRight sl sr idxRight ih =>
    obtain ⟨a, log_a, h_rec, rfl⟩ :=
      getPutativeRoot_step_withQueryLog_decompose
        (getPutativeRoot (m := OracleComp (spec α)) idxRight leaf proof.tail)
        (fun a => (proof.head, a)) r log_v hmem
    exact ⟨a, by simp, chainInLog_mono _ (fun _ => List.mem_append_left _)
      (ih proof.tail a log_a h_rec)⟩

/--
If a particular transcript is in the support of a successful `verifyProof` computation
with the query log,
then that log contains a hash chain from `root` down to `leaf`.
-/
private lemma chainInLog_of_mem_support_verifyProof
    [DecidableEq α]
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (leaf root : α) (proof : List.Vector α idx.depth)
    (log_v : (spec α).QueryLog)
    (hmem : (true, log_v) ∈ support
        (verifyProof (m := OracleComp (spec α)) idx leaf root proof).withQueryLog) :
    ChainInLog log_v leaf root idx proof := by
  grind [ChainInLog, OracleComp.withQueryLog_bind, chainInLog_of_mem_support_getPutativeRoot]

/-- **Log-level binding (Collision Lemma at the log level).** Log-formalized
analog of `getPutativeRootWithHash_binding_collision`: two distinct openings
`(x, proof₁) ≠ (y, proof₂)` of the same `root` at the same index, both
witnessed by hash chains `ChainInLog` in the same `log`, force `log` to
contain a hash collision (two log entries with equal responses but distinct
inputs). -/
theorem logHasCollision_of_chainInLog_of_ne
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (log : (spec α).QueryLog) (root x y : α)
    (proof₁ proof₂ : List.Vector α idx.depth)
    (hne : (x, proof₁) ≠ (y, proof₂))
    (hc₁ : ChainInLog log x root idx proof₁)
    (hc₂ : ChainInLog log y root idx proof₂) :
    LogHasCollision log := by
  induction idx generalizing root x y with
  | ofLeaf =>
    exact absurd (Prod.ext (hc₁.trans hc₂.symm) (List.Vector.ext (fun i => i.elim0))) hne
  | @ofLeft sl sr idxLeft ih =>
    obtain ⟨a₁, h₁_mem, hc₁⟩ := hc₁
    obtain ⟨a₂, h₂_mem, hc₂⟩ := hc₂
    by_cases hpair : (a₁, proof₁.head) = (a₂, proof₂.head)
    · obtain ⟨rfl, hhead⟩ := Prod.mk.inj hpair
      refine ih _ _ _ _ _ (fun heq => hne ?_) hc₁ hc₂
      obtain ⟨rfl, htail⟩ := Prod.mk.inj heq
      exact Prod.ext rfl (((List.Vector.eq_cons_iff _ _ _).mpr
        ⟨hhead, htail⟩).trans proof₂.cons_head_tail)
    · exact LogHasCollision.of_mem (fun h => hpair (congrArg Sigma.fst h))
        h₁_mem h₂_mem (heq_of_eq rfl)
  | @ofRight sl sr idxRight ih =>
    obtain ⟨a₁, h₁_mem, hc₁⟩ := hc₁
    obtain ⟨a₂, h₂_mem, hc₂⟩ := hc₂
    by_cases hpair : (proof₁.head, a₁) = (proof₂.head, a₂)
    · obtain ⟨hhead, rfl⟩ := Prod.mk.inj hpair
      refine ih _ _ _ _ _ (fun heq => hne ?_) hc₁ hc₂
      obtain ⟨rfl, htail⟩ := Prod.mk.inj heq
      exact Prod.ext rfl (((List.Vector.eq_cons_iff _ _ _).mpr
        ⟨hhead, htail⟩).trans proof₂.cons_head_tail)
    · exact LogHasCollision.of_mem (fun h => hpair (congrArg Sigma.fst h))
        h₁_mem h₂_mem (heq_of_eq rfl)

/-- Post-IH assembly for the `ofLeft` case of `chainInLog_of_extractor_get_ne_none`.
Given a recursive witness on the left subtree (with ancestor `x`), repackage it
into the witness for the full internal node, using the log entry `⟨(x, y), root⟩`
and consing the sibling `y` onto the extracted proof. -/
private lemma chainInLog_of_extractor_internal_step_left
    [DecidableEq α]
    {sl sr : Skeleton} (idxLeft : SkeletonLeafIndex sl)
    (log : (spec α).QueryLog) (root x y : α)
    (hf : log.find? (fun ⟨_, r⟩ => r == root) = some ⟨(x, y), root⟩)
    (h_rec : ∃ extLeaf : α, ∃ extProof : List.Vector α idxLeft.depth,
        (extractor sl log x).get idxLeft.toNodeIndex = some extLeaf ∧
        (generateProof (extractor sl log x) idxLeft).toList = extProof.toList.map some ∧
        ChainInLog log extLeaf x idxLeft extProof) :
    ∃ extLeaf : α, ∃ extProof : List.Vector α
        (SkeletonLeafIndex.ofLeft (right := sr) idxLeft).depth,
      (extractor (Skeleton.internal sl sr) log root).get
          (SkeletonLeafIndex.ofLeft (right := sr) idxLeft).toNodeIndex = some extLeaf ∧
      (generateProof (extractor (Skeleton.internal sl sr) log root)
          (SkeletonLeafIndex.ofLeft (right := sr) idxLeft)).toList = extProof.toList.map some ∧
      ChainInLog log extLeaf root (SkeletonLeafIndex.ofLeft (right := sr) idxLeft) extProof := by
  obtain ⟨extLeaf, extProof, h_extLeaf, h_extProof, h_chain⟩ := h_rec
  rw [extractor_internal_eq_of_find?_eq sl sr log root x y hf]
  refine ⟨extLeaf, y ::ᵥ extProof, h_extLeaf, ?_, x, List.mem_of_find?_eq_some hf, h_chain⟩
  have h_root_value : (extractor sr log y).getRootValue = some y :=
    optionPopulateDown_getRootValue _ _
  grind [Nat.succ_eq_add_one, List.Vector.toList_cons, SkeletonLeafIndex.depth]

/-- Post-IH assembly for the `ofRight` case of `chainInLog_of_extractor_get_ne_none`.
Symmetric to `chainInLog_of_extractor_internal_step_left`: the recursive witness
lives on the right subtree (ancestor `y`) and the sibling `x` is consed onto the
extracted proof. -/
private lemma chainInLog_of_extractor_internal_step_right
    [DecidableEq α]
    {sl sr : Skeleton} (idxRight : SkeletonLeafIndex sr)
    (log : (spec α).QueryLog) (root x y : α)
    (hf : log.find? (fun ⟨_, r⟩ => r == root) = some ⟨(x, y), root⟩)
    (h_rec : ∃ extLeaf : α, ∃ extProof : List.Vector α idxRight.depth,
        (extractor sr log y).get idxRight.toNodeIndex = some extLeaf ∧
        (generateProof (extractor sr log y) idxRight).toList = extProof.toList.map some ∧
        ChainInLog log extLeaf y idxRight extProof) :
    ∃ extLeaf : α, ∃ extProof : List.Vector α
        (SkeletonLeafIndex.ofRight (left := sl) idxRight).depth,
      (extractor (Skeleton.internal sl sr) log root).get
          (SkeletonLeafIndex.ofRight (left := sl) idxRight).toNodeIndex = some extLeaf ∧
      (generateProof (extractor (Skeleton.internal sl sr) log root)
          (SkeletonLeafIndex.ofRight (left := sl) idxRight)).toList = extProof.toList.map some ∧
      ChainInLog log extLeaf root (SkeletonLeafIndex.ofRight (left := sl) idxRight) extProof := by
  obtain ⟨extLeaf, extProof, h_extLeaf, h_extProof, h_chain⟩ := h_rec
  rw [extractor_internal_eq_of_find?_eq sl sr log root x y hf]
  refine ⟨extLeaf, x ::ᵥ extProof, h_extLeaf, ?_, y, List.mem_of_find?_eq_some hf, h_chain⟩
  have h_root_value : (extractor sl log x).getRootValue = some x :=
    optionPopulateDown_getRootValue _ _
  grind [Nat.succ_eq_add_one, List.Vector.toList_cons, SkeletonLeafIndex.depth]

/-- **Extractor recovery to a log chain.** When the extractor's path at `idx`
is intact (the value there is `≠ none`), the extracted leaf value and proof
form a hash chain `ChainInLog` in the log. The conclusion bundles three
facts: the extracted leaf (`extLeaf`), the recovered authentication path
(`extProof`), and a chain witness in `log` connecting them to `root`. -/
theorem chainInLog_of_extractor_get_ne_none
    [DecidableEq α]
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (log : (spec α).QueryLog) (root : α)
    (h_ne_none : (extractor s log root).get idx.toNodeIndex ≠ none) :
    ∃ extLeaf : α, ∃ extProof : List.Vector α idx.depth,
      (extractor s log root).get idx.toNodeIndex = some extLeaf ∧
      (generateProof (extractor s log root) idx).toList = extProof.toList.map some ∧
      ChainInLog log extLeaf root idx extProof := by
  induction idx generalizing root with
  | ofLeaf => exact ⟨root, ⟨[], rfl⟩, rfl, rfl, rfl⟩
  | @ofLeft sl sr idxLeft ih =>
    rcases hf : log.find? (fun ⟨_, r⟩ => r == root) with _ | ⟨⟨x, y⟩, r⟩
    · exact absurd (extractor_internal_get_eq_none_of_find?_eq_none
        sl sr log root (Sum.inl idxLeft.toNodeIndex) hf) h_ne_none
    rw [show r = root by grind [find?_eq_some_iff_getElem]] at hf
    exact chainInLog_of_extractor_internal_step_left idxLeft log root x y hf
      (ih x (fun he =>
        h_ne_none (by rw [extractor_internal_eq_of_find?_eq sl sr log root x y hf]; exact he)))
  | @ofRight sl sr idxRight ih =>
    rcases hf : log.find? (fun ⟨_, r⟩ => r == root) with _ | ⟨⟨x, y⟩, r⟩
    · exact absurd (extractor_internal_get_eq_none_of_find?_eq_none
        sl sr log root (Sum.inr idxRight.toNodeIndex) hf) h_ne_none
    rw [show r = root by grind [find?_eq_some_iff_getElem]] at hf
    exact chainInLog_of_extractor_internal_step_right idxRight log root x y hf
      (ih y (fun he =>
        h_ne_none (by rw [extractor_internal_eq_of_find?_eq sl sr log root x y hf]; exact he)))

private theorem extractabilityInner_not_logHasCollision_match
    [DecidableEq α]
    {s : Skeleton} (𝒜 : Adversary α s)
    {root : α} {aux : 𝒜.AuxState} {idx : SkeletonLeafIndex s} {leaf : α}
    {proof : List.Vector α idx.depth}
    {extractedTree : FullData (Option α) s}
    {extractedProof : List.Vector (Option α) idx.depth}
    {log : (spec α).QueryLog}
    (h_not_logHasCollision : ¬ LogHasCollision log)
    (h_ne_none : extractedTree.get idx.toNodeIndex ≠ none)
    (hsupport : ((root, aux, ⟨idx, leaf, proof, extractedTree, extractedProof, true⟩),
                  log) ∈
      support (extractabilityInner 𝒜).withQueryLog) :
    extractedTree.get idx.toNodeIndex = some leaf ∧
      proof.toList.map some = extractedProof.toList := by
  obtain ⟨log_c, log_v, h_vp, h_sub_v, h_sub_c, h_tree_eq, h_proof_ext_eq⟩ :=
    extractabilityInner_support_decompose 𝒜 hsupport
  obtain ⟨extLeaf, extProof, h_extLeaf_eq, h_extProof_eq, h_extChain_lc⟩ :=
    chainInLog_of_extractor_get_ne_none idx log_c root (h_tree_eq ▸ h_ne_none)
  by_cases hpair : (extLeaf, extProof) = (leaf, proof)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    exact ⟨h_tree_eq.symm ▸ h_extLeaf_eq, by rw [h_proof_ext_eq, h_extProof_eq]⟩
  · exact absurd (logHasCollision_of_chainInLog_of_ne idx log root extLeaf leaf
      extProof proof hpair (chainInLog_mono idx h_sub_c h_extChain_lc)
      (chainInLog_mono idx h_sub_v
        (chainInLog_of_mem_support_verifyProof idx leaf root proof log_v h_vp)))
      h_not_logHasCollision

end InductiveMerkleTree
