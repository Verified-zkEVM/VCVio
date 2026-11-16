/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import VCVio.CryptoFoundations.VectorCommitment.OnlineExtraction
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.StrongBound
public import VCVio.OracleComp.QueryTracking.RandomOracle.CacheOverlay

/-!
# Merkle trees as deterministic vector commitments

An addressed Merkle tree over a skeleton `s`, hashing through the complete queries of a
`MerkleTreeExtractability.NodeQueryModel`, as a `DetVectorCommitment` (`merkleVC`). Positions
`Fin ℓ` are the leaves of `s` through an equivalence `pos`; a message is stored at its leaf through
an encoding `enc` into the hash range and read back through a partial decoding `dec`. The opening
proof is a path-pruned batch opening (`InductiveMerkleTree.BatchOpening`), or `none` for the empty
set of positions, and the check verifies that the opening carries exactly the claimed values and
that its batch proof recomputes the commitment.

## Online extraction

The extractor `merkleExtract` reads the claimed leaves off the commitment-phase query log with the
Merkle transcript extractor (`MerkleTreeExtractor.tree`). Its online extraction error against a
two-phase adversary is bounded by the stateful multi-extractability bound for Merkle trees, for
one commitment and one batch opening
(`merkleVC_onlineExtractionError_le`): the online game for a fixed challenge is the
multi-extractability game of the adversary `onlineMerkleAdversary`, under the same random oracle
(`evalDist_run'_randomOracle_eq_withCacheOverlay`), and an accepted opening that disagrees with
the extracted vector is an accepted opening disagreeing with its checkpoint extraction.

## Main definitions

* `InductiveMerkleTree.SelectedValues.get?`: the value of a selected leaf.
* `merkleVC`: the Merkle tree as a deterministic vector commitment.
* `merkleExtract`: the transcript extractor.
* `onlineMerkleAdversary`: the multi-extractability adversary of a two-phase adversary with a fixed
  challenge.

## Main results

* `merkleVC_onlineExtractionError_le`: the online extraction error is at most
  `multiCheckpointROMErrorNumerator (2L - 1) 1 (L - 1) (qc + qr) / |Y|`, for `L` leaves, a
  commitment phase of at most `qc` queries and a response of at most `qr` queries.
-/

public section

open OracleComp OracleSpec BinaryTree InductiveMerkleTree MerkleTreeMultiExtractability

open scoped ENNReal

namespace InductiveMerkleTree

variable {α β : Type}

/-- The value of the leaf `j` in a tuple of selected values, or `none` if `j` is not selected. -/
def SelectedValues.get? : {s : Skeleton} → {sel : LeafData Bool s} → SelectedValues α sel →
    SkeletonLeafIndex s → Option α
  | _, .leaf true, v, .ofLeaf => some v
  | _, .leaf false, _, .ofLeaf => none
  | _, .internal _ _, v, .ofLeft j => SelectedValues.get? v.1 j
  | _, .internal _ _, v, .ofRight j => SelectedValues.get? v.2 j

/-- Reading a mapped tuple of selected values maps the read value. -/
theorem SelectedValues.get?_map (f : α → β) {s : Skeleton} {sel : LeafData Bool s}
    (v : SelectedValues α sel) (j : SkeletonLeafIndex s) :
    (v.map f).get? j = (v.get? j).map f := by
  induction sel with
  | leaf b => cases b <;> cases j <;> rfl
  | internal l r ihl ihr =>
    cases j with
    | ofLeft j => exact ihl v.1 j
    | ofRight j => exact ihr v.2 j

/-- The selected values of a tree read the tree at every selected leaf, and nothing elsewhere. -/
theorem get?_selectedValues {s : Skeleton} (leaves : LeafData α s) (sel : LeafData Bool s)
    (j : SkeletonLeafIndex s) :
    (selectedValues leaves sel).get? j = if sel.get j then some (leaves.get j) else none := by
  induction sel with
  | leaf b =>
    cases leaves with
    | leaf a => cases b <;> cases j <;> rfl
  | internal l r ihl ihr =>
    cases leaves with
    | internal la ra =>
      cases j with
      | ofLeft j => exact ihl la j
      | ofRight j => exact ihr ra j

end InductiveMerkleTree

namespace MerkleTreeExtractability

variable {Query Address Y : Type}

/-- Build the full Merkle tree over the leaf data `leaves`, hashing each internal node through the
complete query of `model` at its address. -/
def buildTree (model : NodeQueryModel Query Address Y) :
    {s : Skeleton} → (addressKey : SkeletonInternalIndex s → Address) → LeafData Y s →
      OracleComp (Query →ₒ Y) (FullData Y s)
  | _, _, .leaf v => pure (.leaf v)
  | _, addressKey, .internal l r => do
      let left ← buildTree model (fun p => addressKey (.ofLeft p)) l
      let right ← buildTree model (fun p => addressKey (.ofRight p)) r
      let root ← (Query →ₒ Y).query
        (model.mkQuery (addressKey .ofInternal) (left.getRootValue, right.getRootValue))
      pure (.internal root left right)

end MerkleTreeExtractability

namespace MerkleVectorCommitment

variable {Query Address Y Msg : Type} {s : Skeleton} {ℓ : ℕ}

/-- The values claimed by a batch opening, as a partial vector: position `i` reads the selected
value at its leaf `pos i`, decoded by `dec`. -/
def openingClaims (pos : Fin ℓ ≃ SkeletonLeafIndex s) (dec : Y → Option Msg)
    (op : BatchOpening Y s) : PartialVec ℓ Msg :=
  fun i => (op.values.get? (pos i)).bind dec

variable [DecidableEq Y] [DecidableEq Msg]

/-- **The Merkle tree as a deterministic vector commitment.** Positions are the leaves of `s`
through `pos`, and a message is stored at its leaf as `enc` of it.

* `commit` builds the tree and returns its root, keeping the full tree as trapdoor;
* `opening` returns the path-pruned batch opening of the selected leaves, or `none` for the empty
  set of positions;
* `check` accepts `none` exactly for the empty claim, and a batch opening exactly when its decoded
  values are the claim and its proof recomputes the root through `model`. -/
@[expose]
def merkleVC (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (addressKey : SkeletonInternalIndex s → Address) (pos : Fin ℓ ≃ SkeletonLeafIndex s)
    (enc : Msg → Y) (dec : Y → Option Msg) :
    DetVectorCommitment Query Y Msg Y (FullData Y s) (Option (BatchOpening Y s)) ℓ where
  commit m := liftComp (do
    let tree ← MerkleTreeExtractability.buildTree model addressKey
      (LeafData.ofFn s fun j => enc (m (pos.symm j)))
    pure (tree.getRootValue, tree)) (unifSpec + (Query →ₒ Y))
  opening Q tree :=
    let sel := LeafData.ofFn s fun j => decide (pos.symm j ∈ Q)
    if h : sel.anySelected = true then
      some ⟨sel, selectedValues tree.toLeafData sel, generateBatchProof tree sel h⟩
    else none
  check root ans
    | none => pure (decide (∀ i, ans i = none))
    | some op =>
      if openingClaims pos dec op = ans then
        MerkleTreeBatchExtractability.verifyOpening model addressKey root op
      else pure false

/-! ### The extractor and the reduction to multi-extractability -/

section Extraction

variable [DecidableEq Address] [Inhabited Msg]

/-- The transcript extractor: read the leaf `pos i` of the partial tree that the Merkle transcript
extractor reconstructs from the query log under the root, and decode it, with `default` where
nothing is extracted or decoded. -/
@[expose]
def merkleExtract (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (addressKey : SkeletonInternalIndex s → Address) (pos : Fin ℓ ≃ SkeletonLeafIndex s)
    (dec : Y → Option Msg) (log : (Query →ₒ Y).QueryLog) (root : Y) (i : Fin ℓ) : Msg :=
  match (MerkleTreeExtractor.tree model.view s addressKey log root).toLeafData.get (pos i) with
  | some y => (dec y).getD default
  | none => default

/-- The Merkle configuration with the single tag `()`, of skeleton `s` and addresses
`addressKey`. -/
@[expose]
def singleConfig (s : Skeleton) (addressKey : SkeletonInternalIndex s → Address) :
    Configuration Unit Address :=
  ⟨fun _ => s, fun _ => addressKey⟩

variable (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
  (addressKey : SkeletonInternalIndex s → Address) (pos : Fin ℓ ≃ SkeletonLeafIndex s)
  (enc : Msg → Y) (dec : Y → Option Msg)

/-- The opening claims of a response against a root and a commitment-phase log: the batch opening,
if it carries exactly the claimed values. -/
@[expose]
def claimsOf (root : Y) (log : MerkleTreeExtractor.QueryLog Query Y)
    (resp : PartialVec ℓ Msg × Option (BatchOpening Y s)) :
    List (OpeningClaim Query Y (singleConfig s addressKey)) :=
  match resp.2 with
  | none => []
  | some op => if openingClaims pos dec op = resp.1 then [⟨(), ⟨root, log⟩, op⟩] else []

/-- The multi-extractability adversary of a two-phase adversary `A` for the fixed challenge `chal`:
one commitment round runs `A`'s commitment phase and records its root, and the terminal opening
phase runs `A`'s response to `chal` and claims its batch opening. -/
@[expose]
def onlineMerkleAdversary {St Chal : Type}
    (A : DetVectorCommitment.OnlineAdversary Query Y Y St Chal
      (PartialVec ℓ Msg × Option (BatchOpening Y s))) (chal : Chal) :
    Adversary Unit Query Address Y (singleConfig s addressKey) where
  committer :=
    { State := Option (St × Y)
      initialState := none
      commit := fun _ _ => (fun z => ((), z.1, some (z.2, z.1))) <$> A.commit }
  opening privateState extractorState :=
    match privateState with
    | none => pure []
    | some p => claimsOf addressKey pos dec p.2 extractorState.cumulativeLog <$> A.respond p.1 chal

/-- The extractor state after the commitment phase of an online transcript. -/
@[expose]
def stateOf {Chal Resp : Type} (t : DetVectorCommitment.OnlineTranscript Query Y Y Chal Resp) :
    ExtractorState Unit Query Address Y (singleConfig s addressKey) :=
  ExtractorState.empty.record () t.log t.cm

/-- The evaluated opening attempts of an online transcript. -/
@[expose]
def attemptsOf {Chal : Type}
    (t : DetVectorCommitment.OnlineTranscript Query Y Y Chal
      (PartialVec ℓ Msg × Option (BatchOpening Y s))) :
    List (AnyEvaluatedOpeningClaim Unit Query Address Y (singleConfig s addressKey)) :=
  match t.resp.2 with
  | none => []
  | some op =>
    if openingClaims pos dec op = t.resp.1 then [⟨(), ⟨⟨t.cm, [] ++ t.log⟩, op, t.accepted⟩⟩]
    else []

omit [DecidableEq Address] [Inhabited Msg] in
/-- For a fixed challenge, the multi-extractability game of `onlineMerkleAdversary` is the online
game of the Merkle vector commitment, read through `stateOf` and `attemptsOf`. -/
theorem map_extractabilityInner_eq {St Chal : Type}
    (A : DetVectorCommitment.OnlineAdversary Query Y Y St Chal
      (PartialVec ℓ Msg × Option (BatchOpening Y s))) (chal : Chal) :
    (fun z => (z.extractorState, z.attempts)) <$>
        extractabilityInner model (singleConfig s addressKey) 1
          (onlineMerkleAdversary addressKey pos dec A chal) =
      (fun t => (stateOf addressKey t, attemptsOf addressKey pos dec t)) <$>
        (merkleVC model addressKey pos enc dec).onlineGame A chal := by
  simp only [extractabilityInner, SequentialCommitter.runFromEmpty,
    SequentialCommitter.runCommitments, onlineMerkleAdversary, DetVectorCommitment.onlineGame,
    map_bind, bind_assoc, pure_bind, map_pure, OracleComp.withQueryLog_map, bind_map_left,
    Prod.map_fst, Prod.map_snd, id]
  refine bind_congr fun z => ?_
  rw [OracleComp.withQueryLog_bind_fst (A.respond z.1.2 chal) fun r => do
    let a ← verifyOpeningClaims model
      (claimsOf addressKey pos dec z.1.1 (ExtractorState.empty.record () z.2 z.1.1).cumulativeLog r)
    pure (ExtractorState.empty.record () z.2 z.1.1, a)]
  refine bind_congr fun r => ?_
  rcases r with ⟨ans, _ | op⟩
  · simp [claimsOf, merkleVC, stateOf, attemptsOf, verifyOpeningClaims]
  · by_cases h : openingClaims pos dec op = ans
    · simp [claimsOf, merkleVC, stateOf, attemptsOf, verifyOpeningClaims, h]
      rfl
    · simp [claimsOf, merkleVC, stateOf, attemptsOf, verifyOpeningClaims, h]

omit [DecidableEq Msg] in
/-- If the checkpoint extraction of a batch opening is the opening itself, the claimed values of
the opening agree with the extracted vector. -/
theorem claimsAgree_of_extractedOpening_eq
    (cp : Checkpoint Query Y (singleConfig s addressKey) ()) (op : BatchOpening Y s)
    (h : cp.extractedOpening model.view op = op.map some) :
    DetVectorCommitment.ClaimsAgree
      (merkleExtract model addressKey pos dec cp.cumulativeLog cp.root)
      (openingClaims pos dec op) := by
  rw [DetVectorCommitment.claimsAgree_iff]
  intro i v hv
  have hval : selectedValues (cp.extractedTree model.view).toLeafData op.selector =
      op.values.map some := by
    simp only [Checkpoint.extractedOpening, BatchOpening.map] at h
    injection h
  obtain ⟨y, hy, hdy⟩ := Option.bind_eq_some_iff.mp hv
  have hget := congrArg (fun w => w.get? (pos i)) hval
  erw [get?_selectedValues, SelectedValues.get?_map, hy] at hget
  simp only [Option.map_some] at hget
  split_ifs at hget with hsel
  have hleaf := Option.some.inj hget
  unfold merkleExtract
  change v = (match (cp.extractedTree model.view).toLeafData.get (pos i) with
    | some y => (dec y).getD default
    | none => default)
  rw [hleaf]
  simp [hdy]

omit [DecidableEq Address] [Inhabited Msg] in
/-- In the online game, an accepted response either carries a batch opening with exactly the
claimed values, or claims nothing. -/
theorem accepted_of_mem_support_onlineGame {St Chal : Type}
    (A : DetVectorCommitment.OnlineAdversary Query Y Y St Chal
      (PartialVec ℓ Msg × Option (BatchOpening Y s))) (chal : Chal)
    {t : DetVectorCommitment.OnlineTranscript Query Y Y Chal
      (PartialVec ℓ Msg × Option (BatchOpening Y s))}
    (ht : t ∈ support ((merkleVC model addressKey pos enc dec).onlineGame A chal))
    (hacc : t.accepted = true) :
    (∃ op, t.resp.2 = some op ∧ openingClaims pos dec op = t.resp.1) ∨
      (t.resp.2 = none ∧ ∀ i, t.resp.1 i = none) := by
  simp only [DetVectorCommitment.onlineGame, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at ht
  obtain ⟨z, -, r, -, b, hb, rfl⟩ := ht
  rcases r with ⟨ans, _ | op⟩
  · simp only [merkleVC, support_pure, Set.mem_singleton_iff] at hb
    subst hb
    exact Or.inr ⟨rfl, by simpa using hacc⟩
  · by_cases hc : openingClaims pos dec op = ans
    · exact Or.inl ⟨op, rfl, hc⟩
    · simp only [merkleVC, hc, ite_false, support_pure, Set.mem_singleton_iff] at hb
      subst hb
      simp at hacc

/-- An accepted response of the online game whose claims disagree with the extracted vector is an
accepted opening that disagrees with its checkpoint extraction. -/
theorem openingOrEqualRootDisagreement_of_mem_support_onlineGame {St Chal : Type}
    (A : DetVectorCommitment.OnlineAdversary Query Y Y St Chal
      (PartialVec ℓ Msg × Option (BatchOpening Y s))) (chal : Chal)
    {t : DetVectorCommitment.OnlineTranscript Query Y Y Chal
      (PartialVec ℓ Msg × Option (BatchOpening Y s))}
    (ht : t ∈ support ((merkleVC model addressKey pos enc dec).onlineGame A chal))
    (hbad : t.accepted = true ∧
      ¬ DetVectorCommitment.ClaimsAgree (merkleExtract model addressKey pos dec t.log t.cm)
        t.resp.1) :
    OpeningOrEqualRootDisagreement model.view (stateOf addressKey t)
      (attemptsOf addressKey pos dec t) := by
  obtain ⟨hacc, hdis⟩ := hbad
  rcases accepted_of_mem_support_onlineGame model addressKey pos enc dec A chal ht hacc with
    ⟨op, hop, hc⟩ | ⟨-, hnone⟩
  · refine Or.inl ⟨(), ⟨⟨t.cm, [] ++ t.log⟩, op, t.accepted⟩, ?_, ?_, hacc, fun h => hdis ?_⟩
    · simp [attemptsOf, hop, hc]
    · simp [stateOf, ExtractorState.record, ExtractorState.empty]
    · have := claimsAgree_of_extractedOpening_eq model addressKey pos dec ⟨t.cm, [] ++ t.log⟩ op h
      simpa [hc] using this
  · exact absurd (fun i v hv => by simp [hnone i] at hv) hdis

/-- **Online extraction for Merkle trees.** Against a two-phase adversary whose commitment phase
makes at most `qc` oracle queries and whose response makes at most `qr`, with a countable
challenge type, the online extraction error of `merkleExtract` is at most the stateful
multi-extractability error of one checkpoint of a tree with `L` leaves and one batch opening,

`multiCheckpointROMErrorNumerator (2L - 1) 1 (L - 1) (qc + qr) / |Y|`. -/
theorem merkleVC_onlineExtractionError_le [DecidableEq Query] [Finite Y] [SampleableType Y]
    [UniformAnswerMeasure (Query →ₒ Y)] {St Chal : Type} [Countable Chal]
    (sampleChal : ProbComp Chal)
    (A : DetVectorCommitment.OnlineAdversary Query Y Y St Chal
      (PartialVec ℓ Msg × Option (BatchOpening Y s)))
    {qc qr : ℕ} (hc : IsTotalQueryBound A.commit qc)
    (hr : ∀ st chal, IsTotalQueryBound (A.respond st chal) qr) :
    (merkleVC model addressKey pos enc dec).onlineExtractionError
        (merkleExtract model addressKey pos dec) sampleChal A ≤
      (multiCheckpointROMErrorNumerator (2 * s.leafCount - 1) 1 (s.leafCount - 1) (qc + qr) :
        ℝ≥0∞) * (Nat.card Y : ℝ≥0∞)⁻¹ := by
  unfold DetVectorCommitment.onlineExtractionError
  refine DetVectorCommitment.prEvent_onlineRun_le_of_forall_chal _ _ _ _ fun chal => ?_
  let config := singleConfig s addressKey
  let adv := onlineMerkleAdversary addressKey pos dec A chal
  -- An accepted, disagreeing response is a checkpoint disagreement of the reduction.
  refine (prEvent_mono_of_support _ _
    (fun t => OpeningOrEqualRootDisagreement model.view (stateOf addressKey t)
      (attemptsOf addressKey pos dec t))
    fun t ht hbad => openingOrEqualRootDisagreement_of_mem_support_onlineGame model addressKey
      pos enc dec A chal (support_simulateQ_run'_subset _ _ _ ht) hbad).trans ?_
  -- The random-oracle run is the cache-overlay run of the multi-extractability game.
  rw [prEvent_run'_randomOracle_eq_withCacheOverlay,
    ← prEvent_map (f := fun t => (stateOf addressKey t, attemptsOf addressKey pos dec t))
      (p := fun w => OpeningOrEqualRootDisagreement model.view w.1 w.2),
    ← withCacheOverlay_map, ← map_extractabilityInner_eq model addressKey pos enc dec A chal,
    withCacheOverlay_map, prEvent_map]
  change Pr{let z ← extractabilityExperiment model config 1 adv}[
    Transcript.HasOpeningOrEqualRootDisagreement model z] ≤ _
  refine (openingOrEqualRootDisagreement_bound_of_anyCheckpointExtractionDisagreement_bound
    model config 1 adv _
      (anyCheckpointDisagreement_rom_bound_of_phaseQueryBounds_and_openingCountBound
        model config 1 adv (fun _ => qc) qr (2 * s.leafCount - 1) 1 1 (s.leafCount - 1)
        (2 * s.leafCount - 1) ?_ ?_ ?_ (fun _ => le_rfl) (fun _ => le_rfl) (by simp)
        le_rfl)).trans ?_
  · intro _ _
    exact (isQueryBound_map_iff _ _ _ _ _).mpr hc
  · rintro (_ | ⟨st, root⟩) es
    · exact isQueryBound_pure _ _ _ _
    · exact (isQueryBound_map_iff _ _ _ _ _).mpr (hr st chal)
  · rintro (_ | ⟨st, root⟩) es claims hclaims
    · simp [adv, onlineMerkleAdversary] at hclaims
      simp [hclaims]
    · simp only [adv, onlineMerkleAdversary, support_map, Set.mem_image] at hclaims
      obtain ⟨r, -, rfl⟩ := hclaims
      unfold claimsOf
      split
      · simp
      · split <;> simp
  · simp [commitmentQueryBudget]

end Extraction

end MerkleVectorCommitment
