/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ShareClaims
public import HashSig.SLHDSA.SHAKE128s.Proof.HypertreeDispatch
public import HashSig.SLHDSA.SHAKE128s.Proof.Checksum

/-!
# Most of the forgery's claims are the verifier's own queries

`ClaimedProbes.claimedCandidatesOf` records 259 claims: one per FORS tree and one per
(layer, chain) of the hypertree. Almost all of them are inputs the verifier itself hashes:

* a FORS claim is the verifier's leaf hash of the revealed secret
  (`queriesUnder_verify_forsClaim`);
* a WOTS claim whose forged digit is below `w - 1` is the verifier's first chain step on that
  chain, at that digit (`queriesUnder_verify_wotsClaim`, by walking the hypertree recovery in
  `queriesUnder_root_chain`).

Only a chain whose digit is exactly `w - 1` (where the verifier takes no chain step) can give a
claim the verifier does not query. The first checksum digit is `checksum / 256 ≤ 1`, and either
some message digit is below the top or the checksum is zero, so at most 33 of the 35 chains sit
at the top (`card_top_le`). Hence at most `7 * 33 = 231` claims are not verifier queries
(`card_unqueried_claims_le`).
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.ClaimsQueried

open CacheReplay

/-! ## The checksum leaves at least two chains below the top -/

theorem chains_eq : chains = 35 := by decide

theorem messageDigits_eq : messageDigits = 32 := by decide

/-- The first checksum digit is at most one. -/
theorem encode_first_checksum_lt (message : Digest) :
    (Checksum.encode message ⟨32, by rw [chains_eq]; omega⟩).val < w - 1 := by
  have hle := Checksum.checksum_le (Checksum.messageDigit message)
  unfold Checksum.encode
  split
  · rename_i h
    rw [messageDigits_eq] at h
    exact absurd h (lt_irrefl 32)
  · simp only [Checksum.checksumDigit, messageDigits_eq, checksumDigits, w, winternitzBits]
    norm_num
    omega

/-- If every message digit is at the top, the checksum is zero. -/
theorem checksum_eq_zero_of_all_top (message : Digest)
    (htop : ∀ i, (Checksum.messageDigit message i).val = w - 1) :
    Checksum.checksum (Checksum.messageDigit message) = 0 := by
  simp [Checksum.checksum, htop]

/-- **Two distinct chains below the top.** -/
theorem exists_two_below_top (message : Digest) :
    ∃ a b : Fin chains, a ≠ b ∧ (Checksum.encode message a).val ≠ w - 1 ∧
      (Checksum.encode message b).val ≠ w - 1 := by
  have hfirst := encode_first_checksum_lt message
  by_cases htop : ∀ i, (Checksum.messageDigit message i).val = w - 1
  · have hzero := checksum_eq_zero_of_all_top message htop
    refine ⟨⟨33, by rw [chains_eq]; omega⟩, ⟨34, by rw [chains_eq]; omega⟩, by simp, ?_, ?_⟩ <;>
    · simp only [Checksum.encode, messageDigits_eq, Checksum.checksumDigit, hzero,
        checksumDigits]
      norm_num [w, winternitzBits]
  · push Not at htop
    obtain ⟨i, hi⟩ := htop
    have hi32 : i.val < 32 := lt_of_lt_of_eq i.isLt messageDigits_eq
    refine ⟨⟨i.val, by rw [chains_eq]; omega⟩, ⟨32, by rw [chains_eq]; omega⟩, ?_, ?_,
      by omega⟩
    · intro h
      have := congrArg Fin.val h
      simp at this
      omega
    · simpa [Checksum.encode, messageDigits_eq, hi32] using hi

/-- **At most 33 of the 35 chains sit at the top digit.** -/
theorem card_top_le (message : Digest) :
    (Finset.univ.filter fun chain : Fin chains =>
      (Checksum.encode message chain).val = w - 1).card ≤ 33 := by
  classical
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_below_top message
  have hsub : (Finset.univ.filter fun chain : Fin chains =>
      (Checksum.encode message chain).val = w - 1) ⊆ Finset.univ \ {a, b} := by
    intro chain hchain
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hchain
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨fun h => ha (h ▸ hchain), fun h => hb (h ▸ hchain)⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_pair hab,
    Finset.card_univ, Fintype.card_fin, chains_eq]

/-- The same count, over the list of chains. -/
theorem countP_top_le (message : Digest) :
    (List.finRange chains).countP (fun chain =>
      decide ((Checksum.encode message chain).val = w - 1)) ≤ 33 := by
  classical
  have h := card_top_le message
  have hbridge : ∀ (k : Nat) (p : Fin k → Prop) [DecidablePred p],
      (Finset.univ.filter p).card = (List.finRange k).countP (fun x => decide (p x)) := by
    intro k p _
    rw [Fin.univ_def, Finset.card, Finset.filter_val, ← Multiset.countP_eq_card_filter]
    rfl
  rw [← hbridge]
  exact h

/-! ## FORS claims are the verifier's leaf hashes -/

open VerifierProbes in
/-- **Every FORS claim is a verifier query.** -/
theorem queriesUnder_verify_forsClaim (cache : QueryCache HashSpec) (pk : PublicKey)
    (request : Message) (wire message : Bytes) (parsed : Signature)
    (hframe : request.frame = some message) (hparsed : Signature.fromBytes? wire = some parsed)
    (tree : Fin forsTrees) :
    QueriesUnder cache (Scheme.verify (m := OracleComp HashSpec) pk request wire)
      (GraphStakes.inputOf pk.seed
        (GraphStakes.forsLeafNode (SplitCharged.forsKeyOfDigest (digestOf cache pk message parsed))
          (GraphStakes.forsIndex (MessageDigest.forsIndices (digestOf cache pk message parsed))
            tree))
        (parsed.fors tree).secret) :=
  queriesUnder_verify_fors cache pk request wire message parsed hframe hparsed _
    (queriesUnder_fors_leaf cache parsed.fors _ pk.seed _ tree)

/-! ## WOTS claims below the top are the verifier's first chain steps -/

open WotsResidueReduction in
/-- Walking the hypertree recovery: the first chain step at the forged digit of every layer is
queried, whenever that digit is below the top. -/
theorem queriesUnder_root_chain (cache : QueryCache HashSpec) (publicSeed : Digest) :
    ∀ (remaining : Nat) (signatures : Fin remaining → XmssSignature) (layer tree : Nat)
      (leaf : Hypertree.LeafIndex) (message : Digest) (i : Fin remaining) (chain : Fin chains),
      (Checksum.encode (@forgedAt (replayQuery cache) publicSeed remaining signatures layer tree
          leaf message i.val) chain).val < w - 1 →
      QueriesUnder cache
        (Hypertree.rootFromSignature (m := OracleComp HashSpec) publicSeed remaining signatures
          layer tree leaf message)
        (Hashing.tweakableInput publicSeed
          { { Merkle.wotsAddress (Hypertree.address (layerAt layer i.val) (treeAt tree i.val))
                (leafAt leaf tree i.val).val with
              chainOrHeight := BitVec.ofNat 32 chain.val } with
            hashOrIndex := BitVec.ofNat 32
              ((Checksum.encode (@forgedAt (replayQuery cache) publicSeed remaining signatures
                layer tree leaf message i.val) chain).val + 0) }
          (bytesBE n ((signatures i).wots chain))) := by
  intro remaining
  induction remaining with
  | zero => intro _ _ _ _ _ i; exact Fin.elim0 i
  | succ remaining ih =>
    intro signatures layer tree leaf message i chain hdigit
    induction i using Fin.cases with
    | zero =>
      refine @HypertreeDispatch.queriesUnder_rootFromSignature_head cache publicSeed remaining
        signatures layer tree leaf message _ ?_
      refine FaultCharge.queriesUnder_merkle_wots cache leaf (signatures 0) message publicSeed
        _ _ ?_
      have h := FaultCharge.queriesUnder_wots_chain cache (signatures 0).wots message publicSeed
        (Merkle.wotsAddress (Hypertree.address layer tree) leaf.val) chain 0
        (by
          have h' : (Checksum.encode message chain).val < w - 1 := hdigit
          omega)
      exact h
    | succ j =>
      refine @HypertreeDispatch.queriesUnder_rootFromSignature_tail cache publicSeed remaining
        signatures layer tree leaf message _ ?_
      rw [← ShareClaims.merkle_replay]
      exact ih (fun k => signatures k.succ) (layer + 1) (tree / 2 ^ subtreeHeight)
        (Hypertree.nextLeaf tree) _ j chain hdigit

open VerifierProbes WotsResidueReduction ClaimedProbes in
/-- **Every WOTS claim whose forged digit is below the top is a verifier query**: it is the
first chain step the verifier takes on that chain. -/
theorem queriesUnder_verify_wotsClaim (cache : QueryCache HashSpec) (pk : PublicKey)
    (request : Message) (wire message : Bytes) (parsed : Signature)
    (hframe : request.frame = some message) (hparsed : Signature.fromBytes? wire = some parsed)
    (layer : Fin layers) (chain : Fin chains)
    (hdigit : (Checksum.encode (@forgedAt (replayQuery cache) pk.seed layers parsed.hypertree 0
        (MessageDigest.treeIndex (digestOf cache pk message parsed)).toNat
        (MessageDigest.leafIndex (digestOf cache pk message parsed)).toFin
        (forsKeyOf cache pk message parsed) layer.val) chain).val < w - 1) :
    QueriesUnder cache (Scheme.verify (m := OracleComp HashSpec) pk request wire)
      (GraphStakes.inputOf pk.seed
        (GraphStakes.wotsHashNode
          (forgedKey (MessageDigest.treeIndex (digestOf cache pk message parsed)).toFin
            (MessageDigest.leafIndex (digestOf cache pk message parsed)).toFin layer) chain
          (@forgedSteps (replayQuery cache) pk.seed parsed
            (MessageDigest.treeIndex (digestOf cache pk message parsed)).toNat
            (MessageDigest.leafIndex (digestOf cache pk message parsed)).toFin
            (forsKeyOf cache pk message parsed) layer chain))
        ((parsed.hypertree layer).wots chain)) := by
  have h := queriesUnder_root_chain cache pk.seed layers parsed.hypertree 0 _ _ _ layer chain
    hdigit
  have hstep : (@forgedSteps (replayQuery cache) pk.seed parsed
      (MessageDigest.treeIndex (digestOf cache pk message parsed)).toNat
      (MessageDigest.leafIndex (digestOf cache pk message parsed)).toFin
      (forsKeyOf cache pk message parsed) layer chain).val =
      (Checksum.encode (@forgedAt (replayQuery cache) pk.seed layers parsed.hypertree 0
        (MessageDigest.treeIndex (digestOf cache pk message parsed)).toNat
        (MessageDigest.leafIndex (digestOf cache pk message parsed)).toFin
        (forsKeyOf cache pk message parsed) layer.val) chain).val :=
    clampStep_val hdigit
  refine queriesUnder_verify_hypertree cache pk request wire message parsed hframe hparsed _ ?_
  rw [layerAt_eq, Nat.zero_add, Nat.add_zero, ← hstep] at h
  exact h

/-! ## Counting the claims the verifier does not make -/

open VerifierProbes WotsResidueReduction ClaimedProbes in
open scoped Classical in
/-- **At most 231 of the 259 claims are not verifier queries**: every FORS claim is one, and on
each of the seven layers at most 33 of the 35 chains sit at the top digit, where the verifier
takes no chain step. -/
theorem card_unqueried_claims_le (cache : QueryCache HashSpec) (pk : PublicKey)
    (request : Message) (wire message : Bytes) (parsed : Signature)
    (hframe : request.frame = some message) (hparsed : Signature.fromBytes? wire = some parsed) :
    ((@ClaimedProbes.claimedCandidatesOf (CacheReplay.replayQuery cache) pk.seed cache pk message
        parsed).filter fun candidate =>
      decide (¬ CacheReplay.QueriesUnder cache
        (Scheme.verify (m := OracleComp HashSpec) pk request wire) candidate)).length ≤ 231 := by
  rw [← List.countP_eq_length_filter]
  unfold ClaimedProbes.claimedCandidatesOf GraphStakes.claimedCandidates
  rw [List.countP_append, List.countP_flatMap]
  have hfors : ((List.finRange forsTrees).map fun tree =>
      GraphStakes.inputOf pk.seed
        (GraphStakes.forsLeafNode (SplitCharged.forsKeyOfDigest (digestOf cache pk message parsed))
          (GraphStakes.forsIndex (MessageDigest.forsIndices (digestOf cache pk message parsed))
            tree))
        (parsed.fors tree).secret).countP (fun candidate =>
      decide (¬ CacheReplay.QueriesUnder cache
        (Scheme.verify (m := OracleComp HashSpec) pk request wire) candidate)) = 0 := by
    rw [List.countP_eq_zero]
    intro candidate hcandidate
    obtain ⟨tree, -, rfl⟩ := List.mem_map.mp hcandidate
    simpa using queriesUnder_verify_forsClaim cache pk request wire message parsed hframe hparsed
      tree
  rw [hfors, Nat.zero_add]
  refine (List.sum_le_length_nsmul _ 33 ?_).trans (by simp [layers])
  intro count hcount
  obtain ⟨layer, -, rfl⟩ := List.mem_map.mp hcount
  simp only [Function.comp_apply, List.countP_map]
  refine le_trans (List.countP_mono_left fun chain _ hchain => ?_)
    (countP_top_le (@forgedAt (replayQuery cache) pk.seed layers parsed.hypertree 0
      (MessageDigest.treeIndex (digestOf cache pk message parsed)).toNat
      (MessageDigest.leafIndex (digestOf cache pk message parsed)).toFin
      (forsKeyOf cache pk message parsed) layer.val))
  simp only [Function.comp_apply, decide_eq_true_eq] at hchain ⊢
  by_contra hne
  have hlt : (Checksum.encode (@forgedAt (replayQuery cache) pk.seed layers parsed.hypertree 0
      (MessageDigest.treeIndex (digestOf cache pk message parsed)).toNat
      (MessageDigest.leafIndex (digestOf cache pk message parsed)).toFin
      (forsKeyOf cache pk message parsed) layer.val) chain).val < w - 1 := by
    have := (Checksum.encode (@forgedAt (replayQuery cache) pk.seed layers parsed.hypertree 0
      (MessageDigest.treeIndex (digestOf cache pk message parsed)).toNat
      (MessageDigest.leafIndex (digestOf cache pk message parsed)).toFin
      (forsKeyOf cache pk message parsed) layer.val) chain).isLt
    omega
  exact hchain (queriesUnder_verify_wotsClaim cache pk request wire message parsed hframe hparsed
    layer chain hlt)

end SlhDsaSecurity.ClaimsQueried
