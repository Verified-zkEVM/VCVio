/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Bridge.Wots
public import Mathlib.Data.Nat.Bitwise
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Option

/-!
# The paper's XMSS programs are FIPS 205's, query for query

Continuing `HashSig.SLHDSA.SHAKE128s.Bridge.Wots`: each XMSS program of the paper model, with its
answers relabelled by `answerEquiv`, is the corresponding FIPS 205 program over the typed
interface mapped through `encImpl FIPS205.params`, with its output read back (`digestEquiv.symm`
for a node, `xmssOfCore` for a signature). The conventions are those of the WOTS+ module: seeds
are paper digests, other nodes and signatures are FIPS 205 values, addresses are paper addresses
given to FIPS 205 through `toAdrs`, and secrets come from the oracle-secret provider.

## Main statements

* `simulateQ_relabel_merkleNode`: `Merkle.node` is `xmssNodeWithSecret`
  (`PerfectMerkleTree.merkleRootM` over WOTS+ leaves) at every node whose leaves have 32-bit
  indices; `simulateQ_relabel_merkleRoot` is the root of a whole XMSS tree.
* `simulateQ_relabel_merkleSign`: `Merkle.sign` is `xmssSignWithSecret`, the authentication path
  first (`intrinsicAuthPathM_eq_ofFnM`), then the WOTS+ signature.
* `simulateQ_relabel_merklePublicKeyFromSignature`: `Merkle.publicKeyFromSignature` is
  `xmssPkFromSigWith`, the WOTS+ public key and then the climb (`simulateQ_relabel_merkleClimb`,
  the paper's fold against `PerfectMerkleTree.climbM`).
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.Bridge

open SLHDSA SLHDSA.Security

/-- Programs of the paper model. -/
local notation "PaperComp" => OracleComp OracleWorld
/-- Programs of FIPS 205 over the typed interface. -/
local notation "TypedComp" => OracleComp (unifSpec + hashSpec FIPS205.core)

/-! ## Merkle helpers -/

/-- The sibling of a node index flips its low bit. -/
theorem sibling_eq_xor (i : ℕ) : PerfectMerkleTree.sibling i = Nat.xor i 1 := by
  unfold PerfectMerkleTree.sibling
  split_ifs with h
  · exact (Nat.xor_one_of_even (Nat.even_iff.mpr h)).symm
  · exact (Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))).symm

/-- The authentication path is the vector of the sibling subtree roots, computed from the leaf
level upward. -/
theorem intrinsicAuthPathM_eq_ofFnM {Y : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (leaf : ℕ → m Y) (nodeHash : ℕ → ℕ → Y → Y → m Y) (idx : ℕ) :
    ∀ z : ℕ, PerfectMerkleTree.intrinsicAuthPathM leaf nodeHash idx z =
      Vector.ofFnM fun j : Fin z =>
        PerfectMerkleTree.merkleRootM leaf nodeHash j.val
          (PerfectMerkleTree.sibling (idx / 2 ^ j.val))
  | 0 => by simp [PerfectMerkleTree.intrinsicAuthPathM]
  | z + 1 => by
    rw [PerfectMerkleTree.intrinsicAuthPathM, Vector.ofFnM_succ, intrinsicAuthPathM_eq_ofFnM]
    rfl

/-! ## XMSS -/

/-- **XMSS nodes** (Algorithm 9): the paper's `Merkle.node` at height `height` and index `index`
is `xmssNodeWithSecret` with the public-hash callbacks and the oracle-secret provider, provided
the leaves below the node have 32-bit indices. -/
theorem simulateQ_relabel_merkleNode (secretSeed publicSeed : Digest) (a : Address) :
    ∀ (height index : ℕ), (index + 1) * 2 ^ height ≤ 2 ^ 32 →
    simulateQ (relabel answerEquiv)
        (Merkle.node secretSeed publicSeed a height index : PaperComp Digest) =
      digestEquiv.symm <$> simulateQ (encImpl FIPS205.params)
        (xmssNodeWithSecret FIPS205.core (PublicHash.f FIPS205.core (digestEquiv publicSeed))
          (PublicHash.tl FIPS205.core (digestEquiv publicSeed))
          (PublicHash.h FIPS205.core (digestEquiv publicSeed))
          (oracleSecret FIPS205.core (Equiv.refl _) (digestEquiv publicSeed)
            (digestEquiv secretSeed)) (toAdrs a) height index : TypedComp _)
  | 0, index, h => by
    rw [Merkle.node, simulateQ_relabel_wotsPublicKey _ _ _ rfl rfl,
      toAdrs_wotsAddress a (by omega)]
    rfl
  | height + 1, index, h => by
    have hpow : 2 ^ height ≥ 1 := Nat.one_le_two_pow
    have h2 : (index + 1) * 2 ^ (height + 1) = (2 * index + 2) * 2 ^ height := by
      rw [pow_succ]; ring
    have hlt : height + 1 < 2 ^ (height + 1) := Nat.lt_two_pow_self
    have hle : 2 ^ (height + 1) ≤ 2 ^ 32 :=
      le_trans (Nat.le_mul_of_pos_left _ (by omega)) h
    have hidx : index < 2 ^ 32 :=
      lt_of_lt_of_le (Nat.lt_succ_self _)
        (le_trans (Nat.le_mul_of_pos_right _ Nat.one_le_two_pow) h)
    rw [Merkle.node, simulateQ_bind,
      simulateQ_relabel_merkleNode secretSeed publicSeed a height (2 * index)
        (by nlinarith), bind_map_left]
    unfold xmssNodeWithSecret
    rw [PerfectMerkleTree.merkleRootM, simulateQ_bind, map_bind]
    refine bind_congr fun l => ?_
    rw [simulateQ_bind,
      simulateQ_relabel_merkleNode secretSeed publicSeed a height (2 * index + 1)
        (by nlinarith), bind_map_left, simulateQ_bind, map_bind]
    refine bind_congr fun r => ?_
    rw [simulateQ_relabel_tweakable_h, toAdrs_merkleNodeAddress a (by omega) hidx]
    rfl

/-- The sibling subtrees of an XMSS authentication path have 32-bit leaf indices. -/
theorem sibling_div_bound (index : Fin (2 ^ subtreeHeight)) (j : Fin subtreeHeight) :
    (PerfectMerkleTree.sibling (index.val / 2 ^ j.val) + 1) * 2 ^ j.val ≤ 2 ^ 32 := by
  have hi : index.val < 512 := index.isLt
  unfold PerfectMerkleTree.sibling
  fin_cases j <;> simp <;> split_ifs <;> omega

/-- **XMSS signing** (Algorithm 10): the paper's `Merkle.sign` is `xmssSignWithSecret` with the
public-hash callbacks and the oracle-secret provider: the authentication path, then the WOTS+
signature. -/
theorem simulateQ_relabel_merkleSign (msg : FIPS205.core.Y) (secretSeed publicSeed : Digest)
    (a : Address) (index : Fin (2 ^ subtreeHeight)) :
    simulateQ (relabel answerEquiv)
        (Merkle.sign (digestEquiv.symm msg) secretSeed publicSeed a index :
          PaperComp XmssSignature) =
      xmssOfCore <$> simulateQ (encImpl FIPS205.params)
        (xmssSignWithSecret FIPS205.core (PublicHash.f FIPS205.core (digestEquiv publicSeed))
          (PublicHash.tl FIPS205.core (digestEquiv publicSeed))
          (PublicHash.h FIPS205.core (digestEquiv publicSeed))
          (oracleSecret FIPS205.core (Equiv.refl _) (digestEquiv publicSeed)
            (digestEquiv secretSeed)) msg (toAdrs a) index.val : TypedComp _) := by
  have hidx : index.val < 2 ^ 32 := lt_of_lt_of_le index.isLt (by decide)
  rw [Merkle.sign, xmssSignWithSecret, intrinsicAuthPathM_eq_ofFnM, simulateQ_bind,
    simulateQ_relabel_sequenceFin digestEquiv.symm subtreeHeight _ _ (fun j => by
      rw [← sibling_eq_xor, simulateQ_relabel_merkleNode _ _ _ _ _ (sibling_div_bound index j)]),
    bind_map_left, simulateQ_bind, map_bind]
  refine bind_congr fun path => ?_
  rw [simulateQ_bind, simulateQ_relabel_wotsSign _ _ _ _ rfl rfl, toAdrs_wotsAddress a hidx,
    bind_map_left, simulateQ_bind, map_bind]
  refine bind_congr fun sig => ?_
  simp only [simulateQ_pure, map_pure]
  rfl

/-- The first `k` steps of the paper's climb from a leaf `v` are `PerfectMerkleTree.climbM` along
the first `k` entries of the authentication path. -/
theorem simulateQ_relabel_merkleClimb (index : Fin (2 ^ subtreeHeight))
    (sig : XmssSig FIPS205.params.params FIPS205.core) (publicSeed : Digest) (a : Address) :
    ∀ k, k ≤ subtreeHeight → ∀ v : FIPS205.core.Y,
    simulateQ (relabel answerEquiv)
        (((List.finRange subtreeHeight).take k).foldlM (fun value j =>
          Hashing.tweakable publicSeed
            (Merkle.nodeAddress a (j.val + 1) (index.val / 2 ^ (j.val + 1)))
            (if index.val / 2 ^ j.val % 2 = 0 then
              bytesBE n value ++ bytesBE n ((xmssOfCore sig).authentication j)
              else bytesBE n ((xmssOfCore sig).authentication j) ++ bytesBE n value))
          (digestEquiv.symm v) : PaperComp Digest) =
      digestEquiv.symm <$> simulateQ (encImpl FIPS205.params)
        (PerfectMerkleTree.climbM
          (xmssNodeHashWith (PublicHash.h FIPS205.core (digestEquiv publicSeed)) (toAdrs a))
          index.val v (sig.auth.toList.take k) : TypedComp _)
  | 0, _, v => by simp
  | k + 1, hk, v => by
    have hk' : k < subtreeHeight := hk
    have hi : index.val < 512 := index.isLt
    have hlen : (sig.auth.toList.take k).length = k := by
      simp only [List.length_take, Vector.length_toList]
      exact Nat.min_eq_left (le_of_lt hk')
    have hk'' : k < FIPS205.params.params.hp := hk'
    rw [List.take_add_one, List.take_add_one,
      List.getElem?_eq_getElem (by simpa using hk'),
      List.getElem?_eq_getElem (by simpa using hk''), Option.toList_some, Option.toList_some,
      List.foldlM_append, simulateQ_bind,
      simulateQ_relabel_merkleClimb index sig publicSeed a k (le_of_lt hk') v, bind_map_left,
      PerfectMerkleTree.climbM_concat, simulateQ_bind, map_bind, hlen]
    refine bind_congr fun child => ?_
    have hz : k + 1 < 2 ^ 32 := by simp only [subtreeHeight] at hk'; omega
    have hidx : index.val / 2 ^ (k + 1) < 2 ^ 32 :=
      lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure, List.getElem_finRange,
      Fin.cast_mk]
    have hauth : (xmssOfCore sig).authentication ⟨k, hk'⟩ =
        digestEquiv.symm (sig.auth.toList[k]'(by simpa using hk'')) := by
      rw [Vector.getElem_toList]
      rfl
    rw [hauth]
    split_ifs
    · rw [simulateQ_relabel_tweakable_h, toAdrs_merkleNodeAddress a hz hidx]
      rfl
    · rw [simulateQ_relabel_tweakable_h, toAdrs_merkleNodeAddress a hz hidx]
      rfl

/-- **XMSS public key from a signature** (Algorithm 11): the paper's
`Merkle.publicKeyFromSignature` is `xmssPkFromSigWith` with the public-hash callbacks: the WOTS+
public key, then the climb. -/
theorem simulateQ_relabel_merklePublicKeyFromSignature (index : Fin (2 ^ subtreeHeight))
    (sig : XmssSig FIPS205.params.params FIPS205.core) (msg : FIPS205.core.Y)
    (publicSeed : Digest) (a : Address) :
    simulateQ (relabel answerEquiv)
        (Merkle.publicKeyFromSignature index (xmssOfCore sig) (digestEquiv.symm msg) publicSeed a :
          PaperComp Digest) =
      digestEquiv.symm <$> simulateQ (encImpl FIPS205.params)
        (xmssPkFromSigWith FIPS205.core (PublicHash.f FIPS205.core (digestEquiv publicSeed))
          (PublicHash.tl FIPS205.core (digestEquiv publicSeed))
          (PublicHash.h FIPS205.core (digestEquiv publicSeed)) index.val sig msg (toAdrs a) :
          TypedComp _) := by
  have hidx : index.val < 2 ^ 32 := lt_of_lt_of_le index.isLt (by decide)
  rw [Merkle.publicKeyFromSignature, xmssPkFromSigWith, simulateQ_bind,
    show (xmssOfCore sig).wots = wotsOfCore sig.wots from rfl,
    simulateQ_relabel_wotsPublicKeyFromSignature _ _ _ _ rfl rfl, toAdrs_wotsAddress a hidx,
    bind_map_left, simulateQ_bind, map_bind]
  refine bind_congr fun leaf => ?_
  have h := simulateQ_relabel_merkleClimb index sig publicSeed a subtreeHeight le_rfl leaf
  rw [List.take_of_length_le (by simp),
    List.take_of_length_le (by simp only [Vector.length_toList]; exact le_rfl)] at h
  exact h

/-- **XMSS roots**: the paper's root of an XMSS tree, `Merkle.node` at height `subtreeHeight`
and index `0`, is `xmssRootWithSecret`. -/
theorem simulateQ_relabel_merkleRoot (secretSeed publicSeed : Digest) (a : Address) :
    simulateQ (relabel answerEquiv)
        (Merkle.node secretSeed publicSeed a subtreeHeight 0 : PaperComp Digest) =
      digestEquiv.symm <$> simulateQ (encImpl FIPS205.params)
        (xmssRootWithSecret FIPS205.core (PublicHash.f FIPS205.core (digestEquiv publicSeed))
          (PublicHash.tl FIPS205.core (digestEquiv publicSeed))
          (PublicHash.h FIPS205.core (digestEquiv publicSeed))
          (oracleSecret FIPS205.core (Equiv.refl _) (digestEquiv publicSeed)
            (digestEquiv secretSeed)) (toAdrs a) : TypedComp _) :=
  simulateQ_relabel_merkleNode secretSeed publicSeed a subtreeHeight 0 (by decide)

end SlhDsaSecurity.Bridge
