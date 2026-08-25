/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Wots
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed

/-!
# XMSS (FIPS 205 §6)

XMSS (`xmssNode`, `xmssSign`, `xmssPkFromSig`; Algorithms 9–11) is the node-addressed perfect
Merkle tree `PerfectMerkleTree` (`VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed`)
with WOTS+ public keys as leaves and `H` under the `TREE` address of each node as the node hash.
That layer is itself the generic `AddressedMerkleTree` engine specialised to heap-style
`(height, index)` addressing, so both its completeness and its oriented binding theorem are
available here:

* `xmssPkFromSig_xmssSign` — XMSS correctness, from `PerfectMerkleTree.climb_authPath` together
  with WOTS+ correctness (`wotsPkFromSig_wotsSign`);
* `xmssPkFromSig_binding` — an XMSS signature whose recovered leaf differs from the honest WOTS+
  public key but which still recovers the honest root exhibits a collision of `H` at some `TREE`
  address, against the honestly precommitted child pair. This is the hook for the multi-target
  target-collision term of `slhdsa_euf_cma_security`.

## References

- NIST FIPS 205, §6 (Algorithms 9–11)
-/

@[expose] public section


namespace SLHDSA

variable {p : Params}

/-! ### XMSS over WOTS+ leaves (FIPS 205 §6) -/

/-- Base WOTS+ address for the leaf at keypair index `t` (type `WOTS_HASH`). -/
def wotsLeafAdrs (adrs : Adrs) (t : ℕ) : Adrs :=
  (adrs.setTypeAndClear .wotsHash).setKeyPairAddress t

/-- The XMSS leaf value at index `t`: the WOTS+ public key of keypair `t`. -/
def xmssLeaf (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (t : ℕ) : prims.Y :=
  wotsPkGen prims sk pk (wotsLeafAdrs adrs t)

/-- The `TREE`-type address of the XMSS node at tree position `(height z, index t)`. -/
def xmssNodeAdrs (adrs : Adrs) (z t : ℕ) : Adrs :=
  ((adrs.setTypeAndClear .tree).setTreeHeight z).setTreeIndex t

/-- The XMSS internal-node hash at tree position `(height z, index t)` (type `TREE`). -/
def xmssNodeHash (prims : Primitives p) (pk : prims.PkSeed) (adrs : Adrs)
    (z t : ℕ) (l r : prims.Y) : prims.Y :=
  prims.H pk (xmssNodeAdrs adrs z t) l r

/-- The XMSS subtree root at `(height z, index t)` (FIPS 205 Algorithm 9). -/
def xmssNode (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (z t : ℕ) : prims.Y :=
  PerfectMerkleTree.merkleRoot (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs) z t

/-- The XMSS tree root (height `h'`, index `0`) — the value committed by key generation. -/
def xmssRoot (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    prims.Y :=
  xmssNode prims sk pk adrs p.hp 0

/-- An XMSS signature: a WOTS+ signature of the leaf message paired with the authentication
path (`h'` sibling nodes). -/
abbrev XmssSig (p : Params) (prims : Primitives p) := WotsSig p prims × List prims.Y

/-- XMSS signing (FIPS 205 Algorithm 10): WOTS+-sign at leaf `idx` and emit the auth path. -/
def xmssSign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) : XmssSig p prims :=
  (wotsSign prims msg sk pk (wotsLeafAdrs adrs idx),
    PerfectMerkleTree.authPath (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs) idx p.hp)

/-- XMSS root recovery from a signature (FIPS 205 Algorithm 11): recover the WOTS+ public key
(the leaf) then climb the auth path. -/
def xmssPkFromSig (prims : Primitives p) (idx : ℕ) (sig : XmssSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) : prims.Y :=
  PerfectMerkleTree.climb (xmssNodeHash prims pk adrs) idx
    (wotsPkFromSig prims sig.1 msg pk (wotsLeafAdrs adrs idx)) sig.2

/-- **XMSS correctness** (FIPS 205, Algorithms 9–11): root recovery from an honest signature at
leaf `idx < 2^{h'}` reproduces the XMSS tree root. Composes WOTS+ correctness with the Merkle
auth-path consistency lemma. -/
theorem xmssPkFromSig_xmssSign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ) (hidx : idx < 2 ^ p.hp) :
    xmssPkFromSig prims idx (xmssSign prims msg sk pk adrs idx) msg pk adrs
      = xmssRoot prims sk pk adrs := by
  unfold xmssPkFromSig xmssSign xmssRoot xmssNode
  dsimp only
  rw [wotsPkFromSig_wotsSign]
  have key := PerfectMerkleTree.climb_authPath (xmssLeaf prims sk pk adrs)
    (xmssNodeHash prims pk adrs) idx p.hp
  rw [Nat.div_eq_of_lt hidx] at key
  exact key

/-- **XMSS binding.** A signature at leaf `idx < 2^{h'}` with a well-formed authentication path
whose recovered WOTS+ public key differs from the honest leaf, yet which recovers the honest XMSS
root, exhibits a collision of `H` at the `TREE` address of some internal node `(h, i)`: the
honestly computed child pair at that node and a distinct pair hash to the same value. The first
endpoint is fixed by the honest tree (a valid target for a target-collision reduction). -/
theorem xmssPkFromSig_binding (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ) (hidx : idx < 2 ^ p.hp)
    (sig : XmssSig p prims) (hlen : sig.2.length = p.hp)
    (hroot : xmssPkFromSig prims idx sig msg pk adrs = xmssRoot prims sk pk adrs)
    (hne : xmssLeaf prims sk pk adrs idx
      ≠ wotsPkFromSig prims sig.1 msg pk (wotsLeafAdrs adrs idx)) :
    ∃ (h i : ℕ) (c : prims.Y × prims.Y), 0 < h ∧ h ≤ p.hp ∧
      (xmssNode prims sk pk adrs (h - 1) (2 * i), xmssNode prims sk pk adrs (h - 1) (2 * i + 1))
        ≠ c ∧
      prims.H pk (xmssNodeAdrs adrs h i) (xmssNode prims sk pk adrs (h - 1) (2 * i))
          (xmssNode prims sk pk adrs (h - 1) (2 * i + 1))
        = prims.H pk (xmssNodeAdrs adrs h i) c.1 c.2 := by
  have hroot' : PerfectMerkleTree.climb (xmssNodeHash prims pk adrs) idx
      (wotsPkFromSig prims sig.1 msg pk (wotsLeafAdrs adrs idx)) sig.2
      = PerfectMerkleTree.merkleRoot (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs)
          p.hp (idx / 2 ^ p.hp) := by
    rw [Nat.div_eq_of_lt hidx]; exact hroot
  exact PerfectMerkleTree.climb_binding (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs)
    p.hp idx _ sig.2 hlen hroot' hne

end SLHDSA
