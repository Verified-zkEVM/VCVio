/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Bolton Bailey
-/

module
public import HashSig.SLHDSA.Wots
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Monadic
import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.QueryBound

/-!
# XMSS (FIPS 205 §6)

XMSS (`xmssNode`, `xmssSign`, `xmssPkFromSig`; Algorithms 9–11) is the node-addressed perfect
Merkle tree `PerfectMerkleTree` with WOTS+ public keys as leaves and `H` under the `TREE` address
of each node as the node hash. Its effectful algorithms have callback-parametric owner
implementations, specialized below to explicit public-hash queries. The `simulateQ_*` parity
theorems identify their canonical deterministic interpretation with the pure API, which is itself
an `Id` interpretation of the same owner implementations. More generally, they identify any fixed
answer table with the pure scheme induced by `withPublicHash`.
The Merkle layer is itself the generic `AddressedMerkleTree` engine specialised to heap-style
`(height, index)` addressing, so its completeness, naturality, and oriented binding theorems are
available here:

* `xmssPkFromSig_xmssSign` — XMSS correctness, from `PerfectMerkleTree.climb_authPath` together
  with WOTS+ correctness (`wotsPkFromSig_wotsSign`);
* `xmssPkFromSig_binding` — an XMSS signature whose recovered leaf differs from the honest WOTS+
  public key but which still recovers the honest root exhibits a collision of `H` at the `TREE`
  address `(h, idx / 2 ^ h)` of an ancestor of leaf `idx`, against the honestly precommitted
  child pair. This deterministic statement is the Merkle-layer hook needed by a future
  seed-aware multi-target target-collision reduction; it is not itself such a reduction.

## References

- NIST FIPS 205, §6 (Algorithms 9–11)
-/

@[expose] public section


namespace SLHDSA

open OracleComp

variable {p : Params}

/-! ### XMSS over WOTS+ leaves (FIPS 205 §6) -/

/-- Base WOTS+ address for the leaf at keypair index `t` (type `WOTS_HASH`). -/
def wotsLeafAdrs (adrs : Adrs) (t : ℕ) : Adrs :=
  (adrs.setTypeAndClear .wotsHash).setKeyPairAddress t

/-- The `TREE`-type address of the XMSS node at tree position `(height z, index t)`. -/
def xmssNodeAdrs (adrs : Adrs) (z t : ℕ) : Adrs :=
  ((adrs.setTypeAndClear .tree).setTreeHeight z).setTreeIndex t

/-- An XMSS signature: a WOTS+ signature of the leaf message paired with the authentication
path (`h'` sibling nodes). -/
abbrev XmssSig (p : Params) (prims : Primitives p) := WotsSig p prims × List prims.Y

/-! ### Callback-parametric owner implementations -/

/-- Callback-parametric XMSS leaf computation: generate the WOTS+ public key at leaf `t`. -/
def xmssLeafWith (prims : Primitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → prims.Y → m prims.Y)
    (compress : Adrs → List prims.Y → m prims.Y)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) : m prims.Y :=
  wotsPkGenWith prims hash compress sk pk (wotsLeafAdrs adrs t)

/-- Apply the callback for the XMSS internal node at `(height z, index t)`. -/
def xmssNodeHashWith {Y : Type} {m : Type → Type*}
    (nodeHash : Adrs → Y → Y → m Y) (adrs : Adrs)
    (z t : ℕ) (l r : Y) : m Y :=
  nodeHash (xmssNodeAdrs adrs z t) l r

/-- Callback-parametric owner implementation of the subtree root at `(height z, index t)`. -/
def xmssNodeWith (prims : Primitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → prims.Y → m prims.Y)
    (compress : Adrs → List prims.Y → m prims.Y)
    (nodeHash : Adrs → prims.Y → prims.Y → m prims.Y)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (z t : ℕ) : m prims.Y :=
  PerfectMerkleTree.merkleRootM (xmssLeafWith prims hash compress sk pk adrs)
    (xmssNodeHashWith nodeHash adrs) z t

/-- Callback-parametric owner implementation of the XMSS tree root. -/
def xmssRootWith (prims : Primitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → prims.Y → m prims.Y)
    (compress : Adrs → List prims.Y → m prims.Y)
    (nodeHash : Adrs → prims.Y → prims.Y → m prims.Y)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) : m prims.Y :=
  xmssNodeWith prims hash compress nodeHash sk pk adrs p.hp 0

/-- Callback-parametric owner implementation of XMSS signing. Following FIPS 205 Algorithm 10,
the sibling-only authentication path is computed before the WOTS+ signature. -/
def xmssSignWith (prims : Primitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → prims.Y → m prims.Y)
    (compress : Adrs → List prims.Y → m prims.Y)
    (nodeHash : Adrs → prims.Y → prims.Y → m prims.Y)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) : m (XmssSig p prims) := do
  let path ← PerfectMerkleTree.authPathM (xmssLeafWith prims hash compress sk pk adrs)
    (xmssNodeHashWith nodeHash adrs) idx p.hp
  let sig ← wotsSignWith prims hash msg sk pk (wotsLeafAdrs adrs idx)
  return (sig, path)

/-- Callback-parametric owner implementation of XMSS root recovery. The WOTS+ public key is
recovered before the authentication path is climbed. -/
def xmssPkFromSigWith (prims : Primitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → prims.Y → m prims.Y)
    (compress : Adrs → List prims.Y → m prims.Y)
    (nodeHash : Adrs → prims.Y → prims.Y → m prims.Y)
    (idx : ℕ) (sig : XmssSig p prims) (msg : prims.Y) (adrs : Adrs) : m prims.Y := do
  let leaf ← wotsPkFromSigWith prims hash compress sig.1 msg (wotsLeafAdrs adrs idx)
  PerfectMerkleTree.climbM (xmssNodeHashWith nodeHash adrs) idx leaf sig.2

/-! ### Pure and explicit-public-hash interpretations -/

/-- The XMSS leaf value at index `t`: the WOTS+ public key of keypair `t`. -/
def xmssLeaf (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (t : ℕ) : prims.Y :=
  Id.run (xmssLeafWith prims
    (m := Id) (fun a y => pure (prims.F pk a y))
    (fun a ys => pure (prims.Tl pk a ys)) sk pk adrs t)

/-- The XMSS internal-node hash at tree position `(height z, index t)` (type `TREE`). -/
def xmssNodeHash (prims : Primitives p) (pk : prims.PkSeed) (adrs : Adrs)
    (z t : ℕ) (l r : prims.Y) : prims.Y :=
  Id.run (xmssNodeHashWith
    (m := Id) (fun a left right => pure (prims.H pk a left right)) adrs z t l r)

/-- The XMSS subtree root at `(height z, index t)` (FIPS 205 Algorithm 9). -/
def xmssNode (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (z t : ℕ) : prims.Y :=
  Id.run (xmssNodeWith prims
    (m := Id) (fun a y => pure (prims.F pk a y))
    (fun a ys => pure (prims.Tl pk a ys))
    (fun a left right => pure (prims.H pk a left right)) sk pk adrs z t)

/-- The XMSS tree root (height `h'`, index `0`) — the value committed by key generation. -/
def xmssRoot (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    prims.Y :=
  Id.run (xmssRootWith prims
    (m := Id) (fun a y => pure (prims.F pk a y))
    (fun a ys => pure (prims.Tl pk a ys))
    (fun a left right => pure (prims.H pk a left right)) sk pk adrs)

/-- XMSS signing (FIPS 205 Algorithm 10): WOTS+-sign at leaf `idx` and emit the auth path. -/
def xmssSign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) : XmssSig p prims :=
  Id.run (xmssSignWith prims
    (m := Id) (fun a y => pure (prims.F pk a y))
    (fun a ys => pure (prims.Tl pk a ys))
    (fun a left right => pure (prims.H pk a left right)) msg sk pk adrs idx)

/-- XMSS root recovery from a signature (FIPS 205 Algorithm 11): recover the WOTS+ public key
(the leaf) then climb the auth path. -/
def xmssPkFromSig (prims : Primitives p) (idx : ℕ) (sig : XmssSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) : prims.Y :=
  Id.run (xmssPkFromSigWith prims
    (m := Id) (fun a y => pure (prims.F pk a y))
    (fun a ys => pure (prims.Tl pk a ys))
    (fun a left right => pure (prims.H pk a left right)) idx sig msg adrs)

/-! ### Pure API equations -/

/-- The owner interpretation preserves the established WOTS+-leaf equation. -/
@[simp]
theorem xmssLeaf_eq_wotsPkGen (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) :
    xmssLeaf prims sk pk adrs t = wotsPkGen prims sk pk (wotsLeafAdrs adrs t) := by
  rfl

/-- The owner interpretation preserves the established addressed node-hash equation. -/
@[simp]
theorem xmssNodeHash_eq_h (prims : Primitives p) (pk : prims.PkSeed) (adrs : Adrs)
    (z t : ℕ) (l r : prims.Y) :
    xmssNodeHash prims pk adrs z t l r = prims.H pk (xmssNodeAdrs adrs z t) l r := by
  rfl

/-- The owner interpretation preserves the established pure perfect-subtree equation. -/
@[simp]
theorem xmssNode_eq_merkleRoot (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (z t : ℕ) :
    xmssNode prims sk pk adrs z t =
      PerfectMerkleTree.merkleRoot (xmssLeaf prims sk pk adrs)
        (xmssNodeHash prims pk adrs) z t := by
  unfold xmssNode xmssNodeWith
  rw [PerfectMerkleTree.idRun_merkleRootM]
  rfl

/-- The owner interpretation preserves the established height-`h'` root equation. -/
@[simp]
theorem xmssRoot_eq_node (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    xmssRoot prims sk pk adrs = xmssNode prims sk pk adrs p.hp 0 := by
  rfl

/-- The pure signing API is the FIPS authentication path paired with the WOTS+ signature. -/
@[simp]
theorem xmssSign_eq_pair (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ) :
    xmssSign prims msg sk pk adrs idx =
      (wotsSign prims msg sk pk (wotsLeafAdrs adrs idx),
        PerfectMerkleTree.authPath (xmssLeaf prims sk pk adrs)
          (xmssNodeHash prims pk adrs) idx p.hp) := by
  unfold xmssSign xmssSignWith
  change
    ((wotsSignWith prims (m := Id) (fun a y => pure (prims.F pk a y))
        msg sk pk (wotsLeafAdrs adrs idx)).run,
      (PerfectMerkleTree.authPathM
        (xmssLeafWith prims (m := Id) (fun a y => pure (prims.F pk a y))
          (fun a ys => pure (prims.Tl pk a ys)) sk pk adrs)
        (xmssNodeHashWith (m := Id)
          (fun a left right => pure (prims.H pk a left right)) adrs) idx p.hp).run) = _
  rw [PerfectMerkleTree.idRun_authPathM]
  rfl

/-- The pure recovery API first recovers the WOTS+ leaf and then climbs the authentication path. -/
@[simp]
theorem xmssPkFromSig_eq_climb (prims : Primitives p) (idx : ℕ)
    (sig : XmssSig p prims) (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    xmssPkFromSig prims idx sig msg pk adrs =
      PerfectMerkleTree.climb (xmssNodeHash prims pk adrs) idx
        (wotsPkFromSig prims sig.1 msg pk (wotsLeafAdrs adrs idx)) sig.2 := by
  unfold xmssPkFromSig xmssPkFromSigWith
  change Id.run (PerfectMerkleTree.climbM
    (xmssNodeHashWith (m := Id)
      (fun a left right => pure (prims.H pk a left right)) adrs) idx
    (Id.run (wotsPkFromSigWith prims (m := Id)
      (fun a y => pure (prims.F pk a y)) (fun a ys => pure (prims.Tl pk a ys))
      sig.1 msg (wotsLeafAdrs adrs idx))) sig.2) = _
  rw [PerfectMerkleTree.idRun_climbM]
  rfl

/-- Explicit-public-hash XMSS leaf computation. -/
def xmssLeafM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m]
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) : m prims.Y :=
  xmssLeafWith prims (PublicHash.f prims pk) (PublicHash.tl prims pk) sk pk adrs t

/-- Explicit-public-hash XMSS internal-node computation. -/
def xmssNodeHashM (prims : Primitives p) {m : Type → Type*}
    [HasQuery (publicHashSpec prims) m] (pk : prims.PkSeed) (adrs : Adrs)
    (z t : ℕ) (l r : prims.Y) : m prims.Y :=
  xmssNodeHashWith (PublicHash.h prims pk) adrs z t l r

/-- Explicit-public-hash XMSS subtree-root computation. -/
def xmssNodeM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m]
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (z t : ℕ) : m prims.Y :=
  xmssNodeWith prims (PublicHash.f prims pk) (PublicHash.tl prims pk)
    (PublicHash.h prims pk) sk pk adrs z t

/-- Explicit-public-hash XMSS tree-root computation. -/
def xmssRootM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m]
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) : m prims.Y :=
  xmssRootWith prims (PublicHash.f prims pk) (PublicHash.tl prims pk)
    (PublicHash.h prims pk) sk pk adrs

/-- Explicit-public-hash XMSS signing. -/
def xmssSignM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m]
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) : m (XmssSig p prims) :=
  xmssSignWith prims (PublicHash.f prims pk) (PublicHash.tl prims pk)
    (PublicHash.h prims pk) msg sk pk adrs idx

/-- Explicit-public-hash XMSS root recovery. -/
def xmssPkFromSigM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m]
    (idx : ℕ) (sig : XmssSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) : m prims.Y :=
  xmssPkFromSigWith prims (PublicHash.f prims pk) (PublicHash.tl prims pk)
    (PublicHash.h prims pk) idx sig msg adrs

/-! ### Naturality -/

/-- A monad morphism commutes with XMSS leaf generation when it commutes with both WOTS+
callbacks. -/
theorem xmssLeafWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (prims : Primitives p)
    (hashm : Adrs → prims.Y → m prims.Y) (hashn : Adrs → prims.Y → n prims.Y)
    (compressm : Adrs → List prims.Y → m prims.Y)
    (compressn : Adrs → List prims.Y → n prims.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) :
    F (xmssLeafWith prims hashm compressm sk pk adrs t) =
      xmssLeafWith prims hashn compressn sk pk adrs t :=
  wotsPkGenWith_natural F prims hashm hashn compressm compressn
    hhash hcompress sk pk (wotsLeafAdrs adrs t)

/-- A monad morphism commutes with addressed XMSS node hashing when it commutes with the node
callback. -/
theorem xmssNodeHashWith_natural {Y : Type} {m n : Type → Type*} [Monad m] [Monad n]
    (F : m →ᵐ n) (hashm : Adrs → Y → Y → m Y) (hashn : Adrs → Y → Y → n Y)
    (hhash : ∀ a l r, F (hashm a l r) = hashn a l r)
    (adrs : Adrs) (z t : ℕ) (l r : Y) :
    F (xmssNodeHashWith hashm adrs z t l r) = xmssNodeHashWith hashn adrs z t l r :=
  hhash _ l r

/-- A monad morphism commutes with XMSS subtree-root computation when it commutes with every
public-hash callback. -/
theorem xmssNodeWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (prims : Primitives p)
    (hashm : Adrs → prims.Y → m prims.Y) (hashn : Adrs → prims.Y → n prims.Y)
    (compressm : Adrs → List prims.Y → m prims.Y)
    (compressn : Adrs → List prims.Y → n prims.Y)
    (nodeHashm : Adrs → prims.Y → prims.Y → m prims.Y)
    (nodeHashn : Adrs → prims.Y → prims.Y → n prims.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (z t : ℕ) :
    F (xmssNodeWith prims hashm compressm nodeHashm sk pk adrs z t) =
      xmssNodeWith prims hashn compressn nodeHashn sk pk adrs z t := by
  apply PerfectMerkleTree.merkleRootM_natural F
  · intro i
    exact xmssLeafWith_natural F prims hashm hashn compressm compressn
      hhash hcompress sk pk adrs i
  · intro h i l r
    exact xmssNodeHashWith_natural F nodeHashm nodeHashn hnode adrs h i l r

/-- A monad morphism commutes with XMSS root computation under pointwise callback maps. -/
theorem xmssRootWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (prims : Primitives p)
    (hashm : Adrs → prims.Y → m prims.Y) (hashn : Adrs → prims.Y → n prims.Y)
    (compressm : Adrs → List prims.Y → m prims.Y)
    (compressn : Adrs → List prims.Y → n prims.Y)
    (nodeHashm : Adrs → prims.Y → prims.Y → m prims.Y)
    (nodeHashn : Adrs → prims.Y → prims.Y → n prims.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    F (xmssRootWith prims hashm compressm nodeHashm sk pk adrs) =
      xmssRootWith prims hashn compressn nodeHashn sk pk adrs :=
  xmssNodeWith_natural F prims hashm hashn compressm compressn nodeHashm nodeHashn
    hhash hcompress hnode sk pk adrs p.hp 0

/-- A monad morphism commutes with XMSS signing under pointwise callback maps. -/
theorem xmssSignWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (prims : Primitives p)
    (hashm : Adrs → prims.Y → m prims.Y) (hashn : Adrs → prims.Y → n prims.Y)
    (compressm : Adrs → List prims.Y → m prims.Y)
    (compressn : Adrs → List prims.Y → n prims.Y)
    (nodeHashm : Adrs → prims.Y → prims.Y → m prims.Y)
    (nodeHashn : Adrs → prims.Y → prims.Y → n prims.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    F (xmssSignWith prims hashm compressm nodeHashm msg sk pk adrs idx) =
      xmssSignWith prims hashn compressn nodeHashn msg sk pk adrs idx := by
  simp only [xmssSignWith, F.mmap_bind]
  simp_rw [wotsSignWith_natural F prims hashm hashn hhash]
  simp_rw [PerfectMerkleTree.authPathM_natural F
    (xmssLeafWith prims hashm compressm sk pk adrs)
    (xmssNodeHashWith nodeHashm adrs)
    (xmssLeafWith prims hashn compressn sk pk adrs)
    (xmssNodeHashWith nodeHashn adrs)
    (fun i => xmssLeafWith_natural F prims hashm hashn compressm compressn
      hhash hcompress sk pk adrs i)
    (fun h i l r => xmssNodeHashWith_natural F nodeHashm nodeHashn hnode adrs h i l r)]
  simp [F.mmap_pure]

/-- A monad morphism commutes with XMSS recovery under pointwise callback maps. -/
theorem xmssPkFromSigWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (prims : Primitives p)
    (hashm : Adrs → prims.Y → m prims.Y) (hashn : Adrs → prims.Y → n prims.Y)
    (compressm : Adrs → List prims.Y → m prims.Y)
    (compressn : Adrs → List prims.Y → n prims.Y)
    (nodeHashm : Adrs → prims.Y → prims.Y → m prims.Y)
    (nodeHashn : Adrs → prims.Y → prims.Y → n prims.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (idx : ℕ) (sig : XmssSig p prims) (msg : prims.Y) (adrs : Adrs) :
    F (xmssPkFromSigWith prims hashm compressm nodeHashm idx sig msg adrs) =
      xmssPkFromSigWith prims hashn compressn nodeHashn idx sig msg adrs := by
  simp only [xmssPkFromSigWith, F.mmap_bind]
  simp_rw [wotsPkFromSigWith_natural F prims hashm hashn compressm compressn hhash hcompress]
  simp_rw [PerfectMerkleTree.climbM_natural F _ _
    (fun h i l r => xmssNodeHashWith_natural F nodeHashm nodeHashn hnode adrs h i l r)]

private theorem queryHom_publicHash (prims : Primitives p) {m n : Type → Type*}
    [Monad m] [Monad n] [HasQuery (publicHashSpec prims) m]
    [HasQuery (publicHashSpec prims) n]
    (F : HasQuery.QueryHom (publicHashSpec prims) m n)
    (q : PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y) :
    F.toMonadHom (query (spec := publicHashSpec prims) q) =
      query (spec := publicHashSpec prims) q :=
  HasQuery.map_query F q

private theorem queryHom_f (prims : Primitives p) {m n : Type → Type*}
    [Monad m] [Monad n] [HasQuery (publicHashSpec prims) m]
    [HasQuery (publicHashSpec prims) n]
    (F : HasQuery.QueryHom (publicHashSpec prims) m n) (pk : prims.PkSeed) :
    ∀ a y, F.toMonadHom (PublicHash.f prims pk a y) = PublicHash.f prims pk a y := by
  intro a y
  unfold PublicHash.f
  exact queryHom_publicHash prims F (.thash pk (prims.adrsToKey a) [y])

private theorem queryHom_tl (prims : Primitives p) {m n : Type → Type*}
    [Monad m] [Monad n] [HasQuery (publicHashSpec prims) m]
    [HasQuery (publicHashSpec prims) n]
    (F : HasQuery.QueryHom (publicHashSpec prims) m n) (pk : prims.PkSeed) :
    ∀ a ys, F.toMonadHom (PublicHash.tl prims pk a ys) = PublicHash.tl prims pk a ys := by
  intro a ys
  unfold PublicHash.tl
  exact queryHom_publicHash prims F (.thash pk (prims.adrsToKey a) ys)

private theorem queryHom_h (prims : Primitives p) {m n : Type → Type*}
    [Monad m] [Monad n] [HasQuery (publicHashSpec prims) m]
    [HasQuery (publicHashSpec prims) n]
    (F : HasQuery.QueryHom (publicHashSpec prims) m n) (pk : prims.PkSeed) :
    ∀ a l r, F.toMonadHom (PublicHash.h prims pk a l r) = PublicHash.h prims pk a l r := by
  intro a l r
  unfold PublicHash.h
  exact queryHom_publicHash prims F (.thash pk (prims.adrsToKey a) [l, r])

/-- Query-preserving monad morphisms commute with explicit XMSS leaf generation. -/
theorem xmssLeafM_natural (prims : Primitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec prims) m]
    [HasQuery (publicHashSpec prims) n]
    (F : HasQuery.QueryHom (publicHashSpec prims) m n)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) :
    F.toMonadHom (xmssLeafM prims sk pk adrs t) = xmssLeafM prims sk pk adrs t := by
  apply xmssLeafWith_natural F.toMonadHom prims
  · exact queryHom_f prims F pk
  · exact queryHom_tl prims F pk

/-- Query-preserving monad morphisms commute with one explicit XMSS node-hash query. -/
theorem xmssNodeHashM_natural (prims : Primitives p)
    {m n : Type → Type*} [Monad m] [Monad n]
    [HasQuery (publicHashSpec prims) m] [HasQuery (publicHashSpec prims) n]
    (F : HasQuery.QueryHom (publicHashSpec prims) m n)
    (pk : prims.PkSeed) (adrs : Adrs) (z t : ℕ) (l r : prims.Y) :
    F.toMonadHom (xmssNodeHashM prims pk adrs z t l r) =
      xmssNodeHashM prims pk adrs z t l r :=
  xmssNodeHashWith_natural F.toMonadHom _ _ (queryHom_h prims F pk) adrs z t l r

/-- Query-preserving monad morphisms commute with explicit XMSS subtree-root computation. -/
theorem xmssNodeM_natural (prims : Primitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec prims) m]
    [HasQuery (publicHashSpec prims) n]
    (F : HasQuery.QueryHom (publicHashSpec prims) m n)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (z t : ℕ) :
    F.toMonadHom (xmssNodeM prims sk pk adrs z t) = xmssNodeM prims sk pk adrs z t := by
  apply xmssNodeWith_natural F.toMonadHom prims
  · exact queryHom_f prims F pk
  · exact queryHom_tl prims F pk
  · exact queryHom_h prims F pk

/-- Query-preserving monad morphisms commute with explicit XMSS root computation. -/
theorem xmssRootM_natural (prims : Primitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec prims) m]
    [HasQuery (publicHashSpec prims) n]
    (F : HasQuery.QueryHom (publicHashSpec prims) m n)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    F.toMonadHom (xmssRootM prims sk pk adrs) = xmssRootM prims sk pk adrs := by
  apply xmssRootWith_natural F.toMonadHom prims
  · exact queryHom_f prims F pk
  · exact queryHom_tl prims F pk
  · exact queryHom_h prims F pk

/-- Query-preserving monad morphisms commute with explicit XMSS signing. -/
theorem xmssSignM_natural (prims : Primitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec prims) m]
    [HasQuery (publicHashSpec prims) n]
    (F : HasQuery.QueryHom (publicHashSpec prims) m n)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    F.toMonadHom (xmssSignM prims msg sk pk adrs idx) =
      xmssSignM prims msg sk pk adrs idx := by
  apply xmssSignWith_natural F.toMonadHom prims
  · exact queryHom_f prims F pk
  · exact queryHom_tl prims F pk
  · exact queryHom_h prims F pk

/-- Query-preserving monad morphisms commute with explicit XMSS root recovery. -/
theorem xmssPkFromSigM_natural (prims : Primitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec prims) m]
    [HasQuery (publicHashSpec prims) n]
    (F : HasQuery.QueryHom (publicHashSpec prims) m n)
    (idx : ℕ) (sig : XmssSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) :
    F.toMonadHom (xmssPkFromSigM prims idx sig msg pk adrs) =
      xmssPkFromSigM prims idx sig msg pk adrs := by
  apply xmssPkFromSigWith_natural F.toMonadHom prims
  · exact queryHom_f prims F pk
  · exact queryHom_tl prims F pk
  · exact queryHom_h prims F pk

/-! ### Structural query bounds -/

/-- Public-hash budget for one XMSS subtree root. A leaf costs one complete WOTS+ public-key
generation; a parent evaluates two children and one ordered binary hash. -/
def xmssNodeQueryBound (p : Params) : ℕ → ℕ
  | 0 => p.len * (p.w - 1) + 1
  | z + 1 => xmssNodeQueryBound p z + xmssNodeQueryBound p z + 1

/-- Public-hash budget for a sibling-only authentication path. At each level, the existing path
is followed by exactly one sibling subtree. -/
def xmssAuthPathQueryBound (p : Params) : ℕ → ℕ
  | 0 => 0
  | z + 1 => xmssAuthPathQueryBound p z + xmssNodeQueryBound p z

private theorem xmssNodeHashM_isTotalQueryBound_one (prims : Primitives p)
    (pk : prims.PkSeed) (adrs : Adrs) (z t : ℕ) (l r : prims.Y) :
    IsTotalQueryBound
      (xmssNodeHashM prims pk adrs z t l r :
        OracleComp (publicHashSpec prims) prims.Y) 1 := by
  simp [xmssNodeHashM, xmssNodeHashWith, PublicHash.h, IsTotalQueryBound]

/-- An XMSS subtree root stays within its structural leaf-and-parent query budget. -/
theorem xmssNodeM_isTotalQueryBound (prims : Primitives p)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (z t : ℕ) :
    IsTotalQueryBound
      (xmssNodeM prims sk pk adrs z t : OracleComp (publicHashSpec prims) prims.Y)
      (xmssNodeQueryBound p z) := by
  induction z generalizing t with
  | zero =>
      simpa [xmssNodeQueryBound, xmssNodeM, xmssNodeWith,
        PerfectMerkleTree.merkleRootM, xmssLeafM, xmssLeafWith, wotsPkGenM] using
        wotsPkGenM_isTotalQueryBound prims sk pk (wotsLeafAdrs adrs t)
  | succ z ih =>
      change IsTotalQueryBound (do
        let left ← xmssNodeM prims sk pk adrs z (2 * t)
        let right ← xmssNodeM prims sk pk adrs z (2 * t + 1)
        xmssNodeHashM prims pk adrs (z + 1) t left right)
        (xmssNodeQueryBound p z + xmssNodeQueryBound p z + 1)
      have hbound := isTotalQueryBound_bind (ih (2 * t)) fun left =>
        isTotalQueryBound_bind (ih (2 * t + 1)) fun right =>
          xmssNodeHashM_isTotalQueryBound_one prims pk adrs (z + 1) t left right
      simpa [Nat.add_assoc] using hbound

/-- XMSS root generation has the subtree budget at the parameter-set height. -/
theorem xmssRootM_isTotalQueryBound (prims : Primitives p)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (xmssRootM prims sk pk adrs : OracleComp (publicHashSpec prims) prims.Y)
      (xmssNodeQueryBound p p.hp) :=
  xmssNodeM_isTotalQueryBound prims sk pk adrs p.hp 0

/-- The sibling-only authentication-path program stays within the sum of one sibling subtree
at every level. -/
theorem xmssAuthPathM_isTotalQueryBound (prims : Primitives p)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (idx z : ℕ) :
    IsTotalQueryBound
      (PerfectMerkleTree.authPathM (xmssLeafM prims sk pk adrs)
        (xmssNodeHashM prims pk adrs) idx z :
          OracleComp (publicHashSpec prims) (List prims.Y))
      (xmssAuthPathQueryBound p z) := by
  induction z with
  | zero => trivial
  | succ z ih =>
      change IsTotalQueryBound (do
        let path ← PerfectMerkleTree.authPathM (xmssLeafM prims sk pk adrs)
          (xmssNodeHashM prims pk adrs) idx z
        let siblingRoot ← xmssNodeM prims sk pk adrs z
          (PerfectMerkleTree.sibling (idx / 2 ^ z))
        return path ++ [siblingRoot])
        (xmssAuthPathQueryBound p z + xmssNodeQueryBound p z)
      exact isTotalQueryBound_bind ih fun path =>
        isTotalQueryBound_bind
          (xmssNodeM_isTotalQueryBound prims sk pk adrs z
            (PerfectMerkleTree.sibling (idx / 2 ^ z)))
          fun siblingRoot =>
            show IsTotalQueryBound
              (pure (path ++ [siblingRoot]) :
                OracleComp (publicHashSpec prims) (List prims.Y)) 0 from trivial

/-- Climbing an XMSS authentication path makes at most one public node-hash query per entry. -/
theorem xmssClimbM_isTotalQueryBound (prims : Primitives p)
    (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ) (node : prims.Y)
    (auth : List prims.Y) :
    IsTotalQueryBound
      (PerfectMerkleTree.climbM (xmssNodeHashM prims pk adrs) idx node auth :
        OracleComp (publicHashSpec prims) prims.Y)
      auth.length := by
  simpa using
    PerfectMerkleTree.isTotalQueryBound_climbM (xmssNodeHashM prims pk adrs) 1 idx node auth
      (fun h i l r => xmssNodeHashM_isTotalQueryBound_one prims pk adrs h i l r)

/-- XMSS recovery is bounded by the complementary WOTS+ chains, one `T_l` compression, and one
node hash per supplied authentication-path entry. -/
theorem xmssPkFromSigM_isTotalQueryBound (prims : Primitives p)
    (idx : ℕ) (sig : XmssSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (xmssPkFromSigM prims idx sig msg pk adrs :
        OracleComp (publicHashSpec prims) prims.Y)
      ((∑ i : Fin p.len, (p.w - 1 - chainSteps prims msg i.val)) + 1 + sig.2.length) := by
  change IsTotalQueryBound (do
    let leaf ← wotsPkFromSigM prims sig.1 msg pk (wotsLeafAdrs adrs idx)
    PerfectMerkleTree.climbM (xmssNodeHashM prims pk adrs) idx leaf sig.2) _
  exact isTotalQueryBound_bind
    (wotsPkFromSigM_isTotalQueryBound prims sig.1 msg pk (wotsLeafAdrs adrs idx)) fun leaf =>
      xmssClimbM_isTotalQueryBound prims pk adrs idx leaf sig.2

private theorem xmssAuthPathM_bind_isTotalQueryBound (prims : Primitives p)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (idx z q : ℕ)
    {beta : Type}
    (k : List prims.Y → OracleComp (publicHashSpec prims) beta)
    (hk : ∀ path, path.length = z → IsTotalQueryBound (k path) q) :
    IsTotalQueryBound
      (PerfectMerkleTree.authPathM (xmssLeafM prims sk pk adrs)
        (xmssNodeHashM prims pk adrs) idx z >>= k)
      (xmssAuthPathQueryBound p z + q) := by
  induction z generalizing k q with
  | zero =>
      simpa [PerfectMerkleTree.authPathM, xmssAuthPathQueryBound] using hk [] rfl
  | succ z ih =>
      rw [PerfectMerkleTree.authPathM]
      simp only [bind_assoc, pure_bind, xmssAuthPathQueryBound]
      change IsTotalQueryBound (do
        let path ← PerfectMerkleTree.authPathM (xmssLeafM prims sk pk adrs)
          (xmssNodeHashM prims pk adrs) idx z
        let siblingRoot ← xmssNodeM prims sk pk adrs z
          (PerfectMerkleTree.sibling (idx / 2 ^ z))
        k (path ++ [siblingRoot]))
        (xmssAuthPathQueryBound p z + xmssNodeQueryBound p z + q)
      have hrest : ∀ path, path.length = z →
          IsTotalQueryBound (do
            let siblingRoot ← xmssNodeM prims sk pk adrs z
              (PerfectMerkleTree.sibling (idx / 2 ^ z))
            k (path ++ [siblingRoot])) (xmssNodeQueryBound p z + q) := by
        intro path hlen
        exact isTotalQueryBound_bind
          (xmssNodeM_isTotalQueryBound prims sk pk adrs z
            (PerfectMerkleTree.sibling (idx / 2 ^ z))) fun siblingRoot =>
              hk (path ++ [siblingRoot]) (by simp [hlen])
      simpa [Nat.add_assoc] using
        (ih (xmssNodeQueryBound p z + q)
          (fun path => do
            let siblingRoot ← xmssNodeM prims sk pk adrs z
              (PerfectMerkleTree.sibling (idx / 2 ^ z))
            k (path ++ [siblingRoot])) hrest)

/-- XMSS signing composes the message-selected WOTS+ chain budget with the sibling-subtree
authentication-path budget. -/
theorem xmssSignM_isTotalQueryBound (prims : Primitives p)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    IsTotalQueryBound
      (xmssSignM prims msg sk pk adrs idx :
        OracleComp (publicHashSpec prims) (XmssSig p prims))
      ((∑ i : Fin p.len, chainSteps prims msg i.val) +
        xmssAuthPathQueryBound p p.hp) := by
  change IsTotalQueryBound (do
    let path ← PerfectMerkleTree.authPathM (xmssLeafM prims sk pk adrs)
      (xmssNodeHashM prims pk adrs) idx p.hp
    let sig ← wotsSignM prims msg sk pk (wotsLeafAdrs adrs idx)
    return (sig, path)) _
  have hbound := isTotalQueryBound_bind
    (xmssAuthPathM_isTotalQueryBound prims sk pk adrs idx p.hp) fun path =>
      isTotalQueryBound_bind
        (wotsSignM_isTotalQueryBound prims msg sk pk (wotsLeafAdrs adrs idx)) fun sig =>
          show IsTotalQueryBound
            (pure (sig, path) : OracleComp (publicHashSpec prims) (XmssSig p prims)) 0 from trivial
  simpa [Nat.add_comm] using hbound

/-- Signing followed by recovery stays within one complete pass over every WOTS+ chain, one
`T_l` compression, the sibling-only authentication-path budget, and one climb hash per tree
level. This is an upper bound on the free-oracle program, not a claim about distinct cache
misses. -/
theorem xmssSignM_then_xmssPkFromSigM_isTotalQueryBound (prims : Primitives p)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    IsTotalQueryBound ((do
      let sig ← xmssSignM prims msg sk pk adrs idx
      xmssPkFromSigM prims idx sig msg pk adrs) :
        OracleComp (publicHashSpec prims) prims.Y)
      ((p.len * (p.w - 1) + 1) + xmssAuthPathQueryBound p p.hp + p.hp) := by
  simp only [xmssSignM, xmssSignWith, xmssPkFromSigM, xmssPkFromSigWith,
    bind_assoc, pure_bind]
  have hbody : ∀ path : List prims.Y, path.length = p.hp →
      IsTotalQueryBound ((do
        let sig ← wotsSignM prims msg sk pk (wotsLeafAdrs adrs idx)
        let leaf ← wotsPkFromSigM prims sig msg pk (wotsLeafAdrs adrs idx)
        PerfectMerkleTree.climbM (xmssNodeHashM prims pk adrs) idx leaf path) :
          OracleComp (publicHashSpec prims) prims.Y)
        ((p.len * (p.w - 1) + 1) + p.hp) := by
    intro path hlen
    have hbound := isTotalQueryBound_bind
      (wotsSignM_isTotalQueryBound prims msg sk pk (wotsLeafAdrs adrs idx)) fun sig =>
        isTotalQueryBound_bind
          (wotsPkFromSigM_isTotalQueryBound prims sig msg pk (wotsLeafAdrs adrs idx)) fun leaf =>
            xmssClimbM_isTotalQueryBound prims pk adrs idx leaf path
    have hsum :
        (∑ i : Fin p.len, chainSteps prims msg i.val) +
            (∑ i : Fin p.len, (p.w - 1 - chainSteps prims msg i.val)) =
          p.len * (p.w - 1) := by
      rw [← Finset.sum_add_distrib]
      simp_rw [Nat.add_sub_of_le (chainSteps_le prims msg _)]
      simp
    simpa [hlen, ← Nat.add_assoc, hsum] using hbound
  have hbound := xmssAuthPathM_bind_isTotalQueryBound prims sk pk adrs idx p.hp
    ((p.len * (p.w - 1) + 1) + p.hp)
    (fun path => do
      let sig ← wotsSignM prims msg sk pk (wotsLeafAdrs adrs idx)
      let leaf ← wotsPkFromSigM prims sig msg pk (wotsLeafAdrs adrs idx)
      PerfectMerkleTree.climbM (xmssNodeHashM prims pk adrs) idx leaf path) hbody
  unfold xmssLeafM xmssNodeHashM at hbound
  simpa only [wotsSignM, wotsPkFromSigM, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hbound

/-! ### Deterministic interpretations -/

/-- A fixed deterministic answer table turns explicit XMSS leaf generation into pure WOTS+
key generation for the induced primitive bundle. -/
@[simp]
theorem simulateQ_xmssLeafM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) :
    simulateQ answer
        (xmssLeafM prims sk pk adrs t : OracleComp (publicHashSpec prims) prims.Y) =
      xmssLeaf (PublicHash.withPublicHash prims answer) sk pk adrs t :=
  simulateQ_wotsPkGenM_withPublicHash prims answer sk pk (wotsLeafAdrs adrs t)

/-- Canonical deterministic-handler parity for XMSS leaves. -/
@[simp]
theorem simulateQ_xmssLeafM (prims : Primitives p)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) :
    simulateQ (PublicHash.impl prims)
        (xmssLeafM prims sk pk adrs t : OracleComp (publicHashSpec prims) prims.Y) =
      xmssLeaf prims sk pk adrs t := by
  convert simulateQ_xmssLeafM_withPublicHash prims (PublicHash.impl prims) sk pk adrs t using 1
  all_goals rfl

/-- A fixed deterministic answer table turns an explicit XMSS internal-node query into the pure
node hash for the induced primitive bundle. -/
@[simp]
theorem simulateQ_xmssNodeHashM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (pk : prims.PkSeed) (adrs : Adrs)
    (z t : ℕ) (l r : prims.Y) :
    simulateQ answer
        (xmssNodeHashM prims pk adrs z t l r :
          OracleComp (publicHashSpec prims) prims.Y) =
      xmssNodeHash (PublicHash.withPublicHash prims answer) pk adrs z t l r := by
  simp [xmssNodeHashM, xmssNodeHashWith, xmssNodeHash, PublicHash.h]

/-- Canonical deterministic-handler parity for XMSS internal nodes. -/
@[simp]
theorem simulateQ_xmssNodeHashM (prims : Primitives p) (pk : prims.PkSeed)
    (adrs : Adrs) (z t : ℕ) (l r : prims.Y) :
    simulateQ (PublicHash.impl prims)
        (xmssNodeHashM prims pk adrs z t l r :
          OracleComp (publicHashSpec prims) prims.Y) =
      xmssNodeHash prims pk adrs z t l r := by
  convert simulateQ_xmssNodeHashM_withPublicHash prims (PublicHash.impl prims)
    pk adrs z t l r using 1
  all_goals rfl

/-- A fixed deterministic answer table turns explicit XMSS subtree computation into the pure
subtree algorithm for the induced primitive bundle. -/
@[simp]
theorem simulateQ_xmssNodeM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (z t : ℕ) :
    simulateQ answer
        (xmssNodeM prims sk pk adrs z t : OracleComp (publicHashSpec prims) prims.Y) =
      xmssNode (PublicHash.withPublicHash prims answer) sk pk adrs z t := by
  rw [xmssNode_eq_merkleRoot]
  simp only [xmssNodeM, xmssNodeWith, PerfectMerkleTree.simulateQ_merkleRootM]
  congr 1
  · funext i
    exact simulateQ_xmssLeafM_withPublicHash prims answer sk pk adrs i

/-- Canonical deterministic-handler parity for XMSS subtree computation. -/
@[simp]
theorem simulateQ_xmssNodeM (prims : Primitives p)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (z t : ℕ) :
    simulateQ (PublicHash.impl prims)
        (xmssNodeM prims sk pk adrs z t : OracleComp (publicHashSpec prims) prims.Y) =
      xmssNode prims sk pk adrs z t := by
  convert simulateQ_xmssNodeM_withPublicHash prims (PublicHash.impl prims)
    sk pk adrs z t using 1
  all_goals rfl

/-- A fixed deterministic answer table turns explicit XMSS root computation into the pure root
for the induced primitive bundle. -/
@[simp]
theorem simulateQ_xmssRootM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (xmssRootM prims sk pk adrs : OracleComp (publicHashSpec prims) prims.Y) =
      xmssRoot (PublicHash.withPublicHash prims answer) sk pk adrs := by
  exact simulateQ_xmssNodeM_withPublicHash prims answer sk pk adrs p.hp 0

/-- Canonical deterministic-handler parity for XMSS roots. -/
@[simp]
theorem simulateQ_xmssRootM (prims : Primitives p)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (xmssRootM prims sk pk adrs : OracleComp (publicHashSpec prims) prims.Y) =
      xmssRoot prims sk pk adrs := by
  convert simulateQ_xmssRootM_withPublicHash prims (PublicHash.impl prims) sk pk adrs using 1
  all_goals rfl

/-- A fixed deterministic answer table turns explicit XMSS signing into pure signing for the
induced primitive bundle. The same answer table interprets the WOTS+ signature and auth path. -/
@[simp]
theorem simulateQ_xmssSignM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    simulateQ answer
        (xmssSignM prims msg sk pk adrs idx :
          OracleComp (publicHashSpec prims) (XmssSig p prims)) =
      xmssSign (PublicHash.withPublicHash prims answer) msg sk pk adrs idx := by
  change simulateQ answer (do
      let path ← PerfectMerkleTree.authPathM (xmssLeafM prims sk pk adrs)
        (xmssNodeHashM prims pk adrs) idx p.hp
      let sig ← wotsSignM prims msg sk pk (wotsLeafAdrs adrs idx)
      return (sig, path)) = _
  simp only [simulateQ_bind, simulateQ_pure]
  rw [PerfectMerkleTree.simulateQ_authPathM]
  rw [simulateQ_wotsSignM_withPublicHash]
  rw [xmssSign_eq_pair]
  simp_rw [simulateQ_xmssLeafM_withPublicHash, simulateQ_xmssNodeHashM_withPublicHash]
  rfl

/-- Canonical deterministic-handler parity for XMSS signing. -/
@[simp]
theorem simulateQ_xmssSignM (prims : Primitives p)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    simulateQ (PublicHash.impl prims)
        (xmssSignM prims msg sk pk adrs idx :
          OracleComp (publicHashSpec prims) (XmssSig p prims)) =
      xmssSign prims msg sk pk adrs idx := by
  convert simulateQ_xmssSignM_withPublicHash prims (PublicHash.impl prims)
    msg sk pk adrs idx using 1
  all_goals rfl

/-- A fixed deterministic answer table turns explicit XMSS root recovery into pure recovery for
the induced primitive bundle. -/
@[simp]
theorem simulateQ_xmssPkFromSigM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id)
    (idx : ℕ) (sig : XmssSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (xmssPkFromSigM prims idx sig msg pk adrs :
          OracleComp (publicHashSpec prims) prims.Y) =
      xmssPkFromSig (PublicHash.withPublicHash prims answer) idx sig msg pk adrs := by
  change simulateQ answer (do
      let leaf ← wotsPkFromSigM prims sig.1 msg pk (wotsLeafAdrs adrs idx)
      PerfectMerkleTree.climbM (xmssNodeHashM prims pk adrs) idx leaf sig.2) = _
  simp only [simulateQ_bind]
  rw [simulateQ_wotsPkFromSigM_withPublicHash]
  simp_rw [PerfectMerkleTree.simulateQ_climbM]
  rw [xmssPkFromSig_eq_climb]
  simp_rw [simulateQ_xmssNodeHashM_withPublicHash]
  rfl

/-- Canonical deterministic-handler parity for XMSS root recovery. -/
@[simp]
theorem simulateQ_xmssPkFromSigM (prims : Primitives p)
    (idx : ℕ) (sig : XmssSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (xmssPkFromSigM prims idx sig msg pk adrs :
          OracleComp (publicHashSpec prims) prims.Y) =
      xmssPkFromSig prims idx sig msg pk adrs := by
  convert simulateQ_xmssPkFromSigM_withPublicHash prims (PublicHash.impl prims)
    idx sig msg pk adrs using 1
  all_goals rfl

/-- **XMSS correctness** (FIPS 205, Algorithms 9–11): root recovery from an honest signature at
leaf `idx < 2^{h'}` reproduces the XMSS tree root. Composes WOTS+ correctness with the Merkle
auth-path consistency lemma. -/
theorem xmssPkFromSig_xmssSign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ) (hidx : idx < 2 ^ p.hp) :
    xmssPkFromSig prims idx (xmssSign prims msg sk pk adrs idx) msg pk adrs
      = xmssRoot prims sk pk adrs := by
  rw [xmssPkFromSig_eq_climb, xmssSign_eq_pair, xmssRoot_eq_node,
    xmssNode_eq_merkleRoot]
  dsimp only
  rw [wotsPkFromSig_wotsSign]
  have key := PerfectMerkleTree.climb_authPath (xmssLeaf prims sk pk adrs)
    (xmssNodeHash prims pk adrs) idx p.hp
  rw [Nat.div_eq_of_lt hidx] at key
  exact key

/-- Functional XMSS completeness for one fixed total public-hash answer function shared by
signing, recovery, and root computation. This is a deterministic interpretation theorem; it does
not claim completeness for independently sampled free-oracle calls or install a lazy cache. -/
theorem simulateQ_xmssPkFromSigM_xmssSignM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) (hidx : idx < 2 ^ p.hp) :
    simulateQ answer (do
      let sig ← xmssSignM prims msg sk pk adrs idx
      xmssPkFromSigM prims idx sig msg pk adrs) =
    simulateQ answer (xmssRootM prims sk pk adrs) := by
  simp only [simulateQ_bind, simulateQ_xmssSignM_withPublicHash,
    simulateQ_xmssPkFromSigM_withPublicHash, simulateQ_xmssRootM_withPublicHash]
  exact xmssPkFromSig_xmssSign (PublicHash.withPublicHash prims answer)
    msg sk pk adrs idx hidx

/-- **XMSS binding.** A signature at leaf `idx < 2^{h'}` with a well-formed authentication path
whose recovered WOTS+ public key differs from the honest leaf, yet which recovers the honest XMSS
root, exhibits a collision of `H` at the `TREE` address of the ancestor of leaf `idx` at some
height `0 < h ≤ h'` — node `(h, idx / 2 ^ h)`: the honestly computed child pair at that node and
a distinct pair hash to the same value. The first endpoint is fixed by the honest tree and
determined by `(idx, h)` (a valid target for a multi-target target-collision reduction). -/
theorem xmssPkFromSig_binding (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ) (hidx : idx < 2 ^ p.hp)
    (sig : XmssSig p prims) (hlen : sig.2.length = p.hp)
    (hroot : xmssPkFromSig prims idx sig msg pk adrs = xmssRoot prims sk pk adrs)
    (hne : xmssLeaf prims sk pk adrs idx
      ≠ wotsPkFromSig prims sig.1 msg pk (wotsLeafAdrs adrs idx)) :
    ∃ (h : ℕ) (c : prims.Y × prims.Y), 0 < h ∧ h ≤ p.hp ∧
      (xmssNode prims sk pk adrs (h - 1) (2 * (idx / 2 ^ h)),
          xmssNode prims sk pk adrs (h - 1) (2 * (idx / 2 ^ h) + 1))
        ≠ c ∧
      prims.H pk (xmssNodeAdrs adrs h (idx / 2 ^ h))
          (xmssNode prims sk pk adrs (h - 1) (2 * (idx / 2 ^ h)))
          (xmssNode prims sk pk adrs (h - 1) (2 * (idx / 2 ^ h) + 1))
        = prims.H pk (xmssNodeAdrs adrs h (idx / 2 ^ h)) c.1 c.2 := by
  have hroot' : PerfectMerkleTree.climb (xmssNodeHash prims pk adrs) idx
      (wotsPkFromSig prims sig.1 msg pk (wotsLeafAdrs adrs idx)) sig.2
      = PerfectMerkleTree.merkleRoot (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs)
          p.hp (idx / 2 ^ p.hp) := by
    rw [Nat.div_eq_of_lt hidx]
    simpa only [xmssPkFromSig_eq_climb, xmssRoot_eq_node, xmssNode_eq_merkleRoot] using hroot
  simpa only [xmssNode_eq_merkleRoot, xmssNodeHash_eq_h] using
    (PerfectMerkleTree.climb_binding (xmssLeaf prims sk pk adrs)
      (xmssNodeHash prims pk adrs) p.hp idx _ sig.2 hlen hroot' hne)

end SLHDSA
