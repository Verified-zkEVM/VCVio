/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.External
public import HashSig.SLHDSA.Codec

/-!
# Pure executable SLH-DSA interpretation

This module gives deterministic key-generation, signing, and verification entry points whose
tree-producing operations execute without constructing a full dependent Merkle tree and without
interpreting a free-monad program.  `treeHash` follows the exact depth-first, left-to-right order
of FIPS 205 Algorithms 9 and 15 while retaining only the current recursion frontier.  Its stack
depth is the requested tree height and it performs exactly one leaf evaluation per leaf.

The executable functions are not a second scheme specification.  The refinement theorems at each
boundary identify their results with `PerfectMerkleTree`, XMSS, FORS, the general hypertree, and
`GeneralScheme` respectively.  No native or foreign implementation is used.

## References

- NIST FIPS 205, Algorithms 9--25
-/

public section

namespace SLHDSA.Execution

/-! ## Streaming perfect-tree operations -/

/-- Depth-first perfect-subtree root evaluation.  Unlike the proof-oriented canonical tree
definition, this evaluator never materializes `FullData`; only the recursion frontier is live. -/
def treeHash {Y : Type} (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) : ℕ → ℕ → Y
  | 0, t => leaf t
  | z + 1, t =>
      nodeHash (z + 1) t (treeHash leaf nodeHash z (2 * t))
        (treeHash leaf nodeHash z (2 * t + 1))

@[simp] theorem treeHash_zero {Y : Type} (leaf : ℕ → Y)
    (nodeHash : ℕ → ℕ → Y → Y → Y) (t : ℕ) :
    treeHash leaf nodeHash 0 t = leaf t := by
  rfl

theorem treeHash_succ {Y : Type} (leaf : ℕ → Y)
    (nodeHash : ℕ → ℕ → Y → Y → Y) (z t : ℕ) :
    treeHash leaf nodeHash (z + 1) t =
      nodeHash (z + 1) t (treeHash leaf nodeHash z (2 * t))
        (treeHash leaf nodeHash z (2 * t + 1)) := by
  rfl

/-- `treeHash` is observationally equal to the canonical addressed perfect-tree root. -/
theorem treeHash_eq_merkleRoot {Y : Type} (leaf : ℕ → Y)
    (nodeHash : ℕ → ℕ → Y → Y → Y) (z t : ℕ) :
    treeHash leaf nodeHash z t = PerfectMerkleTree.merkleRoot leaf nodeHash z t := by
  induction z generalizing t with
  | zero => rfl
  | succ z ih =>
      rw [treeHash, PerfectMerkleTree.merkleRoot_succ, ih, ih]

/-- Streaming authentication-path generation.  At height `z`, only the sibling subtree root is
evaluated; the selected leaf and its ancestors are not materialized or recomputed. -/
def authenticationPath {Y : Type} (leaf : ℕ → Y)
    (nodeHash : ℕ → ℕ → Y → Y → Y) (idx : ℕ) : (z : ℕ) → Vector Y z
  | 0 => #v[]
  | z + 1 =>
      (authenticationPath leaf nodeHash idx z).push
        (treeHash leaf nodeHash z (PerfectMerkleTree.sibling (idx / 2 ^ z)))

@[simp] theorem authenticationPath_zero {Y : Type} (leaf : ℕ → Y)
    (nodeHash : ℕ → ℕ → Y → Y → Y) (idx : ℕ) :
    authenticationPath leaf nodeHash idx 0 = #v[] := by
  rfl

theorem authenticationPath_succ {Y : Type} (leaf : ℕ → Y)
    (nodeHash : ℕ → ℕ → Y → Y → Y) (idx z : ℕ) :
    authenticationPath leaf nodeHash idx (z + 1) =
      (authenticationPath leaf nodeHash idx z).push
        (treeHash leaf nodeHash z (PerfectMerkleTree.sibling (idx / 2 ^ z))) := by
  rfl

/-- The streaming authentication path is exactly the canonical leaf-first path. -/
theorem authenticationPath_eq_intrinsicAuthPath {Y : Type} (leaf : ℕ → Y)
    (nodeHash : ℕ → ℕ → Y → Y → Y) (idx z : ℕ) :
    authenticationPath leaf nodeHash idx z =
      PerfectMerkleTree.intrinsicAuthPath leaf nodeHash idx z := by
  induction z with
  | zero => rfl
  | succ z ih =>
      rw [authenticationPath, PerfectMerkleTree.intrinsicAuthPath, ih,
        treeHash_eq_merkleRoot]

@[simp] theorem authenticationPath_toList {Y : Type} (leaf : ℕ → Y)
    (nodeHash : ℕ → ℕ → Y → Y → Y) (idx z : ℕ) :
    (authenticationPath leaf nodeHash idx z).toList =
      PerfectMerkleTree.authPath leaf nodeHash idx z := by
  rw [authenticationPath_eq_intrinsicAuthPath,
    PerfectMerkleTree.intrinsicAuthPath_toList]

/-! ## XMSS execution -/

variable {p : Params}

/-- Executable XMSS subtree root with logarithmic call-stack depth and no `FullData` allocation. -/
def xmssNode (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (z t : ℕ) : prims.Y :=
  treeHash (SLHDSA.xmssLeaf prims sk pk adrs) (SLHDSA.xmssNodeHash prims pk adrs) z t

/-- Executable top root of one XMSS tree. -/
def xmssRoot (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) : prims.Y :=
  xmssNode prims sk pk adrs p.hp 0

/-- Executable XMSS signing with a streaming authentication path. -/
def xmssSign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ) : XmssSig p prims.core :=
  ⟨wotsSign prims msg sk pk (wotsLeafAdrs adrs idx),
    authenticationPath (SLHDSA.xmssLeaf prims sk pk adrs)
      (SLHDSA.xmssNodeHash prims pk adrs) idx p.hp⟩

theorem xmssNode_eq_spec (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (z t : ℕ) :
    xmssNode prims sk pk adrs z t = SLHDSA.xmssNode prims sk pk adrs z t := by
  rw [xmssNode, SLHDSA.xmssNode_eq_merkleRoot, treeHash_eq_merkleRoot]

theorem xmssRoot_eq_spec (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    xmssRoot prims sk pk adrs = SLHDSA.xmssRoot prims sk pk adrs := by
  rw [xmssRoot, SLHDSA.xmssRoot_eq_node, xmssNode_eq_spec]

theorem xmssSign_eq_spec (prims : Primitives p) (msg : prims.Y)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ) :
    xmssSign prims msg sk pk adrs idx = SLHDSA.xmssSign prims msg sk pk adrs idx := by
  rw [xmssSign, SLHDSA.xmssSign_eq_pair, authenticationPath_eq_intrinsicAuthPath]

/-! ## FORS execution -/

/-- Executable FORS signing.  The `k` selected secrets are generated in increasing tree order;
each authentication path uses `treeHash` and therefore does not construct a full proof tree. -/
def forsSign (prims : Primitives p) (md : List Byte) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) : ForsSigCore p prims.core :=
  Vector.ofFn fun i : Fin p.k =>
    let idx := i.val * 2 ^ p.a + forsIdx p md i.val
    ⟨forsSkGenCore prims.core sk pk adrs idx,
      authenticationPath (SLHDSA.forsLeaf prims sk pk adrs)
        (SLHDSA.forsNodeHash prims pk adrs) idx p.a⟩

theorem forsSign_eq_spec (prims : Primitives p) (md : List Byte)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    forsSign prims md sk pk adrs = SLHDSA.forsSign prims md sk pk adrs := by
  rw [SLHDSA.forsSign_eq_ofFn]
  apply Vector.ext
  intro i hi
  simp only [forsSign, Vector.getElem_ofFn]
  rw [authenticationPath_eq_intrinsicAuthPath]

/-! ## General hypertree execution -/

/-- Executable typed Algorithm 12 loop. -/
def hypertreeSignFromPosition (vp : ValidatedParams) (prims : Primitives vp.params)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (recoverFinal : Bool)
    (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → prims.Y →
      Vector (XmssSig vp.params prims.core) layers
  | 0, _, _ => #v[]
  | 1, _, msg =>
      let sig := xmssSign prims msg sk pk pos.toAdrs pos.leaf.val
      if recoverFinal then
        let _ := SLHDSA.xmssPkFromSig prims pos.leaf.val sig msg pk pos.toAdrs
        #v[sig]
      else
        #v[sig]
  | layers + 2, hremaining, msg =>
      let sig := xmssSign prims msg sk pk pos.toAdrs pos.leaf.val
      let root := SLHDSA.xmssPkFromSig prims pos.leaf.val sig msg pk pos.toAdrs
      let next := pos.next (by omega)
      let rest := hypertreeSignFromPosition vp prims sk pk false next (layers + 1)
        (by simp [next]; omega) root
      rest.insertIdx 0 sig

/-- Executable arbitrary-depth hypertree signer. -/
def hypertreeSign (vp : ValidatedParams) (prims : Primitives vp.params)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) : GeneralHypertree.Signature vp prims.core :=
  let pos := LayerPosition.initial vp parts
  hypertreeSignFromPosition vp prims sk pk (vp.params.d == 1) pos vp.params.d
    (by simp [pos]) msg

theorem hypertreeSignFromPosition_eq_spec (vp : ValidatedParams)
    (prims : Primitives vp.params) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (recoverFinal : Bool) (pos : LayerPosition vp) (layers : ℕ)
    (hremaining : pos.layer.val + layers = vp.params.d) (msg : prims.Y) :
    hypertreeSignFromPosition vp prims sk pk recoverFinal pos layers hremaining msg =
      GeneralHypertree.signFromPosition vp prims sk pk recoverFinal pos layers hremaining msg := by
  induction layers using Nat.twoStepInduction generalizing recoverFinal pos msg with
  | zero => rfl
  | one =>
      cases recoverFinal <;>
        simp only [hypertreeSignFromPosition, GeneralHypertree.signFromPosition,
          xmssSign_eq_spec]
  | more layers _ ih =>
      simp only [hypertreeSignFromPosition, GeneralHypertree.signFromPosition,
        xmssSign_eq_spec, ih]

theorem hypertreeSign_eq_spec (vp : ValidatedParams) (prims : Primitives vp.params)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) :
    hypertreeSign vp prims msg sk pk parts = GeneralHypertree.sign vp prims msg sk pk parts := by
  rw [GeneralHypertree.sign_eq_signFromPosition]
  exact hypertreeSignFromPosition_eq_spec vp prims sk pk _ _ _ _ msg

/-! ## Full deterministic execution -/

/-- Pure executable FIPS Algorithm 18. -/
def keygenInternal (vp : ValidatedParams) (prims : Primitives vp.params)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) :
    PublicKeyCore prims.core × SecretKeyCore prims.core :=
  let root := xmssRoot prims skSeed pkSeed
    (GeneralHypertree.layerAdrs (vp.params.d - 1) 0)
  (⟨pkSeed, root⟩, ⟨skSeed, skPrf, pkSeed, root⟩)

/-- Pure executable FIPS Algorithm 19. -/
def signInternal (vp : ValidatedParams) (prims : Primitives vp.params)
    (msg : List Byte) (sk : SecretKeyCore prims.core) (addrnd : prims.Y) :
    GeneralScheme.SignatureCore vp prims.core :=
  let randomness := prims.PRFmsg sk.skPrf addrnd msg
  let parts := splitDigest vp.params (prims.Hmsg randomness sk.pkSeed sk.pkRoot msg)
  let forsSignature := forsSign prims parts.md.toList sk.skSeed sk.pkSeed parts.forsAdrs
  let forsPk := SLHDSA.forsPkFromSig prims forsSignature parts.md.toList sk.pkSeed parts.forsAdrs
  ⟨randomness, forsSignature,
    hypertreeSign vp prims forsPk sk.skSeed sk.pkSeed parts⟩

/-- Verification does not generate a Merkle tree, so the canonical deterministic verifier is
already the efficient path. -/
def verifyInternal (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y] (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core)
    (pk : PublicKeyCore prims.core) : Bool :=
  GeneralScheme.verifyInternal vp prims msg sig pk

theorem keygenInternal_eq_spec (vp : ValidatedParams) (prims : Primitives vp.params)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) :
    keygenInternal vp prims skSeed skPrf pkSeed =
      GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed := by
  unfold keygenInternal GeneralScheme.keygenInternal GeneralScheme.keygenInternalM
  simp only [simulateQ_bind, simulateQ_pure,
    GeneralHypertree.simulateQ_rootM_withPublicHash,
    GeneralHypertree.root_eq_xmssRoot, xmssRoot_eq_spec]
  cases prims
  rfl

theorem signInternal_eq_spec (vp : ValidatedParams) (prims : Primitives vp.params)
    (msg : List Byte) (sk : SecretKeyCore prims.core) (addrnd : prims.Y) :
    signInternal vp prims msg sk addrnd = GeneralScheme.signInternal vp prims msg sk addrnd := by
  unfold signInternal GeneralScheme.signInternal GeneralScheme.signInternalM
  simp only [simulateQ_bind, simulateQ_pure, PublicHash.simulateQ_hmsg,
    SLHDSA.simulateQ_forsSignM, SLHDSA.simulateQ_forsPkFromSigM,
    GeneralHypertree.simulateQ_signM_withPublicHash,
    forsSign_eq_spec, hypertreeSign_eq_spec]
  cases prims
  rfl

theorem verifyInternal_eq_spec (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y] (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core)
    (pk : PublicKeyCore prims.core) :
    verifyInternal vp prims msg sig pk = GeneralScheme.verifyInternal vp prims msg sig pk := by
  simp [verifyInternal]

/-! ## Byte-level refinement -/

/-- Encoding the executable public key produces exactly the canonical Algorithm 18 bytes. -/
theorem encodePublicKey_keygenInternal_eq_spec (vp : ValidatedParams)
    (prims : Primitives vp.params) (atomic : CoreWireCodec vp.params prims.core)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) :
    encodePublicKey atomic (keygenInternal vp prims skSeed skPrf pkSeed).1 =
      encodePublicKey atomic (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed).1 := by
  rw [keygenInternal_eq_spec]

/-- Encoding the executable secret key produces exactly the canonical Algorithm 18 bytes. -/
theorem encodeSecretKey_keygenInternal_eq_spec (vp : ValidatedParams)
    (prims : Primitives vp.params) (atomic : CoreWireCodec vp.params prims.core)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) :
    encodeSecretKey atomic (keygenInternal vp prims skSeed skPrf pkSeed).2 =
      encodeSecretKey atomic (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed).2 := by
  rw [keygenInternal_eq_spec]

/-- Encoding an executable signature produces exactly the canonical Algorithm 19 bytes. -/
theorem encodeSignature_signInternal_eq_spec (vp : ValidatedParams)
    (prims : Primitives vp.params) (atomic : CoreWireCodec vp.params prims.core)
    (msg : List Byte) (sk : SecretKeyCore prims.core) (addrnd : prims.Y) :
    encodeSignature vp atomic (signInternal vp prims msg sk addrnd) =
      encodeSignature vp atomic (GeneralScheme.signInternal vp prims msg sk addrnd) := by
  rw [signInternal_eq_spec]

/-! ## Deterministic external execution -/

/-- Executable explicit-seed form of FIPS Algorithm 21. -/
def keygenWithSeeds (vp : ValidatedParams) (prims : Primitives vp.params)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) :
    SecretKeyCore prims.core × PublicKeyCore prims.core :=
  let (pk, sk) := keygenInternal vp prims skSeed skPrf pkSeed
  (sk, pk)

theorem keygenWithSeeds_eq_spec (vp : ValidatedParams) (prims : Primitives vp.params)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) :
    keygenWithSeeds vp prims skSeed skPrf pkSeed =
      External.keygenWithSeeds vp prims skSeed skPrf pkSeed := by
  simp [keygenWithSeeds, External.keygenWithSeeds, keygenInternal_eq_spec]

end SLHDSA.Execution
