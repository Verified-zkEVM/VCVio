/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Hypertree
public import VCVio.CryptoFoundations.SignatureAlg

/-!
# SLH-DSA Scheme (FIPS 205 §9–10)

The top-level SLH-DSA signature scheme for the `d = 1` parameter set, assembled from FORS
(`HashSig.SLHDSA.Fors`) and the single-layer hypertree (`HashSig.SLHDSA.Hypertree`). The canonical
internal algorithms depend only on `CorePrimitives` and issue `H_msg` and every tweakable hash as
an explicit `HasQuery` operation:

- `slhKeygenInternalM` / `slhSignInternalM` / `slhVerifyInternalM` (Algorithms 18–20),
- `slhKeygenInternal` / `slhSignInternal` / `slhVerifyInternal`, the deterministic
  `PublicHash.impl` interpretations of those programs,
- `splitDigest`, the message-digest split into `(md, idxLeaf)` (§9; for `d = 1` the tree index
  is always `0`, so it is omitted),
- the external probabilistic wrappers `slhKeygen` / `slhSign` / `slhVerify` (Algorithms 21–24,
  empty context), and the generic `SignatureAlg` instantiation `slhdsaAlg` in `ProbComp`.

Signing follows FIPS 205 Algorithm 19 literally: after `H_msg`, it creates the FORS signature,
recovers the FORS public key from that signature, and signs the recovered value with the
hypertree. It does not independently regenerate the FORS public key.

The headline result `slhdsaAlg_perfectlyComplete` proves **perfect completeness with no `sorry`**:
every honestly generated signature verifies. The deterministic kernel is also exposed for every
fixed total public-hash answer function. This is not a cached-random-oracle theorem; a security
experiment must choose and thread that semantics separately.

## References

- NIST FIPS 205, §9 (Algorithms 18–22, 24), §10 (external API), §4.1 (the H_msg digest split)
-/

@[expose] public section


open OracleComp OracleSpec

namespace SLHDSA

variable {p : Params}

/-- The SLH-DSA public key over an implementation-independent context: public seed and
hypertree root. -/
structure PublicKeyCore (core : CorePrimitives p) where
  /-- Public seed `PK.seed`. -/
  pkSeed : core.PkSeed
  /-- Hypertree root `PK.root`. -/
  pkRoot : core.Y

/-- The SLH-DSA secret key over an implementation-independent context. It carries the public
material required by signing. -/
structure SecretKeyCore (core : CorePrimitives p) where
  /-- Secret seed `SK.seed`. -/
  skSeed : core.SkSeed
  /-- Message-PRF key `SK.prf`. -/
  skPrf : core.SkPrf
  /-- Public seed `PK.seed`. -/
  pkSeed : core.PkSeed
  /-- Hypertree root `PK.root`. -/
  pkRoot : core.Y

/-- An SLH-DSA signature: randomizer `R`, FORS signature, and hypertree signature
(`R ‖ SIG_FORS ‖ SIG_HT`). -/
abbrev SignatureCore (p : Params) (core : CorePrimitives p) :=
  core.Y × ForsSigCore p core × HtSigCore p core

/-! ### Message-digest split (FIPS 205 §9) -/

/-- Split the message digest into the FORS message `md` and the hypertree leaf index `idxLeaf`
(reduced mod `2^{h'}`). For `d = 1` the tree-index field is empty, so the tree index is `0` and
omitted. -/
def splitDigest (p : Params) (digest : Bytes p.m) : List Byte × ℕ :=
  let bytes := digest.toList
  (bytes.take p.digestBytes,
    toInt ((bytes.drop (p.digestBytes + p.treeIdxBytes)).take p.leafIdxBytes) % 2 ^ p.hp)

theorem splitDigest_snd_lt (p : Params) (digest : Bytes p.m) :
    (splitDigest p digest).2 < 2 ^ p.hp := by
  simp only [splitDigest]
  exact Nat.mod_lt _ (by positivity)

/-- The FORS base address keyed to the per-message hypertree leaf `idxLeaf` (FIPS 205 Alg 19). -/
def forsAdrsOf (idxLeaf : ℕ) : Adrs :=
  ((Adrs.zero.setTreeAddress 0).setTypeAndClear .forsTree).setKeyPairAddress idxLeaf

/-! ### Canonical internal algorithms (FIPS 205 §9) -/

/-- Canonical SLH-DSA internal key generation (FIPS 205 Algorithm 18). The public root is
computed by the explicit-query hypertree program. -/
def slhKeygenInternalM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    m (PublicKeyCore core × SecretKeyCore core) := do
  let pkRoot ← htRootM core skSeed pkSeed Adrs.zero 0
  return (⟨pkSeed, pkRoot⟩, ⟨skSeed, skPrf, pkSeed, pkRoot⟩)

/-- Canonical SLH-DSA internal signing (FIPS 205 Algorithm 19). Its public-hash schedule is
`H_msg`, FORS signing, recovery of the FORS public key from that signature, then hypertree
signing. In particular, signing does not call `forsPkGenM`. -/
def slhSignInternalM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    m (SignatureCore p core) := do
  let R := core.PRFmsg sk.skPrf addrnd msg
  let digest ← PublicHash.hmsg core R sk.pkSeed sk.pkRoot msg
  let idxLeaf := (splitDigest p digest).2
  let md := (splitDigest p digest).1
  let fAdrs := forsAdrsOf idxLeaf
  let forsSig ← forsSignM core md sk.skSeed sk.pkSeed fAdrs
  let forsPk ← forsPkFromSigM core forsSig md sk.pkSeed fAdrs
  let htSig ← htSignM core forsPk sk.skSeed sk.pkSeed Adrs.zero 0 idxLeaf
  return (R, forsSig, htSig)

/-- Canonical SLH-DSA internal verification (FIPS 205 Algorithm 20). Its public-hash schedule is
`H_msg`, FORS public-key recovery, then hypertree recovery and comparison with `PK.root`. -/
def slhVerifyInternalM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m] [DecidableEq core.Y]
    (msg : List Byte) (sig : SignatureCore p core) (pk : PublicKeyCore core) : m Bool := do
  let digest ← PublicHash.hmsg core sig.1 pk.pkSeed pk.pkRoot msg
  let idxLeaf := (splitDigest p digest).2
  let md := (splitDigest p digest).1
  let fAdrs := forsAdrsOf idxLeaf
  let forsPk ← forsPkFromSigM core sig.2.1 md pk.pkSeed fAdrs
  htVerifyM core forsPk sig.2.2 pk.pkSeed Adrs.zero 0 idxLeaf pk.pkRoot

/-! ### Pure deterministic interpretations -/

/-- Pure internal key generation is the deterministic interpretation of
`slhKeygenInternalM`. -/
def slhKeygenInternal (prims : Primitives p) (skSeed : prims.SkSeed) (skPrf : prims.SkPrf)
    (pkSeed : prims.PkSeed) : PublicKeyCore prims.core × SecretKeyCore prims.core :=
  simulateQ (PublicHash.impl prims)
    (slhKeygenInternalM prims.core skSeed skPrf pkSeed :
      OracleComp (publicHashSpec prims.core)
        (PublicKeyCore prims.core × SecretKeyCore prims.core))

/-- Pure internal signing is the deterministic interpretation of `slhSignInternalM`. -/
def slhSignInternal (prims : Primitives p) (msg : List Byte) (sk : SecretKeyCore prims.core)
    (addrnd : prims.Y) : SignatureCore p prims.core :=
  simulateQ (PublicHash.impl prims)
    (slhSignInternalM prims.core msg sk addrnd :
      OracleComp (publicHashSpec prims.core) (SignatureCore p prims.core))

/-- Pure internal verification is the deterministic interpretation of
`slhVerifyInternalM`. -/
def slhVerifyInternal (prims : Primitives p) [DecidableEq prims.Y] (msg : List Byte)
    (sig : SignatureCore p prims.core) (pk : PublicKeyCore prims.core) : Bool :=
  simulateQ (PublicHash.impl prims)
    (slhVerifyInternalM prims.core msg sig pk : OracleComp (publicHashSpec prims.core) Bool)

/-! ### Naturality -/

private theorem queryHom_hmsg (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (r : core.Y) (pkSeed : core.PkSeed) (pkRoot : core.Y) (msg : List Byte) :
    F.toMonadHom (PublicHash.hmsg core r pkSeed pkRoot msg) =
      PublicHash.hmsg core r pkSeed pkRoot msg := by
  change F.toMonadHom
      (query (spec := publicHashSpec core) (.hmsg r pkSeed pkRoot msg)) =
    query (spec := publicHashSpec core) (.hmsg r pkSeed pkRoot msg)
  exact HasQuery.map_query F _

/-- Query-preserving monad morphisms commute with canonical internal key generation. -/
theorem slhKeygenInternalM_natural (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    F.toMonadHom (slhKeygenInternalM core skSeed skPrf pkSeed) =
      slhKeygenInternalM core skSeed skPrf pkSeed := by
  simp [slhKeygenInternalM, htRootM_natural core F]

/-- Query-preserving monad morphisms commute with canonical internal signing. -/
theorem slhSignInternalM_natural (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    F.toMonadHom (slhSignInternalM core msg sk addrnd) =
      slhSignInternalM core msg sk addrnd := by
  simp [slhSignInternalM, queryHom_hmsg core F,
    forsSignM_natural core F, forsPkFromSigM_natural core F, htSignM_natural core F]

/-- Query-preserving monad morphisms commute with canonical internal verification. -/
theorem slhVerifyInternalM_natural (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n] [DecidableEq core.Y]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (msg : List Byte) (sig : SignatureCore p core) (pk : PublicKeyCore core) :
    F.toMonadHom (slhVerifyInternalM core msg sig pk) =
      slhVerifyInternalM core msg sig pk := by
  simp [slhVerifyInternalM, queryHom_hmsg core F,
    forsPkFromSigM_natural core F, htVerifyM_natural core F]

/-! ### Structural query bounds -/

/-- Structural public-hash budget for internal key generation. -/
def slhKeygenInternalQueryBound (p : Params) : ℕ :=
  xmssNodeQueryBound p p.hp

/-- Structural public-hash budget for the complete internal signing schedule: one `H_msg`, FORS
signing and recovery from that signature, then hypertree signing.  The WOTS+ term is made uniform
by allowing every chain its full `w - 1` steps. -/
def slhSignInternalQueryBound (p : Params) : ℕ :=
  1 + ((p.k * ((2 ^ p.a - 1) + (2 ^ p.a - p.a - 1)) +
      (p.k * (p.a + 1) + 1)) +
    (p.len * (p.w - 1) + xmssAuthPathQueryBound p p.hp))

/-- Structural public-hash budget for verification of the supplied signature. The FORS term
tracks the actual authentication-path lengths. The hypertree term uses the maximum WOTS+ chain
budget plus the supplied XMSS authentication-path length. -/
def slhVerifyInternalQueryBound (p : Params) (core : CorePrimitives p)
    (sig : SignatureCore p core) : ℕ :=
  1 + ((∑ i : Fin p.k, (fun j : Fin p.k => 1 + (sig.2.1[j.val]).2.length) i) + 1) +
    (p.len * (p.w - 1) + 1 + sig.2.2.2.length)

private theorem publicHash_hmsg_isTotalQueryBound_one (core : CorePrimitives p)
    (r : core.Y) (pkSeed : core.PkSeed) (pkRoot : core.Y) (msg : List Byte) :
    IsTotalQueryBound
      (PublicHash.hmsg core r pkSeed pkRoot msg :
        OracleComp (publicHashSpec core) (Bytes p.m)) 1 := by
  simp [PublicHash.hmsg, IsTotalQueryBound]

/-- Internal key generation inherits the complete hypertree-root budget. -/
theorem slhKeygenInternalM_isTotalQueryBound (core : CorePrimitives p)
    (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    IsTotalQueryBound
      (slhKeygenInternalM core skSeed skPrf pkSeed :
        OracleComp (publicHashSpec core) (PublicKeyCore core × SecretKeyCore core))
      (slhKeygenInternalQueryBound p) := by
  simpa [slhKeygenInternalM, slhKeygenInternalQueryBound] using
    isTotalQueryBound_bind (htRootM_isTotalQueryBound core skSeed pkSeed Adrs.zero 0)
      (fun pkRoot => show IsTotalQueryBound
        (pure (PublicKeyCore.mk pkSeed pkRoot,
          SecretKeyCore.mk skSeed skPrf pkSeed pkRoot) :
          OracleComp (publicHashSpec core) _) 0 from trivial)

private theorem htSignM_isTotalQueryBound_coarse (core : CorePrimitives p)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) :
    IsTotalQueryBound
      (htSignM core msg sk pk adrs idxTree idxLeaf :
        OracleComp (publicHashSpec core) (HtSigCore p core))
      (p.len * (p.w - 1) + xmssAuthPathQueryBound p p.hp) := by
  apply (htSignM_isTotalQueryBound core msg sk pk adrs idxTree idxLeaf).mono
  have hsum :
      (∑ i : Fin p.len, chainStepsCore core msg i.val) ≤ p.len * (p.w - 1) := by
    calc
      (∑ i : Fin p.len, chainStepsCore core msg i.val) ≤
          ∑ _ : Fin p.len, (p.w - 1) := by
            apply Finset.sum_le_sum
            intro i hi
            exact chainStepsCore_le core msg i.val
      _ = p.len * (p.w - 1) := by simp
  omega

/-- Internal signing follows and bounds the whole FIPS 205 Algorithm 19 public-hash schedule:
one `H_msg` query, sibling-only FORS signing, FORS recovery from the generated signature, and
hypertree signing.  The theorem counts calls in the free oracle program.  It is an upper bound,
not a count of distinct lazy-random-oracle cache misses or fresh samples. -/
theorem slhSignInternalM_isTotalQueryBound (core : CorePrimitives p)
    (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    IsTotalQueryBound
      (slhSignInternalM core msg sk addrnd :
        OracleComp (publicHashSpec core) (SignatureCore p core))
      (slhSignInternalQueryBound p) := by
  let R := core.PRFmsg sk.skPrf addrnd msg
  have hbound := isTotalQueryBound_bind
    (publicHash_hmsg_isTotalQueryBound_one core R sk.pkSeed sk.pkRoot msg) fun digest =>
      let idxLeaf := (splitDigest p digest).2
      let md := (splitDigest p digest).1
      let fAdrs := forsAdrsOf idxLeaf
      isTotalQueryBound_bind
        (forsSignM_then_forsPkFromSigM_isTotalQueryBound
          core md sk.skSeed sk.pkSeed fAdrs) fun sigAndPk =>
            isTotalQueryBound_bind
              (htSignM_isTotalQueryBound_coarse core sigAndPk.2 sk.skSeed sk.pkSeed
                Adrs.zero 0 idxLeaf) fun htSig =>
                  show IsTotalQueryBound
                    (pure (R, sigAndPk.1, htSig) :
                      OracleComp (publicHashSpec core) (SignatureCore p core)) 0 from trivial
  simpa [slhSignInternalM, slhSignInternalQueryBound, R, bind_assoc] using hbound

private theorem htVerifyM_isTotalQueryBound_coarse (core : CorePrimitives p)
    [DecidableEq core.Y] (msg : core.Y) (sig : HtSigCore p core)
    (pk : core.PkSeed) (adrs : Adrs) (idxTree idxLeaf : ℕ) (pkRoot : core.Y) :
    IsTotalQueryBound
      (htVerifyM core msg sig pk adrs idxTree idxLeaf pkRoot :
        OracleComp (publicHashSpec core) Bool)
      (p.len * (p.w - 1) + 1 + sig.2.length) := by
  apply (htVerifyM_isTotalQueryBound core msg sig pk adrs idxTree idxLeaf pkRoot).mono
  have hsum :
      (∑ i : Fin p.len, (p.w - 1 - chainStepsCore core msg i.val)) ≤
        p.len * (p.w - 1) := by
    calc
      (∑ i : Fin p.len, (p.w - 1 - chainStepsCore core msg i.val)) ≤
          ∑ _ : Fin p.len, (p.w - 1) := by
            apply Finset.sum_le_sum
            intro i hi
            omega
      _ = p.len * (p.w - 1) := by simp
  omega

/-- Verification is bounded by one `H_msg` query, FORS recovery for the supplied paths, and
hypertree recovery with a coarse full-WOTS chain allowance. This counts free-oracle calls, not
distinct random-oracle cache misses. -/
theorem slhVerifyInternalM_isTotalQueryBound (core : CorePrimitives p) [DecidableEq core.Y]
    (msg : List Byte) (sig : SignatureCore p core) (pk : PublicKeyCore core) :
    IsTotalQueryBound
      (slhVerifyInternalM core msg sig pk : OracleComp (publicHashSpec core) Bool)
      (slhVerifyInternalQueryBound p core sig) := by
  have hbound := isTotalQueryBound_bind
    (publicHash_hmsg_isTotalQueryBound_one core sig.1 pk.pkSeed pk.pkRoot msg) fun digest =>
      isTotalQueryBound_bind
        (forsPkFromSigM_isTotalQueryBound core sig.2.1 (splitDigest p digest).1 pk.pkSeed
          (forsAdrsOf (splitDigest p digest).2)) fun forsPk =>
            htVerifyM_isTotalQueryBound_coarse core forsPk sig.2.2 pk.pkSeed Adrs.zero 0
              (splitDigest p digest).2 pk.pkRoot
  simpa [slhVerifyInternalM, slhVerifyInternalQueryBound, Nat.add_assoc] using hbound

/-! ### Deterministic interpretations -/

@[simp]
theorem simulateQ_slhKeygenInternalM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id)
    (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    simulateQ answer
        (slhKeygenInternalM core skSeed skPrf pkSeed :
          OracleComp (publicHashSpec core) (PublicKeyCore core × SecretKeyCore core)) =
      slhKeygenInternal (PublicHash.withPublicHash core answer) skSeed skPrf pkSeed := by
  simp [slhKeygenInternal, PublicHash.impl_withPublicHash]

@[simp]
theorem simulateQ_slhKeygenInternalM (prims : Primitives p)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) :
    simulateQ (PublicHash.impl prims)
        (slhKeygenInternalM prims.core skSeed skPrf pkSeed :
          OracleComp (publicHashSpec prims.core)
            (PublicKeyCore prims.core × SecretKeyCore prims.core)) =
      slhKeygenInternal prims skSeed skPrf pkSeed := rfl

@[simp]
theorem simulateQ_slhSignInternalM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id)
    (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    simulateQ answer
        (slhSignInternalM core msg sk addrnd :
          OracleComp (publicHashSpec core) (SignatureCore p core)) =
      slhSignInternal (PublicHash.withPublicHash core answer) msg sk addrnd := by
  simp [slhSignInternal, PublicHash.impl_withPublicHash]

@[simp]
theorem simulateQ_slhSignInternalM (prims : Primitives p)
    (msg : List Byte) (sk : SecretKeyCore prims.core) (addrnd : prims.Y) :
    simulateQ (PublicHash.impl prims)
        (slhSignInternalM prims.core msg sk addrnd :
          OracleComp (publicHashSpec prims.core) (SignatureCore p prims.core)) =
      slhSignInternal prims msg sk addrnd := rfl

@[simp]
theorem simulateQ_slhVerifyInternalM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id) [DecidableEq core.Y]
    (msg : List Byte) (sig : SignatureCore p core) (pk : PublicKeyCore core) :
    simulateQ answer
        (slhVerifyInternalM core msg sig pk : OracleComp (publicHashSpec core) Bool) =
      slhVerifyInternal (PublicHash.withPublicHash core answer) msg sig pk := by
  simp [slhVerifyInternal, PublicHash.impl_withPublicHash]

@[simp]
theorem simulateQ_slhVerifyInternalM (prims : Primitives p) [DecidableEq prims.Y]
    (msg : List Byte) (sig : SignatureCore p prims.core) (pk : PublicKeyCore prims.core) :
    simulateQ (PublicHash.impl prims)
        (slhVerifyInternalM prims.core msg sig pk :
          OracleComp (publicHashSpec prims.core) Bool) =
      slhVerifyInternal prims msg sig pk := rfl

/-- Fixed-answer correctness of the canonical internal programs. Key generation, signing, and
verification use one total deterministic answer function. This theorem does not install or make
a claim about random-oracle caching. -/
theorem simulateQ_slhVerifyInternalM_slhSignInternalM_withPublicHash
    (core : CorePrimitives p) (answer : QueryImpl (publicHashSpec core) Id)
    [DecidableEq core.Y]
    (msg : List Byte) (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed)
    (addrnd : core.Y) :
    simulateQ answer (do
      let (pk, sk) ← slhKeygenInternalM core skSeed skPrf pkSeed
      let sig ← slhSignInternalM core msg sk addrnd
      slhVerifyInternalM core msg sig pk) = true := by
  simp only [slhKeygenInternalM, slhSignInternalM, slhVerifyInternalM,
    simulateQ_bind, simulateQ_pure,
    simulateQ_htRootM_withPublicHash, simulateQ_forsSignM_withPublicHash,
    simulateQ_forsPkFromSigM_withPublicHash, simulateQ_htSignM_withPublicHash,
    simulateQ_htVerifyM_withPublicHash]
  exact htVerify_htSign (PublicHash.withPublicHash core answer) _ skSeed pkSeed Adrs.zero 0 _
    (splitDigest_snd_lt p _)

/-- **Deterministic correctness core**: an honestly generated signature verifies, for every
choice of seeds, randomizer, and deterministic public-hash implementation. -/
theorem slhVerifyInternal_slhSignInternal (prims : Primitives p) [DecidableEq prims.Y]
    (msg : List Byte) (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed)
    (addrnd : prims.Y) :
    slhVerifyInternal prims msg
        (slhSignInternal prims msg (slhKeygenInternal prims skSeed skPrf pkSeed).2 addrnd)
        (slhKeygenInternal prims skSeed skPrf pkSeed).1 = true := by
  have h := simulateQ_slhVerifyInternalM_slhSignInternalM_withPublicHash
    prims.core (PublicHash.impl prims) msg skSeed skPrf pkSeed addrnd
  change ((do
    let (pk, sk) ← slhKeygenInternal prims skSeed skPrf pkSeed
    let sig ← slhSignInternal prims msg sk addrnd
    slhVerifyInternal prims msg sig pk) : Id Bool) = true
  simpa only [simulateQ_bind, simulateQ_slhKeygenInternalM,
    simulateQ_slhSignInternalM, simulateQ_slhVerifyInternalM] using h

/-! ### External algorithms and the `SignatureAlg` instance (FIPS 205 §10) -/

variable (prims : Primitives p)

/-- FIPS 205 external-message encoding for the empty-context API:
`M' = 0x00 || 0x00 || M`. Internal algorithms consume `M'`; callers of the generic
signature API supply the raw message `M`. -/
def emptyContextMessage (msg : List Byte) : List Byte :=
  0x00 :: 0x00 :: msg

/-- SLH-DSA key generation (FIPS 205 Algorithm 21): sample the three seeds. -/
def slhKeygen [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] :
    ProbComp (PublicKeyCore prims.core × SecretKeyCore prims.core) := do
  let skSeed ← $ᵗ prims.SkSeed
  let skPrf ← $ᵗ prims.SkPrf
  let pkSeed ← $ᵗ prims.PkSeed
  return slhKeygenInternal prims skSeed skPrf pkSeed

/-- SLH-DSA signing (FIPS 205 Algorithm 22, empty context, hedged): sample `addrnd`. -/
def slhSign [SampleableType prims.Y] (sk : SecretKeyCore prims.core) (msg : List Byte) :
    ProbComp (SignatureCore p prims.core) := do
  let addrnd ← $ᵗ prims.Y
  return slhSignInternal prims (emptyContextMessage msg) sk addrnd

/-- SLH-DSA verification (FIPS 205 Algorithm 24, empty context). -/
def slhVerify [DecidableEq prims.Y] (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : SignatureCore p prims.core) : Bool :=
  slhVerifyInternal prims (emptyContextMessage msg) sig pk

/-- SLH-DSA as a generic `SignatureAlg` in the `ProbComp` monad. -/
def slhdsaAlg [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y] [DecidableEq prims.Y] :
    SignatureAlg ProbComp (List Byte) (PublicKeyCore prims.core) (SecretKeyCore prims.core)
      (SignatureCore p prims.core) where
  keygen := slhKeygen prims
  sign _pk sk msg := slhSign prims sk msg
  verify pk msg σ := pure (slhVerify prims pk msg σ)

/-- **Perfect completeness of SLH-DSA** (FIPS 205 §9 correctness): every honestly generated
signature verifies, with probability one. Proved with no `sorry` from the deterministic core
`slhVerifyInternal_slhSignInternal`. -/
theorem slhdsaAlg_perfectlyComplete [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y] [DecidableEq prims.Y] :
    (slhdsaAlg prims).PerfectlyComplete ProbCompRuntime.probComp := by
  intro msg
  set mx : ProbComp Bool := do
    let (pk, sk) ← (slhdsaAlg prims).keygen
    let sig ← (slhdsaAlg prims).sign pk sk msg
    (slhdsaAlg prims).verify pk msg sig with hmx
  have huniq : ∀ y ∈ support mx, y = true := by
    intro y hy
    rw [hmx] at hy
    simp only [slhdsaAlg] at hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨⟨pk, sk⟩, hpksk, hy⟩ := hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨sig, hsig, hy⟩ := hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    simp only [slhKeygen] at hpksk
    rw [mem_support_bind_iff] at hpksk
    obtain ⟨skSeed, -, hpksk⟩ := hpksk
    rw [mem_support_bind_iff] at hpksk
    obtain ⟨skPrf, -, hpksk⟩ := hpksk
    rw [mem_support_bind_iff] at hpksk
    obtain ⟨pkSeed, -, hpksk⟩ := hpksk
    simp only [support_pure, Set.mem_singleton_iff] at hpksk
    simp only [slhSign] at hsig
    rw [mem_support_bind_iff] at hsig
    obtain ⟨addrnd, -, hsig⟩ := hsig
    simp only [support_pure, Set.mem_singleton_iff] at hsig
    subst hsig
    have hpk : pk = (slhKeygenInternal prims skSeed skPrf pkSeed).1 := congrArg Prod.fst hpksk
    have hsk : sk = (slhKeygenInternal prims skSeed skPrf pkSeed).2 := congrArg Prod.snd hpksk
    subst hpk; subst hsk
    exact slhVerifyInternal_slhSignInternal prims (emptyContextMessage msg)
      skSeed skPrf pkSeed addrnd
  change Pr[= true | mx] = 1
  exact probOutput_eq_one_of_support_subset_singleton
    (NeverFail.probFailure_eq_zero (mx := mx)) huniq

end SLHDSA
