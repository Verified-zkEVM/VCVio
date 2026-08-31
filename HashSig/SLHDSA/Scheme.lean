/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Hypertree
public import HashSig.SLHDSA.Position

/-!
# SLH-DSA Scheme (FIPS 205 §9–10)

The top-level SLH-DSA signature scheme for the `d = 1` parameter set, assembled from FORS
(`HashSig.SLHDSA.Fors`) and the single-layer hypertree (`HashSig.SLHDSA.Hypertree`). The canonical
internal algorithms depend only on `CorePrimitives` and issue `H_msg` and every tweakable hash as
an explicit `HasQuery` operation:

- `slhKeygenInternalM` / `slhSignInternalM` / `slhVerifyInternalM` (Algorithms 18–20),
- `slhKeygenInternal` / `slhSignInternal` / `slhVerifyInternal`, the deterministic
  `PublicHash.impl` interpretations of those programs,
- `splitDigest`, the typed message-digest split into `md`, `idxTree`, and `idxLeaf` (§9), and
- `emptyContextMessage`, the FIPS 205 external-message encoding used by the canonical external
  scheme in `HashSig.SLHDSA.RandomOracle`.

The current signing and verification programs pass `Adrs.zero`, tree index `0`, and
`parts.idxLeaf.val` to the existing one-layer hypertree interface. This is FIPS-correct only for
valid `d = 1` parameters, where `DigestParts.idxTree_eq_zero_of_d_eq_one` proves that the parsed
tree index is zero. General hypertree consumption of `LayerPosition` is deferred to S08/S09.

Signing follows FIPS 205 Algorithm 19 literally: after `H_msg`, it creates the FORS signature,
recovers the FORS public key from that signature, and signs the recovered value with the
hypertree. It does not independently regenerate the FORS public key.

The deterministic correctness result `slhVerifyInternal_slhSignInternal` proves that every
honestly generated signature verifies for every fixed total public-hash answer function. This is
not a cached-random-oracle theorem; a probabilistic experiment must choose and thread that
semantics separately.

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
  let parts := splitDigest p digest
  let forsSig ← forsSignM core parts.md.toList sk.skSeed sk.pkSeed parts.forsAdrs
  let forsPk ← forsPkFromSigM core forsSig parts.md.toList sk.pkSeed parts.forsAdrs
  let htSig ← htSignM core forsPk sk.skSeed sk.pkSeed Adrs.zero 0 parts.idxLeaf.val
  return (R, forsSig, htSig)

/-- Canonical SLH-DSA internal verification (FIPS 205 Algorithm 20). Its public-hash schedule is
`H_msg`, FORS public-key recovery, then hypertree recovery and comparison with `PK.root`. -/
def slhVerifyInternalM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m] [DecidableEq core.Y]
    (msg : List Byte) (sig : SignatureCore p core) (pk : PublicKeyCore core) : m Bool := do
  let digest ← PublicHash.hmsg core sig.1 pk.pkSeed pk.pkRoot msg
  let parts := splitDigest p digest
  let forsPk ← forsPkFromSigM core sig.2.1 parts.md.toList pk.pkSeed parts.forsAdrs
  htVerifyM core forsPk sig.2.2 pk.pkSeed Adrs.zero 0 parts.idxLeaf.val pk.pkRoot

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

/-- Structural public-hash budget for verification. The intrinsic FORS shape contributes exactly
`k * (a + 1) + 1`, and the intrinsic XMSS path contributes exactly `h'`; no caller-controlled
list length appears in the budget. -/
def slhVerifyInternalQueryBound (p : Params) (core : CorePrimitives p)
    (_sig : SignatureCore p core) : ℕ :=
  1 + (p.k * (p.a + 1) + 1) +
    (p.len * (p.w - 1) + 1 + p.hp)

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
      let parts := splitDigest p digest
      isTotalQueryBound_bind
        (forsSignM_then_forsPkFromSigM_isTotalQueryBound
          core parts.md.toList sk.skSeed sk.pkSeed parts.forsAdrs) fun sigAndPk =>
            isTotalQueryBound_bind
              (htSignM_isTotalQueryBound_coarse core sigAndPk.2 sk.skSeed sk.pkSeed
                Adrs.zero 0 parts.idxLeaf.val) fun htSig =>
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
      (p.len * (p.w - 1) + 1 + p.hp) := by
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
      let parts := splitDigest p digest
      isTotalQueryBound_bind
        (forsPkFromSigM_isTotalQueryBound core sig.2.1 parts.md.toList pk.pkSeed
          parts.forsAdrs) fun forsPk =>
            htVerifyM_isTotalQueryBound_coarse core forsPk sig.2.2 pk.pkSeed Adrs.zero 0
              parts.idxLeaf.val pk.pkRoot
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
    (splitDigest p _).idxLeaf.isLt

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

/-! ### External-message encoding (FIPS 205 §10) -/

/-- FIPS 205 external-message encoding for the empty-context API:
`M' = 0x00 || 0x00 || M`. Internal algorithms consume `M'`; callers of the generic
signature API supply the raw message `M`. -/
def emptyContextMessage (msg : List Byte) : List Byte :=
  0x00 :: 0x00 :: msg

end SLHDSA
