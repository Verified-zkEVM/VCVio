/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Bridge.Hypertree
public import HashSig.SLHDSA.SHAKE128s.Bridge.PaperGame

/-!
# The paper model is FIPS 205's SLH-DSA-SHAKE-128s over one random oracle

The paper scheme `Bridge.model` (answers in `HashOutput`) and FIPS 205's pure-mode scheme
`FIPS205.scheme` (answers in `FIPS205.Answer`) are bridged along `answerEquiv`
(`schemeBridge`), so every security bit of the paper model is one of FIPS 205's
(`hasSecurityBits_fips205`).

Keys correspond through `digestEquiv` (`pkMap`, `skMap`). Signing and verification agree query for
query: the paper's `Scheme.sign`, with its answers relabelled, is FIPS 205's signer at the
corresponding key (`simulateQ_relabel_sign`), and likewise verification
(`simulateQ_relabel_verify`). Signing derives the randomizer with `PRF_msg` at `opt_rand = PK.seed`,
then `H_msg`, FORS and the hypertree, in the same order on both sides; the signature bytes agree
through `toBytes_sigOfCore` and parsing through `fromBytes?_eq`.

Key generation agrees in law only: the paper draws the secret seed, the `PRF` seed and the public
seed, in that order, while FIPS 205's `romScheme` draws the public seed first. The draws are
independent and uniform, so the reordered triples have the same law
(`map_seedMap_paperSeeds`), and at corresponding seeds the two programs computing the root are
equal (`keygenInternal_eq`); `keygen_of_seeds` assembles the bridge's key-generation field.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.Bridge

open SLHDSA SLHDSA.Security GeneralHypertree

/-- Programs of the paper model. -/
local notation "PaperComp" => OracleComp OracleWorld
/-- Programs of FIPS 205 over the typed interface. -/
local notation "TypedComp" => OracleComp (unifSpec + hashSpec FIPS205.core)
/-- Run a paper program in the FIPS 205 single-oracle world. -/
local notation "𝓡" => simulateQ (relabel answerEquiv)
/-- Run a program of the typed interface in the FIPS 205 single-oracle world. -/
local notation "𝓔" => simulateQ (encImpl FIPS205.params)

/-! ## Keys -/

/-- FIPS 205's public key of a paper public key: both fields as nodes. -/
@[expose] def pkMap (pk : PublicKey) : PublicKeyCore FIPS205.core :=
  ⟨digestEquiv pk.seed, digestEquiv pk.root⟩

/-- FIPS 205's secret key of a paper secret key: the secret seed, the `PRF` seed and the public
key, as nodes. -/
@[expose] def skMap (sk : SecretKey) : SecretKeyCore FIPS205.core :=
  ⟨digestEquiv sk.seed, digestEquiv sk.prf, digestEquiv sk.publicKey.seed,
    digestEquiv sk.publicKey.root⟩

/-! ## FIPS 205's internal algorithms -/

/-- FIPS 205's deterministic internal signer queries `PRF_msg` at `opt_rand = PK.seed` and signs
with the oracle-secret provider at the randomizer. -/
theorem internal_sign_eq (pk : PublicKeyCore FIPS205.core) (sk : SecretKeyCore FIPS205.core)
    (msg : List Byte) :
    FIPS205.internal.sign pk sk msg =
      𝓔 (do
        let R ← (query (spec := prfMsgSpec FIPS205.core) ⟨sk.skPrf, pk.pkSeed, msg⟩ :
          TypedComp FIPS205.core.Y)
        GeneralScheme.signInternalWithSecretRandomizerM FIPS205.core
          (oracleSecret FIPS205.core (Equiv.refl _) sk.pkSeed sk.skSeed) msg sk.pkSeed sk.pkRoot
          R) := rfl

/-- FIPS 205's internal verifier is `verifyInternalM` over the single oracle. -/
theorem internal_verify_eq (pk : PublicKeyCore FIPS205.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore FIPS205.params FIPS205.core) :
    FIPS205.internal.verify pk msg sig =
      𝓔 (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core msg sig pk :
        TypedComp Bool) := rfl

/-! ## Signing -/

/-- The truncation of an answer, read as a paper value, is the node of its first `n` bytes. -/
theorem truncate_answerEquiv_symm (ans : FIPS205.Answer) :
    Hashing.truncate (answerEquiv.symm ans) =
      digestEquiv.symm (prefixBytes FIPS205.params.params.n ans) := by
  have := prefixBytes_answerEquiv (answerEquiv.symm ans)
  rw [Equiv.apply_symm_apply] at this
  rw [this, Equiv.symm_apply_apply]

/-- **`PRF_msg`**: the paper's randomizer is FIPS 205's `PRF_msg` query. -/
theorem simulateQ_relabel_randomizer (prf seed : Digest) (msg : Bytes) :
    𝓡 (Hashing.randomizer prf seed msg : PaperComp Digest) =
      digestEquiv.symm <$> 𝓔 (query (spec := prfMsgSpec FIPS205.core)
        ⟨digestEquiv prf, digestEquiv seed, msg⟩ : TypedComp _) := by
  have h𝓔 : 𝓔 (query (spec := prfMsgSpec FIPS205.core)
        ⟨digestEquiv prf, digestEquiv seed, msg⟩ : TypedComp _) =
      prefixBytes FIPS205.params.params.n <$>
        (liftM ((Game.World FIPS205.Answer).query (.inr (Hashing.randomizerInput prf seed msg))) :
          OracleComp (Game.World FIPS205.Answer) FIPS205.Answer) := by
    rw [← encode_prfMsg]
    simp [encImpl]
    rfl
  rw [h𝓔, Hashing.randomizer, Hashing.shortHash, simulateQ_bind, simulateQ_relabel_hash,
    bind_map_left]
  simp only [simulateQ_pure, truncate_answerEquiv_symm]
  rfl

/-- **`H_msg`**: the paper's message digest is FIPS 205's `H_msg` query. -/
theorem simulateQ_relabel_messageDigest (r : Digest) (pk : PublicKey) (msg : Bytes) :
    𝓡 (Hashing.messageDigest r pk msg : PaperComp HashOutput) =
      answerEquiv.symm <$> 𝓔 (PublicHash.hmsg FIPS205.core (digestEquiv r) (digestEquiv pk.seed)
        (digestEquiv pk.root) msg : TypedComp _) := by
  have h𝓔 : 𝓔 (PublicHash.hmsg FIPS205.core (digestEquiv r) (digestEquiv pk.seed)
        (digestEquiv pk.root) msg : TypedComp _) =
        (liftM ((Game.World FIPS205.Answer).query (.inr (Hashing.messageInput r pk msg))) :
          OracleComp (Game.World FIPS205.Answer) FIPS205.Answer) := by
    rw [← encode_hmsg]
    simp [PublicHash.hmsg, encImpl]
    rfl
  rw [h𝓔, Hashing.messageDigest]
  exact simulateQ_relabel_hash _

/-- **Internal signing** (Algorithm 19, deterministic): the paper's `Scheme.signInternal` is FIPS
205's internal signer at the corresponding secret key, read back by `sigOfCore`: the randomizer,
the message digest, the FORS signature and its public key, then the hypertree signature. -/
theorem simulateQ_relabel_signInternal (sk : SecretKey) (msg : Bytes) :
    𝓡 (Scheme.signInternal sk msg : PaperComp Signature) =
      sigOfCore <$> FIPS205.internal.sign (FIPS205.SecretKeyCore.publicKey (skMap sk)) (skMap sk)
        msg := by
  rw [internal_sign_eq]
  unfold Scheme.signInternal
  refine ForsBridge.bind_bridge (simulateQ_relabel_randomizer _ _ _) fun R => ?_
  unfold GeneralScheme.signInternalWithSecretRandomizerM
  have hdig := simulateQ_relabel_messageDigest (digestEquiv.symm R) sk.publicKey msg
  rw [Equiv.apply_symm_apply] at hdig
  refine ForsBridge.bind_bridge hdig fun y => ?_
  have hfors := simulateQ_forsSign_parts (answerEquiv.symm y) sk.seed sk.publicKey.seed
  rw [parts, Equiv.apply_symm_apply] at hfors
  refine ForsBridge.bind_bridge hfors fun forsSig => ?_
  have hforsPk := simulateQ_forsPublicKeyFromSignature_parts (answerEquiv.symm y) forsSig
    sk.publicKey.seed
  rw [parts, Equiv.apply_symm_apply] at hforsPk
  refine ForsBridge.bind_bridge hforsPk fun forsPk => ?_
  have hht := simulateQ_relabel_hypertreeSign (answerEquiv.symm y) forsPk sk.seed
    sk.publicKey.seed
  rw [parts, Equiv.apply_symm_apply] at hht
  refine ForsBridge.bind_bridge hht fun ht => ?_
  exact ForsBridge.pure_bridge _ _ _ rfl

/-- **Signing** (Algorithm 22): the paper's `Scheme.sign`, relabelled, is FIPS 205's pure-mode
signer at the corresponding secret key. Both reject a context longer than 255 bytes. -/
theorem simulateQ_relabel_sign (sk : SecretKey) (req : Message) :
    𝓡 (Scheme.sign sk req : PaperComp (Option Bytes)) = FIPS205.scheme.sign (skMap sk) req := by
  simp only [Scheme.sign, FIPS205.scheme, frame_eq_encodePureMessage]
  cases External.encodePureMessage req.context req.message with
  | error e => simp [Except.toOption]
  | ok m =>
    simp only [Except.toOption]
    rw [simulateQ_bind, simulateQ_relabel_signInternal, bind_map_left, map_eq_bind_pure_comp]
    refine bind_congr fun σ => ?_
    simp [toBytes_sigOfCore]

/-! ## Verification -/

/-- **Internal verification** (Algorithm 20): the paper's `Scheme.verifyInternal` of the paper
reading of a FIPS 205 signature is FIPS 205's internal verifier at the corresponding public key. -/
theorem simulateQ_relabel_verifyInternal (pk : PublicKey) (msg : Bytes) (σ : CoreSignature) :
    𝓡 (Scheme.verifyInternal pk msg (sigOfCore σ) : PaperComp Bool) =
      FIPS205.internal.verify (pkMap pk) msg σ := by
  rw [internal_verify_eq, ← id_map (𝓔 _)]
  unfold Scheme.verifyInternal GeneralScheme.verifyInternalM
  have hdig := simulateQ_relabel_messageDigest (digestEquiv.symm σ.randomness) pk msg
  rw [Equiv.apply_symm_apply] at hdig
  refine ForsBridge.bind_bridge hdig fun y => ?_
  have hforsPk := simulateQ_forsPublicKeyFromSignature_parts (answerEquiv.symm y) σ.fors pk.seed
  rw [parts, Equiv.apply_symm_apply] at hforsPk
  refine ForsBridge.bind_bridge hforsPk fun forsPk => ?_
  have hht := simulateQ_relabel_hypertreeVerify (answerEquiv.symm y) forsPk σ.hypertree pk
  rw [parts, Equiv.apply_symm_apply] at hht
  rw [id_map]
  exact hht

/-- **Verification** (Algorithm 24): the paper's `Scheme.verify`, relabelled, is FIPS 205's
pure-mode verifier at the corresponding public key. Both reject a context longer than 255 bytes
and a string that does not parse. -/
theorem simulateQ_relabel_verify (pk : PublicKey) (req : Message) (sig : Bytes) :
    𝓡 (Scheme.verify pk req sig : PaperComp Bool) = FIPS205.scheme.verify (pkMap pk) req sig := by
  simp only [Scheme.verify, FIPS205.scheme, frame_eq_encodePureMessage, fromBytes?_eq]
  cases External.encodePureMessage req.context req.message with
  | error e => simp [Except.toOption]
  | ok m =>
    cases decodeSignature FIPS205.params wireCodec sig with
    | error e => simp [Except.toOption]
    | ok σ =>
      simp only [Except.toOption, Option.map_eq_map, Option.map_some]
      exact simulateQ_relabel_verifyInternal pk m σ

/-! ## Key generation -/

/-- The paper's uniform draws, relabelled, are the same draws in the FIPS 205 world. -/
theorem simulateQ_relabel_unifQuery {α : Type} (oa : ProbComp α) :
    𝓡 (simulateQ (fun i => query (spec := unifSpec) i) oa : PaperComp α) =
      (liftM oa : OracleComp (Game.World FIPS205.Answer) α) := by
  rw [← liftComp_eq_liftM, liftComp_def,
    QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := fun t => liftM (unifSpec.query t))]
  intro t
  rfl

/-- The paper's seeds: the secret seed, the `PRF` seed and the public seed, in that order. -/
@[expose] noncomputable def paperSeeds : ProbComp (Digest × Digest × Digest) := do
  let a ← $ᵗ Digest
  let b ← $ᵗ Digest
  let c ← $ᵗ Digest
  return (a, b, c)

/-- FIPS 205's seeds in `romScheme`: the public seed, the secret seed and the `PRF` seed, in that
order. -/
@[expose] noncomputable def fipsSeeds :
    ProbComp (FIPS205.core.PkSeed × FIPS205.core.SkSeed × FIPS205.core.SkPrf) := do
  let p ← $ᵗ FIPS205.core.PkSeed
  let s ← $ᵗ FIPS205.core.SkSeed
  let f ← $ᵗ FIPS205.core.SkPrf
  return (p, s, f)

/-- FIPS 205's seeds corresponding to the paper's, reordered: public, secret, `PRF`. -/
@[expose] def seedMap (t : Digest × Digest × Digest) :
    FIPS205.core.PkSeed × FIPS205.core.SkSeed × FIPS205.core.SkPrf :=
  (digestEquiv t.2.2, digestEquiv t.1, digestEquiv t.2.1)

/-- The paper's key generation, relabelled, draws its seeds and then runs `keygenInternal`. -/
theorem simulateQ_relabel_keygen :
    𝓡 (Scheme.keygen : PaperComp (SecretKey × PublicKey)) =
      (liftM paperSeeds : OracleComp (Game.World FIPS205.Answer) _) >>= fun t =>
        𝓡 (Scheme.keygenInternal t.1 t.2.1 t.2.2 : PaperComp (SecretKey × PublicKey)) := by
  simp only [Scheme.keygen, simulateQ_bind, simulateQ_relabel_unifQuery]
  simp [paperSeeds]

/-- FIPS 205's key generation draws its seeds and then computes the root with the oracle-secret
provider, returning the keys as `(SK, PK)`. -/
theorem scheme_keygen :
    FIPS205.scheme.keygen =
      (liftM fipsSeeds : OracleComp (Game.World FIPS205.Answer) _) >>= fun t =>
        (fun keys => (keys.2, keys.1)) <$> 𝓔 (do
          let pkRoot ← GeneralScheme.keygenInternalWithSecretM FIPS205.core
            (oracleSecret FIPS205.core (Equiv.refl _) t.1 t.2.1) t.1
          return ((⟨t.1, pkRoot⟩ : PublicKeyCore FIPS205.core),
            (⟨t.2.1, t.2.2, t.1, pkRoot⟩ : SecretKeyCore FIPS205.core)) : TypedComp _) := by
  simp [FIPS205.scheme, FIPS205.internal, fipsSeeds, shakeRomScheme, romScheme, romKeygenAt,
    simulateQ_encImpl_liftM]

/-- **Internal key generation** (Algorithm 18): at corresponding seeds, the paper's
`Scheme.keygenInternal`, relabelled and with its keys mapped, is FIPS 205's: the root of the top
XMSS tree. -/
theorem keygenInternal_eq (t : Digest × Digest × Digest) :
    Prod.map skMap pkMap <$>
        𝓡 (Scheme.keygenInternal t.1 t.2.1 t.2.2 : PaperComp (SecretKey × PublicKey)) =
      (fun keys => (keys.2, keys.1)) <$> 𝓔 (do
          let pkRoot ← GeneralScheme.keygenInternalWithSecretM FIPS205.core
            (oracleSecret FIPS205.core (Equiv.refl _) (seedMap t).1 (seedMap t).2.1) (seedMap t).1
          return ((⟨(seedMap t).1, pkRoot⟩ : PublicKeyCore FIPS205.core),
            (⟨(seedMap t).2.1, (seedMap t).2.2, (seedMap t).1, pkRoot⟩ :
              SecretKeyCore FIPS205.core)) : TypedComp _) := by
  rw [Scheme.keygenInternal, simulateQ_bind, simulateQ_relabel_keygenRoot, bind_map_left,
    simulateQ_bind, map_bind, map_bind]
  refine bind_congr fun root => ?_
  simp [skMap, pkMap, seedMap]

/-- **The seed draws agree in law**: the paper's three uniform digests, reordered and read as
nodes, are FIPS 205's three uniform seeds. -/
theorem map_seedMap_paperSeeds : seedMap <$> paperSeeds =ᵈ fipsSeeds := by
  have h1 : seedMap <$> paperSeeds = (do
      let a ← $ᵗ Digest
      let b ← $ᵗ Digest
      let c ← $ᵗ Digest
      return seedMap (a, b, c) : ProbComp _) := by simp [paperSeeds]
  have h2 : (do
      let c ← $ᵗ Digest
      let a ← $ᵗ Digest
      let b ← $ᵗ Digest
      return seedMap (a, b, c) : ProbComp _) = (do
      let p ← (digestEquiv : Digest → FIPS205.core.PkSeed) <$> ($ᵗ Digest)
      let s ← (digestEquiv : Digest → FIPS205.core.SkSeed) <$> ($ᵗ Digest)
      let f ← (digestEquiv : Digest → FIPS205.core.SkPrf) <$> ($ᵗ Digest)
      return (p, s, f) : ProbComp _) := by
    simp only [seedMap, bind_map_left]
    rfl
  rw [h1]
  refine ((EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_bind_swap _ _ _).trans
    (EvalDistEq.bind_bind_swap _ _ _)).trans ?_
  rw [h2]
  exact map_digestEquiv_uniformSample_pkSeed.bind fun _ =>
    map_digestEquiv_uniformSample_skSeed.bind fun _ =>
      map_digestEquiv_uniformSample_skPrf.bind fun _ => EvalDistEq.rfl

/-! ## The bridge -/

/-- **The paper model is bridged to FIPS 205** along `answerEquiv`: signing and verification agree
through `relabel answerEquiv` at the corresponding keys, and the two key generations agree in
law. -/
@[expose] noncomputable def schemeBridge : SchemeBridge answerEquiv model FIPS205.scheme where
  pk := pkMap
  sk := skMap
  sign := simulateQ_relabel_sign
  verify := simulateQ_relabel_verify
  keygen := keygen_of_seeds pkMap skMap paperSeeds fipsSeeds seedMap map_seedMap_paperSeeds _ _
    simulateQ_relabel_keygen scheme_keygen keygenInternal_eq

/-- **Security bits transfer from the paper model to FIPS 205**: every security bit of the paper
model, in any counting mode, is one of FIPS 205's SLH-DSA-SHAKE-128s over one SHAKE256 random
oracle. -/
theorem hasSecurityBits_fips205 {Z : Finset Unforgeability.QueryKind} {bits : ℕ}
    (h : Game.HasSecurityBits model Z bits) : Game.HasSecurityBits FIPS205.scheme Z bits :=
  hasSecurityBits_of_bridge schemeBridge map_answerEquiv_uniformSample h

end SLHDSA.SHAKE128s.Bridge
