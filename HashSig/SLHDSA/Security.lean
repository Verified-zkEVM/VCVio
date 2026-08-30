/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.RandomOracle
public import HashSig.SLHDSA.Security.Targets
public import VCVio.CryptoFoundations.HardnessAssumptions.CollisionResistance
public import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.ITSR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTDSPR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.PRF

/-!
# SLH-DSA Cryptographic Primitive Families

This module packages the hash and pseudorandom-function primitives used by `slhdsaAlg` into the
generic `TweakableHash` and `PRFScheme` interfaces:

- `Primitives.fHash` and `Primitives.hHash` expose `F` and `H` as tweakable hash families with
  the instantiation's canonical encoded `AdrsKey` as the tweak;
- `Primitives.thashCollection` packages every fixed input arity of `Thash` under one public seed
  and encoded-address space;
- `Primitives.msgPrfScheme` exposes the message randomizer `PRF_msg`; and
- `Primitives.skPrfScheme` exposes the secret-value derivation function `PRF` jointly over its
  public seed and address inputs.

These packages identify the primitive families to which an SLH-DSA security reduction applies.
An aggregate EUF-CMA theorem additionally needs the seed-aware collection games under
`HardnessAssumptions.TweakableHash`, SM-DT-DSPR and SM-DT-OpenPRE/UD variants, an `H_msg`
interleaved-target-subset-resilience game, explicit reductions from the forger, and checked query
bounds. Primitive packaging alone does not supply those ingredients.

## References

- Bernstein, Hülsing, Kölbl, Niederhagen, Rijneveld, Schwabe, "The SPHINCS+ Signature Framework"
- Hülsing, Rijneveld, and Song, "Mitigating Multi-Target Attacks in Hash-Based Signatures"
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified"
- NIST FIPS 205, §10 (security)
-/

@[expose] public section


open OracleComp OracleSpec ENNReal CollisionResistance

namespace SLHDSA

variable {p : Params} (prims : Primitives p)

/-! ### The SLH-DSA hashes as tweakable hash families / PRFs -/

/-- The chain-step / FORS-leaf hash `F` as a tweakable hash family.  Its tweak is the exact
encoded address hashed by the concrete instantiation. -/
def Primitives.fHash [SampleableType prims.PkSeed] :
    TweakableHash prims.PkSeed prims.AdrsKey prims.Y prims.Y where
  seedGen := $ᵗ prims.PkSeed
  eval := fun pkSeed adrsKey x => prims.Thash pkSeed adrsKey [x]

/-- The Merkle / FORS-tree node hash `H` as a tweakable hash family over encoded addresses and
ordered sibling pairs. -/
def Primitives.hHash [SampleableType prims.PkSeed] :
    TweakableHash prims.PkSeed prims.AdrsKey (prims.Y × prims.Y) prims.Y where
  seedGen := $ᵗ prims.PkSeed
  eval := fun pkSeed adrsKey m => prims.Thash pkSeed adrsKey [m.1, m.2]

/-- The fixed-arity members of SLH-DSA's public `Thash` collection.  Member `arity` accepts
exactly `arity` ordered nodes, while all members share the sampled public seed, canonical encoded
address space, and output type. -/
def Primitives.thashCollection :
    TweakableHashCollection ℕ prims.PkSeed prims.AdrsKey prims.Y where
  Msg arity := Vector prims.Y arity
  eval := fun _ pkSeed adrsKey xs => prims.Thash pkSeed adrsKey xs.toList

/-- The fixed-arity member of SLH-DSA's public `Thash` collection. -/
def Primitives.thashMember [SampleableType prims.PkSeed] (arity : ℕ) :
    TweakableHash prims.PkSeed prims.AdrsKey (Vector prims.Y arity) prims.Y where
  seedGen := $ᵗ prims.PkSeed
  eval := fun pkSeed adrsKey xs => prims.Thash pkSeed adrsKey xs.toList

/-- Evaluating the collection at `arity` is definitionally the same operation as evaluating the
corresponding fixed-arity member. -/
@[simp] theorem Primitives.thashCollection_eval [SampleableType prims.PkSeed] (arity : ℕ) :
    prims.thashCollection.eval arity = (prims.thashMember arity).eval := rfl

/-- The SM-DT-TCR problem for the `arity`-input member of `Thash`, with the whole `Thash`
collection available during target selection. -/
def Primitives.thashTcrProblem [SampleableType prims.PkSeed] (arity numTargets : ℕ) :
    TweakableHash.SM_DT_TCR_Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y arity) prims.Y where
  th := prims.thashMember arity
  thColl := prims.thashCollection
  numTargets := numTargets

/-- The unrestricted-subspace SM-DT-PRE problem for the `arity`-input member of `Thash`, with the
whole `Thash` collection available during target selection. -/
def Primitives.thashPreProblem [SampleableType prims.PkSeed] (arity numTargets : ℕ) :
    TweakableHash.SM_DT_PRE_Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y arity) (Vector prims.Y arity) prims.Y where
  th := prims.thashMember arity
  emb := id
  emb_injective := Function.injective_id
  thColl := prims.thashCollection
  numTargets := numTargets

/-- The source-final-validity SM-DT-DSPR problem for one fixed-arity `Thash` member, with the
whole collection available during target selection. -/
def Primitives.thashDsprProblem [SampleableType prims.PkSeed] (arity numTargets : ℕ) :
    TweakableHash.SM_DT_DSPR_Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y arity) prims.Y where
  th := prims.thashMember arity
  thColl := prims.thashCollection
  numTargets := numTargets

/-! ### Exact `d = 1` assumption instances -/

/-- Source-final-validity SM-DT-DSPR problem for all arity-one FORS secret leaves. -/
def Primitives.d1ForsLeafDsprProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_DSPR_Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y 1) prims.Y :=
  prims.thashDsprProblem 1 p.d1TargetProfile.forsLeaf

/-- Collection SM-DT-TCR problem for every arity-two FORS internal node. -/
def Primitives.d1ForsTreeTcrProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y 2) prims.Y :=
  prims.thashTcrProblem 2 p.d1TargetProfile.forsTree

/-- Collection SM-DT-TCR problem for every arity-`k` FORS-root compression. -/
def Primitives.d1ForsRootsTcrProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y p.k) prims.Y :=
  prims.thashTcrProblem p.k p.d1TargetProfile.forsRoots

/-- Collection SM-DT-TCR problem for the WOTS arity-one hash member. -/
def Primitives.d1WotsChainTcrProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y 1) prims.Y :=
  prims.thashTcrProblem 1 p.d1TargetProfile.wotsTcr

/-- Collection SM-DT-PRE problem for the WOTS arity-one hash member. -/
def Primitives.d1WotsChainPreProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_PRE_Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y 1) (Vector prims.Y 1) prims.Y :=
  prims.thashPreProblem 1 p.d1TargetProfile.wotsPre

/-- Collection SM-DT-TCR problem for every arity-`len` WOTS-public-key compression. -/
def Primitives.d1WotsPkTcrProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y p.len) prims.Y :=
  prims.thashTcrProblem p.len p.d1TargetProfile.wotsPk

/-- Collection SM-DT-TCR problem for every arity-two node of the single XMSS tree. -/
def Primitives.d1XmssTreeTcrProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y 2) prims.Y :=
  prims.thashTcrProblem 2 p.d1TargetProfile.xmssTree

/-- The message randomizer `PRF_msg` as a `PRFScheme` keyed by `SK.prf`; `eval` is
`prims.PRFmsg`. -/
def msgPrfScheme [SampleableType prims.SkPrf] :
    PRFScheme prims.SkPrf (prims.Y × List Byte) prims.Y where
  keygen := $ᵗ prims.SkPrf
  eval := fun skPrf rm => prims.PRFmsg skPrf rm.1 rm.2

/-- Secret-value generation as one PRF keyed by `SK.seed`, with the *actual* public seed and
address both in its domain.  This is the source-faithful SKG family used by the top-level hybrid:
the reduction may sample `PK.seed` exactly once and query this family at that same seed. -/
def skPrfScheme [SampleableType prims.SkSeed] :
    PRFScheme prims.SkSeed (prims.PkSeed × Adrs) prims.Y where
  keygen := $ᵗ prims.SkSeed
  eval := fun skSeed pa => prims.PRF pa.1 skSeed pa.2

/-- Fixed-public-seed view retained for component lemmas whose public seed is already in scope. -/
def skPrfSchemeAtSeed [SampleableType prims.SkSeed] (pkSeed : prims.PkSeed) :
    PRFScheme prims.SkSeed Adrs prims.Y where
  keygen := $ᵗ prims.SkSeed
  eval := fun skSeed adrs => prims.PRF pkSeed skSeed adrs

/-- `H_msg` as the keyed hash family used by the ITSR hop after `PRF_msg` has been replaced by a
random function.  The sampled message key is the randomizer `R`; the input carries the actual
`PK.seed`, `PK.root`, and external message jointly, so the hardness problem preserves their
coupling to key generation instead of silently fixing an unrelated public context.  The hash also
includes the canonical empty-context encoding used by `slhdsaAlg`. -/
def hmsgHashFamily [SampleableType prims.Y] :
    KeyedHashFamily prims.Y (prims.PkSeed × prims.Y × List Byte) (Bytes p.m) where
  keygen := $ᵗ prims.Y
  hash := fun R input =>
    prims.Hmsg R input.1 input.2.1 (emptyContextMessage input.2.2)

/-- One semantic FORS leaf selected by message compression: XMSS leaf, FORS tree, and leaf in
that tree. -/
abbrev HmsgIndex := ℕ × ℕ × ℕ

/-- Canonical `d = 1` semantic-index map for the M-FORS ITSR game. -/
def d1HmsgIndices (p : Params) (digest : Bytes p.m) : List HmsgIndex :=
  let (md, idxLeaf) := splitDigest p digest
  (List.range p.k).map fun i => (idxLeaf, i, forsIdx p md i)

/-- The exact message-compression ITSR problem for SLH-DSA public-key/message inputs.  It uses the
scheme's external-message encoding and maps a digest to exactly the `k` source-game triples
`(idxLeaf, FORS-tree index, selected leaf index)`.  A top-level reduction must assume `p.IsD1`. -/
def hmsgItsrProblem [SampleableType prims.Y] :
    KeyedHash.ITSRProblem prims.Y (prims.PkSeed × prims.Y × List Byte)
      (Bytes p.m) HmsgIndex where
  khf := hmsgHashFamily prims
  indices := d1HmsgIndices p

/-! ### Concrete EUF-CMA endpoint -/

section ConcreteEUF

variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
  [SampleableType prims.PkSeed] [SampleableType prims.Y] [DecidableEq prims.Y]

/-- Adversaries against the canonical explicit-query SLH-DSA scheme. -/
abbrev EufCmaAdversary :=
  SignatureAlg.unforgeableAdv
    (slhdsaAlg (m := OracleComp (unifSpec + publicHashSpec prims.core)) prims.core)

/-- The executable EUF-CMA program before applying a public-hash runtime.  Factoring the program
out makes the concrete endpoint auditable: one deterministic simulation surrounds key generation,
the adversary, every signing query, and final verification. -/
noncomputable def eufCmaProgram (adv : EufCmaAdversary prims) :
    OracleComp (unifSpec + publicHashSpec prims.core) Bool :=
  letI : DecidableEq (List Byte) := Classical.decEq _
  letI : DecidableEq (SignatureCore p prims.core) := Classical.decEq _
  let sigAlg := slhdsaAlg
    (m := OracleComp (unifSpec + publicHashSpec prims.core)) prims.core
  do
    let (pk, sk) ← sigAlg.keygen
    let impl : QueryImpl
        ((unifSpec + publicHashSpec prims.core) +
          (List Byte →ₒ SignatureCore p prims.core))
        (WriterT (QueryLog (List Byte →ₒ SignatureCore p prims.core))
          (OracleComp (unifSpec + publicHashSpec prims.core))) :=
      (HasQuery.toQueryImpl
          (spec := unifSpec + publicHashSpec prims.core)
          (m := OracleComp (unifSpec + publicHashSpec prims.core))).liftTarget
        (WriterT (QueryLog (List Byte →ₒ SignatureCore p prims.core))
          (OracleComp (unifSpec + publicHashSpec prims.core))) +
        sigAlg.signingOracle pk sk
    let simAdv : WriterT (QueryLog (List Byte →ₒ SignatureCore p prims.core))
        (OracleComp (unifSpec + publicHashSpec prims.core))
        (List Byte × SignatureCore p prims.core) := simulateQ impl (adv.main pk)
    let ((msg, sig), log) ← simAdv.run
    let verified ← sigAlg.verify pk msg sig
    return !log.wasQueried msg && verified

/-- Concrete-function EUF-CMA experiment for the supplied primitive bundle. -/
noncomputable def concreteEufCmaExperiment (adv : EufCmaAdversary prims) : SPMF Bool :=
  SignatureAlg.unforgeableExp (PublicHash.concreteRuntime prims) adv

/-- Concrete-function EUF-CMA advantage. -/
noncomputable def concreteEufCmaAdvantage (adv : EufCmaAdversary prims) : ℝ≥0∞ :=
  Pr[= true | concreteEufCmaExperiment prims adv]

/-- Endpoint bridge: the generic `SignatureAlg.unforgeableExp` is exactly one simulation of the
whole EUF-CMA program with `PublicHash.impl prims`.  Thus subsequent THF reductions start from
the deterministic SLH-DSA scheme rather than the repository's separate ROM runtime. -/
theorem concreteEufCmaExperiment_eq_simulate (adv : EufCmaAdversary prims) :
    concreteEufCmaExperiment prims adv =
      (liftM (simulateQ (unifFwdAnswerImpl (PublicHash.impl prims))
        (eufCmaProgram prims adv)) : SPMF Bool) := by
  rfl

end ConcreteEUF

end SLHDSA
