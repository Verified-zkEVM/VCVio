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
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTOpenPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUDC
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

/-- The source-final-validity SM-DT-OpenPRE problem for one fixed-arity `Thash` member and the
exact hidden-input distribution embedded by its reduction. -/
def Primitives.thashOpenPreProblem [SampleableType prims.PkSeed] (arity numTargets : ℕ)
    (inputGen : ProbComp (Vector prims.Y arity)) :
    TweakableHash.SM_DT_OpenPRE_Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y arity) prims.Y where
  th := prims.thashMember arity
  inputGen := inputGen
  thColl := prims.thashCollection
  numTargets := numTargets

/-- The source-final-validity SM-DT-UD-C problem for one fixed-arity `Thash` member, with explicit
real-input and ideal-output distributions and the whole collection available during selection. -/
def Primitives.thashUdProblem [SampleableType prims.PkSeed] (arity numTargets : ℕ)
    (inputGen : ProbComp (Vector prims.Y arity)) (outputGen : ProbComp prims.Y) :
    TweakableHash.SM_DT_UD_Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y arity) prims.Y where
  th := prims.thashMember arity
  inputGen := inputGen
  outputGen := outputGen
  thColl := prims.thashCollection
  numTargets := numTargets

/-! ### Exact `d = 1` assumption instances -/

/-- Source-final-validity SM-DT-DSPR problem for all arity-one FORS secret leaves. -/
def Primitives.d1ForsLeafDsprProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_DSPR_Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y 1) prims.Y :=
  prims.thashDsprProblem 1 p.d1TargetProfile.forsLeaf

/-- Source-final-validity SM-DT-OpenPRE problem for all arity-one FORS secret leaves. -/
def Primitives.d1ForsLeafOpenPreProblem [SampleableType prims.PkSeed]
    [SampleableType prims.Y] :
    TweakableHash.SM_DT_OpenPRE_Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y 1) prims.Y :=
  prims.thashOpenPreProblem 1 p.d1TargetProfile.forsLeaf ($ᵗ Vector prims.Y 1)

/-- The concrete FORS OpenPRE problem satisfies the uniform-input hypothesis required by the
source OpenPRE-to-DSPR/TCR finite-fiber argument. -/
@[simp] theorem Primitives.d1ForsLeafOpenPreProblem_hasUniformInputs
    [SampleableType prims.PkSeed] [SampleableType prims.Y] :
    prims.d1ForsLeafOpenPreProblem.HasUniformInputs := by
  rfl

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

/-- Collection SM-DT-UD-C problem for WOTS chain starts.  The real world hashes a uniformly
sampled arity-one chain value; the ideal world samples a uniform digest directly. -/
def Primitives.d1WotsChainUdProblem [SampleableType prims.PkSeed] [SampleableType prims.Y] :
    TweakableHash.SM_DT_UD_Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y 1) prims.Y :=
  prims.thashUdProblem 1 p.d1TargetProfile.wotsUd ($ᵗ Vector prims.Y 1) ($ᵗ prims.Y)

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

/-! ### Deterministic component-reduction witnesses -/

/-- A distinct secret value that hashes to an honest FORS leaf is an arity-one TCR witness at the
exact leaf address. -/
theorem Primitives.forsLeafCollision_to_tcrWitness [SampleableType prims.PkSeed]
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ) (candidate : prims.Y)
    (hne : forsSkGenCore prims.core sk pk adrs idx ≠ candidate)
    (heq : forsLeaf prims sk pk adrs idx =
      prims.F pk (forsNodeAdrs adrs 0 idx) candidate) :
    let target : Vector prims.Y 1 := #v[forsSkGenCore prims.core sk pk adrs idx]
    let collision : Vector prims.Y 1 := #v[candidate]
    target ≠ collision ∧
      (prims.thashMember 1).eval pk (prims.adrsToKey (forsNodeAdrs adrs 0 idx)) target =
        (prims.thashMember 1).eval pk
          (prims.adrsToKey (forsNodeAdrs adrs 0 idx)) collision := by
  dsimp
  constructor
  · intro hv
    apply hne
    have hl := congrArg Vector.toList hv
    simpa using hl
  · simpa [Primitives.thashMember] using heq

/-- A changed vector of WOTS chain ends that still compresses to the honest WOTS public key is an
arity-`len` TCR witness at the exact `WOTS_PK` address. -/
theorem Primitives.wotsPkBinding_to_tcrWitness [SampleableType prims.PkSeed]
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (sig : WotsSig p prims.core)
    (hpk : wotsPkFromSig prims sig msg pk adrs = wotsPkGen prims sk pk adrs)
    (hne : wotsPkGenTops prims sk pk adrs ≠ wotsPkFromSigTops prims sig msg pk adrs) :
    let target := wotsPkGenTops prims sk pk adrs
    let collision := wotsPkFromSigTops prims sig msg pk adrs
    target ≠ collision ∧
      (prims.thashMember p.len).eval pk (prims.adrsToKey (wotsPkAdrs adrs)) target =
        (prims.thashMember p.len).eval pk (prims.adrsToKey (wotsPkAdrs adrs)) collision := by
  dsimp
  refine ⟨hne, ?_⟩
  simpa [Primitives.thashMember] using hpk.symm

/-- The message-independent honest FORS roots committed by the arity-`k` compression. -/
def Primitives.forsHonestRoots (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) : Vector prims.Y p.k :=
  Vector.ofFn fun i => forsRoot prims sk pk adrs i.val

/-- The roots reconstructed from a candidate FORS signature and digest. -/
def Primitives.forsRecoveredRoots (sig : ForsSigCore p prims.core) (md : List Byte)
    (pk : prims.PkSeed) (adrs : Adrs) : Vector prims.Y p.k :=
  Vector.ofFn fun i =>
    let idx := i.val * 2 ^ p.a + forsIdx p md i.val
    PerfectMerkleTree.climb (forsNodeHash prims pk adrs) idx
      (prims.F pk (forsNodeAdrs adrs 0 idx) (sig[i.val]).1) (sig[i.val]).2

/-- A changed reconstructed FORS-root vector that still compresses to the honest FORS public key
is directly an arity-`k` TCR witness at `forsPkAdrs`. -/
theorem Primitives.forsRootsBinding_to_tcrWitness [SampleableType prims.PkSeed]
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (sig : ForsSigCore p prims.core) (md : List Byte)
    (hpk : forsPkFromSig prims sig md pk adrs = forsPkGen prims sk pk adrs)
    (hne : prims.forsHonestRoots sk pk adrs ≠ prims.forsRecoveredRoots sig md pk adrs) :
    let target := prims.forsHonestRoots sk pk adrs
    let collision := prims.forsRecoveredRoots sig md pk adrs
    target ≠ collision ∧
      (prims.thashMember p.k).eval pk (prims.adrsToKey (forsPkAdrs adrs)) target =
        (prims.thashMember p.k).eval pk (prims.adrsToKey (forsPkAdrs adrs)) collision := by
  dsimp
  refine ⟨hne, ?_⟩
  simpa [Primitives.forsHonestRoots, Primitives.forsRecoveredRoots,
    Primitives.thashMember] using hpk.symm

/-- If one well-formed FORS authentication path reconstructs its honest root from a different
leaf, it yields an arity-two TCR witness at an exact `FORS_TREE` address. -/
theorem Primitives.forsTreeBinding_to_tcrWitness [SampleableType prims.PkSeed]
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (sig : ForsSigCore p prims.core) (md : List Byte) (i : Fin p.k)
    (hlen : (sig[i.val]).2.length = p.a)
    (hroot : (prims.forsRecoveredRoots sig md pk adrs)[i.val] =
      (prims.forsHonestRoots sk pk adrs)[i.val])
    (hne :
      let idx := i.val * 2 ^ p.a + forsIdx p md i.val
      forsLeaf prims sk pk adrs idx ≠
        prims.F pk (forsNodeAdrs adrs 0 idx) (sig[i.val]).1) :
    let idx := i.val * 2 ^ p.a + forsIdx p md i.val
    ∃ (h : ℕ) (c : prims.Y × prims.Y), 0 < h ∧ h ≤ p.a ∧
      let target : Vector prims.Y 2 :=
        #v[PerfectMerkleTree.merkleRoot (forsLeaf prims sk pk adrs)
              (forsNodeHash prims pk adrs) (h - 1) (2 * (idx / 2 ^ h)),
          PerfectMerkleTree.merkleRoot (forsLeaf prims sk pk adrs)
              (forsNodeHash prims pk adrs) (h - 1) (2 * (idx / 2 ^ h) + 1)]
      let collision : Vector prims.Y 2 := #v[c.1, c.2]
      target ≠ collision ∧
        (prims.thashMember 2).eval pk
            (prims.adrsToKey (forsNodeAdrs adrs h (idx / 2 ^ h))) target =
          (prims.thashMember 2).eval pk
            (prims.adrsToKey (forsNodeAdrs adrs h (idx / 2 ^ h))) collision := by
  dsimp only
  let idx := i.val * 2 ^ p.a + forsIdx p md i.val
  have ht : idx / 2 ^ p.a = i.val := by
    dsimp [idx]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ p.a),
      Nat.div_eq_of_lt (forsIdx_lt p md i.val), Nat.zero_add]
  have hroot' :
      PerfectMerkleTree.climb (forsNodeHash prims pk adrs) idx
          (prims.F pk (forsNodeAdrs adrs 0 idx) (sig[i.val]).1) (sig[i.val]).2 =
        PerfectMerkleTree.merkleRoot (forsLeaf prims sk pk adrs)
          (forsNodeHash prims pk adrs) p.a (idx / 2 ^ p.a) := by
    rw [ht]
    simpa [idx, Primitives.forsRecoveredRoots, Primitives.forsHonestRoots] using hroot
  obtain ⟨h, c, hpos, hle, hnePairs, heq⟩ :=
    PerfectMerkleTree.climb_binding (forsLeaf prims sk pk adrs)
      (forsNodeHash prims pk adrs) p.a idx
      (prims.F pk (forsNodeAdrs adrs 0 idx) (sig[i.val]).1) (sig[i.val]).2
      hlen hroot' hne
  refine ⟨h, c, hpos, hle, ?_⟩
  dsimp
  constructor
  · intro hv
    apply hnePairs
    have hl := congrArg Vector.toList hv
    have hpairs :
        PerfectMerkleTree.merkleRoot (forsLeaf prims sk pk adrs)
            (forsNodeHash prims pk adrs) (h - 1) (2 * (idx / 2 ^ h)) = c.1 ∧
          PerfectMerkleTree.merkleRoot (forsLeaf prims sk pk adrs)
            (forsNodeHash prims pk adrs) (h - 1) (2 * (idx / 2 ^ h) + 1) = c.2 := by
      simpa using hl
    exact Prod.ext hpairs.1 hpairs.2
  · simpa [Primitives.thashMember] using heq

/-- Translate the existing oriented XMSS binding theorem into the exact message/tweak shape of
the arity-two TCR game.  The first vector is an honest internal-node target and the second is the
distinct adversarial child pair recovered from the forged authentication path. -/
theorem Primitives.xmssBinding_to_tcrWitness [SampleableType prims.PkSeed]
    (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ) (hidx : idx < 2 ^ p.hp)
    (sig : XmssSig p prims) (hlen : sig.2.length = p.hp)
    (hroot : xmssPkFromSig prims idx sig msg pk adrs = xmssRoot prims sk pk adrs)
    (hne : xmssLeaf prims sk pk adrs idx
      ≠ wotsPkFromSig prims sig.1 msg pk (wotsLeafAdrs adrs idx)) :
    ∃ (h : ℕ) (c : prims.Y × prims.Y), 0 < h ∧ h ≤ p.hp ∧
      let target : Vector prims.Y 2 :=
        #v[xmssNode prims sk pk adrs (h - 1) (2 * (idx / 2 ^ h)),
          xmssNode prims sk pk adrs (h - 1) (2 * (idx / 2 ^ h) + 1)]
      let collision : Vector prims.Y 2 := #v[c.1, c.2]
      target ≠ collision ∧
        (prims.thashMember 2).eval pk
            (prims.adrsToKey (xmssNodeAdrs adrs h (idx / 2 ^ h))) target =
          (prims.thashMember 2).eval pk
            (prims.adrsToKey (xmssNodeAdrs adrs h (idx / 2 ^ h))) collision := by
  obtain ⟨h, c, hpos, hle, hnePairs, heq⟩ :=
    xmssPkFromSig_binding prims msg sk pk adrs idx hidx sig hlen hroot hne
  refine ⟨h, c, hpos, hle, ?_⟩
  dsimp
  constructor
  · intro hv
    apply hnePairs
    have hl := congrArg Vector.toList hv
    have hpairs :
        xmssNode prims sk pk adrs (h - 1) (2 * (idx / 2 ^ h)) = c.1 ∧
          xmssNode prims sk pk adrs (h - 1) (2 * (idx / 2 ^ h) + 1) = c.2 := by
      simpa using hl
    exact Prod.ext hpairs.1 hpairs.2
  · exact heq

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

@[simp] theorem msgPrfScheme_uniformKey [SampleableType prims.SkPrf] :
    PRFScheme.UniformKey (msgPrfScheme prims) := rfl

@[simp] theorem skPrfScheme_uniformKey [SampleableType prims.SkSeed] :
    PRFScheme.UniformKey (skPrfScheme prims) := rfl

@[simp] theorem skPrfSchemeAtSeed_uniformKey [SampleableType prims.SkSeed]
    (pkSeed : prims.PkSeed) :
    PRFScheme.UniformKey (skPrfSchemeAtSeed prims pkSeed) := rfl

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

/-! ### Concrete SUF-CMA endpoint

This endpoint is deliberately separate from the EUF reduction above.  Pair freshness admits a
new valid signature on an already signed message, so no EUF theorem may be reused without an
additional same-message binding/re-randomization reduction. -/

section ConcreteSUF

variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
  [SampleableType prims.PkSeed] [SampleableType prims.Y] [DecidableEq prims.Y]

/-- Strong-unforgeability adversaries against the canonical explicit-query SLH-DSA scheme. -/
abbrev StrongEufCmaAdversary :=
  SignatureAlg.strongUnforgeableAdv
    (slhdsaAlg (m := OracleComp (unifSpec + publicHashSpec prims.core)) prims.core)

/-- The executable SUF-CMA program before applying a public-hash runtime.  The final freshness
test is on the exact returned `(message, signature)` pair rather than on the message alone. -/
noncomputable def strongEufCmaProgram (adv : StrongEufCmaAdversary prims) :
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
    return !SignatureAlg.signingLogContains log msg sig && verified

/-- Concrete-function SUF-CMA experiment for the supplied primitive bundle. -/
noncomputable def concreteStrongEufCmaExperiment (adv : StrongEufCmaAdversary prims) : SPMF Bool :=
  SignatureAlg.strongUnforgeableExp (PublicHash.concreteRuntime prims) adv

/-- Concrete-function SUF-CMA advantage. -/
noncomputable def concreteStrongEufCmaAdvantage (adv : StrongEufCmaAdversary prims) : ℝ≥0∞ :=
  Pr[= true | concreteStrongEufCmaExperiment prims adv]

/-- Concrete probability of producing a new valid signature for a message already submitted to
the signing oracle.  This is the exact extra term needed to upgrade the EUF-CMA endpoint to
SUF-CMA; it is not silently identified with any of the EUF hash assumptions. -/
noncomputable def concreteSameMessageStrongAdvantage
    (adv : StrongEufCmaAdversary prims) : ℝ≥0∞ :=
  adv.sameMessageAdvantage (PublicHash.concreteRuntime prims)

/-- The concrete SLH-DSA SUF advantage is bounded by the ordinary EUF advantage of the same
adversary plus its same-message, new-signature probability.  A full SUF theorem therefore needs
one additional scheme-specific reduction for the second term. -/
theorem concreteStrongEufCmaAdvantage_le_euf_add_sameMessage
    (adv : StrongEufCmaAdversary prims) :
    concreteStrongEufCmaAdvantage prims adv ≤
      concreteEufCmaAdvantage prims adv.toUnforgeableAdv +
        concreteSameMessageStrongAdvantage prims adv := by
  exact adv.advantage_le_euf_add_sameMessage (PublicHash.concreteRuntime prims)
    (PublicHash.concreteRuntime_evalSPMF_bind_pure prims)

/-- Endpoint bridge for SUF-CMA: as for EUF-CMA, one deterministic public-hash simulation
surrounds key generation, all signing queries, and final verification. -/
theorem concreteStrongEufCmaExperiment_eq_simulate (adv : StrongEufCmaAdversary prims) :
    concreteStrongEufCmaExperiment prims adv =
      (liftM (simulateQ (unifFwdAnswerImpl (PublicHash.impl prims))
        (strongEufCmaProgram prims adv)) : SPMF Bool) := by
  rfl

end ConcreteSUF

end SLHDSA
