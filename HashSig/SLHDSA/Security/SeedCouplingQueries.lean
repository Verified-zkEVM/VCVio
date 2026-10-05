/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.SeedCoupling
public import HashSig.SLHDSA.Concrete.FIPS
public import HashSig.SLHDSA.Concrete.Instance
import HashSig.SLHDSA.Security.AddressKeys
import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.QueryBound

/-!
# Derivable public queries of the secret-free run of SLH-DSA

In the secret-free run of SLH-DSA (`HashSig.SLHDSA.Security.SeedCoupling`) every secret value
and every message randomizer is a derivation query, answered under secret seeds `s` by the
public query `(secretEncoding core e pkSeed).enc s x`. Every such public query is a
*derivable public query* (`IsDerivablePublicQuery core pkSeed`, `isDerivablePublicQuery_enc`): a
tweakable-hash query at `pkSeed` and the oracle key of a secret-key address, or a `PRF_msg` query.
This module bounds the derivable public queries of the transcript experiment of `deriveScheme`
against a lifted forger by the forger's hash budget.

* `CorePrimitives.KeySeparated core` says that no address of type at most `4` shares its oracle key
  with a secret-key address. The SHAKE bundles (`Concrete.keySeparated_shakePrimitives`) and the
  SLH-DSA-SHA2-128-24 compatibility bundle (`Concrete.keySeparated_shaPrimitives`) satisfy it for
  every address. The FIPS SHA-2 bundles `Concrete.sha2Primitives` send every address outside the
  checked `ADRSc` domain to the all-zero key, the key of an address of type `0`, so they do not.
* Under key separation the honest programs make no derivable public query: each tweakable-hash
  query of WOTS+, XMSS, the hypertree and FORS is at an address of type at most `4`, `H_msg` is
  never derivable, and the secret values and the randomizer are derivation queries. One lemma
  per program layer states this as a budget of `0`, from the WOTS+ chain
  (`isQueryBoundP_chainWith`) to the scheme (`isQueryBoundP_deriveScheme_keygen`,
  `isQueryBoundP_deriveScheme_sign`, `isQueryBoundP_deriveScheme_verify`).
* `isQueryBoundP_unforgeableTranscriptExperiment_deriveAdversary`: a forger with hash budget `qh`
  (`UnforgeableAdversary.RomQueryBound`) makes the transcript experiment of `deriveScheme`
  against `deriveAdversary core adv pkSeed` issue at most `qh` derivable public queries.

## Labels

*Key separation*: `CorePrimitives.KeySeparated`, `Concrete.keySeparated_shakePrimitives`,
`Concrete.keySeparated_shaPrimitives`.

*Derivable public queries*: `IsDerivablePublicQuery`, `isDerivablePublicQuery_enc`.

*Base queries*: `isQueryBoundP_publicHash_tl`, `isQueryBoundP_publicHash_f`,
`isQueryBoundP_publicHash_h`, `isQueryBoundP_publicHash_hmsg`, `isQueryBoundP_liftM_probComp`,
`isQueryBoundP_deriveSecret`.

*WOTS+*: `isQueryBoundP_chainWith`, `isQueryBoundP_wotsPkGenTopsWithSecret`,
`isQueryBoundP_wotsPkGenWithSecret`, `isQueryBoundP_wotsSignWithSecret`,
`isQueryBoundP_wotsPkFromSigWith`.

*XMSS*: `isQueryBoundP_xmssNodeWithSecret`, `isQueryBoundP_xmssSignWithSecret`,
`isQueryBoundP_xmssPkFromSigWith`.

*The hypertree*: `isQueryBoundP_signFromPositionWithSecret`, `isQueryBoundP_signWithSecretM`,
`isQueryBoundP_rootWithSecretM`, `isQueryBoundP_recoverFromPositionWith`,
`isQueryBoundP_hypertreeVerifyM`.

*FORS*: `isQueryBoundP_forsLeafWithSecret`, `isQueryBoundP_forsSignWithSecretM`,
`isQueryBoundP_forsPkFromSigM`.

*The internal scheme*: `isQueryBoundP_keygenInternalWithSecretM`,
`isQueryBoundP_signInternalWithSecretRandomizerM`, `isQueryBoundP_verifyInternalM`.

*The secret-free scheme and its experiment*: `isQueryBoundP_deriveScheme_keygen`,
`isQueryBoundP_deriveScheme_sign`, `isQueryBoundP_deriveScheme_verify`,
`isQueryBoundP_unforgeableTranscriptExperiment_deriveAdversary`.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA

/-! ## Key separation -/

/-- The oracle key of a secret-key address is the key of no address of type at most `4`, the
types of the `WOTS_HASH`, `WOTS_PK`, `TREE`, `FORS_TREE` and `FORS_ROOTS` addresses at which
SLH-DSA evaluates the tweakable hash. -/
@[expose] def CorePrimitives.KeySeparated {p : Params} (core : CorePrimitives p) : Prop :=
  ∀ a b : Adrs, a.IsSecretKey → b.type ≤ 4 → core.adrsToKey a ≠ core.adrsToKey b

/-- Equal big-endian encodings of one width encode equal values below the width's bound. -/
private theorem eq_of_toBytesBE_eq {x y w : ℕ} (hx : x < 256 ^ w) (hy : y < 256 ^ w)
    (h : Adrs.toBytesBE x w = Adrs.toBytesBE y w) : x = y := by
  have h' := congrArg toInt h
  simp only [Adrs.toBytesBE] at h'
  rwa [toInt_toByte _ _ hx, toInt_toByte _ _ hy] at h'

/-- A secret-key address has type `5` or `6`. -/
private theorem Adrs.IsSecretKey.type_eq {a : Adrs} (ha : a.IsSecretKey) :
    a.type = 5 ∨ a.type = 6 := ha

namespace Concrete

/-- The SHAKE bundles are key-separated: their oracle key is the full 32-byte address, whose type
block separates the secret-key types from the types at most `4`. -/
theorem keySeparated_shakePrimitives (p : Params) : (shakePrimitives p).core.KeySeparated := by
  intro a b ha hb h
  have hbytes : a.toBytes = b.toBytes := by
    have h' := congrArg Vector.toList h
    simpa only [Primitives.core, shakePrimitives, Adrs.toVector, Vector.toList_mk,
      List.toList_toArray] using h'
  have := eq_of_toBytesBE_eq (w := 4) (by rcases ha.type_eq with h | h <;> rw [h] <;> norm_num)
    (by omega) (Security.toBytes_blocks hbytes).2.2.1
  rcases ha.type_eq with h | h <;> omega

/-- The SLH-DSA-SHA2-128-24 compatibility bundle is key-separated: its oracle key is the
compressed address `ADRSc`, whose one-byte type block separates the secret-key types from the
types at most `4`. -/
theorem keySeparated_shaPrimitives : shaPrimitives.core.KeySeparated := by
  intro a b ha hb h
  have hbytes : a.compressSha2 = b.compressSha2 := by
    rw [← shaAdrsKey_toList, ← shaAdrsKey_toList]
    exact congrArg Vector.toList h
  have := eq_of_toBytesBE_eq (w := 1) (by rcases ha.type_eq with h | h <;> rw [h] <;> norm_num)
    (by omega) (Security.compressSha2_blocks hbytes).2.2.1
  rcases ha.type_eq with h | h <;> omega

end Concrete

namespace Security

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-! ## Derivable public queries -/

/-- A public query of `deriveSpec core` at which `secretEncoding core e pkSeed` can encode a
derivation: a tweakable-hash query at public seed `pkSeed` and the oracle key of a secret-key
address, or a `PRF_msg` query. -/
@[expose] def IsDerivablePublicQuery (pkSeed : core.PkSeed) : (deriveSpec core).Domain → Prop
  | .inl (.inr (.inl (.thash s k _))) =>
      s = pkSeed ∧ ∃ a : Adrs, a.IsSecretKey ∧ core.adrsToKey a = k
  | .inl (.inr (.inr _)) => True
  | _ => False

open Classical in
/-- Membership of a key in the keys of secret-key addresses is decided classically. -/
noncomputable instance instDecidablePredIsDerivablePublicQuery (pkSeed : core.PkSeed) :
    DecidablePred (IsDerivablePublicQuery core pkSeed) :=
  fun _ => Classical.dec _

/-- Every encoding of a derivation at public seed `pkSeed` is a derivable public query. -/
theorem isDerivablePublicQuery_enc (e : core.SkSeed ≃ core.Y) (pkSeed : core.PkSeed)
    (s : core.SkSeed × core.SkPrf) (x : DeriveQuery core) :
    IsDerivablePublicQuery core pkSeed (.inl (.inr ((secretEncoding core e pkSeed).enc s x))) := by
  rcases x with k | ⟨o, msg⟩
  · exact ⟨rfl, k.2⟩
  · trivial

/-! ## Budget-zero combinators -/

section Combinators

variable {ι : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p] {α β Y : Type}

/-- Two programs that make no `p`-query compose to one that makes none. -/
private theorem isQueryBoundP_bind_zero {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    (h : IsQueryBoundP oa p 0) (h' : ∀ x, IsQueryBoundP (ob x) p 0) :
    IsQueryBoundP (oa >>= ob) p 0 :=
  isQueryBoundP_bind h fun x _ => h' x

/-- A vector of programs that make no `p`-query makes none. -/
private theorem isQueryBoundP_ofFnM_zero {n : ℕ} (f : Fin n → OracleComp spec α)
    (h : ∀ i, IsQueryBoundP (f i) p 0) : IsQueryBoundP (Vector.ofFnM f) p 0 := by
  induction n with
  | zero =>
      rw [Vector.ofFnM_zero]
      exact isQueryBoundP_pure _ _ _
  | succ n ih =>
      rw [Vector.ofFnM_succ]
      exact isQueryBoundP_bind_zero (ih _ fun i => h i.castSucc) fun _ =>
        isQueryBoundP_bind_zero (h _) fun _ => isQueryBoundP_pure _ _ _

/-- A Merkle root makes no `p`-query when its leaf and node callbacks make none. -/
private theorem isQueryBoundP_merkleRootM_zero (leaf : ℕ → OracleComp spec Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y) (z t : ℕ)
    (hleaf : ∀ i, IsQueryBoundP (leaf i) p 0)
    (hnode : ∀ h i l r, IsQueryBoundP (nodeHash h i l r) p 0) :
    IsQueryBoundP (PerfectMerkleTree.merkleRootM leaf nodeHash z t) p 0 :=
  PerfectMerkleTree.merkleRootM_pred_of_subtree (fun oa => IsQueryBoundP oa p 0)
    (fun _ _ h h' => isQueryBoundP_bind_zero h h') leaf nodeHash z t (fun i _ => hleaf i)
    (fun h i _ _ _ l r => hnode h i l r)

/-- An authentication path makes no `p`-query when its leaf and node callbacks make none. -/
private theorem isQueryBoundP_intrinsicAuthPathM_zero (leaf : ℕ → OracleComp spec Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y) (idx z : ℕ)
    (hleaf : ∀ i, IsQueryBoundP (leaf i) p 0)
    (hnode : ∀ h i l r, IsQueryBoundP (nodeHash h i l r) p 0) :
    IsQueryBoundP (PerfectMerkleTree.intrinsicAuthPathM leaf nodeHash idx z) p 0 :=
  PerfectMerkleTree.intrinsicAuthPathM_pred_of_tree (fun oa => IsQueryBoundP oa p 0)
    (fun x => isQueryBoundP_pure _ x 0) (fun _ _ h h' => isQueryBoundP_bind_zero h h') leaf
    nodeHash idx z (fun i _ => hleaf i) (fun h i _ _ _ l r => hnode h i l r)

/-- A root recovery makes no `p`-query when its node callback makes none. -/
private theorem isQueryBoundP_climbM_zero (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)
    (idx : ℕ) (node : Y) (auth : List Y)
    (hnode : ∀ h i l r, IsQueryBoundP (nodeHash h i l r) p 0) :
    IsQueryBoundP (PerfectMerkleTree.climbM nodeHash idx node auth) p 0 :=
  PerfectMerkleTree.climbM_pred_of_ancestors (fun oa => IsQueryBoundP oa p 0)
    (fun x => isQueryBoundP_pure _ x 0) (fun _ _ h h' => isQueryBoundP_bind_zero h h') nodeHash
    idx node auth (fun h _ _ l r => hnode h _ l r)

end Combinators

/-! ## The queries of the honest programs -/

section Base

variable {core} (pkSeed : core.PkSeed)

/-- An `H_msg` query is not derivable. -/
theorem isQueryBoundP_publicHash_hmsg (r : core.Y) (s : core.PkSeed) (pkRoot : core.Y)
    (msg : List Byte) :
    IsQueryBoundP (PublicHash.hmsg core r s pkRoot msg :
      OracleComp (deriveSpec core) (Bytes vp.params.m)) (IsDerivablePublicQuery core pkSeed) 0 := by
  change IsQueryBoundP (liftM ((deriveSpec core).query
    (.inl (.inr (.inl (.hmsg r s pkRoot msg))))) : OracleComp (deriveSpec core) _) _ 0
  rw [isQueryBoundP_query_iff]
  exact False.elim

/-- Uniform sampling makes no derivable public query. -/
theorem isQueryBoundP_liftM_probComp {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftM oa : OracleComp (deriveSpec core) α)
      (IsDerivablePublicQuery core pkSeed) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp only [liftM_pure, isQueryBoundP_pure]
  | query_bind t k ih =>
      simp only [liftM_bind]
      refine isQueryBoundP_bind_zero ?_ ih
      change IsQueryBoundP (liftM ((deriveSpec core).query (.inl (.inl t))) :
        OracleComp (deriveSpec core) _) _ 0
      rw [isQueryBoundP_query_iff]
      exact False.elim

/-- The derivation-backed secret provider makes no derivable public query: at a secret-key
address it makes a derivation query, and elsewhere it samples uniformly. -/
theorem isQueryBoundP_deriveSecret [SampleableType core.Y] (a : Adrs) :
    IsQueryBoundP (deriveSecret core a) (IsDerivablePublicQuery core pkSeed) 0 := by
  unfold deriveSecret
  split
  · rename_i h
    change IsQueryBoundP (liftM ((deriveSpec core).query
      (.inr (.inl ⟨core.adrsToKey a, a, h, rfl⟩))) : OracleComp (deriveSpec core) core.Y) _ 0
    rw [isQueryBoundP_query_iff]
    exact False.elim
  · exact isQueryBoundP_liftM_probComp pkSeed _

end Base

section Honest

variable {core} (hsep : core.KeySeparated) (pkSeed : core.PkSeed)
include hsep

/-- A tweakable-hash query at an address of type at most `4` is not derivable. -/
theorem isQueryBoundP_publicHash_tl (s : core.PkSeed) {a : Adrs} (ha : a.type ≤ 4)
    (xs : List core.Y) :
    IsQueryBoundP (PublicHash.tl core s a xs : OracleComp (deriveSpec core) core.Y)
      (IsDerivablePublicQuery core pkSeed) 0 := by
  change IsQueryBoundP (liftM ((deriveSpec core).query
    (.inl (.inr (.inl (.thash s (core.adrsToKey a) xs))))) : OracleComp (deriveSpec core) _) _ 0
  rw [isQueryBoundP_query_iff]
  rintro ⟨-, b, hb, hk⟩
  exact (hsep b a hb ha hk).elim

/-- An `F` query at an address of type at most `4` is not derivable. -/
theorem isQueryBoundP_publicHash_f (s : core.PkSeed) {a : Adrs} (ha : a.type ≤ 4) (x : core.Y) :
    IsQueryBoundP (PublicHash.f core s a x : OracleComp (deriveSpec core) core.Y)
      (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_publicHash_tl hsep pkSeed s ha [x]

/-- An `H` query at an address of type at most `4` is not derivable. -/
theorem isQueryBoundP_publicHash_h (s : core.PkSeed) {a : Adrs} (ha : a.type ≤ 4)
    (l r : core.Y) :
    IsQueryBoundP (PublicHash.h core s a l r : OracleComp (deriveSpec core) core.Y)
      (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_publicHash_tl hsep pkSeed s ha [l, r]

variable (s : core.PkSeed)

/-! ### WOTS+ -/

/-- A WOTS+ chain at an address of type at most `4` makes no derivable public query. -/
theorem isQueryBoundP_chainWith {adrs : Adrs} (hadrs : adrs.type ≤ 4) (x : core.Y) (i : ℕ) :
    ∀ steps, IsQueryBoundP (chainWith (PublicHash.f core s) adrs x i steps :
      OracleComp (deriveSpec core) core.Y) (IsDerivablePublicQuery core pkSeed) 0
  | 0 => isQueryBoundP_pure _ _ _
  | steps + 1 => isQueryBoundP_bind_zero (isQueryBoundP_chainWith hadrs x i steps) fun y =>
      isQueryBoundP_publicHash_f hsep pkSeed s (a := adrs.setHashAddress (i + steps)) hadrs y

/-- The WOTS+ chain ends over derivation-backed secrets make no derivable public query. -/
theorem isQueryBoundP_wotsPkGenTopsWithSecret [SampleableType core.Y] (adrs : Adrs) :
    IsQueryBoundP (wotsPkGenTopsWithSecret core (PublicHash.f core s) (deriveSecret core) adrs :
      OracleComp (deriveSpec core) _) (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_ofFnM_zero _ fun _ =>
    isQueryBoundP_bind_zero (isQueryBoundP_deriveSecret pkSeed _) fun x =>
      isQueryBoundP_chainWith hsep pkSeed s (Nat.zero_le 4) x 0 _

/-- The WOTS+ public key over derivation-backed secrets makes no derivable public query. -/
theorem isQueryBoundP_wotsPkGenWithSecret [SampleableType core.Y] (adrs : Adrs) :
    IsQueryBoundP (wotsPkGenWithSecret core (PublicHash.f core s) (PublicHash.tl core s)
      (deriveSecret core) adrs : OracleComp (deriveSpec core) core.Y)
      (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_bind_zero (isQueryBoundP_wotsPkGenTopsWithSecret hsep pkSeed s adrs) fun _ =>
    isQueryBoundP_publicHash_tl hsep pkSeed s (show 1 ≤ 4 by decide) _

/-- WOTS+ signing over derivation-backed secrets makes no derivable public query. -/
theorem isQueryBoundP_wotsSignWithSecret [SampleableType core.Y] (msg : core.Y) (adrs : Adrs) :
    IsQueryBoundP (wotsSignWithSecret core (PublicHash.f core s) (deriveSecret core) msg adrs :
      OracleComp (deriveSpec core) _) (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_ofFnM_zero _ fun _ =>
    isQueryBoundP_bind_zero (isQueryBoundP_deriveSecret pkSeed _) fun x =>
      isQueryBoundP_chainWith hsep pkSeed s (Nat.zero_le 4) x 0 _

/-- WOTS+ public-key recovery makes no derivable public query. -/
theorem isQueryBoundP_wotsPkFromSigWith (sig : WotsSig vp.params core) (msg : core.Y)
    (adrs : Adrs) :
    IsQueryBoundP (wotsPkFromSigWith core (PublicHash.f core s) (PublicHash.tl core s) sig msg
      adrs : OracleComp (deriveSpec core) core.Y) (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_bind_zero
    (isQueryBoundP_ofFnM_zero _ fun _ =>
      isQueryBoundP_chainWith hsep pkSeed s (Nat.zero_le 4) _ _ _) fun _ =>
    isQueryBoundP_publicHash_tl hsep pkSeed s (show 1 ≤ 4 by decide) _

/-! ### XMSS -/

/-- An XMSS subtree root over derivation-backed secrets makes no derivable public query. -/
theorem isQueryBoundP_xmssNodeWithSecret [SampleableType core.Y] (adrs : Adrs) (z t : ℕ) :
    IsQueryBoundP (xmssNodeWithSecret core (PublicHash.f core s) (PublicHash.tl core s)
      (PublicHash.h core s) (deriveSecret core) adrs z t : OracleComp (deriveSpec core) core.Y)
      (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_merkleRootM_zero _ _ z t
    (fun _ => isQueryBoundP_wotsPkGenWithSecret hsep pkSeed s _)
    (fun _ _ l r => isQueryBoundP_publicHash_h hsep pkSeed s (show 2 ≤ 4 by decide) l r)

/-- XMSS signing over derivation-backed secrets makes no derivable public query. -/
theorem isQueryBoundP_xmssSignWithSecret [SampleableType core.Y] (msg : core.Y) (adrs : Adrs)
    (idx : ℕ) :
    IsQueryBoundP (xmssSignWithSecret core (PublicHash.f core s) (PublicHash.tl core s)
      (PublicHash.h core s) (deriveSecret core) msg adrs idx :
        OracleComp (deriveSpec core) (XmssSig vp.params core))
      (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_bind_zero
    (isQueryBoundP_intrinsicAuthPathM_zero _ _ idx _
      (fun _ => isQueryBoundP_wotsPkGenWithSecret hsep pkSeed s _)
      (fun _ _ l r => isQueryBoundP_publicHash_h hsep pkSeed s (show 2 ≤ 4 by decide) l r))
    fun _ => isQueryBoundP_bind_zero (isQueryBoundP_wotsSignWithSecret hsep pkSeed s msg _)
      fun _ => isQueryBoundP_pure _ _ _

/-- XMSS root recovery makes no derivable public query. -/
theorem isQueryBoundP_xmssPkFromSigWith (idx : ℕ) (sig : XmssSig vp.params core) (msg : core.Y)
    (adrs : Adrs) :
    IsQueryBoundP (xmssPkFromSigWith core (PublicHash.f core s) (PublicHash.tl core s)
      (PublicHash.h core s) idx sig msg adrs : OracleComp (deriveSpec core) core.Y)
      (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_bind_zero (isQueryBoundP_wotsPkFromSigWith hsep pkSeed s sig.wots msg _)
    fun leaf => isQueryBoundP_climbM_zero _ idx leaf _
      (fun _ _ l r => isQueryBoundP_publicHash_h hsep pkSeed s (show 2 ≤ 4 by decide) l r)

/-! ### The hypertree -/

/-- Hypertree signing from a layer position over derivation-backed secrets makes no derivable
public query. -/
theorem isQueryBoundP_signFromPositionWithSecret [SampleableType core.Y] (recoverFinal : Bool)
    (pos : LayerPosition vp) :
    ∀ (layers : ℕ) (h : pos.layer.val + layers = vp.params.d) (msg : core.Y),
      IsQueryBoundP (GeneralHypertree.signFromPositionWithSecret core (PublicHash.f core s)
        (PublicHash.tl core s) (PublicHash.h core s) (deriveSecret core) recoverFinal pos
          layers h msg : OracleComp (deriveSpec core) _) (IsDerivablePublicQuery core pkSeed) 0
  | 0, _, _ => isQueryBoundP_pure _ _ _
  | 1, _, msg => by
      rw [GeneralHypertree.signFromPositionWithSecret]
      refine isQueryBoundP_bind_zero (isQueryBoundP_xmssSignWithSecret hsep pkSeed s msg _ _)
        fun sig => ?_
      cases recoverFinal
      · exact isQueryBoundP_pure _ _ _
      · exact isQueryBoundP_bind_zero (isQueryBoundP_xmssPkFromSigWith hsep pkSeed s _ sig msg _)
          fun _ => isQueryBoundP_pure _ _ _
  | layers + 2, hremaining, msg => by
      rw [GeneralHypertree.signFromPositionWithSecret]
      exact isQueryBoundP_bind_zero (isQueryBoundP_xmssSignWithSecret hsep pkSeed s msg _ _)
        fun sig => isQueryBoundP_bind_zero
          (isQueryBoundP_xmssPkFromSigWith hsep pkSeed s _ sig msg _) fun root =>
            isQueryBoundP_bind_zero
              (isQueryBoundP_signFromPositionWithSecret false _ (layers + 1) _ root)
              fun _ => isQueryBoundP_pure _ _ _

/-- Hypertree signing over derivation-backed secrets makes no derivable public query. -/
theorem isQueryBoundP_signWithSecretM [SampleableType core.Y] (msg : core.Y)
    (parts : DigestParts vp.params) :
    IsQueryBoundP (GeneralHypertree.signWithSecretM core (deriveSecret core) msg s parts :
      OracleComp (deriveSpec core) _) (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_signFromPositionWithSecret hsep pkSeed s _ _ _ _ msg

/-- The top-layer hypertree root over derivation-backed secrets makes no derivable public
query. -/
theorem isQueryBoundP_rootWithSecretM [SampleableType core.Y] :
    IsQueryBoundP (GeneralHypertree.rootWithSecretM core (deriveSecret core) s :
      OracleComp (deriveSpec core) core.Y) (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_xmssNodeWithSecret hsep pkSeed s _ _ _

/-- Hypertree root recovery from a layer position makes no derivable public query. -/
theorem isQueryBoundP_recoverFromPositionWith (pos : LayerPosition vp) :
    ∀ (layers : ℕ) (h : pos.layer.val + layers = vp.params.d) (msg : core.Y)
      (sigs : Vector (XmssSig vp.params core) layers),
      IsQueryBoundP (GeneralHypertree.recoverFromPositionWith vp core (PublicHash.f core s)
        (PublicHash.tl core s) (PublicHash.h core s) s pos layers h msg sigs :
          OracleComp (deriveSpec core) core.Y) (IsDerivablePublicQuery core pkSeed) 0
  | 0, _, _, _ => isQueryBoundP_pure _ _ _
  | 1, _, msg, sigs => isQueryBoundP_xmssPkFromSigWith hsep pkSeed s _ sigs.head msg _
  | layers + 2, _, msg, sigs => by
      rw [GeneralHypertree.recoverFromPositionWith]
      exact isQueryBoundP_bind_zero
        (isQueryBoundP_xmssPkFromSigWith hsep pkSeed s _ sigs.head msg _) fun root =>
          isQueryBoundP_recoverFromPositionWith _ (layers + 1) _ root sigs.tail

/-- Hypertree verification makes no derivable public query. -/
theorem isQueryBoundP_hypertreeVerifyM [DecidableEq core.Y] (msg : core.Y)
    (sig : GeneralHypertree.Signature vp core) (parts : DigestParts vp.params)
    (pkRoot : core.Y) :
    IsQueryBoundP (GeneralHypertree.verifyM vp core msg sig s parts pkRoot :
      OracleComp (deriveSpec core) Bool) (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_bind_zero (isQueryBoundP_recoverFromPositionWith hsep pkSeed s _ _ _ msg sig)
    fun _ => isQueryBoundP_pure _ _ _

/-! ### FORS -/

/-- A FORS leaf over derivation-backed secrets makes no derivable public query. -/
theorem isQueryBoundP_forsLeafWithSecret [SampleableType core.Y] (adrs : Adrs) (t : ℕ) :
    IsQueryBoundP (forsLeafWithSecret core (PublicHash.f core s) (deriveSecret core) adrs t :
      OracleComp (deriveSpec core) core.Y) (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_bind_zero (isQueryBoundP_deriveSecret pkSeed _) fun x =>
    isQueryBoundP_publicHash_f hsep pkSeed s (show 3 ≤ 4 by decide) x

/-- FORS signing over derivation-backed secrets makes no derivable public query. -/
theorem isQueryBoundP_forsSignWithSecretM [SampleableType core.Y] (md : List Byte) (adrs : Adrs) :
    IsQueryBoundP (forsSignWithSecretM core (deriveSecret core) md s adrs :
      OracleComp (deriveSpec core) _) (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_ofFnM_zero _ fun _ =>
    isQueryBoundP_bind_zero
      (isQueryBoundP_intrinsicAuthPathM_zero _ _ _ _
        (fun _ => isQueryBoundP_forsLeafWithSecret hsep pkSeed s _ _)
        (fun _ _ l r => isQueryBoundP_publicHash_h hsep pkSeed s (show 3 ≤ 4 by decide) l r))
      fun _ => isQueryBoundP_bind_zero (isQueryBoundP_deriveSecret pkSeed _) fun _ =>
        isQueryBoundP_pure _ _ _

/-- FORS public-key recovery makes no derivable public query. -/
theorem isQueryBoundP_forsPkFromSigM (sig : ForsSigCore vp.params core) (md : List Byte)
    (adrs : Adrs) :
    IsQueryBoundP (forsPkFromSigM core sig md s adrs : OracleComp (deriveSpec core) core.Y)
      (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_bind_zero
    (isQueryBoundP_ofFnM_zero _ fun _ =>
      isQueryBoundP_bind_zero (isQueryBoundP_publicHash_f hsep pkSeed s (show 3 ≤ 4 by decide) _)
        fun leaf => isQueryBoundP_climbM_zero _ _ leaf _
          (fun _ _ l r => isQueryBoundP_publicHash_h hsep pkSeed s (show 3 ≤ 4 by decide) l r))
    fun _ => isQueryBoundP_publicHash_tl hsep pkSeed s (show 4 ≤ 4 by decide) _

/-! ### The internal scheme -/

/-- Key generation over derivation-backed secrets makes no derivable public query. -/
theorem isQueryBoundP_keygenInternalWithSecretM [SampleableType core.Y] :
    IsQueryBoundP (GeneralScheme.keygenInternalWithSecretM core (deriveSecret core) s :
      OracleComp (deriveSpec core) core.Y) (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_rootWithSecretM hsep pkSeed s

/-- Signing over derivation-backed secrets at a supplied randomizer makes no derivable public
query. -/
theorem isQueryBoundP_signInternalWithSecretRandomizerM [SampleableType core.Y] (msg : List Byte)
    (pkRoot R : core.Y) :
    IsQueryBoundP (GeneralScheme.signInternalWithSecretRandomizerM core (deriveSecret core) msg s
      pkRoot R : OracleComp (deriveSpec core) _) (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_bind_zero (isQueryBoundP_publicHash_hmsg pkSeed R s pkRoot msg) fun _ =>
    isQueryBoundP_bind_zero (isQueryBoundP_forsSignWithSecretM hsep pkSeed s _ _) fun _ =>
      isQueryBoundP_bind_zero (isQueryBoundP_forsPkFromSigM hsep pkSeed s _ _ _) fun _ =>
        isQueryBoundP_bind_zero (isQueryBoundP_signWithSecretM hsep pkSeed s _ _) fun _ =>
          isQueryBoundP_pure _ _ _

/-- Verification makes no derivable public query. -/
theorem isQueryBoundP_verifyInternalM [DecidableEq core.Y] (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp core) (pk : PublicKeyCore core) :
    IsQueryBoundP (GeneralScheme.verifyInternalM vp core msg sig pk :
      OracleComp (deriveSpec core) Bool) (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_bind_zero (isQueryBoundP_publicHash_hmsg pkSeed _ _ _ msg) fun _ =>
    isQueryBoundP_bind_zero (isQueryBoundP_forsPkFromSigM hsep pkSeed _ _ _ _) fun _ =>
      isQueryBoundP_hypertreeVerifyM hsep pkSeed _ _ _ _ _

end Honest

/-! ## The secret-free scheme and its experiment -/

section Scheme

variable {core} [SampleableType core.Y] [DecidableEq core.Y] (hsep : core.KeySeparated)
  (pkSeed : core.PkSeed)
include hsep

/-- Key generation of `deriveScheme` makes no derivable public query. -/
theorem isQueryBoundP_deriveScheme_keygen (optRand : PublicKeyCore core → ProbComp core.Y) :
    IsQueryBoundP (deriveScheme core optRand pkSeed).keygen
      (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_bind_zero (isQueryBoundP_keygenInternalWithSecretM hsep pkSeed pkSeed) fun _ =>
    isQueryBoundP_pure _ _ _

/-- Signing with `deriveScheme` makes no derivable public query: the randomizer is a derivation
query, every secret value a derivation query, and every public query an `H_msg` query or a
tweakable-hash query at an address of type at most `4`. -/
theorem isQueryBoundP_deriveScheme_sign (optRand : PublicKeyCore core → ProbComp core.Y)
    (pk sk : PublicKeyCore core) (msg : List Byte) :
    IsQueryBoundP ((deriveScheme core optRand pkSeed).sign pk sk msg)
      (IsDerivablePublicQuery core pkSeed) 0 := by
  refine isQueryBoundP_bind_zero (isQueryBoundP_liftM_probComp pkSeed _) fun addrnd =>
    isQueryBoundP_bind_zero ?_ fun R =>
      isQueryBoundP_signInternalWithSecretRandomizerM hsep pkSeed sk.pkSeed msg sk.pkRoot R
  change IsQueryBoundP (liftM ((deriveSpec core).query (.inr (.inr (addrnd, msg)))) :
    OracleComp (deriveSpec core) core.Y) _ 0
  rw [isQueryBoundP_query_iff]
  exact False.elim

/-- Verification with `deriveScheme` makes no derivable public query. -/
theorem isQueryBoundP_deriveScheme_verify (optRand : PublicKeyCore core → ProbComp core.Y)
    (pk : PublicKeyCore core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp core) :
    IsQueryBoundP ((deriveScheme core optRand pkSeed).verify pk msg sig)
      (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_verifyInternalM hsep pkSeed msg sig pk

/-- **Every derivable public query of the secret-free experiment is a forger hash query.** If the
forger makes at most `qh` hash queries, the transcript experiment of `deriveScheme` against the
lifted forger makes at most `qh` derivable public queries: key generation, signing and
verification make none. -/
theorem isQueryBoundP_unforgeableTranscriptExperiment_deriveAdversary
    [SampleableType core.SkSeed] [SampleableType core.SkPrf] {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    {adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    IsQueryBoundP (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed))
      (IsDerivablePublicQuery core pkSeed) qh := by
  refine (isQueryBoundP_iff_of_map_eq (map_wins_unforgeableTranscriptExperiment _)).2 ?_
  rw [unforgeableExperiment, show qh = 0 + (qh + (0 + 0)) by omega]
  refine isQueryBoundP_bind (isQueryBoundP_deriveScheme_keygen hsep pkSeed optRand)
    fun ⟨pk, sk⟩ _ => ?_
  refine isQueryBoundP_bind ?_ fun ⟨⟨msg, sig⟩, _⟩ _ =>
    isQueryBoundP_bind (isQueryBoundP_deriveScheme_verify hsep pkSeed optRand pk msg sig)
      fun _ _ => isQueryBoundP_pure _ _ _
  rw [deriveAdversary, UnforgeableAdversary.mapOracles_main]
  refine isQueryBoundP_runWithSigningOracle_simulateQ_addLift _ pk sk _ (hadv pk).1
    (fun t _ => ?_) (fun t ht => ?_) fun msg =>
      isQueryBoundP_deriveScheme_sign hsep pkSeed optRand pk sk msg
  · change IsQueryBoundP (liftM ((deriveSpec core).query (.inl t)) :
      OracleComp (deriveSpec core) _) _ 1
    rw [isQueryBoundP_query_iff]
    exact fun _ => Nat.one_pos
  · rcases t with n | t
    · change IsQueryBoundP (liftM ((deriveSpec core).query (.inl (.inl n))) :
        OracleComp (deriveSpec core) _) _ 0
      rw [isQueryBoundP_query_iff]
      exact False.elim
    · exact (ht trivial).elim

end Scheme

end Security

end SLHDSA
