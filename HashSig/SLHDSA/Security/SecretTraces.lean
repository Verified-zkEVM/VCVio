/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.AddressDiscipline
public import HashSig.SLHDSA.Security.NodeGraph
import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.QueryBound

/-!
# The provider-parametric SLH-DSA programs at the union ledger

The provider-parametric programs of `HashSig.SLHDSA.SecretProvider` read their WOTS+ and FORS
secrets from a provider `secret : Adrs → m core.Y`. This module states, for any predicate `Q` on
programs that holds of every `pure` and is preserved by `bind`, that `Q` holds of these programs,
and of the verification programs, at every reachable position once it holds of

* each hash callback at every address of the union ledger `constructionAddresses` (for the
  internal scheme, of `PublicHash.tl` at the public seed the program uses and every ledger
  address),
* the secret provider at every secret child (`childAdrs`) of a ledger address, and
* the one `H_msg` query of internal signing and of verification.

This is the ledger-indexed counterpart of `HashSig.SLHDSA.AddressDiscipline`, whose hypotheses
range over address types. The hypotheses here range over the addresses the programs visit, so a
predicate that holds only on the ledger and its secret children meets them: the instance
`fun oa => AllQueriesSatisfy oa P` with `P` saying that a query is at an honest address key, for
example. The positions are given as in `HashSig.SLHDSA.Security.ComponentTraces`: a
`LayerPosition` for WOTS+, XMSS signing and recovery and the hypertree loops, a `LayerTreeCoord`
for an XMSS subtree root, a `BottomPosition` for FORS, and the digest-derived positions for the
internal scheme. The ledger memberships of the visited addresses are those of `ComponentTraces`;
the secrets read are the children of the first step of a WOTS+ chain
(`childAdrs_wotsChainAdrs_setHashAddress_zero`) and of a FORS leaf (`childAdrs_forsNodeAdrs_zero`).

## Labels

*WOTS+*: `chainWith_pred_of_ledger`, `wotsPkGenWithSecret_pred_of_ledger`,
`wotsSignWithSecret_pred_of_ledger`, `wotsPkFromSigWith_pred_of_ledger`.

*XMSS*: `xmssLeafWithSecret_pred_of_ledger`, `xmssNodeWithSecret_pred_of_ledger`,
`xmssSignWithSecret_pred_of_ledger`, `xmssPkFromSigWith_pred_of_ledger`.

*FORS*: `forsLeafWithSecret_pred_of_ledger`, `forsSignWithSecret_pred_of_ledger`,
`forsPkFromSigWith_pred_of_ledger`.

*The hypertree*: `signFromPositionWithSecret_pred_of_ledger`,
`recoverFromPositionWith_pred_of_ledger`.

*The internal scheme*: `keygenInternalWithSecretM_pred_of_ledger`,
`signInternalWithSecretRandomizerM_pred_of_ledger`, `verifyInternalM_pred_of_ledger`.
-/

public section

namespace SLHDSA.Security

variable {m : Type → Type*} [Monad m] [LawfulMonad m] (Q : ∀ {α : Type}, m α → Prop)
  (hpure : ∀ {α : Type} (x : α), Q (pure x))
  (hbind : ∀ {α β : Type} (oa : m α) (ob : α → m β), Q oa → (∀ x, Q (ob x)) → Q (oa >>= ob))

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
  {hash : Adrs → core.Y → m core.Y} {compress : Adrs → List core.Y → m core.Y}
  {nodeHash : Adrs → core.Y → core.Y → m core.Y} {secret : Adrs → m core.Y}
  (hhash : ∀ a ∈ constructionAddresses vp, ∀ y, Q (hash a y))
  (hcompress : ∀ a ∈ constructionAddresses vp, ∀ ys, Q (compress a ys))
  (hnode : ∀ a ∈ constructionAddresses vp, ∀ l r, Q (nodeHash a l r))
  (hsecret : ∀ a b, b ∈ constructionAddresses vp → .inl a ∈ childAdrs vp b → Q (secret a))

/-! ## WOTS+ -/

omit [LawfulMonad m] in
include hpure hbind hhash in
/-- A chain of a reachable WOTS+ instance from hash address `i` over `s` steps with
`i + s ≤ w - 1` satisfies `Q`. -/
theorem chainWith_pred_of_ledger (pos : LayerPosition vp) (c : Fin vp.params.len) (x : core.Y)
    {i s : ℕ} (h : i + s ≤ vp.params.w - 1) :
    Q (chainWith hash (wotsChainAdrs (wotsInstanceAdrs pos) c.val) x i s) :=
  chainWith_pred Q hpure hbind x i s fun _ _ =>
    hhash _ (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos c (by omega))

omit [Monad m] [LawfulMonad m] in
include hsecret in
/-- The provider at a chain start of a reachable WOTS+ instance satisfies `Q`. -/
private theorem secret_wotsSkAdrs_pred (pos : LayerPosition vp) (i : Fin vp.params.len) :
    Q (secret (wotsSkAdrs (wotsInstanceAdrs pos) i.val)) := by
  refine hsecret _ _ (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i (t := 0) ?_)
    (by rw [childAdrs_wotsChainAdrs_setHashAddress_zero]; exact List.mem_singleton_self _)
  have : 2 ≤ vp.params.w := Nat.le_self_pow (Nat.pos_iff_ne_zero.1 vp.valid.lgw_pos) 2
  omega

include hpure hbind hhash hcompress hsecret in
/-- WOTS+ public-key generation at a reachable instance satisfies `Q`. -/
theorem wotsPkGenWithSecret_pred_of_ledger (pos : LayerPosition vp) :
    Q (wotsPkGenWithSecret core hash compress secret (wotsInstanceAdrs pos)) :=
  hbind _ _ (Vector.ofFnM_pred Q hpure hbind _ fun i =>
    hbind _ _ (secret_wotsSkAdrs_pred Q core hsecret pos i) fun x =>
      chainWith_pred_of_ledger Q hpure hbind core hhash pos i x (by omega))
    fun _ => hcompress _ (wotsPkAdrs_mem_constructionAddresses pos) _

include hpure hbind hhash hsecret in
/-- WOTS+ signing at a reachable instance satisfies `Q`. -/
theorem wotsSignWithSecret_pred_of_ledger (msg : core.Y) (pos : LayerPosition vp) :
    Q (wotsSignWithSecret core hash secret msg (wotsInstanceAdrs pos)) :=
  Vector.ofFnM_pred Q hpure hbind _ fun i =>
    hbind _ _ (secret_wotsSkAdrs_pred Q core hsecret pos i) fun x =>
      chainWith_pred_of_ledger Q hpure hbind core hhash pos i x
        (by simpa using chainStepsCore_le core msg i.val)

include hpure hbind hhash hcompress in
/-- WOTS+ public-key recovery at a reachable instance satisfies `Q`. -/
theorem wotsPkFromSigWith_pred_of_ledger (sig : WotsSig vp.params core) (msg : core.Y)
    (pos : LayerPosition vp) :
    Q (wotsPkFromSigWith core hash compress sig msg (wotsInstanceAdrs pos)) :=
  hbind _ _ (Vector.ofFnM_pred Q hpure hbind _ fun i =>
    chainWith_pred_of_ledger Q hpure hbind core hhash pos i _
      (by have := chainStepsCore_le core msg i.val; omega))
    fun _ => hcompress _ (wotsPkAdrs_mem_constructionAddresses pos) _

/-! ## XMSS -/

include hpure hbind hhash hcompress hsecret in
/-- The XMSS leaf at a leaf `i < 2 ^ hp` of a reachable tree satisfies `Q`. -/
theorem xmssLeafWithSecret_pred_of_ledger (coord : LayerTreeCoord vp) {i : ℕ}
    (hi : i < 2 ^ vp.params.hp) :
    Q (xmssLeafWithSecret core hash compress secret coord.toAdrs i) :=
  wotsPkGenWithSecret_pred_of_ledger Q hpure hbind core hhash hcompress hsecret
    ⟨coord.layer, coord.tree, ⟨i, hi⟩⟩

include hpure hbind hhash hcompress hnode hsecret in
/-- An XMSS subtree root at `(z, t)` inside a reachable tree, `z ≤ hp` and `t < 2 ^ (hp - z)`,
satisfies `Q`. -/
theorem xmssNodeWithSecret_pred_of_ledger (coord : LayerTreeCoord vp) {z t : ℕ}
    (hz : z ≤ vp.params.hp) (ht : t < 2 ^ (vp.params.hp - z)) :
    Q (xmssNodeWithSecret core hash compress nodeHash secret coord.toAdrs z t) :=
  PerfectMerkleTree.merkleRootM_pred_of_subtree Q hbind _ _ z t
    (fun _ hi => xmssLeafWithSecret_pred_of_ledger Q hpure hbind core hhash hcompress hsecret
      coord (lt_pow_of_div_pow_lt hz hi ht))
    fun h _ hh hhz hi => hnode _ (xmssNodeAdrs_mem_constructionAddresses coord hh (hhz.trans hz)
      (lt_pow_of_div_pow_lt (by omega) hi
        (by rwa [show vp.params.hp - h - (z - h) = vp.params.hp - z by omega])))

include hpure hbind hhash hcompress hnode hsecret in
/-- XMSS signing at a reachable position satisfies `Q`. -/
theorem xmssSignWithSecret_pred_of_ledger (msg : core.Y) (pos : LayerPosition vp) :
    Q (xmssSignWithSecret core hash compress nodeHash secret msg pos.toAdrs pos.leaf.val) :=
  have hleaf : pos.leaf.val / 2 ^ vp.params.hp = 0 := Nat.div_eq_of_lt pos.leaf.isLt
  hbind _ _ (PerfectMerkleTree.intrinsicAuthPathM_pred_of_tree Q hpure hbind _ _ _ _
    (fun i hi => wotsPkGenWithSecret_pred_of_ledger Q hpure hbind core hhash hcompress hsecret
      ⟨pos.layer, pos.tree, ⟨i, lt_pow_of_div_pow_lt le_rfl (hi.trans hleaf) (by positivity)⟩⟩)
    fun _ _ hh hhp hi => hnode _ (xmssNodeAdrs_mem_constructionAddresses_of_position pos hh hhp
      (lt_pow_of_div_pow_lt le_rfl (hi.trans hleaf) (by positivity))))
    fun _ => hbind _ _ (wotsSignWithSecret_pred_of_ledger Q hpure hbind core hhash hsecret msg pos)
      fun _ => hpure _

include hpure hbind hhash hcompress hnode in
/-- XMSS root recovery at a reachable position satisfies `Q`. -/
theorem xmssPkFromSigWith_pred_of_ledger (sig : XmssSig vp.params core) (msg : core.Y)
    (pos : LayerPosition vp) :
    Q (xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sig msg pos.toAdrs) :=
  hbind _ _ (wotsPkFromSigWith_pred_of_ledger Q hpure hbind core hhash hcompress sig.wots msg pos)
    fun leaf => PerfectMerkleTree.climbM_pred_of_ancestors Q hpure hbind _ _ leaf _
      fun h hh hhp => by
        simp only [Vector.length_toList] at hhp
        refine hnode _ (xmssNodeAdrs_mem_constructionAddresses_of_position pos hh hhp ?_)
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hhp]
        exact pos.leaf.isLt

/-! ## FORS -/

omit [Monad m] [LawfulMonad m] in
include hsecret in
/-- The provider at the secret of a leaf of FORS tree `tree` at a reachable bottom position
satisfies `Q`. -/
private theorem secret_forsSkAdrs_pred (pos : BottomPosition vp) (tree : Fin vp.params.k)
    {i : ℕ} (hi : i / 2 ^ vp.params.a = tree.val) :
    Q (secret (forsSkAdrs pos.forsAdrs i)) :=
  hsecret _ _ (forsLeafAdrs_mem_constructionAddresses pos tree hi)
    (by rw [childAdrs_forsNodeAdrs_zero]; exact List.mem_singleton_self _)

omit [LawfulMonad m] in
include hbind hhash hsecret in
/-- A leaf of FORS tree `tree` at a reachable bottom position satisfies `Q`. -/
theorem forsLeafWithSecret_pred_of_ledger (pos : BottomPosition vp) (tree : Fin vp.params.k)
    {i : ℕ} (hi : i / 2 ^ vp.params.a = tree.val) :
    Q (forsLeafWithSecret core hash secret pos.forsAdrs i) :=
  hbind _ _ (secret_forsSkAdrs_pred Q core hsecret pos tree hi) fun x =>
    hhash _ (forsLeafAdrs_mem_constructionAddresses pos tree hi) x

include hpure hbind hhash hnode hsecret in
/-- FORS signing at a reachable bottom position satisfies `Q`. -/
theorem forsSignWithSecret_pred_of_ledger (md : List Byte) (pos : BottomPosition vp) :
    Q (forsSignWithSecret core hash nodeHash secret md pos.forsAdrs) :=
  Vector.ofFnM_pred Q hpure hbind _ fun tree =>
    have hdiv := forsLeafIndex_div vp.params md tree.val
    hbind _ _ (PerfectMerkleTree.intrinsicAuthPathM_pred_of_tree Q hpure hbind _ _ _ _
      (fun _ hi => forsLeafWithSecret_pred_of_ledger Q hbind core hhash hsecret pos tree
        (hi.trans hdiv))
      fun _ _ hh hha hi => hnode _
        (forsTreeAdrs_mem_constructionAddresses pos tree hh hha (hi.trans hdiv)))
    fun _ => hbind _ _ (secret_forsSkAdrs_pred Q core hsecret pos tree hdiv) fun _ => hpure _

include hpure hbind hhash hcompress hnode in
/-- FORS public-key recovery at a reachable bottom position satisfies `Q`. -/
theorem forsPkFromSigWith_pred_of_ledger (sig : ForsSigCore vp.params core) (md : List Byte)
    (pos : BottomPosition vp) :
    Q (forsPkFromSigWith core hash nodeHash compress sig md pos.forsAdrs) :=
  hbind _ _ (Vector.ofFnM_pred Q hpure hbind _ fun tree =>
    hbind _ _ (hhash _ (forsLeafAdrs_mem_constructionAddresses pos tree
      (forsLeafIndex_div _ md _)) _) fun leaf =>
      PerfectMerkleTree.climbM_pred_of_ancestors Q hpure hbind _ _ leaf _ fun h hh hha => by
        simp only [Vector.length_toList] at hha
        refine hnode _ (forsTreeAdrs_mem_constructionAddresses pos tree hh hha ?_)
        rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_cancel' hha, forsLeafIndex_div])
    fun _ => hcompress _ (forsRootAdrs_mem_constructionAddresses pos) _

/-! ## The hypertree -/

include hpure hbind hhash hcompress hnode hsecret in
/-- Hypertree signing from a reachable position satisfies `Q`. -/
theorem signFromPositionWithSecret_pred_of_ledger (recoverFinal : Bool)
    (pos : LayerPosition vp) :
    ∀ (layers : ℕ) (h : pos.layer.val + layers = vp.params.d) (msg : core.Y),
      Q (GeneralHypertree.signFromPositionWithSecret core hash compress nodeHash secret
        recoverFinal pos layers h msg)
  | 0, _, _ => hpure _
  | 1, _, msg => by
      rw [GeneralHypertree.signFromPositionWithSecret]
      refine hbind _ _ (xmssSignWithSecret_pred_of_ledger Q hpure hbind core hhash hcompress hnode
        hsecret msg pos) fun sig => ?_
      cases recoverFinal
      · exact hpure _
      · exact hbind _ _ (xmssPkFromSigWith_pred_of_ledger Q hpure hbind core hhash hcompress hnode
          sig msg pos) fun _ => hpure _
  | layers + 2, _, msg => by
      rw [GeneralHypertree.signFromPositionWithSecret]
      exact hbind _ _ (xmssSignWithSecret_pred_of_ledger Q hpure hbind core hhash hcompress hnode
        hsecret msg pos) fun sig => hbind _ _ (xmssPkFromSigWith_pred_of_ledger Q hpure hbind core
          hhash hcompress hnode sig msg pos) fun root => hbind _ _
            (signFromPositionWithSecret_pred_of_ledger false _ (layers + 1) _ root) fun _ =>
              hpure _

include hpure hbind hhash hcompress hnode in
/-- Hypertree root recovery from a reachable position satisfies `Q`. -/
theorem recoverFromPositionWith_pred_of_ledger (pkSeed : core.PkSeed) (pos : LayerPosition vp) :
    ∀ (layers : ℕ) (h : pos.layer.val + layers = vp.params.d) (msg : core.Y)
      (sigs : Vector (XmssSig vp.params core) layers),
      Q (GeneralHypertree.recoverFromPositionWith vp core hash compress nodeHash pkSeed pos layers
        h msg sigs)
  | 0, _, _, _ => hpure _
  | 1, _, msg, sigs =>
      xmssPkFromSigWith_pred_of_ledger Q hpure hbind core hhash hcompress hnode sigs.head msg pos
  | layers + 2, _, msg, sigs => by
      rw [GeneralHypertree.recoverFromPositionWith]
      exact hbind _ _ (xmssPkFromSigWith_pred_of_ledger Q hpure hbind core hhash hcompress hnode
        sigs.head msg pos) fun root =>
          recoverFromPositionWith_pred_of_ledger pkSeed _ (layers + 1) _ root sigs.tail

/-! ## The internal scheme -/

section Scheme

variable [HasQuery (publicHashSpec core) m]

include hpure hbind hsecret in
/-- Key generation at public seed `pkSeed` satisfies `Q`. -/
theorem keygenInternalWithSecretM_pred_of_ledger (pkSeed : core.PkSeed)
    (htl : ∀ a ∈ constructionAddresses vp, ∀ xs, Q (PublicHash.tl core pkSeed a xs)) :
    Q (GeneralScheme.keygenInternalWithSecretM core secret pkSeed) := by
  have h := xmssNodeWithSecret_pred_of_ledger Q hpure hbind core (hash := PublicHash.f core pkSeed)
    (compress := PublicHash.tl core pkSeed) (nodeHash := PublicHash.h core pkSeed)
    (fun a ha x => htl a ha [x]) htl (fun a ha l r => htl a ha [l, r]) hsecret
    (LayerTreeCoord.top vp) (z := vp.params.hp) (t := 0) le_rfl (by positivity)
  rw [LayerTreeCoord.top_toAdrs_layerAdrs] at h
  exact h

include hpure hbind hsecret in
/-- Signing at public seed `pkSeed` and a supplied randomizer satisfies `Q`. -/
theorem signInternalWithSecretRandomizerM_pred_of_ledger (msg : List Byte) (pkSeed : core.PkSeed)
    (pkRoot R : core.Y)
    (htl : ∀ a ∈ constructionAddresses vp, ∀ xs, Q (PublicHash.tl core pkSeed a xs))
    (hmsg : Q (PublicHash.hmsg core R pkSeed pkRoot msg)) :
    Q (GeneralScheme.signInternalWithSecretRandomizerM core secret msg pkSeed pkRoot R) := by
  have hf := fun a ha x => htl a ha [x]
  have hh := fun a ha l r => htl a ha [l, r]
  refine hbind _ _ hmsg fun digest => ?_
  have hpos := BottomPosition.forsAdrs_ofDigestParts vp (splitDigest vp.params digest)
  refine hbind _ _ ?_ fun _ => hbind _ _ ?_ fun _ => hbind _ _
    (signFromPositionWithSecret_pred_of_ledger Q hpure hbind core hf htl hh hsecret _ _ _ _ _)
    fun _ => hpure _
  · rw [← hpos]
    exact forsSignWithSecret_pred_of_ledger Q hpure hbind core hf hh hsecret _ _
  · rw [← hpos]
    exact forsPkFromSigWith_pred_of_ledger Q hpure hbind core hf htl hh _ _ _

include hpure hbind in
/-- Verification against public key `pk` satisfies `Q`. -/
theorem verifyInternalM_pred_of_ledger [DecidableEq core.Y] (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp core) (pk : PublicKeyCore core)
    (htl : ∀ a ∈ constructionAddresses vp, ∀ xs, Q (PublicHash.tl core pk.pkSeed a xs))
    (hmsg : Q (PublicHash.hmsg core sig.randomness pk.pkSeed pk.pkRoot msg)) :
    Q (GeneralScheme.verifyInternalM vp core msg sig pk) := by
  have hf := fun a ha x => htl a ha [x]
  have hh := fun a ha l r => htl a ha [l, r]
  refine hbind _ _ hmsg fun digest => ?_
  have hpos := BottomPosition.forsAdrs_ofDigestParts vp (splitDigest vp.params digest)
  refine hbind _ _ ?_ fun _ => hbind _ _
    (recoverFromPositionWith_pred_of_ledger Q hpure hbind core hf htl hh _ _ _ _ _ _)
    fun _ => hpure _
  rw [← hpos]
  exact forsPkFromSigWith_pred_of_ledger Q hpure hbind core hf htl hh _ _ _

end Scheme

end SLHDSA.Security
