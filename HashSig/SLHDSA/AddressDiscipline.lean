/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SecretProvider
import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.QueryBound

/-!
# The address discipline of the SLH-DSA programs

SLH-DSA evaluates its tweakable hash only at addresses of type at most `4` (`WOTS_HASH`,
`WOTS_PK`, `TREE`, `FORS_TREE` and `FORS_ROOTS`) and reads its secret values only at secret-key
addresses (`Adrs.IsSecretKey`). This module states that fact for the provider-parametric programs
of `HashSig.SLHDSA.SecretProvider` and for the verification programs, for any predicate `Q` on
programs that holds of every `pure` and is preserved by `bind`, in the style of
`PerfectMerkleTree.merkleRootM_pred_of_subtree`. `Q` holds of a program once it holds of

* each hash callback at every address of type at most `4` (for the internal scheme, of
  `PublicHash.tl` at the public seed the program uses and every such address),
* the secret provider at every secret-key address, and
* the one `H_msg` query of internal signing and of verification.

Instances of `Q` include `fun oa => IsQueryBoundP oa p 0` and `fun oa => AllQueriesSatisfy oa P`.
The hypotheses range over address types rather than the exact addresses visited, so they are the
same at every layer; the type of each address a program builds is checked by evaluation
(`Nat.le_of_ble_eq_true rfl`). A predicate that holds only on a bounded family of addresses, such
as the addresses a program visits, does not meet them. The chain lemma `chainWith_pred` is the
exception: its hypothesis is on the addresses the chain visits, so it also serves a predicate that
holds only on part of a chain.

The key-level counterpart is `CorePrimitives.KeySeparated`: no address of type at most `4` shares
its oracle key with a secret-key address. Every shipped bundle satisfies it
(`HashSig.SLHDSA.Security.KeySeparation`), and `CorePrimitives.KeyDiscipline`
(`HashSig.SLHDSA.Security.KeyDiscipline`) bundles it with injectivity of the oracle key on in-range
addresses and the parameter set's address width bounds.

## Labels

*WOTS+*: `chainWith_pred`, `wotsPkGenWithSecret_pred`, `wotsSignWithSecret_pred`,
`wotsPkFromSigWith_pred`.

*XMSS*: `xmssNodeWithSecret_pred`, `xmssSignWithSecret_pred`, `xmssPkFromSigWith_pred`.

*FORS*: `forsSignWithSecret_pred`, `forsPkFromSigWith_pred`.

*The hypertree*: `GeneralHypertree.signFromPositionWithSecret_pred`,
`GeneralHypertree.recoverFromPositionWith_pred`.

*The internal scheme*: `GeneralScheme.keygenInternalWithSecretM_pred`,
`GeneralScheme.signInternalWithSecretRandomizerM_pred`, `GeneralScheme.verifyInternalM_pred`.

*Key separation*: `CorePrimitives.KeySeparated`.
-/

public section

/-- A proof that an address built by the SLH-DSA address setters has type at most `4`, by
evaluating its type. -/
local macro "type_le_four" : term => `(Nat.le_of_ble_eq_true rfl)

namespace SLHDSA

variable {m : Type → Type*} [Monad m] [LawfulMonad m] (Q : ∀ {α : Type}, m α → Prop)
  (hpure : ∀ {α : Type} (x : α), Q (pure x))
  (hbind : ∀ {α β : Type} (oa : m α) (ob : α → m β), Q oa → (∀ x, Q (ob x)) → Q (oa >>= ob))

omit [LawfulMonad m] in
include hpure hbind in
/-- A WOTS+ chain from hash address `i` over `s` steps satisfies `Q` when the hash callback does
at each address the chain visits, `adrs.setHashAddress (i + j)` for `j < s`. -/
theorem chainWith_pred {Y : Type} {hash : Adrs → Y → m Y} {adrs : Adrs} (x : Y) (i : ℕ) :
    ∀ s, (∀ j < s, ∀ y, Q (hash (adrs.setHashAddress (i + j)) y)) →
      Q (chainWith hash adrs x i s)
  | 0, _ => hpure _
  | s + 1, h => hbind _ _ (chainWith_pred x i s fun j hj => h j (by omega)) fun y =>
      h s (by omega) y

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
  {hash : Adrs → core.Y → m core.Y} {compress : Adrs → List core.Y → m core.Y}
  {nodeHash : Adrs → core.Y → core.Y → m core.Y} {secret : Adrs → m core.Y}
  (hhash : ∀ a : Adrs, a.type ≤ 4 → ∀ y, Q (hash a y))
  (hcompress : ∀ a : Adrs, a.type ≤ 4 → ∀ ys, Q (compress a ys))
  (hnode : ∀ a : Adrs, a.type ≤ 4 → ∀ l r, Q (nodeHash a l r))
  (hsecret : ∀ a : Adrs, a.IsSecretKey → Q (secret a))

/-! ## WOTS+ -/

include hpure hbind hhash hcompress hsecret in
/-- The provider-parametric WOTS+ public key satisfies `Q`. -/
theorem wotsPkGenWithSecret_pred (adrs : Adrs) :
    Q (wotsPkGenWithSecret core hash compress secret adrs) :=
  hbind _ _ (Vector.ofFnM_pred Q hpure hbind _ fun _ =>
    hbind _ _ (hsecret _ (Adrs.isSecretKey_wotsSkAdrs _ _)) fun x =>
      chainWith_pred Q hpure hbind x 0 _ fun _ _ => hhash _ type_le_four)
    fun _ => hcompress _ type_le_four _

include hpure hbind hhash hsecret in
/-- Provider-parametric WOTS+ signing satisfies `Q`. -/
theorem wotsSignWithSecret_pred (msg : core.Y) (adrs : Adrs) :
    Q (wotsSignWithSecret core hash secret msg adrs) :=
  Vector.ofFnM_pred Q hpure hbind _ fun _ =>
    hbind _ _ (hsecret _ (Adrs.isSecretKey_wotsSkAdrs _ _)) fun x =>
      chainWith_pred Q hpure hbind x 0 _ fun _ _ => hhash _ type_le_four

include hpure hbind hhash hcompress in
/-- WOTS+ public-key recovery satisfies `Q`. -/
theorem wotsPkFromSigWith_pred (sig : WotsSig vp.params core) (msg : core.Y) (adrs : Adrs) :
    Q (wotsPkFromSigWith core hash compress sig msg adrs) :=
  hbind _ _ (Vector.ofFnM_pred Q hpure hbind _ fun _ =>
    chainWith_pred Q hpure hbind _ _ _ fun _ _ => hhash _ type_le_four)
    fun _ => hcompress _ type_le_four _

/-! ## XMSS -/

include hpure hbind hhash hcompress hnode hsecret in
/-- A provider-parametric XMSS subtree root satisfies `Q`. -/
theorem xmssNodeWithSecret_pred (adrs : Adrs) (z t : ℕ) :
    Q (xmssNodeWithSecret core hash compress nodeHash secret adrs z t) :=
  PerfectMerkleTree.merkleRootM_pred_of_subtree Q hbind _ _ z t
    (fun _ _ => wotsPkGenWithSecret_pred Q hpure hbind core hhash hcompress hsecret _)
    fun _ _ _ _ _ => hnode _ type_le_four

include hpure hbind hhash hcompress hnode hsecret in
/-- Provider-parametric XMSS signing satisfies `Q`. -/
theorem xmssSignWithSecret_pred (msg : core.Y) (adrs : Adrs) (idx : ℕ) :
    Q (xmssSignWithSecret core hash compress nodeHash secret msg adrs idx) :=
  hbind _ _ (PerfectMerkleTree.intrinsicAuthPathM_pred_of_tree Q hpure hbind _ _ idx _
    (fun _ _ => wotsPkGenWithSecret_pred Q hpure hbind core hhash hcompress hsecret _)
    fun _ _ _ _ _ => hnode _ type_le_four)
    fun _ => hbind _ _ (wotsSignWithSecret_pred Q hpure hbind core hhash hsecret msg _)
      fun _ => hpure _

include hpure hbind hhash hcompress hnode in
/-- XMSS root recovery satisfies `Q`. -/
theorem xmssPkFromSigWith_pred (idx : ℕ) (sig : XmssSig vp.params core) (msg : core.Y)
    (adrs : Adrs) : Q (xmssPkFromSigWith core hash compress nodeHash idx sig msg adrs) :=
  hbind _ _ (wotsPkFromSigWith_pred Q hpure hbind core hhash hcompress sig.wots msg _) fun leaf =>
    PerfectMerkleTree.climbM_pred_of_ancestors Q hpure hbind _ idx leaf _
      fun _ _ _ => hnode _ type_le_four

/-! ## FORS -/

include hpure hbind hhash hnode hsecret in
/-- Provider-parametric FORS signing satisfies `Q`. -/
theorem forsSignWithSecret_pred (md : List Byte) (adrs : Adrs) :
    Q (forsSignWithSecret core hash nodeHash secret md adrs) :=
  Vector.ofFnM_pred Q hpure hbind _ fun _ =>
    hbind _ _ (PerfectMerkleTree.intrinsicAuthPathM_pred_of_tree Q hpure hbind _ _ _ _
      (fun _ _ => hbind _ _ (hsecret _ (Adrs.isSecretKey_forsSkAdrs _ _)) fun _ =>
        hhash _ type_le_four _)
      fun _ _ _ _ _ => hnode _ type_le_four)
    fun _ => hbind _ _ (hsecret _ (Adrs.isSecretKey_forsSkAdrs _ _)) fun _ => hpure _

include hpure hbind hhash hcompress hnode in
/-- FORS public-key recovery satisfies `Q`. -/
theorem forsPkFromSigWith_pred (sig : ForsSigCore vp.params core) (md : List Byte)
    (adrs : Adrs) : Q (forsPkFromSigWith core hash nodeHash compress sig md adrs) :=
  hbind _ _ (Vector.ofFnM_pred Q hpure hbind _ fun _ =>
    hbind _ _ (hhash _ type_le_four _) fun leaf =>
      PerfectMerkleTree.climbM_pred_of_ancestors Q hpure hbind _ _ leaf _
        fun _ _ _ => hnode _ type_le_four)
    fun _ => hcompress _ type_le_four _

/-! ## The hypertree -/

include hpure hbind hhash hcompress hnode hsecret in
/-- Provider-parametric hypertree signing from a layer position satisfies `Q`. -/
theorem GeneralHypertree.signFromPositionWithSecret_pred (recoverFinal : Bool)
    (pos : LayerPosition vp) :
    ∀ (layers : ℕ) (h : pos.layer.val + layers = vp.params.d) (msg : core.Y),
      Q (signFromPositionWithSecret core hash compress nodeHash secret recoverFinal pos layers h
        msg)
  | 0, _, _ => hpure _
  | 1, _, msg => by
      rw [signFromPositionWithSecret]
      refine hbind _ _ (xmssSignWithSecret_pred Q hpure hbind core hhash hcompress hnode hsecret
        msg _ _) fun sig => ?_
      cases recoverFinal
      · exact hpure _
      · exact hbind _ _ (xmssPkFromSigWith_pred Q hpure hbind core hhash hcompress hnode _ sig
          msg _) fun _ => hpure _
  | layers + 2, _, msg => by
      rw [signFromPositionWithSecret]
      exact hbind _ _ (xmssSignWithSecret_pred Q hpure hbind core hhash hcompress hnode hsecret
        msg _ _) fun sig => hbind _ _ (xmssPkFromSigWith_pred Q hpure hbind core hhash hcompress
          hnode _ sig msg _) fun root => hbind _ _
            (signFromPositionWithSecret_pred false _ (layers + 1) _ root) fun _ => hpure _

include hpure hbind hhash hcompress hnode in
/-- Hypertree root recovery from a layer position satisfies `Q`. -/
theorem GeneralHypertree.recoverFromPositionWith_pred (pkSeed : core.PkSeed)
    (pos : LayerPosition vp) :
    ∀ (layers : ℕ) (h : pos.layer.val + layers = vp.params.d) (msg : core.Y)
      (sigs : Vector (XmssSig vp.params core) layers),
      Q (recoverFromPositionWith vp core hash compress nodeHash pkSeed pos layers h msg sigs)
  | 0, _, _, _ => hpure _
  | 1, _, msg, sigs =>
      xmssPkFromSigWith_pred Q hpure hbind core hhash hcompress hnode _ sigs.head msg _
  | layers + 2, _, msg, sigs => by
      rw [recoverFromPositionWith]
      exact hbind _ _ (xmssPkFromSigWith_pred Q hpure hbind core hhash hcompress hnode _
        sigs.head msg _) fun root =>
          recoverFromPositionWith_pred pkSeed _ (layers + 1) _ root sigs.tail

end SLHDSA

/-! ## The internal scheme -/

namespace SLHDSA.GeneralScheme

variable {m : Type → Type*} [Monad m] [LawfulMonad m] (Q : ∀ {α : Type}, m α → Prop)
  (hpure : ∀ {α : Type} (x : α), Q (pure x))
  (hbind : ∀ {α β : Type} (oa : m α) (ob : α → m β), Q oa → (∀ x, Q (ob x)) → Q (oa >>= ob))
  {vp : ValidatedParams} (core : CorePrimitives vp.params) [HasQuery (publicHashSpec core) m]
  {secret : Adrs → m core.Y} (hsecret : ∀ a : Adrs, a.IsSecretKey → Q (secret a))

include hpure hbind hsecret in
/-- Provider-parametric key generation at public seed `pkSeed` satisfies `Q`. -/
theorem keygenInternalWithSecretM_pred (pkSeed : core.PkSeed)
    (htl : ∀ a : Adrs, a.type ≤ 4 → ∀ xs, Q (PublicHash.tl core pkSeed a xs)) :
    Q (keygenInternalWithSecretM core secret pkSeed) :=
  xmssNodeWithSecret_pred Q hpure hbind core (fun a ha x => htl a ha [x]) htl
    (fun a ha l r => htl a ha [l, r]) hsecret _ _ _

include hpure hbind hsecret in
/-- Provider-parametric signing at public seed `pkSeed` and a supplied randomizer satisfies
`Q`. -/
theorem signInternalWithSecretRandomizerM_pred (msg : List Byte) (pkSeed : core.PkSeed)
    (pkRoot R : core.Y)
    (htl : ∀ a : Adrs, a.type ≤ 4 → ∀ xs, Q (PublicHash.tl core pkSeed a xs))
    (hmsg : Q (PublicHash.hmsg core R pkSeed pkRoot msg)) :
    Q (signInternalWithSecretRandomizerM core secret msg pkSeed pkRoot R) :=
  have hf := fun a ha x => htl a ha [x]
  have hh := fun a ha l r => htl a ha [l, r]
  hbind _ _ hmsg fun _ =>
    hbind _ _ (forsSignWithSecret_pred Q hpure hbind core hf hh hsecret _ _) fun _ =>
      hbind _ _ (forsPkFromSigWith_pred Q hpure hbind core hf htl hh _ _ _) fun _ =>
        hbind _ _ (GeneralHypertree.signFromPositionWithSecret_pred Q hpure hbind core hf htl hh
          hsecret _ _ _ _ _) fun _ => hpure _

include hpure hbind in
/-- Verification against public key `pk` satisfies `Q`. -/
theorem verifyInternalM_pred [DecidableEq core.Y] (msg : List Byte) (sig : SignatureCore vp core)
    (pk : PublicKeyCore core)
    (htl : ∀ a : Adrs, a.type ≤ 4 → ∀ xs, Q (PublicHash.tl core pk.pkSeed a xs))
    (hmsg : Q (PublicHash.hmsg core sig.randomness pk.pkSeed pk.pkRoot msg)) :
    Q (verifyInternalM vp core msg sig pk) :=
  have hf := fun a ha x => htl a ha [x]
  have hh := fun a ha l r => htl a ha [l, r]
  hbind _ _ hmsg fun _ =>
    hbind _ _ (forsPkFromSigWith_pred Q hpure hbind core hf htl hh _ _ _) fun _ =>
      hbind _ _ (GeneralHypertree.recoverFromPositionWith_pred Q hpure hbind core hf htl hh _ _
        _ _ _ _) fun _ => hpure _

end SLHDSA.GeneralScheme

/-! ## Key separation -/

namespace SLHDSA

/-- The oracle key of a secret-key address is the key of no address of type at most `4`, the
types of the `WOTS_HASH`, `WOTS_PK`, `TREE`, `FORS_TREE` and `FORS_ROOTS` addresses at which
SLH-DSA evaluates the tweakable hash. -/
@[expose] def CorePrimitives.KeySeparated {p : Params} (core : CorePrimitives p) : Prop :=
  ∀ a b : Adrs, a.IsSecretKey → b.type ≤ 4 → core.adrsToKey a ≠ core.adrsToKey b

end SLHDSA
