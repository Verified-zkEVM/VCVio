/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.GeneralScheme

/-!
# Secret providers for the honest SLH-DSA programs

A *secret provider* is a monadic callback `secret : Adrs → m core.Y` that answers the draw of one
WOTS+ or FORS secret value at a given address. The honest programs of `HashSig.SLHDSA` draw every
such value from `CorePrimitives.PRF` at the signer's secret seed, so the secret seed is baked into
their control flow. This module provides the twin of each honest program in which those draws go
to a provider instead: `wotsSignWithSecret`, `xmssSignWithSecret`, `forsSignWithSecret`,
`signFromPositionWithSecret`, `keygenInternalWithSecretM`, `signInternalWithSecretM`, and the
intermediate programs they are built from. A reduction that must answer the secret draws from an
oracle — a PRF challenger, or a lazily sampled table — instantiates `secret` with that oracle
instead of rewriting the program.

The `*_eq_*` theorems are the faithfulness half of the abstraction: at the honest provider
`fun a => pure (core.PRF pkSeed skSeed a)` each program of this module *is* the landed program it
twins, as an equation in `m`. Every twin is reached this way, from `wotsPkGenTopsWithSecret` up to
`signInternalWithSecretM`, so a reduction may descend to whatever layer it needs and rewrite back.

## Scope

Nothing here is probabilistic: `m` is an arbitrary (lawful, for the equations) monad, no
distribution is formed, and no security property is stated — a provider is a plumbing device, and
whether a particular provider is indistinguishable from the honest one is a question for
`HashSig.SLHDSA.Security`. The public hash is untouched: the twins take the same hash, compression
and node-hash callbacks as the `*With` programs, the `*M` twins still reach the public hash through
`HasQuery (publicHashSpec core)`, and no landed program is redefined in terms of its twin. The
message randomizer `core.PRFmsg` and the digest split are likewise untouched;
`signInternalWithSecretM` abstracts only the WOTS+ and FORS secrets, and still takes `skPrf`.

Each equation pins the *returned value* of a twin, and, because the hash callbacks are universally
quantified, the hash traffic the twin issues. It pins nothing about the provider traffic: the
honest provider is effect-free, so the equation does not say how many times a twin calls `secret`,
at which addresses it calls it when the result is discarded, or how those calls interleave with
the hash callbacks. A twin that drew the same secret twice, or drew one it never used, would
satisfy the same equation. A consumer that needs such a bound — a query count, or the set of
addresses a twin touches — needs a separate lemma about the twin itself, of the kind the landed
modules carry for their own programs (`wotsPkGenM_isTotalQueryBound` in `HashSig.SLHDSA.Wots`).

## Labels

Thirty-eight declarations: nineteen provider-parametric programs and nineteen specialisation
equations.

*Provider-parametric programs*:

* WOTS+: `wotsPkGenTopsWithSecret`, `wotsSignWithSecret`, `wotsPkGenWithSecret`;
* XMSS: `xmssLeafWithSecret`, `xmssNodeWithSecret`, `xmssSignWithSecret`, `xmssRootWithSecret`;
* FORS: `forsLeafWithSecret`, `forsRootWithSecret`, `forsPkGenWithSecret`,
  `forsSignWithSecret`, and its explicit-public-hash form `forsSignWithSecretM`;
* hypertree: `signFromPositionWithSecret`, `signWithSecret`, `rootWithSecret`, and their
  explicit-public-hash forms `signWithSecretM`, `rootWithSecretM`;
* scheme: `keygenInternalWithSecretM`, `signInternalWithSecretM`.

*Specialisation at the honest provider* — each states that the twin equals its landed program:

* `wotsPkGenTopsWithSecret_eq_wotsPkGenTopsWith`, `wotsSignWithSecret_eq_wotsSignWith`,
  `wotsPkGenWithSecret_eq_wotsPkGenWith`;
* `xmssLeafWithSecret_eq_xmssLeafWith`, `xmssNodeWithSecret_eq_xmssNodeWith`,
  `xmssSignWithSecret_eq_xmssSignWith`, `xmssRootWithSecret_eq_xmssRootWith`;
* `forsLeafWithSecret_eq_forsLeafWith`, `forsRootWithSecret_eq_forsRootWith`,
  `forsPkGenWithSecret_eq_forsPkGenWith`, `forsSignWithSecret_eq_forsSignWith`,
  `forsSignWithSecretM_eq_forsSignM`;
* `signFromPositionWithSecret_eq_signFromPositionWith`, `signWithSecret_eq_signWith`,
  `rootWithSecret_eq_rootWith`, `signWithSecretM_eq_signM`, `rootWithSecretM_eq_rootM`;
* `keygenInternalWithSecretM_eq_keygenInternalM`, `signInternalWithSecretM_eq_signInternalM`.

## References

- NIST FIPS 205, §5 (Algorithms 5–8), §6 (Algorithms 9–10), §7 (Algorithm 12),
  §8 (Algorithms 14–16), §9 (Algorithms 18–19)
-/

public section

open OracleComp OracleSpec

namespace SLHDSA

variable {p : Params} (core : CorePrimitives p)

/-! ## Provider-parametric WOTS+ -/

/-- The `p.len` WOTS+ chain ends at `adrs`, with each chain started from the value the provider
`secret` returns at its `WOTS_PRF` address rather than from `core.PRF` at a secret seed. -/
@[expose] def wotsPkGenTopsWithSecret {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (secret : Adrs → m core.Y)
    (adrs : Adrs) : m (Vector core.Y p.len) :=
  Vector.ofFnM fun i => do
    let x ← secret (wotsSkAdrs adrs i.val)
    chainWith hash (wotsChainAdrs adrs i.val) x 0 (p.w - 1)

/-- At the honest provider the provider-parametric WOTS+ chain ends are `wotsPkGenTopsWith`. -/
theorem wotsPkGenTopsWithSecret_eq_wotsPkGenTopsWith {m : Type → Type*} [Monad m] [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    wotsPkGenTopsWithSecret core hash (fun a => pure (core.PRF pk sk a)) adrs =
      wotsPkGenTopsWith core hash sk pk adrs := by
  simp only [wotsPkGenTopsWithSecret, wotsPkGenTopsWith, pure_bind]

/-- The WOTS+ signature on `msg` at `adrs` (FIPS 205 Algorithm 7), with each chain started from
the value the provider `secret` returns at its `WOTS_PRF` address. -/
@[expose] def wotsSignWithSecret {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (secret : Adrs → m core.Y)
    (msg : core.Y) (adrs : Adrs) : m (WotsSig p core) :=
  Vector.ofFnM fun i => do
    let x ← secret (wotsSkAdrs adrs i.val)
    chainWith hash (wotsChainAdrs adrs i.val) x 0 (chainStepsCore core msg i.val)

/-- At the honest provider provider-parametric WOTS+ signing is `wotsSignWith`. -/
theorem wotsSignWithSecret_eq_wotsSignWith {m : Type → Type*} [Monad m] [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y) (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) :
    wotsSignWithSecret core hash (fun a => pure (core.PRF pk sk a)) msg adrs =
      wotsSignWith core hash msg sk pk adrs := by
  simp only [wotsSignWithSecret, wotsSignWith, pure_bind]

/-- The WOTS+ public key at `adrs` (FIPS 205 Algorithm 6): the provider-parametric chain ends
compressed by `T_len` at `wotsPkAdrs adrs`. -/
@[expose] def wotsPkGenWithSecret {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (secret : Adrs → m core.Y) (adrs : Adrs) : m core.Y := do
  let tops ← wotsPkGenTopsWithSecret core hash secret adrs
  compress (wotsPkAdrs adrs) tops.toList

/-- At the honest provider the provider-parametric WOTS+ public key is `wotsPkGenWith`. -/
theorem wotsPkGenWithSecret_eq_wotsPkGenWith {m : Type → Type*} [Monad m] [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    wotsPkGenWithSecret core hash compress (fun a => pure (core.PRF pk sk a)) adrs =
      wotsPkGenWith core hash compress sk pk adrs := by
  rw [wotsPkGenWithSecret, wotsPkGenWith, wotsPkGenTopsWithSecret_eq_wotsPkGenTopsWith]

/-! ## Provider-parametric XMSS -/

/-- The XMSS leaf at keypair index `t` under `adrs`: the provider-parametric WOTS+ public key of
that keypair. -/
@[expose] def xmssLeafWithSecret {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (secret : Adrs → m core.Y) (adrs : Adrs) (t : ℕ) : m core.Y :=
  wotsPkGenWithSecret core hash compress secret (wotsLeafAdrs adrs t)

/-- The height-`z`, index-`t` node of the XMSS tree at `adrs` (FIPS 205 Algorithm 9), over
provider-parametric leaves. -/
@[expose] def xmssNodeWithSecret {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y) (secret : Adrs → m core.Y)
    (adrs : Adrs) (z t : ℕ) : m core.Y :=
  PerfectMerkleTree.merkleRootM (xmssLeafWithSecret core hash compress secret adrs)
    (xmssNodeHashWith nodeHash adrs) z t

/-- The XMSS signature at leaf `idx` on `msg` (FIPS 205 Algorithm 10): the authentication path
through the provider-parametric tree, paired with the provider-parametric WOTS+ signature. -/
@[expose] def xmssSignWithSecret {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y) (secret : Adrs → m core.Y)
    (msg : core.Y) (adrs : Adrs) (idx : ℕ) : m (XmssSig p core) := do
  let path ← PerfectMerkleTree.intrinsicAuthPathM
    (xmssLeafWithSecret core hash compress secret adrs)
    (xmssNodeHashWith nodeHash adrs) idx p.hp
  let sig ← wotsSignWithSecret core hash secret msg (wotsLeafAdrs adrs idx)
  return ⟨sig, path⟩

/-- At the honest provider the provider-parametric XMSS leaf is `xmssLeafWith`. -/
theorem xmssLeafWithSecret_eq_xmssLeafWith {m : Type → Type*} [Monad m] [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (t : ℕ) :
    xmssLeafWithSecret core hash compress (fun a => pure (core.PRF pk sk a)) adrs t =
      xmssLeafWith core hash compress sk pk adrs t := by
  rw [xmssLeafWithSecret, xmssLeafWith, wotsPkGenWithSecret_eq_wotsPkGenWith]

/-- At the honest provider provider-parametric XMSS signing is `xmssSignWith`. -/
theorem xmssSignWithSecret_eq_xmssSignWith {m : Type → Type*} [Monad m] [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (idx : ℕ) :
    xmssSignWithSecret core hash compress nodeHash (fun a => pure (core.PRF pk sk a))
        msg adrs idx =
      xmssSignWith core hash compress nodeHash msg sk pk adrs idx := by
  rw [xmssSignWithSecret, xmssSignWith, wotsSignWithSecret_eq_wotsSignWith,
    funext fun t => xmssLeafWithSecret_eq_xmssLeafWith core hash compress sk pk adrs t]

/-- The root of the XMSS tree at `adrs`, over provider-parametric leaves. -/
@[expose] def xmssRootWithSecret {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y) (secret : Adrs → m core.Y)
    (adrs : Adrs) : m core.Y :=
  xmssNodeWithSecret core hash compress nodeHash secret adrs p.hp 0

/-- At the honest provider the provider-parametric XMSS subtree root is `xmssNodeWith`. -/
theorem xmssNodeWithSecret_eq_xmssNodeWith {m : Type → Type*} [Monad m] [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (z t : ℕ) :
    xmssNodeWithSecret core hash compress nodeHash (fun a => pure (core.PRF pk sk a)) adrs z t =
      xmssNodeWith core hash compress nodeHash sk pk adrs z t := by
  rw [xmssNodeWithSecret, xmssNodeWith,
    funext fun t => xmssLeafWithSecret_eq_xmssLeafWith core hash compress sk pk adrs t]

/-- At the honest provider the provider-parametric XMSS root is `xmssRootWith`. -/
theorem xmssRootWithSecret_eq_xmssRootWith {m : Type → Type*} [Monad m] [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    xmssRootWithSecret core hash compress nodeHash (fun a => pure (core.PRF pk sk a)) adrs =
      xmssRootWith core hash compress nodeHash sk pk adrs := by
  rw [xmssRootWithSecret, xmssRootWith, xmssNodeWithSecret_eq_xmssNodeWith]

/-! ## Provider-parametric FORS -/

/-- The FORS leaf at global index `t` under `adrs` (FIPS 205 Algorithms 14–15): `F` at
`forsNodeAdrs adrs 0 t` of the value the provider `secret` returns at `forsSkAdrs adrs t`. -/
@[expose] def forsLeafWithSecret {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (secret : Adrs → m core.Y)
    (adrs : Adrs) (t : ℕ) : m core.Y := do
  let x ← secret (forsSkAdrs adrs t)
  hash (forsNodeAdrs adrs 0 t) x

/-- At the honest provider the provider-parametric FORS leaf is `forsLeafWith`. -/
theorem forsLeafWithSecret_eq_forsLeafWith {m : Type → Type*} [Monad m] [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (t : ℕ) :
    forsLeafWithSecret core hash (fun a => pure (core.PRF pk sk a)) adrs t =
      forsLeafWith core hash sk pk adrs t := by
  simp only [forsLeafWithSecret, forsLeafWith, forsSkGenCore, pure_bind]

/-- The root of FORS tree `i` under `adrs` (FIPS 205 Algorithm 15), over provider-parametric
leaves. -/
@[expose] def forsRootWithSecret {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (secret : Adrs → m core.Y) (adrs : Adrs) (i : ℕ) : m core.Y :=
  PerfectMerkleTree.merkleRootM (forsLeafWithSecret core hash secret adrs)
    (forsNodeHashWith nodeHash adrs) p.a i

/-- The FORS public key at `adrs`: the `p.k` provider-parametric tree roots compressed by `T_k` at
`forsPkAdrs adrs`. -/
@[expose] def forsPkGenWithSecret {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y) (secret : Adrs → m core.Y)
    (adrs : Adrs) : m core.Y := do
  let roots ← Vector.ofFnM fun i : Fin p.k =>
    forsRootWithSecret core hash nodeHash secret adrs i.val
  compress (forsPkAdrs adrs) roots.toList

/-- The FORS signature on digest `md` at `adrs` (FIPS 205 Algorithm 16): for each tree, the
authentication path through the provider-parametric tree together with the provider's value at the
indexed leaf's `FORS_PRF` address. -/
@[expose] def forsSignWithSecret {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (secret : Adrs → m core.Y) (md : List Byte) (adrs : Adrs) : m (ForsSigCore p core) :=
  Vector.ofFnM fun i : Fin p.k => do
    let idx := i.val * 2 ^ p.a + forsIdx p md i.val
    let path ← PerfectMerkleTree.intrinsicAuthPathM (forsLeafWithSecret core hash secret adrs)
      (forsNodeHashWith nodeHash adrs) idx p.a
    let sk ← secret (forsSkAdrs adrs idx)
    return ⟨sk, path⟩

/-- At the honest provider the provider-parametric FORS root is `forsRootWith`. -/
theorem forsRootWithSecret_eq_forsRootWith {m : Type → Type*} [Monad m] [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y) (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (i : ℕ) :
    forsRootWithSecret core hash nodeHash (fun a => pure (core.PRF pk sk a)) adrs i =
      forsRootWith core hash nodeHash sk pk adrs i := by
  have hleaf : forsLeafWithSecret core hash (fun a => pure (core.PRF pk sk a)) adrs =
      forsLeafWith core hash sk pk adrs :=
    funext fun t => forsLeafWithSecret_eq_forsLeafWith core hash sk pk adrs t
  rw [forsRootWithSecret, forsRootWith, hleaf]

/-- At the honest provider the provider-parametric FORS public key is `forsPkGenWith`. -/
theorem forsPkGenWithSecret_eq_forsPkGenWith {m : Type → Type*} [Monad m] [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y) (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    forsPkGenWithSecret core hash nodeHash compress (fun a => pure (core.PRF pk sk a)) adrs =
      forsPkGenWith core hash nodeHash compress sk pk adrs := by
  rw [forsPkGenWithSecret, forsPkGenWith]
  congr 1
  exact congrArg Vector.ofFnM
    (funext fun i => forsRootWithSecret_eq_forsRootWith core hash nodeHash sk pk adrs i.val)

/-- At the honest provider provider-parametric FORS signing is `forsSignWith`. -/
theorem forsSignWithSecret_eq_forsSignWith {m : Type → Type*} [Monad m] [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y) (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (md : List Byte) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    forsSignWithSecret core hash nodeHash (fun a => pure (core.PRF pk sk a)) md adrs =
      forsSignWith core hash nodeHash md sk pk adrs := by
  have hleaf : forsLeafWithSecret core hash (fun a => pure (core.PRF pk sk a)) adrs =
      forsLeafWith core hash sk pk adrs :=
    funext fun t => forsLeafWithSecret_eq_forsLeafWith core hash sk pk adrs t
  rw [forsSignWithSecret, forsSignWith, hleaf]
  refine congrArg Vector.ofFnM (funext fun i => ?_)
  simp only [forsSkGenCore, pure_bind]

/-- `forsSignWithSecret` with the public hash issued through `HasQuery (publicHashSpec core)` at
`pkSeed`. -/
@[expose] def forsSignWithSecretM {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (secret : Adrs → m core.Y) (md : List Byte) (pkSeed : core.PkSeed) (adrs : Adrs) :
    m (ForsSigCore p core) :=
  forsSignWithSecret core (PublicHash.f core pkSeed) (PublicHash.h core pkSeed) secret md adrs

/-- At the honest provider provider-parametric FORS signing is `forsSignM`. -/
theorem forsSignWithSecretM_eq_forsSignM {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec core) m] (skSeed : core.SkSeed) (pkSeed : core.PkSeed)
    (md : List Byte) (adrs : Adrs) :
    forsSignWithSecretM core (fun a => pure (core.PRF pkSeed skSeed a)) md pkSeed adrs =
      (forsSignM core md skSeed pkSeed adrs : m (ForsSigCore p core)) := by
  rw [forsSignWithSecretM, forsSignM, forsSignWithSecret_eq_forsSignWith]

end SLHDSA

namespace SLHDSA.GeneralHypertree

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-- The hypertree signature of `msg` from layer position `pos` upward over `layers` layers
(FIPS 205 Algorithm 12), with every XMSS signature produced by `xmssSignWithSecret`. `recoverFinal`
forces the redundant root recovery in the top layer, matching `signFromPositionWith`. -/
@[expose] def signFromPositionWithSecret {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (secret : Adrs → m core.Y) (recoverFinal : Bool) (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → core.Y →
      m (Vector (XmssSig vp.params core) layers)
  | 0, _, _ => pure #v[]
  | 1, _, msg => do
      let sig ← xmssSignWithSecret core hash compress nodeHash secret msg pos.toAdrs pos.leaf.val
      if recoverFinal then
        let _ ← xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sig msg pos.toAdrs
        return #v[sig]
      else
        return #v[sig]
  | layers + 2, hremaining, msg => do
      let sig ← xmssSignWithSecret core hash compress nodeHash secret msg pos.toAdrs pos.leaf.val
      let root ←
        xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sig msg pos.toAdrs
      let next := pos.next (by omega)
      let rest ← signFromPositionWithSecret hash compress nodeHash secret false next
        (layers + 1) (by simp [next]; omega) root
      return rest.insertIdx 0 sig

/-- At the honest provider provider-parametric hypertree signing from a position is
`signFromPositionWith`. -/
theorem signFromPositionWithSecret_eq_signFromPositionWith {m : Type → Type*} [Monad m]
    [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (recoverFinal : Bool) (pos : LayerPosition vp) :
    ∀ (layers : ℕ) (h : pos.layer.val + layers = vp.params.d) (msg : core.Y),
      signFromPositionWithSecret core hash compress nodeHash (fun a => pure (core.PRF pk sk a))
          recoverFinal pos layers h msg =
        signFromPositionWith vp core hash compress nodeHash sk pk recoverFinal pos layers h msg
  | 0, _, _ => by rw [signFromPositionWithSecret, signFromPositionWith]
  | 1, _, msg => by
      rw [signFromPositionWithSecret, signFromPositionWith, xmssSignWithSecret_eq_xmssSignWith]
  | layers + 2, hremaining, msg => by
      rw [signFromPositionWithSecret, signFromPositionWith, xmssSignWithSecret_eq_xmssSignWith]
      refine bind_congr fun sig => bind_congr fun root => ?_
      dsimp only
      rw [signFromPositionWithSecret_eq_signFromPositionWith hash compress nodeHash sk pk false _
        (layers + 1)]

/-- The full hypertree signature of `msg` for the digest parts `parts` (FIPS 205 Algorithm 12),
over provider-parametric XMSS signatures. -/
@[expose] def signWithSecret {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y) (secret : Adrs → m core.Y)
    (msg : core.Y) (parts : DigestParts vp.params) : m (Signature vp core) :=
  let pos := LayerPosition.initial vp parts
  signFromPositionWithSecret core hash compress nodeHash secret (vp.params.d == 1) pos
    vp.params.d (by simp [pos]) msg

/-- The root of the top-layer XMSS tree of the hypertree, over provider-parametric leaves. -/
@[expose] def rootWithSecret {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y) (secret : Adrs → m core.Y) : m core.Y :=
  xmssRootWithSecret core hash compress nodeHash secret (layerAdrs (vp.params.d - 1) 0)

/-- At the honest provider provider-parametric hypertree signing is `signWith`. -/
theorem signWithSecret_eq_signWith {m : Type → Type*} [Monad m] [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (msg : core.Y) (parts : DigestParts vp.params) :
    signWithSecret core hash compress nodeHash (fun a => pure (core.PRF pk sk a)) msg parts =
      signWith vp core hash compress nodeHash msg sk pk parts := by
  rw [signWithSecret, signWith, signFromPositionWithSecret_eq_signFromPositionWith]

/-- At the honest provider the provider-parametric hypertree root is `rootWith`. -/
theorem rootWithSecret_eq_rootWith {m : Type → Type*} [Monad m] [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) :
    rootWithSecret core hash compress nodeHash (fun a => pure (core.PRF pk sk a)) =
      rootWith vp core hash compress nodeHash sk pk := by
  rw [rootWithSecret, rootWith, xmssRootWithSecret_eq_xmssRootWith]

/-- `signWithSecret` with the public hash issued through `HasQuery (publicHashSpec core)` at
`pkSeed`. -/
@[expose] def signWithSecretM {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (secret : Adrs → m core.Y) (msg : core.Y) (pkSeed : core.PkSeed)
    (parts : DigestParts vp.params) : m (Signature vp core) :=
  signWithSecret core (PublicHash.f core pkSeed) (PublicHash.tl core pkSeed)
    (PublicHash.h core pkSeed) secret msg parts

/-- `rootWithSecret` with the public hash issued through `HasQuery (publicHashSpec core)` at
`pkSeed`. -/
@[expose] def rootWithSecretM {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (secret : Adrs → m core.Y) (pkSeed : core.PkSeed) : m core.Y :=
  rootWithSecret core (PublicHash.f core pkSeed) (PublicHash.tl core pkSeed)
    (PublicHash.h core pkSeed) secret

/-- At the honest provider provider-parametric hypertree signing is `signM`. -/
theorem signWithSecretM_eq_signM {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec core) m] (skSeed : core.SkSeed) (pkSeed : core.PkSeed)
    (msg : core.Y) (parts : DigestParts vp.params) :
    signWithSecretM core (fun a => pure (core.PRF pkSeed skSeed a)) msg pkSeed parts =
      (signM vp core msg skSeed pkSeed parts : m (Signature vp core)) := by
  rw [signWithSecretM, signWithSecret, signM, signFromPositionM,
    signFromPositionWithSecret_eq_signFromPositionWith]

/-- At the honest provider the provider-parametric hypertree root is `rootM`. -/
theorem rootWithSecretM_eq_rootM {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec core) m] (skSeed : core.SkSeed) (pkSeed : core.PkSeed) :
    rootWithSecretM core (fun a => pure (core.PRF pkSeed skSeed a)) pkSeed =
      (rootM vp core skSeed pkSeed : m core.Y) := by
  rw [rootWithSecretM, rootM, rootWithSecret_eq_rootWith]

end SLHDSA.GeneralHypertree

namespace SLHDSA

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

namespace GeneralScheme

/-- FIPS 205 Algorithm 18 with the WOTS+ secrets drawn from the provider `secret`: the top-layer
hypertree root, which is the public key root. -/
@[expose] def keygenInternalWithSecretM {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (secret : Adrs → m core.Y) (pkSeed : core.PkSeed) : m core.Y :=
  GeneralHypertree.rootWithSecretM core secret pkSeed

/-- FIPS 205 Algorithm 19 with every WOTS+ and FORS secret drawn from the provider `secret`, so
that no secret seed appears: the message randomizer still comes from `core.PRFmsg` at `skPrf`, and
the digest is split exactly as in `signInternalM`. -/
@[expose] def signInternalWithSecretM {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (secret : Adrs → m core.Y) (msg : List Byte) (skPrf : core.SkPrf) (pkSeed : core.PkSeed)
    (pkRoot : core.Y) (addrnd : core.Y) : m (SignatureCore vp core) := do
  let R := core.PRFmsg skPrf addrnd msg
  let digest ← PublicHash.hmsg core R pkSeed pkRoot msg
  let parts := splitDigest vp.params digest
  let forsSig ← forsSignWithSecretM core secret parts.md.toList pkSeed parts.forsAdrs
  let forsPk ← forsPkFromSigM core forsSig parts.md.toList pkSeed parts.forsAdrs
  let htSig ← GeneralHypertree.signWithSecretM core secret forsPk pkSeed parts
  return ⟨R, forsSig, htSig⟩

/-- At the honest provider provider-parametric key generation, paired with the seeds into the
key structures, is `keygenInternalM`. -/
theorem keygenInternalWithSecretM_eq_keygenInternalM {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec core) m] (skSeed : core.SkSeed) (skPrf : core.SkPrf)
    (pkSeed : core.PkSeed) :
    ((fun pkRoot => ((⟨pkSeed, pkRoot⟩ : PublicKeyCore core),
          (⟨skSeed, skPrf, pkSeed, pkRoot⟩ : SecretKeyCore core))) <$>
        keygenInternalWithSecretM core (fun a => pure (core.PRF pkSeed skSeed a)) pkSeed) =
      (keygenInternalM vp core skSeed skPrf pkSeed :
        m (PublicKeyCore core × SecretKeyCore core)) := by
  rw [keygenInternalWithSecretM, GeneralHypertree.rootWithSecretM_eq_rootM, keygenInternalM,
    map_eq_bind_pure_comp]
  rfl

/-- At the honest provider provider-parametric signing is `signInternalM`. -/
theorem signInternalWithSecretM_eq_signInternalM {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec core) m] (msg : List Byte) (sk : SecretKeyCore core)
    (addrnd : core.Y) :
    signInternalWithSecretM core (fun a => pure (core.PRF sk.pkSeed sk.skSeed a)) msg sk.skPrf
        sk.pkSeed sk.pkRoot addrnd =
      (signInternalM vp core msg sk addrnd : m (SignatureCore vp core)) := by
  rw [signInternalWithSecretM, signInternalM]
  simp only [forsSignWithSecretM_eq_forsSignM, GeneralHypertree.signWithSecretM_eq_signM]

end GeneralScheme

end SLHDSA
