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
`signFromPositionWithSecret`, `keygenInternalWithSecretM`, `signInternalWithSecretRandomizerM`,
and the intermediate programs they are built from. A reduction that must answer the secret draws
from an oracle — a PRF challenger, or a lazily sampled table — instantiates `secret` with that
oracle instead of rewriting the program.

The `*_eq_*` theorems are the faithfulness half of the abstraction: at the honest provider
`fun a => pure (core.PRF pkSeed skSeed a)` a twin *is* the landed program it twins, as an equation
in `m`. Every twin that the two scheme twins are built from is reached this way, from
`wotsPkGenTopsWithSecret` up to `signInternalWithSecretRandomizerM`, so a reduction may descend to
whatever layer it needs and rewrite back.

The `*_natural` theorems carry a twin across a monad morphism: a morphism that commutes with the
hash callbacks, and with the provider at secret-key addresses (`Adrs.IsSecretKey`, type `WOTS_PRF`
or `FORS_PRF`), commutes with each program built from them. The twins read a secret only at
`wotsSkAdrs` and `forsSkAdrs`, both secret-key addresses, so two providers that agree there give the
same program. A reduction that interprets the provider — answering the secret draws from a challenge
oracle, and then reading that interpretation back as the honest provider — moves the whole program
along the interpretation with these, exactly as the `*With_natural` theorems of
`HashSig.SLHDSA.Wots`, `Xmss` and `Fors` move the landed programs. At the `*M` layer the morphism is
a `HasQuery.QueryHom (publicHashSpec core)`, so only the provider needs a hypothesis of its own.

## Scope

Nothing here is probabilistic: `m` is an arbitrary (lawful, for the theorems) monad, no
distribution is formed, and no security property is stated — a provider is a plumbing device, and
whether a particular provider is indistinguishable from the honest one is a question for
`HashSig.SLHDSA.Security`. The public hash is untouched: the twins take the same hash, compression
and node-hash callbacks as the `*With` programs, the `*M` twins still reach the public hash through
`HasQuery (publicHashSpec core)`, and no landed program is redefined in terms of its twin. The
digest split is likewise untouched, and `signInternalWithSecretRandomizerM` takes the message
randomizer `R` itself, so a caller may draw it from an oracle.

Each `*_eq_*` equation pins the *returned value* of a twin and, because the hash callbacks are
universally quantified, the hash traffic the twin issues. It pins nothing about the provider
traffic: the honest provider is effect-free, so the equation does not say how many times a twin
calls `secret`, at which addresses it calls it when the result is discarded, or how those calls
interleave with the hash callbacks, and nothing here bounds that traffic.

## Labels

Sixty declarations: the secret-key address predicate, its decidability instance and its two
builder lemmas, nineteen provider-parametric programs, eighteen specialisation equations, and
nineteen naturality theorems. There is no private declaration: the monadic-vector naturality step
the WOTS+ and FORS twins need is `Vector.ofFnM_natural` of `ToMathlib.Data.Vector`.

*Secret-key addresses*: `Adrs.IsSecretKey`, `Adrs.isSecretKey_wotsSkAdrs`,
`Adrs.isSecretKey_forsSkAdrs`.

*Provider-parametric programs*:

* WOTS+: `wotsPkGenTopsWithSecret`, `wotsSignWithSecret`, `wotsPkGenWithSecret`;
* XMSS: `xmssLeafWithSecret`, `xmssNodeWithSecret`, `xmssSignWithSecret`, `xmssRootWithSecret`;
* FORS: `forsLeafWithSecret`, `forsRootWithSecret`, `forsPkGenWithSecret`,
  `forsSignWithSecret`, and its explicit-public-hash form `forsSignWithSecretM`;
* hypertree: `signFromPositionWithSecret`, `signWithSecret`, `rootWithSecret`, and their
  explicit-public-hash forms `signWithSecretM`, `rootWithSecretM`;
* scheme: `keygenInternalWithSecretM`, `signInternalWithSecretRandomizerM`.

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
* `signInternalWithSecretRandomizerM_eq_signInternalWithRandomizerM`; key generation is
  `rootWithSecretM_eq_rootM`, `keygenInternalWithSecretM` being `rootWithSecretM`.

*Naturality* — each states that a monad morphism commuting with the callbacks, and with the
provider at secret-key addresses, commutes with the twin, named after it:
`wotsPkGenTopsWithSecret_natural`, `wotsSignWithSecret_natural`, `wotsPkGenWithSecret_natural`,
`xmssLeafWithSecret_natural`, `xmssNodeWithSecret_natural`, `xmssRootWithSecret_natural`,
`xmssSignWithSecret_natural`, `forsLeafWithSecret_natural`, `forsRootWithSecret_natural`,
`forsPkGenWithSecret_natural`, `forsSignWithSecret_natural`, `forsSignWithSecretM_natural`,
`signFromPositionWithSecret_natural`, `signWithSecret_natural`, `rootWithSecret_natural`,
`signWithSecretM_natural`, `rootWithSecretM_natural`, `keygenInternalWithSecretM_natural`,
`signInternalWithSecretRandomizerM_natural`.

## References

- NIST FIPS 205, §5 (Algorithms 5–8), §6 (Algorithms 9–10), §7 (Algorithm 12),
  §8 (Algorithms 14–16), §9 (Algorithms 18–19)
-/

public section

open OracleComp OracleSpec

namespace SLHDSA

variable {p : Params} (core : CorePrimitives p)

/-- An address is a secret-key address when its type is `WOTS_PRF` or `FORS_PRF`. -/
@[expose] def Adrs.IsSecretKey (a : Adrs) : Prop :=
  a.type = AddrType.wotsPrf.toCode ∨ a.type = AddrType.forsPrf.toCode

instance (a : Adrs) : Decidable a.IsSecretKey := inferInstanceAs (Decidable (_ ∨ _))

/-- The WOTS+ secret-value address is a secret-key address. -/
theorem Adrs.isSecretKey_wotsSkAdrs (adrs : Adrs) (i : ℕ) : (wotsSkAdrs adrs i).IsSecretKey :=
  .inl rfl

/-- The FORS secret-value address is a secret-key address. -/
theorem Adrs.isSecretKey_forsSkAdrs (adrs : Adrs) (t : ℕ) : (forsSkAdrs adrs t).IsSecretKey :=
  .inr rfl

/-! ## Provider-parametric WOTS+ -/

/-- The `p.len` WOTS+ chain ends at `adrs`, with each chain started from the value the provider
`secret` returns at its `WOTS_PRF` address rather than from `core.PRF` at a secret seed. -/
@[expose] def wotsPkGenTopsWithSecret {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (secret : Adrs → m core.Y)
    (adrs : Adrs) : m (Vector core.Y p.len) :=
  Wots.Program.runTops (I := Fin p.len) Vector.ofFnM
    (fun i => secret (wotsSkAdrs adrs i.val))
    (fun i j y => hash ((wotsChainAdrs adrs i.val).setHashAddress j) y)
    (p.w - 1) .publicKey

/-- Provider public-key tops preserve each native secret action before its chain. -/
theorem wotsPkGenTopsWithSecret_eq {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (secret : Adrs → m core.Y) (adrs : Adrs) :
    wotsPkGenTopsWithSecret core hash secret adrs = Vector.ofFnM (fun i => do
      let x ← secret (wotsSkAdrs adrs i.val)
      chainWith hash (wotsChainAdrs adrs i.val) x 0 (p.w - 1)) := by
  simp only [wotsPkGenTopsWithSecret, Wots.Program.runTops_publicKey,
    Wots.Program.runChains_eq, chainWith]

/-- At the honest provider the provider-parametric WOTS+ chain ends are `wotsPkGenTopsWith`. -/
theorem wotsPkGenTopsWithSecret_eq_wotsPkGenTopsWith {m : Type → Type*} [Monad m] [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    wotsPkGenTopsWithSecret core hash (fun a => pure (core.PRF pk sk a)) adrs =
      wotsPkGenTopsWith core hash sk pk adrs := by
  simp only [wotsPkGenTopsWithSecret_eq, wotsPkGenTopsWith_eq, pure_bind]

/-- The WOTS+ signature on `msg` at `adrs` (FIPS 205 Algorithm 7), with each chain started from
the value the provider `secret` returns at its `WOTS_PRF` address. -/
@[expose] def wotsSignWithSecret {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (secret : Adrs → m core.Y)
    (msg : core.Y) (adrs : Adrs) : m (WotsSig p core) :=
  Wots.Program.runTops (I := Fin p.len) Vector.ofFnM
    (fun i => secret (wotsSkAdrs adrs i.val))
    (fun i j y => hash ((wotsChainAdrs adrs i.val).setHashAddress j) y)
    (p.w - 1) (.sign (fun i => chainStepsCore core msg i.val))

/-- Provider signing preserves each native secret action before its message-selected chain. -/
theorem wotsSignWithSecret_eq {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (secret : Adrs → m core.Y)
    (msg : core.Y) (adrs : Adrs) :
    wotsSignWithSecret core hash secret msg adrs = Vector.ofFnM (fun i => do
      let x ← secret (wotsSkAdrs adrs i.val)
      chainWith hash (wotsChainAdrs adrs i.val) x 0 (chainStepsCore core msg i.val)) := by
  simp only [wotsSignWithSecret, Wots.Program.runTops_sign,
    Wots.Program.runChains_eq, chainWith]

/-- At the honest provider provider-parametric WOTS+ signing is `wotsSignWith`. -/
theorem wotsSignWithSecret_eq_wotsSignWith {m : Type → Type*} [Monad m] [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y) (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) :
    wotsSignWithSecret core hash (fun a => pure (core.PRF pk sk a)) msg adrs =
      wotsSignWith core hash msg sk pk adrs := by
  simp only [wotsSignWithSecret_eq, wotsSignWith_eq, pure_bind]

/-- The WOTS+ public key at `adrs` (FIPS 205 Algorithm 6): the provider-parametric chain ends
compressed by `T_len` at `wotsPkAdrs adrs`. -/
@[expose] def wotsPkGenWithSecret {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (secret : Adrs → m core.Y) (adrs : Adrs) : m core.Y :=
  Wots.Program.run (I := Fin p.len) Vector.ofFnM
    (fun i => secret (wotsSkAdrs adrs i.val))
    (fun i j y => hash ((wotsChainAdrs adrs i.val).setHashAddress j) y)
    (fun tops => compress (wotsPkAdrs adrs) tops.toList) (p.w - 1) .publicKey

/-- Provider public-key compression follows the provider-generated native chain tops. -/
theorem wotsPkGenWithSecret_eq {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (secret : Adrs → m core.Y) (adrs : Adrs) :
    wotsPkGenWithSecret core hash compress secret adrs = (do
      let tops ← wotsPkGenTopsWithSecret core hash secret adrs
      compress (wotsPkAdrs adrs) tops.toList) := by
  simp only [wotsPkGenWithSecret, wotsPkGenTopsWithSecret, Wots.Program.run_publicKey]

/-- At the honest provider the provider-parametric WOTS+ public key is `wotsPkGenWith`. -/
theorem wotsPkGenWithSecret_eq_wotsPkGenWith {m : Type → Type*} [Monad m] [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    wotsPkGenWithSecret core hash compress (fun a => pure (core.PRF pk sk a)) adrs =
      wotsPkGenWith core hash compress sk pk adrs := by
  rw [wotsPkGenWithSecret_eq, wotsPkGenWith_eq, wotsPkGenTopsWithSecret_eq_wotsPkGenTopsWith]

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
provider's value at the indexed leaf's `FORS_PRF` address, then the authentication path through
the provider-parametric tree, in the order FIPS 205 evaluates them. -/
@[expose] def forsSignWithSecret {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (secret : Adrs → m core.Y) (md : List Byte) (adrs : Adrs) : m (ForsSigCore p core) :=
  Vector.ofFnM fun i : Fin p.k => do
    let idx := i.val * 2 ^ p.a + forsIdx p md i.val
    let sk ← secret (forsSkAdrs adrs idx)
    let path ← PerfectMerkleTree.intrinsicAuthPathM (forsLeafWithSecret core hash secret adrs)
      (forsNodeHashWith nodeHash adrs) idx p.a
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

/-! ## Naturality of the WOTS+, XMSS and FORS twins -/

/-- A monad morphism commutes with the provider-parametric WOTS+ chain ends when it commutes with
the hash callback and with the provider at secret-key addresses. -/
theorem wotsPkGenTopsWithSecret_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (secretm : Adrs → m core.Y) (secretn : Adrs → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hsecret : ∀ a, a.IsSecretKey → F (secretm a) = secretn a)
    (adrs : Adrs) :
    F (wotsPkGenTopsWithSecret core hashm secretm adrs) =
      wotsPkGenTopsWithSecret core hashn secretn adrs := by
  simp only [wotsPkGenTopsWithSecret_eq]
  apply Vector.ofFnM_natural F
  intro i
  rw [F.mmap_bind, hsecret _ (Adrs.isSecretKey_wotsSkAdrs _ _)]
  exact bind_congr fun x => chainWith_natural F hashm hashn hhash _ _ _ _

/-- A monad morphism commutes with provider-parametric WOTS+ signing when it commutes with the
hash callback and with the provider at secret-key addresses. -/
theorem wotsSignWithSecret_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (secretm : Adrs → m core.Y) (secretn : Adrs → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hsecret : ∀ a, a.IsSecretKey → F (secretm a) = secretn a)
    (msg : core.Y) (adrs : Adrs) :
    F (wotsSignWithSecret core hashm secretm msg adrs) =
      wotsSignWithSecret core hashn secretn msg adrs := by
  simp only [wotsSignWithSecret_eq]
  apply Vector.ofFnM_natural F
  intro i
  rw [F.mmap_bind, hsecret _ (Adrs.isSecretKey_wotsSkAdrs _ _)]
  exact bind_congr fun x => chainWith_natural F hashm hashn hhash _ _ _ _

/-- A monad morphism commutes with provider-parametric WOTS+ public-key generation when it
commutes with the hash and compression callbacks and with the provider at secret-key addresses. -/
theorem wotsPkGenWithSecret_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (compressm : Adrs → List core.Y → m core.Y) (compressn : Adrs → List core.Y → n core.Y)
    (secretm : Adrs → m core.Y) (secretn : Adrs → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (hsecret : ∀ a, a.IsSecretKey → F (secretm a) = secretn a) (adrs : Adrs) :
    F (wotsPkGenWithSecret core hashm compressm secretm adrs) =
      wotsPkGenWithSecret core hashn compressn secretn adrs := by
  rw [wotsPkGenWithSecret_eq, wotsPkGenWithSecret_eq, F.mmap_bind,
    wotsPkGenTopsWithSecret_natural core F hashm hashn secretm secretn hhash hsecret]
  exact bind_congr fun tops => hcompress _ _

/-- A monad morphism commutes with a provider-parametric XMSS leaf when it commutes with the
hash and compression callbacks and with the provider at secret-key addresses. -/
theorem xmssLeafWithSecret_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (compressm : Adrs → List core.Y → m core.Y) (compressn : Adrs → List core.Y → n core.Y)
    (secretm : Adrs → m core.Y) (secretn : Adrs → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (hsecret : ∀ a, a.IsSecretKey → F (secretm a) = secretn a) (adrs : Adrs) (t : ℕ) :
    F (xmssLeafWithSecret core hashm compressm secretm adrs t) =
      xmssLeafWithSecret core hashn compressn secretn adrs t :=
  wotsPkGenWithSecret_natural core F hashm hashn compressm compressn secretm secretn
    hhash hcompress hsecret (wotsLeafAdrs adrs t)

/-- A monad morphism commutes with a provider-parametric XMSS subtree root when it commutes with
every callback and with the provider at secret-key addresses. -/
theorem xmssNodeWithSecret_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (compressm : Adrs → List core.Y → m core.Y) (compressn : Adrs → List core.Y → n core.Y)
    (nodeHashm : Adrs → core.Y → core.Y → m core.Y)
    (nodeHashn : Adrs → core.Y → core.Y → n core.Y)
    (secretm : Adrs → m core.Y) (secretn : Adrs → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (hsecret : ∀ a, a.IsSecretKey → F (secretm a) = secretn a) (adrs : Adrs) (z t : ℕ) :
    F (xmssNodeWithSecret core hashm compressm nodeHashm secretm adrs z t) =
      xmssNodeWithSecret core hashn compressn nodeHashn secretn adrs z t := by
  apply PerfectMerkleTree.merkleRootM_natural F
  · intro i
    exact xmssLeafWithSecret_natural core F hashm hashn compressm compressn secretm secretn
      hhash hcompress hsecret adrs i
  · intro h i l r
    exact xmssNodeHashWith_natural F nodeHashm nodeHashn hnode adrs h i l r

/-- A monad morphism commutes with the provider-parametric XMSS root when it commutes with every
callback and with the provider at secret-key addresses. -/
theorem xmssRootWithSecret_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (compressm : Adrs → List core.Y → m core.Y) (compressn : Adrs → List core.Y → n core.Y)
    (nodeHashm : Adrs → core.Y → core.Y → m core.Y)
    (nodeHashn : Adrs → core.Y → core.Y → n core.Y)
    (secretm : Adrs → m core.Y) (secretn : Adrs → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (hsecret : ∀ a, a.IsSecretKey → F (secretm a) = secretn a) (adrs : Adrs) :
    F (xmssRootWithSecret core hashm compressm nodeHashm secretm adrs) =
      xmssRootWithSecret core hashn compressn nodeHashn secretn adrs :=
  xmssNodeWithSecret_natural core F hashm hashn compressm compressn nodeHashm nodeHashn
    secretm secretn hhash hcompress hnode hsecret adrs p.hp 0

/-- A monad morphism commutes with provider-parametric XMSS signing when it commutes with every
callback and with the provider at secret-key addresses. -/
theorem xmssSignWithSecret_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (compressm : Adrs → List core.Y → m core.Y) (compressn : Adrs → List core.Y → n core.Y)
    (nodeHashm : Adrs → core.Y → core.Y → m core.Y)
    (nodeHashn : Adrs → core.Y → core.Y → n core.Y)
    (secretm : Adrs → m core.Y) (secretn : Adrs → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (hsecret : ∀ a, a.IsSecretKey → F (secretm a) = secretn a)
    (msg : core.Y) (adrs : Adrs) (idx : ℕ) :
    F (xmssSignWithSecret core hashm compressm nodeHashm secretm msg adrs idx) =
      xmssSignWithSecret core hashn compressn nodeHashn secretn msg adrs idx := by
  rw [xmssSignWithSecret, xmssSignWithSecret, F.mmap_bind,
    PerfectMerkleTree.intrinsicAuthPathM_natural F _ _
      (xmssLeafWithSecret core hashn compressn secretn adrs)
      (xmssNodeHashWith nodeHashn adrs)
      (fun i => xmssLeafWithSecret_natural core F hashm hashn compressm compressn secretm secretn
        hhash hcompress hsecret adrs i)
      (fun h i l r => xmssNodeHashWith_natural F nodeHashm nodeHashn hnode adrs h i l r)]
  refine bind_congr fun path => ?_
  rw [F.mmap_bind, wotsSignWithSecret_natural core F hashm hashn secretm secretn hhash hsecret]
  exact bind_congr fun sig => F.mmap_pure _

/-- A monad morphism commutes with a provider-parametric FORS leaf when it commutes with the
leaf-hash callback and with the provider at secret-key addresses. -/
theorem forsLeafWithSecret_natural {m n : Type → Type*} [Monad m] [Monad n] (F : m →ᵐ n)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (secretm : Adrs → m core.Y) (secretn : Adrs → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hsecret : ∀ a, a.IsSecretKey → F (secretm a) = secretn a)
    (adrs : Adrs) (t : ℕ) :
    F (forsLeafWithSecret core hashm secretm adrs t) =
      forsLeafWithSecret core hashn secretn adrs t := by
  rw [forsLeafWithSecret, forsLeafWithSecret, F.mmap_bind,
    hsecret _ (Adrs.isSecretKey_forsSkAdrs _ _)]
  exact bind_congr fun x => hhash _ _

/-- A monad morphism commutes with a provider-parametric FORS tree root when it commutes with the
leaf and node callbacks and with the provider at secret-key addresses. -/
theorem forsRootWithSecret_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (nodeHashm : Adrs → core.Y → core.Y → m core.Y)
    (nodeHashn : Adrs → core.Y → core.Y → n core.Y)
    (secretm : Adrs → m core.Y) (secretn : Adrs → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (hsecret : ∀ a, a.IsSecretKey → F (secretm a) = secretn a) (adrs : Adrs) (i : ℕ) :
    F (forsRootWithSecret core hashm nodeHashm secretm adrs i) =
      forsRootWithSecret core hashn nodeHashn secretn adrs i :=
  PerfectMerkleTree.merkleRootM_natural F _ _ _ _
    (fun t => forsLeafWithSecret_natural core F hashm hashn secretm secretn hhash hsecret adrs t)
    (fun z t l r => forsNodeHashWith_natural F nodeHashm nodeHashn hnode adrs z t l r) _ _

/-- A monad morphism commutes with provider-parametric FORS public-key generation when it
commutes with every callback and with the provider at secret-key addresses. -/
theorem forsPkGenWithSecret_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (nodeHashm : Adrs → core.Y → core.Y → m core.Y)
    (nodeHashn : Adrs → core.Y → core.Y → n core.Y)
    (compressm : Adrs → List core.Y → m core.Y) (compressn : Adrs → List core.Y → n core.Y)
    (secretm : Adrs → m core.Y) (secretn : Adrs → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (hsecret : ∀ a, a.IsSecretKey → F (secretm a) = secretn a) (adrs : Adrs) :
    F (forsPkGenWithSecret core hashm nodeHashm compressm secretm adrs) =
      forsPkGenWithSecret core hashn nodeHashn compressn secretn adrs := by
  rw [forsPkGenWithSecret, forsPkGenWithSecret, F.mmap_bind,
    Vector.ofFnM_natural F _ _ (fun i : Fin p.k => forsRootWithSecret_natural core F hashm hashn
      nodeHashm nodeHashn secretm secretn hhash hnode hsecret adrs i.val)]
  exact bind_congr fun roots => hcompress _ _

/-- A monad morphism commutes with provider-parametric FORS signing when it commutes with the
leaf and node callbacks and with the provider at secret-key addresses. -/
theorem forsSignWithSecret_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (nodeHashm : Adrs → core.Y → core.Y → m core.Y)
    (nodeHashn : Adrs → core.Y → core.Y → n core.Y)
    (secretm : Adrs → m core.Y) (secretn : Adrs → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (hsecret : ∀ a, a.IsSecretKey → F (secretm a) = secretn a) (md : List Byte) (adrs : Adrs) :
    F (forsSignWithSecret core hashm nodeHashm secretm md adrs) =
      forsSignWithSecret core hashn nodeHashn secretn md adrs := by
  apply Vector.ofFnM_natural F
  intro i
  rw [F.mmap_bind, hsecret _ (Adrs.isSecretKey_forsSkAdrs _ _)]
  refine bind_congr fun sk => ?_
  rw [F.mmap_bind, PerfectMerkleTree.intrinsicAuthPathM_natural F _ _
    (forsLeafWithSecret core hashn secretn adrs) (forsNodeHashWith nodeHashn adrs)
    (fun t => forsLeafWithSecret_natural core F hashm hashn secretm secretn hhash hsecret adrs t)
    (fun z t l r => forsNodeHashWith_natural F nodeHashm nodeHashn hnode adrs z t l r)]
  exact bind_congr fun path => F.mmap_pure _

/-- A query-preserving monad morphism commutes with provider-parametric FORS signing when it
commutes with the provider at secret-key addresses. -/
theorem forsSignWithSecretM_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n] (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (secretm : Adrs → m core.Y) (secretn : Adrs → n core.Y)
    (hsecret : ∀ a, a.IsSecretKey → F.toMonadHom (secretm a) = secretn a)
    (md : List Byte) (pkSeed : core.PkSeed) (adrs : Adrs) :
    F.toMonadHom (forsSignWithSecretM core secretm md pkSeed adrs) =
      forsSignWithSecretM core secretn md pkSeed adrs :=
  forsSignWithSecret_natural core F.toMonadHom _ _ _ _ secretm secretn
    (PublicHash.f_natural core F pkSeed) (PublicHash.h_natural core F pkSeed) hsecret md adrs

end SLHDSA

namespace SLHDSA.GeneralHypertree

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-- The hypertree signature of `msg` from layer position `pos` upward over `layers` layers
(FIPS 205 Algorithm 12), with every XMSS signature produced by `xmssSignWithSecret`. `recoverFinal`
requests discarded recovery only for a singleton entry. Nonfinal recursion resets it to false. -/
@[expose] def signFromPositionWithSecret {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (secret : Adrs → m core.Y) (recoverFinal : Bool) (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → core.Y →
      m (Vector (XmssSig vp.params core) layers) :=
  fun layers remaining message =>
    Hypertree.Program.signLayers (nextRemainingPosition vp)
      (fun _ current value =>
        xmssSignWithSecret core hash compress nodeHash secret value current.val.toAdrs
          current.val.leaf.val)
      (fun _ current signature value =>
        xmssPkFromSigWith core hash compress nodeHash current.val.leaf.val signature value
          current.val.toAdrs)
      recoverFinal layers ⟨pos, remaining⟩ message

/-- The zero component equation for the typed signer. -/
theorem signFromPositionWithSecret_zero {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (secret : Adrs → m core.Y) (recoverFinal : Bool) (pos : LayerPosition vp)
    (remaining : pos.layer.val + (0) = vp.params.d) (message : core.Y) :
    signFromPositionWithSecret core hash compress nodeHash secret recoverFinal pos (0)
      remaining message =
      (pure #v[] : m (Vector (XmssSig vp.params core) (0))) := rfl

/-- The one component equation for the typed signer. -/
theorem signFromPositionWithSecret_one {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (secret : Adrs → m core.Y) (recoverFinal : Bool) (pos : LayerPosition vp)
    (remaining : pos.layer.val + (1) = vp.params.d) (message : core.Y) :
    signFromPositionWithSecret core hash compress nodeHash secret recoverFinal pos (1)
      remaining message =
      (do
        let sig ← xmssSignWithSecret core hash compress nodeHash secret message
          pos.toAdrs pos.leaf.val
        if recoverFinal then
          let _ ← xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sig message pos.toAdrs
          return #v[sig]
        else
          return #v[sig] : m (Vector (XmssSig vp.params core) (1))) := rfl

/-- The add two component equation for the typed signer. -/
theorem signFromPositionWithSecret_add_two {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (secret : Adrs → m core.Y) (recoverFinal : Bool) (pos : LayerPosition vp)
    (layers : Nat) (remaining : pos.layer.val + (layers + 2) = vp.params.d) (message : core.Y) :
    signFromPositionWithSecret core hash compress nodeHash secret recoverFinal pos
      (layers + 2) remaining message =
      (do
        let sig ← xmssSignWithSecret core hash compress nodeHash secret message
          pos.toAdrs pos.leaf.val
        let root ←
          xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sig message pos.toAdrs
        let next := pos.next (by omega)
        let rest ← signFromPositionWithSecret core hash compress nodeHash secret false next
          (layers + 1) (by simp [next]; omega) root
        return rest.insertIdx 0 sig : m (Vector (XmssSig vp.params core) (layers + 2))) := rfl

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
  | 0, _, _ => by rw [signFromPositionWithSecret_zero, signFromPositionWith_zero]
  | 1, _, msg => by
      rw [signFromPositionWithSecret_one, signFromPositionWith_one,
        xmssSignWithSecret_eq_xmssSignWith]
  | layers + 2, hremaining, msg => by
      rw [signFromPositionWithSecret_add_two, signFromPositionWith_add_two,
        xmssSignWithSecret_eq_xmssSignWith]
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
  rw [signWithSecretM, signWithSecret_eq_signWith]
  rfl

/-- At the honest provider the provider-parametric hypertree root is `rootM`. -/
theorem rootWithSecretM_eq_rootM {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec core) m] (skSeed : core.SkSeed) (pkSeed : core.PkSeed) :
    rootWithSecretM core (fun a => pure (core.PRF pkSeed skSeed a)) pkSeed =
      (rootM vp core skSeed pkSeed : m core.Y) := by
  rw [rootWithSecretM, rootM, rootWithSecret_eq_rootWith]

/-! ## Naturality of the hypertree twins -/

/-- A monad morphism commutes with provider-parametric hypertree signing from a position when it
commutes with every callback and with the provider at secret-key addresses. -/
theorem signFromPositionWithSecret_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (compressm : Adrs → List core.Y → m core.Y) (compressn : Adrs → List core.Y → n core.Y)
    (nodeHashm : Adrs → core.Y → core.Y → m core.Y)
    (nodeHashn : Adrs → core.Y → core.Y → n core.Y)
    (secretm : Adrs → m core.Y) (secretn : Adrs → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (hsecret : ∀ a, a.IsSecretKey → F (secretm a) = secretn a)
    (recoverFinal : Bool) (pos : LayerPosition vp) :
    ∀ (layers : ℕ) (h : pos.layer.val + layers = vp.params.d) (msg : core.Y),
      F (signFromPositionWithSecret core hashm compressm nodeHashm secretm recoverFinal pos
          layers h msg) =
        signFromPositionWithSecret core hashn compressn nodeHashn secretn recoverFinal pos
          layers h msg
  | 0, _, _ => by
      rw [signFromPositionWithSecret_zero, signFromPositionWithSecret_zero, F.mmap_pure]
  | 1, _, msg => by
      rw [signFromPositionWithSecret_one, signFromPositionWithSecret_one, F.mmap_bind,
        xmssSignWithSecret_natural core F hashm hashn compressm compressn nodeHashm nodeHashn
          secretm secretn hhash hcompress hnode hsecret]
      refine bind_congr fun sig => ?_
      cases recoverFinal with
      | false => simp only [Bool.false_eq_true, reduceIte, F.mmap_pure]
      | true =>
          simp only [reduceIte, F.mmap_bind,
            xmssPkFromSigWith_natural F core hashm hashn compressm compressn nodeHashm nodeHashn
              hhash hcompress hnode]
          exact bind_congr fun _ => F.mmap_pure _
  | layers + 2, hremaining, msg => by
      rw [signFromPositionWithSecret_add_two, signFromPositionWithSecret_add_two, F.mmap_bind,
        xmssSignWithSecret_natural core F hashm hashn compressm compressn nodeHashm nodeHashn
          secretm secretn hhash hcompress hnode hsecret]
      refine bind_congr fun sig => ?_
      rw [F.mmap_bind, xmssPkFromSigWith_natural F core hashm hashn compressm compressn
        nodeHashm nodeHashn hhash hcompress hnode]
      refine bind_congr fun root => ?_
      refine (F.mmap_bind _ _).trans ?_
      rw [signFromPositionWithSecret_natural F hashm hashn compressm compressn
        nodeHashm nodeHashn secretm secretn hhash hcompress hnode hsecret false _ (layers + 1)]
      exact bind_congr fun rest => F.mmap_pure _

/-- A monad morphism commutes with provider-parametric hypertree signing when it commutes with
every callback and with the provider at secret-key addresses. -/
theorem signWithSecret_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (compressm : Adrs → List core.Y → m core.Y) (compressn : Adrs → List core.Y → n core.Y)
    (nodeHashm : Adrs → core.Y → core.Y → m core.Y)
    (nodeHashn : Adrs → core.Y → core.Y → n core.Y)
    (secretm : Adrs → m core.Y) (secretn : Adrs → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (hsecret : ∀ a, a.IsSecretKey → F (secretm a) = secretn a)
    (msg : core.Y) (parts : DigestParts vp.params) :
    F (signWithSecret core hashm compressm nodeHashm secretm msg parts) =
      signWithSecret core hashn compressn nodeHashn secretn msg parts :=
  signFromPositionWithSecret_natural core F hashm hashn compressm compressn nodeHashm nodeHashn
    secretm secretn hhash hcompress hnode hsecret _ _ _ _ _

/-- A monad morphism commutes with the provider-parametric hypertree root when it commutes with
every callback and with the provider at secret-key addresses. -/
theorem rootWithSecret_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (compressm : Adrs → List core.Y → m core.Y) (compressn : Adrs → List core.Y → n core.Y)
    (nodeHashm : Adrs → core.Y → core.Y → m core.Y)
    (nodeHashn : Adrs → core.Y → core.Y → n core.Y)
    (secretm : Adrs → m core.Y) (secretn : Adrs → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (hsecret : ∀ a, a.IsSecretKey → F (secretm a) = secretn a) :
    F (rootWithSecret core hashm compressm nodeHashm secretm) =
      rootWithSecret core hashn compressn nodeHashn secretn :=
  xmssRootWithSecret_natural core F hashm hashn compressm compressn nodeHashm nodeHashn
    secretm secretn hhash hcompress hnode hsecret _

/-- A query-preserving monad morphism commutes with provider-parametric hypertree signing when it
commutes with the provider at secret-key addresses. -/
theorem signWithSecretM_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n] (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (secretm : Adrs → m core.Y) (secretn : Adrs → n core.Y)
    (hsecret : ∀ a, a.IsSecretKey → F.toMonadHom (secretm a) = secretn a)
    (msg : core.Y) (pkSeed : core.PkSeed) (parts : DigestParts vp.params) :
    F.toMonadHom (signWithSecretM core secretm msg pkSeed parts) =
      signWithSecretM core secretn msg pkSeed parts :=
  signWithSecret_natural core F.toMonadHom _ _ _ _ _ _ secretm secretn
    (PublicHash.f_natural core F pkSeed) (PublicHash.tl_natural core F pkSeed)
    (PublicHash.h_natural core F pkSeed) hsecret msg parts

/-- A query-preserving monad morphism commutes with the provider-parametric hypertree root when
it commutes with the provider at secret-key addresses. -/
theorem rootWithSecretM_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n] (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (secretm : Adrs → m core.Y) (secretn : Adrs → n core.Y)
    (hsecret : ∀ a, a.IsSecretKey → F.toMonadHom (secretm a) = secretn a) (pkSeed : core.PkSeed) :
    F.toMonadHom (rootWithSecretM core secretm pkSeed) = rootWithSecretM core secretn pkSeed :=
  rootWithSecret_natural core F.toMonadHom _ _ _ _ _ _ secretm secretn
    (PublicHash.f_natural core F pkSeed) (PublicHash.tl_natural core F pkSeed)
    (PublicHash.h_natural core F pkSeed) hsecret

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

/-- FIPS 205 Algorithm 19 with every WOTS+ and FORS secret drawn from the provider `secret` and
the message randomizer `R` supplied: neither secret seed appears. -/
@[expose] def signInternalWithSecretRandomizerM {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (secret : Adrs → m core.Y) (msg : List Byte) (pkSeed : core.PkSeed) (pkRoot : core.Y)
    (R : core.Y) : m (SignatureCore vp core) :=
  Scheme.Program.sign (PublicHash.hmsg core R pkSeed pkRoot msg) (splitDigest vp.params)
    (fun parts => forsSignWithSecretM core secret parts.md.toList pkSeed parts.forsAdrs)
    (fun parts signature => forsPkFromSigM core signature parts.md.toList pkSeed parts.forsAdrs)
    (fun parts root => GeneralHypertree.signWithSecretM core secret root pkSeed parts)
    (fun forsSignature hypertreeSignature => ⟨R, forsSignature, hypertreeSignature⟩)

/-- At the honest provider provider-parametric signing at a supplied randomizer is
`signInternalWithRandomizerM`. -/
theorem signInternalWithSecretRandomizerM_eq_signInternalWithRandomizerM {m : Type → Type*}
    [Monad m] [LawfulMonad m] [HasQuery (publicHashSpec core) m] (skSeed : core.SkSeed)
    (pkSeed : core.PkSeed) (msg : List Byte) (pkRoot R : core.Y) :
    signInternalWithSecretRandomizerM core (fun a => pure (core.PRF pkSeed skSeed a)) msg pkSeed
        pkRoot R =
      (signInternalWithRandomizerM vp core msg skSeed pkSeed pkRoot R :
        m (SignatureCore vp core)) := by
  rw [signInternalWithSecretRandomizerM, signInternalWithRandomizerM]
  simp only [forsSignWithSecretM_eq_forsSignM, GeneralHypertree.signWithSecretM_eq_signM]

/-! ## Naturality of the scheme twins -/

/-- A query-preserving monad morphism commutes with provider-parametric key generation when it
commutes with the provider at secret-key addresses. -/
theorem keygenInternalWithSecretM_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n] (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (secretm : Adrs → m core.Y) (secretn : Adrs → n core.Y)
    (hsecret : ∀ a, a.IsSecretKey → F.toMonadHom (secretm a) = secretn a) (pkSeed : core.PkSeed) :
    F.toMonadHom (keygenInternalWithSecretM core secretm pkSeed) =
      keygenInternalWithSecretM core secretn pkSeed :=
  GeneralHypertree.rootWithSecretM_natural core F secretm secretn hsecret pkSeed

/-- A query-preserving monad morphism commutes with provider-parametric signing at a supplied
randomizer when it commutes with the provider at secret-key addresses. -/
theorem signInternalWithSecretRandomizerM_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n] (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (secretm : Adrs → m core.Y) (secretn : Adrs → n core.Y)
    (hsecret : ∀ a, a.IsSecretKey → F.toMonadHom (secretm a) = secretn a)
    (msg : List Byte) (pkSeed : core.PkSeed) (pkRoot R : core.Y) :
    F.toMonadHom (signInternalWithSecretRandomizerM core secretm msg pkSeed pkRoot R) =
      signInternalWithSecretRandomizerM core secretn msg pkSeed pkRoot R := by
  unfold signInternalWithSecretRandomizerM Scheme.Program.sign
  rw [F.toMonadHom.mmap_bind, PublicHash.hmsg_natural core F]
  refine bind_congr fun digest => ?_
  rw [F.toMonadHom.mmap_bind, forsSignWithSecretM_natural core F secretm secretn hsecret]
  refine bind_congr fun forsSig => ?_
  rw [F.toMonadHom.mmap_bind, forsPkFromSigM_natural core F]
  refine bind_congr fun forsPk => ?_
  rw [F.toMonadHom.mmap_bind,
    GeneralHypertree.signWithSecretM_natural core F secretm secretn hsecret]
  exact bind_congr fun htSig => F.toMonadHom.mmap_pure _

end GeneralScheme

end SLHDSA
