/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.CacheSecret

/-!
# The random-oracle scheme at a deterministic primitive bundle

`romScheme` of `HashSig.SLHDSA.Security.Target` draws every WOTS+ and FORS secret from the
tweakable-hash oracle at a `PRF` address, and its randomizer from the `PRF_msg` oracle. This module
answers the three oracles by a deterministic primitive bundle and identifies the result with
FIPS 205's internal algorithms at that bundle. The secret draws become the honest provider
`fun a => pure (prims.PRF pkSeed skSeed a)` when the bundle's tweakable hash at a
secret-key address, applied to the secret seed read as a node, is its `PRF`; the provider-parametric
programs then are the landed ones (the `*_eq_*` equations of `HashSig.SLHDSA.SecretProvider`).

## Main definitions

* `Security.romAnswer prims`: the answer function of `hashSpec prims.core` given by a bundle: the
  tweakable hash and `H_msg` by `PublicHash.impl prims`, `PRF_msg` by `prims.PRFmsg`.
* `Security.internalAlg vp prims optRand pkSeedDist`: FIPS 205 Algorithms 18–20 as a signature
  scheme over `ProbComp`, built from `GeneralScheme.keygenInternal`, `signInternal` and
  `verifyInternal`, with the public seed drawn from `pkSeedDist`, the secret seeds uniformly, and
  `opt_rand` from `optRand`.

## Main statements

* `Security.romScheme_map_romAnswer`: when the tweakable hash of `prims` at a secret-key address
  applied to `e SK.seed` is `prims.PRF`, answering the oracles of `romScheme prims.core e` by
  `romAnswer prims` gives `internalAlg vp prims`.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.Security

variable {vp : ValidatedParams}

/-- The answer function of the random-oracle interface given by a deterministic primitive
bundle: the tweakable hash and `H_msg` by `PublicHash.impl prims`, and `PRF_msg` by
`prims.PRFmsg`. -/
@[expose] def romAnswer (prims : Primitives vp.params) : QueryImpl (hashSpec prims.core) Id
  | .inl q => PublicHash.impl prims q
  | .inr q => prims.PRFmsg q.skPrf q.optRand q.msg

/-- **FIPS 205 Algorithms 18–20 as a signature scheme.** Key generation draws the public seed
from `pkSeedDist` and the two secret seeds uniformly and returns
`GeneralScheme.keygenInternal`; signing draws `opt_rand` from `optRand` and returns
`GeneralScheme.signInternal`; verification is `GeneralScheme.verifyInternal`. -/
@[expose] noncomputable def internalAlg (vp : ValidatedParams) (prims : Primitives vp.params)
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [DecidableEq prims.Y]
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    SignatureAlg ProbComp (List Byte) (PublicKeyCore prims.core) (SecretKeyCore prims.core)
      (GeneralScheme.SignatureCore vp prims.core) where
  keygen := do
    let pkSeed ← pkSeedDist
    let skSeed ← $ᵗ prims.SkSeed
    let skPrf ← $ᵗ prims.SkPrf
    pure (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed)
  sign pk sk msg := do
    let addrnd ← optRand pk
    pure (GeneralScheme.signInternal vp prims msg sk addrnd)
  verify pk msg sig := pure (GeneralScheme.verifyInternal vp prims msg sig pk)

section Conformance

variable (prims : Primitives vp.params) [SampleableType prims.SkSeed]
  [SampleableType prims.SkPrf] [DecidableEq prims.Y]

/-- **The random-oracle scheme at a deterministic bundle is FIPS 205.** If the tweakable hash of
`prims` at every secret-key address, applied to the secret seed read as a node through `e`, is
`prims.PRF`, then answering the oracles of `romScheme prims.core e` by `romAnswer prims` and
keeping its uniform draws gives `internalAlg vp prims`, for every `opt_rand` source and every
public-seed distribution. -/
theorem romScheme_map_romAnswer (e : prims.SkSeed ≃ prims.Y)
    (hprf : ∀ pkSeed skSeed (a : Adrs), a.IsSecretKey →
      prims.Thash pkSeed (prims.adrsToKey a) [e skSeed] = prims.PRF pkSeed skSeed a)
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    (romScheme prims.core e optRand pkSeedDist).map
        (simulateQ' (unifFwdAnswerImpl (romAnswer prims))) =
      internalAlg vp prims optRand pkSeedDist := by
  let _ : HasQuery (publicHashSpec prims.core) ProbComp :=
    ⟨fun q => liftM (PublicHash.impl prims q)⟩
  let F : HasQuery.QueryHom (publicHashSpec prims.core)
      (OracleComp (unifSpec + hashSpec prims.core)) ProbComp :=
    { toMonadHom := simulateQ' (unifFwdAnswerImpl (romAnswer prims))
      map_query' := fun q => by
        simp [unifFwdAnswerImpl, romAnswer] }
  have hLift : ∀ {α : Type} (oa : ProbComp α),
      F.toMonadHom (liftM oa : OracleComp (unifSpec + hashSpec prims.core) α) = oa := by
    intro α oa
    change simulateQ (unifFwdAnswerImpl (romAnswer prims)) _ = oa
    rw [unifFwdAnswerImpl, QueryImpl.passthrough_add, QueryImpl.simulateQ_add_liftM_left,
      QueryImpl.liftTarget_self, simulateQ_id']
  have hFree : ∀ {α : Type} (oa : OracleComp (publicHashSpec prims.core) α),
      (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core)
        (m := ProbComp)).toMonadHom oa = pure (simulateQ (PublicHash.impl prims) oa) := by
    intro α oa
    have hImpl : HasQuery.toQueryImpl (spec := publicHashSpec prims.core) (m := ProbComp) =
        (PublicHash.impl prims).liftTarget ProbComp := by
      funext q
      rfl
    rw [HasQuery.QueryHom.ofSimulateQ_apply, hImpl, simulateQ_liftTarget]
    rfl
  have hSecret : ∀ pkSeed skSeed (a : Adrs), a.IsSecretKey →
      F.toMonadHom (oracleSecret prims.core e pkSeed skSeed a) =
        (pure (prims.PRF pkSeed skSeed a) : ProbComp prims.Y) := by
    intro pkSeed skSeed a ha
    rw [oracleSecret_natural prims.core F e pkSeed skSeed a]
    change (pure (prims.Thash pkSeed (prims.adrsToKey a) [e skSeed]) : ProbComp prims.Y) = _
    rw [hprf pkSeed skSeed a ha]
  apply SignatureAlg.ext
  · change F.toMonadHom (liftM pkSeedDist >>= romKeygenAt prims.core e) = _
    rw [F.toMonadHom.mmap_bind, hLift]
    refine bind_congr fun pkSeed => ?_
    rw [romKeygenAt, F.toMonadHom.mmap_bind, hLift]
    refine bind_congr fun skSeed => ?_
    rw [F.toMonadHom.mmap_bind, hLift]
    refine bind_congr fun skPrf => ?_
    rw [F.toMonadHom.mmap_bind, GeneralScheme.keygenInternalWithSecretM_natural prims.core F _ _
      (hSecret pkSeed skSeed), GeneralScheme.keygenInternalWithSecretM,
      GeneralHypertree.rootWithSecretM_eq_rootM,
      ← GeneralHypertree.rootM_natural vp prims.core
        (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp)),
      hFree, pure_bind, F.toMonadHom.mmap_pure]
    congr 1
    exact Prod.ext (GeneralScheme.keygenInternal_fst vp prims skSeed skPrf pkSeed).symm
      (GeneralScheme.keygenInternal_snd vp prims skSeed skPrf pkSeed).symm
  · funext pk sk msg
    change F.toMonadHom ((romScheme prims.core e optRand pkSeedDist).sign pk sk msg) = _
    rw [romScheme_sign, F.toMonadHom.mmap_bind, hLift]
    refine bind_congr fun addrnd => ?_
    have hR : F.toMonadHom (query (spec := prfMsgSpec prims.core) ⟨sk.skPrf, addrnd, msg⟩ :
        OracleComp (unifSpec + hashSpec prims.core) prims.Y) =
          pure (prims.PRFmsg sk.skPrf addrnd msg) := by
      simp [F, unifFwdAnswerImpl, romAnswer]
      rfl
    rw [F.toMonadHom.mmap_bind, hR, pure_bind,
      GeneralScheme.signInternalWithSecretRandomizerM_natural prims.core F _ _
        (hSecret sk.pkSeed sk.skSeed),
      GeneralScheme.signInternalWithSecretRandomizerM_eq_signInternalWithRandomizerM,
      ← GeneralScheme.signInternalM_eq_signInternalWithRandomizerM,
      ← GeneralScheme.signInternalM_natural vp prims.core
        (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp)),
      hFree]
    rfl
  · funext pk msg sig
    change F.toMonadHom (GeneralScheme.verifyInternalM vp prims.core msg sig pk) = _
    rw [GeneralScheme.verifyInternalM_natural vp prims.core F,
      ← GeneralScheme.verifyInternalM_natural vp prims.core
        (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp)),
      hFree]
    rfl

end Conformance

end SLHDSA.Security
