/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.CountedRom

/-!
# The deterministic interpretation of `generalAlgM` is `generalAlg`

This module relates the two external SLH-DSA signature algebras of the security lane: the
oracle-parametric `SLHDSA.Security.generalAlgM` of `HashSig.SLHDSA.Security.CountedRom`, which
leaves every public-hash evaluation as a query, and the standard-model
`SLHDSA.Security.generalAlg` of `HashSig.SLHDSA.Security.SchemeGames`, which evaluates the public
hash as a function of `prims`.

`generalAlgM_map_eq` states that interpreting `generalAlgM` over `unifSpec + publicHashSpec`
with `unifFwdAnswerImpl (PublicHash.impl prims)` — uniform samples forwarded unchanged, every
public-hash query answered by `prims` — *is* `generalAlg prims`, as an equality of
`SignatureAlg`s.  The proof is the one `SLHDSA.slhdsaConcreteAlg` of `HashSig.SLHDSA.RandomOracle`
uses for the depth-one compatibility programs: the interpreting morphism is a query-preserving
`HasQuery.QueryHom`, so `GeneralScheme.keygenInternalM_natural`, `signInternalM_natural` and
`verifyInternalM_natural` move it inside each component, where the `publicHashSpec` handler is
`PublicHash.impl prims` lifted to `ProbComp` and the component collapses to the pure
`GeneralScheme.keygenInternal`, `signInternal`, `verifyInternal` that `generalAlg` is built from.

The consequence for the experiments is `unforgeableExp_toMappedAdv`: an EUF-CMA forger against
`generalAlg prims` is, unchanged, a forger against the interpreted `generalAlgM`, with the same
experiment and hence the same advantage under every runtime.  The transport is `toMappedAdv`,
which re-indexes the adversary's `main` program; no cast is involved, because `unforgeableAdv`
does not store the scheme and the four carrier types coincide.

## Scope

* The equality is between `generalAlg prims` and `generalAlgM` interpreted by a *deterministic*
  handler.  `countedRomExperiment` of `HashSig.SLHDSA.Security.CountedRom` interprets the same
  program by the lazily-sampled `PublicHash.randomOracle`; relating it, or `romGameCore`, to
  `unforgeableExp` under `PublicHash.runtime` is not done here.  The bound of
  `HashSig.SLHDSA.Security.OpenPreBound` and the counted experiment remain unconnected.
* Nothing here is quantitative.  The module proves that two descriptions of one scheme agree; it
  proves no bound and asserts nothing about the security of SLH-DSA.
* Nothing here is quantum.

## Labels

Four declarations.

*Deterministic bridge*:

* `generalAlgM_map_eq`;
* `toMappedAdv`, `unforgeableExp_toMappedAdv`, `advantage_toMappedAdv`.

## References

- NIST FIPS 205, §9, Algorithms 18--20
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec SignatureAlg

/-! ## The scheme equality -/

section Scheme

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
  [SampleableType prims.Y] [DecidableEq prims.Y]

/-- **Interpreting `generalAlgM` with the deterministic public hash recovers `generalAlg`.**

The morphism forwards `unifSpec` queries unchanged and answers every `publicHashSpec` query with
`PublicHash.impl prims`; under it key generation, signing and verification of `generalAlgM` are
exactly the three components of `generalAlg prims`.

*Deterministic bridge.* -/
theorem generalAlgM_map_eq :
    SignatureAlg.map (simulateQ' (unifFwdAnswerImpl (PublicHash.impl prims)))
        (generalAlgM (m := OracleComp (unifSpec + publicHashSpec prims.core)) vp prims.core) =
      generalAlg prims := by
  let _ : HasQuery (publicHashSpec prims.core) ProbComp :=
    ⟨fun q => liftM (PublicHash.impl prims q)⟩
  let F : HasQuery.QueryHom (publicHashSpec prims.core)
      (OracleComp (unifSpec + publicHashSpec prims.core)) ProbComp :=
    { toMonadHom := simulateQ' (unifFwdAnswerImpl (PublicHash.impl prims))
      map_query' := fun q => by
        simpa [unifFwdAnswerImpl] using
          (QueryImpl.simulateQ_add_liftM_query_right
            (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp))
            ((PublicHash.impl prims).liftTarget ProbComp) q) }
  have hLift : HasQuery.PreservesProbCompLift F.toMonadHom := by
    intro α oa
    change simulateQ (unifFwdAnswerImpl (PublicHash.impl prims))
      (liftM oa : OracleComp (unifSpec + publicHashSpec prims.core) α) = oa
    rw [unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftM_left,
      HasQuery.toQueryImpl_eq_id', simulateQ_id']
  have hImpl :
      (HasQuery.toQueryImpl (spec := publicHashSpec prims.core) (m := ProbComp)) =
        (PublicHash.impl prims).liftTarget ProbComp := by
    funext q
    rfl
  have hKeygen : ∀ skSeed skPrf pkSeed,
      (GeneralScheme.keygenInternalM vp prims.core skSeed skPrf pkSeed :
          ProbComp (PublicKeyCore prims.core × SecretKeyCore prims.core)) =
        pure (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed) := by
    intro skSeed skPrf pkSeed
    rw [← GeneralScheme.keygenInternalM_natural vp prims.core
        (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp)),
      HasQuery.QueryHom.ofSimulateQ_apply, hImpl, simulateQ_liftTarget]
    rfl
  have hSign : ∀ msg sk addrnd,
      (GeneralScheme.signInternalM vp prims.core msg sk addrnd :
          ProbComp (GeneralScheme.SignatureCore vp prims.core)) =
        pure (GeneralScheme.signInternal vp prims msg sk addrnd) := by
    intro msg sk addrnd
    rw [← GeneralScheme.signInternalM_natural vp prims.core
        (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp)),
      HasQuery.QueryHom.ofSimulateQ_apply, hImpl, simulateQ_liftTarget]
    rfl
  have hVerify : ∀ msg sig pk,
      (GeneralScheme.verifyInternalM vp prims.core msg sig pk : ProbComp Bool) =
        pure (GeneralScheme.verifyInternal vp prims msg sig pk) := by
    intro msg sig pk
    rw [← GeneralScheme.verifyInternalM_natural vp prims.core
        (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp)),
      HasQuery.QueryHom.ofSimulateQ_apply, hImpl, simulateQ_liftTarget]
    rfl
  change SignatureAlg.map F.toMonadHom
      (generalAlgM (m := OracleComp (unifSpec + publicHashSpec prims.core)) vp prims.core) = _
  apply SignatureAlg.ext
  · simp [generalAlgM_keygen, hLift ($ᵗ prims.SkSeed), hLift ($ᵗ prims.SkPrf),
      hLift ($ᵗ prims.PkSeed), GeneralScheme.keygenInternalM_natural vp prims.core F, hKeygen]
  · funext pk sk msg
    simp [generalAlgM_sign, hLift ($ᵗ prims.Y), GeneralScheme.signInternalM_natural vp prims.core F,
      hSign]
  · funext pk msg sig
    simp [generalAlgM_verify, GeneralScheme.verifyInternalM_natural vp prims.core F, hVerify]

end Scheme

/-! ## Transport of forgers -/

section Forger

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
  [SampleableType prims.Y] [DecidableEq prims.Y]

/-- A forger against `generalAlg prims`, read as a forger against `generalAlgM` interpreted by
`unifFwdAnswerImpl (PublicHash.impl prims)`.  The adversary's program is unchanged.

*Deterministic bridge.* -/
def toMappedAdv (adv : unforgeableAdv (generalAlg prims)) :
    unforgeableAdv (SignatureAlg.map (simulateQ' (unifFwdAnswerImpl (PublicHash.impl prims)))
      (generalAlgM (m := OracleComp (unifSpec + publicHashSpec prims.core)) vp prims.core)) :=
  ⟨adv.main⟩

/-- The transported forger runs the same EUF-CMA experiment as the original, under every runtime.

*Deterministic bridge.* -/
theorem unforgeableExp_toMappedAdv (runtime : ProbCompRuntime ProbComp)
    (adv : unforgeableAdv (generalAlg prims)) :
    unforgeableExp runtime (toMappedAdv prims adv) = unforgeableExp runtime adv := by
  unfold toMappedAdv
  rw [generalAlgM_map_eq]

/-- The transported forger has the advantage of the original, under every runtime.

*Deterministic bridge.* -/
theorem advantage_toMappedAdv (runtime : ProbCompRuntime ProbComp)
    (adv : unforgeableAdv (generalAlg prims)) :
    (toMappedAdv prims adv).advantage runtime = adv.advantage runtime := by
  unfold unforgeableAdv.advantage
  rw [unforgeableExp_toMappedAdv]

end Forger

end SLHDSA.Security
