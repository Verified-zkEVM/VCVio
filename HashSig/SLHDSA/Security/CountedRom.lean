/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.RandomOracle
public import HashSig.SLHDSA.Security.SchemeGames
public import VCVio.OracleComp.QueryTracking.QueryCost

/-!
# The counted random-oracle EUF-CMA experiment for SLH-DSA

This module states the SLH-DSA unforgeability experiment in a model where the public hash is
reachable only by querying one shared lazy random oracle, and where every such query is counted.

## Why the experiment is restated

`HashSig.SLHDSA.Security.SchemeGames`' `generalAlg` evaluates the public hash as a function, and
the games of `HashSig.SLHDSA.Security.CanonicalGames` hand their second-phase adversary the
public seed and the same function.  `OracleComp` carries no resource bound, so in that model two
of the hash-property advantages are provably one: `HashSigTest.SLHDSA.Composition` proves
`winningOpenPre_advantage` and `freePreAdv_advantage`, each exhibiting an adversary of advantage
exactly one against the open-preimage and the preimage game.  No bound on those two can be
established there.  The target-collision, undetectability, decisional second-preimage and
interleaved-target games are not shown winnable, and nothing bounds them either.  The bound of
`HashSig.SLHDSA.Security.OpenPreBound` is therefore an inequality between advantages rather than
a security level.

The repair is to count queries rather than to bound computation.  An adversary here is still
computationally unbounded, may use private randomness adaptively, and is restricted only by how
many public-hash queries its whole execution makes.  Brute-force inversion is then not free: it
costs queries, and the budget is what a bound is stated against.

## The experiment

`romGameCore` is the ordinary EUF-CMA game — key generation, a logged signing oracle, the
forger, then verification — written as one program over `unifSpec + publicHashSpec core`, so that
every public-hash evaluation by *any* party is a query.  `countedRomImpl` interprets it with
`PublicHash.randomOracle`, one lazily-sampled cache threaded through the entire experiment and
never reset between components or signing calls, and charges `1` to each public-hash query and
`0` to private sampling.  `countedRomExperiment` runs it from the empty cache and returns the
success bit together with the total charge.

`HasHashQueryBound adv q` then says every execution of the experiment costs at most `q`.  It is a
condition on the support, not a complexity assumption: nothing about running time or memory is
asserted, and private sampling is free.

## Scope

* The count includes key generation, signing and the final verification, not only the forger's
  own queries.  A bound stated at `q` therefore covers the honest work too.  Splitting the budget
  into adversarial and honest parts is a refinement this module does not make; `IsQueryBoundP`
  and a predicate on `publicHashSpec` queries are what such a split would use.
* The secret-key operations `PRF` and `PRF_msg` remain functions of the key and are not part of
  `publicHashSpec`; they are not modelled as random oracles and not counted.
  `HashSig.SLHDSA.Security.PrfHops` takes the `MKG_PRF` hop for `PRF_msg`; the `SKG_PRF` hop for
  `PRF` is not taken anywhere in this repository.
* `HashSig.SLHDSA.Security.PrfHops` and `HashSig.SLHDSA.Security.OpenPreBound` are stated for
  `SchemeGames.generalAlg`, whose public hash is a function.
  `HashSig.SLHDSA.Security.GeneralAlgBridge` identifies `generalAlg` with `generalAlgM`
  interpreted by the deterministic public hash; nothing relates `romGameCore` or
  `countedRomExperiment` to `unforgeableExp` under `PublicHash.runtime`.
* Nothing here is quantum.  `PublicHash.randomOracle` is a classical lazily-sampled oracle and
  the count is a classical query count, so any bound proved against this experiment is a
  classical random-oracle statement.
* **This module proves no bound.**  It defines the experiment and the budget predicate; the
  quantitative theorem is separate, and until it exists nothing here says SLH-DSA is secure.

## Labels

Eleven declarations.

*Counted random-oracle experiment*:

* `generalAlgM`, `generalAlgM_keygen`, `generalAlgM_sign`, `generalAlgM_verify`;
* `romGameCore`, `countedRomImpl`, `countedRomImpl_inl`, `countedRomImpl_inr`,
  `countedRomExperiment`;
* `romForgeAdvantage`, `HasHashQueryBound`.

## References

- NIST FIPS 205, §9, Algorithms 18--20
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec ENNReal SignatureAlg

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-! ## The oracle-parametric scheme at arbitrary depth -/

/-- **The SLH-DSA external algebra with every public-hash evaluation left as a query.**

`SLHDSA.slhdsaAlg` is the same thing over the depth-one compatibility programs and carries
`hd : p.d = 1`; this one runs `GeneralScheme`'s Algorithms 18--20 at every validated parameter
set, so it is the oracle-parametric counterpart of `SchemeGames.generalAlg` rather than a second
scheme.  Like `generalAlg` it signs and verifies `emptyContextMessage msg`.

*Counted random-oracle experiment.* -/
def generalAlgM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [MonadLiftT ProbComp m] [HasQuery (publicHashSpec core) m]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed]
    [SampleableType core.Y] [DecidableEq core.Y] :
    SignatureAlg m (List Byte) (PublicKeyCore core) (SecretKeyCore core)
      (GeneralScheme.SignatureCore vp core) where
  keygen := do
    let skSeed ← (monadLift ($ᵗ core.SkSeed) : m core.SkSeed)
    let skPrf ← (monadLift ($ᵗ core.SkPrf) : m core.SkPrf)
    let pkSeed ← (monadLift ($ᵗ core.PkSeed) : m core.PkSeed)
    GeneralScheme.keygenInternalM vp core skSeed skPrf pkSeed
  sign _pk sk msg := do
    let addrnd ← (monadLift ($ᵗ core.Y) : m core.Y)
    GeneralScheme.signInternalM vp core (emptyContextMessage msg) sk addrnd
  verify pk msg sig :=
    GeneralScheme.verifyInternalM vp core (emptyContextMessage msg) sig pk

section Equations

variable {m : Type → Type*} [Monad m] [MonadLiftT ProbComp m] [HasQuery (publicHashSpec core) m]
  [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed]
  [SampleableType core.Y] [DecidableEq core.Y]

/-- Key generation samples the three seeds privately and runs Algorithm 18 as a query program.
The body of `generalAlgM` is not exposed, so this is what a consumer rewrites with.

*Counted random-oracle experiment.* -/
@[simp] theorem generalAlgM_keygen :
    (generalAlgM (m := m) vp core).keygen = (do
      let skSeed ← (monadLift ($ᵗ core.SkSeed) : m core.SkSeed)
      let skPrf ← (monadLift ($ᵗ core.SkPrf) : m core.SkPrf)
      let pkSeed ← (monadLift ($ᵗ core.PkSeed) : m core.PkSeed)
      GeneralScheme.keygenInternalM vp core skSeed skPrf pkSeed) := by
  rfl

/-- Signing samples `addrnd` privately and runs Algorithm 19 on the *internal* message as a query
program.  The public key argument is ignored, as FIPS 205 Algorithm 19 ignores it.  The body of
`generalAlgM` is not exposed, so this is what a consumer rewrites with.

*Counted random-oracle experiment.* -/
@[simp] theorem generalAlgM_sign (pk : PublicKeyCore core) (sk : SecretKeyCore core)
    (msg : List Byte) :
    (generalAlgM (m := m) vp core).sign pk sk msg = (do
      let addrnd ← (monadLift ($ᵗ core.Y) : m core.Y)
      GeneralScheme.signInternalM vp core (emptyContextMessage msg) sk addrnd) := by
  rfl

/-- Verification runs Algorithm 20 on the *internal* message as a query program, with no private
sampling.  The body of `generalAlgM` is not exposed, so this is what a consumer rewrites with.

*Counted random-oracle experiment.* -/
@[simp] theorem generalAlgM_verify (pk : PublicKeyCore core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp core) :
    (generalAlgM (m := m) vp core).verify pk msg sig =
      GeneralScheme.verifyInternalM vp core (emptyContextMessage msg) sig pk := by
  rfl

end Equations

/-! ## The counted experiment -/

section Counted

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed]
  [SampleableType core.Y] [DecidableEq core.Y] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [SampleableType (Bytes vp.params.m)]

/-- The oracle family the whole experiment runs in: private sampling together with the public
hash. -/
local notation "romSpec" => unifSpec + publicHashSpec core

/-- **The EUF-CMA game as one program in the shared public-hash world.**  Key generation, a
logged signing oracle, the forger, then verification — the body of
`VCVio`'s `unforgeableExp`, but left uninterpreted so that every public-hash evaluation by any
party is a query rather than a function call.

*Counted random-oracle experiment.* -/
noncomputable def romGameCore
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    OracleComp romSpec Bool :=
  letI : DecidableEq (List Byte) := Classical.decEq _
  letI : DecidableEq (GeneralScheme.SignatureCore vp core) := Classical.decEq _
  do
    let alg := generalAlgM (m := OracleComp romSpec) vp core
    let (pk, sk) ← alg.keygen
    let impl : QueryImpl (romSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp core))
        (WriterT (QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core))
          (OracleComp romSpec)) :=
      (HasQuery.toQueryImpl (spec := romSpec) (m := OracleComp romSpec)).liftTarget
          (WriterT (QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core))
            (OracleComp romSpec)) +
        alg.signingOracle pk sk
    let ((msg, sig), log) ← (simulateQ impl (adv.main pk)).run
    let verified ← alg.verify pk msg sig
    return !log.wasQueried msg && verified

open scoped Classical in
/-- **The counted interpretation.**  One lazily-sampled public-hash cache, shared by every party
and never reset, with each public-hash query charged `1` and private sampling charged `0`.

*Counted random-oracle experiment.* -/
noncomputable def countedRomImpl :
    QueryImpl romSpec (AddWriterT ℕ (StateT (PublicHash.Cache core) ProbComp)) :=
  (unifFwdImpl (publicHashSpec core) + PublicHash.randomOracle core).withAddCost
    (fun q => match q with | .inl _ => 0 | .inr _ => 1)

omit [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed] in
open scoped Classical in
/-- A private-sampling query is charged `0` and forwarded to `unifFwdImpl`.  The body of
`countedRomImpl` is not exposed, so this is what a consumer reading its charge rewrites with.

*Counted random-oracle experiment.* -/
theorem countedRomImpl_inl (i : unifSpec.Domain) :
    countedRomImpl core (Sum.inl i) = (do
      AddWriterT.addTell (M := StateT (PublicHash.Cache core) ProbComp) (0 : ℕ)
      liftM (unifFwdImpl (publicHashSpec core) i)) := by
  rw [countedRomImpl, QueryImpl.withAddCost_apply_inl]; rfl

omit [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed] in
open scoped Classical in
/-- A public-hash query is charged `1` and forwarded to the shared lazy random oracle.

*Counted random-oracle experiment.* -/
theorem countedRomImpl_inr (q : (publicHashSpec core).Domain) :
    countedRomImpl core (Sum.inr q) = (do
      AddWriterT.addTell (M := StateT (PublicHash.Cache core) ProbComp) (1 : ℕ)
      liftM (PublicHash.randomOracle core q)) := by
  rw [countedRomImpl, QueryImpl.withAddCost_apply_inr]; rfl

open scoped Classical in
/-- **The experiment**, from the empty cache: the success bit together with the number of
public-hash queries the whole execution made.

*Counted random-oracle experiment.* -/
noncomputable def countedRomExperiment
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    ProbComp (Bool × ℕ) :=
  (simulateQ (countedRomImpl core) (romGameCore core adv)).runAdd.run' ∅

open scoped Classical in
/-- The probability that the forger wins, ignoring the charge.

*Counted random-oracle experiment.* -/
noncomputable def romForgeAdvantage
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) : ℝ≥0∞ :=
  𝒟[Prod.fst <$> countedRomExperiment core adv] {true}

open scoped Classical in
/-- **The query budget.**  Every execution of the experiment makes at most `q` public-hash
queries, counting key generation, signing and the final verification as well as the forger's own.

This is a condition on the support, not a complexity assumption: the adversary's running time and
memory are unconstrained and its private sampling is free.

The body is exposed, so a consumer can both establish and eliminate the bound directly; the
named elimination lemmas are preferable wherever one applies.

*Counted random-oracle experiment.* -/
@[expose] def HasHashQueryBound
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) (q : ℕ) : Prop :=
  ∀ result ∈ support (countedRomExperiment core adv), result.2 ≤ q

end Counted

end SLHDSA.Security
