/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.RomRun
public import HashSig.SLHDSA.Security.Composition
public import HashSig.SLHDSA.SecretProvider
public import VCVio.OracleComp.QueryTracking.RandomOracle.Joint
import all HashSig.SLHDSA.Security.CountedRom

/-!
# The secret-value `PRF` hop in the counted random-oracle lane

This module takes the `SKG_PRF` hop inside the counted random-oracle experiment of
`HashSig.SLHDSA.Security.CountedRom`: it replaces the derivation of every WOTS+ and FORS secret
value from `SK.seed` by a challenge oracle, at the cost of one `PRF` distinguishing advantage.

## The statement

`SLHDSA.Security.romForgeAdvantage_le_skgPrf_add_ideal` says: for every forger `adv` against the
counted random-oracle experiment,

`romForgeAdvantage core adv ≤
  prfAbsAdvantage (skgPrfScheme core) (skgPrfReductionGen core adv) + skgPrfIdealAdvantage core adv`

Both terms on the right are functions of `adv` alone: `skgPrfReductionGen adv` is a closed term of
`PRFScheme.PRFAdversary`, and `skgPrfIdealAdvantage adv` is that same distinguisher's success
probability in the ideal `PRF` experiment — the counted experiment with every WOTS+ and FORS
secret drawn from a lazily sampled random function of `(PK.seed, ADRS)`.  No certificate supplies
either, and the inequality is unconditional: `evalDist_prfRealExp_skgPrfReductionGen` proves that
the reduction's success probability in the *real* `PRF` experiment is `romForgeAdvantage core adv`
exactly.

## Why the hop is needed

`CorePrimitives.PRF` carries no law, so a constant function is an admissible instantiation, and
then every WOTS+ and FORS secret is computable by the adversary from public data.  Any bound on a
hidden-value event of the counted experiment is therefore false for some admissible parameter
bundle.  After this hop the secrets are a random function, and a hidden-value event has a
probability the fresh-answer machinery can bound.  The hop is what makes such a term boundable at
all, not an optimisation of a bound that already held.

## How the reduction is built

The game is written once, `romGameCoreGen`, over the three-summand signature
`unifSpec + (publicHashSpec core + ((PK.seed × ADRS) →ₒ Y))`, with `SK.seed` absent: key
generation and signing take every secret value from the third summand through `skgSecret`, using
the provider-parametric programs of `HashSig.SLHDSA.SecretProvider`
(`keygenInternalWithSecretM`, `signInternalWithSecretM`).  `skgPrfReductionGen` samples `SK.prf`
and `PK.seed` itself and interprets that game with `skgLaneImpl`: private sampling is forwarded to
its own `unifSpec`, public-hash queries go to one shared lazy cache (`skgHashImpl`) threaded
through key generation, every signing query and the final verification, and secret-value queries
go to its challenge oracle.  Its output bit is the EUF-CMA win bit.

The identification of the real experiment has two halves, both proved here.  At query level,
`prfReal_mapStateTBase_skgLaneImpl` says that composing the reduction's handler with the real
`PRF` handler gives the counted lane's own handler (`romLaneImpl`); its proof uses the generic
`QueryImpl.mapStateTBase_withCaching`.  At game level,
`simulateQ_skgRealImpl_romGameCoreGen` pushes that interpretation through the game — through key
generation, through the forger's own program with its `WriterT` log, and through verification —
using the naturality lemmas of `HashSig.SLHDSA.SecretProvider` and the specialisation of each
provider-parametric program at the honest provider.  `prfRealExp_skgPrfReductionGen` then assembles
the two, and no reordering of the seed samples is needed: the `PRF` experiment draws the key first
and `generalAlgM`'s key generation draws `SK.seed` first as well.

The signature is *re-associated* relative to the counted lane's `unifSpec + publicHashSpec core`:
the two random oracles of the ideal experiment — the public hash inside, the challenge function
outside — then sit as the right summand of `unifSpec + (publicHashSpec core + prfSpec)`.
`prfIdeal_mapStateTBase_skgLaneImpl` confirms that at that association the ideal interpretation of
the game's oracles *is* `OracleSpec.nestedRandomOracle` of those two signatures behind the
private-sampling summand, which is what
`VCVio.OracleComp.QueryTracking.RandomOracle.Joint` identifies with a single lazy oracle on one
joint cache and what its fresh-answer bound consumes.

## Scope

* **No bound on `prfAbsAdvantage` at this scheme is proved, and none can be proved against an
  unbounded distinguisher over a finite key space.**  `SampleableType core.SkSeed`
  makes the key space finite and `OracleComp` carries no resource bound, so a forger may recover
  `SK.seed` from the secret values one signature reveals and then forge, which makes the
  constructed distinguisher's advantage essentially one.  The hop remains true — it is the
  triangle inequality — and what it changed is qualitative: without it the hidden-value event has
  probability one for every adversary, and with it that event becomes boundable in the ideal game
  while this term becomes the assumption slot.  A number out of it needs a `PRF` assumption
  restricted to a bounded adversary class, which these types cannot express.  This is the same
  structural gap `HashSig.SLHDSA.Security.OpenPreBound` records for its own
  assumption-parametric bound, now carried by this summand rather than by a tweakable-hash game.
* The hash-query budget does not transport across the hop.  `HasHashQueryBound adv q` is a
  condition on `support (countedRomExperiment core adv)`, that is on the *real* counted
  experiment, so it constrains no execution of the ideal one; bounding `skgPrfIdealAdvantage`
  needs a lane-independent query bound, of the structural `…_isTotalQueryBound` kind, rather than
  the counted charge.
* **No bound on `skgPrfIdealAdvantage` is proved.**  It is the honest carrier of everything not
  yet reduced, and nothing here claims it is small.  In particular no hidden-value event, and no
  `q/2^{8n}`-style estimate, appears in this module.
* On the ideal side only the *handler* is identified.
  `prfIdeal_mapStateTBase_skgLaneImpl` says the reduction's oracles under the ideal `PRF` handler
  are the private-sampling summand in front of `OracleSpec.nestedRandomOracle` of the public hash
  and the challenge signature — the handler
  `VCVio.OracleComp.QueryTracking.RandomOracle.Joint` collapses to one lazy oracle on one joint
  cache, and the handler its fresh-answer bound consumes.  The *experiment*-level rewriting, which
  would identify `PRFScheme.prfIdealExp (skgPrfReductionGen core adv)` with a run of that handler
  from the two empty caches, is not stated or proved here, and neither is any bound obtained from
  the engine.
* Secret-value queries are not counted.  `HasHashQueryBound` counts public-hash queries only, and
  the reduction issues one challenge query per secret value it needs, which is a separate
  accounting this module does not do.
* The hop is stated at the *absolute* distinguishing advantage `prfAbsAdvantage`, so it is
  agnostic about which direction the distinguisher favours; it assumes nothing about `core.PRF`.
* Nothing here is quantum.  The public hash is a classical lazily-sampled oracle and the `PRF`
  experiments are classical, so the inequality is a classical random-oracle statement.
* The message randomizer `PRF_msg` is untouched: `signInternalWithSecretM` still takes `SK.prf`,
  and `HashSig.SLHDSA.Security.PrfHops` is where that hop is taken, in the deterministic lane.

## Labels

Thirty-six declarations.  There is no private declaration and no instance.

*The secret-value `PRF` scheme*:

* `skgPrfScheme`, `skgPrfScheme_keygen`, `skgPrfScheme_eval`, `skgPrfSpec`.

*The reduction's lane*:

* `SkgLane`, `skgUnifImpl`, `skgHashImpl`.

*The game left uninterpreted*:

* `skgGameSpec`, `skgSecret`, `skgSigningOracle`, `skgGameImpl`, `romGameCoreGen`.

*The distinguisher*:

* `skgLaneImpl`, `skgPrfReductionGen`, `skgPrfIdealAdvantage`, `skgPrfIdealAdvantage_le_one`.

*The query-level identification*:

* `romLaneImpl`, `prfReal_mapStateTBase_skgLaneImpl`.

*The game-level identification*:

* `skgRealImpl`, `romLaneImpl_eq_compose`, `skgRealHom`, `skgRealHom_secret`,
  `simulateQ_skgRealImpl_liftM`, `simulateQ_skgRealImpl_query`;
* `romCmaImpl`, `simulateQ_skgRealImpl_skgSigningOracle`,
  `writerTMapBase_skgRealImpl_skgGameImpl`;
* `romGameCoreAt`, `simulateQ_skgRealImpl_romGameCoreGen`, `romGameCore_eq_bind`,
  `run'_simulateQ_romImpl_liftM_bind`;
* `prfRealExp_skgPrfReductionGen`, `fst_map_countedRomExperiment_eq`,
  `evalDist_prfRealExp_skgPrfReductionGen`.

*The ideal experiment's shape*:

* `prfIdeal_mapStateTBase_skgLaneImpl`.

*The hop*:

* `romForgeAdvantage_le_skgPrf_add_ideal`.

## References

- NIST FIPS 205, §4.1 (`PRF`), §9, Algorithms 18--19
- `VCVio.CryptoFoundations.PRF` for the `PRF` notion used: `PRFScheme.prfRealExp`,
  `PRFScheme.prfIdealExp`, and the absolute advantage `prfAbsAdvantage` of
  `HashSig.SLHDSA.Security.Composition`
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified", whose `SKG_PRF` step keys its oracle on the address alone at a fixed public
  seed and runs outside a random-oracle lane; this one keys on `(PK.seed, ADRS)` and runs inside
  the counted random-oracle experiment
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec ENNReal SignatureAlg

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-! ## The secret-value `PRF` scheme -/

/-- The secret-value `PRF` as a `PRFScheme` keyed by `SK.seed`, with the public seed part of the
domain rather than a parameter of the scheme. -/
@[expose] def skgPrfScheme [SampleableType core.SkSeed] :
    PRFScheme core.SkSeed (core.PkSeed × Adrs) core.Y where
  keygen := $ᵗ core.SkSeed
  eval := fun skSeed q => core.PRF q.1 skSeed q.2

/-- The secret-value `PRF` scheme generates its key by sampling `SK.seed` uniformly. -/
theorem skgPrfScheme_keygen [SampleableType core.SkSeed] :
    (skgPrfScheme core).keygen = $ᵗ core.SkSeed := rfl

/-- The secret-value `PRF` scheme evaluates to `core.PRF` at the queried public seed. -/
theorem skgPrfScheme_eval [SampleableType core.SkSeed] (skSeed : core.SkSeed)
    (q : core.PkSeed × Adrs) : (skgPrfScheme core).eval skSeed q = core.PRF q.1 skSeed q.2 := rfl

/-- The oracle family the secret-value distinguisher runs in. -/
abbrev skgPrfSpec := PRFScheme.PRFOracleSpec (core.PkSeed × Adrs) core.Y

/-- The monad the reduction runs the whole experiment in: one lazy public-hash cache over the
distinguisher's own oracle family. -/
abbrev SkgLane := StateT (PublicHash.Cache core) (OracleComp (skgPrfSpec core))

section

variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)]
  [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]

/-! ## The reduction's lane -/

/-- Uniform sampling of a public-hash answer inside the distinguisher's oracle family: the fresh
answer a lazy public-hash oracle draws on a cache miss. -/
def skgUnifImpl : QueryImpl (publicHashSpec core) (OracleComp (skgPrfSpec core)) :=
  fun q => OracleComp.liftComp ($ᵗ ((publicHashSpec core).Range q)) (skgPrfSpec core)

/-- The shared lazy public-hash oracle, inside the distinguisher's oracle family. -/
def skgHashImpl : QueryImpl (publicHashSpec core) (SkgLane core) :=
  (skgUnifImpl core).withCaching

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed]

/-- The oracle family the counted experiment runs in. -/
local notation "romSpec" => unifSpec + publicHashSpec core

/-! ## The game left uninterpreted -/

/-- The oracle family the provider-parametric game runs in: private sampling, the public hash,
and the secret-value oracle at `(PK.seed, ADRS)`.  It is associated so that the public hash and
the secret-value oracle together form the right summand. -/
abbrev skgGameSpec := unifSpec + (publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y))

/-- The secret-value provider of the game: the secret at `adrs` is the answer of the third oracle
summand at `(pkSeed, adrs)`. -/
def skgSecret (pkSeed : core.PkSeed) : Adrs → OracleComp (skgGameSpec core) core.Y :=
  fun a => liftM ((skgGameSpec core).query (Sum.inr (Sum.inr (pkSeed, a))))

/-- The signing oracle of the game: it samples `addrnd`, holds `SK.prf`, `PK.seed` and `PK.root`,
and runs FIPS 205 Algorithm 19 with every WOTS+ and FORS secret taken from `skgSecret`. -/
noncomputable def skgSigningOracle (skPrf : core.SkPrf) (pkSeed : core.PkSeed)
    (pkRoot : core.Y) :
    QueryImpl (List Byte →ₒ GeneralScheme.SignatureCore vp core)
      (OracleComp (skgGameSpec core)) := fun msg => do
  let addrnd ← (liftM ($ᵗ core.Y) : OracleComp (skgGameSpec core) core.Y)
  GeneralScheme.signInternalWithSecretM core (skgSecret core pkSeed) (emptyContextMessage msg)
    skPrf pkSeed pkRoot addrnd

/-- The forger's oracles as the reduction's game serves them: private sampling and public-hash
queries are forwarded into the game's own oracle family, and signing queries are answered by
`skgSigningOracle` and logged. -/
noncomputable def skgGameImpl (skPrf : core.SkPrf) (pkSeed : core.PkSeed) (pkRoot : core.Y) :
    QueryImpl (romSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp core))
      (WriterT (QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core))
        (OracleComp (skgGameSpec core))) :=
  (HasQuery.toQueryImpl (spec := romSpec) (m := OracleComp (skgGameSpec core))).liftTarget
      (WriterT (QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core))
        (OracleComp (skgGameSpec core))) +
    (skgSigningOracle core skPrf pkSeed pkRoot).withLogging

/-- **The EUF-CMA game with every WOTS+ and FORS secret taken from an oracle**, left
uninterpreted.  `SK.seed` does not occur. -/
noncomputable def romGameCoreGen
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core))
    (skPrf : core.SkPrf) (pkSeed : core.PkSeed) : OracleComp (skgGameSpec core) Bool :=
  letI : DecidableEq (List Byte) := Classical.decEq _
  letI : DecidableEq (GeneralScheme.SignatureCore vp core) := Classical.decEq _
  do
    let pkRoot ← GeneralScheme.keygenInternalWithSecretM core (skgSecret core pkSeed) pkSeed
    let pk : PublicKeyCore core := ⟨pkSeed, pkRoot⟩
    let ((msg, sig), log) ←
      (simulateQ (skgGameImpl core skPrf pkSeed pkRoot) (adv.main pk)).run
    let verified ← GeneralScheme.verifyInternalM vp core (emptyContextMessage msg) sig pk
    return !log.wasQueried msg && verified

/-! ## The distinguisher -/

/-- The reduction's interpretation of the game's three oracles: private sampling is forwarded to
the distinguisher's own `unifSpec`, public-hash queries go to one shared lazy cache, and
secret-value queries go to the distinguisher's challenge oracle. -/
def skgLaneImpl : QueryImpl (skgGameSpec core) (SkgLane core) :=
  ((QueryImpl.ofLift unifSpec (OracleComp (skgPrfSpec core))).liftTarget (SkgLane core)) +
    (skgHashImpl core +
      ((fun q => liftM (PRFScheme.functionQuery (D := core.PkSeed × Adrs) (R := core.Y) q)) :
        QueryImpl ((core.PkSeed × Adrs) →ₒ core.Y) (SkgLane core)))

/-- **The `SKG_PRF` distinguisher constructed from a counted-random-oracle forger.**  It samples
`SK.prf` and `PK.seed`, plays the uninterpreted game with `skgLaneImpl` from the empty public-hash
cache, and outputs the forger's EUF-CMA win bit.  A function of the forger: no certificate supplies
it. -/
noncomputable def skgPrfReductionGen
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    PRFScheme.PRFAdversary (core.PkSeed × Adrs) core.Y :=
  (do
    let skPrf ← OracleComp.liftComp ($ᵗ core.SkPrf) (skgPrfSpec core)
    let pkSeed ← OracleComp.liftComp ($ᵗ core.PkSeed) (skgPrfSpec core)
    (simulateQ (skgLaneImpl core) (romGameCoreGen core adv skPrf pkSeed)).run' ∅ :
    OracleComp (skgPrfSpec core) Bool)

/-- **The advantage that survives the `SKG_PRF` hop**: the reduction's success probability in the
ideal `PRF` experiment, which is the counted random-oracle EUF-CMA game with every WOTS+ and FORS
secret drawn from a lazily sampled random function of `(PK.seed, ADRS)`. -/
noncomputable def skgPrfIdealAdvantage
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) : ℝ≥0∞ :=
  𝒟[PRFScheme.prfIdealExp (skgPrfReductionGen core adv)] {true}

/-- The advantage surviving the `SKG_PRF` hop is a probability, so it is at most one.  The body of
`skgPrfIdealAdvantage` is not exposed, so this is what a consumer bounding it from above uses. -/
theorem skgPrfIdealAdvantage_le_one
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    skgPrfIdealAdvantage core adv ≤ 1 :=
  MeasureTheory.measure_le_one _ _

/-! ## The query-level identification -/

/-- The three oracles of the game, interpreted as the counted lane interprets them, with the
secret-value oracle answered by the real `PRF` at `skSeed`. -/
noncomputable def romLaneImpl (skSeed : core.SkSeed) :
    QueryImpl (skgGameSpec core) (StateT (PublicHash.Cache core) ProbComp) :=
  unifFwdImpl (publicHashSpec core) +
    (PublicHash.randomOracle core +
      ((fun q => pure (core.PRF q.1 skSeed q.2)) :
        QueryImpl ((core.PkSeed × Adrs) →ₒ core.Y)
          (StateT (PublicHash.Cache core) ProbComp)))

omit [SampleableType core.SkPrf] [SampleableType core.PkSeed] in
/-- **Under the real `PRF` handler the reduction's three oracles are the counted lane's
oracles.**  This is the query-level content of the hop: the challenge oracle answered by
`core.PRF` at `skSeed` restores the secret values the honest signer would have derived, and the
reduction's own lazy cache becomes the shared public-hash random oracle. -/
theorem prfReal_mapStateTBase_skgLaneImpl (skSeed : core.SkSeed) :
    (PRFScheme.prfRealQueryImpl (skgPrfScheme core) skSeed).mapStateTBase (skgLaneImpl core)
      = romLaneImpl core skSeed := by
  funext q
  cases q with
  | inl i =>
      ext s
      simp only [QueryImpl.mapStateTBase, skgLaneImpl, romLaneImpl, QueryImpl.add_apply_inl,
        unifFwdImpl, StateT.run_mk, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
        StateT.run_monadLift]
      rw [simulateQ_bind]
      rw [show (monadLift (liftM (OracleSpec.query i)) :
          OracleComp (skgPrfSpec core) (unifSpec.Range i)) =
          OracleComp.liftComp (liftM (OracleSpec.query i) : ProbComp _)
            (skgPrfSpec core) from by rfl]
      rw [PRFScheme.simulateQ_prfRealQueryImpl_liftComp]
      simp
  | inr q =>
      cases q with
      | inr q =>
          ext s
          simp [QueryImpl.mapStateTBase, skgLaneImpl, romLaneImpl, PRFScheme.functionQuery,
            skgPrfScheme]
      | inl t =>
          ext s
          have hcache := congrFun (QueryImpl.mapStateTBase_withCaching
            (PRFScheme.prfRealQueryImpl (skgPrfScheme core) skSeed) (skgUnifImpl core)) t
          have key : (((PRFScheme.prfRealQueryImpl (skgPrfScheme core) skSeed).mapStateTBase
                (skgLaneImpl core)) (Sum.inr (Sum.inl t))) =
              ((PRFScheme.prfRealQueryImpl (skgPrfScheme core) skSeed).mapStateTBase
                (QueryImpl.withCaching (skgUnifImpl core))) t := rfl
          have hunif : (fun t : (publicHashSpec core).Domain =>
              simulateQ (PRFScheme.prfRealQueryImpl (skgPrfScheme core) skSeed)
                (skgUnifImpl core t)) = uniformSampleImpl := by
            funext t
            rw [skgUnifImpl, PRFScheme.simulateQ_prfRealQueryImpl_liftComp, uniformSampleImpl_apply]
          rw [key, hcache, hunif]
          rfl

/-! ## The game-level identification -/

/-- The game's three oracles read as the counted lane's own oracle syntax: private sampling and
public-hash queries are forwarded unchanged, and a secret-value query at `(pkSeed, adrs)` is
answered by the real `PRF` at `skSeed`. -/
noncomputable def skgRealImpl (skSeed : core.SkSeed) :
    QueryImpl (skgGameSpec core) (OracleComp romSpec) :=
  HasQuery.toQueryImpl (spec := unifSpec) (m := OracleComp romSpec) +
    (HasQuery.toQueryImpl (spec := publicHashSpec core) (m := OracleComp romSpec) +
      ((fun q => pure (core.PRF q.1 skSeed q.2)) :
        QueryImpl ((core.PkSeed × Adrs) →ₒ core.Y) (OracleComp romSpec)))

omit [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed] in
/-- The counted lane's interpretation of the game's oracles factors through `skgRealImpl`: first
answer the secret-value oracle by the real `PRF`, then run the shared lazy public-hash oracle. -/
theorem romLaneImpl_eq_compose (skSeed : core.SkSeed) :
    romLaneImpl core skSeed =
      (unifFwdImpl (publicHashSpec core) + PublicHash.randomOracle core) ∘ₛ
        skgRealImpl core skSeed := by
  funext q
  cases q with
  | inl i =>
      rw [QueryImpl.apply_compose, skgRealImpl, QueryImpl.add_apply_inl,
        show (HasQuery.toQueryImpl (spec := unifSpec) (m := OracleComp romSpec) i) =
          OracleComp.liftComp (liftM (OracleSpec.query i) : ProbComp (unifSpec.Range i))
            (unifSpec + publicHashSpec core) from by rfl]
      rw [OracleComp.liftComp_eq_liftM, QueryImpl.simulateQ_add_liftM_left, simulateQ_spec_query,
        romLaneImpl, QueryImpl.add_apply_inl]
  | inr q =>
      cases q with
      | inl t => simp [skgRealImpl, romLaneImpl]
      | inr q => simp [skgRealImpl, romLaneImpl]

/-- `skgRealImpl` as a public-hash-query-preserving monad morphism from the game's oracle syntax
to the counted lane's, which is what carries the provider-parametric programs across. -/
noncomputable def skgRealHom (skSeed : core.SkSeed) :
    HasQuery.QueryHom (publicHashSpec core) (OracleComp (skgGameSpec core))
      (OracleComp romSpec) where
  toMonadHom := simulateQ' (skgRealImpl core skSeed)
  map_query' t := by simp [skgRealImpl]

omit [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.Y] [SampleableType core.SkSeed]
  [SampleableType core.SkPrf] [SampleableType core.PkSeed] in
/-- Along `skgRealHom` the game's secret-value provider becomes the honest provider: the secret at
`adrs` is `core.PRF` at the public seed the game is keyed to and at `skSeed`. -/
theorem skgRealHom_secret (skSeed : core.SkSeed) (pkSeed : core.PkSeed) (a : Adrs) :
    (skgRealHom core skSeed).toMonadHom (skgSecret core pkSeed a) =
      pure (core.PRF pkSeed skSeed a) := by
  simp [skgRealHom, skgSecret, skgRealImpl]

omit [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.Y] [SampleableType core.SkSeed]
  [SampleableType core.SkPrf] [SampleableType core.PkSeed] in
/-- `skgRealImpl` is transparent on private sampling lifted in from `ProbComp`. -/
theorem simulateQ_skgRealImpl_liftM (skSeed : core.SkSeed) {α : Type} (oa : ProbComp α) :
    simulateQ (skgRealImpl core skSeed) (liftM oa : OracleComp (skgGameSpec core) α) =
      (liftM oa : OracleComp romSpec α) := by
  rw [← OracleComp.liftComp_eq_liftM, skgRealImpl, QueryImpl.simulateQ_add_liftComp_left]
  rfl

omit [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.Y] [SampleableType core.SkSeed]
  [SampleableType core.SkPrf] [SampleableType core.PkSeed] in
/-- `skgRealImpl` forwards a private-sampling or public-hash query to the same query of the
counted lane. -/
theorem simulateQ_skgRealImpl_query (skSeed : core.SkSeed) (t : (romSpec).Domain) :
    simulateQ (skgRealImpl core skSeed)
        (liftM (OracleSpec.query t) : OracleComp (skgGameSpec core) ((romSpec).Range t)) =
      (liftM (OracleSpec.query t) : OracleComp romSpec ((romSpec).Range t)) := by
  cases t with
  | inl i =>
      rw [show (liftM (OracleSpec.query (Sum.inl i)) :
            OracleComp (skgGameSpec core) ((romSpec).Range (Sum.inl i))) =
          liftM (OracleSpec.query (Sum.inl i) :
            OracleQuery (skgGameSpec core) (unifSpec.Range i)) from rfl,
        simulateQ_spec_query, skgRealImpl, QueryImpl.add_apply_inl]
      rfl
  | inr q =>
      rw [show (liftM (OracleSpec.query (Sum.inr q)) :
            OracleComp (skgGameSpec core) ((romSpec).Range (Sum.inr q))) =
          liftM (OracleSpec.query (Sum.inr (Sum.inl q)) :
            OracleQuery (skgGameSpec core) ((publicHashSpec core).Range q)) from rfl,
        simulateQ_spec_query, skgRealImpl, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
      rfl

/-- The forger's oracles as the counted game serves them at a named key pair: ambient queries
forwarded, signing queries answered by `generalAlgM` and logged. -/
noncomputable def romCmaImpl (pk : PublicKeyCore core) (sk : SecretKeyCore core) :
    QueryImpl (romSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp core))
      (WriterT (QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core))
        (OracleComp romSpec)) :=
  (HasQuery.toQueryImpl (spec := romSpec) (m := OracleComp romSpec)).liftTarget
      (WriterT (QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core))
        (OracleComp romSpec)) +
    (generalAlgM (m := OracleComp romSpec) vp core).signingOracle pk sk

omit [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] in
/-- **Under the real `PRF` the reduction's signing oracle is the counted game's signing
algorithm.**  The provider-parametric signer at the honest provider is Algorithm 19 at the secret
key `⟨skSeed, skPrf, pkSeed, pkRoot⟩`. -/
theorem simulateQ_skgRealImpl_skgSigningOracle (skSeed : core.SkSeed) (skPrf : core.SkPrf)
    (pkSeed : core.PkSeed) (pkRoot : core.Y) (msg : List Byte) :
    simulateQ (skgRealImpl core skSeed) (skgSigningOracle core skPrf pkSeed pkRoot msg) =
      (generalAlgM (m := OracleComp romSpec) vp core).sign ⟨pkSeed, pkRoot⟩
        ⟨skSeed, skPrf, pkSeed, pkRoot⟩ msg := by
  rw [skgSigningOracle, simulateQ_bind, simulateQ_skgRealImpl_liftM, generalAlgM_sign]
  refine bind_congr fun addrnd => ?_
  rw [show simulateQ (skgRealImpl core skSeed)
      (GeneralScheme.signInternalWithSecretM core (skgSecret core pkSeed)
        (emptyContextMessage msg) skPrf pkSeed pkRoot addrnd) =
      (skgRealHom core skSeed).toMonadHom
        (GeneralScheme.signInternalWithSecretM core (skgSecret core pkSeed)
          (emptyContextMessage msg) skPrf pkSeed pkRoot addrnd) from rfl,
    GeneralScheme.signInternalWithSecretM_natural core (skgRealHom core skSeed)
      (skgSecret core pkSeed) (fun a => pure (core.PRF pkSeed skSeed a))
      (skgRealHom_secret core skSeed pkSeed)]
  exact GeneralScheme.signInternalWithSecretM_eq_signInternalM core (emptyContextMessage msg)
    ⟨skSeed, skPrf, pkSeed, pkRoot⟩ addrnd

omit [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] in
/-- **Under the real `PRF` the reduction's forger oracles are the counted game's forger
oracles**, logging included. -/
theorem writerTMapBase_skgRealImpl_skgGameImpl (skSeed : core.SkSeed) (skPrf : core.SkPrf)
    (pkSeed : core.PkSeed) (pkRoot : core.Y) :
    (skgRealImpl core skSeed).writerTMapBase (skgGameImpl core skPrf pkSeed pkRoot) =
      romCmaImpl core ⟨pkSeed, pkRoot⟩ ⟨skSeed, skPrf, pkSeed, pkRoot⟩ := by
  funext t
  cases t with
  | inl t =>
      ext
      simp [QueryImpl.writerTMapBase, skgGameImpl, romCmaImpl,
        simulateQ_skgRealImpl_query core skSeed t]
  | inr msg =>
      ext
      rw [QueryImpl.writerTMapBase_apply, skgGameImpl, QueryImpl.add_apply_inr,
        romCmaImpl, QueryImpl.add_apply_inr, SignatureAlg.signingOracle,
        QueryImpl.withLogging_apply, QueryImpl.withLogging_apply]
      simp only [WriterT.run_bind, WriterT.run_monadLift', WriterT.run_tell, WriterT.run_pure,
        simulateQ_bind, simulateQ_map, simulateQ_pure, Functor.map_map, bind_map_left,
        pure_bind]
      rw [simulateQ_skgRealImpl_skgSigningOracle]

/-- The counted EUF-CMA game at a fixed seed triple: `romGameCore` with its three private
samples already drawn. -/
noncomputable def romGameCoreAt
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core))
    (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    OracleComp romSpec Bool :=
  letI : DecidableEq (List Byte) := Classical.decEq _
  letI : DecidableEq (GeneralScheme.SignatureCore vp core) := Classical.decEq _
  do
    let (pk, sk) ← (GeneralScheme.keygenInternalM vp core skSeed skPrf pkSeed :
      OracleComp romSpec (PublicKeyCore core × SecretKeyCore core))
    let ((msg, sig), log) ← (simulateQ (romCmaImpl core pk sk) (adv.main pk)).run
    let verified ← GeneralScheme.verifyInternalM vp core (emptyContextMessage msg) sig pk
    return !log.wasQueried msg && verified

omit [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] in
/-- **Under the real `PRF` the uninterpreted game is the counted game at the same seeds.**  Key
generation, every signing query and the final verification all become the honest programs. -/
theorem simulateQ_skgRealImpl_romGameCoreGen
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core))
    (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    simulateQ (skgRealImpl core skSeed) (romGameCoreGen core adv skPrf pkSeed) =
      romGameCoreAt core adv skSeed skPrf pkSeed := by
  rw [romGameCoreGen, romGameCoreAt, simulateQ_bind,
    show simulateQ (skgRealImpl core skSeed)
        (GeneralScheme.keygenInternalWithSecretM core (skgSecret core pkSeed) pkSeed) =
        (skgRealHom core skSeed).toMonadHom
          (GeneralScheme.keygenInternalWithSecretM core (skgSecret core pkSeed) pkSeed) from rfl,
    GeneralScheme.keygenInternalWithSecretM_natural core (skgRealHom core skSeed)
      (skgSecret core pkSeed) (fun a => pure (core.PRF pkSeed skSeed a))
      (skgRealHom_secret core skSeed pkSeed),
    ← GeneralScheme.keygenInternalWithSecretM_eq_keygenInternalM core skSeed skPrf pkSeed,
    map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun pkRoot => ?_
  simp only [Function.comp_apply, pure_bind]
  rw [simulateQ_bind, QueryImpl.simulateQ_writerTMapBase_run,
    writerTMapBase_skgRealImpl_skgGameImpl]
  refine bind_congr fun x => ?_
  rw [simulateQ_bind,
    show simulateQ (skgRealImpl core skSeed)
        (GeneralScheme.verifyInternalM vp core (emptyContextMessage x.1.1) x.1.2
          ⟨pkSeed, pkRoot⟩) =
        (skgRealHom core skSeed).toMonadHom
          (GeneralScheme.verifyInternalM vp core (emptyContextMessage x.1.1) x.1.2
            ⟨pkSeed, pkRoot⟩) from rfl,
    GeneralScheme.verifyInternalM_natural vp core (skgRealHom core skSeed)]
  exact bind_congr fun verified => simulateQ_pure _ _

omit [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] in
/-- The counted game draws `SK.seed`, `SK.prf` and `PK.seed` and then plays `romGameCoreAt`. -/
theorem romGameCore_eq_bind
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    romGameCore core adv =
      (do
        let skSeed ← (liftM ($ᵗ core.SkSeed) : OracleComp romSpec core.SkSeed)
        let skPrf ← (liftM ($ᵗ core.SkPrf) : OracleComp romSpec core.SkPrf)
        let pkSeed ← (liftM ($ᵗ core.PkSeed) : OracleComp romSpec core.PkSeed)
        romGameCoreAt core adv skSeed skPrf pkSeed : OracleComp romSpec Bool) := by
  rw [romGameCore, generalAlgM_keygen]
  simp only [bind_assoc]
  refine bind_congr fun skSeed => bind_congr fun skPrf => bind_congr fun pkSeed => ?_
  rw [romGameCoreAt]
  exact bind_congr fun ⟨_, _⟩ => rfl

omit [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed] in
/-- Private sampling at the head of a program leaves the shared public-hash cache untouched, so
it commutes out of the lazy run. -/
theorem run'_simulateQ_romImpl_liftM_bind {α β : Type} (oa : ProbComp α)
    (k : α → OracleComp romSpec β) (c : PublicHash.Cache core) :
    (simulateQ (unifFwdImpl (publicHashSpec core) + PublicHash.randomOracle core)
        (liftM oa >>= k)).run' c =
      oa >>= fun x => (simulateQ (unifFwdImpl (publicHashSpec core) +
        PublicHash.randomOracle core) (k x)).run' c := by
  rw [simulateQ_bind, QueryImpl.simulateQ_add_liftM_left, unifFwdImpl, simulateQ_liftTarget,
    simulateQ_ofLift_eq_self, StateT.run'_eq, StateT.run_bind, StateT.run_monadLift]
  simp [StateT.run'_eq]

/-- **The real `PRF` experiment at the reduction is the counted random-oracle experiment.**  Both
sides draw `SK.seed`, `SK.prf`, `PK.seed` in that order, so no reordering is involved. -/
theorem prfRealExp_skgPrfReductionGen
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    PRFScheme.prfRealExp (skgPrfScheme core) (skgPrfReductionGen core adv) =
      (simulateQ (unifFwdImpl (publicHashSpec core) + PublicHash.randomOracle core)
        (romGameCore core adv)).run' ∅ := by
  rw [romGameCore_eq_bind, run'_simulateQ_romImpl_liftM_bind, PRFScheme.prfRealExp,
    skgPrfScheme_keygen]
  refine bind_congr fun skSeed => ?_
  rw [skgPrfReductionGen, simulateQ_bind, PRFScheme.simulateQ_prfRealQueryImpl_liftComp,
    run'_simulateQ_romImpl_liftM_bind]
  refine bind_congr fun skPrf => ?_
  rw [simulateQ_bind, PRFScheme.simulateQ_prfRealQueryImpl_liftComp,
    run'_simulateQ_romImpl_liftM_bind]
  refine bind_congr fun pkSeed => ?_
  rw [QueryImpl.simulateQ_mapStateTBase_run', prfReal_mapStateTBase_skgLaneImpl,
    romLaneImpl_eq_compose, QueryImpl.simulateQ_compose,
    simulateQ_skgRealImpl_romGameCoreGen]

open scoped Classical in
/-- The success bit of the counted experiment is the outcome of the shared lazy run of
`romGameCore` from the empty cache; the query charge is discarded. -/
theorem fst_map_countedRomExperiment_eq
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    Prod.fst <$> countedRomExperiment core adv =
      (simulateQ (unifFwdImpl (publicHashSpec core) + PublicHash.randomOracle core)
        (romGameCore core adv)).run' ∅ := by
  unfold countedRomExperiment countedRomImpl
  rw [← StateT.run'_map', QueryImpl.fst_map_runAdd_withAddCost]

open scoped Classical in
/-- **In the real `PRF` experiment the reduction wins exactly as often as the forger.**  Its
success probability is `romForgeAdvantage core adv`, not a bound on it. -/
theorem evalDist_prfRealExp_skgPrfReductionGen
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    𝒟[PRFScheme.prfRealExp (skgPrfScheme core) (skgPrfReductionGen core adv)] {true}
      = romForgeAdvantage core adv := by
  rw [romForgeAdvantage, fst_map_countedRomExperiment_eq, prfRealExp_skgPrfReductionGen]

/-! ## The ideal experiment's shape -/

omit [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed] in
/-- **Under the ideal `PRF` handler the reduction's three oracles are one private-sampling
summand in front of two nested lazy random oracles**, the public hash inside and the challenge
function outside.  This is the handler
`VCVio.OracleComp.QueryTracking.RandomOracle.Joint` identifies with a single lazy random oracle on
the sum signature and one joint cache. -/
theorem prfIdeal_mapStateTBase_skgLaneImpl :
    (PRFScheme.prfIdealQueryImpl (D := core.PkSeed × Adrs) (R := core.Y)).mapStateTBase
        (skgLaneImpl core)
      = (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (PublicHash.Cache core)
            (StateT ((core.PkSeed × Adrs) →ₒ core.Y).QueryCache ProbComp)) +
        OracleSpec.nestedRandomOracle (publicHashSpec core)
          ((core.PkSeed × Adrs) →ₒ core.Y) := by
  funext q
  cases q with
  | inl i =>
      ext s
      simp only [QueryImpl.mapStateTBase, skgLaneImpl, QueryImpl.add_apply_inl,
        StateT.run_mk, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_monadLift]
      rw [simulateQ_bind]
      rw [show (monadLift (liftM (OracleSpec.query i)) :
          OracleComp (skgPrfSpec core) (unifSpec.Range i)) =
          OracleComp.liftComp (liftM (OracleSpec.query i) : ProbComp _)
            (skgPrfSpec core) from by rfl]
      rw [PRFScheme.simulateQ_prfIdealQueryImpl_liftComp]
      simp
  | inr q =>
      cases q with
      | inr q =>
          ext s c
          simp only [QueryImpl.mapStateTBase, skgLaneImpl, PRFScheme.functionQuery,
            OracleSpec.nestedRandomOracle, QueryImpl.add_apply_inr, StateT.run_mk,
            StateT.run_monadLift, QueryImpl.liftTarget_apply]
          rcases h : c.toFn q with _ | u <;> simp [h]
      | inl t =>
          ext s c
          have hcache := congrFun (QueryImpl.mapStateTBase_withCaching
            (PRFScheme.prfIdealQueryImpl (D := core.PkSeed × Adrs) (R := core.Y))
            (skgUnifImpl core)) t
          have key : ((PRFScheme.prfIdealQueryImpl (D := core.PkSeed × Adrs)
                (R := core.Y)).mapStateTBase (skgLaneImpl core)) (Sum.inr (Sum.inl t)) =
              ((PRFScheme.prfIdealQueryImpl (D := core.PkSeed × Adrs)
                (R := core.Y)).mapStateTBase (QueryImpl.withCaching (skgUnifImpl core))) t := rfl
          have hunif : ∀ t' : (publicHashSpec core).Domain,
              simulateQ (PRFScheme.prfIdealQueryImpl (D := core.PkSeed × Adrs) (R := core.Y))
                  (skgUnifImpl core t') =
                (liftM (uniformSampleImpl t') :
                  StateT ((core.PkSeed × Adrs) →ₒ core.Y).QueryCache ProbComp _) := by
            intro t'
            rw [skgUnifImpl, PRFScheme.simulateQ_prfIdealQueryImpl_liftComp,
              uniformSampleImpl_apply]
          rw [key, hcache]
          rcases h : s.toFn t with _ | u <;>
            simp [h, hunif, OracleSpec.nestedRandomOracle, OracleSpec.randomOracle,
              QueryImpl.liftBase, Functor.map_map]

/-! ## The hop -/

/-- **The `SKG_PRF` hop, taken in the counted random-oracle lane.**  The forger's advantage in the
counted experiment is at most the secret-value `PRF` distinguishing advantage of a distinguisher
*constructed from that forger*, plus the advantage that survives the hop.

Both right-hand terms are functions of `adv`, and the inequality is unconditional: the real `PRF`
experiment at the reduction *is* the counted experiment
(`evalDist_prfRealExp_skgPrfReductionGen`). -/
theorem romForgeAdvantage_le_skgPrf_add_ideal
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    romForgeAdvantage core adv ≤
      prfAbsAdvantage (skgPrfScheme core) (skgPrfReductionGen core adv)
        + skgPrfIdealAdvantage core adv := by
  rw [← evalDist_prfRealExp_skgPrfReductionGen, skgPrfIdealAdvantage]
  exact prfRealExp_le_prfAbsAdvantage_add_prfIdealExp _ _

end

end SLHDSA.Security
