/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.RomSchemeRun
public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed

/-!
# The secret-free run of SLH-DSA

At a fixed public seed, the run of SLH-DSA in the random-oracle model (`romSchemeRun`) is the
hidden-seed real game of `VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed` applied to a
program that never mentions a secret seed. Every WOTS+ and FORS secret value and every message
randomizer is a *derivation* query, and the secret seeds enter only through the encoding that
answers a derivation by a public query.

* `DeriveQuery core` indexes the derivations: the secret value at the oracle key of a secret-key
  address (`PrfKey core`), and the randomizer at `(opt_rand, M)`. A secret value is indexed by
  its key, not its address, so two secret-key addresses with one key derive one value, as they
  do under the real oracle.
* `secretEncoding core e pkSeed` is the `SecretEncoding` that places the secret value at key `k`
  at the `F` query `thash PK.seed k [e SK.seed]`, FIPS 205's `PRF(PK.seed, SK.seed, ADRS)`, and
  the randomizer at the `PRF_msg` query `⟨SK.prf, opt_rand, M⟩`.
* `deriveSecret core` is the derivation-backed secret provider, and `deriveScheme core optRand
  pkSeed` is SLH-DSA at public seed `pkSeed` with every secret value drawn from it and every
  randomizer drawn as a derivation. Its secret key is the public key: the scheme holds no secret.
* `deriveAdversary core adv` is a forger of `romScheme` lifted into the derivation world, and
  `fill core s` rebuilds the transcript of `romScheme` from the transcript of `deriveScheme` and
  the secret seeds `s`.

`romSchemeRun_pure_eq` is the resulting equation: the run at public seed `pkSeed` draws the
secret seeds `s` uniformly, runs the transcript experiment of `deriveScheme` against
`deriveAdversary core adv` in the real game `(secretEncoding core e pkSeed).realImpl s` from the
empty cache, and rebuilds the transcript with `fill core s`. `prEvent_romSchemeRun_pure_eq` is
its form for the probability of an event, the shape `SecretEncoding.prEvent_realImpl_le_add`
consumes at each fixed `s`.

## Scope

* The statements are per public seed: the scheme is `romScheme core e optRand (pure pkSeed)`.
* This module states equations of runs; it bounds no probability.
* Nothing here is quantum.

## Labels

*Derivations*: `PrfKey`, `DeriveQuery`, `deriveSpec`, `secretEncoding`, `secretEncoding_enc_inl`,
`secretEncoding_enc_inr`, `deriveSecret`, `deriveHom`, `simulateQ_deriveImpl_deriveSecret`.

*The secret-free scheme*: `DeriveOutcome`, `fillSk`, `fill`, `deriveScheme`, `deriveAdversary`.

*The experiment*: `mapOracles_deriveImpl_deriveAdversary`,
`unforgeableTranscriptExperiment_romScheme_pure_eq`.

*The run*: `romSchemeRun_pure_eq`, `prEvent_romSchemeRun_pure_eq`.
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec SignatureAlg

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-! ## Derivations -/

/-- The oracle key of a secret-key address. -/
abbrev PrfKey : Type := {k : core.AdrsKey // ∃ a : Adrs, a.IsSecretKey ∧ core.adrsToKey a = k}

/-- A derivation query: the secret value at the oracle key of a secret-key address, or the
message randomizer at `(opt_rand, M)`. -/
abbrev DeriveQuery : Type := PrfKey core ⊕ (core.Y × List Byte)

/-- Programs with uniform sampling, the hash oracles `hashSpec core`, and derivation queries
answered with nodes. -/
abbrev deriveSpec := (hashSpec core).withDerivations (DeriveQuery core) core.Y

/-- The encoding of derivations at public seed `pkSeed`: under secret seeds `s`, the secret value
at key `k` is the `F` query `thash PK.seed k [e SK.seed]`, which is `PRF(PK.seed, SK.seed, ADRS)`
at every address with key `k`, and the randomizer at `(opt_rand, M)` is the `PRF_msg` query
`⟨SK.prf, opt_rand, M⟩`. -/
@[expose] def secretEncoding (e : core.SkSeed ≃ core.Y) (pkSeed : core.PkSeed) :
    SecretEncoding (hashSpec core) (core.SkSeed × core.SkPrf) (DeriveQuery core) core.Y where
  enc s x := match x with
    | .inl k => .inl (.thash pkSeed k.1 [e s.1])
    | .inr (o, msg) => .inr ⟨s.2, o, msg⟩
  range_eq s x := by rcases x with k | ⟨o, msg⟩ <;> rfl
  injective s := by
    rintro (k | ⟨o, m⟩) (k' | ⟨o', m'⟩) h
    · simp only [Sum.inl.injEq, PublicHashQuery.thash.injEq] at h
      exact congrArg Sum.inl (Subtype.ext h.2.1)
    · cases h
    · cases h
    · simp only [Sum.inr.injEq, PrfMsgQuery.mk.injEq] at h
      rw [h.2.1, h.2.2]

/-- The secret value at key `k` is encoded at `thash PK.seed k [e SK.seed]`. -/
@[simp] theorem secretEncoding_enc_inl (e : core.SkSeed ≃ core.Y) (pkSeed : core.PkSeed)
    (s : core.SkSeed × core.SkPrf) (k : PrfKey core) :
    (secretEncoding core e pkSeed).enc s (.inl k) = .inl (.thash pkSeed k.1 [e s.1]) := rfl

/-- The randomizer at `(opt_rand, M)` is encoded at `PRF_msg(SK.prf, opt_rand, M)`. -/
@[simp] theorem secretEncoding_enc_inr (e : core.SkSeed ≃ core.Y) (pkSeed : core.PkSeed)
    (s : core.SkSeed × core.SkPrf) (o : core.Y) (msg : List Byte) :
    (secretEncoding core e pkSeed).enc s (.inr (o, msg)) = .inr ⟨s.2, o, msg⟩ := rfl

variable [SampleableType core.Y]

/-- The derivation-backed secret provider: the secret value at a secret-key address is the
derivation at its key. The honest programs read secrets only at secret-key addresses; at any
other address the provider draws a uniform node. -/
@[expose] def deriveSecret (a : Adrs) : OracleComp (deriveSpec core) core.Y :=
  if h : a.IsSecretKey then
    (query (spec := deriveSpec core) (.inr (.inl ⟨core.adrsToKey a, a, h, rfl⟩)) :
      OracleComp (deriveSpec core) core.Y)
  else ($ᵗ core.Y : ProbComp core.Y)

/-- Answering derivations through the encoding at secret seeds `s`, as a morphism that preserves
the public hash queries. -/
def deriveHom (e : core.SkSeed ≃ core.Y) (pkSeed : core.PkSeed) (s : core.SkSeed × core.SkPrf) :
    HasQuery.QueryHom (publicHashSpec core) (OracleComp (deriveSpec core))
      (OracleComp (unifSpec + hashSpec core)) where
  toMonadHom := simulateQ' ((secretEncoding core e pkSeed).deriveImpl s)
  map_query' _ := rfl

/-- At a secret-key address, the derivation-backed secret answered through the encoding at secret
seeds `s` is the oracle-backed secret `PRF(PK.seed, SK.seed, ADRS)`. -/
theorem simulateQ_deriveImpl_deriveSecret (e : core.SkSeed ≃ core.Y) (pkSeed : core.PkSeed)
    (s : core.SkSeed × core.SkPrf) {a : Adrs} (ha : a.IsSecretKey) :
    simulateQ ((secretEncoding core e pkSeed).deriveImpl s) (deriveSecret core a) =
      oracleSecret core e pkSeed s.1 a := by
  simp only [deriveSecret, ha, dite_true, oracleSecret, PublicHash.f]
  rfl

/-! ## The secret-free scheme -/

/-- The transcript of the unforgeability experiment of a scheme whose secret key is the public
key. -/
abbrev DeriveOutcome : Type :=
  UnforgeableTranscript (List Byte) (PublicKeyCore core) (PublicKeyCore core)
    (GeneralScheme.SignatureCore vp core)

/-- The secret key with secret seeds `s` and public part `pk`. -/
@[expose] def fillSk (s : core.SkSeed × core.SkPrf) (pk : PublicKeyCore core) :
    SecretKeyCore core :=
  ⟨s.1, s.2, pk.pkSeed, pk.pkRoot⟩

/-- The transcript of `romScheme` rebuilt from a transcript of `deriveScheme` and the secret
seeds `s`: its secret key carries `s` and the public part of the transcript's key. -/
@[expose] def fill (s : core.SkSeed × core.SkPrf) (z : DeriveOutcome core) : RomOutcome vp core :=
  z.mapSk (fillSk core s)

variable [DecidableEq core.Y]

/-- SLH-DSA at public seed `pkSeed` with no secret: key generation computes the root with every
secret value drawn from `deriveSecret`, and signing draws `opt_rand` from `optRand`, the randomizer
as the derivation at `(opt_rand, M)`, and every secret value from `deriveSecret`. The secret key is
the public key. -/
@[expose] def deriveScheme (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) :
    SignatureAlg (OracleComp (deriveSpec core)) (List Byte) (PublicKeyCore core)
      (PublicKeyCore core) (GeneralScheme.SignatureCore vp core) where
  keygen := do
    let pkRoot ← GeneralScheme.keygenInternalWithSecretM core (deriveSecret core) pkSeed
    return (⟨pkSeed, pkRoot⟩, ⟨pkSeed, pkRoot⟩)
  sign pk sk msg := do
    let addrnd ← (optRand pk : ProbComp core.Y)
    let R ← (query (spec := deriveSpec core) (.inr (.inr (addrnd, msg))) :
      OracleComp (deriveSpec core) core.Y)
    GeneralScheme.signInternalWithSecretRandomizerM core (deriveSecret core) msg sk.pkSeed
      sk.pkRoot R
  verify pk msg sig := GeneralScheme.verifyInternalM vp core msg sig pk

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

/-- A forger of `romScheme` as a forger of `deriveScheme`: its sampling and hash queries are lifted
into the derivation world, and it makes no derivation query. -/
@[expose] def deriveAdversary {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) (pkSeed : core.PkSeed) :
    UnforgeableAdversary (deriveScheme core optRand pkSeed) :=
  adv.mapOracles (sigAlg' := deriveScheme core optRand pkSeed)
    ((hashSpec core).withDerivationsLift (DeriveQuery core) core.Y)

/-! ## The experiment -/

/-- The lifted forger, its queries answered through the encoding at secret seeds `s`, is the
forger itself. -/
theorem mapOracles_deriveImpl_deriveAdversary (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed)))
    (s : core.SkSeed × core.SkPrf) :
    (deriveAdversary core adv pkSeed).mapOracles ((secretEncoding core e pkSeed).deriveImpl s)
        (sigAlg' := (deriveScheme core optRand pkSeed).map
          (simulateQ' ((secretEncoding core e pkSeed).deriveImpl s))) =
      ⟨adv.main⟩ := by
  rw [deriveAdversary, UnforgeableAdversary.mapOracles_mapOracles,
    SecretEncoding.deriveImpl_comp_withDerivationsLift, UnforgeableAdversary.mapOracles_id'_eq_mk]

/-- **The experiment of `romScheme` at a public seed is the secret-free experiment with its
derivations answered at uniform secret seeds.** The transcript experiment draws the secret
seeds `s` uniformly, runs the transcript experiment of `deriveScheme` against the lifted forger
with every derivation answered through the encoding at `s`, and rebuilds the transcript with
`fill core s`. -/
theorem unforgeableTranscriptExperiment_romScheme_pure_eq (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))) :
    unforgeableTranscriptExperiment adv =
      (liftM ($ᵗ (core.SkSeed × core.SkPrf)) : OracleComp (unifSpec + hashSpec core) _) >>=
        fun s => fill core s <$> simulateQ ((secretEncoding core e pkSeed).deriveImpl s)
          (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed)) := by
  rw [unforgeableTranscriptExperiment_eq_bind_mapSk_of_keygen_eq_map _
    (fun s => (deriveScheme core optRand pkSeed).map
      (simulateQ' ((secretEncoding core e pkSeed).deriveImpl s)))
    (liftM ($ᵗ (core.SkSeed × core.SkPrf)))
    (fun s => GeneralScheme.keygenInternalWithSecretM core (oracleSecret core e pkSeed s.1) pkSeed)
    (fun _ pkRoot => ((⟨pkSeed, pkRoot⟩ : PublicKeyCore core),
      (⟨pkSeed, pkRoot⟩ : PublicKeyCore core)))
    (fun s => fillSk core s) ?hkg ?hkgA ?hsign ?hver adv]
  · refine bind_congr fun s => ?_
    rw [simulateQ_unforgeableTranscriptExperiment, mapOracles_deriveImpl_deriveAdversary]
    rfl
  case hkg =>
    have hprod : ($ᵗ (core.SkSeed × core.SkPrf) : ProbComp _) =
        (·, ·) <$> ($ᵗ core.SkSeed) <*> ($ᵗ core.SkPrf) := rfl
    rw [romScheme_keygen, hprod]
    simp only [seq_eq_bind_map, map_eq_bind_pure_comp, liftM_bind, liftM_pure, bind_assoc,
      pure_bind, Function.comp_apply, fillSk]
  case hkgA =>
    intro s
    rw [map_keygen]
    have hnat : simulateQ ((secretEncoding core e pkSeed).deriveImpl s)
        (GeneralScheme.keygenInternalWithSecretM core (deriveSecret core) pkSeed) =
          GeneralScheme.keygenInternalWithSecretM core (oracleSecret core e pkSeed s.1) pkSeed :=
      GeneralScheme.keygenInternalWithSecretM_natural core (deriveHom core e pkSeed s)
        (deriveSecret core) (oracleSecret core e pkSeed s.1)
        (fun _ ha => simulateQ_deriveImpl_deriveSecret core e pkSeed s ha) pkSeed
    simp only [deriveScheme, simulateQ_bind, simulateQ_pure, hnat, map_eq_bind_pure_comp]
    rfl
  case hsign =>
    intro s pkRoot msg
    have hnat : ∀ R, simulateQ ((secretEncoding core e pkSeed).deriveImpl s)
        (GeneralScheme.signInternalWithSecretRandomizerM core (deriveSecret core) msg pkSeed
          pkRoot R) =
        GeneralScheme.signInternalWithSecretRandomizerM core (oracleSecret core e pkSeed s.1) msg
          pkSeed pkRoot R := fun R =>
      GeneralScheme.signInternalWithSecretRandomizerM_natural core (deriveHom core e pkSeed s)
        (deriveSecret core) (oracleSecret core e pkSeed s.1)
        (fun _ ha => simulateQ_deriveImpl_deriveSecret core e pkSeed s ha) msg pkSeed pkRoot R
    rw [romScheme_sign, map_sign]
    simp only [deriveScheme, fillSk, simulateQ_bind, hnat,
      SecretEncoding.simulateQ_deriveImpl_liftM]
    rfl
  case hver =>
    intro s
    funext pk msg sig
    rw [romScheme_verify, map_verify]
    exact (GeneralScheme.verifyInternalM_natural vp core (deriveHom core e pkSeed s) msg sig
      pk).symm

/-! ## The run -/

variable [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]
  [DecidableEq core.SkPrf]

/-- **The run of SLH-DSA at a public seed is the real hidden-seed game of the secret-free
experiment, averaged over the secret seeds.** The run draws the secret seeds `s` uniformly, runs
the transcript experiment of `deriveScheme` against the lifted forger in the real game
`(secretEncoding core e pkSeed).realImpl s` from the empty cache, and rebuilds the transcript with
`fill core s`, keeping the final cache. -/
theorem romSchemeRun_pure_eq (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))) :
    romSchemeRun core e optRand (pure pkSeed) adv = do
      let s ← $ᵗ (core.SkSeed × core.SkPrf)
      let z ← (simulateQ ((secretEncoding core e pkSeed).realImpl s)
        (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed))).run ∅
      return (fill core s z.1, z.2) := by
  rw [romSchemeRun, unforgeableTranscriptExperiment_romScheme_pure_eq, simulateQ_bind,
    StateT.run_bind, simulateQ_romImpl_liftM_run, bind_map_left]
  refine bind_congr fun s => ?_
  rw [simulateQ_map, StateT.run_map, SecretEncoding.realImpl, QueryImpl.simulateQ_compose,
    map_eq_bind_pure_comp]
  rfl

/-- An event of the run of SLH-DSA at a public seed has the probability of the event, read on the
rebuilt transcript, when the secret seeds `s` are drawn uniformly and the secret-free experiment
runs in the real game `(secretEncoding core e pkSeed).realImpl s` from the empty cache. -/
theorem prEvent_romSchemeRun_pure_eq (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed)))
    (Q : RomOutcome vp core × (hashSpec core).QueryCache → Prop) :
    Pr{let z ← romSchemeRun core e optRand (pure pkSeed) adv}[Q z] =
      Pr{let s ← $ᵗ (core.SkSeed × core.SkPrf)
         let z ← (simulateQ ((secretEncoding core e pkSeed).realImpl s)
           (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed))).run ∅}[
        Q (fill core s z.1, z.2)] := by
  rw [romSchemeRun_pure_eq]
  simp only [bind_assoc, pure_bind]

end SLHDSA.Security
