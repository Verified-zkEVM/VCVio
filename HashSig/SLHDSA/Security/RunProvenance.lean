/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteRouter
public import HashSig.SLHDSA.Security.SecretTraces

/-!
# Provenance of the cached points of the SLH-DSA run

The final cache of the run of SLH-DSA in the random-oracle model (`romSchemeRun`) holds the points
that key generation, the signing oracle, verification and the forger queried. This module shows
that every point an honest algorithm caches is an *honest query* of the run's key pair
(`IsHonestQuery vp pk skPrf`):

1. a tweakable-hash point is at the public seed `PK.seed` and an honest address key
   (`IsHonestKey`: a key of the union ledger `constructionAddresses`, or of a secret child of a
   ledger address);
2. an `H_msg` point is at `(PK.seed, PK.root)`;
3. a `PRF_msg` point is keyed by `SK.prf`.

The forger's points are described by whatever predicate `F pk` its hash queries at the public key
`pk` satisfy, so every cached point is an honest query or satisfies `F pk`
(`isHonestQuery_or_of_mem_support_romSchemeRun`).

## The route

* Key generation, signing and verification run, in the run's monad, the provider-parametric
  programs at the oracle-backed provider `oracleSecret` and the verification program. Their
  queries are honest by the ledger-indexed lemmas of `HashSig.SLHDSA.Security.SecretTraces`
  (`keygenInternalWithSecretM_pred_of_ledger`, `signInternalWithSecretRandomizerM_pred_of_ledger`,
  `verifyInternalM_pred_of_ledger`) at the predicate "every hash query is an honest query of the
  key pair": the tweakable hash at a ledger address is queried at `PK.seed` and that address's
  key, and the provider at a secret child of a ledger address at `PK.seed` and the child's key
  (`isHonestKey_of_inl_mem_childAdrs`). Signing also queries `PRF_msg` once, at `SK.prf`.
* The lazy random oracle caches exactly the points it is queried at, so a predicate that every
  query of a program satisfies holds of every point the program adds to the cache
  (`OracleComp.forall_isSome_of_mem_support_run_simulateQ_romImpl`). The transcript experiment
  threads it through key generation, the forger with its signing oracle, and verification
  (`SignatureAlg.exists_mem_support_run_of_mem_support_run_unforgeableTranscriptExperiment`,
  `SignatureAlg.holds_of_mem_support_run_runWithSigningOracle`).

## Main statements

* `IsHonestQuery`;
* `allQueriesSatisfy_keygenInternalWithSecretM_oracleSecret`, `allQueriesSatisfy_romScheme_sign`,
  `allQueriesSatisfy_verifyInternalM_isHonestQuery`: the honest algorithms issue honest queries
  only;
* `isHonestQuery_or_of_mem_support_romSchemeRun`: every point of the final cache of the run is an
  honest query of the run's key pair or a forger query.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.Security

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-! ## Honest queries -/

variable (vp) in
/-- A query an honest algorithm of the key pair with public key `pk` and message-`PRF` key
`skPrf` may issue: a tweakable-hash query at `PK.seed` and an honest address key, an `H_msg` query
at `(PK.seed, PK.root)`, or a `PRF_msg` query keyed by `skPrf`. -/
@[expose] def IsHonestQuery (pk : PublicKeyCore core) (skPrf : core.SkPrf) :
    (hashSpec core).Domain → Prop
  | .inl (.thash s k _) => s = pk.pkSeed ∧ IsHonestKey vp core k
  | .inl (.hmsg _ s root _) => s = pk.pkSeed ∧ root = pk.pkRoot
  | .inr q => q.skPrf = skPrf

/-! ## The honest algorithms -/

section Algorithms

variable (core) in
/-- **Key generation queries honest queries only.** Key generation at public seed `pkSeed`, with
every secret drawn from the oracle, queries the tweakable hash at `pkSeed` and honest keys only,
so honest queries of every key pair with that seed. -/
theorem allQueriesSatisfy_keygenInternalWithSecretM_oracleSecret (e : core.SkSeed ≃ core.Y)
    (pkSeed : core.PkSeed) (skSeed : core.SkSeed) {pk : PublicKeyCore core}
    (hpk : pk.pkSeed = pkSeed) (skPrf : core.SkPrf) :
    AllQueriesSatisfy (GeneralScheme.keygenInternalWithSecretM core
      (oracleSecret core e pkSeed skSeed) pkSeed : OracleComp (unifSpec + hashSpec core) core.Y)
      (Sum.elim (fun _ => True) (IsHonestQuery vp pk skPrf)) :=
  keygenInternalWithSecretM_pred_of_ledger (AllQueriesSatisfy · _)
    (fun x => allQueriesSatisfy_pure x _) (fun _ _ h₁ h₂ => allQueriesSatisfy_bind h₁ h₂) core
    (fun _ _ hb hab => (allQueriesSatisfy_query_iff _ _).2
      ⟨hpk.symm, isHonestKey_of_inl_mem_childAdrs hb hab⟩)
    pkSeed fun _ ha _ => (allQueriesSatisfy_query_iff _ _).2 ⟨hpk.symm, _, .inl ha, rfl⟩

variable [DecidableEq core.Y]

/-- **Verification queries honest queries only.** Verification against `pk` queries `H_msg` at
`(PK.seed, PK.root)` and the tweakable hash at `PK.seed` and union-ledger keys. -/
theorem allQueriesSatisfy_verifyInternalM_isHonestQuery (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp core) (pk : PublicKeyCore core) (skPrf : core.SkPrf) :
    AllQueriesSatisfy (GeneralScheme.verifyInternalM vp core msg sig pk :
      OracleComp (unifSpec + hashSpec core) Bool)
      (Sum.elim (fun _ => True) (IsHonestQuery vp pk skPrf)) :=
  verifyInternalM_pred_of_ledger (AllQueriesSatisfy · _) (fun x => allQueriesSatisfy_pure x _)
    (fun _ _ h₁ h₂ => allQueriesSatisfy_bind h₁ h₂) core msg sig pk
    (fun _ ha _ => (allQueriesSatisfy_query_iff _ _).2 ⟨rfl, _, .inl ha, rfl⟩)
    ((allQueriesSatisfy_query_iff _ _).2 ⟨rfl, rfl⟩)

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

/-- **Signing queries honest queries only.** Against a secret key carrying the public key's seed
and root, signing draws `opt_rand`, queries `PRF_msg` at `SK.prf`, then `H_msg` at
`(PK.seed, PK.root)` and the tweakable hash at `PK.seed` and honest keys. -/
theorem allQueriesSatisfy_romScheme_sign (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeedDist : ProbComp core.PkSeed)
    {pk : PublicKeyCore core} {sk : SecretKeyCore core} (hs : sk.pkSeed = pk.pkSeed)
    (hr : sk.pkRoot = pk.pkRoot) (msg : List Byte) :
    AllQueriesSatisfy ((romScheme core e optRand pkSeedDist).sign pk sk msg)
      (Sum.elim (fun _ => True) (IsHonestQuery vp pk sk.skPrf)) := by
  rw [romScheme_sign]
  refine allQueriesSatisfy_bind (allQueriesSatisfy_liftM_sum_elim _ _) fun addrnd =>
    allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).2 rfl) fun R => ?_
  exact signInternalWithSecretRandomizerM_pred_of_ledger (AllQueriesSatisfy · _)
    (fun x => allQueriesSatisfy_pure x _) (fun _ _ h₁ h₂ => allQueriesSatisfy_bind h₁ h₂) core
    (fun _ _ hb hab => (allQueriesSatisfy_query_iff _ _).2
      ⟨hs, isHonestKey_of_inl_mem_childAdrs hb hab⟩)
    msg sk.pkSeed sk.pkRoot R
    (fun _ ha _ => (allQueriesSatisfy_query_iff _ _).2 ⟨hs, _, .inl ha, rfl⟩)
    ((allQueriesSatisfy_query_iff _ _).2 ⟨hs, hr⟩)

end Algorithms

/-! ## The run -/

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf] [DecidableEq core.Y]
  [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-- Key generation of `romScheme`, run from the empty cache, outputs a public seed drawn from the
seed distribution and a secret key carrying the public key's seed and root, and caches only honest
queries of the key pair. -/
theorem isHonestQuery_of_mem_support_run_romScheme_keygen (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeedDist : ProbComp core.PkSeed)
    {z : (PublicKeyCore core × SecretKeyCore core) × (hashSpec core).QueryCache}
    (hz : z ∈ support ((simulateQ (hashSpec core).romImpl
      (romScheme core e optRand pkSeedDist).keygen).run ∅)) :
    z.1.1.pkSeed ∈ support pkSeedDist ∧ z.1.2.pkSeed = z.1.1.pkSeed ∧
      z.1.2.pkRoot = z.1.1.pkRoot ∧ ∀ q, (z.2 q).isSome → IsHonestQuery vp z.1.1 z.1.2.skPrf q := by
  obtain ⟨pkSeed, hpk, hz⟩ := roSim.exists_mem_support_run_of_mem_support_run_liftM_bind _ _ _ hz
  unfold romKeygenAt at hz
  obtain ⟨skSeed, -, hz⟩ := roSim.exists_mem_support_run_of_mem_support_run_liftM_bind _ _ _ hz
  obtain ⟨skPrf, -, hz⟩ := roSim.exists_mem_support_run_of_mem_support_run_liftM_bind _ _ _ hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨pkRoot, c⟩, hroot, hz⟩ := hz
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨hpk, rfl, rfl, forall_isSome_of_mem_support_run_simulateQ_romImpl
    (allQueriesSatisfy_keygenInternalWithSecretM_oracleSecret core e pkSeed skSeed
      (pk := ⟨pkSeed, pkRoot⟩) rfl skPrf)
    (fun _ h => by simp at h) hroot⟩

/-- **Provenance of the cached points of the run.** Against a forger whose hash queries at every
public key `pk` satisfy `F pk`, every point of the final cache of `romSchemeRun` is an honest query
of the run's key pair (`IsHonestQuery`: a tweakable-hash point at `PK.seed` and an honest address
key, an `H_msg` point at `(PK.seed, PK.root)`, a `PRF_msg` point keyed by `SK.prf`) or satisfies
`F` at the run's public key. -/
theorem isHonestQuery_or_of_mem_support_romSchemeRun (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeedDist : ProbComp core.PkSeed)
    {adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)}
    (F : PublicKeyCore core → (hashSpec core).Domain → Prop)
    (hadv : ∀ pk, AllQueriesSatisfy (adv.main pk)
      (Sum.elim (Sum.elim (fun _ => True) (F pk)) fun _ => True))
    {z : RomOutcome vp core × (hashSpec core).QueryCache}
    (hz : z ∈ support (romSchemeRun core e optRand pkSeedDist adv)) :
    ∀ q, (z.2 q).isSome → IsHonestQuery vp z.1.pk z.1.sk.skPrf q ∨ F z.1.pk q := by
  obtain ⟨s₁, s₂, hk, hf, hv⟩ :=
    exists_mem_support_run_of_mem_support_run_unforgeableTranscriptExperiment
      (hashSpec core).romImpl adv hz
  obtain ⟨-, hs, hr, hk⟩ :=
    isHonestQuery_of_mem_support_run_romScheme_keygen e optRand pkSeedDist hk
  let P : (hashSpec core).Domain → Prop := fun q =>
    IsHonestQuery vp z.1.pk z.1.sk.skPrf q ∨ F z.1.pk q
  have hP : ∀ {Q : (hashSpec core).Domain → Prop}, (∀ q, Q q → P q) →
      ∀ t : ℕ ⊕ (hashSpec core).Domain,
        Sum.elim (fun _ => True) Q t → Sum.elim (fun _ => True) P t := fun hQ t ht => by
    rcases t with n | t
    exacts [trivial, hQ t ht]
  have hf := holds_of_mem_support_run_runWithSigningOracle (hashSpec core).romImpl _ z.1.pk z.1.sk
    (allowed := Sum.elim (fun _ => True) (F z.1.pk)) (fun _ c => ∀ q, (c q).isSome → P q)
    (fun t ht _ _ hc _ hz => forall_isSome_of_mem_support_run_romImpl
      (hP (fun _ => Or.inr) t ht) hc hz)
    (fun msg _ _ hc _ hz => forall_isSome_of_mem_support_run_simulateQ_romImpl
      ((allQueriesSatisfy_romScheme_sign e optRand pkSeedDist hs hr msg).mono
        (hP fun _ => Or.inl)) hc hz)
    (hadv z.1.pk) (fun q hq => Or.inl (hk q hq)) hf
  exact forall_isSome_of_mem_support_run_simulateQ_romImpl
    ((allQueriesSatisfy_verifyInternalM_isHonestQuery z.1.msg z.1.sig z.1.pk z.1.sk.skPrf).mono
      (hP fun _ => Or.inl)) hf hv

/-- The public seed of every transcript of the run is drawn from the seed distribution. -/
theorem pkSeed_mem_support_of_mem_support_romSchemeRun (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeedDist : ProbComp core.PkSeed)
    {adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)}
    {z : RomOutcome vp core × (hashSpec core).QueryCache}
    (hz : z ∈ support (romSchemeRun core e optRand pkSeedDist adv)) :
    z.1.pk.pkSeed ∈ support pkSeedDist :=
  let ⟨_, _, hk, _⟩ := exists_mem_support_run_of_mem_support_run_unforgeableTranscriptExperiment
    (hashSpec core).romImpl adv hz
  (isHonestQuery_of_mem_support_run_romScheme_keygen e optRand pkSeedDist hk).1

end SLHDSA.Security
