/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteClash
public import HashSig.SLHDSA.Security.ByteConformance

/-!
# The classification of SHAKE256 clashes, checked

`HashSig.SLHDSA.Security.ByteClash` shows that on the support of the routed three-oracle run a
clash of SHAKE256 strings is an `H_msg` point at `SK.prf` (Fev), `SK.prf = PK.seed` (K1) or, through
the weak-key `H_msg` event, a weak public key (BK). This file checks it at the parameters of
FIPS 205.

* **At the parameters of the 12 FIPS 205 parameter sets**, with `n ≤ 32`, `n ≤ m` and `16 ≤ n`
  discharged: the honest key generation, the routed forger's route-fixedness, the provenance of
  the tweakable-hash points, the classification, the weak-key `H_msg` event as a property of the
  public key, and the bound on the strong advantage.
* **The shape consumed downstream**: the bound splits into the probability of a win or a hit of
  the message-`PRF` key, `RunPrfKeyHit id pkSeed`, and the probability of BK.
* **The ledger-indexed traces at another predicate**: the construction predicate
  `QueriesWithinConstructionTargets` of internal key generation and signing at the provider
  computing every secret by `core.PRF`.
* **A concrete clash at SLH-DSA-SHAKE-128s**: the `PRF_msg` string `SK.prf ‖ PK.seed ‖ PK.root` is
  the `H_msg` string `SK.prf ‖ PK.seed ‖ PK.root` with no message. In the two-point cache holding
  both, with `SK.prf ≠ PK.seed`, the classification can only conclude Fev.
* **A concrete weak-key clash at SLH-DSA-SHAKE-128s**: when `PK.seed ‖ PK.root` is the key of a
  ledger address, the `H_msg` string `PK.seed ‖ PK.seed ‖ PK.root` is the string of the
  tweakable-hash query at `PK.seed`, that key and no input. In the two-point cache holding both,
  with `SK.prf ≠ PK.seed`, the classification can only conclude the weak-key `H_msg` event, and
  the public key is weak.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.ByteClashTest

open Concrete Security

/-- SLH-DSA-SHAKE-128s. -/
abbrev vp128s : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_128s

/-! ## At the parameters of the 12 FIPS 205 parameter sets -/

/-- Key generation at the oracle-backed provider queries honest queries of every key pair with
its public seed only. -/
example (set : FipsParameterSet) (e : (shakeCore set.validatedParams).SkSeed ≃
      (shakeCore set.validatedParams).Y) (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (skSeed : (shakeCore set.validatedParams).SkSeed)
    (pkRoot : (shakeCore set.validatedParams).Y) (skPrf : (shakeCore set.validatedParams).SkPrf) :
    AllQueriesSatisfy (GeneralScheme.keygenInternalWithSecretM (shakeCore set.validatedParams)
      (oracleSecret (shakeCore set.validatedParams) e pkSeed skSeed) pkSeed :
        OracleComp (unifSpec + hashSpec (shakeCore set.validatedParams)) _)
      (Sum.elim (fun _ => True) (IsHonestQuery set.validatedParams ⟨pkSeed, pkRoot⟩ skPrf)) :=
  allQueriesSatisfy_keygenInternalWithSecretM_oracleSecret _ e pkSeed skSeed rfl skPrf

/-- The routed forger queries route-fixed points only. -/
example (set : FipsParameterSet)
    {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    {pkSeedDist : ProbComp (shakeCore set.validatedParams).PkSeed}
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams optRand pkSeedDist))
    (pk : PublicKeyCore (shakeCore set.validatedParams)) :
    AllQueriesSatisfy ((routeAdv _ set.n_le_32 set.n_le_m adv).main pk)
      (Sum.elim (Sum.elim (fun _ => True) fun q =>
        (shakeEncoding _ set.n_le_32 set.n_le_m pk.pkSeed).route (encode _ q) = some q)
        fun _ => True) :=
  allQueriesSatisfy_routeAdv_main set.n_le_32 set.n_le_m adv pk

/-- Every tweakable-hash point of the routed run is at the run's public seed and an honest key. -/
example (set : FipsParameterSet)
    {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    {pkSeedDist : ProbComp (shakeCore set.validatedParams).PkSeed}
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams optRand pkSeedDist))
    {z : RomOutcome set.validatedParams (shakeCore set.validatedParams) ×
      (hashSpec (shakeCore set.validatedParams)).QueryCache}
    (hz : z ∈ support (romSchemeRun (shakeCore set.validatedParams) (Equiv.refl _) optRand
      pkSeedDist (routeAdv _ set.n_le_32 set.n_le_m adv)))
    {s : (shakeCore set.validatedParams).PkSeed} {k : (shakeCore set.validatedParams).AdrsKey}
    {xs : List (shakeCore set.validatedParams).Y} (hq : (z.2 (.inl (.thash s k xs))).isSome) :
    s = z.1.pk.pkSeed ∧ IsHonestKey set.validatedParams (shakeCore set.validatedParams) k :=
  eq_and_isHonestKey_of_mem_support_romSchemeRun_routeAdv set.n_le_32 set.n_le_m adv hz hq

/-- The classification with the `opt_rand` of a `PRF_msg` clash, both signing modes: a clash
through a cached `H_msg` point at `SK.prf` also caches a `PRF_msg` point keyed by `SK.prf` with
`opt_rand = PK.seed`. -/
example (set : FipsParameterSet)
    {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams optRand (pure pkSeed)))
    {z : RomOutcome set.validatedParams (shakeCore set.validatedParams) ×
      (hashSpec (shakeCore set.validatedParams)).QueryCache}
    (hz : z ∈ support (romSchemeRun (shakeCore set.validatedParams) (Equiv.refl _) optRand
      (pure pkSeed) (routeAdv _ set.n_le_32 set.n_le_m adv)))
    (h : (shakeEncoding _ set.n_le_32 set.n_le_m pkSeed).Clash z.2) :
    ((RunHmsgAtPrfKey id z ∧ PrfMsgAt z.1.sk.skPrf pkSeed z.2) ∨ z.1.sk.skPrf = pkSeed) ∨
      IsWeakKey _ z.1.pk :=
  runPrfKeyClash_or_isWeakKey_of_clash set.n_le_32 set.n_le_m set.sixteen_le_n pkSeed adv hz h

/-- The weak-key `H_msg` event makes the public key weak. -/
example (set : FipsParameterSet) {pkSeed : (shakeCore set.validatedParams).PkSeed}
    {pkRoot : (shakeCore set.validatedParams).Y}
    {c : (hashSpec (shakeCore set.validatedParams)).QueryCache}
    (h : HmsgAtWeakKey pkSeed pkRoot c) : IsWeakKey _ ⟨pkSeed, pkRoot⟩ :=
  isWeakKey_of_hmsgAtWeakKey set.sixteen_le_n h

/-- The bound on the strong advantage, both signing modes. -/
example (set : FipsParameterSet)
    (optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y)
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme set.validatedParams optRand (pure pkSeed))) :
    shakeStrongAdvantage _ adv ≤
      Pr{let z ← romSchemeRun (shakeCore set.validatedParams) (Equiv.refl _) optRand
          (pure pkSeed) (routeAdv _ set.n_le_32 set.n_le_m adv.toUnforgeableAdversary)}[
        (z.1.strongWins = true ∨ RunPrfKeyHit id pkSeed z) ∨ IsWeakKey _ z.1.pk] :=
  shakeStrongAdvantage_pure_le_strongWins_or_runPrfKeyHit_or_isWeakKey set.n_le_32 set.n_le_m
    set.sixteen_le_n pkSeed adv

/-! ## The shape consumed downstream -/

/-- The bound splits into the probability that the routed run wins strongly or hits the
message-`PRF` key, and the probability of BK. -/
example (set : FipsParameterSet)
    (optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y)
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme set.validatedParams optRand (pure pkSeed))) :
    shakeStrongAdvantage _ adv ≤
      Pr{let z ← romSchemeRun (shakeCore set.validatedParams) (Equiv.refl _) optRand
          (pure pkSeed) (routeAdv _ set.n_le_32 set.n_le_m adv.toUnforgeableAdversary)}[
        z.1.strongWins = true ∨ RunPrfKeyHit id pkSeed z] +
      Pr{let z ← romSchemeRun (shakeCore set.validatedParams) (Equiv.refl _) optRand
          (pure pkSeed) (routeAdv _ set.n_le_32 set.n_le_m adv.toUnforgeableAdversary)}[
        IsWeakKey _ z.1.pk] :=
  (shakeStrongAdvantage_pure_le_strongWins_or_runPrfKeyHit_or_isWeakKey set.n_le_32 set.n_le_m
    set.sixteen_le_n pkSeed adv).trans (prEvent_or_le _ _ _)

/-! ## The ledger-indexed traces at another predicate -/

/-- Internal key generation at the provider computing every secret by `core.PRF` queries only
union-ledger tweaks. -/
example (set : FipsParameterSet) (skSeed : (shakeCore set.validatedParams).SkSeed)
    (pkSeed : (shakeCore set.validatedParams).PkSeed) :
    QueriesWithinConstructionTargets (shakeCore set.validatedParams)
      (GeneralScheme.keygenInternalWithSecretM (shakeCore set.validatedParams)
        (fun a => pure ((shakeCore set.validatedParams).PRF pkSeed skSeed a)) pkSeed :
          OracleComp (publicHashSpec (shakeCore set.validatedParams)) _) :=
  keygenInternalWithSecretM_pred_of_ledger (QueriesWithinConstructionTargets _)
    (QueriesWithinConstructionTargets.pure _) (fun _ _ h₁ h₂ => h₁.bind h₂) _
    (fun _ _ _ _ => QueriesWithinConstructionTargets.pure _ _) pkSeed
    fun a ha xs => publicHash_tl_queriesWithinConstructionTargets_of_mem _ pkSeed a xs ha

/-- Internal signing at the provider computing every secret by `core.PRF` queries only
union-ledger tweaks. -/
example (set : FipsParameterSet) (skSeed : (shakeCore set.validatedParams).SkSeed)
    (pkSeed : (shakeCore set.validatedParams).PkSeed) (msg : List Byte)
    (pkRoot R : (shakeCore set.validatedParams).Y) :
    QueriesWithinConstructionTargets (shakeCore set.validatedParams)
      (GeneralScheme.signInternalWithSecretRandomizerM (shakeCore set.validatedParams)
        (fun a => pure ((shakeCore set.validatedParams).PRF pkSeed skSeed a)) msg pkSeed pkRoot
          R : OracleComp (publicHashSpec (shakeCore set.validatedParams)) _) :=
  signInternalWithSecretRandomizerM_pred_of_ledger (QueriesWithinConstructionTargets _)
    (QueriesWithinConstructionTargets.pure _) (fun _ _ h₁ h₂ => h₁.bind h₂) _
    (fun _ _ _ _ => QueriesWithinConstructionTargets.pure _ _) msg pkSeed pkRoot R
    (fun a ha xs => publicHash_tl_queriesWithinConstructionTargets_of_mem _ pkSeed a xs ha)
    (publicHash_hmsg_queriesWithinConstructionTargets _ R pkSeed pkRoot msg)

/-! ## A concrete clash at SLH-DSA-SHAKE-128s -/

/-- A public seed. -/
def seed : (shakeCore vp128s).PkSeed :=
  (⟨#[3, 10, 17, 24, 31, 38, 45, 52, 59, 66, 73, 80, 87, 94, 101, 108], rfl⟩ : Bytes 16)

/-- A message-`PRF` key, distinct from the public seed. -/
def skPrf : (shakeCore vp128s).SkPrf :=
  (⟨#[1, 14, 27, 40, 53, 66, 79, 92, 105, 118, 131, 144, 157, 170, 183, 196], rfl⟩ : Bytes 16)

/-- A root. -/
def root : (shakeCore vp128s).Y :=
  (⟨#[11, 16, 21, 26, 31, 36, 41, 46, 51, 56, 61, 66, 71, 76, 81, 86], rfl⟩ : Bytes 16)

/-- The signer's `PRF_msg` query at `opt_rand = PK.seed` on the message `PK.root`. -/
abbrev prfPoint : (hashSpec (shakeCore vp128s)).Domain :=
  .inr ⟨skPrf, seed, Vector.toList (root : Bytes 16)⟩

/-- The `H_msg` query at randomizer `SK.prf`, the public key, and no message. -/
abbrev hmsgPoint : (hashSpec (shakeCore vp128s)).Domain := .inl (.hmsg skPrf seed root [])

/-- The two strings coincide. -/
example : encode vp128s prfPoint = encode vp128s hmsgPoint := by decide

/-- The cache holding both points. -/
noncomputable def cache : (hashSpec (shakeCore vp128s)).QueryCache :=
  ((∅ : (hashSpec (shakeCore vp128s)).QueryCache).cacheQuery prfPoint root).cacheQuery hmsgPoint
    (Vector.replicate _ 0)

theorem cache_apply_of_ne {q : (hashSpec (shakeCore vp128s)).Domain} (h₁ : q ≠ prfPoint)
    (h₂ : q ≠ hmsgPoint) : cache q = none := by
  rw [cache, QueryCache.cacheQuery_of_ne _ _ h₂, QueryCache.cacheQuery_of_ne _ _ h₁,
    QueryCache.empty_apply]

theorem isSome_cache_prfPoint : (cache prfPoint).isSome := by
  rw [cache, QueryCache.cacheQuery_of_ne _ _ (by decide), QueryCache.cacheQuery_self]
  rfl

theorem isSome_cache_hmsgPoint : (cache hmsgPoint).isSome := by
  rw [cache, QueryCache.cacheQuery_self]
  rfl

/-- The cache has the provenance of a run at `(seed, root)` with key `skPrf`. -/
theorem cache_provenance (q : (hashSpec (shakeCore vp128s)).Domain) (hq : (cache q).isSome) :
    shakeRoute vp128s (IsHonestKey vp128s (shakeCore vp128s)) seed (encode vp128s q) = some q ∨
      (∃ r msg, q = .inl (.hmsg r seed root msg)) ∨ ∃ o msg, q = .inr ⟨skPrf, o, msg⟩ := by
  by_cases h₁ : q = prfPoint
  · exact Or.inr (Or.inr ⟨_, _, h₁⟩)
  by_cases h₂ : q = hmsgPoint
  · exact Or.inr (Or.inl ⟨_, _, h₂⟩)
  rw [cache_apply_of_ne h₁ h₂] at hq
  cases hq

/-- The two points are a clash. -/
theorem clash_cache :
    (shakeEncoding vp128s (FipsParameterSet.n_le_32 _) (FipsParameterSet.n_le_m _) seed).Clash
      cache :=
  ⟨prfPoint, hmsgPoint, by decide, isSome_cache_prfPoint, isSome_cache_hmsgPoint, by decide⟩

/-- The message-`PRF` key is not the public seed. -/
theorem skPrf_ne_seed : (skPrf : Bytes 16) ≠ (seed : Bytes 16) := fun h =>
  absurd (congrArg Vector.toList h) (by decide)

/-- BK does not hold of this cache. -/
theorem not_hmsgAtWeakKey : ¬HmsgAtWeakKey seed root cache := by
  rintro ⟨msg, h, -⟩
  rw [cache_apply_of_ne (by simp [prfPoint]) fun h => by
    simp only [hmsgPoint, Sum.inl.injEq] at h
    exact skPrf_ne_seed (PublicHashQuery.hmsg.inj h).1.symm] at h
  cases h

/-- So the classification concludes Fev: an `H_msg` point at `SK.prf` is cached. -/
example : HmsgAtPrfKey id skPrf cache :=
  (((hmsgAtPrfKey_and_prfMsgAt_or_eq_or_hmsgAtWeakKey_of_clash (FipsParameterSet.n_le_32 _)
    (FipsParameterSet.n_le_m _) cache_provenance clash_cache).resolve_right
      not_hmsgAtWeakKey).resolve_right skPrf_ne_seed).1

/-! ## A concrete weak-key clash at SLH-DSA-SHAKE-128s -/

/-- The node at height `1`, index `0` of the top XMSS tree, a ledger address. -/
abbrev weakAdrs : Adrs :=
  xmssNodeAdrs (GeneralHypertree.layerAdrs (vp128s.params.d - 1) 0) 1 0

theorem weakAdrs_mem : weakAdrs ∈ constructionAddresses vp128s := by
  rw [weakAdrs, ← LayerTreeCoord.top_toAdrs_layerAdrs]
  exact xmssNodeAdrs_mem_constructionAddresses _ one_pos (by decide) (by decide)

/-- The key of `weakAdrs`, honest as the key of a node of the SLH-DSA graph. -/
abbrev weakKey : NodeKey (shakeCore vp128s) :=
  ⟨(shakeCore vp128s).adrsToKey weakAdrs, weakAdrs, weakAdrs_mem, rfl⟩

/-- The first 16 bytes of the key of `weakAdrs`, as a public seed. -/
def weakSeed : (shakeCore vp128s).PkSeed :=
  (⟨#[0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], rfl⟩ : Bytes 16)

/-- The last 16 bytes of the key of `weakAdrs`, as a root. -/
def weakRoot : (shakeCore vp128s).Y :=
  (⟨#[0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], rfl⟩ : Bytes 16)

/-- The tweakable-hash query at the public seed, the key of `weakAdrs`, and no input. -/
abbrev thashPoint : (hashSpec (shakeCore vp128s)).Domain := .inl (.thash weakSeed weakKey.1 [])

/-- The `H_msg` query at randomizer `PK.seed`, the public key `(weakSeed, weakRoot)`, and no
message. -/
abbrev weakHmsgPoint : (hashSpec (shakeCore vp128s)).Domain :=
  .inl (.hmsg weakSeed weakSeed weakRoot [])

/-- The two strings coincide: `PK.seed ‖ PK.root` is the key of `weakAdrs`. -/
theorem encode_thashPoint : encode vp128s thashPoint = encode vp128s weakHmsgPoint := by decide

/-- The cache holding both points. -/
noncomputable def weakCache : (hashSpec (shakeCore vp128s)).QueryCache :=
  ((∅ : (hashSpec (shakeCore vp128s)).QueryCache).cacheQuery thashPoint weakRoot).cacheQuery
    weakHmsgPoint (Vector.replicate _ 0)

theorem weakCache_apply_of_ne {q : (hashSpec (shakeCore vp128s)).Domain} (h₁ : q ≠ thashPoint)
    (h₂ : q ≠ weakHmsgPoint) : weakCache q = none := by
  rw [weakCache, QueryCache.cacheQuery_of_ne _ _ h₂, QueryCache.cacheQuery_of_ne _ _ h₁,
    QueryCache.empty_apply]

/-- The cache has the provenance of a run at `(weakSeed, weakRoot)` with key `skPrf`: the
tweakable-hash point is route-fixed. -/
theorem weakCache_provenance (q : (hashSpec (shakeCore vp128s)).Domain)
    (hq : (weakCache q).isSome) :
    shakeRoute vp128s (IsHonestKey vp128s (shakeCore vp128s)) weakSeed (encode vp128s q) =
        some q ∨
      (∃ r msg, q = .inl (.hmsg r weakSeed weakRoot msg)) ∨ ∃ o msg, q = .inr ⟨skPrf, o, msg⟩ := by
  by_cases h₁ : q = thashPoint
  · exact Or.inl (h₁ ▸ shakeEncoding_route_encode_thash (FipsParameterSet.n_le_32 _)
      (FipsParameterSet.n_le_m _) weakSeed (isHonestKey_nodeKey weakKey) [])
  by_cases h₂ : q = weakHmsgPoint
  · exact Or.inr (Or.inl ⟨_, _, h₂⟩)
  rw [weakCache_apply_of_ne h₁ h₂] at hq
  cases hq

/-- The two points are a clash. -/
theorem clash_weakCache :
    (shakeEncoding vp128s (FipsParameterSet.n_le_32 _) (FipsParameterSet.n_le_m _)
      weakSeed).Clash weakCache := by
  refine ⟨thashPoint, weakHmsgPoint, by simp, ?_, ?_, encode_thashPoint⟩
  · rw [weakCache, QueryCache.cacheQuery_of_ne _ _ (by simp), QueryCache.cacheQuery_self]
    rfl
  · rw [weakCache, QueryCache.cacheQuery_self]
    rfl

/-- The message-`PRF` key is not the weak public seed. -/
theorem skPrf_ne_weakSeed : (skPrf : Bytes 16) ≠ (weakSeed : Bytes 16) := fun h =>
  absurd (congrArg Vector.toList h) (by decide)

/-- Neither Fev nor K1 holds of this cache. -/
theorem not_hmsgAtPrfKey_or_eq :
    ¬(HmsgAtPrfKey id skPrf weakCache ∨ skPrf = weakSeed) := by
  rintro (⟨ps, pr, msg, h⟩ | h)
  · rw [weakCache_apply_of_ne (by simp) fun h => by
      simp only [weakHmsgPoint, Sum.inl.injEq] at h
      exact skPrf_ne_weakSeed (PublicHashQuery.hmsg.inj h).1] at h
    cases h
  · exact skPrf_ne_weakSeed h

/-- So the classification concludes the weak-key `H_msg` event. -/
theorem hmsgAtWeakKey_weakCache : HmsgAtWeakKey weakSeed weakRoot weakCache :=
  (hmsgAtPrfKey_and_prfMsgAt_or_eq_or_hmsgAtWeakKey_of_clash (FipsParameterSet.n_le_32 _)
    (FipsParameterSet.n_le_m _) weakCache_provenance clash_weakCache).resolve_left
      fun h => not_hmsgAtPrfKey_or_eq (h.imp_left And.left)

/-- And the public key `(weakSeed, weakRoot)` is weak: BK. -/
example : IsWeakKey vp128s ⟨weakSeed, weakRoot⟩ :=
  isWeakKey_of_hmsgAtWeakKey (FipsParameterSet.sixteen_le_n _) hmsgAtWeakKey_weakCache

end SLHDSA.ByteClashTest
