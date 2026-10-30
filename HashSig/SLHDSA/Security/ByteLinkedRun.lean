/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteClash
public import HashSig.SLHDSA.Security.ByteRedirect
public import HashSig.SLHDSA.Security.RomSchemeRun

/-!
# The single-SHAKE256 run as a prefix of the run of the verifying adversary

At `n = 32` a tweakable-hash query at a *linked* point (`IsLinked`) and its `H_msg` reading share
one SHAKE256 string. At a fixed public seed and for every `opt_rand` distribution, the strong
advantage against SLH-DSA over one SHAKE256 oracle is at most the probability of an event of the
three-oracle run of `romScheme` against the verifying adversary `verifyingAdv`
(`shakeStrongAdvantage_pure_le_verifyingAdv`):

* `RedirectedWins`: the forged pair of message and signature is fresh and the redirected
  verification `redirectedVerify` accepts on the public-hash part of the final cache;
* `RunPrfKeyClash id pkSeed pkSeed`: the message-`PRF` key is hit at `opt_rand = PK.seed`;
* `¬HonestOffLinked`: key generation or a logged signature, replayed at the oracle-backed provider
  on the public-hash cache with its linked points removed, fails to return its value.

## The argument

The linked scheme `linkedRomScheme`, `romScheme` verifying by `redirectedVerify`, encodes to
`shakeRomScheme` (`shakeRomScheme_eq_map_linkedRomScheme`), so the single-oracle coupling bounds the
advantage by its run against `linkedRouteAdv` winning or ending with a clash
(`shakeStrongAdvantage_pure_le_linkedRomScheme`). That run is the run against `verifyingAdv` up to
its final, non-redirected verification (`SignatureAlg.unforgeableTranscriptExperiment_withPost`),
which only adds cache entries. A clash is not carried to the larger cache by that verification
alone, since it caches linked points whose `H_msg` readings the redirected one has cached, so the
clash is classified on the linked run, where only the honest algorithms cache linked points
(`honestReplays_of_mem_support_run_linkedRomScheme`,
`hmsgAtPrfKey_and_prfMsgAt_or_eq_or_linkedCached_of_clash`).

## The root event

`¬HonestOffLinked` never holds on the support of a run at a public seed whose bytes are not an
honest address key (`honestOffLinked_of_mem_support_romSchemeRun`). `HonestOffLinked` makes the
honest replays settle below both the cache and its view through `linkedRedirect`
(`OracleSpec.QueryCache.filter_le_viewBy`).
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.Security

open Concrete

variable {vp : ValidatedParams}

/-! ## The linked scheme and the coupling -/

section Coupling

variable {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
  {pkSeedDist : ProbComp (shakeCore vp).PkSeed}

variable (vp optRand pkSeedDist) in
/-- **The linked scheme**: the three-oracle scheme `romScheme`, verifying by the redirected
verification `redirectedVerify`. -/
noncomputable def linkedRomScheme :
    SignatureAlg (OracleComp (unifSpec + hashSpec (shakeCore vp))) (List Byte)
      (PublicKeyCore (shakeCore vp)) (SecretKeyCore (shakeCore vp))
      (GeneralScheme.SignatureCore vp (shakeCore vp)) :=
  (romScheme (shakeCore vp) (Equiv.refl _) optRand pkSeedDist).withVerify fun pk msg sig =>
    liftPub (redirectedVerify vp pk msg sig)

/-- **The single-SHAKE256 scheme is the linked scheme, encoded.** -/
theorem shakeRomScheme_eq_map_linkedRomScheme :
    shakeRomScheme vp optRand pkSeedDist =
      (linkedRomScheme vp optRand pkSeedDist).map (simulateQ' (encImpl vp)) := by
  ext
  · rfl
  · rfl
  · exact shakeRomScheme_verify_eq optRand pkSeedDist _ _

/-- **The per-seed coupling on the linked run.** At a fixed public seed, the strong advantage
against `shakeRomScheme` is at most the probability that the run of the linked scheme against the
routed adversary with linked strings wins strongly or ends with a clash. -/
theorem shakeStrongAdvantage_pure_le_linkedRomScheme (hn : vp.params.n ≤ 32)
    (hnm : vp.params.n ≤ vp.params.m) (pkSeed : (shakeCore vp).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) :
    shakeStrongAdvantage vp adv ≤
      Pr{let z ← (simulateQ (hashSpec (shakeCore vp)).romImpl (unforgeableTranscriptExperiment
          (sigAlg := linkedRomScheme vp optRand (pure pkSeed))
          ⟨(linkedRouteAdv vp hn hnm adv.toUnforgeableAdversary).main⟩)).run ∅}[
        z.1.strongWins = true ∨ (shakeEncoding vp hn hnm pkSeed).Clash z.2] := by
  have hE : ∀ z ∈ support (linkedRomScheme vp optRand (pure pkSeed)).keygen,
      shakeEncoding vp hn hnm z.1.pkSeed = shakeEncoding vp hn hnm pkSeed := fun _ hz => by
    rw [linkedRomScheme, withVerify_keygen] at hz
    exact congrArg _ (pkSeed_eq_of_mem_support_romScheme_keygen _ _ hz)
  let A : UnforgeableAdversary ((linkedRomScheme vp optRand (pure pkSeed)).map
      (simulateQ' (liftTypedImpl (ext := shakeSpec vp)))) :=
    ⟨(linkedAdv vp adv.toUnforgeableAdversary).main⟩
  refine le_of_eq_of_le ?_ ((shakeEncoding vp hn hnm pkSeed)
    |>.prEvent_simulateQ_singleImpl_run_unforgeableTranscriptExperiment_le A hE
      (·.strongWins = true))
  have hnat :=
    simulateQ_unforgeableTranscriptExperiment (shakeEncoding vp hn hnm pkSeed).encodeImpl A
  rw [map_simulateQ'_map_simulateQ', encodeImpl_shakeEncoding_compose_liftTypedImpl] at hnat
  have hA : A.mapOracles (shakeEncoding vp hn hnm pkSeed).encodeImpl
      (sigAlg' := (linkedRomScheme vp optRand (pure pkSeed)).map (simulateQ' (encImpl vp))) =
      ⟨adv.main⟩ := by
    refine congrArg UnforgeableAdversary.mk (funext fun pk => ?_)
    change _ = adv.toUnforgeableAdversary.main pk
    rw [UnforgeableAdversary.mapOracles_main,
      ← mapOracles_encodeImpl_linkedAdv hn hnm pkSeed adv.toUnforgeableAdversary,
      UnforgeableAdversary.mapOracles_main]
  rw [shakeStrongAdvantage_eq, ← RandomOracleEncoding.simulateQ_romImpl_simulateQ_encodeImpl, hnat,
    unforgeableTranscriptExperiment_congr shakeRomScheme_eq_map_linkedRomScheme
      adv.toUnforgeableAdversary, hA]
  rfl

end Coupling

/-! ## The events -/

variable (vp) in
/-- **The honest replays** of the key pair `(pk, sk)` and the signing log `log` on a public-hash
cache `d`: key generation at the oracle-backed provider returns `PK.root`, and every logged
signature is returned by signing at its own randomizer. -/
@[expose] def HonestReplays (pk : PublicKeyCore (shakeCore vp)) (sk : SecretKeyCore (shakeCore vp))
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp (shakeCore vp)))
    (d : PublicHash.Cache (shakeCore vp)) : Prop :=
  simulateQ d.toPartialImpl (GeneralScheme.keygenInternalWithSecretM (shakeCore vp)
      (oracleSecret (shakeCore vp) (Equiv.refl _) pk.pkSeed sk.skSeed) pk.pkSeed) =
      some pk.pkRoot ∧
    ∀ x ∈ log, simulateQ d.toPartialImpl (GeneralScheme.signInternalWithSecretRandomizerM
      (shakeCore vp) (oracleSecret (shakeCore vp) (Equiv.refl _) pk.pkSeed sk.skSeed) x.1
      pk.pkSeed pk.pkRoot x.2.randomness) = some x.2

variable (vp) in
/-- **The honest replays avoid the linked points**: the honest replays of a transcript settle on
the public-hash part of the cache with every linked point removed. -/
@[expose] def HonestOffLinked
    (z : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache) : Prop :=
  HonestReplays vp z.1.pk z.1.sk z.1.log (QueryCache.filter (¬IsLinked vp z.1.pk ·) z.2.fst)

variable (vp) in
/-- **The forgery wins on the redirected verification**: its pair of message and signature was
never returned by the signing oracle and the redirected verification accepts it on the public-hash
part of the cache. -/
@[expose] def RedirectedWins
    (z : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache) : Prop :=
  ⟨z.1.msg, z.1.sig⟩ ∉ z.1.log ∧
    simulateQ z.2.fst.toPartialImpl (redirectedVerify vp z.1.pk z.1.msg z.1.sig) = some true

variable (vp) in
/-- The cache holds a linked point of the public key `pk`. -/
@[expose] def LinkedCached (pk : PublicKeyCore (shakeCore vp))
    (c : (hashSpec (shakeCore vp)).QueryCache) : Prop :=
  ∃ t, IsLinked vp pk t ∧ (c (.inl t)).isSome

section Events

variable {pk : PublicKeyCore (shakeCore vp)} {sk : SecretKeyCore (shakeCore vp)}
  {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp (shakeCore vp))}

theorem HonestReplays.mono {d d' : PublicHash.Cache (shakeCore vp)} (h : d ≤ d')
    (hr : HonestReplays vp pk sk log d) : HonestReplays vp pk sk log d' :=
  ⟨QueryCache.simulateQ_toPartialImpl_mono h _ hr.1,
    fun x hx => QueryCache.simulateQ_toPartialImpl_mono h _ (hr.2 x hx)⟩

/-- Honest replays that settle on `d` and fail off the linked points of `d` fail off the linked
points of every larger cache. -/
theorem HonestReplays.not_filter_of_le {d d' : PublicHash.Cache (shakeCore vp)} (h : d ≤ d')
    (hr : HonestReplays vp pk sk log d)
    (hn : ¬HonestReplays vp pk sk log (QueryCache.filter (¬IsLinked vp pk ·) d)) :
    ¬HonestReplays vp pk sk log (QueryCache.filter (¬IsLinked vp pk ·) d') := fun ⟨hk, hl⟩ =>
  hn ⟨QueryCache.simulateQ_toPartialImpl_filter_of_le h hr.1 hk,
    fun x hx => QueryCache.simulateQ_toPartialImpl_filter_of_le h (hr.2 x hx) (hl x hx)⟩

end Events

/-! ## The clash at `n = 32` -/

section Clash

variable {pkSeed : (shakeCore vp).PkSeed} {pkRoot : (shakeCore vp).Y}
  {skPrf : (shakeCore vp).SkPrf} {c : (hashSpec (shakeCore vp)).QueryCache}

/-- **The classification of a clash at `n = 32` with the linked points.** In a cache whose points
are route-fixed, `H_msg` points at `(pkSeed, pkRoot)`, or `PRF_msg` points keyed by `skPrf`, a
clash gives an `H_msg` point at `skPrf` together with a cached `PRF_msg` point keyed by `skPrf`
whose `opt_rand` is `pkSeed`, `skPrf = pkSeed`, or a cached linked point of `(pkSeed, pkRoot)`. -/
theorem hmsgAtPrfKey_and_prfMsgAt_or_eq_or_linkedCached_of_clash (h32 : vp.params.n = 32)
    (hnm : vp.params.n ≤ vp.params.m)
    (hc : ∀ q, (c q).isSome →
      shakeRoute vp (IsHonestKey vp (shakeCore vp)) pkSeed (encode vp q) = some q ∨
        (∃ r msg, q = .inl (.hmsg r pkSeed pkRoot msg)) ∨ ∃ o msg, q = .inr ⟨skPrf, o, msg⟩)
    (h : (shakeEncoding vp h32.le hnm pkSeed).Clash c) :
    ((HmsgAtPrfKey id skPrf c ∧ PrfMsgAt skPrf pkSeed c) ∨ skPrf = pkSeed) ∨
      LinkedCached vp ⟨pkSeed, pkRoot⟩ c := by
  obtain ⟨q, q', hne, hq, hq', he, hfix⟩ := h.exists_route_ne
  replace he : encode vp q = encode vp q' := he
  rcases hc q hq with h | ⟨r, msg, rfl⟩ | ⟨o, msg, rfl⟩
  · exact (hfix h).elim
  · have hT : IsThashString vp (IsHonestKey vp (shakeCore vp)) pkSeed
        (encode vp (.inl (.hmsg r pkSeed pkRoot msg))) := by
      by_contra hT
      exact hfix (shakeRoute_encode_hmsg r pkRoot msg hT)
    rcases q' with (⟨s, k, xs⟩ | ⟨r', s', root', msg'⟩) | ⟨k', o', m'⟩
    · rcases hc _ hq' with h | ⟨_, _, h⟩ | ⟨_, _, h⟩
      · obtain ⟨rfl, -⟩ := eq_and_isHonestKey_of_shakeRoute_encode_thash h
        exact Or.inr ⟨_, isLinked_of_encode_eq_encode_hmsg (pk := ⟨s, pkRoot⟩) h32 he.symm, hq'⟩
      · cases h
      · cases h
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := (encode_hmsg_inj (vp := vp)).1 he
      exact (hne rfl).elim
    · rcases hc _ hq' with h | ⟨_, _, h⟩ | ⟨_, _, h⟩
      · rw [← he, shakeRoute_of_isThashString hT] at h
        cases h
      · cases h
      · cases h
        rw [he] at hT
        exact Or.inl (Or.inr (Vector.toList_inj.1 (toList_eq_of_isThashString_encode_prfMsg _ hT)))
  · exact Or.inl (hmsgAtPrfKey_and_prfMsgAt_or_eq_of_shakeRoute_ne_prfMsg hc hq hq' hne he hfix)

end Clash

/-! ## The queries of the linked run -/

section Queries

/-- **The redirected verification queries no linked point.** At the public key `pk`, every query
of the redirected verification is an honest query of `pk` and any `skPrf`, and is not a linked
point. -/
theorem allQueriesSatisfy_liftPub_redirectedVerify (pk : PublicKeyCore (shakeCore vp))
    (skPrf : (shakeCore vp).SkPrf) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp (shakeCore vp)) :
    AllQueriesSatisfy (liftPub (redirectedVerify vp pk msg sig))
      (Sum.elim (fun _ => True) fun q =>
        IsHonestQuery vp pk skPrf q ∧ ∀ t, q = .inl t → ¬IsLinked vp pk t) := by
  have hV : AllQueriesSatisfy (GeneralScheme.verifyInternalM
      (m := OracleComp (publicHashSpec (shakeCore vp))) vp (shakeCore vp) msg sig pk)
      (fun t => IsHonestQuery vp pk skPrf (.inl t)) :=
    verifyInternalM_pred_of_ledger (AllQueriesSatisfy · _) (fun x => allQueriesSatisfy_pure x _)
      (fun _ _ h₁ h₂ => allQueriesSatisfy_bind h₁ h₂) (shakeCore vp) msg sig pk
      (fun _ ha _ => (allQueriesSatisfy_query_iff _ _).2 ⟨rfl, _, .inl ha, rfl⟩)
      ((allQueriesSatisfy_query_iff _ _).2 ⟨rfl, rfl⟩)
  have hR : AllQueriesSatisfy (redirectedVerify vp pk msg sig)
      (fun t => IsHonestQuery vp pk skPrf (.inl t) ∧ ¬IsLinked vp pk t) := by
    refine hV.simulateQ fun t ht => ?_
    by_cases hl : IsLinked vp pk t
    · rcases t with ⟨s, k, _ | ⟨r, rest⟩⟩ | _
      · exact hl.elim
      · rw [linkedRedirect_of_isLinked hl]
        exact (allQueriesSatisfy_def _ _).2 ((isQueryBound_map_iff _ _ _ _ _).2
          ((allQueriesSatisfy_def _ _).1 ((allQueriesSatisfy_query_iff (linkedHmsg vp s r rest)
            fun t => IsHonestQuery vp pk skPrf (.inl t) ∧ ¬IsLinked vp pk t).2
              ⟨⟨hl.1, hl.2.2⟩, id⟩)))
      · exact hl.elim
    · rw [linkedRedirect_of_not_isLinked hl]
      exact (allQueriesSatisfy_query_iff _ _).2 ⟨ht, hl⟩
  exact hR.simulateQ fun t ht =>
    (allQueriesSatisfy_query_iff (spec := unifSpec + hashSpec (shakeCore vp)) (.inr (.inl t)) _).2
      ⟨ht.1, fun _ h => Sum.inl.inj h ▸ ht.2⟩

variable {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
  {pkSeedDist : ProbComp (shakeCore vp).PkSeed}

/-- **The forger's queries in the linked run.** At the public key `pk`, every typed query of the
routed adversary with linked strings is route-fixed and not a linked point, or is the `H_msg`
query `H_msg(PK.seed, PK.seed, PK.root, M)` of a linked string. -/
theorem allQueriesSatisfy_linkedRouteAdv_main (hn : vp.params.n ≤ 32)
    (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand pkSeedDist))
    (pk : PublicKeyCore (shakeCore vp)) :
    AllQueriesSatisfy ((linkedRouteAdv vp hn hnm adv).main pk)
      (Sum.elim (Sum.elim (fun _ => True) fun q =>
        ((shakeEncoding vp hn hnm pk.pkSeed).route (encode vp q) = some q ∧
          ∀ t, q = .inl t → ¬IsLinked vp pk t) ∨
        ∃ M, q = .inl (.hmsg pk.pkSeed pk.pkSeed pk.pkRoot M)) fun _ => True) := by
  unfold linkedRouteAdv
  refine UnforgeableAdversary.allQueriesSatisfy_route_of_raw
    (sigAlg := romScheme (shakeCore vp) (Equiv.refl _) optRand pkSeedDist) (adv := linkedAdv vp adv)
    (R := fun pk => (shakeEncoding vp hn hnm pk.pkSeed).tableRouter)
    (P := fun pk q => ((shakeEncoding vp hn hnm pk.pkSeed).route (encode vp q) = some q ∧
      ∀ t, q = .inl t → ¬IsLinked vp pk t) ∨ ∃ M, q = .inl (.hmsg pk.pkSeed pk.pkSeed pk.pkRoot M))
    (Raw := fun pk x => ¬IsLinkedString vp pk x) ?_ ?_ ∅ pk
  · intro pk x hx s
    refine ((shakeEncoding vp hn hnm pk.pkSeed).allQueriesSatisfy_run_tableRouter_route x s).mono ?_
    rintro (n | q) hq
    · trivial
    · have he := (shakeEncoding vp hn hnm pk.pkSeed).encode_eq_of_route_eq_some hq
      refine Or.inl ⟨?_, fun t ht hl => hx ⟨t, hl, by rw [← he, ht]; rfl⟩⟩
      rw [show encode vp q = x from he]
      exact hq
  · intro pk
    refine (allQueriesSatisfy_mapOracles (G := linkedRawImpl vp pk)
      (sigAlg' := (romScheme (shakeCore vp) (Equiv.refl _) optRand pkSeedDist).map
        (simulateQ' (liftTypedImpl (ext := shakeSpec vp))))
      (allowed := Sum.elim (fun _ => True) (Sum.elim
        (fun q => ∃ M, q = .inl (.hmsg pk.pkSeed pk.pkSeed pk.pkRoot M))
          fun x => ¬IsLinkedString vp pk x)) adv ?_ pk).mono ?_
    · rintro (n | x)
      · exact (allQueriesSatisfy_query_iff _ _).2 trivial
      · by_cases h : IsLinkedString vp pk x
        · simp only [linkedRawImpl, h, ↓reduceIte]
          exact (allQueriesSatisfy_query_iff _ _).2 ⟨_, rfl⟩
        · simp only [linkedRawImpl, h, ↓reduceIte]
          exact (allQueriesSatisfy_query_iff _ _).2 h
    · rintro ((n | q | x) | m) h
      exacts [trivial, Or.inr h, h, trivial]

end Queries

/-! ## The linked invariant -/

section Invariant

variable {pk : PublicKeyCore (shakeCore vp)} {sk : SecretKeyCore (shakeCore vp)}
  {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp (shakeCore vp))}
  {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
  {pkSeedDist : ProbComp (shakeCore vp).PkSeed}

/-- The honest replays settle on the cache, and fail off its linked points once it caches one. -/
private def LinkedInv (pk : PublicKeyCore (shakeCore vp)) (sk : SecretKeyCore (shakeCore vp))
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp (shakeCore vp)))
    (c : (hashSpec (shakeCore vp)).QueryCache) : Prop :=
  HonestReplays vp pk sk log c.fst ∧ (LinkedCached vp pk c →
    ¬HonestReplays vp pk sk log (QueryCache.filter (¬IsLinked vp pk ·) c.fst))

/-- A run of a program that queries no linked point keeps the linked invariant. -/
private theorem linkedInv_of_mem_support_run {α : Type}
    {oa : OracleComp (unifSpec + hashSpec (shakeCore vp)) α}
    (hoa : AllQueriesSatisfy oa (Sum.elim (fun _ => True) fun q =>
      ∀ t, q = .inl t → ¬IsLinked vp pk t))
    {c : (hashSpec (shakeCore vp)).QueryCache} (h : LinkedInv pk sk log c)
    {z : α × (hashSpec (shakeCore vp)).QueryCache}
    (hz : z ∈ support ((simulateQ (hashSpec (shakeCore vp)).romImpl oa).run c)) :
    LinkedInv pk sk log z.2 := by
  have hle := QueryCache.fst_mono
    (le_snd_of_mem_support_run_unifFwdImpl_add_withCaching uniformSampleImpl _ hz)
  refine ⟨h.1.mono hle, fun ⟨t, ht, hct⟩ => h.1.not_filter_of_le hle (h.2 ⟨t, ht, ?_⟩)⟩
  rcases forall_isSome_of_mem_support_run_simulateQ_romImpl
    (P := fun q => (c q).isSome ∨ ∀ t', q = .inl t' → ¬IsLinked vp pk t')
    (hoa.mono fun q hq => by rcases q with n | q; exacts [trivial, Or.inr hq])
    (fun q hq => Or.inl hq) hz (.inl t) hct with h' | h'
  · exact h'
  · exact (h' t rfl ht).elim

/-- Key generation establishes the linked invariant. -/
private theorem linkedInv_keygen
    {z : (PublicKeyCore (shakeCore vp) × SecretKeyCore (shakeCore vp)) ×
      (hashSpec (shakeCore vp)).QueryCache}
    (hz : z ∈ support ((simulateQ (hashSpec (shakeCore vp)).romImpl
      (romScheme (shakeCore vp) (Equiv.refl _) optRand pkSeedDist).keygen).run ∅)) :
    LinkedInv z.1.1 z.1.2 [] z.2 := by
  obtain ⟨pkSeed, -, hz⟩ := roSim.exists_mem_support_run_of_mem_support_run_liftM_bind _ _ _ hz
  unfold romKeygenAt at hz
  obtain ⟨skSeed, -, hz⟩ := roSim.exists_mem_support_run_of_mem_support_run_liftM_bind _ _ _ hz
  obtain ⟨skPrf, -, hz⟩ := roSim.exists_mem_support_run_of_mem_support_run_liftM_bind _ _ _ hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨pkRoot, c⟩, hroot, hz⟩ := hz
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rw [keygenInternalWithSecretM_oracleSecret_eq_ofSimulateQ (core := shakeCore vp)
    (m := OracleComp (unifSpec + hashSpec (shakeCore vp))) (Equiv.refl _) pkSeed skSeed] at hroot
  refine ⟨⟨simulateQ_toPartialImpl_snd_fst_of_mem_support_run_romImpl _ hroot,
    fun x hx => by simp at hx⟩, fun ⟨t, ht, hct⟩ hk => ?_⟩
  exact forall_of_simulateQ_toPartialImpl_filter_fst_of_mem_support_run_romImpl _ hroot hk.1 t
    rfl hct ht

/-- A signing query keeps the linked invariant, its entry appended to the log. -/
private theorem linkedInv_sign (hs : sk.pkSeed = pk.pkSeed) (hr : sk.pkRoot = pk.pkRoot)
    {msg : List Byte} {c : (hashSpec (shakeCore vp)).QueryCache} (h : LinkedInv pk sk log c)
    {z : GeneralScheme.SignatureCore vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache}
    (hz : z ∈ support ((simulateQ (hashSpec (shakeCore vp)).romImpl
      ((romScheme (shakeCore vp) (Equiv.refl _) optRand pkSeedDist).sign pk sk msg)).run c)) :
    LinkedInv pk sk (log ++ [⟨msg, z.1⟩]) z.2 := by
  obtain ⟨addrnd, -, hz⟩ := roSim.exists_mem_support_run_of_mem_support_run_liftM_bind _ _ _ hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨R, c₁⟩, hR, hz⟩ := hz
  have h₁ : LinkedInv pk sk log c₁ := linkedInv_of_mem_support_run
    ((allQueriesSatisfy_query_iff (spec := unifSpec + hashSpec (shakeCore vp))
      (.inr (.inr ⟨sk.skPrf, addrnd, msg⟩)) _).2 fun _ h => by cases h) h hR
  rw [hs, hr, signInternalWithSecretRandomizerM_oracleSecret_eq_ofSimulateQ (core := shakeCore vp)
    (m := OracleComp (unifSpec + hashSpec (shakeCore vp))) (Equiv.refl _) pk.pkSeed sk.skSeed msg
    pk.pkRoot R] at hz
  have hread := simulateQ_toPartialImpl_snd_fst_of_mem_support_run_romImpl _ hz
  obtain ⟨hRr, -⟩ :=
    components_of_simulateQ_toPartialImpl_signInternalWithSecretRandomizerM _ _ _ _ _ _ _ hread
  rw [← hRr] at hread
  have hle := QueryCache.fst_mono
    (le_snd_of_mem_support_run_unifFwdImpl_add_withCaching uniformSampleImpl _ hz)
  refine ⟨⟨(h₁.1.mono hle).1, fun x hx => ?_⟩, fun ⟨t, ht, hzt⟩ hoff => ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact (h₁.1.mono hle).2 x hx
    · rw [List.mem_singleton.1 hx]
      exact hread
  · by_cases hlc : LinkedCached vp pk c₁
    · exact h₁.1.not_filter_of_le hle (h₁.2 hlc)
        ⟨hoff.1, fun x hx => hoff.2 x (List.mem_append_left _ hx)⟩
    · have hnew := hoff.2 ⟨msg, z.1⟩ (by simp)
      simp only at hnew
      rw [hRr] at hnew
      exact forall_of_simulateQ_toPartialImpl_filter_fst_of_mem_support_run_romImpl _ hz hnew t
        (Option.not_isSome_iff_eq_none.1 fun h => hlc ⟨t, ht, h⟩) hzt ht

/-- **The linked run.** Let `F pk` be a predicate holding of no linked point of `pk`, and let the
adversary's hash queries at every public key `pk` satisfy `F pk`. On every transcript of the run of
the linked scheme: the public seed is drawn from the seed distribution; every cached point is an
honest query of the key pair or satisfies `F` at the public key; the honest replays settle on the
public-hash cache, and once a linked point is cached they fail off the linked points; and the
verdict is the replay of the redirected verification on the public-hash cache. -/
theorem honestReplays_of_mem_support_run_linkedRomScheme
    (F : PublicKeyCore (shakeCore vp) → (hashSpec (shakeCore vp)).Domain → Prop)
    (hF : ∀ pk q, F pk q → ∀ t, q = .inl t → ¬IsLinked vp pk t)
    {adv : UnforgeableAdversary (linkedRomScheme vp optRand pkSeedDist)}
    (hadv : ∀ pk, AllQueriesSatisfy (adv.main pk)
      (Sum.elim (Sum.elim (fun _ => True) (F pk)) fun _ => True))
    {z : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache}
    (hz : z ∈ support ((simulateQ (hashSpec (shakeCore vp)).romImpl
      (unforgeableTranscriptExperiment adv)).run ∅)) :
    z.1.pk.pkSeed ∈ support pkSeedDist ∧
      (∀ q, (z.2 q).isSome → IsHonestQuery vp z.1.pk z.1.sk.skPrf q ∨ F z.1.pk q) ∧
      HonestReplays vp z.1.pk z.1.sk z.1.log z.2.fst ∧
      (LinkedCached vp z.1.pk z.2 → ¬HonestOffLinked vp z) ∧
      simulateQ z.2.fst.toPartialImpl (redirectedVerify vp z.1.pk z.1.msg z.1.sig) =
        some z.1.verified := by
  obtain ⟨s₁, s₂, hk, hf, hv⟩ :=
    exists_mem_support_run_of_mem_support_run_unforgeableTranscriptExperiment _ adv hz
  rw [linkedRomScheme, withVerify_keygen] at hk
  rw [linkedRomScheme, withVerify_verify] at hv
  obtain ⟨hseed, hs, hr, hprov⟩ := isHonestQuery_of_mem_support_run_romScheme_keygen
    (core := shakeCore vp) _ _ _ hk
  let I : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp (shakeCore vp)) →
      (hashSpec (shakeCore vp)).QueryCache → Prop := fun log c =>
    (∀ q, (c q).isSome → IsHonestQuery vp z.1.pk z.1.sk.skPrf q ∨ F z.1.pk q) ∧
      LinkedInv z.1.pk z.1.sk log c
  -- a program whose queries are honest or in `F`, and never linked, keeps `I`
  have hstep : ∀ {α : Type} {oa : OracleComp (unifSpec + hashSpec (shakeCore vp)) α},
      AllQueriesSatisfy oa (Sum.elim (fun _ => True) fun q =>
        (IsHonestQuery vp z.1.pk z.1.sk.skPrf q ∨ F z.1.pk q) ∧
          ∀ t, q = .inl t → ¬IsLinked vp z.1.pk t) →
      ∀ log c, I log c → ∀ w ∈ support ((simulateQ (hashSpec (shakeCore vp)).romImpl oa).run c),
        I log w.2 := fun hoa _ _ hI _ hw =>
    ⟨forall_isSome_of_mem_support_run_simulateQ_romImpl (hoa.mono fun q hq => by
        rcases q with n | q; exacts [trivial, hq.1]) hI.1 hw,
      linkedInv_of_mem_support_run (hoa.mono fun q hq => by
        rcases q with n | q; exacts [trivial, hq.2]) hI.2 hw⟩
  have hI := holds_of_mem_support_run_runWithSigningOracle (hashSpec (shakeCore vp)).romImpl
    (linkedRomScheme vp optRand pkSeedDist) z.1.pk z.1.sk I
    (fun t ht _ _ hI _ hw => hstep
      (oa := (liftM ((unifSpec + hashSpec (shakeCore vp)).query t) : OracleComp _ _))
      ((allQueriesSatisfy_query_iff _ _).2 (by
        rcases t with n | q; exacts [trivial, ⟨Or.inr ht, hF _ _ ht⟩])) _ _ hI _
      (by rwa [simulateQ_spec_query]))
    (fun msg _ _ hI _ hw => ⟨forall_isSome_of_mem_support_run_simulateQ_romImpl
      ((allQueriesSatisfy_romScheme_sign (core := shakeCore vp) (Equiv.refl _) optRand pkSeedDist
        hs hr msg).mono
        fun q hq => by rcases q with n | q; exacts [trivial, Or.inl hq]) hI.1 hw,
      linkedInv_sign (optRand := optRand) (pkSeedDist := pkSeedDist) hs hr hI.2 hw⟩)
    (hadv z.1.pk) ⟨fun q hq => Or.inl (hprov q hq), linkedInv_keygen hk⟩ hf
  obtain ⟨hprov', hlink⟩ := hstep ((allQueriesSatisfy_liftPub_redirectedVerify _ z.1.sk.skPrf
    _ _).mono fun q h => by rcases q with n | q; exacts [trivial, ⟨Or.inl h.1, h.2⟩]) _ _ hI _ hv
  exact ⟨hseed, hprov', hlink.1, hlink.2,
    simulateQ_toPartialImpl_snd_fst_of_mem_support_run_romImpl _ hv⟩

end Invariant

/-! ## The headline -/

section Headline

variable {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}

/-- **SLH-DSA over one SHAKE256 oracle at `n = 32`, per public seed, against the verifying
adversary.** At `n = 32` and `n ≤ m`, for every public seed `pkSeed` and every `opt_rand`
distribution, the strong advantage of an adversary against `shakeRomScheme` at `pkSeed` is at most
the probability that, in the three-oracle run of `romScheme` against the verifying adversary
`verifyingAdv`, the forgery wins on the redirected verification (`RedirectedWins`), the
message-`PRF` key is hit at `opt_rand = PK.seed` (`RunPrfKeyClash id pkSeed pkSeed`), or an
honest replay fails off the linked points (`¬HonestOffLinked`). -/
theorem shakeStrongAdvantage_pure_le_verifyingAdv (h32 : vp.params.n = 32)
    (hnm : vp.params.n ≤ vp.params.m) (pkSeed : (shakeCore vp).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) :
    shakeStrongAdvantage vp adv ≤
      Pr{let z ← romSchemeRun (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)
          (verifyingAdv vp h32.le hnm adv.toUnforgeableAdversary)}[
        (RedirectedWins vp z ∨ RunPrfKeyClash id pkSeed pkSeed z) ∨ ¬HonestOffLinked vp z] := by
  refine (shakeStrongAdvantage_pure_le_linkedRomScheme h32.le hnm pkSeed adv).trans ?_
  refine prEvent_run_withVerify_le_prEvent_run_withPost (hashSpec (shakeCore vp)).romImpl
    (romScheme (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed))
    (linkedRouteAdv vp h32.le hnm adv.toUnforgeableAdversary)
    (fun pk out => liftPub (redirectedVerify vp pk out.1 out.2)) ∅ _ _ fun z hz hP r hr => ?_
  obtain ⟨hseed, hprov, hset, hlink, hver⟩ := honestReplays_of_mem_support_run_linkedRomScheme
    _ (fun _ q h t ht => by rcases h with ⟨-, h⟩ | ⟨M, rfl⟩; exacts [h t ht, by cases ht; exact id])
    (allQueriesSatisfy_linkedRouteAdv_main h32.le hnm _) hz
  replace hseed : z.1.pk.pkSeed = pkSeed := by simpa using hseed
  have hshape : ∀ q, (z.2 q).isSome →
      shakeRoute vp (IsHonestKey vp (shakeCore vp)) z.1.pk.pkSeed (encode vp q) = some q ∨
        (∃ r msg, q = .inl (.hmsg r z.1.pk.pkSeed z.1.pk.pkRoot msg)) ∨
          ∃ o msg, q = .inr ⟨z.1.sk.skPrf, o, msg⟩ := fun q hq => by
    rcases hprov q hq with h | h | ⟨M, rfl⟩
    · exact shakeRoute_encode_eq_some_or_of_isHonestQuery h32.le hnm h
    · exact Or.inl h.1
    · exact Or.inr (Or.inl ⟨_, M, rfl⟩)
  have hle : z.2 ≤ r.2 :=
    le_snd_of_mem_support_run_unifFwdImpl_add_withCaching uniformSampleImpl _ hr
  rcases hP with hw | hcl
  · obtain ⟨hfresh, hv⟩ := (UnforgeableTranscript.strongWins_eq_true_iff _).1 hw
    rw [hv] at hver
    exact Or.inl (Or.inl ⟨hfresh, QueryCache.simulateQ_toPartialImpl_mono
      (QueryCache.fst_mono hle) _ hver⟩)
  rw [← hseed] at hcl
  rcases hmsgAtPrfKey_and_prfMsgAt_or_eq_or_linkedCached_of_clash h32 hnm hshape hcl with
    (⟨⟨a, b, m, hm⟩, ⟨m', hm'⟩⟩ | hk) | hl
  · exact Or.inl (Or.inr (Or.inl ⟨⟨a, b, m, QueryCache.isSome_mono hle hm⟩, m',
      hseed ▸ QueryCache.isSome_mono hle hm'⟩))
  · exact Or.inl (Or.inr (Or.inr (hk.trans hseed)))
  · exact Or.inr (hset.not_filter_of_le (QueryCache.fst_mono hle) (hlink hl))

end Headline

/-! ## Off weak seeds -/

/-- **The root event needs a weak seed.** On the support of the run of `romScheme` against any
adversary, if the address key held by the bytes of the public seed is not an honest key, the
honest replays avoid the linked points: they query honest keys only, and a linked point at an
honest key has that key. -/
theorem honestOffLinked_of_mem_support_romSchemeRun
    {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
    {pkSeedDist : ProbComp (shakeCore vp).PkSeed}
    {adv : UnforgeableAdversary (romScheme (shakeCore vp) (Equiv.refl _) optRand pkSeedDist)}
    {z : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache}
    (hz : z ∈ support (romSchemeRun (shakeCore vp) (Equiv.refl _) optRand pkSeedDist adv))
    (hs : ¬IsHonestKey vp (shakeCore vp)
      (adrsKeyOfList vp (Vector.toList (z.1.pk.pkSeed : Bytes vp.params.n)))) :
    HonestOffLinked vp z := by
  obtain ⟨-, -, hk, hl, -⟩ := settled_of_mem_support_romSchemeRun _ _ _ _ _ hz
  have hT : ∀ s k xs, IsHonestKey vp (shakeCore vp) k →
      ¬IsLinked vp z.1.pk (.thash s k xs) := by
    rintro s k (_ | ⟨r, rest⟩) hk hl
    · exact hl
    · obtain ⟨rfl, hks, -⟩ := hl
      refine hs ?_
      rw [← hks]
      convert hk using 1
      exact bytesOfList_toList (k : Bytes 32)
  have hsecret : ∀ a b, b ∈ constructionAddresses vp → .inl a ∈ childAdrs vp b →
      AllQueriesSatisfy (oracleSecret (shakeCore vp) (Equiv.refl _) z.1.pk.pkSeed z.1.sk.skSeed a :
        OracleComp (publicHashSpec (shakeCore vp)) _) (¬IsLinked vp z.1.pk ·) :=
    fun _ _ hb hab => (allQueriesSatisfy_query_iff _ _).2
      (hT _ _ _ (isHonestKey_of_inl_mem_childAdrs hb hab))
  have htl : ∀ a ∈ constructionAddresses vp, ∀ xs, AllQueriesSatisfy
      (PublicHash.tl (shakeCore vp) z.1.pk.pkSeed a xs :
        OracleComp (publicHashSpec (shakeCore vp)) _) (¬IsLinked vp z.1.pk ·) :=
    fun _ ha _ => (allQueriesSatisfy_query_iff _ _).2 (hT _ _ _ ⟨_, .inl ha, rfl⟩)
  refine ⟨?_, fun x hx => ?_⟩
  · rw [QueryCache.simulateQ_toPartialImpl_filter_eq_of_allQueriesSatisfy _
      (keygenInternalWithSecretM_pred_of_ledger (AllQueriesSatisfy · _)
        (fun x => allQueriesSatisfy_pure x _) (fun _ _ h₁ h₂ => allQueriesSatisfy_bind h₁ h₂)
        (shakeCore vp) hsecret _ htl)]
    exact hk
  · rw [QueryCache.simulateQ_toPartialImpl_filter_eq_of_allQueriesSatisfy _
      (signInternalWithSecretRandomizerM_pred_of_ledger (AllQueriesSatisfy · _)
        (fun x => allQueriesSatisfy_pure x _) (fun _ _ h₁ h₂ => allQueriesSatisfy_bind h₁ h₂)
        (shakeCore vp) hsecret _ _ _ _ htl ((allQueriesSatisfy_query_iff _ _).2 id))]
    exact hl x hx

end SLHDSA.Security
