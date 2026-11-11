/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.HedgedKeyBound
public import HashSig.SLHDSA.Security.RunProvenance

/-!
# Classifying the SHAKE256 clashes of the routed run

`HashSig.SLHDSA.Security.ByteRouter` bounds the strong advantage of an adversary against SLH-DSA
over one SHAKE256 random oracle, at a fixed public seed `pkSeed`, by the probability that the run of
the three-oracle scheme against the routed adversary wins strongly or ends with a *clash*: two
distinct cached typed queries with the same FIPS 205 §11.1 byte string
(`shakeStrongAdvantage_pure_le`). This module shows that on the support of that run a clash is one
of three events:

* **Fev with O**: the cache holds an `H_msg` point whose randomizer is `SK.prf` (Fev) and a
  `PRF_msg` point keyed by `SK.prf` whose `opt_rand` is `PK.seed` (O, `PrfMsgAt`);
* **K1**: the message-`PRF` key is the public seed, `SK.prf = PK.seed`;
* **BK** (`IsWeakKey`): the public key is weak, the 32 bytes `(PK.seed ‖ PK.root)[0:32]` being an
  honest address key. On the cache it is the weak-key `H_msg` event (`HmsgAtWeakKey`): an `H_msg`
  point at the public key with randomizer `PK.seed` whose string `PK.seed ‖ PK.seed ‖ PK.root ‖ M`
  is a tweakable-hash string at an honest address key (`IsThashString`), which for `n ≥ 16` makes
  the public key weak (`isWeakKey_of_hmsgAtWeakKey`).

Fev with O, or K1, is the hit of the message-`PRF` key at `opt_rand = PK.seed`,
`RunPrfKeyClash id pkSeed pkSeed` of `HashSig.SLHDSA.Security.HedgedKeyBound`, at the identity
reading of `SK.prf` as a node; dropping O gives the hit `RunPrfKeyHit id pkSeed` of
`HashSig.SLHDSA.Security.PrfKeyBound`.

## The argument

Every cached point of the run is an honest query of the run's key pair or a forger query
(`HashSig.SLHDSA.Security.RunProvenance`), and every forger query is *route-fixed*: the router
reads its string back as the query itself
(`RandomOracleEncoding.allQueriesSatisfy_route_tableRouter`).
An honest tweakable-hash query is at `PK.seed` and an honest key, so it is route-fixed too
(`shakeEncoding_route_encode_thash`). Two route-fixed points with one string are equal, so a
clash has a point `q` that is not route-fixed, an honest `H_msg` or `PRF_msg` query:

* `q = H_msg(R, PK.seed, PK.root, M)`: it is not route-fixed only when its string is a
  tweakable-hash string at `PK.seed` and an honest key (`shakeRoute_encode_hmsg`), which forces
  `R = PK.seed`: the weak-key `H_msg` event, hence BK;
* `q = PRF_msg(SK.prf, opt, M)`: if its string is a tweakable-hash string at `PK.seed`,
  `SK.prf = PK.seed`: K1. Otherwise its string is an `H_msg` string at `PK.seed`, since the router
  would read any other string of its shape back as `q`; so `opt = PK.seed` (O: the cache holds a
  `PRF_msg` point keyed by `SK.prf` with `opt_rand = PK.seed`, `PrfMsgAt`). Its partner `q'` is
  not a tweakable-hash point, whose string would be one (every cached tweakable-hash point is
  route-fixed), nor another `PRF_msg` point, whose encoding is injective; so `q'` is an `H_msg`
  point, whose string begins with its randomizer, which is then `SK.prf`: Fev, together with O.

## Main statements

* `isHonestQuery_or_route_eq_some_of_mem_support_romSchemeRun_routeAdv`,
  `eq_and_isHonestKey_of_mem_support_romSchemeRun_routeAdv`: provenance on the support of the
  routed run;
* `hmsgAtPrfKey_and_prfMsgAt_or_eq_of_shakeRoute_ne_prfMsg`: the `PRF_msg` row;
* `hmsgAtPrfKey_and_prfMsgAt_or_eq_or_hmsgAtWeakKey_of_clash`: the classification on a cache of
  known provenance;
* `runPrfKeyClash_or_isWeakKey_of_clash`: the classification on the routed run;
* `shakeStrongAdvantage_pure_le_strongWins_or_runPrfKeyClash_or_isWeakKey`,
  `shakeStrongAdvantage_pure_le_strongWins_or_runPrfKeyHit_or_isWeakKey`: the strong advantage
  against the single-oracle scheme is at most the probability that the routed run wins or fires Fev
  with O, K1 or BK, and so Fev, K1 or BK. -/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.Security

open Concrete

variable {vp : ValidatedParams}

/-! ## The weak-key event -/

/-- **The weak-key `H_msg` event on a cache.** The cache holds an `H_msg` point at the public key
`(pkSeed, pkRoot)` whose randomizer is `pkSeed` and whose string `PK.seed ‖ PK.seed ‖ PK.root ‖ M`
is a tweakable-hash string at `pkSeed` with an honest address key. -/
@[expose] def HmsgAtWeakKey (pkSeed : (shakeCore vp).PkSeed) (pkRoot : (shakeCore vp).Y)
    (c : (hashSpec (shakeCore vp)).QueryCache) : Prop :=
  ∃ msg, (c (.inl (.hmsg pkSeed pkSeed pkRoot msg))).isSome ∧
    IsThashString vp (IsHonestKey vp (shakeCore vp)) pkSeed
      (encode vp (.inl (.hmsg pkSeed pkSeed pkRoot msg)))

/-- **The weak-key `H_msg` event is a property of the public key.** For `16 ≤ n`, a cache holding
a weak-key `H_msg` point at `(pkSeed, pkRoot)` makes that public key weak (`IsWeakKey`). -/
theorem isWeakKey_of_hmsgAtWeakKey (hn : 16 ≤ vp.params.n) {pkSeed : (shakeCore vp).PkSeed}
    {pkRoot : (shakeCore vp).Y} {c : (hashSpec (shakeCore vp)).QueryCache}
    (h : HmsgAtWeakKey pkSeed pkRoot c) : IsWeakKey vp ⟨pkSeed, pkRoot⟩ :=
  let ⟨_, _, hT⟩ := h
  isWeakKey_of_isThashString_encode_hmsg hn hT

/-! ## Route-fixed points -/

section Route

variable {pkSeed : (shakeCore vp).PkSeed}

/-- A string the router at the honest keys reads as a tweakable-hash query is a tweakable-hash
string at the public seed with an honest address key: only rule 1 yields a tweakable-hash query. -/
theorem isThashString_of_shakeRoute_eq_thash {x : List Byte} {s : (shakeCore vp).PkSeed}
    {k : (shakeCore vp).AdrsKey} {xs : List (shakeCore vp).Y}
    (h : shakeRoute vp (IsHonestKey vp (shakeCore vp)) pkSeed x = some (.inl (.thash s k xs))) :
    IsThashString vp (IsHonestKey vp (shakeCore vp)) pkSeed x := by
  unfold shakeRoute at h
  split_ifs at h with h₁
  · exact h₁
  all_goals cases h

/-- A route-fixed tweakable-hash point is at the public seed and an honest address key. -/
theorem eq_and_isHonestKey_of_shakeRoute_encode_thash {s : (shakeCore vp).PkSeed}
    {k : (shakeCore vp).AdrsKey} {xs : List (shakeCore vp).Y}
    (h : shakeRoute vp (IsHonestKey vp (shakeCore vp)) pkSeed (encode vp (.inl (.thash s k xs))) =
      some (.inl (.thash s k xs))) :
    s = pkSeed ∧ IsHonestKey vp (shakeCore vp) k := by
  have hT := isThashString_of_shakeRoute_eq_thash h
  refine ⟨Vector.toList_inj.1 ((take_encode_thash vp s k xs).symm.trans hT.2.2.1), ?_⟩
  have := hT.2.2.2
  rwa [adrsKeyOfList_drop_encode_thash] at this

/-- **The `PRF_msg` row of the classification.** In a cache whose points are route-fixed, `H_msg`
points at `(pkSeed, pkRoot)`, or `PRF_msg` points keyed by `skPrf`, a cached `PRF_msg` point keyed
by `skPrf` that is not route-fixed and shares its string with another cached point gives an
`H_msg` point at `skPrf` together with a cached `PRF_msg` point keyed by `skPrf` whose `opt_rand`
is `pkSeed`, or `skPrf = pkSeed`. -/
theorem hmsgAtPrfKey_and_prfMsgAt_or_eq_of_shakeRoute_ne_prfMsg
    {pkRoot : (shakeCore vp).Y} {skPrf : (shakeCore vp).SkPrf}
    {c : (hashSpec (shakeCore vp)).QueryCache}
    (hc : ∀ q, (c q).isSome →
      shakeRoute vp (IsHonestKey vp (shakeCore vp)) pkSeed (encode vp q) = some q ∨
        (∃ r msg, q = .inl (.hmsg r pkSeed pkRoot msg)) ∨ ∃ o msg, q = .inr ⟨skPrf, o, msg⟩)
    {o : (shakeCore vp).Y} {msg : List Byte} {q' : (hashSpec (shakeCore vp)).Domain}
    (hq : (c (.inr ⟨skPrf, o, msg⟩)).isSome) (hq' : (c q').isSome)
    (hne : .inr ⟨skPrf, o, msg⟩ ≠ q') (he : encode vp (.inr ⟨skPrf, o, msg⟩) = encode vp q')
    (hfix : shakeRoute vp (IsHonestKey vp (shakeCore vp)) pkSeed
      (encode vp (.inr ⟨skPrf, o, msg⟩)) ≠ some (.inr ⟨skPrf, o, msg⟩)) :
    (HmsgAtPrfKey id skPrf c ∧ PrfMsgAt skPrf pkSeed c) ∨ skPrf = pkSeed := by
  by_cases hT : IsThashString vp (IsHonestKey vp (shakeCore vp)) pkSeed
      (encode vp (.inr ⟨skPrf, o, msg⟩))
  · exact Or.inr (Vector.toList_inj.1 (toList_eq_of_isThashString_encode_prfMsg _ hT))
  have hH : IsHmsgString vp pkSeed (encode vp (.inr ⟨skPrf, o, msg⟩)) := by
    by_contra hH
    exact hfix (shakeRoute_encode_prfMsg _ hT hH)
  obtain rfl : o = pkSeed :=
    Vector.toList_inj.1 (toList_eq_of_isHmsgString_encode_prfMsg _ hH).1
  refine Or.inl ⟨?_, msg, hq⟩
  rcases q' with (⟨s, k, xs⟩ | ⟨r', s', root', msg'⟩) | q'
  · rcases hc _ hq' with h | ⟨_, _, h⟩ | ⟨_, _, h⟩
    · exact (hT (he ▸ isThashString_of_shakeRoute_eq_thash h)).elim
    · cases h
    · cases h
  · refine ⟨s', root', msg', ?_⟩
    have h₁ := take_encode_prfMsg vp ⟨skPrf, o, msg⟩
    rw [he, take_encode_hmsg] at h₁
    rwa [show r' = skPrf from Vector.toList_inj.1 h₁] at hq'
  · exact (hne (congrArg Sum.inr ((encode_prfMsg_inj vp).1 he))).elim

/-- **The classification at one non-route-fixed point.** In a cache whose points are route-fixed,
`H_msg` points at `(pkSeed, pkRoot)`, or `PRF_msg` points keyed by `skPrf`, a cached point that
is not route-fixed and shares its string with another cached point gives an `H_msg` point at
`skPrf` together with a cached `PRF_msg` point keyed by `skPrf` whose `opt_rand` is `pkSeed`,
`skPrf = pkSeed`, or the weak-key event. -/
theorem hmsgAtPrfKey_and_prfMsgAt_or_eq_or_hmsgAtWeakKey_of_shakeRoute_ne
    {pkRoot : (shakeCore vp).Y} {skPrf : (shakeCore vp).SkPrf}
    {c : (hashSpec (shakeCore vp)).QueryCache}
    (hc : ∀ q, (c q).isSome →
      shakeRoute vp (IsHonestKey vp (shakeCore vp)) pkSeed (encode vp q) = some q ∨
        (∃ r msg, q = .inl (.hmsg r pkSeed pkRoot msg)) ∨ ∃ o msg, q = .inr ⟨skPrf, o, msg⟩)
    {q q' : (hashSpec (shakeCore vp)).Domain} (hq : (c q).isSome) (hq' : (c q').isSome)
    (hne : q ≠ q') (he : encode vp q = encode vp q')
    (hfix : shakeRoute vp (IsHonestKey vp (shakeCore vp)) pkSeed (encode vp q) ≠ some q) :
    ((HmsgAtPrfKey id skPrf c ∧ PrfMsgAt skPrf pkSeed c) ∨ skPrf = pkSeed) ∨
      HmsgAtWeakKey pkSeed pkRoot c := by
  rcases hc q hq with h | ⟨r, msg, rfl⟩ | ⟨o, msg, rfl⟩
  · exact (hfix h).elim
  · have hT : IsThashString vp (IsHonestKey vp (shakeCore vp)) pkSeed
        (encode vp (.inl (.hmsg r pkSeed pkRoot msg))) := by
      by_contra hT
      exact hfix (shakeRoute_encode_hmsg r pkRoot msg hT)
    obtain rfl : r = pkSeed :=
      Vector.toList_inj.1 (toList_eq_of_isThashString_encode_hmsg _ hT)
    exact Or.inr ⟨msg, hq, hT⟩
  · exact Or.inl (hmsgAtPrfKey_and_prfMsgAt_or_eq_of_shakeRoute_ne_prfMsg hc hq hq' hne he hfix)

/-- **The classification of a clash in a cache of known provenance.** In a cache whose points are
route-fixed, `H_msg` points at `(pkSeed, pkRoot)`, or `PRF_msg` points keyed by `skPrf`, a clash
gives an `H_msg` point at `skPrf` together with a cached `PRF_msg` point keyed by `skPrf` whose
`opt_rand` is `pkSeed`, `skPrf = pkSeed`, or the weak-key event. -/
theorem hmsgAtPrfKey_and_prfMsgAt_or_eq_or_hmsgAtWeakKey_of_clash (hn : vp.params.n ≤ 32)
    (hnm : vp.params.n ≤ vp.params.m)
    {pkRoot : (shakeCore vp).Y} {skPrf : (shakeCore vp).SkPrf}
    {c : (hashSpec (shakeCore vp)).QueryCache}
    (hc : ∀ q, (c q).isSome →
      shakeRoute vp (IsHonestKey vp (shakeCore vp)) pkSeed (encode vp q) = some q ∨
        (∃ r msg, q = .inl (.hmsg r pkSeed pkRoot msg)) ∨ ∃ o msg, q = .inr ⟨skPrf, o, msg⟩)
    (h : (shakeEncoding vp hn hnm pkSeed).Clash c) :
    ((HmsgAtPrfKey id skPrf c ∧ PrfMsgAt skPrf pkSeed c) ∨ skPrf = pkSeed) ∨
      HmsgAtWeakKey pkSeed pkRoot c :=
  let ⟨_, _, hne, hq, hq', he, hfix⟩ := h.exists_route_ne
  hmsgAtPrfKey_and_prfMsgAt_or_eq_or_hmsgAtWeakKey_of_shakeRoute_ne hc hq hq' hne he hfix

end Route

/-! ## The routed run -/

section Run

variable {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
  {pkSeedDist : ProbComp (shakeCore vp).PkSeed} (hn : vp.params.n ≤ 32)
  (hnm : vp.params.n ≤ vp.params.m)

/-- **The routed forger queries route-fixed points only.** At the public key `pk`, every hash
query of the routed adversary is read back from its string by the router at `PK.seed`. -/
theorem allQueriesSatisfy_routeAdv_main
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand pkSeedDist))
    (pk : PublicKeyCore (shakeCore vp)) :
    AllQueriesSatisfy ((routeAdv vp hn hnm adv).main pk)
      (Sum.elim (Sum.elim (fun _ => True) fun q =>
        (shakeEncoding vp hn hnm pk.pkSeed).route (encode vp q) = some q) fun _ => True) :=
  RandomOracleEncoding.allQueriesSatisfy_route_tableRouter adv ∅ pk

/-- **Provenance on the routed run.** Every point of the final cache of the routed run is an
honest query of the run's key pair (`IsHonestQuery`) or is read back from its string by the router
at the run's public seed. -/
theorem isHonestQuery_or_route_eq_some_of_mem_support_romSchemeRun_routeAdv
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand pkSeedDist))
    {z : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache}
    (hz : z ∈ support (romSchemeRun (shakeCore vp) (Equiv.refl _) optRand pkSeedDist
      (routeAdv vp hn hnm adv))) (q : (hashSpec (shakeCore vp)).Domain)
    (hq : (z.2 q).isSome) :
    IsHonestQuery vp z.1.pk z.1.sk.skPrf q ∨
      (shakeEncoding vp hn hnm z.1.pk.pkSeed).route (encode vp q) = some q :=
  isHonestQuery_or_of_mem_support_romSchemeRun _ optRand pkSeedDist
    (fun pk q => (shakeEncoding vp hn hnm pk.pkSeed).route (encode vp q) = some q)
    (allQueriesSatisfy_routeAdv_main hn hnm adv) hz q hq

include hn hnm in
/-- An honest query of a key pair is route-fixed at its public seed, an `H_msg` point at its
public key, or a `PRF_msg` point keyed by its `SK.prf`. -/
theorem shakeRoute_encode_eq_some_or_of_isHonestQuery {pk : PublicKeyCore (shakeCore vp)}
    {skPrf : (shakeCore vp).SkPrf} {q : (hashSpec (shakeCore vp)).Domain}
    (h : IsHonestQuery vp pk skPrf q) :
    shakeRoute vp (IsHonestKey vp (shakeCore vp)) pk.pkSeed (encode vp q) = some q ∨
      (∃ r msg, q = .inl (.hmsg r pk.pkSeed pk.pkRoot msg)) ∨
        ∃ o msg, q = .inr ⟨skPrf, o, msg⟩ := by
  rcases q with (⟨s, k, xs⟩ | ⟨r, s, root, msg⟩) | ⟨skPrf', o, msg⟩
  · obtain ⟨rfl, hk⟩ := h
    exact Or.inl (shakeEncoding_route_encode_thash hn hnm _ hk xs)
  · obtain ⟨rfl, rfl⟩ := h
    exact Or.inr (Or.inl ⟨r, msg, rfl⟩)
  · obtain rfl : skPrf' = skPrf := h
    exact Or.inr (Or.inr ⟨o, msg, rfl⟩)

/-- Every point of the final cache of the routed run is route-fixed at the run's public seed, an
`H_msg` point at the run's public key, or a `PRF_msg` point keyed by the run's `SK.prf`. -/
theorem route_eq_some_or_of_mem_support_romSchemeRun_routeAdv
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand pkSeedDist))
    {z : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache}
    (hz : z ∈ support (romSchemeRun (shakeCore vp) (Equiv.refl _) optRand pkSeedDist
      (routeAdv vp hn hnm adv))) (q : (hashSpec (shakeCore vp)).Domain)
    (hq : (z.2 q).isSome) :
    shakeRoute vp (IsHonestKey vp (shakeCore vp)) z.1.pk.pkSeed (encode vp q) = some q ∨
      (∃ r msg, q = .inl (.hmsg r z.1.pk.pkSeed z.1.pk.pkRoot msg)) ∨
        ∃ o msg, q = .inr ⟨z.1.sk.skPrf, o, msg⟩ :=
  (isHonestQuery_or_route_eq_some_of_mem_support_romSchemeRun_routeAdv hn hnm adv hz q hq).elim
    (shakeRoute_encode_eq_some_or_of_isHonestQuery hn hnm) Or.inl

/-- **Provenance of the tweakable-hash points.** Every tweakable-hash point of the final cache of
the routed run, honest or forged, is at the run's public seed and an honest address key. -/
theorem eq_and_isHonestKey_of_mem_support_romSchemeRun_routeAdv
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand pkSeedDist))
    {z : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache}
    (hz : z ∈ support (romSchemeRun (shakeCore vp) (Equiv.refl _) optRand pkSeedDist
      (routeAdv vp hn hnm adv))) {s : (shakeCore vp).PkSeed} {k : (shakeCore vp).AdrsKey}
    {xs : List (shakeCore vp).Y} (hq : (z.2 (.inl (.thash s k xs))).isSome) :
    s = z.1.pk.pkSeed ∧ IsHonestKey vp (shakeCore vp) k := by
  rcases route_eq_some_or_of_mem_support_romSchemeRun_routeAdv hn hnm adv hz _ hq
    with h | ⟨_, _, h⟩ | ⟨_, _, h⟩
  · exact eq_and_isHonestKey_of_shakeRoute_encode_thash h
  · cases h
  · cases h

/-! ## The classification -/

/-- **Clash ⇒ (Fev ∧ O) ∨ K1 ∨ BK.** At a fixed public seed `pkSeed` and `16 ≤ n`, on the support
of the run of the three-oracle scheme against the routed adversary, two distinct cached typed
queries with the same SHAKE256 string give a hit of the message-`PRF` key at `opt_rand = PK.seed`
(`RunPrfKeyClash id pkSeed pkSeed`: a cached `H_msg` point whose randomizer is `SK.prf` (Fev)
together with a cached `PRF_msg` point keyed by `SK.prf` whose `opt_rand` is `PK.seed` (O), or
`SK.prf = PK.seed` (K1)) or a weak public key (BK, `IsWeakKey`). -/
theorem runPrfKeyClash_or_isWeakKey_of_clash (hn16 : 16 ≤ vp.params.n)
    (pkSeed : (shakeCore vp).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed)))
    {z : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache}
    (hz : z ∈ support (romSchemeRun (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)
      (routeAdv vp hn hnm adv)))
    (h : (shakeEncoding vp hn hnm pkSeed).Clash z.2) :
    RunPrfKeyClash id pkSeed pkSeed z ∨ IsWeakKey vp z.1.pk := by
  have hpk : z.1.pk.pkSeed = pkSeed := by
    simpa using pkSeed_mem_support_of_mem_support_romSchemeRun _ optRand _ hz
  have hc := route_eq_some_or_of_mem_support_romSchemeRun_routeAdv hn hnm adv hz
  rw [hpk] at hc
  refine (hmsgAtPrfKey_and_prfMsgAt_or_eq_or_hmsgAtWeakKey_of_clash hn hnm hc h).imp_right
    fun hw => ?_
  rw [← hpk] at hw
  exact isWeakKey_of_hmsgAtWeakKey hn16 hw

/-- **SLH-DSA over one SHAKE256 oracle: the faithfulness events, with the `opt_rand` of a
`PRF_msg` clash.** At a fixed public seed and `16 ≤ n`, the strong forging advantage against
`shakeRomScheme` is at most the probability that the run of the three-oracle scheme against the
routed adversary wins strongly or hits the message-`PRF` key at `opt_rand = PK.seed`
(`RunPrfKeyClash id pkSeed pkSeed`: Fev with O, or K1), or has a weak public key (BK). -/
theorem shakeStrongAdvantage_pure_le_strongWins_or_runPrfKeyClash_or_isWeakKey
    (hn16 : 16 ≤ vp.params.n) (pkSeed : (shakeCore vp).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) :
    shakeStrongAdvantage vp adv ≤
      Pr{let z ← romSchemeRun (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)
          (routeAdv vp hn hnm adv.toUnforgeableAdversary)}[
        (z.1.strongWins = true ∨ RunPrfKeyClash id pkSeed pkSeed z) ∨ IsWeakKey vp z.1.pk] :=
  (shakeStrongAdvantage_pure_le hn hnm pkSeed adv).trans <| prEvent_mono_of_support _ _ _
    fun _ hz h => h.elim (fun h => Or.inl (Or.inl h)) fun h =>
      (runPrfKeyClash_or_isWeakKey_of_clash hn hnm hn16 pkSeed _ hz h).imp_left Or.inr

/-- **SLH-DSA over one SHAKE256 oracle: the faithfulness events.** At a fixed public seed and
`16 ≤ n`, the strong forging advantage against `shakeRomScheme` is at most the probability that the
run of the three-oracle scheme against the routed adversary wins strongly or hits the message-`PRF`
key (`RunPrfKeyHit id pkSeed`: Fev or K1), or has a weak public key (BK). -/
theorem shakeStrongAdvantage_pure_le_strongWins_or_runPrfKeyHit_or_isWeakKey
    (hn16 : 16 ≤ vp.params.n) (pkSeed : (shakeCore vp).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) :
    shakeStrongAdvantage vp adv ≤
      Pr{let z ← romSchemeRun (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)
          (routeAdv vp hn hnm adv.toUnforgeableAdversary)}[
        (z.1.strongWins = true ∨ RunPrfKeyHit id pkSeed z) ∨ IsWeakKey vp z.1.pk] :=
  (shakeStrongAdvantage_pure_le_strongWins_or_runPrfKeyClash_or_isWeakKey hn hnm hn16 pkSeed
    adv).trans <|
    prEvent_mono _ _ _ fun _ => Or.imp_left (Or.imp_right (Or.imp_left And.left))

end Run

end SLHDSA.Security
