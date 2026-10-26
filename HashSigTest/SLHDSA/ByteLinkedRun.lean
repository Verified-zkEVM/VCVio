/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteLinkedRun
public import HashSig.SLHDSA.Security.ByteConformance

/-!
# The single-SHAKE256 run as a prefix of the verifying run, checked

`HashSig.SLHDSA.Security.ByteLinkedRun` bounds the strong advantage against SLH-DSA over one
SHAKE256 oracle at `n = 32` by an event of the run against the verifying adversary. This file checks
it.

* **At SLH-DSA-SHAKE-256s** the bound holds at every public seed, for any `opt_rand`, with the
  verifying adversary of an adversary making `2 ^ 64` hash and `2 ^ 64` signing queries making
  `2 ^ 64 + V` hash and `2 ^ 64` signing queries; at a public seed whose bytes are not an honest
  address key the root event never fires.
* **The clash of the final verification, at a weak seed.** At a public seed whose bytes are the
  key of an honest address, the top-layer XMSS node `weakAdrs`, the cache holding the linked point
  at that key and its `H_msg` reading, the two points the non-redirected and the redirected
  verification query, has a clash that is not the message-`PRF` key hit: `SK.prf ≠ PK.seed`, and
  no `H_msg` point has randomizer `SK.prf`. The classification of the linked run reads it as a
  cached linked point.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.ByteLinkedRunTest

open Concrete Security

/-- SLH-DSA-SHAKE-256s. -/
abbrev vp256s : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_256s

/-! ## The headline at SLH-DSA-SHAKE-256s -/

/-- **The headline with a concrete budget.** -/
example {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    (pkSeed : (shakeCore vp256s).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp256s optRand (pure pkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    shakeStrongAdvantage vp256s adv ≤
        Pr{let z ← romSchemeRun (shakeCore vp256s) (Equiv.refl _) optRand (pure pkSeed)
            (verifyingAdv vp256s (by decide) (by decide) adv.toUnforgeableAdversary)}[
          (RedirectedWins vp256s z ∨ RunPrfKeyClash id pkSeed pkSeed z) ∨
            ¬HonestOffLinked vp256s z] ∧
      (verifyingAdv vp256s (by decide) (by decide) adv.toUnforgeableAdversary).RomQueryBound
        (2 ^ 64 + GeneralScheme.verifyInternalQueryBound vp256s.params) (2 ^ 64) :=
  ⟨shakeStrongAdvantage_pure_le_verifyingAdv rfl (by decide) pkSeed adv,
    romQueryBound_verifyingAdv _ _ hadv⟩

/-- **The root event needs a weak seed.** -/
example {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    (pkSeed : (shakeCore vp256s).PkSeed)
    (hs : ¬IsHonestKey vp256s (shakeCore vp256s)
      (adrsKeyOfList vp256s (Vector.toList (pkSeed : Bytes 32))))
    (adv : UnforgeableAdversary (shakeRomScheme vp256s optRand (pure pkSeed)))
    {z : RomOutcome vp256s (shakeCore vp256s) × (hashSpec (shakeCore vp256s)).QueryCache}
    (hz : z ∈ support (romSchemeRun (shakeCore vp256s) (Equiv.refl _) optRand (pure pkSeed)
      (verifyingAdv vp256s (by decide) (by decide) adv))) :
    HonestOffLinked vp256s z := by
  have hseed : z.1.pk.pkSeed = pkSeed := by
    simpa using pkSeed_mem_support_of_mem_support_romSchemeRun _ optRand _ hz
  exact honestOffLinked_of_mem_support_romSchemeRun hz (hseed ▸ hs)

/-! ## The clash of the final verification, at a weak seed -/

/-- The address of the node at height `1` and index `0` of the top-layer XMSS tree. -/
abbrev weakAdrs : Adrs :=
  xmssNodeAdrs (GeneralHypertree.layerAdrs (vp256s.params.d - 1) 0) 1 0

theorem weakAdrs_mem : weakAdrs ∈ constructionAddresses vp256s := by
  rw [weakAdrs, ← LayerTreeCoord.top_toAdrs_layerAdrs]
  exact xmssNodeAdrs_mem_constructionAddresses _ one_pos (by decide) (by decide)

/-- The key of `weakAdrs`. -/
abbrev weakKey : (shakeCore vp256s).AdrsKey := (shakeCore vp256s).adrsToKey weakAdrs

/-- It is an honest address key. -/
theorem isHonestKey_weakKey : IsHonestKey vp256s (shakeCore vp256s) weakKey :=
  ⟨weakAdrs, .inl weakAdrs_mem, rfl⟩

/-- A public key whose seed has the bytes of `weakKey`, so the seed is weak, and whose root is
`7, …, 7`. -/
def pk : PublicKeyCore (shakeCore vp256s) := ⟨(weakKey : Bytes 32), Vector.replicate 32 7⟩

/-- The bytes of the seed are the honest key `weakKey`. -/
example : IsHonestKey vp256s (shakeCore vp256s)
    (adrsKeyOfList vp256s (Vector.toList (pk.pkSeed : Bytes 32))) := by
  convert isHonestKey_weakKey using 1
  exact bytesOfList_toList (weakKey : Bytes 32)

/-- A message-`PRF` key: `5, …, 5`. -/
def skPrf : (shakeCore vp256s).SkPrf := Vector.replicate 32 5

/-- A node: `9, …, 9`. -/
def node : (shakeCore vp256s).Y := Vector.replicate 32 9

/-- The linked point `T(PK.seed, weakKey, [PK.root, node])`, at the honest key `weakKey`: the
input that the verification of a forgery whose path reaches `weakAdrs` with first block `PK.root`
queries without the redirect. -/
abbrev linkedPoint : (hashSpec (shakeCore vp256s)).Domain :=
  .inl (.thash pk.pkSeed weakKey [pk.pkRoot, node])

/-- Its `H_msg` reading, which the redirected verification queries in its place. -/
abbrev linkedPointHmsg : (hashSpec (shakeCore vp256s)).Domain :=
  .inl (linkedHmsg vp256s pk.pkSeed pk.pkRoot [node])

/-- The cache holding the two. -/
noncomputable def cache : (hashSpec (shakeCore vp256s)).QueryCache :=
  ((∅ : (hashSpec (shakeCore vp256s)).QueryCache).cacheQuery linkedPoint node).cacheQuery
    linkedPointHmsg (Vector.replicate _ 0)

theorem cache_apply_of_ne {q : (hashSpec (shakeCore vp256s)).Domain} (h₁ : q ≠ linkedPoint)
    (h₂ : q ≠ linkedPointHmsg) : cache q = none := by
  rw [cache, QueryCache.cacheQuery_of_ne _ _ h₂, QueryCache.cacheQuery_of_ne _ _ h₁,
    QueryCache.empty_apply]

/-- The cache has the provenance of the linked run at `pk` with key `skPrf`: the tweakable-hash
point is route-fixed, and the other point is an `H_msg` point at `pk`. -/
theorem cache_provenance (q : (hashSpec (shakeCore vp256s)).Domain) (hq : (cache q).isSome) :
    shakeRoute vp256s (IsHonestKey vp256s (shakeCore vp256s)) pk.pkSeed (encode vp256s q) =
        some q ∨
      (∃ r msg, q = .inl (.hmsg r pk.pkSeed pk.pkRoot msg)) ∨
        ∃ o msg, q = .inr ⟨skPrf, o, msg⟩ := by
  by_cases h₁ : q = linkedPoint
  · subst h₁
    exact Or.inl (shakeRoute_encode_thash (pkSeed := pk.pkSeed) weakKey [pk.pkRoot, node]
      isHonestKey_weakKey)
  by_cases h₂ : q = linkedPointHmsg
  · exact Or.inr (Or.inl ⟨_, _, h₂⟩)
  rw [cache_apply_of_ne h₁ h₂] at hq
  cases hq

/-- **The cache has a clash.** -/
theorem clash_cache : (shakeEncoding vp256s (FipsParameterSet.n_le_32 _)
    (FipsParameterSet.n_le_m _) pk.pkSeed).Clash cache := by
  refine ⟨linkedPoint, linkedPointHmsg, by simp, ?_, ?_, ?_⟩
  · rw [cache, QueryCache.cacheQuery_of_ne _ _ (by simp), QueryCache.cacheQuery_self]
    rfl
  · rw [cache, QueryCache.cacheQuery_self]
    rfl
  · exact (encode_linkedHmsg (vp := vp256s) [node] rfl).symm

/-- The message-`PRF` key is not the public seed. -/
theorem skPrf_ne : skPrf ≠ pk.pkSeed := fun h => by
  have h0 : (pk.pkSeed : Bytes 32).toList.head? = some 0 := by rfl
  exact absurd ((congrArg (fun v : Bytes 32 => v.toList.head?) h).trans h0) (by decide)

/-- **It is neither Fev nor K1.** No `H_msg` point of the cache has randomizer `SK.prf`, and
`SK.prf ≠ PK.seed`. -/
theorem not_hmsgAtPrfKey_or_eq : ¬(HmsgAtPrfKey id skPrf cache ∨ skPrf = pk.pkSeed) := by
  rintro (⟨ps, pr, msg, h⟩ | h)
  · rw [cache_apply_of_ne (by simp) fun h => by
      simp only [linkedPointHmsg, Sum.inl.injEq] at h
      exact skPrf_ne (PublicHashQuery.hmsg.inj h).1] at h
    cases h
  · exact skPrf_ne h

/-- So the classification of the linked run concludes a cached linked point. -/
example : LinkedCached vp256s pk cache :=
  (hmsgAtPrfKey_and_prfMsgAt_or_eq_or_linkedCached_of_clash (pkRoot := pk.pkRoot) rfl
    (FipsParameterSet.n_le_m _) cache_provenance clash_cache).resolve_left
      fun h => not_hmsgAtPrfKey_or_eq (h.imp_left And.left)

end SLHDSA.ByteLinkedRunTest
