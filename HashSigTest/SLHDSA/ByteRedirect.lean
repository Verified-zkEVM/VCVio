/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteRedirect
public import HashSig.SLHDSA.Security.ByteConformance

/-!
# The linked redirect, checked

`HashSig.SLHDSA.Security.ByteRedirect` redirects the tweakable-hash queries whose SHAKE256 layout
is also that of an `H_msg` query. This file checks it.

* **At SLH-DSA-SHAKE-256s** (`n = 32`) a concrete point is linked, and the redirect is not the
  identity there: the view, through the redirect, of the cache holding only that point has no entry
  at it. The string laying it out is linked and is issued as its `H_msg` query. A point at the
  seed's address with first block other than `PK.root` is not linked and is passed on. The linked
  string with one more byte is not linked, so the forger-side redirect leaves it raw, and the
  router reads it by its `H_msg` rule.
* **At SLH-DSA-SHAKE-256f** (`n = 32`) a concrete point is linked and the redirect is not the
  identity there.
* **At SLH-DSA-SHAKE-128s** (`n = 16`) the redirect is the identity, every cache is its own view
  through it, no string is linked, and the forger-side redirect is the plain lift of raw
  queries.
* **At all 12 FIPS 205 parameter sets**: invisibility over the single oracle, the verification
  identity, and the budget of the verifying adversary.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.ByteRedirectTest

open Concrete Security

/-- SLH-DSA-SHAKE-256s. -/
abbrev vp256s : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_256s

/-- SLH-DSA-SHAKE-256f. -/
abbrev vp256f : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_256f

/-- SLH-DSA-SHAKE-128s. -/
abbrev vp128s : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_128s

/-! ## A linked point at SLH-DSA-SHAKE-256s -/

/-- The bytes `0, 1, …, 31`. -/
def seedBytes : Bytes 32 :=
  ⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31], rfl⟩

/-- The bytes `7, …, 7`. -/
def rootBytes : Bytes 32 :=
  ⟨#[7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
    7], rfl⟩

/-- The bytes `9, …, 9`. -/
def nodeBytes : Bytes 32 :=
  ⟨#[9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
    9], rfl⟩

/-- A public key: seed `seedBytes`, root `rootBytes`. -/
def pk : PublicKeyCore (shakeCore vp256s) := ⟨seedBytes, rootBytes⟩

/-- The address key with the bytes of the public seed. -/
def seedKey : (shakeCore vp256s).AdrsKey := seedBytes

/-- A node. -/
def node : (shakeCore vp256s).Y := nodeBytes

/-- The tweakable-hash query `T(PK.seed, PK.seed, [PK.root, node])`. -/
abbrev linkedPoint : (publicHashSpec (shakeCore vp256s)).Domain :=
  .thash pk.pkSeed seedKey [pk.pkRoot, node]

/-- It is linked. -/
theorem isLinked_linkedPoint : IsLinked vp256s pk linkedPoint := ⟨rfl, rfl, rfl⟩

/-- The cache holding the node `node` at the linked point and nothing else. -/
noncomputable def cache : (publicHashSpec (shakeCore vp256s)).QueryCache :=
  (∅ : (publicHashSpec (shakeCore vp256s)).QueryCache).cacheQuery linkedPoint node

/-- The view of the cache through the redirect has no entry at the linked point, where the cache
has one. -/
theorem viewBy_cache_linkedPoint :
    cache.viewBy (linkedRedirect vp256s pk) linkedPoint = none ∧
      cache linkedPoint = some node := by
  refine ⟨?_, QueryCache.cacheQuery_self _ _ _⟩
  rw [viewBy_linkedRedirect_of_isLinked cache isLinked_linkedPoint]
  change Option.map (prefixBytes 32) (cache (linkedHmsg vp256s pk.pkSeed pk.pkRoot [node])) =
    (none : Option (Bytes 32))
  simp [cache, QueryCache.cacheQuery_of_ne]

/-- **The redirect is not the identity at SLH-DSA-SHAKE-256s.** -/
theorem linkedRedirect_linkedPoint_ne :
    linkedRedirect vp256s pk linkedPoint ≠ query linkedPoint := fun h => by
  have := viewBy_cache_linkedPoint
  rw [QueryCache.viewBy_apply_of_eq_query h] at this
  simp [this.2] at this

/-- The string laying out the linked point is linked. -/
theorem isLinkedString_encode :
    IsLinkedString vp256s pk (encode vp256s (.inl linkedPoint)) :=
  ⟨_, isLinked_linkedPoint, rfl⟩

/-- The forger-side redirect issues that string as the `H_msg` query it lays out. -/
example : linkedRawImpl vp256s pk (.inr (encode vp256s (.inl linkedPoint))) =
    (query (spec := unifSpec + (hashSpec (shakeCore vp256s) + shakeSpec vp256s))
      (.inr (.inl (.inl (.hmsg pk.pkSeed pk.pkSeed pk.pkRoot
        ((encode vp256s (.inl linkedPoint)).drop 96))))) :
      OracleComp (unifSpec + (hashSpec (shakeCore vp256s) + shakeSpec vp256s))
        (Bytes vp256s.params.m)) := by
  simp only [linkedRawImpl, isLinkedString_encode, ↓reduceIte]
  rfl

/-- A tweakable-hash query at `PK.seed` with the seed's bytes as address but a first block other
than `PK.root`. -/
abbrev offPoint : (publicHashSpec (shakeCore vp256s)).Domain :=
  .thash pk.pkSeed seedKey [node, pk.pkRoot]

/-- It is not linked, and the redirect passes it on. -/
example : ¬IsLinked vp256s pk offPoint ∧ linkedRedirect vp256s pk offPoint = query offPoint :=
  have h : ¬IsLinked vp256s pk offPoint := fun h =>
    absurd (congrArg Vector.toList h.2.2) (by decide)
  ⟨h, linkedRedirect_of_not_isLinked h⟩

/-- The linked string with one more byte: of the linked shape, its tail not a whole number of
blocks. -/
abbrev longString : List Byte := encode vp256s (.inl linkedPoint) ++ [0]

/-- It has `129` bytes. -/
theorem length_longString : longString.length = 129 := by
  rw [List.length_append, length_encode_thash]
  rfl

/-- It is not linked: no tweakable-hash string has `129` bytes. -/
theorem not_isLinkedString_longString : ¬IsLinkedString vp256s pk longString := by
  rintro ⟨⟨s, k, xs⟩ | _, h, he⟩
  · have hl := length_encode_thash vp256s s k xs
    rw [he, length_longString, show vp256s.params.n = 32 by decide] at hl
    omega
  · exact h

/-- So the forger-side redirect leaves it raw. -/
example : linkedRawImpl vp256s pk (.inr longString) =
    (query (spec := unifSpec + (hashSpec (shakeCore vp256s) + shakeSpec vp256s))
      (.inr (.inr longString)) :
      OracleComp (unifSpec + (hashSpec (shakeCore vp256s) + shakeSpec vp256s))
        (Bytes vp256s.params.m)) := by
  simp only [linkedRawImpl, not_isLinkedString_longString, ↓reduceIte]

/-- The router, every key admitted, reads it by its `H_msg` rule: its tail after the address is
not a whole number of blocks, and its second block is the public seed. -/
example : shakeRoute vp256s (fun _ => True) pk.pkSeed longString =
    some (.inl (.hmsg (nodeOfList vp256s longString) pk.pkSeed
      (nodeOfList vp256s (longString.drop 64)) (longString.drop 96))) := by
  refine shakeRoute_of_isHmsgString (fun h => ?_) ⟨?_, ?_⟩
  · have h2 := h.2.1
    rw [length_longString, show vp256s.params.n = 32 by decide] at h2
    exact absurd h2 (by decide)
  · rw [length_longString]
    decide
  · change ((encode vp256s (.inl linkedPoint) ++ [0]).drop 32).take 32 = Vector.toList seedBytes
    rw [List.drop_append_of_le_length (by rw [length_encode_thash]; decide),
      List.take_append_of_le_length (by rw [List.length_drop, length_encode_thash]; decide)]
    exact take_drop_encode_thash vp256s pk.pkSeed seedKey [pk.pkRoot, node]

/-! ## A linked point at SLH-DSA-SHAKE-256f -/

/-- A public key at SLH-DSA-SHAKE-256f: seed `seedBytes`, root `rootBytes`. -/
def pk256f : PublicKeyCore (shakeCore vp256f) := ⟨seedBytes, rootBytes⟩

/-- The tweakable-hash query `T(PK.seed, PK.seed, [PK.root])` at SLH-DSA-SHAKE-256f. -/
abbrev linkedPoint256f : (publicHashSpec (shakeCore vp256f)).Domain :=
  .thash pk256f.pkSeed seedBytes [pk256f.pkRoot]

/-- It is linked. -/
theorem isLinked_linkedPoint256f : IsLinked vp256f pk256f linkedPoint256f := ⟨rfl, rfl, rfl⟩

/-- The redirect is not the identity at SLH-DSA-SHAKE-256f: on the cache holding only the linked
point, the view has no entry there. -/
example : linkedRedirect vp256f pk256f linkedPoint256f ≠ query linkedPoint256f := fun h => by
  let c := (∅ : (publicHashSpec (shakeCore vp256f)).QueryCache).cacheQuery linkedPoint256f
    pk256f.pkRoot
  have hv := viewBy_linkedRedirect_of_isLinked c isLinked_linkedPoint256f
  rw [QueryCache.viewBy_apply_of_eq_query h] at hv
  change c linkedPoint256f = (Option.map (prefixBytes 32)
    (c (linkedHmsg vp256f pk256f.pkSeed pk256f.pkRoot [])) : Option (Bytes 32)) at hv
  simp [c, QueryCache.cacheQuery_of_ne] at hv

/-! ## The identity at SLH-DSA-SHAKE-128s -/

/-- The redirect passes every query on. -/
example (pk : PublicKeyCore (shakeCore vp128s)) (t : (publicHashSpec (shakeCore vp128s)).Domain) :
    linkedRedirect vp128s pk t = query t :=
  linkedRedirect_eq_query_of_ne (by decide) t

/-- Every cache is its own view through the redirect. -/
example (pk : PublicKeyCore (shakeCore vp128s))
    (c : (publicHashSpec (shakeCore vp128s)).QueryCache) :
    c.viewBy (linkedRedirect vp128s pk) = c :=
  QueryCache.ext fun t =>
    QueryCache.viewBy_apply_of_eq_query (linkedRedirect_eq_query_of_ne (by decide) t) c

/-- No string is linked. -/
example (pk : PublicKeyCore (shakeCore vp128s)) (x : List Byte) : ¬IsLinkedString vp128s pk x :=
  not_isLinkedString_of_ne (by decide) x

/-- The forger-side redirect is the plain lift of raw queries. -/
example (pk : PublicKeyCore (shakeCore vp128s)) :
    linkedRawImpl vp128s pk = liftRawImpl (hs := hashSpec (shakeCore vp128s)) :=
  linkedRawImpl_eq_liftRawImpl_of_ne (by decide)

/-! ## At all 12 FIPS 205 parameter sets -/

/-- The redirect is invisible over the single oracle. -/
example (set : FipsParameterSet) (pk : PublicKeyCore (shakeCore set.validatedParams)) {α : Type}
    (oa : OracleComp (unifSpec + hashSpec (shakeCore set.validatedParams)) α) :
    simulateQ (encImpl _) (simulateQ (linkedHashRedirect _ pk) oa) = simulateQ (encImpl _) oa :=
  simulateQ_encImpl_simulateQ_linkedHashRedirect oa

/-- The single-SHAKE256 verification is the redirected verification, encoded. -/
example (set : FipsParameterSet)
    (optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y)
    (pkSeedDist : ProbComp (shakeCore set.validatedParams).PkSeed)
    (pk : PublicKeyCore (shakeCore set.validatedParams)) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore set.validatedParams (shakeCore set.validatedParams)) :
    (shakeRomScheme _ optRand pkSeedDist).verify pk msg sig =
      simulateQ (encImpl _) (liftPub (redirectedVerify _ pk msg sig)) :=
  shakeRomScheme_verify_eq optRand pkSeedDist msg sig

/-- Encoding the common interface undoes the forger-side redirect. -/
example (set : FipsParameterSet) (pk : PublicKeyCore (shakeCore set.validatedParams))
    (pkSeed : (shakeCore set.validatedParams).PkSeed) :
    (shakeEncoding _ set.n_le_32 set.n_le_m pkSeed).encodeImpl ∘ₛ linkedRawImpl _ pk =
      QueryImpl.id' _ :=
  encodeImpl_shakeEncoding_compose_linkedRawImpl set.n_le_32 set.n_le_m pkSeed

/-- The verifying adversary makes at most `qh + V` hash and `qs` signing queries. -/
example (set : FipsParameterSet)
    {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    {pkSeedDist : ProbComp (shakeCore set.validatedParams).PkSeed}
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams optRand pkSeedDist))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    (verifyingAdv _ set.n_le_32 set.n_le_m adv).RomQueryBound
      (qh + GeneralScheme.verifyInternalQueryBound set.validatedParams.params) qs :=
  romQueryBound_verifyingAdv set.n_le_32 set.n_le_m hadv

end SLHDSA.ByteRedirectTest
