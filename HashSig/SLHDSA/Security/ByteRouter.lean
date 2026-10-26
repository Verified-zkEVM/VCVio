/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteModel
public import HashSig.SLHDSA.Security.NodeGraph
public import HashSig.SLHDSA.Security.RomSchemeRun
public import VCVio.CryptoFoundations.SignatureAlg.Routed

/-!
# Routing SHAKE256 strings to the three SLH-DSA oracles

`HashSig.SLHDSA.Security.ByteModel` states SLH-DSA over one random oracle on byte strings,
`shakeRomScheme`, whose every typed query is one query of the single oracle at its FIPS 205 §11.1
layout `encode`. This module reads a byte string back as a typed query of the three-oracle
interface `hashSpec` of `HashSig.SLHDSA.Security.Target`, and so turns an adversary against
`shakeRomScheme` into an adversary against the three-oracle scheme `romScheme`.

## The router

`shakeRoute vp A pkSeed x` reads a byte string `x` at the public seed `pkSeed`, with `A` a
predicate on address keys, by the first rule that applies:

1. `x` is a tweakable-hash string `PK.seed ‖ ADRS ‖ M_1 ‖ … ‖ M_ℓ` at `pkSeed` whose address key
   satisfies `A` (`IsThashString`): the tweakable-hash query it lays out;
2. `x` has at least `3n` bytes and its second block of `n` bytes is `pkSeed` (`IsHmsgString`):
   the `H_msg` query `R ‖ PK.seed ‖ PK.root ‖ M` it lays out;
3. `x` has at least `2n` bytes: the `PRF_msg` query `SK.prf ‖ opt_rand ‖ M` it lays out;
4. otherwise `x` is read as no query.

A query the router returns encodes the string (`encode_eq_of_shakeRoute_eq_some`), and for
`n ≤ 32` every encoding has at least `2n` bytes, so the router reads every encoding as some query
(`isSome_shakeRoute_encode`). The bound `n ≤ 32` is needed: for `n > 32`, a tweakable-hash string
with no input blocks is shorter than `2n` bytes and may fail rule 1.

The router need not read an encoding back as the query it encodes, since one string can lay out
queries of several roles. A query read back from its encoding is *route-fixed*: every
tweakable-hash query at `pkSeed` whose key satisfies `A` (`shakeRoute_encode_thash`); an `H_msg`
query at `pkSeed` whose encoding is not a rule 1 string (`shakeRoute_encode_hmsg`); a `PRF_msg`
query whose encoding is neither a rule 1 nor a rule 2 string (`shakeRoute_encode_prfMsg`). The rule
1 string of an `H_msg` query has `R = PK.seed`, that of a `PRF_msg` query `SK.prf = PK.seed`, and
the rule 2 string of a `PRF_msg` query `opt_rand = PK.seed` with a message of at least `n` bytes
(`toList_eq_of_isThashString_encode_hmsg` and its two siblings).

## Honest addresses

The router is instantiated at the honest address keys `IsHonestKey vp core`: the keys of the
addresses of the union ledger `constructionAddresses vp` and of their secret children
(`IsHonestAdrs`), so that every tweakable-hash query of honest SLH-DSA at the public seed is
route-fixed (`shakeEncoding_route_encode_thash`). That honest SLH-DSA queries the tweakable hash
only at honest keys is argued here from the ledger, not proved: this module proves route-fixedness
of a query from its key, and the membership of the keys of honest queries is a statement about the
programs, proved separately. The keys of the nodes of the SLH-DSA graph are honest
(`isHonestKey_nodeKey`), and so are those of their secret children
(`isHonestKey_of_inl_mem_childAdrs`) and of honest entries (`isHonestKey_of_honestEntry`). The
predicate is decided classically, by a pinned instance, and never enumerated.

An `H_msg` string `R ‖ PK.seed ‖ PK.root ‖ M` is read by rule 1 only if its address key, the first
`32` bytes of `PK.seed ‖ PK.root` for `16 ≤ n`, is honest: the public key is then weak
(`IsWeakKey`, `isWeakKey_of_isThashString_encode_hmsg`), a predicate of the public key alone.

## The encoding and the routed adversary

`shakeEncoding vp hn hnm pkSeed` is the `RandomOracleEncoding` of the three oracles into the
single oracle with the router at the honest keys: the typed answer is the first `n` bytes of the
`m`-byte answer at a tweakable-hash or `PRF_msg` query and the whole answer at an `H_msg` query,
as in `encImpl` (`encodeImpl_shakeEncoding_compose_liftTypedImpl`). It needs `n ≤ 32` and
`n ≤ m`, which every FIPS 205 parameter set satisfies (`FipsParameterSet.n_le_32`,
`FipsParameterSet.n_le_m`).

`routeAdv vp hn hnm adv` runs an adversary against `shakeRomScheme` against `romScheme`: at its
public key `pk` it holds the router of `shakeEncoding vp hn hnm pk.pkSeed` and its table of private
values (`RandomOracleEncoding.tableRouter`), so it reads the public seed from the public key. It
keeps the budget of `adv` (`romQueryBound_routeAdv`).

## Main statements

* `shakeStrongAdvantage_pure_le`: at a fixed public seed, the strong advantage of an adversary
  against `shakeRomScheme` is at most the probability that the run of `romScheme` against the routed
  adversary wins strongly or ends with two distinct cached typed queries of the same encoding.
* `romQueryBound_routeAdv`: the routed adversary keeps the budget.
* `encode_eq_of_shakeRoute_eq_some`, `isSome_shakeRoute_encode`, and the route-fixedness lemmas,
  for the router at any key predicate (`shakeRoute_encode_thash`, `shakeRoute_encode_hmsg`,
  `shakeRoute_encode_prfMsg`) and for the encoding at the honest keys
  (`shakeEncoding_route_encode_thash`, `shakeEncoding_route_encode_hmsg`,
  `shakeEncoding_route_encode_prfMsg`).
* `isWeakKey_of_isThashString_encode_hmsg`: rule 1 on an `H_msg` encoding needs a weak public key.

## References

* NIST FIPS 205, §11.1 (SLH-DSA using SHAKE).
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.Security

open Concrete

/-! ## Reading fields at the carriers -/

variable (vp : ValidatedParams)

/-- The node held by the first `n` bytes of a byte string. -/
@[expose] def nodeOfList (l : List Byte) : (shakeCore vp).Y := bytesOfList vp.params.n l

/-- The `PRF_msg` key held by the first `n` bytes of a byte string. -/
@[expose] def skPrfOfList (l : List Byte) : (shakeCore vp).SkPrf := bytesOfList vp.params.n l

/-- The address key held by the first `32` bytes of a byte string. -/
@[expose] def adrsKeyOfList (l : List Byte) : (shakeCore vp).AdrsKey := bytesOfList 32 l

/-- The nodes held by the first `k` blocks of `n` bytes of a byte string. -/
@[expose] def nodesOfList (k : ℕ) (l : List Byte) : List (shakeCore vp).Y :=
  bytesBlocks vp.params.n k l

variable {vp}

/-- A string of at least `n` bytes holds its first `n` bytes as a node. -/
theorem toList_nodeOfList {l : List Byte} (h : vp.params.n ≤ l.length) :
    Vector.toList (nodeOfList vp l : Bytes vp.params.n) = l.take vp.params.n :=
  toList_bytesOfList_of_le h

/-- A string of at least `n` bytes holds its first `n` bytes as a `PRF_msg` key. -/
theorem toList_skPrfOfList {l : List Byte} (h : vp.params.n ≤ l.length) :
    Vector.toList (skPrfOfList vp l : Bytes vp.params.n) = l.take vp.params.n :=
  toList_bytesOfList_of_le h

/-- A string of at least `32` bytes holds its first `32` bytes as an address key. -/
theorem toList_adrsKeyOfList {l : List Byte} (h : 32 ≤ l.length) :
    Vector.toList (adrsKeyOfList vp l : Bytes 32) = l.take 32 :=
  toList_bytesOfList_of_le h

/-- A string of `n k` bytes is the concatenation of the `k` nodes it holds. -/
theorem flatten_map_toList_nodesOfList {k : ℕ} {l : List Byte} (h : l.length = vp.params.n * k) :
    ((nodesOfList vp k l).map fun y : (shakeCore vp).Y => Vector.toList (y : Bytes vp.params.n)
      ).flatten = l :=
  flatten_map_toList_bytesBlocks h

/-! ## The rules -/

variable (vp) (A : (shakeCore vp).AdrsKey → Prop) (pkSeed : (shakeCore vp).PkSeed)

/-- **Rule 1**: `x` has the shape `PK.seed ‖ ADRS ‖ M_1 ‖ … ‖ M_ℓ` of a tweakable-hash string at
the public seed `pkSeed`, `n + 32` bytes followed by whole blocks of `n` bytes, and its address
key `ADRS` satisfies `A`. -/
@[expose] def IsThashString (x : List Byte) : Prop :=
  vp.params.n + 32 ≤ x.length ∧ vp.params.n ∣ x.length - (vp.params.n + 32) ∧
    x.take vp.params.n = Vector.toList (pkSeed : Bytes vp.params.n) ∧
    A (adrsKeyOfList vp (x.drop vp.params.n))

/-- **Rule 2**: `x` has the shape `R ‖ PK.seed ‖ PK.root ‖ M` of an `H_msg` string at the public
seed `pkSeed`: at least `3n` bytes, the second block of `n` bytes being `pkSeed`. -/
@[expose] def IsHmsgString (x : List Byte) : Prop :=
  3 * vp.params.n ≤ x.length ∧
    (x.drop vp.params.n).take vp.params.n = Vector.toList (pkSeed : Bytes vp.params.n)

instance [DecidablePred A] (x : List Byte) : Decidable (IsThashString vp A pkSeed x) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (x : List Byte) : Decidable (IsHmsgString vp pkSeed x) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **The router of SHAKE256 strings at the public seed `pkSeed`.** A byte string `x` is read as
1. the tweakable-hash query `T(PK.seed, ADRS, M_1 … M_ℓ)` it lays out, if it is a tweakable-hash
   string at `pkSeed` whose address key satisfies `A` (`IsThashString`); else
2. the `H_msg` query `H_msg(R, PK.seed, PK.root, M)` it lays out, if its second block of `n` bytes
   is `pkSeed` and it has at least `3n` bytes (`IsHmsgString`); else
3. the `PRF_msg` query `PRF_msg(SK.prf, opt_rand, M)` it lays out, if it has at least `2n` bytes;
4. no query otherwise. -/
@[expose] def shakeRoute [DecidablePred A] (x : List Byte) :
    Option (hashSpec (shakeCore vp)).Domain :=
  if IsThashString vp A pkSeed x then
    some (.inl (.thash pkSeed (adrsKeyOfList vp (x.drop vp.params.n))
      (nodesOfList vp ((x.length - (vp.params.n + 32)) / vp.params.n)
        (x.drop (vp.params.n + 32)))))
  else if IsHmsgString vp pkSeed x then
    some (.inl (.hmsg (nodeOfList vp x) pkSeed (nodeOfList vp (x.drop (2 * vp.params.n)))
      (x.drop (3 * vp.params.n))))
  else if 2 * vp.params.n ≤ x.length then
    some (.inr ⟨skPrfOfList vp x, nodeOfList vp (x.drop vp.params.n), x.drop (2 * vp.params.n)⟩)
  else none

variable {vp A pkSeed}

section Route

variable [DecidablePred A]

/-- Rule 1 of the router. -/
theorem shakeRoute_of_isThashString {x : List Byte} (h : IsThashString vp A pkSeed x) :
    shakeRoute vp A pkSeed x = some (.inl (.thash pkSeed (adrsKeyOfList vp (x.drop vp.params.n))
      (nodesOfList vp ((x.length - (vp.params.n + 32)) / vp.params.n)
        (x.drop (vp.params.n + 32))))) := by
  simp only [shakeRoute, h, ↓reduceIte]

/-- Rule 2 of the router. -/
theorem shakeRoute_of_isHmsgString {x : List Byte} (h₁ : ¬IsThashString vp A pkSeed x)
    (h₂ : IsHmsgString vp pkSeed x) :
    shakeRoute vp A pkSeed x = some (.inl (.hmsg (nodeOfList vp x) pkSeed
      (nodeOfList vp (x.drop (2 * vp.params.n))) (x.drop (3 * vp.params.n)))) := by
  simp only [shakeRoute, h₁, h₂, ↓reduceIte]

/-- Rule 3 of the router. -/
theorem shakeRoute_of_two_mul_le_length {x : List Byte} (h₁ : ¬IsThashString vp A pkSeed x)
    (h₂ : ¬IsHmsgString vp pkSeed x) (h₃ : 2 * vp.params.n ≤ x.length) :
    shakeRoute vp A pkSeed x = some (.inr ⟨skPrfOfList vp x, nodeOfList vp (x.drop vp.params.n),
      x.drop (2 * vp.params.n)⟩) := by
  simp only [shakeRoute, h₁, h₂, h₃, ↓reduceIte]

/-- A string the router reads as a query is that query's encoding. -/
theorem encode_eq_of_shakeRoute_eq_some {x : List Byte} {t : (hashSpec (shakeCore vp)).Domain}
    (h : shakeRoute vp A pkSeed x = some t) : encode vp t = x := by
  unfold shakeRoute at h
  split_ifs at h with h₁ h₂ h₃ <;> cases h
  · obtain ⟨hl, hd, ht, -⟩ := h₁
    rw [encode_thash, toList_adrsKeyOfList (by simp; omega),
      flatten_map_toList_nodesOfList (by simp [Nat.mul_div_cancel' hd]), ← ht, List.append_assoc,
      ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  · obtain ⟨hl, ht⟩ := h₂
    rw [encode_hmsg, toList_nodeOfList (by omega),
      toList_nodeOfList (by simp; omega), ← ht,
      show 3 * vp.params.n = 2 * vp.params.n + vp.params.n by omega, ← List.drop_drop,
      List.append_assoc, List.take_append_drop, two_mul, ← List.drop_drop, List.append_assoc,
      List.take_append_drop, List.take_append_drop]
  · rw [encode_prfMsg, toList_skPrfOfList (by omega), toList_nodeOfList (by simp; omega), two_mul,
      ← List.drop_drop, List.append_assoc, List.take_append_drop, List.take_append_drop]

/-- The router reads every string of at least `2n` bytes as a query. -/
theorem isSome_shakeRoute_of_two_mul_le_length {x : List Byte} (h : 2 * vp.params.n ≤ x.length) :
    (shakeRoute vp A pkSeed x).isSome := by
  unfold shakeRoute
  split_ifs <;> simp

/-- For `n ≤ 32`, the router reads every encoding as a query. -/
theorem isSome_shakeRoute_encode (hn : vp.params.n ≤ 32) (t : (hashSpec (shakeCore vp)).Domain) :
    (shakeRoute vp A pkSeed (encode vp t)).isSome :=
  isSome_shakeRoute_of_two_mul_le_length (two_mul_le_length_encode vp hn t)

/-! ## Route-fixed queries -/

section Fixed

variable (r pkRoot : (shakeCore vp).Y) (adrsKey : (shakeCore vp).AdrsKey)
  (xs : List (shakeCore vp).Y) (msg : List Byte)

/-- The address key read from a tweakable-hash string is its address key. -/
theorem adrsKeyOfList_drop_encode_thash (s : (shakeCore vp).PkSeed) :
    adrsKeyOfList vp ((encode vp (.inl (.thash s adrsKey xs))).drop vp.params.n) = adrsKey := by
  rw [adrsKeyOfList, ← bytesOfList_take, take_drop_encode_thash]
  exact bytesOfList_toList (adrsKey : Bytes 32)

/-- **Honest tweakable-hash queries are route-fixed.** A tweakable-hash query at the public seed
whose address key satisfies `A` is read back from its encoding. -/
theorem shakeRoute_encode_thash (hA : A adrsKey) :
    shakeRoute vp A pkSeed (encode vp (.inl (.thash pkSeed adrsKey xs))) =
      some (.inl (.thash pkSeed adrsKey xs)) := by
  have hr : IsThashString vp A pkSeed (encode vp (.inl (.thash pkSeed adrsKey xs))) := by
    refine ⟨?_, ?_, take_encode_thash vp pkSeed adrsKey xs, ?_⟩
    · rw [length_encode_thash]
      omega
    · rw [length_encode_thash, Nat.add_sub_cancel_left]
      exact Dvd.intro _ rfl
    · rwa [adrsKeyOfList_drop_encode_thash]
  have h := shakeRoute_of_isThashString hr
  obtain ⟨-, hk, hxs⟩ := (encode_thash_inj (vp := vp)).1 (encode_eq_of_shakeRoute_eq_some h)
  rw [h, hk, hxs]

/-- An `H_msg` query at the public seed is read back from its encoding unless the encoding is a
tweakable-hash string at the public seed whose address key satisfies `A`. -/
theorem shakeRoute_encode_hmsg
    (h : ¬IsThashString vp A pkSeed (encode vp (.inl (.hmsg r pkSeed pkRoot msg)))) :
    shakeRoute vp A pkSeed (encode vp (.inl (.hmsg r pkSeed pkRoot msg))) =
      some (.inl (.hmsg r pkSeed pkRoot msg)) := by
  have hr : IsHmsgString vp pkSeed (encode vp (.inl (.hmsg r pkSeed pkRoot msg))) :=
    ⟨by rw [length_encode_hmsg]; omega, take_drop_encode_hmsg vp r pkSeed pkRoot msg⟩
  have h' := shakeRoute_of_isHmsgString h hr
  obtain ⟨hr', -, hroot, hmsg⟩ :=
    (encode_hmsg_inj (vp := vp)).1 (encode_eq_of_shakeRoute_eq_some h')
  rw [h', hr', hroot, hmsg]

/-- A `PRF_msg` query is read back from its encoding unless the encoding is a tweakable-hash
string at the public seed whose address key satisfies `A`, or an `H_msg` string at the public
seed. -/
theorem shakeRoute_encode_prfMsg (q : PrfMsgQuery (shakeCore vp).SkPrf (shakeCore vp).Y)
    (h₁ : ¬IsThashString vp A pkSeed (encode vp (.inr q)))
    (h₂ : ¬IsHmsgString vp pkSeed (encode vp (.inr q))) :
    shakeRoute vp A pkSeed (encode vp (.inr q)) = some (.inr q) := by
  have h := shakeRoute_of_two_mul_le_length h₁ h₂ (by rw [length_encode_prfMsg]; omega)
  rw [h, (encode_prfMsg_inj (vp := vp)).1 (encode_eq_of_shakeRoute_eq_some h)]

/-- The address key read from an `H_msg` string `R ‖ PK.seed ‖ PK.root ‖ M` is the first `32`
bytes of `PK.seed ‖ PK.root ‖ M`. -/
theorem adrsKeyOfList_drop_encode_hmsg (s : (shakeCore vp).PkSeed) :
    adrsKeyOfList vp ((encode vp (.inl (.hmsg r s pkRoot msg))).drop vp.params.n) =
      adrsKeyOfList vp (Vector.toList (s : Bytes vp.params.n) ++
        Vector.toList (pkRoot : Bytes vp.params.n) ++ msg) := by
  rw [drop_encode_hmsg]

end Fixed

end Route

/-! ## Which rule fires on an encoding -/

/-- An `H_msg` string that is also a tweakable-hash string at the public seed has `R = PK.seed`.
-/
theorem toList_eq_of_isThashString_encode_hmsg {r pkRoot : (shakeCore vp).Y} {msg : List Byte}
    (s : (shakeCore vp).PkSeed)
    (h : IsThashString vp A pkSeed (encode vp (.inl (.hmsg r s pkRoot msg)))) :
    Vector.toList (r : Bytes vp.params.n) = Vector.toList (pkSeed : Bytes vp.params.n) :=
  (take_encode_hmsg vp r s pkRoot msg).symm.trans h.2.2.1

/-- A `PRF_msg` string that is also a tweakable-hash string at the public seed has
`SK.prf = PK.seed`. -/
theorem toList_eq_of_isThashString_encode_prfMsg
    (q : PrfMsgQuery (shakeCore vp).SkPrf (shakeCore vp).Y)
    (h : IsThashString vp A pkSeed (encode vp (.inr q))) :
    Vector.toList (q.skPrf : Bytes vp.params.n) = Vector.toList (pkSeed : Bytes vp.params.n) :=
  (take_encode_prfMsg vp q).symm.trans h.2.2.1

/-- A `PRF_msg` string that is also an `H_msg` string at the public seed has
`opt_rand = PK.seed` and a message of at least `n` bytes. -/
theorem toList_eq_of_isHmsgString_encode_prfMsg
    (q : PrfMsgQuery (shakeCore vp).SkPrf (shakeCore vp).Y)
    (h : IsHmsgString vp pkSeed (encode vp (.inr q))) :
    Vector.toList (q.optRand : Bytes vp.params.n) = Vector.toList (pkSeed : Bytes vp.params.n) ∧
      vp.params.n ≤ q.msg.length := by
  obtain ⟨hl, ht⟩ := h
  rw [length_encode_prfMsg] at hl
  exact ⟨(take_drop_encode_prfMsg vp q).symm.trans ht, by omega⟩

/-! ## Honest addresses -/

section Honest

variable (vp) (core : CorePrimitives vp.params)

/-- An address at which honest SLH-DSA may evaluate the tweakable hash: an address of the union
ledger `constructionAddresses vp`, or a secret-key address that is the secret child of one
(`childAdrs`), where `PRF` derives a secret value. -/
@[expose] def IsHonestAdrs (a : Adrs) : Prop :=
  a ∈ constructionAddresses vp ∨ ∃ b ∈ constructionAddresses vp, .inl a ∈ childAdrs vp b

/-- The oracle key of an honest address (`IsHonestAdrs`). -/
@[expose] def IsHonestKey (k : core.AdrsKey) : Prop :=
  ∃ a, IsHonestAdrs vp a ∧ core.adrsToKey a = k

/-- Honest keys are decided classically; the predicate is never enumerated. -/
noncomputable instance : DecidablePred (IsHonestKey vp core) := Classical.decPred _

variable {vp core}

/-- The key of a node of the SLH-DSA graph is honest. -/
theorem isHonestKey_nodeKey (κ : NodeKey core) : IsHonestKey vp core κ.1 :=
  let ⟨a, ha, hk⟩ := κ.2
  ⟨a, .inl ha, hk⟩

/-- The key of the secret child of a ledger address is honest. -/
theorem isHonestKey_of_inl_mem_childAdrs {a b : Adrs} (ha : a ∈ constructionAddresses vp)
    (hb : .inl b ∈ childAdrs vp a) : IsHonestKey vp core (core.adrsToKey b) :=
  ⟨b, .inr ⟨a, ha, hb⟩, rfl⟩

/-- Every honest entry is at the key of a ledger address. -/
theorem isHonestKey_of_honestEntry {s pk : core.PkSeed} {k : core.AdrsKey} {xs : List core.Y}
    {secret : Adrs → OracleComp (publicHashSpec core) core.Y} {c : PublicHash.Cache core}
    (h : HonestEntry secret pk c (.thash s k xs)) : IsHonestKey vp core k := by
  cases h <;> exact ⟨_, .inl ‹_ ∈ constructionAddresses vp›, rfl⟩

end Honest

/-! ## Weak public keys -/

section Weak

variable (vp)

/-- **The weak-key event.** A public key `(PK.seed, PK.root)` is weak when the first `32` bytes of
`PK.seed ‖ PK.root` are an honest address key (`IsHonestKey`). For `16 ≤ n` these are the bytes
the router reads as the address key of every `H_msg` string `R ‖ PK.seed ‖ PK.root ‖ M`, so rule 1
of the router fires on the encoding of an honest `H_msg` query only at a weak public key
(`isWeakKey_of_isThashString_encode_hmsg`). -/
@[expose] def IsWeakKey (pk : PublicKeyCore (shakeCore vp)) : Prop :=
  IsHonestKey vp (shakeCore vp) (adrsKeyOfList vp
    (Vector.toList (pk.pkSeed : Bytes vp.params.n) ++
      Vector.toList (pk.pkRoot : Bytes vp.params.n)))

variable {vp}

/-- **Rule 1 on an `H_msg` string needs a weak public key.** For `16 ≤ n`, if the encoding of the
`H_msg` query `H_msg(R, PK.seed, PK.root, M)` is a tweakable-hash string with an honest address key,
then `(PK.seed, PK.root)` is weak, whatever `R` and `M`. -/
theorem isWeakKey_of_isThashString_encode_hmsg (hn : 16 ≤ vp.params.n)
    {pkSeed s : (shakeCore vp).PkSeed} {r pkRoot : (shakeCore vp).Y} {msg : List Byte}
    (h : IsThashString vp (IsHonestKey vp (shakeCore vp)) pkSeed
      (encode vp (.inl (.hmsg r s pkRoot msg)))) :
    IsWeakKey vp ⟨s, pkRoot⟩ := by
  have hk := h.2.2.2
  rw [adrsKeyOfList_drop_encode_hmsg] at hk
  have hlen : 32 ≤ (Vector.toList (s : Bytes vp.params.n) ++
      Vector.toList (pkRoot : Bytes vp.params.n)).length := by
    rw [List.length_append, Vector.length_toList (xs := (s : Bytes vp.params.n)),
      Vector.length_toList (xs := (pkRoot : Bytes vp.params.n))]
    omega
  unfold IsWeakKey
  rwa [adrsKeyOfList, ← bytesOfList_take, List.take_append_of_le_length hlen, bytesOfList_take]
    at hk

end Weak

/-! ## The encoding -/

variable (vp)

/-- What an `m`-byte answer of the single oracle holds beyond a typed answer: the last `m - n`
bytes at a tweakable-hash or `PRF_msg` query, nothing at an `H_msg` query. -/
@[expose] def ShakeTail : (hashSpec (shakeCore vp)).Domain → Type
  | .inl (.thash ..) => Bytes (vp.params.m - vp.params.n)
  | .inl (.hmsg ..) => Unit
  | .inr _ => Bytes (vp.params.m - vp.params.n)

instance : ∀ t, SampleableType (ShakeTail vp t)
  | .inl (.thash ..) => inferInstanceAs (SampleableType (Bytes (vp.params.m - vp.params.n)))
  | .inl (.hmsg ..) => inferInstanceAs (SampleableType Unit)
  | .inr _ => inferInstanceAs (SampleableType (Bytes (vp.params.m - vp.params.n)))

variable {vp}

/-- An `m`-byte answer split, at each typed query, into the typed answer and the tail. -/
@[expose] def shakeSplit (hnm : vp.params.n ≤ vp.params.m) :
    (t : (hashSpec (shakeCore vp)).Domain) →
      Bytes vp.params.m ≃ (hashSpec (shakeCore vp)).Range t × ShakeTail vp t
  | .inl (.thash ..) => splitBytes hnm
  | .inl (.hmsg ..) => (Equiv.prodPUnit _).symm
  | .inr _ => splitBytes hnm

variable (vp)

/-- **The SHAKE256 encoding of the three SLH-DSA oracles at the public seed `pkSeed`.** A typed
query is encoded at its FIPS 205 §11.1 layout (`encode`); its answer is the first `n` bytes of the
`m`-byte answer of the single oracle at a tweakable-hash or `PRF_msg` query and the whole answer at
an `H_msg` query; raw strings are read by the router `shakeRoute` with the honest address keys
`IsHonestKey`. -/
@[expose] noncomputable def shakeEncoding (hn : vp.params.n ≤ 32)
    (hnm : vp.params.n ≤ vp.params.m) (pkSeed : (shakeCore vp).PkSeed) :
    RandomOracleEncoding (hashSpec (shakeCore vp)) (List Byte) (Bytes vp.params.m) :=
  RandomOracleEncoding.ofSplit (encode vp) (shakeRoute vp (IsHonestKey vp (shakeCore vp)) pkSeed)
    encode_eq_of_shakeRoute_eq_some (isSome_shakeRoute_encode hn) (shakeSplit hnm)

variable {vp}

section Encoding

variable (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
  (pkSeed : (shakeCore vp).PkSeed)

/-- The encoding of a typed query is its FIPS 205 §11.1 layout. -/
theorem shakeEncoding_encode : (shakeEncoding vp hn hnm pkSeed).encode = encode vp := rfl

/-- The router of the encoding is `shakeRoute` at the honest address keys. -/
theorem shakeEncoding_route :
    (shakeEncoding vp hn hnm pkSeed).route =
      shakeRoute vp (IsHonestKey vp (shakeCore vp)) pkSeed := rfl

/-- **Honest tweakable-hash queries are route-fixed in the encoding.** A tweakable-hash query at
the public seed whose address key is honest is read back from its encoding. -/
theorem shakeEncoding_route_encode_thash {k : (shakeCore vp).AdrsKey}
    (hk : IsHonestKey vp (shakeCore vp) k) (xs : List (shakeCore vp).Y) :
    (shakeEncoding vp hn hnm pkSeed).route (encode vp (.inl (.thash pkSeed k xs))) =
      some (.inl (.thash pkSeed k xs)) :=
  shakeRoute_encode_thash k xs hk

/-- An `H_msg` query at the public seed is read back from its encoding in the encoding unless its
encoding is a tweakable-hash string at the public seed with an honest address key. -/
theorem shakeEncoding_route_encode_hmsg (r pkRoot : (shakeCore vp).Y) (msg : List Byte)
    (h : ¬IsThashString vp (IsHonestKey vp (shakeCore vp)) pkSeed
      (encode vp (.inl (.hmsg r pkSeed pkRoot msg)))) :
    (shakeEncoding vp hn hnm pkSeed).route (encode vp (.inl (.hmsg r pkSeed pkRoot msg))) =
      some (.inl (.hmsg r pkSeed pkRoot msg)) :=
  shakeRoute_encode_hmsg r pkRoot msg h

/-- A `PRF_msg` query is read back from its encoding in the encoding unless its encoding is a
tweakable-hash string at the public seed with an honest address key, or an `H_msg` string at the
public seed. -/
theorem shakeEncoding_route_encode_prfMsg (q : PrfMsgQuery (shakeCore vp).SkPrf (shakeCore vp).Y)
    (h₁ : ¬IsThashString vp (IsHonestKey vp (shakeCore vp)) pkSeed (encode vp (.inr q)))
    (h₂ : ¬IsHmsgString vp pkSeed (encode vp (.inr q))) :
    (shakeEncoding vp hn hnm pkSeed).route (encode vp (.inr q)) = some (.inr q) :=
  shakeRoute_encode_prfMsg q h₁ h₂

/-- The typed answer at a tweakable-hash query is the first `n` bytes. -/
theorem shakeEncoding_trunc_thash (s : (shakeCore vp).PkSeed) (k : (shakeCore vp).AdrsKey)
    (xs : List (shakeCore vp).Y) (w : Bytes vp.params.m) :
    (shakeEncoding vp hn hnm pkSeed).trunc (.inl (.thash s k xs)) w = prefixBytes vp.params.n w :=
  rfl

/-- The typed answer at an `H_msg` query is the whole answer. -/
theorem shakeEncoding_trunc_hmsg (r root : (shakeCore vp).Y) (s : (shakeCore vp).PkSeed)
    (msg : List Byte) (w : Bytes vp.params.m) :
    (shakeEncoding vp hn hnm pkSeed).trunc (.inl (.hmsg r s root msg)) w = w :=
  rfl

/-- The typed answer at a `PRF_msg` query is the first `n` bytes. -/
theorem shakeEncoding_trunc_prfMsg (q : PrfMsgQuery (shakeCore vp).SkPrf (shakeCore vp).Y)
    (w : Bytes vp.params.m) :
    (shakeEncoding vp hn hnm pkSeed).trunc (.inr q) w = prefixBytes vp.params.n w :=
  rfl

/-- **The encoding translates the three-oracle scheme as `encImpl` does.** -/
theorem encodeImpl_shakeEncoding_compose_liftTypedImpl :
    (shakeEncoding vp hn hnm pkSeed).encodeImpl ∘ₛ liftTypedImpl = encImpl vp := by
  funext u
  rcases u with k | ((⟨_, _, _⟩ | ⟨_, _, _, _⟩) | _)
  · rfl
  · rfl
  · simp only [encImpl]
    rfl
  · rfl

end Encoding

/-! ## The routed adversary -/

section Routed

variable {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
  {pkSeedDist : ProbComp (shakeCore vp).PkSeed}

variable (vp) in
/-- **The routed adversary.** An adversary against `shakeRomScheme`, which queries the single
oracle on byte strings, as an adversary against the three-oracle scheme `romScheme` at the same
`opt_rand` source and public-seed distribution: at its public key `pk` it reads each raw string by
the router of `shakeEncoding vp hn hnm pk.pkSeed`, answering the typed query it is read as from the
typed oracles and completing the answer to `m` bytes with a private value of the string, from a
table it holds in its own state, initially empty. -/
@[expose] noncomputable def routeAdv (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand pkSeedDist)) :
    UnforgeableAdversary (romScheme (shakeCore vp) (Equiv.refl _) optRand pkSeedDist) :=
  (adv.mapOracles liftRawImpl (sigAlg' := (romScheme (shakeCore vp) (Equiv.refl _) optRand
      pkSeedDist).map (simulateQ' liftTypedImpl))).route
    (fun pk => (shakeEncoding vp hn hnm pk.pkSeed).tableRouter) ∅

/-- **The budget of the routed adversary.** It makes at most as many typed hash queries as the
adversary makes queries of the single oracle, and as many signing queries. -/
theorem romQueryBound_routeAdv (hn : vp.params.n ≤ 32)
    (hnm : vp.params.n ≤ vp.params.m)
    {adv : UnforgeableAdversary (shakeRomScheme vp optRand pkSeedDist)} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) : (routeAdv vp hn hnm adv).RomQueryBound qh qs :=
  RandomOracleEncoding.romQueryBound_route_tableRouter hadv ∅

end Routed

/-! ## The bound at a fixed public seed -/

section Bound

variable {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}

/-- The strong advantage against `shakeRomScheme` is the probability that the transcript of its
experiment, run in the random oracle model of the single oracle from the empty cache, wins
strongly. -/
theorem shakeStrongAdvantage_eq {pkSeedDist : ProbComp (shakeCore vp).PkSeed}
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand pkSeedDist)) :
    shakeStrongAdvantage vp adv = Pr{let z ← (simulateQ (shakeSpec vp).romImpl
      (unforgeableTranscriptExperiment adv.toUnforgeableAdversary)).run ∅}[
        z.1.strongWins = true] := by
  rw [prEvent_eq_evalDist_decide, shakeStrongAdvantage_def, strongUnforgeableAdvantage,
    ProbCompRuntime.rom_evalDist, ← map_strongWins_unforgeableTranscriptExperiment]
  congr 1
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, bind_pure_comp,
    Bool.decide_eq_true]

/-- **SLH-DSA over one SHAKE256 oracle, routed.** At a fixed public seed, the strong forging
advantage of an adversary against `shakeRomScheme` is at most the probability that, in the run of
the three-oracle scheme against the routed adversary, the transcript wins strongly or two distinct
cached typed queries have the same SHAKE256 input string (`RandomOracleEncoding.Clash`). -/
theorem shakeStrongAdvantage_pure_le (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (pkSeed : (shakeCore vp).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) :
    shakeStrongAdvantage vp adv ≤
      Pr{let z ← romSchemeRun (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)
          (routeAdv vp hn hnm adv.toUnforgeableAdversary)}[
        z.1.strongWins = true ∨ (shakeEncoding vp hn hnm pkSeed).Clash z.2] := by
  have hE : ∀ z ∈ support (romScheme (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)).keygen,
      shakeEncoding vp hn hnm z.1.pkSeed = shakeEncoding vp hn hnm pkSeed := fun _ hz =>
    congrArg (shakeEncoding vp hn hnm) (pkSeed_eq_of_mem_support_romScheme_keygen _ _ hz)
  have h := fun a : UnforgeableAdversary ((romScheme (shakeCore vp) (Equiv.refl _) optRand
      (pure pkSeed)).map (simulateQ' ((shakeEncoding vp hn hnm pkSeed).encodeImpl ∘ₛ
        liftTypedImpl))) =>
    RandomOracleEncoding.prEvent_simulateQ_romImpl_run_unforgeableTranscriptExperiment_le
      (shakeEncoding vp hn hnm pkSeed) a
      (Ek := fun pk : PublicKeyCore (shakeCore vp) => shakeEncoding vp hn hnm pk.pkSeed) hE
      (fun o => o.strongWins = true)
  rw [encodeImpl_shakeEncoding_compose_liftTypedImpl] at h
  rw [shakeStrongAdvantage_eq]
  exact h adv.toUnforgeableAdversary

end Bound

end SLHDSA.Security
