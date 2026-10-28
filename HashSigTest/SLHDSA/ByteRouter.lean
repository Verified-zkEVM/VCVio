/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteRouter
public import HashSig.SLHDSA.Security.ByteConformance

/-!
# The SHAKE256 router, checked

`HashSig.SLHDSA.Security.ByteRouter` reads byte strings as queries of the three SLH-DSA oracles
and routes an adversary against the single-oracle scheme `shakeRomScheme` into one against
`romScheme`. This file checks it at the parameters of FIPS 205.

* **The encoding and the bound at all 12 FIPS 205 parameter sets** (`FipsParameterSet`, whose
  SHA-2 sets share their parameters with the SHAKE sets), with the side conditions `n ≤ 32` and
  `n ≤ m` discharged: the encoding, its agreement with `encImpl`, the routed adversary's budget,
  the per-seed bound `shakeStrongAdvantage_pure_le`, and route-fixedness at the honest keys of every
  node of the SLH-DSA graph.
* **Each rule at SLH-DSA-SHAKE-128s** on concrete strings, with the address-key predicate
  everywhere true or everywhere false. Which rule fires is decided by evaluation; the query read
  then follows from the router's equations. An `F` string is read as the tweakable-hash query it
  lays out when its key is admitted (rule 1) and as a `PRF_msg` query otherwise (rule 3); an
  `H_msg` string with `R ≠ PK.seed` is read as its `H_msg` query (rule 2), while one with
  `R = PK.seed` and no message is also a tweakable-hash string at `PK.seed` and fires rule 1 when
  its key is admitted; a string of `2n - 1` bytes is read as no query (rule 4).
* **Route-fixedness** of honest queries from the lemmas, with the honest-key decidability
  instance found without opening `Classical`.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.ByteRouterTest

open Concrete Security

/-- SLH-DSA-SHAKE-128s. -/
abbrev vp128s : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_128s

/-! ## At all 12 FIPS 205 parameter sets -/

/-- The encoding exists at all 12 FIPS 205 parameter sets and every public seed. -/
noncomputable example (set : FipsParameterSet) (pkSeed : (shakeCore set.validatedParams).PkSeed) :
    RandomOracleEncoding (hashSpec (shakeCore set.validatedParams)) (List Byte)
      (Bytes set.validatedParams.params.m) :=
  shakeEncoding _ set.n_le_32 set.n_le_m pkSeed

/-- It translates the three-oracle scheme as `encImpl` does. -/
example (set : FipsParameterSet) (pkSeed : (shakeCore set.validatedParams).PkSeed) :
    (shakeEncoding _ set.n_le_32 set.n_le_m pkSeed).encodeImpl ∘ₛ liftTypedImpl =
      encImpl set.validatedParams :=
  encodeImpl_shakeEncoding_compose_liftTypedImpl _ _ _

/-- The routed adversary keeps the budget. -/
example (set : FipsParameterSet)
    {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    {pkSeedDist : ProbComp (shakeCore set.validatedParams).PkSeed}
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams optRand pkSeedDist))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    (routeAdv set.validatedParams set.n_le_32 set.n_le_m adv).RomQueryBound qh qs :=
  romQueryBound_routeAdv set.n_le_32 set.n_le_m hadv

/-- The per-seed bound at all 12 FIPS 205 parameter sets, both signing modes. -/
example (set : FipsParameterSet)
    (optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y)
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme set.validatedParams optRand (pure pkSeed))) :
    shakeStrongAdvantage _ adv ≤
      Pr{let z ← romSchemeRun (shakeCore set.validatedParams) (Equiv.refl _) optRand
          (pure pkSeed) (routeAdv _ set.n_le_32 set.n_le_m adv.toUnforgeableAdversary)}[
        z.1.strongWins = true ∨ (shakeEncoding _ set.n_le_32 set.n_le_m pkSeed).Clash z.2] :=
  shakeStrongAdvantage_pure_le set.n_le_32 set.n_le_m pkSeed adv

/-- At the honest keys, the tweakable-hash query at the key of every node of the SLH-DSA graph is
route-fixed in the encoding. -/
example (set : FipsParameterSet) (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (κ : NodeKey (shakeCore set.validatedParams)) (xs : List (shakeCore set.validatedParams).Y) :
    (shakeEncoding _ set.n_le_32 set.n_le_m pkSeed).route
        (encode _ (.inl (.thash pkSeed κ.1 xs))) = some (.inl (.thash pkSeed κ.1 xs)) :=
  shakeEncoding_route_encode_thash set.n_le_32 set.n_le_m pkSeed (isHonestKey_nodeKey κ) xs

/-! ## Each rule at SLH-DSA-SHAKE-128s -/

/-- A public seed. -/
def seed : (shakeCore vp128s).PkSeed :=
  (⟨#[3, 10, 17, 24, 31, 38, 45, 52, 59, 66, 73, 80, 87, 94, 101, 108], rfl⟩ : Bytes 16)

/-- A node. -/
def node : (shakeCore vp128s).Y :=
  (⟨#[1, 14, 27, 40, 53, 66, 79, 92, 105, 118, 131, 144, 157, 170, 183, 196], rfl⟩ : Bytes 16)

/-- A root. -/
def root : (shakeCore vp128s).Y :=
  (⟨#[11, 16, 21, 26, 31, 36, 41, 46, 51, 56, 61, 66, 71, 76, 81, 86], rfl⟩ : Bytes 16)

/-- An address key: layer `2`, tree `5`, the remaining words zero. -/
def key : (shakeCore vp128s).AdrsKey :=
  (⟨#[0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0], rfl⟩ : Bytes 32)

/-- Every address key admitted. -/
abbrev admitAll : (shakeCore vp128s).AdrsKey → Prop := fun _ => True

/-- No address key admitted. -/
abbrev admitNone : (shakeCore vp128s).AdrsKey → Prop := fun _ => False

/-- An `F` string `PK.seed ‖ ADRS ‖ M_1` at the public seed. -/
abbrev fString : List Byte := encode vp128s (.inl (.thash seed key [node]))

/-- Rule 1 fires on the `F` string when its key is admitted. -/
example : IsThashString vp128s admitAll seed fString := by decide

/-- Rule 1 does not fire on the `F` string when its key is not admitted, and rule 2 does not fire
either: its second block is not the public seed. -/
example : ¬IsThashString vp128s admitNone seed fString ∧ ¬IsHmsgString vp128s seed fString := by
  decide

/-- Hence the router reads it as its tweakable-hash query when the key is admitted. -/
example : shakeRoute vp128s admitAll seed fString = some (.inl (.thash seed key [node])) :=
  shakeRoute_encode_thash _ _ trivial

/-- Otherwise it reads it as the `PRF_msg` query with `SK.prf = PK.seed` (rule 3). -/
example : shakeRoute vp128s admitNone seed fString =
    some (.inr ⟨skPrfOfList vp128s fString, nodeOfList vp128s (fString.drop 16),
      fString.drop 32⟩) :=
  shakeRoute_of_two_mul_le_length (by decide) (by decide) (by decide)

/-- An `H_msg` string `R ‖ PK.seed ‖ PK.root` with `R ≠ PK.seed` and no message has the length of
a tweakable-hash string with no input block, but does not begin with the public seed: rule 1 does
not fire and rule 2 does. -/
example : ¬IsThashString vp128s admitAll seed (encode vp128s (.inl (.hmsg node seed root []))) ∧
    IsHmsgString vp128s seed (encode vp128s (.inl (.hmsg node seed root []))) := by
  decide

/-- So it is read as its `H_msg` query. -/
example : shakeRoute vp128s admitAll seed (encode vp128s (.inl (.hmsg node seed root []))) =
    some (.inl (.hmsg node seed root [])) :=
  shakeRoute_encode_hmsg _ _ _ (by decide)

/-- With `R = PK.seed`, the same string is a tweakable-hash string at the public seed: rule 1
fires when its key, the first `32` bytes of `PK.seed ‖ PK.root`, is admitted, and the `H_msg` query
is not route-fixed. -/
example : IsThashString vp128s admitAll seed (encode vp128s (.inl (.hmsg seed seed root []))) := by
  decide

/-- It is route-fixed when the key is not admitted. -/
example : shakeRoute vp128s admitNone seed (encode vp128s (.inl (.hmsg seed seed root []))) =
    some (.inl (.hmsg seed seed root [])) :=
  shakeRoute_encode_hmsg _ _ _ (by decide)

/-- Rule 4: a string of `2n - 1` bytes is read as no query. -/
example : shakeRoute vp128s admitAll seed (List.replicate 31 0) = none := by
  decide

/-! ## Route-fixedness from the lemmas -/

/-- Honest tweakable-hash queries are route-fixed, at every input length. -/
example (k : (shakeCore vp128s).AdrsKey) (xs : List (shakeCore vp128s).Y) :
    shakeRoute vp128s admitAll seed (encode vp128s (.inl (.thash seed k xs))) =
      some (.inl (.thash seed k xs)) :=
  shakeRoute_encode_thash _ _ trivial

/-- With no key admitted, every `H_msg` query at the public seed is route-fixed. -/
example (r pkRoot : (shakeCore vp128s).Y) (msg : List Byte) :
    shakeRoute vp128s admitNone seed (encode vp128s (.inl (.hmsg r seed pkRoot msg))) =
      some (.inl (.hmsg r seed pkRoot msg)) :=
  shakeRoute_encode_hmsg _ _ _ fun h => h.2.2.2

/-- The honest keys are decidable without opening `Classical`. -/
noncomputable example : DecidablePred (IsHonestKey vp128s (shakeCore vp128s)) := inferInstance

/-- The keys of the nodes of the SLH-DSA graph are honest at the SHAKE bundle. -/
example (κ : NodeKey (shakeCore vp128s)) : IsHonestKey vp128s (shakeCore vp128s) κ.1 :=
  isHonestKey_nodeKey κ

end SLHDSA.ByteRouterTest
