/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ComponentTraces
public import HashSig.SLHDSA.Security.NodeGraph

/-!
# The key discipline at the FIPS SHA-2 bundles

`CorePrimitives.KeySeparated` quantifies over every address, in range or not. The FIPS SHA-2 key
`Concrete.sha2AdrsKey` sends an address outside the checked `ADRSc` domain to the type-tagged
`Concrete.sha2FallbackKey`. A `WOTS_PRF` address at layer `300`, whose layer does not fit `ADRSc`'s
one-byte layer field, is such an address: its key is the fallback key of a secret-key type
(`sha2AdrsKey_wotsPrf_layer300`), which is neither the all-zero key nor the key of the all-zero
address, of type `0` (`sha2AdrsKey_wotsPrf_layer300_ne_zero`). The fallback key of a type at
most `4` carries `7` at the type byte instead (`sha2FallbackKey_zero_toList`).

No honest input reaches the fallback. Every tweak in the encoded union ledger at FIPS SHA-2 is the
checked `ADRSc` of a ledger address (`compressSha2Checked_eq_ok_of_constructionQueryReachable`),
and the trace theorems of `SLHDSA.Security.ComponentTraces` place every `thash` query of honest key
generation, signing and verification in that ledger, for every oracle answer and every presented
signature.

The statements below also pin the resulting discharges: key separation at every FIPS SHA-2
bundle, and the key discipline at every FIPS 205 parameter set, at the limited SHA2-128-24 profile
and at the compatibility bundle. At every FIPS 205 parameter set an honest entry exists.

## The address encoding is not injective at any shipped bundle

`CorePrimitives.KeyInjective` asks for injectivity of `core.adrsToKey` on the in-range addresses
only, because no shipped bundle is injective on all of `Adrs`. Each of its six natural-number
fields is written into a fixed number of bytes, four for the leaf index, so `⟨0, 0, 3, 0, 0, 0⟩`
and `⟨0, 0, 3, 0, 0, 2 ^ 32⟩`, two FORS leaf addresses of one tree differing only in the leaf
index, have the same 32-byte serialization (`toBytes_collision`) and the same 22-byte `ADRSc`
compression (`compressSha2_collision`). The FIPS SHA-2 key `Concrete.sha2AdrsKey` routes
through the checked compression instead and maps every rejected address of one type class to
one fallback key (`sha2AdrsKey_toList_collision`).
Hence `not_injective_adrsToKey_shake`, `not_injective_adrsToKey_sha` and
`not_injective_adrsToKey_sha2`, stated at the field each bundle installs.
-/

public section

namespace SLHDSA.KeyDisciplineTest

open Concrete Security

/-- A `WOTS_PRF` address whose layer does not fit the one-byte `ADRSc` layer field. -/
def wotsPrfLayer300 : Adrs := { wotsSkAdrs Adrs.zero 0 with layer := 300 }

/-- The checked compression rejects it. -/
theorem compressSha2Checked_wotsPrfLayer300 :
    wotsPrfLayer300.compressSha2Checked = .error (.outOfRange 1 300) := by rfl

/-- Its SHA-2 key is the fallback key of a secret-key type: the all-zero string with `8` at the type
byte. -/
theorem sha2AdrsKey_wotsPrf_layer300 :
    sha2AdrsKey wotsPrfLayer300 = sha2FallbackKey 5 ∧
      (sha2FallbackKey 5).toList = List.replicate 9 0 ++ [8] ++ List.replicate 12 0 :=
  ⟨sha2AdrsKey_eq_sha2FallbackKey_of_compressSha2Checked_eq_error
    compressSha2Checked_wotsPrfLayer300, by decide⟩

/-- Its SHA-2 key is neither the all-zero key nor the key of the all-zero address. -/
theorem sha2AdrsKey_wotsPrf_layer300_ne_zero :
    sha2AdrsKey wotsPrfLayer300 ≠ zeroBytes 22 ∧
      sha2AdrsKey wotsPrfLayer300 ≠ sha2AdrsKey Adrs.zero := by
  rw [sha2AdrsKey_wotsPrf_layer300.1]
  exact ⟨fun h => absurd (congrArg Vector.toList h) (by decide),
    sha2AdrsKey_eq_compressed Adrs.zero (by decide) (by decide) (by decide) ▸
      fun h => absurd (congrArg Vector.toList h) (by decide)⟩

/-- The fallback key of a type at most `4` is the all-zero string with `7` at the type byte. -/
theorem sha2FallbackKey_zero_toList :
    (sha2FallbackKey 0).toList = List.replicate 9 0 ++ [7] ++ List.replicate 12 0 := by decide

/-- Under the compressed `ADRSc` widths, the tweak of every construction-reachable `thash` query at
FIPS SHA-2 is the checked `ADRSc` of a ledger address. -/
theorem compressSha2Checked_eq_ok_of_constructionQueryReachable {vp : ValidatedParams}
    (hb : ApprovedAddressBounds vp.params) {pkSeed : (sha2Primitives vp.params).core.PkSeed}
    {adrsKey : (sha2Primitives vp.params).core.AdrsKey}
    {xs : List (sha2Primitives vp.params).core.Y}
    (h : ConstructionQueryReachable vp (sha2Primitives vp.params).core
      (.thash pkSeed adrsKey xs)) :
    ∃ a ∈ constructionAddresses vp, a.compressSha2Checked = .ok adrsKey := by
  obtain ⟨a, ha, rfl⟩ := (mem_encodedConstructionAddresses_iff _ adrsKey).1
    ((constructionQueryReachable_thash_iff _ pkSeed adrsKey xs).1 h)
  exact ⟨a, ha, compressSha2Checked_eq_ok_sha2AdrsKey_of_addressFacts hb
    (addressFacts_of_mem_constructionAddresses hb.toCanonicalAddressBounds ha)⟩

/-- Every query of honest signing at FIPS SHA-2 is construction-reachable. -/
example (vp : ValidatedParams) (msg : List Byte)
    (sk : SecretKeyCore (sha2Primitives vp.params).core)
    (addrnd : (sha2Primitives vp.params).core.Y) :
    QueriesWithinConstructionTargets (sha2Primitives vp.params).core
      (GeneralScheme.signInternalM vp (sha2Primitives vp.params).core msg sk addrnd :
        OracleComp (publicHashSpec (sha2Primitives vp.params).core) _) :=
  signInternalM_queriesWithinConstructionTargets _ msg sk addrnd

/-- Every query of honest key generation at FIPS SHA-2 is construction-reachable. -/
example (vp : ValidatedParams) (skSeed : (sha2Primitives vp.params).core.SkSeed)
    (skPrf : (sha2Primitives vp.params).core.SkPrf)
    (pkSeed : (sha2Primitives vp.params).core.PkSeed) :
    QueriesWithinConstructionTargets (sha2Primitives vp.params).core
      (GeneralScheme.keygenInternalM vp (sha2Primitives vp.params).core skSeed skPrf pkSeed :
        OracleComp (publicHashSpec (sha2Primitives vp.params).core) _) :=
  keygenInternalM_queriesWithinConstructionTargets _ skSeed skPrf pkSeed

/-- Every query of verification at FIPS SHA-2 is construction-reachable, whatever signature is
presented. -/
example (vp : ValidatedParams) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp (sha2Primitives vp.params).core)
    (pk : PublicKeyCore (sha2Primitives vp.params).core) :
    QueriesWithinConstructionTargets (sha2Primitives vp.params).core
      (GeneralScheme.verifyInternalM vp (sha2Primitives vp.params).core msg sig pk :
        OracleComp (publicHashSpec (sha2Primitives vp.params).core) Bool) :=
  verifyInternalM_queriesWithinConstructionTargets _ msg sig pk

/-- Secret-key addresses at reachable positions are keyed injectively at every FIPS 205
parameter set. -/
example (ps : FipsParameterSet) (pos pos' : LayerPosition ps.validatedParams)
    (i i' : Fin ps.validatedParams.params.len)
    (h : (approvedPrimitives ps).core.adrsToKey (wotsSkAdrs (wotsInstanceAdrs pos) i.val) =
      (approvedPrimitives ps).core.adrsToKey (wotsSkAdrs (wotsInstanceAdrs pos') i'.val)) :
    wotsSkAdrs (wotsInstanceAdrs pos) i.val = wotsSkAdrs (wotsInstanceAdrs pos') i'.val :=
  keyInjective_approvedPrimitives ps
    (addressFacts_wotsSkAdrs (fipsApprovedAddressBounds ps).toCanonicalAddressBounds pos i)
    (addressFacts_wotsSkAdrs (fipsApprovedAddressBounds ps).toCanonicalAddressBounds pos' i') h

/-- Every FIPS SHA-2 bundle is key-separated. -/
example (p : Params) : (sha2Primitives p).core.KeySeparated := keySeparated_sha2Primitives p

/-- Every FIPS 205 parameter set's approved bundle satisfies the key discipline. -/
example (ps : FipsParameterSet) :
    (approvedPrimitives ps).core.KeyDiscipline ps.validatedParams :=
  keyDiscipline_approvedPrimitives ps

/-- The FIPS SHA-2 bundle at the limited SHA2-128-24 profile satisfies the key discipline. -/
example : (sha2Primitives slhdsaSha2_128_24).core.KeyDiscipline
    (LimitedParameterSet.validatedParams .SLHDSA_SHA2_128_24) :=
  keyDiscipline_limited .SLHDSA_SHA2_128_24

/-- The compatibility bundle satisfies the key discipline. -/
example : shaPrimitives.core.KeyDiscipline
    (LimitedParameterSet.validatedParams .SLHDSA_SHA2_128_24) :=
  keyDiscipline_shaPrimitives

/-- At every FIPS 205 parameter set an honest entry exists: a FORS leaf of the first tree at the
first bottom position, over a provider that returns `y` everywhere, for every cache. -/
example (ps : FipsParameterSet) (c : PublicHash.Cache (approvedPrimitives ps).core)
    (pk : (approvedPrimitives ps).core.PkSeed) (y : (approvedPrimitives ps).core.Y) :
    let pos : BottomPosition ps.validatedParams := ⟨⟨0, by positivity⟩, ⟨0, by positivity⟩⟩
    HonestEntry (vp := ps.validatedParams) (fun _ => pure y) pk c
      (.thash pk ((approvedPrimitives ps).core.adrsToKey (forsNodeAdrs pos.forsAdrs 0 0)) [y]) :=
  .forsLeaf _ 0 y
    (forsLeafAdrs_mem_constructionAddresses _ ⟨0, ps.validatedParams.valid.k_pos⟩
      (Nat.zero_div _))
    (by rw [simulateQ_pure]; rfl)

/-! ## The address encoding is not injective at any shipped bundle -/

/-- Two FORS leaf addresses differing only by `2 ^ 32` in the leaf index have the same 32-byte
serialization. -/
theorem toBytes_collision :
    Adrs.toBytes ⟨0, 0, 3, 0, 0, 0⟩ = Adrs.toBytes ⟨0, 0, 3, 0, 0, 2 ^ 32⟩ := by decide

/-- The same two addresses have the same 22-byte `ADRSc` compression. -/
theorem compressSha2_collision :
    Adrs.compressSha2 ⟨0, 0, 3, 0, 0, 0⟩ = Adrs.compressSha2 ⟨0, 0, 3, 0, 0, 2 ^ 32⟩ := by decide

/-- The FIPS SHA-2 tweak map sends two FORS leaf addresses the checked compression rejects to one
fallback key. -/
theorem sha2AdrsKey_toList_collision : (sha2AdrsKey ⟨0, 0, 3, 0, 0, 2 ^ 32⟩).toList =
    (sha2AdrsKey ⟨0, 0, 3, 0, 0, 2 ^ 32 + 1⟩).toList := by decide

/-- The tweak map the SHAKE bundle installs is not injective. -/
theorem not_injective_adrsToKey_shake (p : Params) :
    ¬ Function.Injective (shakePrimitives p).adrsToKey := fun h =>
  absurd (h (show Adrs.toVector _ = Adrs.toVector _ from
    Vector.toList_inj.mp (by simpa [Adrs.toVector] using toBytes_collision))) (by decide)

/-- The tweak map the compatibility bundle installs is not injective. -/
theorem not_injective_adrsToKey_sha : ¬ Function.Injective shaPrimitives.adrsToKey := fun h =>
  absurd (h (show shaAdrsKey _ = shaAdrsKey _ from
    Vector.toList_inj.mp (by simpa using compressSha2_collision))) (by decide)

/-- The tweak map the FIPS SHA-2 bundle installs is not injective. -/
theorem not_injective_adrsToKey_sha2 (p : Params) :
    ¬ Function.Injective (sha2Primitives p).adrsToKey := fun h =>
  absurd (h (show sha2AdrsKey _ = sha2AdrsKey _ from
    Vector.toList_inj.mp sha2AdrsKey_toList_collision)) (by decide)

end SLHDSA.KeyDisciplineTest
