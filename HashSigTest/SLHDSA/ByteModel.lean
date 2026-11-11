/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteConformance
public import HashSig.SLHDSA.Concrete.Codec
public import Lean.Data.Json.Parser

/-!
# SLH-DSA over a single SHAKE256 oracle, checked

`HashSig.SLHDSA.Security.ByteModel` states SLH-DSA over one random oracle on byte strings, and
`HashSig.SLHDSA.Security.ByteConformance` identifies it, with the oracle answered by SHAKE256,
with FIPS 205's SHAKE internal algorithms. This file checks both at concrete parameter sets.

* **Conformance at the shipped sets, both signing modes.** At SLH-DSA-SHAKE-128s with
  deterministic signing (`opt_rand = PK.seed`) and at SLH-DSA-SHAKE-256f with hedged signing
  (`opt_rand` uniform), the single-oracle scheme answered by SHAKE256 is `internalAlg` at the
  SHAKE bundle; key generation, signing and verification are restated one by one.
* **The per-role equations evaluate**, in the `slhdsa_byte_model_tests` executable. At 128s the
  `n`-byte prefix of the SHAKE256 answer at the tweakable-hash and `PRF_msg` layouts, and the
  whole answer at the `H_msg` layout (with `R ≠ PK.root`), equal the landed `shakeThash`,
  `shakePRFmsg` and `shakeHmsg` on concrete inputs; the same answer at a layout with `PK.seed` and
  `ADRS` swapped, or with `R` and `PK.root` swapped, does not (negative controls). Prefix
  consistency evaluates at the 256s widths `n = 32`, `m = 47`.
* **The right-hand side of conformance against NIST vectors**, in the same executable. At
  SLH-DSA-SHAKE-128f, `GeneralScheme.keygenInternal`, `signInternal` and `verifyInternal` at the
  SHAKE bundle reproduce five NIST ACVP-Server SLH-DSA sample vectors (commit `975de31e`), stored
  with their provenance in `ByteModelVectors/vectors.json`: keyGen test case 31 (public and secret
  key), internal-interface sigGen test cases 137 (deterministic, `addrnd = PK.seed`) and 448
  (hedged, `addrnd` the vector's additional randomness), and internal-interface sigVer test cases
  223 (accepted) and 219 (rejected, a full-length signature that decodes). A perturbed `SK.seed`
  is a negative control for key generation. The same checks also run five independent records
  each at SHAKE-192f and SHAKE-256f: keyGen 71/111; deterministic sigGen 148/154;
  hedged sigGen 461/462; and valid/invalid sigVer 232/225 and 239/241.
* **The oracle does not separate roles.** A tweakable-hash string and a `PRF_msg` string can be the
  same bytes, so the two queries are one oracle point (`encode_thash_eq_encode_prfMsg`): the model
  is a single function, as FIPS 205's SHAKE instantiation is, unlike the three-oracle model of
  `HashSig.SLHDSA.Security.Target`.
* **Layout shapes**: the `F`, `H_msg` and `PRF_msg` strings at 128s have `64`, `48 + |M|` and
  `32 + |M|` bytes; every encoded query at a FIPS 205 parameter set has at least `2n` bytes; zero
  padding of `bytesOfList`.
-/

public section

open OracleComp OracleSpec SignatureAlg VCVio.Algorithms

namespace SLHDSA.ByteModelTest

open Concrete Security

/-- SLH-DSA-SHAKE-128s. -/
abbrev vp128s : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_128s

/-- SLH-DSA-SHAKE-256f. -/
abbrev vp256f : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_256f

/-- Deterministic signing (FIPS 205 Algorithm 19 line 2): `opt_rand = PK.seed`. -/
def deterministicRandomizer (vp : ValidatedParams) :
    PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y :=
  fun pk => pure (shakeRandomizerOfPkSeed vp.params pk.pkSeed)

/-- Hedged signing: `opt_rand` uniform. -/
noncomputable def hedgedRandomizer (vp : ValidatedParams) :
    PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y :=
  fun _ => $ᵗ (shakeCore vp).Y

/-! ## Conformance at the shipped sets -/

/-- Deterministic SLH-DSA-SHAKE-128s over the single oracle, answered by SHAKE256, is FIPS 205. -/
example :
    (shakeRomScheme vp128s (deterministicRandomizer vp128s) ($ᵗ (shakeCore vp128s).PkSeed)).map
        (simulateQ' (unifFwdAnswerImpl (shakeAnswer vp128s))) =
      internalAlg vp128s (shakePrimitives vp128s.params) (deterministicRandomizer vp128s)
        ($ᵗ (shakeCore vp128s).PkSeed) :=
  shakeRomScheme_map_shakeAnswer_validatedParams .SLHDSA_SHAKE_128s _ _

/-- Hedged SLH-DSA-SHAKE-256f over the single oracle, answered by SHAKE256, is FIPS 205. -/
example :
    (shakeRomScheme vp256f (hedgedRandomizer vp256f) ($ᵗ (shakeCore vp256f).PkSeed)).map
        (simulateQ' (unifFwdAnswerImpl (shakeAnswer vp256f))) =
      internalAlg vp256f (shakePrimitives vp256f.params) (hedgedRandomizer vp256f)
        ($ᵗ (shakeCore vp256f).PkSeed) :=
  shakeRomScheme_map_shakeAnswer_validatedParams .SLHDSA_SHAKE_256f _ _

section Components

variable (pkSeedDist : ProbComp (shakeCore vp128s).PkSeed)

private theorem conformance128s :
    (shakeRomScheme vp128s (deterministicRandomizer vp128s) pkSeedDist).map
        (simulateQ' (unifFwdAnswerImpl (shakeAnswer vp128s))) =
      internalAlg vp128s (shakePrimitives vp128s.params) (deterministicRandomizer vp128s)
        pkSeedDist :=
  shakeRomScheme_map_shakeAnswer_validatedParams .SLHDSA_SHAKE_128s _ _

/-- Key generation answered by SHAKE256 is `slh_keygen_internal` at freshly drawn seeds. -/
example :
    simulateQ (unifFwdAnswerImpl (shakeAnswer vp128s))
        (shakeRomScheme vp128s (deterministicRandomizer vp128s) pkSeedDist).keygen =
      (do
        let pkSeed ← pkSeedDist
        let skSeed ← $ᵗ (shakePrimitives vp128s.params).SkSeed
        let skPrf ← $ᵗ (shakePrimitives vp128s.params).SkPrf
        pure (GeneralScheme.keygenInternal vp128s (shakePrimitives vp128s.params) skSeed skPrf
          pkSeed)) :=
  congrArg SignatureAlg.keygen (conformance128s pkSeedDist)

/-- Deterministic signing answered by SHAKE256 is `slh_sign_internal` at `opt_rand = PK.seed`. -/
example (pk : PublicKeyCore (shakeCore vp128s)) (sk : SecretKeyCore (shakeCore vp128s))
    (msg : List Byte) :
    simulateQ (unifFwdAnswerImpl (shakeAnswer vp128s))
        ((shakeRomScheme vp128s (deterministicRandomizer vp128s) pkSeedDist).sign pk sk msg) =
      pure (GeneralScheme.signInternal vp128s (shakePrimitives vp128s.params) msg sk
        pk.pkSeed) := by
  refine (congrArg (fun A => A.sign pk sk msg) (conformance128s pkSeedDist)).trans ?_
  simp only [internalAlg, deterministicRandomizer, shakeRandomizerOfPkSeed, id]
  rfl

/-- Verification answered by SHAKE256 is `slh_verify_internal`. -/
example (pk : PublicKeyCore (shakeCore vp128s)) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp128s (shakeCore vp128s)) :
    simulateQ (unifFwdAnswerImpl (shakeAnswer vp128s))
        ((shakeRomScheme vp128s (deterministicRandomizer vp128s) pkSeedDist).verify pk msg sig) =
      pure (GeneralScheme.verifyInternal vp128s (shakePrimitives vp128s.params) msg sig pk) :=
  congrArg (fun A => A.verify pk msg sig) (conformance128s pkSeedDist)

end Components

/-! ## The per-role equations, evaluated -/

/-- A fixed 16-byte value. -/
def seed16 : Bytes 16 := Vector.ofFn fun i => (i.val * 7 + 3).toUInt8

/-- A second fixed 16-byte value. -/
def node16 : Bytes 16 := Vector.ofFn fun i => (i.val * 13 + 1).toUInt8

/-- A third fixed 16-byte value. -/
def root16 : Bytes 16 := Vector.ofFn fun i => (i.val * 5 + 11).toUInt8

/-- A WOTS+ hash address. -/
def adrs : Adrs := ((Adrs.zero.setLayerAddress 2).setTreeAddress 5).setTypeAndClear .wotsHash

def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"byte-model check failed: {label}")

/-- The SHAKE256 answer at each layout, read at the role's width, against the landed SHAKE
function of that role, with a layout-order negative control and prefix consistency. -/
def checkRoles : IO Unit := do
  ensure "F at 128s is shakeThash"
    (prefixBytes 16 (shakeAnswer vp128s (encode vp128s (.inl (.thash seed16 adrs.toVector
      [node16])))) == shakeThash vp128s.params seed16 adrs.toVector [node16])
  ensure "H_msg at 128s is shakeHmsg"
    (shakeHmsg vp128s.params node16 seed16 node16 [1, 2, 3] ==
      shakeAnswer vp128s (encode vp128s (.inl (.hmsg node16 seed16 node16 [1, 2, 3]))))
  ensure "H_msg at 128s is shakeHmsg, R ≠ PK.root"
    (shakeHmsg vp128s.params node16 seed16 root16 [1, 2, 3] ==
      shakeAnswer vp128s (encode vp128s (.inl (.hmsg node16 seed16 root16 [1, 2, 3]))))
  ensure "R and PK.root swapped is not H_msg"
    (shakeHmsg vp128s.params node16 seed16 root16 [1, 2, 3] !=
      shakeAnswer vp128s (encode vp128s (.inl (.hmsg root16 seed16 node16 [1, 2, 3]))))
  ensure "PRF_msg at 128s is shakePRFmsg"
    (prefixBytes 16 (shakeAnswer vp128s (encode vp128s (.inr ⟨node16, seed16, [9, 8]⟩))) ==
      shakePRFmsg node16 seed16 [9, 8])
  ensure "ADRS before PK.seed is not F"
    (prefixBytes 16 (shakeAnswer vp128s (adrs.toBytes ++ seed16.toList ++ node16.toList)) !=
      shakeThash vp128s.params seed16 adrs.toVector [node16])
  ensure "PRF is the tweakable hash at the PRF address"
    (shakeThash vp128s.params seed16 (adrs.setTypeAndClear .wotsPrf).toVector [node16] ==
      shakePRF seed16 node16 (adrs.setTypeAndClear .wotsPrf))
  ensure "SHAKE256 prefix consistency at n = 32, m = 47"
    ((Keccak.shake256 (seed16.toList ++ adrs.toBytes).toByteArray 47).data.toList.take 32 ==
      (Keccak.shake256 (seed16.toList ++ adrs.toBytes).toByteArray 32).data.toList)
  ensure "zero padding" (bytesOfList 4 [1, 2] == #v[1, 2, 0, 0])
  ensure "truncation" (bytesOfList 2 [1, 2, 3] == #v[1, 2])

/-- Prefix consistency at zero length and across exact and partial SHAKE rate boundaries. -/
def checkMultiBlockPrefixes : IO Unit := do
  let input : ByteArray := ByteArray.mk #[0, 1, 2, 3]
  for (short, long) in [(0, 0), (0, 137), (135, 136), (136, 137), (137, 272), (272, 300)] do
    ensure s!"SHAKE256 prefix {short}/{long}"
      ((Keccak.shake256 input long).data.toList.take short ==
        (Keccak.shake256 input short).data.toList)
    ensure s!"SHAKE128 prefix {short}/{long}"
      ((Keccak.shake128 input long).data.toList.take short ==
        (Keccak.shake128 input short).data.toList)

/-! ## NIST ACVP vectors at SLH-DSA-SHAKE-128f -/

/-- SLH-DSA-SHAKE-128f. -/
abbrev vp128f : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_128f

/-- The value of a hexadecimal digit. -/
def hexValue (c : Char) : ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- The bytes of a hexadecimal string. -/
def parseHex (hex : String) : List Byte :=
  let cs := hex.toList.toArray
  (List.range (cs.size / 2)).map fun i =>
    (hexValue cs[2 * i]! * 16 + hexValue cs[2 * i + 1]!).toUInt8

/-- The field `key` of a fixture record. -/
def field (α : Type) [Lean.FromJson α] (record : Lean.Json) (key : String) : IO α :=
  match record.getObjValAs? α key with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"ACVP fixture: field {key}: {error}")

/-- The hexadecimal field `key` of a fixture record, as bytes. -/
def hexField (record : Lean.Json) (key : String) : IO (List Byte) :=
  parseHex <$> field String record key

/-- ACVP keyGen: `slh_keygen_internal` at the record's seeds gives its public and secret keys. -/
def checkKeyGen (vp : ValidatedParams) (record : Lean.Json) : IO Unit := do
  let n := vp.params.n
  let tcId ← field ℕ record "tcId"
  let skSeed ← hexField record "skSeed"
  let skPrf ← hexField record "skPrf"
  let pkSeed ← hexField record "pkSeed"
  ensure s!"keyGen tcId {tcId}: seed widths"
    (skSeed.length == n && skPrf.length == n && pkSeed.length == n)
  let (pk, sk) := GeneralScheme.keygenInternal vp (shakePrimitives vp.params)
    (bytesOfList n skSeed) (bytesOfList n skPrf) (bytesOfList n pkSeed)
  ensure s!"keyGen tcId {tcId}: pk"
    (encodePublicKey (shakeWireCodec vp.params) pk == (← hexField record "pk"))
  ensure s!"keyGen tcId {tcId}: sk"
    (encodeSecretKey (shakeWireCodec vp.params) sk == (← hexField record "sk"))
  -- negative control: a different `SK.seed` gives a different `PK.root`
  let (pk', _) := GeneralScheme.keygenInternal vp (shakePrimitives vp.params)
    (bytesOfList n (skSeed.modifyHead (· ^^^ 1))) (bytesOfList n skPrf) (bytesOfList n pkSeed)
  ensure s!"keyGen tcId {tcId}: perturbed SK.seed is rejected"
    (encodePublicKey (shakeWireCodec vp.params) pk' != (← hexField record "pk"))

/-- ACVP sigGen, internal interface: `slh_sign_internal` gives the record's signature, with
`addrnd = PK.seed` for a deterministic record and the record's additional randomness otherwise. -/
def checkSigGen (vp : ValidatedParams) (record : Lean.Json) : IO Unit := do
  let tcId ← field ℕ record "tcId"
  let sk ← match decodeSecretKey (shakeWireCodec vp.params) (← hexField record "sk") with
    | .ok sk => pure sk
    | .error _ => throw (IO.userError s!"sigGen tcId {tcId}: secret key does not decode")
  let addrnd ← if ← field Bool record "deterministic" then
      pure (shakeRandomizerOfPkSeed vp.params sk.pkSeed)
    else do
      let bytes ← hexField record "additionalRandomness"
      ensure s!"sigGen tcId {tcId}: randomness width" (bytes.length == vp.params.n)
      pure (bytesOfList vp.params.n bytes)
  let sig := GeneralScheme.signInternal vp (shakePrimitives vp.params)
    (← hexField record "message") sk addrnd
  ensure s!"sigGen tcId {tcId}: signature"
    (encodeSignature vp (shakeWireCodec vp.params) sig == (← hexField record "signature"))

/-- ACVP sigVer, internal interface: `slh_verify_internal` returns the record's verdict. -/
def checkSigVer (vp : ValidatedParams) (record : Lean.Json) : IO Unit := do
  let tcId ← field ℕ record "tcId"
  let pk ← match decodePublicKey (shakeWireCodec vp.params) (← hexField record "pk") with
    | .ok pk => pure pk
    | .error _ => throw (IO.userError s!"sigVer tcId {tcId}: public key does not decode")
  let sig ← match decodeSignature vp (shakeWireCodec vp.params)
      (← hexField record "signature") with
    | .ok sig => pure sig
    | .error _ => throw (IO.userError s!"sigVer tcId {tcId}: signature does not decode")
  ensure s!"sigVer tcId {tcId}: verdict"
    (GeneralScheme.verifyInternal vp (shakePrimitives vp.params)
      (← hexField record "message") sig pk == (← field Bool record "testPassed"))

/-- The pinned ACVP records of `ByteModelVectors/vectors.json`. -/
def checkAcvp : IO Unit := do
  let source ← IO.FS.readFile "HashSigTest/SLHDSA/ByteModelVectors/vectors.json"
  let root ← match Lean.Json.parse source with
    | .ok root => pure root
    | .error error => throw (IO.userError s!"ACVP fixture rejected: {error}")
  ensure "ACVP fixture parameter set"
    ((← field String root "parameterSet") == "SLH-DSA-SHAKE-128f")
  let keyGen ← field (Array Lean.Json) root "keyGen"
  let sigGen ← field (Array Lean.Json) root "sigGen"
  let sigVer ← field (Array Lean.Json) root "sigVer"
  ensure "ACVP fixture keyGen cases" ((← keyGen.mapM (field ℕ · "tcId")) == #[31])
  ensure "ACVP fixture sigGen cases" ((← sigGen.mapM (field ℕ · "tcId")) == #[137, 448])
  ensure "ACVP fixture sigGen modes"
    ((← sigGen.mapM (field Bool · "deterministic")) == #[true, false])
  ensure "ACVP fixture sigVer cases" ((← sigVer.mapM (field ℕ · "tcId")) == #[223, 219])
  ensure "ACVP fixture sigVer verdicts"
    ((← sigVer.mapM (field Bool · "testPassed")) == #[true, false])
  keyGen.forM (checkKeyGen vp128f)
  sigGen.forM (checkSigGen vp128f)
  sigVer.forM (checkSigVer vp128f)

/-- Independent key generation, both signing modes, and valid/invalid verification at a
pinned wider SHAKE parameter set. -/
def checkAcvpWide (set : FipsParameterSet) (width : Nat)
    (keyIds signIds verifyIds : Array Nat) : IO Unit := do
  let source ← IO.FS.readFile s!"HashSigTest/SLHDSA/ByteModelVectors/vectors-{width}f.json"
  let root ← match Lean.Json.parse source with
    | .ok root => pure root
    | .error error => throw (IO.userError s!"ACVP fixture rejected: {error}")
  ensure "ACVP wide parameter set"
    ((← field String root "parameterSet") == s!"SLH-DSA-SHAKE-{width}f")
  let keyGen ← field (Array Lean.Json) root "keyGen"
  let sigGen ← field (Array Lean.Json) root "sigGen"
  let sigVer ← field (Array Lean.Json) root "sigVer"
  ensure "ACVP wide keyGen cases" ((← keyGen.mapM (field Nat · "tcId")) == keyIds)
  ensure "ACVP wide sigGen cases" ((← sigGen.mapM (field Nat · "tcId")) == signIds)
  ensure "ACVP wide sigGen modes" ((← sigGen.mapM (field Bool · "deterministic")) == #[true, false])
  ensure "ACVP wide sigVer cases" ((← sigVer.mapM (field Nat · "tcId")) == verifyIds)
  ensure "ACVP wide sigVer verdicts" ((← sigVer.mapM (field Bool · "testPassed")) == #[true, false])
  keyGen.forM (checkKeyGen set.validatedParams)
  sigGen.forM (checkSigGen set.validatedParams)
  sigVer.forM (checkSigVer set.validatedParams)

/-! ## The oracle does not separate roles -/

/-- At 128s, every tweakable-hash string `PK.seed ‖ ADRS ‖ M_1 ‖ … ‖ M_ℓ` is also the `PRF_msg`
string with `SK.prf = PK.seed`, `opt_rand` the first half of `ADRS` and the message the rest. -/
theorem encode_thash_eq_encode_prfMsg (pkSeed : Bytes vp128s.params.n) (adrsKey : Bytes 32)
    (xs : List (Bytes vp128s.params.n)) :
    encode vp128s (.inl (.thash pkSeed adrsKey xs)) =
      encode vp128s (.inr ⟨pkSeed, bytesOfList vp128s.params.n adrsKey.toList,
        adrsKey.toList.drop vp128s.params.n ++ (xs.map Vector.toList).flatten⟩) := by
  refine (encode_thash vp128s pkSeed adrsKey xs).trans ?_
  change _ = pkSeed.toList ++ (bytesOfList vp128s.params.n adrsKey.toList).toList ++
    (adrsKey.toList.drop vp128s.params.n ++ (xs.map Vector.toList).flatten)
  rw [toList_bytesOfList_of_le (by rw [Vector.length_toList]; decide), List.append_assoc,
    List.append_assoc, ← List.append_assoc (List.take _ _), List.take_append_drop]
  rfl

/-! ## Layout shapes -/

example : (encode vp128s (.inl (.thash seed16 adrs.toVector [node16]))).length = 64 :=
  (length_encode_thash vp128s seed16 adrs.toVector [node16]).trans rfl

example (msg : List Byte) :
    (encode vp128s (.inl (.hmsg node16 seed16 node16 msg))).length = 48 + msg.length :=
  (length_encode_hmsg vp128s node16 seed16 node16 msg).trans rfl

example (msg : List Byte) :
    (encode vp128s (.inr ⟨node16, seed16, msg⟩)).length = 32 + msg.length :=
  (length_encode_prfMsg vp128s ⟨node16, seed16, msg⟩).trans rfl

example : ∀ set ∈ FipsParameterSet.all,
    set.validatedParams.params.n ≤ set.validatedParams.params.m ∧
      set.validatedParams.params.m < 136 ∧ set.validatedParams.params.n ≤ 32 :=
  fun set _ => ⟨set.n_le_m, set.m_lt_136, set.n_le_32⟩

/-- At every FIPS 205 parameter set every encoded query has at least `2n` bytes. -/
example (set : FipsParameterSet) (t : (hashSpec (shakeCore set.validatedParams)).Domain) :
    2 * set.validatedParams.params.n ≤ (encode set.validatedParams t).length :=
  two_mul_le_length_encode _ set.n_le_32 t

def main : IO Unit := do
  checkRoles
  checkMultiBlockPrefixes
  checkAcvp
  checkAcvpWide .SLHDSA_SHAKE_192f 192 #[71] #[148, 461] #[232, 225]
  checkAcvpWide .SLHDSA_SHAKE_256f 256 #[111] #[154, 462] #[239, 241]
  IO.println "SLH-DSA byte-model tests: PASS \
    (SHAKE256 at the F, H_msg and PRF_msg layouts, PRF, prefix consistency, \
    ACVP SHAKE-128f/192f/256f key generation, deterministic and hedged signing, \
    valid and invalid verification)"

end SLHDSA.ByteModelTest

def main : IO Unit := SLHDSA.ByteModelTest.main
