/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.Target
public import HashSig.SLHDSA.Concrete.FIPS
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# SLH-DSA over a single SHAKE256 random oracle

FIPS 205 instantiates every hash function of the SHAKE parameter sets with one function,
SHAKE256, applied to a byte string laid out per role (§11.1). This module states that model: a
single random oracle on byte strings, and SLH-DSA's internal algorithms with every hash evaluation
a query of it at the role's byte layout.

## The oracle

`shakeSpec vp` is a random oracle `List Byte →ₒ Bytes m`, `m` the `H_msg` digest length. A role
whose output is `n` bytes reads the first `n` bytes of the answer (`prefixBytes`). This is
SHAKE256 as an extendable-output random oracle with `m`-byte outputs, `m` being the longest
SHAKE256 output FIPS 205 reads (`H_msg`; every other call reads the first `n ≤ m` bytes), so every
output the scheme itself reads is a prefix of the `m`-byte answer. The output length is a
modelling choice: a forger against a variable-length extendable-output oracle that reads more than
`m` bytes at a string sees only bytes no SLH-DSA evaluation reads, and is simulated against this
oracle, query for query, by sampling those bytes itself; that simulation is not formalised. The
runtime `shakeRuntime vp` is VCVio's lazy random
oracle `ProbCompRuntime.rom (shakeSpec vp)` from the empty cache, the strong forging advantage is
`shakeStrongAdvantage vp`, the existential one `shakeAdvantage vp`, at most the strong one
(`shakeAdvantage_le_shakeStrongAdvantage`), and an adversary's budget is the generic
`RomQueryBound`, one count per query of the single oracle.

## The scheme

`encode vp` writes a query of the three-oracle interface `hashSpec` of
`HashSig.SLHDSA.Security.Target` at its FIPS 205 §11.1 layout:

* the tweakable hash `F`/`H`/`T_ℓ`: `PK.seed ‖ ADRS ‖ M_1 ‖ … ‖ M_ℓ`;
* `H_msg`: `R ‖ PK.seed ‖ PK.root ‖ M`;
* `PRF_msg`: `SK.prf ‖ opt_rand ‖ M`.

`PRF(PK.seed, SK.seed, ADRS)` is the tweakable hash at a `PRF` address applied to `SK.seed`
(`oracleSecret`), so its layout `PK.seed ‖ ADRS ‖ SK.seed` is the tweakable-hash layout
(`encode_oracleSecret`). `encImpl vp` answers each typed query by one query of the single oracle
at its encoding, read at the role's length, and `shakeRomScheme vp optRand pkSeedDist` is
`romScheme` mapped through it: every landed program of the three-oracle scheme, with the secret
seed read as a node by the identity.

## Main statements

* `strongUnforgeableExperiment_shakeRomScheme`, `shakeStrongAdvantage_le_lintegral`: the experiment
  draws the public seed first, so a bound at each public seed averages to a bound at every seed
  distribution.
* `length_encode_thash`, `length_encode_hmsg`, `length_encode_prfMsg`,
  `two_mul_le_length_encode`; the `take_*` and `drop_*` equations reading each field of a layout
  at its offset; and `encode_thash_inj`, `encode_hmsg_inj`, `encode_prfMsg_inj`: the shape of each
  layout and the injectivity of each role.

## Implementation notes

The layout equations take their fields at the carriers of `shakeCore vp` (`PkSeed`, `AdrsKey`,
`Y`, `SkPrf`), the types the fields of a query of `hashSpec (shakeCore vp)` have, for instance
after `rcases`; `rw` and `simp` then apply them to such terms directly. The carriers are `Bytes n`
and `Bytes 32` only after `shakePrimitives` is unfolded, which `rw` and `simp` do not do: at a
term whose fields are typed as byte vectors, instantiate the equation explicitly
(`(encode_thash vp _ _ _).trans`) rather than rewriting with it, and read the length of a field's
bytes with `Vector.length_toList (xs := (x : Bytes n))`.

`HashSig.SLHDSA.Security.ByteConformance` instantiates the oracle by SHAKE256 and identifies the
result with FIPS 205's SHAKE internal algorithms.

## References

* NIST FIPS 205, §9 (Algorithms 18–20), §11.1 (SLH-DSA using SHAKE).
-/

public section

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal

namespace SLHDSA.Security

open Concrete

variable (vp : ValidatedParams)

/-- The SHAKE256 primitive context at validated parameters `vp`: every carrier is a byte vector,
`PK.seed`, `SK.seed`, `SK.prf` and nodes of `n` bytes, addresses of `32`. -/
abbrev shakeCore : CorePrimitives vp.params := (shakePrimitives vp.params).core

/-- **The single SHAKE256 oracle**: a random oracle on byte strings with `m`-byte answers. -/
abbrev shakeSpec : OracleSpec (List Byte) := List Byte →ₒ Bytes vp.params.m

/-! ## Fixed-width byte vectors from lists -/

/-- The `k`-byte vector holding the first `k` bytes of `l`, padded with zeros when `l` is shorter.
-/
@[expose] def bytesOfList (k : ℕ) (l : List Byte) : Bytes k := Vector.ofFn fun i => l.getD i 0

/-- The first `n` bytes of a byte vector, padded with zeros when it is shorter. -/
@[expose] def prefixBytes (n : ℕ) {m : ℕ} (v : Bytes m) : Bytes n := bytesOfList n v.toList

variable {vp}

/-- A list of at least `k` bytes gives its first `k` bytes. -/
theorem toList_bytesOfList_of_le {k : ℕ} {l : List Byte} (h : k ≤ l.length) :
    (bytesOfList k l).toList = l.take k := by
  apply List.ext_getElem
  · simp [bytesOfList, h]
  · intro i h₁ h₂
    have hi : i < l.length := by simp at h₂; omega
    simp [bytesOfList, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- A byte vector read back from its own bytes is itself. -/
@[simp] theorem bytesOfList_toList {k : ℕ} (v : Bytes k) : bytesOfList k v.toList = v := by
  apply Vector.toList_inj.mp
  rw [toList_bytesOfList_of_le (by simp), List.take_of_length_le (by simp)]

/-- `bytesOfList k` reads only the first `k` bytes. -/
theorem bytesOfList_take (k : ℕ) (l : List Byte) : bytesOfList k (l.take k) = bytesOfList k l := by
  ext i hi
  simp [bytesOfList, List.getD_eq_getElem?_getD]

/-- `bytesOfList k` ignores everything after the first `k` bytes. -/
theorem bytesOfList_append_of_length_eq {k : ℕ} {l : List Byte} (h : l.length = k)
    (l' : List Byte) : bytesOfList k (l ++ l') = bytesOfList k l := by
  rw [← bytesOfList_take k (l ++ l'), List.take_append_of_le_length (by omega),
    List.take_of_length_le (by omega)]

/-- The first `n ≤ m` bytes of an `m`-byte vector. -/
theorem toList_prefixBytes_of_le {n m : ℕ} (h : n ≤ m) (v : Bytes m) :
    (prefixBytes n v).toList = v.toList.take n :=
  toList_bytesOfList_of_le (by simpa using h)

/-- For `n ≤ m`, an `m`-byte vector is its first `n` bytes and the remaining `m - n`. -/
def prefixDropEquiv {n m : ℕ} (hnm : n ≤ m) : Bytes m ≃ Bytes n × Bytes (m - n) where
  toFun u := (prefixBytes n u, bytesOfList (m - n) (u.toList.drop n))
  invFun ab := bytesOfList m (ab.1.toList ++ ab.2.toList)
  left_inv u := by
    have hl : (u.toList.drop n).length = m - n := by simp
    simp only [toList_prefixBytes_of_le hnm, toList_bytesOfList_of_le hl.ge,
      List.take_of_length_le hl.le, List.take_append_drop, bytesOfList_toList]
  right_inv := fun ⟨a, b⟩ ↦ by
    have hl : (a.toList ++ b.toList).length = m := by simp; omega
    simp only [prefixBytes, toList_bytesOfList_of_le hl.ge, List.take_of_length_le hl.le]
    rw [bytesOfList_append_of_length_eq (by simp), List.drop_left' (by simp), bytesOfList_toList,
      bytesOfList_toList]

/-- **The first `n` bytes of a uniform `m`-byte vector are uniform**, for `n ≤ m`. -/
theorem prEvent_uniformSample_prefixBytes_eq {n m : ℕ} (hnm : n ≤ m) (ℓ : Bytes n) :
    Pr{let u ← $ᵗ (Bytes m)}[prefixBytes n u = ℓ] = (Nat.card (Bytes n) : ℝ≥0∞)⁻¹ :=
  (SampleableType.prEvent_uniformSample_equiv (prefixDropEquiv hnm) (·.1 = ℓ)).trans <|
    (SampleableType.prEvent_uniformSample_fst (· = ℓ)).trans
      (SampleableType.prEvent_uniformSample_eq_singleton_natCard ℓ)

/-- The first `k` blocks of `n` bytes of a byte string, each padded with zeros when the string runs
short. -/
@[expose] def bytesBlocks (n : ℕ) : ℕ → List Byte → List (Bytes n)
  | 0, _ => []
  | k + 1, l => bytesOfList n l :: bytesBlocks n k (l.drop n)

/-- A string of `n k` bytes is the concatenation of its `k` blocks of `n` bytes. -/
theorem flatten_map_toList_bytesBlocks {n k : ℕ} {l : List Byte} (h : l.length = n * k) :
    ((bytesBlocks n k l).map Vector.toList).flatten = l := by
  induction k generalizing l with
  | zero => simp_all [bytesBlocks]
  | succ k ih =>
      rw [bytesBlocks, List.map_cons, List.flatten_cons,
        toList_bytesOfList_of_le (by rw [h, Nat.mul_succ]; omega),
        ih (by rw [List.length_drop, h, Nat.mul_succ]; omega), List.take_append_drop]

/-- `Bytes m ≃ Bytes n × Bytes (m - n)` for `n ≤ m`: the first `n` bytes and the rest. -/
@[expose] def splitBytes {n m : ℕ} (h : n ≤ m) : Bytes m ≃ Bytes n × Bytes (m - n) where
  toFun w := (prefixBytes n w, bytesOfList (m - n) (w.toList.drop n))
  invFun p := bytesOfList m (p.1.toList ++ p.2.toList)
  left_inv w := by
    apply Vector.toList_inj.mp
    change (bytesOfList m ((bytesOfList n w.toList).toList ++
      (bytesOfList (m - n) (w.toList.drop n)).toList)).toList = w.toList
    have h₁ : n ≤ w.toList.length := by simpa using h
    have h₂ : m - n ≤ (w.toList.drop n).length := by simp
    rw [toList_bytesOfList_of_le h₁, toList_bytesOfList_of_le h₂, List.take_of_length_le
      (l := List.drop n w.toList) (by simp), List.take_append_drop, toList_bytesOfList_of_le
      (by simp), List.take_of_length_le (by simp)]
  right_inv p := by
    obtain ⟨a, b⟩ := p
    have hw : (bytesOfList m (a.toList ++ b.toList)).toList = a.toList ++ b.toList := by
      rw [toList_bytesOfList_of_le (by simp; omega), List.take_of_length_le (by simp; omega)]
    refine Prod.ext (Vector.toList_inj.mp ?_) (Vector.toList_inj.mp ?_)
    · change (bytesOfList n (bytesOfList m (a.toList ++ b.toList)).toList).toList = a.toList
      rw [hw, toList_bytesOfList_of_le (by simp), List.take_left' (by simp)]
    · change (bytesOfList (m - n) ((bytesOfList m (a.toList ++ b.toList)).toList.drop n)).toList =
        b.toList
      rw [hw, List.drop_left' (by simp), bytesOfList_toList]

/-! ## The encodings -/

variable (vp)

/-- **The FIPS 205 §11.1 SHAKE input layouts**: `PK.seed ‖ ADRS ‖ M_1 ‖ … ‖ M_ℓ` for the
tweakable hash, `R ‖ PK.seed ‖ PK.root ‖ M` for `H_msg`, `SK.prf ‖ opt_rand ‖ M` for
`PRF_msg`. -/
@[expose] def encode : (hashSpec (shakeCore vp)).Domain → List Byte
  | .inl (.thash pkSeed adrsKey xs) =>
      Vector.toList (pkSeed : Bytes vp.params.n) ++ Vector.toList (adrsKey : Bytes 32) ++
        (xs.map fun x : (shakeCore vp).Y => Vector.toList (x : Bytes vp.params.n)).flatten
  | .inl (.hmsg r pkSeed pkRoot msg) =>
      Vector.toList (r : Bytes vp.params.n) ++ Vector.toList (pkSeed : Bytes vp.params.n) ++
        Vector.toList (pkRoot : Bytes vp.params.n) ++ msg
  | .inr q =>
      Vector.toList (q.skPrf : Bytes vp.params.n) ++
        Vector.toList (q.optRand : Bytes vp.params.n) ++ q.msg

/-- Each typed query is one query of the single oracle at its encoding: a tweakable-hash or
`PRF_msg` query reads the first `n` bytes of the answer, an `H_msg` query reads all `m`. -/
@[expose] noncomputable def encHashImpl :
    QueryImpl (hashSpec (shakeCore vp)) (OracleComp (unifSpec + shakeSpec vp)) := fun t =>
  match t with
  | .inl (.thash pkSeed adrsKey xs) =>
      (prefixBytes vp.params.n <$>
        (query (spec := shakeSpec vp) (encode vp (.inl (.thash pkSeed adrsKey xs))) :
          OracleComp (unifSpec + shakeSpec vp) (Bytes vp.params.m)) :
        OracleComp (unifSpec + shakeSpec vp) (Bytes vp.params.n))
  | .inl (.hmsg r pkSeed pkRoot msg) =>
      (query (spec := shakeSpec vp) (encode vp (.inl (.hmsg r pkSeed pkRoot msg))) :
        OracleComp (unifSpec + shakeSpec vp) (Bytes vp.params.m))
  | .inr q =>
      (prefixBytes vp.params.n <$>
        (query (spec := shakeSpec vp) (encode vp (.inr q)) :
          OracleComp (unifSpec + shakeSpec vp) (Bytes vp.params.m)) :
        OracleComp (unifSpec + shakeSpec vp) (Bytes vp.params.n))

/-- The encoding handler on the whole interface: uniform draws pass through, and every hash query
is `encHashImpl`. -/
@[expose] noncomputable def encImpl :
    QueryImpl (unifSpec + hashSpec (shakeCore vp)) (OracleComp (unifSpec + shakeSpec vp)) :=
  QueryImpl.ofLift unifSpec (OracleComp (unifSpec + shakeSpec vp)) + encHashImpl vp

/-- **SLH-DSA over one SHAKE256 oracle.** FIPS 205's internal key generation, signing and
verification, with every tweakable-hash, `PRF`, `PRF_msg` and `H_msg` evaluation one query of the
single oracle at its §11.1 layout. The public seed is drawn from `pkSeedDist` and `opt_rand` from
`optRand`; the secret seeds are drawn uniformly. -/
@[expose] noncomputable def shakeRomScheme
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeedDist : ProbComp (shakeCore vp).PkSeed) :
    SignatureAlg (OracleComp (unifSpec + shakeSpec vp)) (List Byte)
      (PublicKeyCore (shakeCore vp)) (SecretKeyCore (shakeCore vp))
      (GeneralScheme.SignatureCore vp (shakeCore vp)) :=
  (romScheme (shakeCore vp) (Equiv.refl _) optRand pkSeedDist).map (simulateQ' (encImpl vp))

/-- The runtime of the single-oracle model: the lazy random oracle on byte strings, from the empty
cache, with uniform draws as sampled. -/
noncomputable abbrev shakeRuntime : ProbCompRuntime (OracleComp (unifSpec + shakeSpec vp)) :=
  ProbCompRuntime.rom (shakeSpec vp)

/-- The forging advantage against `shakeRomScheme` under `shakeRuntime`. -/
noncomputable def shakeAdvantage
    {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
    {pkSeedDist : ProbComp (shakeCore vp).PkSeed}
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand pkSeedDist)) : ℝ≥0∞ :=
  unforgeableAdvantage (shakeRuntime vp) adv

/-- The forging advantage against `shakeRomScheme` is the unforgeability advantage under
`shakeRuntime`. -/
theorem shakeAdvantage_def
    {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
    {pkSeedDist : ProbComp (shakeCore vp).PkSeed}
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand pkSeedDist)) :
    shakeAdvantage vp adv = unforgeableAdvantage (shakeRuntime vp) adv := by
  rw [shakeAdvantage]

/-- The strong forging advantage against `shakeRomScheme` under `shakeRuntime`: the probability of
a valid pair of message and signature that the signing oracle never returned. -/
noncomputable def shakeStrongAdvantage
    {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
    {pkSeedDist : ProbComp (shakeCore vp).PkSeed}
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand pkSeedDist)) : ℝ≥0∞ :=
  strongUnforgeableAdvantage (shakeRuntime vp) adv

/-- The strong forging advantage against `shakeRomScheme` is the strong unforgeability advantage
under `shakeRuntime`. -/
theorem shakeStrongAdvantage_def
    {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
    {pkSeedDist : ProbComp (shakeCore vp).PkSeed}
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand pkSeedDist)) :
    shakeStrongAdvantage vp adv = strongUnforgeableAdvantage (shakeRuntime vp) adv := by
  rw [shakeStrongAdvantage]

variable {vp} in
/-- The forging advantage against `shakeRomScheme` is at most the strong forging advantage of the
same adversary program. -/
theorem shakeAdvantage_le_shakeStrongAdvantage
    {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
    {pkSeedDist : ProbComp (shakeCore vp).PkSeed}
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand pkSeedDist)) :
    shakeAdvantage vp adv ≤ shakeStrongAdvantage vp
      (⟨adv.main⟩ : StrongUnforgeableAdversary (shakeRomScheme vp optRand pkSeedDist)) :=
  unforgeableAdvantage_le_strongUnforgeableAdvantage _ adv

/-! ## The shape of each layout -/

section Layout

variable (r : (shakeCore vp).Y) (pkSeed : (shakeCore vp).PkSeed) (pkRoot : (shakeCore vp).Y)
  (adrsKey : (shakeCore vp).AdrsKey) (xs : List (shakeCore vp).Y) (msg : List Byte)

/-- The tweakable-hash layout `PK.seed ‖ ADRS ‖ M_1 ‖ … ‖ M_ℓ`. -/
@[simp] theorem encode_thash :
    encode vp (.inl (.thash pkSeed adrsKey xs)) =
      Vector.toList (pkSeed : Bytes vp.params.n) ++ Vector.toList (adrsKey : Bytes 32) ++
        (xs.map fun x : (shakeCore vp).Y => Vector.toList (x : Bytes vp.params.n)).flatten := rfl

/-- The `H_msg` layout `R ‖ PK.seed ‖ PK.root ‖ M`. -/
@[simp] theorem encode_hmsg :
    encode vp (.inl (.hmsg r pkSeed pkRoot msg)) =
      Vector.toList (r : Bytes vp.params.n) ++ Vector.toList (pkSeed : Bytes vp.params.n) ++
        Vector.toList (pkRoot : Bytes vp.params.n) ++ msg := rfl

/-- The `PRF_msg` layout `SK.prf ‖ opt_rand ‖ M`. -/
@[simp] theorem encode_prfMsg (q : PrfMsgQuery (shakeCore vp).SkPrf (shakeCore vp).Y) :
    encode vp (.inr q) =
      Vector.toList (q.skPrf : Bytes vp.params.n) ++
        Vector.toList (q.optRand : Bytes vp.params.n) ++ q.msg := rfl

/-- The secret value at a WOTS+ or FORS secret-key address `a` is the oracle's answer at
`PK.seed ‖ ADRS ‖ SK.seed`, FIPS 205's `PRF` layout. -/
theorem encode_oracleSecret (skSeed : (shakeCore vp).SkSeed) (a : Adrs) :
    encode vp (.inl (.thash pkSeed ((shakeCore vp).adrsToKey a) [skSeed])) =
      Vector.toList (pkSeed : Bytes vp.params.n) ++ a.toBytes ++
        Vector.toList (skSeed : Bytes vp.params.n) := by
  refine (encode_thash vp pkSeed (Adrs.toVector a) [skSeed]).trans ?_
  rw [show Vector.toList (Adrs.toVector a) = a.toBytes by simp [Adrs.toVector]]
  exact congrArg _ (List.append_nil _)

/-- A tweakable-hash string has `n + 32 + n ℓ` bytes. -/
theorem length_encode_thash :
    (encode vp (.inl (.thash pkSeed adrsKey xs))).length =
      vp.params.n + 32 + vp.params.n * xs.length := by
  have hxs : ∀ ys : List (shakeCore vp).Y,
      (ys.map fun y : (shakeCore vp).Y => Vector.toList (y : Bytes vp.params.n)).flatten.length =
        vp.params.n * ys.length := by
    intro ys
    induction ys with
    | nil => simp
    | cons y ys ih =>
        rw [List.map_cons, List.flatten_cons, List.length_append, ih,
          Vector.length_toList (xs := (y : Bytes vp.params.n)), List.length_cons]
        ring
  rw [encode_thash, List.length_append, List.length_append,
    Vector.length_toList (xs := (pkSeed : Bytes vp.params.n)),
    Vector.length_toList (xs := (adrsKey : Bytes 32)), hxs]

/-- An `H_msg` string has `3n + |M|` bytes. -/
theorem length_encode_hmsg :
    (encode vp (.inl (.hmsg r pkSeed pkRoot msg))).length = 3 * vp.params.n + msg.length := by
  rw [encode_hmsg, List.length_append, List.length_append, List.length_append,
    Vector.length_toList (xs := (r : Bytes vp.params.n)),
    Vector.length_toList (xs := (pkSeed : Bytes vp.params.n)),
    Vector.length_toList (xs := (pkRoot : Bytes vp.params.n))]
  omega

/-- A `PRF_msg` string has `2n + |M|` bytes. -/
theorem length_encode_prfMsg (q : PrfMsgQuery (shakeCore vp).SkPrf (shakeCore vp).Y) :
    (encode vp (.inr q)).length = 2 * vp.params.n + q.msg.length := by
  rw [encode_prfMsg, List.length_append, List.length_append,
    Vector.length_toList (xs := (q.skPrf : Bytes vp.params.n)),
    Vector.length_toList (xs := (q.optRand : Bytes vp.params.n))]
  omega

/-- For `n ≤ 32`, every encoded query has at least `2n` bytes. -/
theorem two_mul_le_length_encode (h : vp.params.n ≤ 32) (t : (hashSpec (shakeCore vp)).Domain) :
    2 * vp.params.n ≤ (encode vp t).length := by
  rcases t with (⟨pkSeed, adrsKey, xs⟩ | ⟨r, pkSeed, pkRoot, msg⟩) | q
  · rw [length_encode_thash]
    omega
  · rw [length_encode_hmsg]
    omega
  · rw [length_encode_prfMsg]
    omega

/-- A tweakable-hash string begins with `PK.seed`. -/
theorem take_encode_thash :
    (encode vp (.inl (.thash pkSeed adrsKey xs))).take vp.params.n =
      Vector.toList (pkSeed : Bytes vp.params.n) := by
  rw [encode_thash, List.append_assoc]
  exact List.take_left' (Vector.length_toList (xs := (pkSeed : Bytes vp.params.n)))

/-- After `PK.seed`, a tweakable-hash string is the address followed by the input blocks. -/
theorem drop_encode_thash :
    (encode vp (.inl (.thash pkSeed adrsKey xs))).drop vp.params.n =
      Vector.toList (adrsKey : Bytes 32) ++
        (xs.map fun x : (shakeCore vp).Y => Vector.toList (x : Bytes vp.params.n)).flatten := by
  rw [encode_thash, List.append_assoc]
  exact List.drop_left' (Vector.length_toList (xs := (pkSeed : Bytes vp.params.n)))

/-- The address field of a tweakable-hash string, bytes `n` to `n + 32`. -/
theorem take_drop_encode_thash :
    ((encode vp (.inl (.thash pkSeed adrsKey xs))).drop vp.params.n).take 32 =
      Vector.toList (adrsKey : Bytes 32) := by
  rw [drop_encode_thash]
  exact List.take_left' (Vector.length_toList (xs := (adrsKey : Bytes 32)))

/-- After `PK.seed ‖ ADRS`, a tweakable-hash string is the concatenation of its input blocks. -/
theorem drop_add_encode_thash :
    (encode vp (.inl (.thash pkSeed adrsKey xs))).drop (vp.params.n + 32) =
      (xs.map fun x : (shakeCore vp).Y => Vector.toList (x : Bytes vp.params.n)).flatten := by
  rw [← List.drop_drop, drop_encode_thash]
  exact List.drop_left' (Vector.length_toList (xs := (adrsKey : Bytes 32)))

/-- An `H_msg` string begins with `R`. -/
theorem take_encode_hmsg :
    (encode vp (.inl (.hmsg r pkSeed pkRoot msg))).take vp.params.n =
      Vector.toList (r : Bytes vp.params.n) := by
  rw [encode_hmsg, List.append_assoc, List.append_assoc]
  exact List.take_left' (Vector.length_toList (xs := (r : Bytes vp.params.n)))

/-- After `R`, an `H_msg` string is `PK.seed ‖ PK.root ‖ M`. -/
theorem drop_encode_hmsg :
    (encode vp (.inl (.hmsg r pkSeed pkRoot msg))).drop vp.params.n =
      Vector.toList (pkSeed : Bytes vp.params.n) ++ Vector.toList (pkRoot : Bytes vp.params.n) ++
        msg := by
  rw [encode_hmsg, List.append_assoc, List.append_assoc,
    List.drop_left' (Vector.length_toList (xs := (r : Bytes vp.params.n))), List.append_assoc]

/-- The second `n`-byte block of an `H_msg` string is `PK.seed`. -/
theorem take_drop_encode_hmsg :
    ((encode vp (.inl (.hmsg r pkSeed pkRoot msg))).drop vp.params.n).take vp.params.n =
      Vector.toList (pkSeed : Bytes vp.params.n) := by
  rw [drop_encode_hmsg, List.append_assoc]
  exact List.take_left' (Vector.length_toList (xs := (pkSeed : Bytes vp.params.n)))

/-- The third `n`-byte block of an `H_msg` string is `PK.root`. -/
theorem take_drop_two_mul_encode_hmsg :
    ((encode vp (.inl (.hmsg r pkSeed pkRoot msg))).drop (2 * vp.params.n)).take vp.params.n =
      Vector.toList (pkRoot : Bytes vp.params.n) := by
  rw [Nat.two_mul, ← List.drop_drop, drop_encode_hmsg, List.append_assoc,
    List.drop_left' (Vector.length_toList (xs := (pkSeed : Bytes vp.params.n)))]
  exact List.take_left' (Vector.length_toList (xs := (pkRoot : Bytes vp.params.n)))

/-- After `R ‖ PK.seed ‖ PK.root`, an `H_msg` string is the message. -/
theorem drop_three_mul_encode_hmsg :
    (encode vp (.inl (.hmsg r pkSeed pkRoot msg))).drop (3 * vp.params.n) = msg := by
  rw [show 3 * vp.params.n = vp.params.n + vp.params.n + vp.params.n by omega, ← List.drop_drop,
    ← List.drop_drop, drop_encode_hmsg, List.append_assoc,
    List.drop_left' (Vector.length_toList (xs := (pkSeed : Bytes vp.params.n)))]
  exact List.drop_left' (Vector.length_toList (xs := (pkRoot : Bytes vp.params.n)))

/-- A `PRF_msg` string begins with `SK.prf`. -/
theorem take_encode_prfMsg (q : PrfMsgQuery (shakeCore vp).SkPrf (shakeCore vp).Y) :
    (encode vp (.inr q)).take vp.params.n = Vector.toList (q.skPrf : Bytes vp.params.n) := by
  rw [encode_prfMsg, List.append_assoc]
  exact List.take_left' (Vector.length_toList (xs := (q.skPrf : Bytes vp.params.n)))

/-- After `SK.prf`, a `PRF_msg` string is `opt_rand ‖ M`. -/
theorem drop_encode_prfMsg (q : PrfMsgQuery (shakeCore vp).SkPrf (shakeCore vp).Y) :
    (encode vp (.inr q)).drop vp.params.n =
      Vector.toList (q.optRand : Bytes vp.params.n) ++ q.msg := by
  rw [encode_prfMsg, List.append_assoc]
  exact List.drop_left' (Vector.length_toList (xs := (q.skPrf : Bytes vp.params.n)))

/-- The second `n`-byte block of a `PRF_msg` string is `opt_rand`. -/
theorem take_drop_encode_prfMsg (q : PrfMsgQuery (shakeCore vp).SkPrf (shakeCore vp).Y) :
    ((encode vp (.inr q)).drop vp.params.n).take vp.params.n =
      Vector.toList (q.optRand : Bytes vp.params.n) := by
  rw [drop_encode_prfMsg]
  exact List.take_left' (Vector.length_toList (xs := (q.optRand : Bytes vp.params.n)))

/-- After `SK.prf ‖ opt_rand`, a `PRF_msg` string is the message. -/
theorem drop_two_mul_encode_prfMsg (q : PrfMsgQuery (shakeCore vp).SkPrf (shakeCore vp).Y) :
    (encode vp (.inr q)).drop (2 * vp.params.n) = q.msg := by
  rw [Nat.two_mul, ← List.drop_drop, drop_encode_prfMsg]
  exact List.drop_left' (Vector.length_toList (xs := (q.optRand : Bytes vp.params.n)))

end Layout

/-- Concatenations of `n`-byte blocks, `n` positive, determine the blocks. -/
theorem flatten_map_toList_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective fun xs : List (Bytes n) => (xs.map Vector.toList).flatten := by
  intro xs
  induction xs with
  | nil =>
      rintro (_ | ⟨y, ys⟩) h
      · rfl
      · have := congrArg List.length h
        simp at this
        omega
  | cons x xs ih =>
      rintro (_ | ⟨y, ys⟩) h
      · have := congrArg List.length h
        simp at this
        omega
      · simp only [List.map_cons, List.flatten_cons] at h
        obtain ⟨hxy, hrest⟩ := List.append_inj h (by simp)
        rw [Vector.toList_inj.mp hxy, ih hrest]

/-- The tweakable-hash layout is injective. -/
theorem encode_thash_inj {pkSeed pkSeed' : (shakeCore vp).PkSeed}
    {adrsKey adrsKey' : (shakeCore vp).AdrsKey} {xs xs' : List (shakeCore vp).Y} :
    encode vp (.inl (.thash pkSeed adrsKey xs)) = encode vp (.inl (.thash pkSeed' adrsKey' xs')) ↔
      pkSeed = pkSeed' ∧ adrsKey = adrsKey' ∧ xs = xs' := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl, rfl⟩; rfl⟩
  rw [encode_thash, encode_thash, List.append_assoc, List.append_assoc] at h
  obtain ⟨h₁, h₂⟩ := List.append_inj h
    ((Vector.length_toList (xs := (pkSeed : Bytes vp.params.n))).trans
      (Vector.length_toList (xs := (pkSeed' : Bytes vp.params.n))).symm)
  obtain ⟨h₃, h₄⟩ := List.append_inj h₂
    ((Vector.length_toList (xs := (adrsKey : Bytes 32))).trans
      (Vector.length_toList (xs := (adrsKey' : Bytes 32))).symm)
  exact ⟨Vector.toList_inj.mp h₁, Vector.toList_inj.mp h₃,
    flatten_map_toList_injective vp.valid.n_pos h₄⟩

/-- The `H_msg` layout is injective. -/
theorem encode_hmsg_inj {r r' : (shakeCore vp).Y} {pkSeed pkSeed' : (shakeCore vp).PkSeed}
    {pkRoot pkRoot' : (shakeCore vp).Y} {msg msg' : List Byte} :
    encode vp (.inl (.hmsg r pkSeed pkRoot msg)) =
        encode vp (.inl (.hmsg r' pkSeed' pkRoot' msg')) ↔
      r = r' ∧ pkSeed = pkSeed' ∧ pkRoot = pkRoot' ∧ msg = msg' := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl, rfl, rfl⟩; rfl⟩
  rw [encode_hmsg, encode_hmsg] at h
  simp only [List.append_assoc] at h
  obtain ⟨h₁, h₂⟩ := List.append_inj h
    ((Vector.length_toList (xs := (r : Bytes vp.params.n))).trans
      (Vector.length_toList (xs := (r' : Bytes vp.params.n))).symm)
  obtain ⟨h₃, h₄⟩ := List.append_inj h₂
    ((Vector.length_toList (xs := (pkSeed : Bytes vp.params.n))).trans
      (Vector.length_toList (xs := (pkSeed' : Bytes vp.params.n))).symm)
  obtain ⟨h₅, h₆⟩ := List.append_inj h₄
    ((Vector.length_toList (xs := (pkRoot : Bytes vp.params.n))).trans
      (Vector.length_toList (xs := (pkRoot' : Bytes vp.params.n))).symm)
  exact ⟨Vector.toList_inj.mp h₁, Vector.toList_inj.mp h₃, Vector.toList_inj.mp h₅, h₆⟩

/-- The `PRF_msg` layout is injective. -/
theorem encode_prfMsg_inj {q q' : PrfMsgQuery (shakeCore vp).SkPrf (shakeCore vp).Y} :
    encode vp (.inr q) = encode vp (.inr q') ↔ q = q' := by
  refine ⟨fun h => ?_, by rintro rfl; rfl⟩
  obtain ⟨skPrf, optRand, msg⟩ := q
  obtain ⟨skPrf', optRand', msg'⟩ := q'
  change (skPrf : Bytes vp.params.n).toList ++ (optRand : Bytes vp.params.n).toList ++ msg =
    (skPrf' : Bytes vp.params.n).toList ++ (optRand' : Bytes vp.params.n).toList ++ msg' at h
  simp only [List.append_assoc] at h
  obtain ⟨h₁, h₂⟩ := List.append_inj h
    ((Vector.length_toList (xs := (skPrf : Bytes vp.params.n))).trans
      (Vector.length_toList (xs := (skPrf' : Bytes vp.params.n))).symm)
  obtain ⟨h₃, h₄⟩ := List.append_inj h₂
    ((Vector.length_toList (xs := (optRand : Bytes vp.params.n))).trans
      (Vector.length_toList (xs := (optRand' : Bytes vp.params.n))).symm)
  simp only [PrfMsgQuery.mk.injEq]
  exact ⟨Vector.toList_inj.mp h₁, Vector.toList_inj.mp h₃, h₄⟩

/-! ## Averaging over the public seed -/

variable {vp}

/-- The encoding handler leaves the uniform draws of a computation unchanged. -/
theorem simulateQ_encImpl_liftM {α : Type} (oa : ProbComp α) :
    simulateQ (encImpl vp) (liftM oa : OracleComp (unifSpec + hashSpec (shakeCore vp)) α) =
      liftM oa := by
  rw [encImpl, QueryImpl.simulateQ_add_liftM_left, ← OracleComp.liftComp_eq_liftM]
  rfl

/-- The strong unforgeability experiment of `shakeRomScheme` draws the public seed and then runs
the experiment of `shakeRomScheme` at that seed, against the same adversary program. -/
theorem strongUnforgeableExperiment_shakeRomScheme
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeedDist : ProbComp (shakeCore vp).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand pkSeedDist)) :
    strongUnforgeableExperiment adv =
      liftM pkSeedDist >>= fun pkSeed =>
        strongUnforgeableExperiment
          (⟨adv.main⟩ : StrongUnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) := by
  simp only [strongUnforgeableExperiment, shakeRomScheme, SignatureAlg.map_keygen, romScheme,
    simulateQ_bind, simulateQ_encImpl_liftM, bind_assoc, liftM_pure,
    pure_bind]
  rfl

/-- **Averaging over the public seed.** A bound `β pkSeed` on the strong advantage of every
adversary against `shakeRomScheme` at each public seed, under a query budget, bounds the strong
advantage at the seed distribution `pkSeedDist` by the average of `β`. -/
theorem shakeStrongAdvantage_le_lintegral [MeasurableSpace (shakeCore vp).PkSeed]
    [DiscreteMeasurableSpace (shakeCore vp).PkSeed]
    {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
    (pkSeedDist : ProbComp (shakeCore vp).PkSeed) (β : (shakeCore vp).PkSeed → ℝ≥0∞) {qh qs : ℕ}
    (h : ∀ pkSeed (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))),
      adv.RomQueryBound qh qs → shakeStrongAdvantage vp adv ≤ β pkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand pkSeedDist))
    (hb : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp adv ≤ ∫⁻ pkSeed, β pkSeed ∂𝒟[pkSeedDist] := by
  rw [shakeStrongAdvantage, strongUnforgeableAdvantage,
    strongUnforgeableExperiment_shakeRomScheme,
    ProbCompRuntime.rom_evalDist_bind_liftM,
    Measure.bind_apply (measurableSet_singleton true) Measurable.of_discrete.aemeasurable]
  exact lintegral_mono fun pkSeed => h pkSeed ⟨adv.main⟩ hb

end SLHDSA.Security
