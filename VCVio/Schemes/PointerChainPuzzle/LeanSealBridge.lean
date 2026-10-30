/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.LeanSeal
public import VCVio.CryptoFoundations.TimeLockPuzzle.Encoding

/-!
# leanSeal over one random oracle

leanSeal hashes every typed point of the pointer-chain puzzle with SHA-256
(`VCVio/Schemes/PointerChainPuzzle/LeanSeal.lean`). This file idealizes SHA-256 as one random
oracle `byteSpec = ByteArray →ₒ Bytes 32` and relates it to the six typed oracles of the
pointer-chain puzzle at the byte types.

The delay proof of the pointer-chain puzzle needs six independent oracles, but leanSeal has one
hash. The encoding (`OracleComp.RandomOracleEncoding`) recovers the six from the one by domain
separation: every typed point is hashed at its own byte string, and a typed answer is the
truncation of the raw answer there. When distinct typed points never share a hash input, the
encoding has no clash, and the truncated answers at distinct inputs are independent and uniform,
so the single random oracle answers the typed points exactly as six independent typed random
oracles would. That injectivity is the content of SPEC §3, through the length prefix of every
label and the fixed widths of the fields; this file proves it for fewer than `2^32` chains. The
delay theorem then transfers to the byte level through the adapter of
`VCVio/CryptoFoundations/TimeLockPuzzle/Encoding.lean`, which turns a byte-level adversary into a
typed one within the same budgets.

## Main definitions

* `PointerChainPuzzle.LeanSeal.hashInput`: the SHA-256 input of a typed point (SPEC §3): a
  52-byte chain step, or a length-prefixed label followed by fixed-width fields.
* `PointerChainPuzzle.LeanSeal.route`: the typed point a byte string is the hash input of, if any.
* `PointerChainPuzzle.LeanSeal.encoding`: the `RandomOracleEncoding` of the typed oracles into
  `byteSpec`, splitting a 32-byte answer into a `b`-byte link and a tail at the mask oracle.
* `PointerChainPuzzle.LeanSeal.byteScheme`: leanSeal as a `TimeLockPuzzle` over `byteSpec`, the
  typed rounds of the generator and the checked solver submitted as rounds of hash inputs.

## Main statements

* `PointerChainPuzzle.LeanSeal.hashInput_injective`, `route_hashInput`, `route_eq_none_iff`:
  for fewer than `2^32` chains the hash input is injective, and `route` recognizes exactly its
  image; hence `not_clash`: the encoding never clashes.
* `PointerChainPuzzle.LeanSeal.simulateQ_byteScheme_gen`, `simulateQ_byteScheme_solve`: on the
  answers of a byte function the byte-level puzzle is the executable leanSeal of `LeanSeal.lean`.
* `PointerChainPuzzle.LeanSeal.delayAdvantage_byteScheme_le`: a byte-level adversary wins the
  leanSeal delay experiment with probability at most that of its adapted adversary
  (`OracleComp.RandomOracleEncoding.adaptAdversary`) in the typed delay experiment, the instance
  for leanSeal of `OracleComp.RandomOracleEncoding.delayAdvantage_le_delayAdvantage_adaptAdversary`.
-/

public section

open OracleSpec OracleComp VCVio.Algorithms

namespace PointerChainPuzzle.LeanSeal

/-! ## The typed and the byte-level oracles -/

/-- The points of the six typed oracles of leanSeal with link width `b` and `n` chains. -/
abbrev TypedPoint (b n : ℕ) := Point n (Bytes 32) (Bytes b) (Bytes 16) (Bytes 32)

/-- The six typed oracles of leanSeal with link width `b` and `n` chains. -/
abbrev typedSpec (b n : ℕ) := oracleSpec n (Bytes 32) (Bytes b) (Bytes 16) (Bytes 32)

/-- SHA-256 idealized as one random oracle on byte strings. -/
abbrev byteSpec : OracleSpec ByteArray := ByteArray →ₒ Bytes 32

/-! ## Hash inputs of typed points -/

section HashInput

variable {b n : ℕ}

/-- The input `u8(len label) ‖ label ‖ x` of the labelled hash `TH(label, x)`. -/
@[expose]
def labelled (label : String) (x : ByteArray) : ByteArray :=
  ByteArray.mk #[label.toUTF8.size.toUInt8] ++ label.toUTF8 ++ x

lemma TH_eq (h : ByteArray → Bytes 32) (label : String) (x : ByteArray) :
    TH h label x = h (labelled label x) := rfl

/-- The input of the single oracle at which leanSeal answers a typed point. -/
@[expose]
def hashInput : TypedPoint b n → ByteArray
  | .start ctx i x =>
      labelled "leanseal/v1/start" (ctx.toByteArray ++ be 4 (i + 1) ++ x.toByteArray)
  | .step salt i s => s.toByteArray ++ salt.toByteArray ++ be 4 (i + 1)
  | .mask ctx y => labelled "leanseal/v1/mask" (ctx.toByteArray ++ y.toByteArray)
  | .acc a y => labelled "leanseal/v1/acc" (a.toByteArray ++ y.toByteArray)
  | .key ctx a => labelled "leanseal/v1/key" (ctx.toByteArray ++ a.toByteArray)
  | .commit ctx k => labelled "leanseal/v1/commit" (ctx.toByteArray ++ k.toByteArray)

/-- The typed answer at a point read off a 32-byte answer of the single oracle: its first `b`
bytes at a mask point, all of it at any other point. -/
@[expose]
def truncate : (t : TypedPoint b n) → Bytes 32 → (typedSpec b n).Range t
  | .start .., w => w
  | .step .., w => w
  | .mask .., w => w.take
  | .acc .., w => w
  | .key .., w => w
  | .commit .., w => w

/-- The typed oracles answered through the byte encoding by `h` answer a point `t` with the
truncation of `h` at its hash input. -/
lemma toImpl_oracles_apply (h : ByteArray → Bytes 32) (t : TypedPoint b n) :
    ((oracles (b := b) (n := n) h).toImpl t).run = truncate t (h (hashInput t)) := by
  cases t <;> rfl

/-! ### Reading a hash input back -/

/-- The bytes of a label. -/
@[expose]
def labelBytes (label : String) : List UInt8 := label.toUTF8.data.toList

/-- Split a length-prefixed label off a byte string: the label and the rest. -/
@[expose]
def unlabel : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | c :: l => some (l.take c.toNat, l.drop c.toNat)

/-- The typed point that the bytes `l` would be the hash input of, read from the length, the
label and the fixed-width fields without checking the other bytes. Chain-step inputs are the
52-byte ones; every other input is read by its length-prefixed label. -/
@[expose]
def parsePoint (l : List UInt8) : Option (TypedPoint b n) :=
  if l.length = 52 then
    if hj : beNat ((l.drop 48).take 4) - 1 < n then
      some (.step (Bytes.read l 32) ⟨_, hj⟩ (Bytes.read l 0))
    else none
  else
    match unlabel l with
    | none => none
    | some (lab, r) =>
        if lab = labelBytes "leanseal/v1/start" then
          if hj : beNat ((r.drop 32).take 4) - 1 < n then
            some (.start (Bytes.read r 0) ⟨_, hj⟩ (Bytes.read r 36))
          else none
        else if lab = labelBytes "leanseal/v1/mask" then
          some (.mask (Bytes.read r 0) (Bytes.read r 32))
        else if lab = labelBytes "leanseal/v1/acc" then
          some (.acc (Bytes.read r 0) (Bytes.read r 32))
        else if lab = labelBytes "leanseal/v1/key" then
          some (.key (Bytes.read r 0) (Bytes.read r 32))
        else if lab = labelBytes "leanseal/v1/commit" then
          some (.commit (Bytes.read r 0) (Bytes.read r 32))
        else none

/-- The typed point a byte string is the hash input of, if any: the point read off by
`parsePoint`, kept only if its hash input is the byte string. -/
@[expose]
def route (x : ByteArray) : Option (TypedPoint b n) :=
  match parsePoint x.data.toList with
  | some t => if hashInput t = x then some t else none
  | none => none

lemma hashInput_of_route_eq_some {x : ByteArray} {t : TypedPoint b n} (h : route x = some t) :
    hashInput t = x := by
  unfold route at h
  split at h
  · split_ifs at h with hx
    cases h
    exact hx
  · cases h

@[simp] lemma data_toList_toByteArray {k : ℕ} (x : Bytes k) :
    x.toByteArray.data.toList = x.toList := rfl

@[simp] lemma data_toList_be (w x : ℕ) :
    (be w x).data.toList = Encoding.natToBytesBE x w := by
  simp [be]

lemma data_toList_labelled (label : String) (x : ByteArray) :
    (labelled label x).data.toList =
      label.toUTF8.size.toUInt8 :: (labelBytes label ++ x.data.toList) := by
  simp [labelled, labelBytes]

lemma unlabel_labelled {label : String} (hl : label.toUTF8.size < 256) (x : ByteArray) :
    unlabel (labelled label x).data.toList = some (labelBytes label, x.data.toList) := by
  have hlen : (labelBytes label).length = label.toUTF8.size := by simp [labelBytes]
  have hc : label.toUTF8.size.toUInt8.toNat = label.toUTF8.size := by
    simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
    exact Nat.mod_eq_of_lt hl
  rw [data_toList_labelled, unlabel, hc, List.take_left' hlen, List.drop_left' hlen]

lemma length_labelBytes (label : String) : (labelBytes label).length = label.utf8ByteSize := by
  simp [labelBytes]

lemma labelBytes_inj {label label' : String} :
    labelBytes label = labelBytes label' ↔ label = label' := by
  refine ⟨fun h => String.toByteArray_inj.mp
    (ByteArray.ext (Array.toList_inj.mp (by simpa [labelBytes] using h))), ?_⟩
  rintro rfl
  rfl

lemma labelBytes_ne {label label' : String} (h : label ≠ label') :
    labelBytes label ≠ labelBytes label' :=
  fun h' => h (labelBytes_inj.mp h')

lemma unlabel_cons (c : UInt8) (lab r : List UInt8) (h : lab.length = c.toNat) :
    unlabel (c :: (lab ++ r)) = some (lab, r) := by
  rw [unlabel, List.take_left' h, List.drop_left' h]

lemma beNat_be_succ {n : ℕ} (hn : n < 2 ^ 32) (i : Fin n) :
    beNat (Encoding.natToBytesBE (i + 1) 4) - 1 = i := by
  rw [beNat_natToBytesBE, Nat.mod_eq_of_lt (by have := i.isLt; norm_num at hn ⊢; omega)]
  omega

lemma parsePoint_hashInput (hn : n < 2 ^ 32) (t : TypedPoint b n) :
    parsePoint (hashInput t).data.toList = some t := by
  cases t with
  | step salt i s =>
      have hl : (hashInput (.step salt i s : TypedPoint b n)).data.toList =
          (s.toList ++ salt.toList) ++ Encoding.natToBytesBE (i + 1) 4 := by
        simp [hashInput]
      have hj : beNat ((((hashInput (.step salt i s : TypedPoint b n)).data.toList).drop
          48).take 4) - 1 = i := by
        rw [hl, List.drop_left' (by simp), List.take_of_length_le (by simp)]
        exact beNat_be_succ hn i
      simp only [parsePoint, hj, i.isLt, dite_true]
      simp [hl, Bytes.read_append_left, Bytes.read_append_right]
  | start ctx i x =>
      have hl : (hashInput (.start ctx i x : TypedPoint b n)).data.toList =
          (17 : UInt8) :: (labelBytes "leanseal/v1/start" ++
            ((ctx.toList ++ Encoding.natToBytesBE (i + 1) 4) ++ x.toList)) := by
        simp only [hashInput, data_toList_labelled, String.toUTF8_eq_toByteArray,
          String.size_toByteArray, Nat.toUInt8_eq, ByteArray.data_append, Array.append_assoc,
          Array.toList_append, data_toList_toByteArray, data_toList_be, List.append_assoc,
          List.cons.injEq, and_true]
        decide
      have hj : beNat (((((ctx.toList ++ Encoding.natToBytesBE (i + 1) 4) ++ x.toList)).drop
          32).take 4) - 1 = i := by
        rw [List.append_assoc, List.drop_left' (by simp), List.take_left' (by simp)]
        exact beNat_be_succ hn i
      have h52 : ¬ (hashInput (.start ctx i x : TypedPoint b n)).data.toList.length = 52 := by
        rw [hl]
        simp [length_labelBytes, show "leanseal/v1/start".utf8ByteSize = 17 by decide]
        omega
      rw [parsePoint]
      simp only [h52, ↓reduceIte]
      rw [hl, unlabel_cons _ _ _ (by rw [length_labelBytes]; decide)]
      simp only [↓reduceIte, hj, i.isLt, ↓reduceDIte]
      simp [Bytes.read_append_left, Bytes.read_append_right]
  | mask ctx y =>
      have hl : (hashInput (.mask ctx y : TypedPoint b n)).data.toList =
          (16 : UInt8) :: (labelBytes "leanseal/v1/mask" ++ (ctx.toList ++ y.toList)) := by
        simp only [hashInput, data_toList_labelled, String.toUTF8_eq_toByteArray,
          String.size_toByteArray, Nat.toUInt8_eq, ByteArray.data_append, Array.toList_append,
          data_toList_toByteArray, List.cons.injEq, and_true]
        decide
      rw [hl, parsePoint]
      simp only [List.length_cons, List.length_append, Bytes.length_toList, length_labelBytes,
        show "leanseal/v1/mask".utf8ByteSize = 16 by decide, Nat.reduceAdd, Nat.reduceEqDiff,
        ↓reduceIte]
      rw [unlabel_cons _ _ _ (by rw [length_labelBytes]; decide)]
      simp only [labelBytes_ne (show "leanseal/v1/mask" ≠ "leanseal/v1/start" by decide),
        ↓reduceIte]
      simp [Bytes.read_append_left, Bytes.read_append_right]
  | acc a y =>
      have hl : (hashInput (.acc a y : TypedPoint b n)).data.toList =
          (15 : UInt8) :: (labelBytes "leanseal/v1/acc" ++ (a.toList ++ y.toList)) := by
        simp only [hashInput, data_toList_labelled, String.toUTF8_eq_toByteArray,
          String.size_toByteArray, Nat.toUInt8_eq, ByteArray.data_append, Array.toList_append,
          data_toList_toByteArray, List.cons.injEq, and_true]
        decide
      rw [hl, parsePoint]
      simp only [List.length_cons, List.length_append, Bytes.length_toList, length_labelBytes,
        show "leanseal/v1/acc".utf8ByteSize = 15 by decide, Nat.reduceAdd, Nat.reduceEqDiff,
        ↓reduceIte]
      rw [unlabel_cons _ _ _ (by rw [length_labelBytes]; decide)]
      simp only [labelBytes_ne (show "leanseal/v1/acc" ≠ "leanseal/v1/start" by decide),
        labelBytes_ne (show "leanseal/v1/acc" ≠ "leanseal/v1/mask" by decide),
        ↓reduceIte]
      simp [Bytes.read_append_left, Bytes.read_append_right]
  | key ctx a =>
      have hl : (hashInput (.key ctx a : TypedPoint b n)).data.toList =
          (15 : UInt8) :: (labelBytes "leanseal/v1/key" ++ (ctx.toList ++ a.toList)) := by
        simp only [hashInput, data_toList_labelled, String.toUTF8_eq_toByteArray,
          String.size_toByteArray, Nat.toUInt8_eq, ByteArray.data_append, Array.toList_append,
          data_toList_toByteArray, List.cons.injEq, and_true]
        decide
      rw [hl, parsePoint]
      simp only [List.length_cons, List.length_append, Bytes.length_toList, length_labelBytes,
        show "leanseal/v1/key".utf8ByteSize = 15 by decide, Nat.reduceAdd, Nat.reduceEqDiff,
        ↓reduceIte]
      rw [unlabel_cons _ _ _ (by rw [length_labelBytes]; decide)]
      simp only [labelBytes_ne (show "leanseal/v1/key" ≠ "leanseal/v1/start" by decide),
        labelBytes_ne (show "leanseal/v1/key" ≠ "leanseal/v1/mask" by decide),
        labelBytes_ne (show "leanseal/v1/key" ≠ "leanseal/v1/acc" by decide),
        ↓reduceIte]
      simp [Bytes.read_append_left, Bytes.read_append_right]
  | commit ctx k =>
      have hl : (hashInput (.commit ctx k : TypedPoint b n)).data.toList =
          (18 : UInt8) :: (labelBytes "leanseal/v1/commit" ++ (ctx.toList ++ k.toList)) := by
        simp only [hashInput, data_toList_labelled, String.toUTF8_eq_toByteArray,
          String.size_toByteArray, Nat.toUInt8_eq, ByteArray.data_append, Array.toList_append,
          data_toList_toByteArray, List.cons.injEq, and_true]
        decide
      rw [hl, parsePoint]
      simp only [List.length_cons, List.length_append, Bytes.length_toList, length_labelBytes,
        show "leanseal/v1/commit".utf8ByteSize = 18 by decide, Nat.reduceAdd, Nat.reduceEqDiff,
        ↓reduceIte]
      rw [unlabel_cons _ _ _ (by rw [length_labelBytes]; decide)]
      simp only [labelBytes_ne (show "leanseal/v1/commit" ≠ "leanseal/v1/start" by decide),
        labelBytes_ne (show "leanseal/v1/commit" ≠ "leanseal/v1/mask" by decide),
        labelBytes_ne (show "leanseal/v1/commit" ≠ "leanseal/v1/acc" by decide),
        labelBytes_ne (show "leanseal/v1/commit" ≠ "leanseal/v1/key" by decide),
        ↓reduceIte]
      simp [Bytes.read_append_left, Bytes.read_append_right]

/-- **The byte encoding is injective.** For fewer than `2^32` chains, distinct typed points have
distinct hash inputs: chain-step inputs are exactly the 52-byte ones, distinct length-prefixed
labels separate the labelled families, and fixed-width fields separate the points of one
family; `parsePoint` reads every point back from its hash input. -/
theorem hashInput_injective (hn : n < 2 ^ 32) :
    Function.Injective (hashInput (b := b) (n := n)) := fun t t' h =>
  Option.some.inj ((parsePoint_hashInput hn t).symm.trans
    ((congrArg (fun x : ByteArray => parsePoint x.data.toList) h).trans
      (parsePoint_hashInput hn t')))

/-- `route` reads every typed point back from its hash input. -/
theorem route_hashInput (hn : n < 2 ^ 32) (t : TypedPoint b n) : route (hashInput t) = some t := by
  simp [route, parsePoint_hashInput hn]

/-- `route` recognizes exactly the hash inputs of typed points: it returns `none` on every other
byte string. -/
theorem route_eq_none_iff (hn : n < 2 ^ 32) (x : ByteArray) :
    route (b := b) (n := n) x = none ↔ ∀ t : TypedPoint b n, hashInput t ≠ x := by
  refine ⟨fun h t ht => ?_, fun h => ?_⟩
  · subst ht
    simp [route_hashInput hn] at h
  · cases hr : route (b := b) (n := n) x with
    | none => rfl
    | some t => exact absurd (hashInput_of_route_eq_some hr) (h t)

end HashInput

/-! ## The encoding of the typed oracles into the single oracle -/

section Encoding

variable {b n : ℕ}

/-- A 32-byte value as its first `b` bytes and its last `32 - b` bytes. -/
@[expose]
def splitMask (hb : b ≤ 32) : Bytes 32 ≃ Bytes b × Bytes (32 - b) where
  toFun w := (w.take, Bytes.read w.toList b)
  invFun p := ⟨(p.1.toVector ++ p.2.toVector).cast (by omega)⟩
  left_inv w := Bytes.ext_getElem fun i hi => by
    by_cases h : i < b
    · simp [Bytes.take, Bytes.read, h, List.getD_eq_getElem?_getD,
        Bytes.getElem_toList, show i < 32 by omega]
    · simp [Bytes.take, Bytes.read, Vector.getElem_append, h, List.getD_eq_getElem?_getD,
        Bytes.getElem_toList, show b + (i - b) = i by omega, hi]
  right_inv p := by
    obtain ⟨x, y⟩ := p
    refine Prod.ext (Bytes.ext_getElem fun i hi => ?_) (Bytes.ext_getElem fun i hi => ?_)
    · simp [Bytes.take, Bytes.read, List.getD_eq_getElem?_getD, Bytes.getElem_toList,
        hi, show i < 32 by omega]
    · simp [Bytes.read, List.getD_eq_getElem?_getD, Bytes.getElem_toList,
        show b + i < 32 by omega]

/-- The part of a 32-byte answer that the typed answer at a point does not carry: its last
`32 - b` bytes at a mask point (none when `b = 32`), nothing at any other point. -/
@[expose]
def Tail (b : ℕ) : TypedPoint b n → Type
  | .mask .. => Bytes (32 - b)
  | _ => Unit

instance (t : TypedPoint b n) : SampleableType (Tail b t) :=
  match t with
  | .start .. => inferInstanceAs (SampleableType Unit)
  | .step .. => inferInstanceAs (SampleableType Unit)
  | .mask .. => inferInstanceAs (SampleableType (Bytes (32 - b)))
  | .acc .. => inferInstanceAs (SampleableType Unit)
  | .key .. => inferInstanceAs (SampleableType Unit)
  | .commit .. => inferInstanceAs (SampleableType Unit)

/-- A 32-byte answer split into the typed answer at a point and the tail. -/
@[expose]
def split (hb : b ≤ 32) : (t : TypedPoint b n) → Bytes 32 ≃ (typedSpec b n).Range t × Tail b t
  | .start .. => (Equiv.prodPUnit (Bytes 32)).symm
  | .step .. => (Equiv.prodPUnit (Bytes 32)).symm
  | .mask .. => splitMask hb
  | .acc .. => (Equiv.prodPUnit (Bytes 32)).symm
  | .key .. => (Equiv.prodPUnit (Bytes 32)).symm
  | .commit .. => (Equiv.prodPUnit (Bytes 32)).symm

/-- The encoding of the six typed oracles of leanSeal into the single oracle `byteSpec`, for a
link width `b ≤ 32` and fewer than `2^32` chains: a typed point is the query at its hash input,
the typed answer is the truncation of the answer there, and `route` reads hash inputs back. -/
@[expose]
noncomputable def encoding (hb : b ≤ 32) (hn : n < 2 ^ 32) :
    RandomOracleEncoding (typedSpec b n) ByteArray (Bytes 32) :=
  RandomOracleEncoding.ofSplit hashInput route hashInput_of_route_eq_some
    (fun t => by rw [route_hashInput hn]; rfl) (split hb)

variable (hb : b ≤ 32) (hn : n < 2 ^ 32)

@[simp] lemma encoding_encode : (encoding hb hn).encode = hashInput := rfl

@[simp] lemma encoding_route : (encoding hb hn).route = route := rfl

@[simp] lemma encoding_trunc (t : TypedPoint b n) (w : Bytes 32) :
    (encoding hb hn).trunc t w = truncate t w := by
  cases t <;> rfl

/-- No two cached typed points share a hash input: the encoding has no clash. -/
theorem not_clash (c : (typedSpec b n).QueryCache) : ¬ (encoding hb hn).Clash c := by
  rintro ⟨q, q', hne, -, -, he⟩
  exact hne (hashInput_injective hn he)

end Encoding

/-! ## leanSeal over the single oracle -/

section ByteScheme

variable {b n : ℕ}

/-- The answers to a round of typed points read off the answers at their hash inputs. -/
@[expose]
def truncateRound (ts : List (TypedPoint b n)) (us : byteSpec.batch.Range (ts.map hashInput)) :
    (typedSpec b n).batch.Range ts :=
  fun j => truncate ts[j] (us ⟨j, by simp⟩)

/-- A round of typed points submitted as the round of their hash inputs, each answer truncated;
uniform queries pass through. -/
@[expose]
def roundImpl :
    QueryImpl (unifSpec + (typedSpec b n).batch) (OracleComp (unifSpec + byteSpec.batch))
  | .inl k => liftM ((unifSpec + byteSpec.batch).query (.inl k))
  | .inr ts => truncateRound ts <$>
      liftM ((unifSpec + byteSpec.batch).query (.inr (ts.map hashInput)))

/-- leanSeal over the single oracle `byteSpec`: the generator and the checked solver of the
pointer-chain puzzle at the context `ctx` with `initAcc = id`, every round of typed points
submitted as the round of their hash inputs. -/
@[expose]
def byteScheme (b n m : ℕ) [NeZero n] : TimeLockPuzzle byteSpec (Puzzle b n) (Bytes 32) where
  gen := simulateQ roundImpl (PointerChainPuzzle.gen m (ctx b n m) id)
  solve puzzle := simulateQ roundImpl (PointerChainPuzzle.solve m (ctx b n m) id puzzle)

/-- The pointer-chain puzzle over the typed oracles of leanSeal, at the context `ctx` with
`initAcc = id`. -/
abbrev typedScheme (b n m : ℕ) [NeZero n] :
    TimeLockPuzzle (typedSpec b n) (Puzzle b n) (Bytes 32) :=
  scheme n m (ctx b n m) id (L := Bytes b)

/-- The single oracle answered by the byte-answer function `h`, round by round, with uniform
queries passed through. -/
abbrev byteImpl (h : ByteArray → Bytes 32) : QueryImpl (unifSpec + byteSpec.batch) ProbComp :=
  QueryImpl.batch' (unifFwdAnswerImpl (spec := byteSpec) fun x => (h x : Id (Bytes 32)))

/-- Answering the single oracle by `h` after submitting typed rounds as rounds of hash inputs is
answering the typed oracles through the byte encoding by `h`. -/
theorem byteImpl_compose_roundImpl (h : ByteArray → Bytes 32) :
    byteImpl h ∘ₛ roundImpl = impl h b n := by
  funext t
  rcases t with k | ts
  · rw [QueryImpl.apply_compose, roundImpl, simulateQ_spec_query]
    rfl
  · rw [QueryImpl.apply_compose, roundImpl, simulateQ_map, simulateQ_spec_query]
    simp only [byteImpl, impl, QueryImpl.batch'_apply_inr]
    rw [QueryImpl.batch_unifFwdAnswerImpl, QueryImpl.batch_unifFwdAnswerImpl]
    refine (map_pure _ _).trans (congrArg pure (funext fun j => ?_))
    simp [truncateRound, toImpl_oracles_apply]
    rfl

/-- The byte-level generator, with the single oracle answered by `h`, is the leanSeal generator
at `h`. -/
theorem simulateQ_byteScheme_gen (h : ByteArray → Bytes 32) (m : ℕ) [NeZero n] :
    simulateQ (byteImpl h) (byteScheme b n m).gen = gen h m := by
  rw [byteScheme, ← QueryImpl.simulateQ_compose, byteImpl_compose_roundImpl, simulateQ_gen_eq]

/-- The byte-level solver, with the single oracle answered by `h`, is the checked leanSeal solver
at `h`, on every puzzle. -/
theorem simulateQ_byteScheme_solve (h : ByteArray → Bytes 32) (m : ℕ) [NeZero n]
    (puzzle : Puzzle b n) :
    simulateQ (byteImpl h) ((byteScheme b n m).solve puzzle) = pure (solve h m puzzle) := by
  rw [byteScheme, ← QueryImpl.simulateQ_compose, byteImpl_compose_roundImpl, simulateQ_solve_eq]

end ByteScheme

end PointerChainPuzzle.LeanSeal

/-! ## The leanSeal delay experiments -/

namespace PointerChainPuzzle.LeanSeal

open TimeLockPuzzle

variable {b n : ℕ} (hb : b ≤ 32) (hn : n < 2 ^ 32)

/-- The rounds of the byte-level puzzle are the typed rounds translated by the byte encoding. -/
lemma roundImpl_eq : roundImpl (b := b) (n := n) = (encoding hb hn).roundImpl := by
  funext t
  rcases t with k | ts
  · rfl
  · simp only [roundImpl, RandomOracleEncoding.roundImpl]
    congr 1
    funext us
    funext j
    simp [truncateRound, RandomOracleEncoding.truncRound]

/-- **The byte-level delay experiment against the typed one.** For `b ≤ 32` and fewer than
`2^32` chains, a byte-level adversary wins the leanSeal delay experiment over the single oracle
`ByteArray →ₒ Bytes 32` with probability at most that of its adapted adversary in the typed delay
experiment of the pointer-chain puzzle at the byte types, with the honest generator between the
phases. -/
theorem delayAdvantage_byteScheme_le (m : ℕ) [NeZero n]
    (adv : Adversary byteSpec (Puzzle b n) (Bytes 32)) :
    delayAdvantage (byteScheme b n m) adv ≤
      delayAdvantage (typedScheme b n m) ((encoding hb hn).adaptAdversary adv) :=
  (encoding hb hn).delayAdvantage_le_delayAdvantage_adaptAdversary
    (by rw [byteScheme, roundImpl_eq hb hn]; rfl) (not_clash hb hn) adv

end PointerChainPuzzle.LeanSeal
