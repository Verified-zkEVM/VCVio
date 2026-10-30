/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.LeanSeal
public import VCVio.OracleComp.QueryTracking.RandomOracle.Encoded
import VCVio.OracleComp.SimSemantics.StateT.Measure

/-!
# leanSeal over one random oracle

leanSeal hashes every typed point of the pointer-chain puzzle with SHA-256
(`VCVio/Schemes/PointerChainPuzzle/LeanSeal.lean`). This file idealizes SHA-256 as one random
oracle `byteSpec = ByteArray →ₒ Bytes 32` and relates it to the six typed oracles of the
pointer-chain puzzle at the byte types.

## Main definitions

* `PointerChainPuzzle.LeanSeal.hashInput`: the SHA-256 input of a typed point (SPEC §3): a
  52-byte chain step, or a length-prefixed label followed by fixed-width fields.
* `PointerChainPuzzle.LeanSeal.route`: the typed point a byte string is the hash input of, if any.
* `PointerChainPuzzle.LeanSeal.encoding`: the `RandomOracleEncoding` of the typed oracles into
  `byteSpec`, splitting a 32-byte answer into a `b`-byte link and a tail at the mask oracle.
* `PointerChainPuzzle.LeanSeal.byteScheme`: leanSeal as a `TimeLockPuzzle` over `byteSpec`, the
  typed rounds of the generator and the checked solver submitted as rounds of hash inputs.
* `OracleComp.RandomOracleEncoding.adaptAdversary`: the typed adversary of a raw adversary. Each
  raw round is parsed before any answer; the inputs that encode typed points are submitted as one
  typed round, the others are answered from a private lazy random oracle whose cache passes from
  the preprocessing phase to the online phase, and each typed answer is completed with the private
  value at its input.

## Main statements

* `PointerChainPuzzle.LeanSeal.hashInput_injective`, `route_hashInput`, `route_eq_none_iff`:
  for fewer than `2^32` chains the hash input is injective, and `route` recognizes exactly its
  image; hence `not_clash`: the encoding never clashes.
* `PointerChainPuzzle.LeanSeal.simulateQ_byteScheme_gen`, `simulateQ_byteScheme_solve`: on the
  answers of a byte function the byte-level puzzle is the executable leanSeal of `LeanSeal.lean`.
* `OracleComp.RandomOracleEncoding.isQueryBound_adaptAdversary`: the adapter preserves the
  preprocessing budget and the online budget of rounds and points.
* `OracleComp.RandomOracleEncoding.delayAdvantage_le_delayAdvantage_adaptAdversary`: for an
  encoding without clashes and a raw puzzle whose generator is the typed generator with encoded
  rounds, a raw adversary wins the raw delay experiment with probability at most that of its
  adapted adversary in the typed delay experiment, with the honest generator between the phases.
  `PointerChainPuzzle.LeanSeal.delayAdvantage_byteScheme_le` instantiates it for leanSeal.
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

/-! ## The adversary adapter and the experiment comparison -/

namespace OracleComp.RandomOracleEncoding

open TimeLockPuzzle

/-! ### Auxiliary lemmas -/

@[simp] lemma batchCons_mk_zero {τ : Type} {spec' : OracleSpec τ} {t : τ} {ts : List τ}
    (u : spec'.Range t) (us : spec'.batch.Range ts) (h : 0 < (t :: ts).length) :
    batchCons u us ⟨0, h⟩ = u :=
  rfl

lemma batch_randomOracle_run_bind_cast {ι β : Type} {spec : OracleSpec.{0, 0} ι} [DecidableEq ι]
    [∀ t, SampleableType (spec.Range t)] {l l' : List ι} (h : l = l') (c : spec.QueryCache)
    (f : spec.batch.Range l × spec.QueryCache → ProbComp β) :
    (spec.randomOracle.batch l).run c >>= f =
      (spec.randomOracle.batch l').run c >>= fun y => f (cast (by rw [h]) y.1, y.2) := by
  subst h
  rfl

lemma run_simulateQ_unifFwdImpl_add_liftM {ι τ α : Type} {spec : OracleSpec.{0, 0} ι}
    {spec' : OracleSpec.{0, 0} τ}
    (ro : QueryImpl spec' (StateT spec.QueryCache ProbComp)) (oa : ProbComp α)
    (c : spec.QueryCache) :
    (simulateQ (unifFwdImpl spec + ro) (liftM oa)).run c = (fun x => (x, c)) <$> oa := by
  rw [show simulateQ (unifFwdImpl spec + ro) (liftM oa) = simulateQ (unifFwdImpl spec) oa from
    QueryImpl.simulateQ_add_liftComp_left (m' := StateT spec.QueryCache ProbComp)
      (unifFwdImpl spec) ro oa]
  exact unifFwdImpl.simulateQ_run oa c

variable {ι D M : Type} {spec : OracleSpec.{0, 0} ι} [SampleableType M]
  [∀ t, SampleableType (spec.Range t)] (E : RandomOracleEncoding spec D M)

/-! ### The adapter -/

/-- The answers to a raw round reassembled from the private values `ps` at its inputs and the
answers `us` to the round of the typed points they encode: at an encoding, the typed answer
completed from the private value, and elsewhere the private value. -/
@[expose]
def assemble : (xs : List D) → (D →ₒ M).batch.Range xs →
    spec.batch.Range (xs.filterMap E.route) → (D →ₒ M).batch.Range xs
  | [], _, _ => batchNil
  | x :: xs, ps, us =>
      match hx : E.route x with
      | none =>
          batchCons (ps ⟨0, by simp⟩) (assemble xs (fun j => ps j.succ)
            (cast (by rw [List.filterMap_cons_none hx]) us))
      | some q =>
          let us' : spec.batch.Range (q :: xs.filterMap E.route) :=
            cast (by rw [List.filterMap_cons_some hx]) us
          batchCons (E.complete q (us' ⟨0, by simp⟩) (ps ⟨0, by simp⟩))
            (assemble xs (fun j => ps j.succ) (fun j => us' j.succ))

lemma assemble_cons_none {x : D} {xs : List D} (hx : E.route x = none)
    (ps : (D →ₒ M).batch.Range (x :: xs)) (us : spec.batch.Range ((x :: xs).filterMap E.route)) :
    E.assemble (x :: xs) ps us = batchCons (ps ⟨0, by simp⟩)
      (E.assemble xs (fun j => ps j.succ) (cast (by rw [List.filterMap_cons_none hx]) us)) := by
  rw [assemble]
  split
  · rfl
  · rename_i heq
    simp [hx] at heq

lemma assemble_cons_some {x : D} {xs : List D} {q : ι} (hx : E.route x = some q)
    (ps : (D →ₒ M).batch.Range (x :: xs)) (us : spec.batch.Range (q :: xs.filterMap E.route)) :
    E.assemble (x :: xs) ps (cast (by rw [List.filterMap_cons_some hx]) us) =
      batchCons (E.complete q (us ⟨0, by simp⟩) (ps ⟨0, by simp⟩))
        (E.assemble xs (fun j => ps j.succ) (fun j => us j.succ)) := by
  rw [assemble]
  split
  · rename_i heq
    simp [hx] at heq
  · rename_i q' hx'
    obtain rfl : q' = q := Option.some_injective _ (hx'.symm.trans hx)
    simp

section adapter

variable [DecidableEq D]

/-- The private lazy random oracle of the adapter at a raw input, flipping local coins of the
typed program. -/
@[expose]
def privateDraw {τ : Type} {spec' : OracleSpec.{0, 0} τ} [MonadLiftT ProbComp (OracleComp spec')]
    (x : D) : StateT (D →ₒ M).QueryCache (OracleComp spec') M :=
  StateT.mk fun pv => liftM (((D →ₒ M).randomOracle x).run pv)

/-- The private lazy random oracle of the adapter at every raw input of a round, in order. -/
@[expose]
def privateDraws {τ : Type} {spec' : OracleSpec.{0, 0} τ} [MonadLiftT ProbComp (OracleComp spec')]
    (xs : List D) : StateT (D →ₒ M).QueryCache (OracleComp spec') ((D →ₒ M).batch.Range xs) :=
  StateT.mk fun pv => liftM (((D →ₒ M).randomOracle.batch xs).run pv)

/-- The preprocessing step of the adapter: a raw input draws its private value; if it is the
encoding of a typed point, the answer is the typed answer there completed from the private value,
and otherwise it is the private value. Uniform queries pass through. -/
@[expose]
def preprocessImpl :
    QueryImpl (unifSpec + (D →ₒ M)) (StateT (D →ₒ M).QueryCache (OracleComp (unifSpec + spec)))
  | .inl k => StateT.lift (liftM ((unifSpec + spec).query (.inl k)))
  | .inr x => do
      let p ← privateDraw x
      match E.route x with
      | some q => (E.complete q · p) <$> StateT.lift (liftM ((unifSpec + spec).query (.inr q)))
      | none => pure p

/-- The online step of the adapter on a raw round: draw the private values of all its inputs,
submit the encoded typed points as one typed round, and reassemble the answers. Uniform queries
pass through. -/
@[expose]
def onlineImpl : QueryImpl (unifSpec + (D →ₒ M).batch)
    (StateT (D →ₒ M).QueryCache (OracleComp (unifSpec + spec.batch)))
  | .inl k => StateT.lift (liftM ((unifSpec + spec.batch).query (.inl k)))
  | .inr xs => do
      let ps ← privateDraws xs
      let us ← StateT.lift (liftM ((unifSpec + spec.batch).query (.inr (xs.filterMap E.route))))
      return E.assemble xs ps us

/-- The typed adversary of a raw adversary: both phases run the raw adversary, answering raw
inputs at encodings through the typed oracles and other raw inputs from a private lazy random
oracle, whose cache passes from the preprocessing phase to the online phase. -/
@[expose]
def adaptAdversary {Puzzle Key : Type} (adv : Adversary (D →ₒ M) Puzzle Key) :
    Adversary spec Puzzle Key where
  State := adv.State × (D →ₒ M).QueryCache
  preprocess := (simulateQ E.preprocessImpl adv.preprocess).run ∅
  online σ puzzle := (simulateQ E.onlineImpl (adv.online σ.1 puzzle)).run' σ.2

/-! ### Budgets -/

omit [∀ t, SampleableType (spec.Range t)] in
lemma isQueryBoundP_liftM_probComp {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftM oa : OracleComp (unifSpec + spec) α) (·.isRight) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
      change IsQueryBoundP (liftComp (liftM (unifSpec.query t) >>= k) (unifSpec + spec))
        (·.isRight) 0
      rw [liftComp_bind, liftComp_query]
      exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp, fun u => by simpa using ih u⟩

lemma isQueryBoundP_preprocessImpl (t : (unifSpec + (D →ₒ M)).Domain)
    (s : (D →ₒ M).QueryCache) :
    IsQueryBoundP ((E.preprocessImpl t).run s) (·.isRight) (if t.isRight then 1 else 0) := by
  rcases t with k | x
  · simp only [preprocessImpl, Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte]
    exact isQueryBoundP_bind_zero _ _ (by simp) fun _ => isQueryBoundP_pure _ _ _
  · simp only [preprocessImpl, Sum.isRight_inr, ↓reduceIte, StateT.run_bind]
    rw [← Nat.zero_add 1]
    refine isQueryBoundP_bind (isQueryBoundP_liftM_probComp _) fun z _ => ?_
    rcases E.route x with _ | q
    · exact (isQueryBoundP_pure _ _ _)
    · simp only [StateT.run_map, StateT.run_lift, isQueryBoundP_map_iff]
      rw [← Nat.add_zero 1]
      exact isQueryBoundP_bind (by simp) fun _ _ => isQueryBoundP_pure _ _ _

lemma isOnlineQueryBound_onlineImpl (t : (unifSpec + (D →ₒ M).batch).Domain)
    (s : (D →ₒ M).QueryCache) :
    IsOnlineQueryBound ((E.onlineImpl t).run s) (onlineStep t) := by
  rcases t with k | xs
  · simp only [onlineImpl, onlineStep_inl, StateT.run_lift]
    exact (isOnlineQueryBound_query_bind_inl_iff _ _ _).2 fun _ => isOnlineQueryBound_pure _ _
  · simp only [onlineImpl, onlineStep_inr, StateT.run_bind]
    refine isOnlineQueryBound_bind_le (0, 0) (1, xs.length) (isOnlineQueryBound_liftComp _ _)
      (fun z => ?_) ⟨by omega, by omega⟩
    rw [StateT.run_lift, bind_assoc]
    refine isOnlineQueryBound_bind_le (1, xs.length) (0, 0) ?_ (fun _ => ?_) ⟨le_rfl, le_rfl⟩
    · rw [IsOnlineQueryBound, isQueryBound_query_iff]
      simp [List.length_filterMap_le]
    · simp only [pure_bind, StateT.run_pure]
      exact isOnlineQueryBound_pure _ _

/-- **The adapter preserves the budgets.** If a raw adversary makes at most `Q` preprocessing
queries and its online phase submits at most `b.1` rounds holding at most `b.2` points, so does
its typed adversary: each raw query or round becomes at most one typed query or round with at
most as many points, and raw inputs that encode no typed point cost nothing. -/
theorem isQueryBound_adaptAdversary {Puzzle Key : Type} {adv : Adversary (D →ₒ M) Puzzle Key}
    {Q : ℕ} {b : ℕ × ℕ} (h : adv.IsQueryBound Q b) : (E.adaptAdversary adv).IsQueryBound Q b := by
  refine ⟨h.1.simulateQ_run_StateT_of_step (E.isQueryBoundP_preprocessImpl) ∅, fun σ puzzle => ?_⟩
  have hrun : IsOnlineQueryBound ((simulateQ E.onlineImpl (adv.online σ.1 puzzle)).run σ.2) b :=
    IsQueryBound.simulateQ_run_of_step (combine := (· + ·)) (mapBudget := id)
      (stepBudget := fun t _ => onlineStep t) (h.2 σ.1 puzzle) isOnlineQueryBound_bind
      (fun t _ s _ => E.isOnlineQueryBound_onlineImpl t s)
      (fun t b hb => by
        rcases t with k | xs
        · simp
        · simp only [onlineCanQuery_inr] at hb
          refine Prod.ext ?_ ?_ <;> simp <;> omega) σ.2
  exact (isQueryBound_map_iff _ _ _ _ _).2 hrun

end adapter

/-! ### Comparing the delay experiments -/

/-- The raw interface as part of the combined interface of typed points and raw inputs. -/
@[expose]
def rawLift : QueryImpl (unifSpec + (D →ₒ M)) (OracleComp (unifSpec + (spec + (D →ₒ M))))
  | .inl n => liftM ((unifSpec + (spec + (D →ₒ M))).query (.inl n))
  | .inr x => liftM ((unifSpec + (spec + (D →ₒ M))).query (.inr (.inr x)))

/-- The typed interface as part of the combined interface of typed points and raw inputs. -/
@[expose]
def typedLift : QueryImpl (unifSpec + spec) (OracleComp (unifSpec + (spec + (D →ₒ M))))
  | .inl n => liftM ((unifSpec + (spec + (D →ₒ M))).query (.inl n))
  | .inr t => liftM ((unifSpec + (spec + (D →ₒ M))).query (.inr (.inl t)))

/-- The typed answers to a round read off the raw answers at the encodings of its points. -/
@[expose]
def truncRound (ts : List ι) (us : (D →ₒ M).batch.Range (ts.map E.encode)) :
    spec.batch.Range ts :=
  fun j => E.trunc ts[j] (us ⟨j, by simp⟩)

lemma truncRound_cons (t : ι) (ts : List ι) (u : M)
    (us : (D →ₒ M).batch.Range (ts.map E.encode)) :
    E.truncRound (t :: ts) (batchCons (t := E.encode t) u us) =
      batchCons (E.trunc t u) (E.truncRound ts us) := by
  funext j
  cases j using Fin.cases <;> rfl

/-- The encoding as a translation of rounds: a typed round is the raw round of the encodings of
its points, with every answer truncated. Uniform queries pass through. -/
@[expose]
def roundImpl : QueryImpl (unifSpec + spec.batch) (OracleComp (unifSpec + (D →ₒ M).batch))
  | .inl n => liftM ((unifSpec + (D →ₒ M).batch).query (.inl n))
  | .inr ts => E.truncRound ts <$>
      liftM ((unifSpec + (D →ₒ M).batch).query (.inr (ts.map E.encode)))

/-- The delay experiment of a typed puzzle against a raw adversary, on the combined interface:
the adversary queries raw inputs and the generator queries typed points. Its encoding is the raw
delay experiment of the encoded puzzle, and in the typed world it is the typed delay experiment
of the adapted adversary. -/
@[expose]
def combinedExperiment {Puzzle Key : Type} [DecidableEq Key] (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : Adversary (D →ₒ M) Puzzle Key) : OracleComp (unifSpec + (spec + (D →ₒ M))) Bool := do
  let σ ← simulateQ rawLift adv.preprocess
  let (puzzle, key) ← simulateQ typedLift (simulateQ spec.unbatch tlp.gen)
  let key' ← simulateQ rawLift (simulateQ (D →ₒ M).unbatch (adv.online σ puzzle))
  return decide (key' = key)

lemma simulateQ_encodeImpl_rawLift {α : Type} (oa : OracleComp (unifSpec + (D →ₒ M)) α) :
    simulateQ E.encodeImpl (simulateQ rawLift oa) = oa := by
  rw [QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := QueryImpl.id' _) (fun t => ?_),
    simulateQ_id']
  rcases t with n | x <;> simp [rawLift, encodeImpl]

lemma batch_encodeImpl_typedLift (ts : List ι) :
    QueryImpl.batch (fun t => simulateQ E.encodeImpl (typedLift (.inr t))) ts =
      E.truncRound ts <$> QueryImpl.batch (spec := D →ₒ M)
        (fun x => liftM ((unifSpec + (D →ₒ M)).query (.inr x))) (ts.map E.encode) := by
  induction ts with
  | nil =>
    change _ = E.truncRound [] <$> QueryImpl.batch _ []
    rw [QueryImpl.batch_nil, QueryImpl.batch_nil, map_pure, eq_batchNil (E.truncRound [] batchNil)]
  | cons t ts ih =>
    change _ = E.truncRound (t :: ts) <$> QueryImpl.batch _ (E.encode t :: ts.map E.encode)
    rw [QueryImpl.batch_cons, QueryImpl.batch_cons, ih]
    simp only [typedLift, simulateQ_spec_query, encodeImpl, map_bind, bind_map_left, map_pure,
      truncRound_cons]
    rfl

lemma encodeImpl_compose_typedLift_batch' :
    (E.encodeImpl ∘ₛ typedLift).batch' = (D →ₒ M).unbatch ∘ₛ E.roundImpl := by
  funext t
  rcases t with n | ts
  · simp [typedLift, encodeImpl, roundImpl]
  · simp only [QueryImpl.batch'_apply_inr, QueryImpl.apply_compose, roundImpl, simulateQ_map,
      simulateQ_spec_query, OracleSpec.unbatch_apply_inr]
    exact E.batch_encodeImpl_typedLift ts

/-- The combined experiment encoded into the single raw oracle is the raw delay experiment of a raw
puzzle whose generator is the typed generator translated by `roundImpl`. -/
lemma simulateQ_encodeImpl_combinedExperiment {Puzzle Key : Type} [DecidableEq Key]
    {tlpRaw : TimeLockPuzzle (D →ₒ M) Puzzle Key} {tlp : TimeLockPuzzle spec Puzzle Key}
    (hgen : tlpRaw.gen = simulateQ E.roundImpl tlp.gen) (adv : Adversary (D →ₒ M) Puzzle Key) :
    simulateQ E.encodeImpl (combinedExperiment tlp adv) = tlpRaw.delayExperiment adv := by
  have hg : simulateQ E.encodeImpl (simulateQ typedLift (simulateQ spec.unbatch tlp.gen)) =
      simulateQ (D →ₒ M).unbatch tlpRaw.gen := by
    rw [← QueryImpl.simulateQ_compose, QueryImpl.simulateQ_simulateQ_unbatch,
      encodeImpl_compose_typedLift_batch', QueryImpl.simulateQ_compose, hgen]
  simp only [combinedExperiment, delayExperiment, simulateQ_bind, simulateQ_encodeImpl_rawLift, hg,
    simulateQ_pure]

section typedWorld

variable [DecidableEq ι] [DecidableEq D]

lemma preprocessImpl_run_step (t : (unifSpec + (D →ₒ M)).Domain) (pv : (D →ₒ M).QueryCache)
    (c : spec.QueryCache) :
    (simulateQ spec.romImpl ((E.preprocessImpl t).run pv)).run c =
      (fun z => ((z.1, z.2.2), z.2.1)) <$> ((E.typedImpl ∘ₛ rawLift) t).run (c, pv) := by
  rcases t with n | x
  · simp only [preprocessImpl, rawLift, QueryImpl.apply_compose, simulateQ_spec_query]
    rw [typedImpl_inl_run]
    simp [OracleSpec.romImpl]
  · simp only [preprocessImpl, rawLift, QueryImpl.apply_compose, simulateQ_spec_query,
      typedImpl, QueryImpl.add_apply_inr]
    rw [typedHashImpl_inr_run]
    simp only [privateDraw, StateT.run_bind, StateT.run_mk, simulateQ_bind, StateT.run_bind,
      OracleSpec.simulateQ_romImpl_liftM_run, bind_map_left, map_bind]
    refine bind_congr fun z => ?_
    rcases E.route x with _ | q
    · simp
    · simp [OracleSpec.romImpl]

/-- A raw round answered input by input in the typed world is equal in distribution to drawing
all private values first, then the typed round of the encoded points, and reassembling. -/
lemma batch_typedHashImpl_run (xs : List D) (c : spec.QueryCache) (pv : (D →ₒ M).QueryCache) :
    (QueryImpl.batch (spec := D →ₒ M) (fun x => E.typedHashImpl (.inr x)) xs).run (c, pv) =ᵈ
      ((D →ₒ M).randomOracle.batch xs).run pv >>= fun z =>
        (spec.randomOracle.batch (xs.filterMap E.route)).run c >>= fun y =>
          pure (E.assemble xs z.1 y.1, (y.2, z.2)) := by
  induction xs generalizing c pv with
  | nil => simp [assemble]
  | cons x xs ih =>
    rcases hx : E.route x with _ | q
    · simp only [QueryImpl.batch_cons, StateT.run_bind]
      rw [typedHashImpl_inr_run]
      simp only [hx, bind_assoc, StateT.run_pure, pure_bind]
      refine (EvalDistEq.bind_right _ fun (z : M × (D →ₒ M).QueryCache) =>
        (ih c z.2).bind_left _).trans ?_
      simp only [batch_randomOracle_run_bind_cast (List.filterMap_cons_none hx),
        assemble_cons_none _ hx, bind_assoc, pure_bind, cast_cast, cast_eq, batchCons_mk_zero,
        batchCons_succ]
      exact EvalDistEq.rfl
    · simp only [QueryImpl.batch_cons, StateT.run_bind]
      rw [typedHashImpl_inr_run]
      simp only [hx, bind_assoc, map_eq_bind_pure_comp, Function.comp_apply, StateT.run_pure,
        pure_bind]
      refine (EvalDistEq.bind_right _ fun (z : M × (D →ₒ M).QueryCache) =>
        EvalDistEq.bind_right _ fun (y : spec.Range q × spec.QueryCache) =>
          (ih y.2 z.2).bind_left _).trans ?_
      simp only [batch_randomOracle_run_bind_cast (List.filterMap_cons_some hx),
        assemble_cons_some _ hx, QueryImpl.batch_cons, StateT.run_bind, StateT.run_pure,
        bind_assoc, pure_bind, batchCons_mk_zero, batchCons_succ]
      refine EvalDistEq.bind_right _ fun z => ?_
      exact EvalDistEq.bind_bind_swap _ _ _

lemma typedImpl_compose_rawLift_inr (x : D) :
    (E.typedImpl ∘ₛ rawLift) (.inr x) = E.typedHashImpl (.inr x) := by
  simp only [QueryImpl.apply_compose, rawLift, simulateQ_spec_query, typedImpl,
    QueryImpl.add_apply_inr]

lemma onlineImpl_run_step (t : (unifSpec + (D →ₒ M).batch).Domain) (pv : (D →ₒ M).QueryCache)
    (c : spec.QueryCache) :
    (simulateQ (unifFwdImpl spec + spec.randomOracle.batch) ((E.onlineImpl t).run pv)).run c =ᵈ
      (fun z => ((z.1, z.2.2), z.2.1)) <$> ((E.typedImpl ∘ₛ rawLift).batch' t).run (c, pv) := by
  rcases t with n | xs
  · simp only [onlineImpl, QueryImpl.batch'_apply_inl, QueryImpl.apply_compose, rawLift,
      simulateQ_spec_query]
    rw [typedImpl_inl_run]
    simp [OracleSpec.romImpl]
  · rw [QueryImpl.batch'_apply_inr, show (fun x => (E.typedImpl ∘ₛ rawLift) (.inr x)) =
      fun x => E.typedHashImpl (.inr x) from funext E.typedImpl_compose_rawLift_inr]
    refine EvalDistEq.trans ?_ ((E.batch_typedHashImpl_run xs c pv).map _).symm
    simp [onlineImpl, privateDraws, run_simulateQ_unifFwdImpl_add_liftM]

lemma simulateQ_typedImpl_typedLift_run {α : Type} (oa : OracleComp (unifSpec + spec) α)
    (c : spec.QueryCache) (pv : (D →ₒ M).QueryCache) :
    (simulateQ E.typedImpl (simulateQ typedLift oa)).run (c, pv) =
      (fun z => (z.1, (z.2, pv))) <$> (simulateQ spec.romImpl oa).run c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp
  | query_bind t k ih =>
    have ht : (simulateQ E.typedImpl (typedLift t)).run (c, pv) =
        (fun z => (z.1, (z.2, pv))) <$> (spec.romImpl t).run c := by
      rcases t with n | t
      · simp only [typedLift, simulateQ_spec_query]
        exact typedImpl_inl_run n c pv
      · simp only [typedLift, simulateQ_spec_query]
        exact typedImpl_inr_inl_run t c pv
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, ht, bind_map_left, ih,
      map_bind]

/-- In the typed world, the combined experiment wins with the probability of the typed delay
experiment against the adapted adversary. -/
lemma typedImpl_combinedExperiment_evalDistEq {Puzzle Key : Type} [DecidableEq Key]
    (tlp : TimeLockPuzzle spec Puzzle Key) (adv : Adversary (D →ₒ M) Puzzle Key) :
    Prod.fst <$> (simulateQ E.typedImpl (combinedExperiment tlp adv)).run (∅, ∅) =ᵈ
      (simulateQ spec.romImpl (tlp.delayExperiment (E.adaptAdversary adv))).run' ∅ := by
  have hpre := simulateQ_run_simulateQ_run_evalDistEq spec.romImpl E.preprocessImpl
    (E.typedImpl ∘ₛ rawLift) (fun t s q => by rw [E.preprocessImpl_run_step]) adv.preprocess ∅ ∅
  simp only [combinedExperiment, delayExperiment, adaptAdversary, simulateQ_bind, StateT.run_bind,
    StateT.run'_eq, map_bind]
  refine EvalDistEq.trans ?_ (hpre.bind_left _).symm
  rw [← QueryImpl.simulateQ_compose, bind_map_left]
  refine EvalDistEq.bind_right _ fun z => ?_
  obtain ⟨st, c, pv⟩ := z
  simp only [simulateQ_typedImpl_typedLift_run, bind_map_left, simulateQ_pure, StateT.run_pure,
    map_pure]
  refine EvalDistEq.bind_right _ fun w => ?_
  rw [← QueryImpl.simulateQ_compose, QueryImpl.simulateQ_simulateQ_unbatch, simulateQ_map,
    simulateQ_map, OracleSpec.simulateQ_romImpl_simulateQ_unbatch, StateT.run_map, bind_map_left]
  refine EvalDistEq.trans ?_ ((simulateQ_run_simulateQ_run_evalDistEq _ E.onlineImpl
    (E.typedImpl ∘ₛ rawLift).batch' E.onlineImpl_run_step (adv.online st w.1.1) pv w.2).bind_left
      _).symm
  rw [bind_map_left]

/-- **The raw delay experiment against the typed one.** If the generator of a raw puzzle is the
typed generator with every round translated by `roundImpl`, and the encoding never clashes, a raw
adversary wins the raw delay experiment with probability at most that of its adapted typed
adversary in the typed delay experiment. -/
theorem delayAdvantage_le_delayAdvantage_adaptAdversary {Puzzle Key : Type} [DecidableEq Key]
    {tlpRaw : TimeLockPuzzle (D →ₒ M) Puzzle Key} {tlp : TimeLockPuzzle spec Puzzle Key}
    (hgen : tlpRaw.gen = simulateQ E.roundImpl tlp.gen) (hclash : ∀ c, ¬ E.Clash c)
    (adv : Adversary (D →ₒ M) Puzzle Key) :
    delayAdvantage tlpRaw adv ≤ delayAdvantage tlp (E.adaptAdversary adv) := by
  rw [delayAdvantage_eq, delayAdvantage_eq, ProbCompRuntime.rom_evalDist,
    ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton,
    ← prEvent_eq_evalDist_singleton,
    ← (E.typedImpl_combinedExperiment_evalDistEq tlp adv).prEvent_eq,
    ← E.simulateQ_encodeImpl_combinedExperiment hgen adv, StateT.run'_eq, prEvent_map, prEvent_map]
  refine (E.prEvent_simulateQ_romImpl_encodeImpl_run_le _ (· = true)).trans (le_of_eq ?_)
  simp [hclash]

end typedWorld

end OracleComp.RandomOracleEncoding

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
