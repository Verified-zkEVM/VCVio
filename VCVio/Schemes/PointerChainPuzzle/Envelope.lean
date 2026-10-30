/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.LeanSeal
public import VCVio.CryptoFoundations.DataEncapMech
public import VCVio.CryptoFoundations.PRF

/-!
# The leanSeal envelope over abstract primitives

leanSeal encrypts a message under a puzzle and its key as an envelope (SPEC §6.2 and §7): an
encrypt-then-MAC composition of a keyed stream cipher and a MAC, with fresh subkeys for every
nonce. This file writes the envelope once over a nonce type and three abstract primitives:

* a **nonce type** `N` with a fixed-width byte codec `codec : FixedCodec N w`, the `w` bytes the
  envelope carries for the nonce; leanSeal's nonces are 16 bytes, encoded as themselves;
* a **subkey derivation** `derive : Key → N → OracleComp spec (K × K)`, a program over some
  oracles that maps the puzzle key and the nonce to the encryption subkey and the MAC subkey;
  leanSeal answers it with two labelled hashes, and a typed model with two random oracles;
* a **PRF** `prf : PRFScheme K ByteArray (Bytes 32)`, which gives the keystream blocks and the
  tag; leanSeal uses HMAC-SHA256;
* a **puzzle encoding** `encodePuzzle : Puzzle → ByteArray`, the puzzle bytes the envelope carries
  and its tag authenticates.

For a nonce `η` with subkeys `(k_enc, k_mac)`, a message `M` of `L ≤ 2^24` bytes is sealed as

```
E = "LSEN" ‖ u8(1) ‖ 0x000000 ‖ puzzle ‖ encode(η) ‖ be32(L) ‖ (M ⊕ keystream)
envelope = E ‖ prf(k_mac, E)
```

where keystream block `j` is `prf(k_enc, be64(j))`. Opening under a puzzle and its key checks the
header, that the envelope carries exactly the puzzle's bytes, the length field and the total
length, decodes the nonce and derives the subkeys from it, recomputes the tag over every byte
before it and compares; on any mismatch it outputs no plaintext. The tag comparison is an equality
test: constant-time comparison is an implementation property with no counterpart here.

Opening trusts the puzzle bytes and the key it is given. SPEC-conforming use opens under an
already validated puzzle encoding and a key accepted against the puzzle's commitment, and
rejection checks the envelope relative to those values; this file decodes no puzzle and checks no
commitment.

* **Messages.** `Envelope.Plaintext` is the type of byte strings of at most `2^24` bytes, the
  range of the 4-byte length field that SPEC §6.2 allows, so sealing is total and every sealed
  envelope opens. The hiding game's leakage is the length, `fun msg => msg.1.size`.
* **Rejection.** `Envelope.openUnder` returns `Option Plaintext`, `none` on rejection. A
  `DEMScheme` over `OracleComp` has a total `decrypt` and `OracleComp` cannot fail, so the DEM's
  `decrypt` reports a rejection as the empty message; authenticated opening is `openUnder` (and
  `openQuery` over the oracles), and the hiding game uses only `encrypt`.
* **The puzzle is part of the key.** The DEM is keyed by a puzzle together with its key, as in
  `TimeLockPuzzle.hidingExperiment`, and opening accepts only envelopes that carry that puzzle.

## Main definitions

* `PointerChainPuzzle.LeanSeal.FixedCodec`: a fixed-width byte encoding with a decoding that
  inverts it, and `FixedCodec.bytes`, byte strings encoded as themselves.
* `PointerChainPuzzle.LeanSeal.Envelope.sealWith`, `Envelope.sealUnder`: the envelope of a message
  under a nonce and subkeys, respectively a subkey function of the nonce.
* `Envelope.parse`, `Envelope.openFields`, `Envelope.openUnder`: parsing an envelope under known
  puzzle bytes, checking its tag and decrypting, and their composition.
* `Envelope.openQuery`: opening with the subkeys derived by a program over the oracles.
* `Envelope.dem`: the envelope as a `DEMScheme` over `OracleComp (unifSpec + spec)`, keyed by a
  puzzle and its key, whose encryption draws a uniform nonce from local coins.
* `Envelope.subkeysAt`: the subkey function a derivation computes with the oracles answered by a
  fixed table.

## Main statements

* `Envelope.openUnder_sealUnder`: opening a sealed envelope under the same puzzle bytes and subkey
  function returns the message, for every nonce, subkey function and PRF.
* `Envelope.sealWith_eq_sealBy`: `sealWith` is `sealBy` in `Id`, with the PRF under the two subkeys
  as the block and tag functions.
* `Envelope.nodup_map_be_range`: the keystream block counters of a plaintext are distinct.
* `Envelope.map_xorBytes_flatMap_evalDistEq`: the one-time pad on byte strings: XOR with
  independent uniform blocks is distributed as the blocks themselves.
* `Envelope.sealBy_uniform_evalDistEq`: with uniform keystream blocks and tag, the envelopes of
  two messages of the same length have the same distribution.
* `Envelope.simulateQ_dem_encrypt`, `Envelope.simulateQ_dem_decrypt`: with the oracles answered
  by a fixed table, the DEM seals under a uniform nonce and opens with `openUnder`.
* `Envelope.dem_perfectlyCorrect_answerTable`, `Envelope.dem_perfectlyCorrect_rom`: the DEM is
  perfectly correct against every fixed answer table and in the random oracle model.
-/

public section

open OracleSpec OracleComp VCVio.Algorithms

namespace PointerChainPuzzle.LeanSeal

/-! ## Fixed-width codecs -/

/-- A fixed-width byte codec for `N`: an encoding of every value as `w` bytes and a decoding of
`w` bytes, which inverts the encoding and may reject the bytes no value encodes to. -/
structure FixedCodec (N : Type) (w : ℕ) where
  /-- The `w` bytes of a value. -/
  encode : N → Bytes w
  /-- The value with the given bytes, if any. -/
  decode : Bytes w → Option N
  /-- Decoding inverts encoding. -/
  decode_encode : ∀ x, decode (encode x) = some x

attribute [simp] FixedCodec.decode_encode

/-- Byte strings of length `w`, encoded as themselves. -/
@[expose]
def FixedCodec.bytes (w : ℕ) : FixedCodec (Bytes w) w where
  encode x := x
  decode := some
  decode_encode _ := rfl

namespace Envelope

/-! ## The format -/

/-- The largest message length, `2^24` bytes (SPEC §6.2). -/
@[expose]
def maxLength : ℕ := 2 ^ 24

/-- Messages of at most `maxLength` bytes. -/
abbrev Plaintext := {msg : ByteArray // msg.size ≤ maxLength}

instance : Inhabited Plaintext := ⟨⟨ByteArray.empty, by simp [maxLength]⟩⟩

/-- The envelope header: the magic `"LSEN"`, the version `1` and three reserved zero bytes. -/
@[expose]
def header : List UInt8 := [0x4c, 0x53, 0x45, 0x4e, 1, 0, 0, 0]

/-- Bytewise XOR, truncated to the shorter list. -/
@[expose]
def xorBytes (l l' : List UInt8) : List UInt8 := List.zipWith (· ^^^ ·) l l'

variable {K : Type} (prf : PRFScheme K ByteArray (Bytes 32)) {N : Type} {w : ℕ}
  (codec : FixedCodec N w)

/-- The first `len` bytes of the keystream under `k`: the concatenated blocks
`prf.eval k (be64(j))` for `j = 0, 1, …`. -/
@[expose]
def keystream (k : K) (len : ℕ) : List UInt8 :=
  ((List.range ((len + 31) / 32)).flatMap fun j => (prf.eval k (be 8 j)).toList).take len

/-- The envelope bytes before the tag: the header, the puzzle bytes, the encoded nonce, the
ciphertext length in four bytes, and the ciphertext. -/
@[expose]
def signedBytes (pz : ByteArray) (nonce : N) (ct : List UInt8) : List UInt8 :=
  header ++
    (pz.data.toList ++ ((codec.encode nonce).toList ++ (Encoding.natToBytesBE ct.length 4 ++ ct)))

/-- The envelope of `msg` under the puzzle bytes `pz`, the nonce and the subkeys
`(k_enc, k_mac)`: the signed bytes with the ciphertext `msg ⊕ keystream k_enc`, followed by the
tag `prf.eval k_mac` of the signed bytes (SPEC §7). -/
@[expose]
def sealWith (pz : ByteArray) (nonce : N) (ks : K × K) (msg : Plaintext) : ByteArray :=
  let e := signedBytes codec pz nonce (xorBytes msg.1.data.toList (keystream prf ks.1 msg.1.size))
  ⟨(e ++ (prf.eval ks.2 ⟨e.toArray⟩).toList).toArray⟩

/-- The fields of an envelope read under known puzzle bytes, with nonces in `N`. -/
structure Fields (N : Type) where
  /-- The nonce. -/
  nonce : N
  /-- The ciphertext. -/
  ciphertext : List UInt8
  /-- The ciphertext is within the length bound. -/
  length_ciphertext_le : ciphertext.length ≤ maxLength
  /-- Every envelope byte before the tag. -/
  signed : List UInt8
  /-- The tag. -/
  tag : Bytes 32

/-- Parse an envelope that carries the puzzle bytes `pz` (SPEC §6.2): `none` unless it starts
with the header and `pz`, its length field is at most `2^24`, its length is exactly the one the
length field implies, and its nonce bytes decode. -/
@[expose]
def parse (pz env : ByteArray) : Option (Fields N) :=
  let l := env.data.toList
  let rest := l.drop (8 + pz.size)
  let len := beNat ((rest.drop w).take 4)
  if h : l.take (8 + pz.size) = header ++ pz.data.toList ∧ len ≤ maxLength ∧
      rest.length = w + 4 + len + 32 then
    (codec.decode (Bytes.read rest 0)).map fun nonce =>
      { nonce
        ciphertext := (rest.drop (w + 4)).take len
        length_ciphertext_le := by simp only [List.length_take]; omega
        signed := l.take (8 + pz.size + w + 4 + len)
        tag := Bytes.read rest (w + 4 + len) }
  else none

lemma length_data_toList (x : ByteArray) : x.data.toList.length = x.size := Array.length_toList

lemma length_xorBytes (l l' : List UInt8) : (xorBytes l l').length = min l.length l'.length :=
  List.length_zipWith

lemma xorBytes_xorBytes {l l' : List UInt8} (h : l.length ≤ l'.length) :
    xorBytes (xorBytes l l') l' = l := by
  induction l generalizing l' with
  | nil => rfl
  | cons x l ih =>
      cases l' with
      | nil => simp at h
      | cons y l' =>
          simp only [xorBytes, List.zipWith_cons_cons, UInt8.xor_assoc, UInt8.xor_self,
            UInt8.xor_zero, List.cons.injEq, true_and] at ih ⊢
          exact ih (by simpa using h)

lemma xorBytes_append (l u v : List UInt8) :
    xorBytes l (u ++ v) = xorBytes (l.take u.length) u ++ xorBytes (l.drop u.length) v := by
  induction u generalizing l with
  | nil => simp [xorBytes]
  | cons a u ih =>
    cases l with
    | nil => simp [xorBytes]
    | cons c l => simpa [xorBytes] using ih l

lemma xorBytes_take_length (l l' : List UInt8) : xorBytes l (l'.take l.length) = xorBytes l l' := by
  induction l generalizing l' with
  | nil => simp [xorBytes]
  | cons c l ih =>
    cases l' with
    | nil => simp [xorBytes]
    | cons a l' => simpa [xorBytes] using ih l'

/-- XOR of at most `k` bytes `l` with a byte string `x` of length `k` is the first `|l|` bytes of
`x` plus `l` padded with zeros. -/
lemma xorBytes_toList_eq {k : ℕ} (l : List UInt8) (hl : l.length ≤ k) (x : Bytes k) :
    xorBytes l x.toList = (Bytes.read l 0 + x).toList.take l.length := by
  apply List.ext_getElem
  · simp [length_xorBytes, hl]
  · intro i h₁ _
    have hi : i < l.length := by simp [length_xorBytes] at h₁; omega
    simp [xorBytes, Bytes.getElem_toList, Bytes.read, List.getD_eq_getElem?_getD, hi]

@[simp] lemma length_keystream (k : K) (len : ℕ) : (keystream prf k len).length = len := by
  simp only [keystream, List.length_take, List.length_flatMap, Bytes.length_toList,
    List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  omega

/-- Check the tag of parsed fields under the MAC subkey and decrypt under the encryption subkey:
`none` if the tag differs. -/
@[expose]
def openFields (ks : K × K) (f : Fields N) : Option Plaintext :=
  if prf.eval ks.2 ⟨f.signed.toArray⟩ = f.tag then
    some ⟨⟨(xorBytes f.ciphertext (keystream prf ks.1 f.ciphertext.length)).toArray⟩, by
      change (xorBytes _ _).toArray.size ≤ maxLength
      simpa [length_xorBytes] using f.length_ciphertext_le⟩
  else none

/-- Parsing the signed bytes of a ciphertext within the length bound followed by a tag, under the
puzzle bytes they carry, reads back the nonce, the ciphertext, the signed bytes and the tag. -/
lemma parse_signedBytes_append (pz : ByteArray) (nonce : N) (ct : List UInt8)
    (tag : Bytes 32) (hmax : ct.length ≤ maxLength) :
    parse codec pz ⟨(signedBytes codec pz nonce ct ++ tag.toList).toArray⟩ =
      some ⟨nonce, ct, hmax, signedBytes codec pz nonce ct, tag⟩ := by
  have hbe : beNat (Encoding.natToBytesBE ct.length 4) = ct.length := by
    rw [beNat_natToBytesBE, Nat.mod_eq_of_lt]
    exact lt_of_le_of_lt hmax (by decide)
  have hpz : pz.data.toList.length = pz.size := length_data_toList pz
  have hh : header.length = 8 := rfl
  have h4 : (Encoding.natToBytesBE ct.length 4).length = 4 := Encoding.natToBytesBE_length _ _
  have hl : signedBytes codec pz nonce ct ++ tag.toList =
      (header ++ pz.data.toList) ++ ((codec.encode nonce).toList ++
        (Encoding.natToBytesBE ct.length 4 ++ (ct ++ tag.toList))) := by
    simp [signedBytes]
  have hrest : (signedBytes codec pz nonce ct ++ tag.toList).drop (8 + pz.size) =
      (codec.encode nonce).toList ++ (Encoding.natToBytesBE ct.length 4 ++ (ct ++ tag.toList)) := by
    rw [hl, List.drop_left' (by simp [hh, hpz])]
  have hfield : beNat ((List.drop w ((codec.encode nonce).toList ++
      (Encoding.natToBytesBE ct.length 4 ++ (ct ++ tag.toList)))).take 4) = ct.length := by
    rw [List.drop_left' (by simp), List.take_left' h4, hbe]
  have hc1 : (signedBytes codec pz nonce ct ++ tag.toList).take (8 + pz.size) =
      header ++ pz.data.toList := by
    rw [hl, List.take_left' (by simp [hh, hpz])]
  have hc3 : ((codec.encode nonce).toList ++
      (Encoding.natToBytesBE ct.length 4 ++ (ct ++ tag.toList))).length =
      w + 4 + ct.length + 32 := by
    simp [h4]; omega
  simp only [parse, hrest, hfield, hc1, hmax, hc3, and_self, ↓reduceDIte]
  rw [Bytes.read_append_left (off := 0) (by simp), Bytes.read_toList, codec.decode_encode,
    Option.map_some]
  simp only [Option.some.injEq, Fields.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_⟩
  · rw [← List.append_assoc, List.drop_left' (by simp [h4]), List.take_left' rfl]
  · exact List.take_left' (by simp [signedBytes, hh, hpz, h4]; omega)
  · rw [show (codec.encode nonce).toList ++
          (Encoding.natToBytesBE ct.length 4 ++ (ct ++ tag.toList)) =
        ((codec.encode nonce).toList ++ (Encoding.natToBytesBE ct.length 4 ++ ct)) ++
          tag.toList by simp,
      Bytes.read_append_right (by simp [h4]; omega)]
    rw [show w + 4 + ct.length -
        ((codec.encode nonce).toList ++ (Encoding.natToBytesBE ct.length 4 ++ ct)).length = 0
      by simp [h4]; omega, Bytes.read_toList]

lemma length_xorBytes_keystream (k : K) (msg : Plaintext) :
    (xorBytes msg.1.data.toList (keystream prf k msg.1.size)).length = msg.1.size := by
  simp [length_xorBytes]

/-- Parsing an envelope under the puzzle bytes it carries reads back its nonce, its ciphertext,
its signed bytes and its tag. -/
lemma parse_sealWith (pz : ByteArray) (nonce : N) (ks : K × K) (msg : Plaintext) :
    parse codec pz (sealWith prf codec pz nonce ks msg) =
      some ⟨nonce, xorBytes msg.1.data.toList (keystream prf ks.1 msg.1.size),
        (length_xorBytes_keystream prf ks.1 msg).trans_le msg.2,
        signedBytes codec pz nonce (xorBytes msg.1.data.toList (keystream prf ks.1 msg.1.size)),
        prf.eval ks.2 ⟨(signedBytes codec pz nonce
          (xorBytes msg.1.data.toList (keystream prf ks.1 msg.1.size))).toArray⟩⟩ :=
  parse_signedBytes_append codec pz nonce _ _ _

/-- Opening the fields of an envelope sealed under the subkeys `ks` with the same subkeys returns
the message. -/
lemma openFields_sealWith (pz : ByteArray) (nonce : N) (ks : K × K) (msg : Plaintext) :
    ((parse codec pz (sealWith prf codec pz nonce ks msg)).bind fun f => openFields prf ks f) =
      some msg := by
  simp only [parse_sealWith, Option.bind_some, openFields, ite_true, Option.some.injEq]
  refine Subtype.ext ?_
  simp only [length_xorBytes_keystream]
  rw [xorBytes_xorBytes (by simp)]

/-! ## Sealing and opening under a subkey function -/

/-- The envelope of `msg` under the puzzle bytes `pz` and the nonce, with the subkeys `sk nonce`. -/
@[expose]
def sealUnder (sk : N → K × K) (pz : ByteArray) (nonce : N) (msg : Plaintext) : ByteArray :=
  sealWith prf codec pz nonce (sk nonce) msg

/-- Open an envelope under the puzzle bytes `pz` and the subkey function `sk`: parse it, derive
the subkeys from its nonce, check its tag and decrypt. `none` on malformed input relative to `pz`
or a tag mismatch under `sk`; the puzzle bytes and the subkey function are trusted, not checked. -/
@[expose]
def openUnder (sk : N → K × K) (pz env : ByteArray) : Option Plaintext :=
  (parse codec pz env).bind fun f => openFields prf (sk f.nonce) f

/-- Opening a sealed envelope under the same puzzle bytes and subkey function returns the message,
for every nonce. -/
theorem openUnder_sealUnder (sk : N → K × K) (pz : ByteArray) (nonce : N) (msg : Plaintext) :
    openUnder prf codec sk pz (sealUnder prf codec sk pz nonce msg) = some msg := by
  rw [openUnder, sealUnder, ← openFields_sealWith prf codec pz nonce (sk nonce) msg,
    parse_sealWith, Option.bind_some, Option.bind_some]

/-! ## The envelope with monadic PRF evaluations -/

/-- The envelope of `msg` under the puzzle bytes `pz` and the nonce, with the PRF evaluations given
as monadic functions: keystream block `j` is `block (be64(j))`, for each of the `⌈|msg| / 32⌉`
blocks in order, and the tag is `tag` of the signed bytes. `sealWith prf codec` is the case
`block := prf.eval k_enc`, `tag := prf.eval k_mac` in `Id` (`sealWith_eq_sealBy`); a reduction
that answers the two evaluations with oracle queries runs it in `OracleComp`. -/
@[expose]
def sealBy {μ : Type → Type} [Monad μ] (block tag : ByteArray → μ (Bytes 32)) (pz : ByteArray)
    (nonce : N) (msg : Plaintext) : μ ByteArray := do
  let blocks ← (List.range ((msg.1.size + 31) / 32)).mapM fun j => block (be 8 j)
  let ks := (blocks.flatMap fun x => x.toList).take msg.1.size
  let e := signedBytes codec pz nonce (xorBytes msg.1.data.toList ks)
  let t ← tag ⟨e.toArray⟩
  return ⟨(e ++ t.toList).toArray⟩

/-- The envelope under the subkeys `(k_enc, k_mac)` is `sealBy` in `Id` with the block function
`prf.eval k_enc` and the tag function `prf.eval k_mac`. -/
theorem sealWith_eq_sealBy (pz : ByteArray) (nonce : N) (ks : K × K) (msg : Plaintext) :
    sealWith prf codec pz nonce ks msg =
      (sealBy codec (fun x => pure (prf.eval ks.1 x)) (fun x => pure (prf.eval ks.2 x)) pz nonce
        msg : Id ByteArray).run := by
  simp [sealBy, sealWith, keystream, List.flatMap_map]

/-- `sealBy` commutes with monad morphisms: mapping the envelope through a morphism `F` is the
envelope with the block and tag functions mapped through `F`. -/
theorem sealBy_map {μ ν : Type → Type} [Monad μ] [Monad ν] {F : ∀ {α}, μ α → ν α}
    (hF : Cslib.IsMonadHom μ ν F) (block tag : ByteArray → μ (Bytes 32)) (pz : ByteArray)
    (nonce : N) (msg : Plaintext) :
    F (sealBy codec block tag pz nonce msg) =
      sealBy codec (fun x => F (block x)) (fun x => F (tag x)) pz nonce msg := by
  simp only [sealBy, hF.map_bind, hF.map_listMapM, hF.map_pure, Function.comp_def]

/-- The block counters `be 8 i` at which the envelope of a plaintext evaluates the keystream are
distinct: a plaintext has fewer than `256 ^ 8` blocks. -/
theorem nodup_map_be_range (msg : Plaintext) :
    ((List.range ((msg.1.size + 31) / 32)).map (be 8)).Nodup := by
  have hlt : ∀ i ∈ List.range ((msg.1.size + 31) / 32), i ∈ Set.Iio (256 ^ 8) := fun i hi => by
    have := List.mem_range.mp hi
    have := msg.2
    simp only [maxLength] at *
    simp only [Set.mem_Iio]
    omega
  exact List.nodup_range.map_on fun x hx y hy h => be_injOn 8 (hlt x hx) (hlt y hy) h

/-! ## The envelope with uniform blocks and tag -/

/-- **One-time pad on byte strings.** XOR of `l` with the concatenation of independent uniform
byte strings of length `k`, as many as `xs` has entries and at least `|l|` bytes in all, is
distributed as the first `|l|` bytes of the concatenation. -/
theorem map_xorBytes_flatMap_evalDistEq {k : ℕ} {α : Type} (xs : List α) (l : List UInt8)
    (hl : l.length ≤ k * xs.length) :
    (fun bs : List (Bytes k) => xorBytes l (bs.flatMap Bytes.toList)) <$>
        xs.mapM (fun _ => ($ᵗ Bytes k : ProbComp (Bytes k))) =ᵈ
      (fun bs : List (Bytes k) => (bs.flatMap Bytes.toList).take l.length) <$>
        xs.mapM (fun _ => ($ᵗ Bytes k : ProbComp (Bytes k))) := by
  induction xs generalizing l with
  | nil =>
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    simp [xorBytes]
  | cons x xs ih =>
    set M := xs.mapM (fun _ => ($ᵗ Bytes k : ProbComp (Bytes k)))
    set p : Bytes k := Bytes.read (l.take k) 0
    have hA : ∀ b : Bytes k, xorBytes (l.take k) b.toList = (p + b).toList.take l.length := by
      intro b
      rw [xorBytes_toList_eq _ (by simp) b, List.length_take]
      rcases le_total l.length k with h | h
      · rw [min_eq_right h]
      · rw [min_eq_left h]
        change List.take k (p + b).toList = _
        rw [List.take_of_length_le (by simp), List.take_of_length_le (by simp; omega)]
    have hdrop : (l.drop k).length ≤ k * xs.length := by
      simp only [List.length_drop, List.length_cons] at hl ⊢; rw [Nat.mul_succ] at hl; omega
    simp only [List.mapM_cons, map_bind, map_pure, List.flatMap_cons, xorBytes_append,
      Bytes.length_toList, List.take_append]
    calc _ =ᵈ (do
          let b ← ($ᵗ Bytes k : ProbComp (Bytes k))
          let bs ← M
          pure ((p + b).toList.take l.length ++
            (bs.flatMap Bytes.toList).take (l.drop k).length) : ProbComp _) := by
          refine EvalDistEq.bind_right _ fun b => ?_
          rw [hA b]
          simpa only [Functor.map_map, map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Function.comp_def] using
            (ih _ hdrop).map (fun r => (p + b).toList.take l.length ++ r)
      _ =ᵈ (do
          let bs ← M
          let b ← ($ᵗ Bytes k : ProbComp (Bytes k))
          pure ((p + b).toList.take l.length ++
            (bs.flatMap Bytes.toList).take (l.drop k).length) : ProbComp _) :=
          EvalDistEq.bind_bind_swap _ _ _
      _ =ᵈ (do
          let bs ← M
          let b ← ($ᵗ Bytes k : ProbComp (Bytes k))
          pure (b.toList.take l.length ++
            (bs.flatMap Bytes.toList).take (l.drop k).length) : ProbComp _) := by
          refine EvalDistEq.bind_right _ fun bs => ?_
          simpa only [Functor.map_map, map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Function.comp_def] using
            (SampleableType.map_uniformSample_evalDistEq_of_bijective
              (add_right_injective p).bijective_of_finite).map
              (fun b : Bytes k => b.toList.take l.length ++
                (bs.flatMap Bytes.toList).take (l.drop k).length)
      _ =ᵈ _ := by
          refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
          simp only [List.length_drop]
          exact EvalDistEq.rfl

/-- **The envelope with uniform blocks hides the message up to its length.** With every keystream
block and the tag drawn uniformly and independently, the envelopes of two messages of the same
length under the same puzzle bytes and nonce have the same distribution. -/
theorem sealBy_uniform_evalDistEq (pz : ByteArray) (nonce : N) {msg msg' : Plaintext}
    (h : msg.1.size = msg'.1.size) :
    sealBy codec (fun _ => ($ᵗ Bytes 32 : ProbComp (Bytes 32))) (fun _ => $ᵗ Bytes 32) pz nonce
        msg =ᵈ
      sealBy codec (fun _ => ($ᵗ Bytes 32 : ProbComp (Bytes 32))) (fun _ => $ᵗ Bytes 32) pz nonce
        msg' := by
  let M : ℕ → ProbComp (List (Bytes 32)) := fun s =>
    (List.range ((s + 31) / 32)).mapM fun _ => ($ᵗ Bytes 32 : ProbComp (Bytes 32))
  let T : List UInt8 → ProbComp ByteArray := fun ct => do
    let t ← ($ᵗ Bytes 32 : ProbComp (Bytes 32))
    pure ⟨(signedBytes codec pz nonce ct ++ t.toList).toArray⟩
  have key : ∀ m : Plaintext,
      sealBy codec (fun _ => ($ᵗ Bytes 32 : ProbComp (Bytes 32))) (fun _ => $ᵗ Bytes 32) pz nonce
        m =ᵈ ((fun bs : List (Bytes 32) => (bs.flatMap Bytes.toList).take m.1.size) <$>
          M m.1.size) >>= T := by
    intro m
    have hm : m.1.data.toList.length ≤ 32 * (List.range ((m.1.size + 31) / 32)).length := by
      simp only [length_data_toList, List.length_range]; omega
    have := (map_xorBytes_flatMap_evalDistEq _ _ hm).bind_left T
    simp only [length_data_toList] at this
    refine EvalDistEq.trans ?_ this
    simp only [sealBy, bind_map_left, T, ← length_data_toList m.1, xorBytes_take_length]
    exact EvalDistEq.rfl
  exact (key msg).trans (by rw [h]; exact (key msg').symm)

/-! ## The envelope as a DEM -/

section DEM

variable {ι : Type} {spec : OracleSpec ι} {Puzzle Key : Type}

/-- Open an envelope under the puzzle bytes `pz`, deriving the subkeys from its nonce with the
oracle program `derive`: `none` on malformed input relative to `pz` or a tag mismatch, with no
query made on malformed input; the puzzle bytes and the derivation are trusted, not checked. -/
@[expose]
def openQuery (derive : N → OracleComp spec (K × K)) (pz env : ByteArray) :
    OracleComp spec (Option Plaintext) :=
  match parse codec pz env with
  | none => pure none
  | some f => (openFields prf · f) <$> derive f.nonce

variable (f : QueryImpl spec Id)

/-- The subkey function of the derivation `derive'` with its oracles answered by the table `f`. -/
@[expose]
def subkeysAt (derive' : N → OracleComp spec (K × K)) (nonce : N) : K × K :=
  (simulateQ f (derive' nonce)).run

/-- With the oracles answered by the table `f`, opening with `openQuery` is opening under the
subkey function the table gives. -/
lemma simulateQ_openQuery (derive' : N → OracleComp spec (K × K)) (pz env : ByteArray) :
    simulateQ f (openQuery prf codec derive' pz env) =
      pure (openUnder prf codec (subkeysAt f derive') pz env) := by
  unfold openQuery openUnder
  cases parse codec pz env with
  | none => simp
  | some v => simp only [simulateQ_map, Option.bind_some]; rfl

private lemma simulateQ_unifFwdAnswerImpl_liftM_probComp {α : Type} (oa : ProbComp α) :
    simulateQ (unifFwdAnswerImpl f) (liftM oa : OracleComp (unifSpec + spec) α) = oa := by
  simp [unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftM_left]

private lemma simulateQ_unifFwdAnswerImpl_liftM {α : Type} (oa : OracleComp spec α) :
    simulateQ (unifFwdAnswerImpl f) (liftM oa : OracleComp (unifSpec + spec) α) =
      pure (simulateQ f oa).run := by
  simp [unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftM_right]
  rfl

private lemma simulateQ_stateOracle {σ α : Type} (oa : OracleComp (unifSpec + spec) α) :
    simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) +
        fun t => (pure (f t) : StateT σ ProbComp (spec.Range t))) oa =
      liftM (simulateQ (unifFwdAnswerImpl f) oa) := by
  rw [← simulateQ_liftTarget]
  congr 1
  funext t
  rcases t with t | t
  · rfl
  · change (pure (f t) : StateT σ ProbComp (spec.Range t)) =
      liftM (pure (f t) : ProbComp (spec.Range t))
    simp

variable [SampleableType N]

/-- The envelope as a DEM over the oracles `spec` with local coins, keyed by a puzzle together
with its key. Encryption draws a uniform nonce from local coins, derives the subkeys from the key
and the nonce with `derive`, and seals under the puzzle bytes `encodePuzzle puzzle`. Decryption
opens with `openQuery` and reports a rejection as the empty message, since a `DEMScheme` has a
total decryption; `openQuery` and `openUnder` are the authenticated opening. -/
@[expose]
def dem (derive : Key → N → OracleComp spec (K × K)) (encodePuzzle : Puzzle → ByteArray) :
    DEMScheme (OracleComp (unifSpec + spec)) (Puzzle × Key) Plaintext ByteArray where
  encrypt key msg := do
    let nonce ← liftM ($ᵗ N)
    let ks ← liftM (derive key.2 nonce)
    return sealWith prf codec (encodePuzzle key.1) nonce ks msg
  decrypt key env :=
    (fun r => r.getD default) <$>
      liftM (openQuery prf codec (derive key.2) (encodePuzzle key.1) env)

variable (derive : Key → N → OracleComp spec (K × K)) (encodePuzzle : Puzzle → ByteArray)

/-- With local coins kept and the oracles answered by the table `f`, encryption seals under a
uniform nonce with the subkey function the table gives. -/
theorem simulateQ_dem_encrypt (key : Puzzle × Key) (msg : Plaintext) :
    simulateQ (unifFwdAnswerImpl f) ((dem prf codec derive encodePuzzle).encrypt key msg) =
      (fun nonce =>
        sealUnder prf codec (subkeysAt f (derive key.2)) (encodePuzzle key.1) nonce msg) <$>
        ($ᵗ N) := by
  simp only [dem, simulateQ_bind, simulateQ_map, simulateQ_unifFwdAnswerImpl_liftM_probComp,
    simulateQ_unifFwdAnswerImpl_liftM, bind_pure_comp, map_pure]
  rfl

/-- With local coins kept and the oracles answered by the table `f`, decryption opens under the
subkey function the table gives, a rejection read as the empty message. -/
theorem simulateQ_dem_decrypt (key : Puzzle × Key) (env : ByteArray) :
    simulateQ (unifFwdAnswerImpl f) ((dem prf codec derive encodePuzzle).decrypt key env) =
      pure ((openUnder prf codec (subkeysAt f (derive key.2)) (encodePuzzle key.1) env).getD
        default) := by
  simp only [dem, simulateQ_map, simulateQ_unifFwdAnswerImpl_liftM, simulateQ_openQuery, map_pure]
  rfl

/-- With local coins kept and the oracles answered by the table `f`, the correctness experiment
returns `true` on every nonce. -/
theorem simulateQ_dem_correctnessExperiment (key : Puzzle × Key) (msg : Plaintext) :
    simulateQ (unifFwdAnswerImpl f)
        ((dem prf codec derive encodePuzzle).correctnessExperiment key msg) =
      (fun _ => true) <$> ($ᵗ N) := by
  simp only [DEMScheme.correctnessExperiment, simulateQ_bind, simulateQ_dem_encrypt,
    simulateQ_dem_decrypt, simulateQ_pure, bind_map_left, pure_bind, openUnder_sealUnder,
    Option.getD_some, decide_true]
  rw [map_eq_bind_pure_comp]
  rfl

/-- The envelope DEM is perfectly correct when its oracles are answered by a fixed table. -/
theorem dem_perfectlyCorrect_answerTable :
    (dem prf codec derive encodePuzzle).PerfectlyCorrect
      (ProbCompRuntime.withStateOracle
        (fun t => (pure (f t) : StateT Unit ProbComp (spec.Range t))) ()) := by
  intro key msg
  have hrun (x : ProbComp Bool) : (liftM x : StateT Unit ProbComp Bool).run' () = x := by simp
  rw [ProbCompRuntime.withStateOracle_evalDist, simulateQ_stateOracle, hrun,
    simulateQ_dem_correctnessExperiment, ← prEvent_eq_evalDist_singleton]
  refine prEvent_eq_one_of_forall_mem_support _ _ fun y hy => ?_
  rw [support_map] at hy
  obtain ⟨_, _, rfl⟩ := hy
  rfl

/-- The envelope DEM is perfectly correct in the random oracle model, from every initial cache. -/
theorem dem_perfectlyCorrect_rom [DecidableEq ι] [∀ t, SampleableType (spec.Range t)]
    (cache : spec.QueryCache) :
    (dem prf codec derive encodePuzzle).PerfectlyCorrect (ProbCompRuntime.rom spec cache) := by
  intro key msg
  rw [ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton]
  refine prEvent_eq_one_of_forall_mem_support _ _ fun y hy => ?_
  rw [StateT.run'_eq, support_map] at hy
  obtain ⟨⟨y, cache'⟩, hy, rfl⟩ := hy
  obtain ⟨g, -, hg⟩ := (exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff _ cache
    y).2 ⟨cache', hy⟩
  rw [simulateQ_dem_correctnessExperiment, support_map] at hg
  obtain ⟨_, _, rfl⟩ := hg
  rfl

end DEM

end Envelope

end PointerChainPuzzle.LeanSeal
