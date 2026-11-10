/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.LeanSealEnvelope
public import VCVio.Schemes.PointerChainPuzzle.Hiding

/-!
# leanSeal's encryption oracles over one random oracle

Time-lock encryption with leanSeal queries SHA-256 at two kinds of inputs: the hash inputs of the
six typed oracles of the puzzle (`VCVio/Schemes/PointerChainPuzzle/LeanSealBridge.lean`), and the
two subkey derivations of the envelope (SPEC §7),
`TH("leanseal/v1/enc", K ‖ η)` and `TH("leanseal/v1/mac", K ‖ η)` for a key `K` and a nonce `η`.
In the typed model the subkeys are two random oracles on `Bytes 32 × Bytes 16` with 32-byte
values, joined to the typed oracles as a summand (`sealSpec` of
`VCVio/Schemes/PointerChainPuzzle/Hiding.lean`, at leanSeal's types `sealTypedSpec`). This file
encodes all eight oracles into the single oracle `byteSpec = ByteArray →ₒ Bytes 32`.

A subkey input is 64 bytes long, `u8(15) ‖ label ‖ K ‖ η`, and its label is neither of the puzzle
labels, so it is no hash input of a typed point (`route_subkeyInput`). The subkey inputs are read
back by their label and two fixed-width fields, kept only if they re-encode to the byte string
(`sealRoute`), as `route` does for the typed points; a subkey answer is the whole 32-byte answer.

The extended encoding never clashing is the byte-level form of the remark in the paper's proof of
the hiding theorem (`app:hiding`) that subkey inputs differ from every other path input because
their labels differ: SHA-256 as one random oracle then answers the eight typed oracles as eight
independent random oracles, which is the model of the typed hiding theorem.

## Main definitions

* `PointerChainPuzzle.LeanSeal.sealTypedSpec`: the oracles of time-lock encryption at leanSeal's
  types.
* `PointerChainPuzzle.LeanSeal.subkeyInput`, `sealInput`: the SHA-256 input of a subkey point, and
  of any point of `sealTypedSpec`.
* `PointerChainPuzzle.LeanSeal.sealRoute`: the point of `sealTypedSpec` a byte string is the input
  of, if any.
* `PointerChainPuzzle.LeanSeal.sealEncoding`: the `RandomOracleEncoding` of `sealTypedSpec` into
  `byteSpec`, truncating mask answers to `b` bytes and keeping every other answer whole.
* `PointerChainPuzzle.LeanSeal.typedSealScheme`, `typedSealDEM`: the typed puzzle over the oracles
  with subkeys, and the typed envelope, at leanSeal's types.

## Main statements

* `sealInput_injective`, `sealRoute_sealInput`, `sealRoute_eq_none_iff`: for fewer than `2^32`
  chains the input map is injective and `sealRoute` recognizes exactly its image; hence
  `not_clash_sealEncoding`: the extended encoding never clashes.
* `byteScheme_gen_eq`: the generator of the byte-level puzzle `byteScheme` is the typed generator
  over the oracles with subkeys, its rounds translated by the extended encoding.
* `byteEnvelope_encrypt_eq`: the encryption of the byte-level envelope `byteEnvelope` is the typed
  envelope's encryption with its two subkey queries sent to their inputs, which are the queries
  of `subkeysQuery`.
-/

public section

open OracleSpec OracleComp TimeLockPuzzle

namespace PointerChainPuzzle.LeanSeal

open Envelope

/-! ## The oracles with subkeys at leanSeal's types -/

/-- The oracles of time-lock encryption with leanSeal's types: the six typed oracles at link width
`b` with `n` chains, and the two subkey oracles on `Bytes 32 × Bytes 16` with 32-byte values. -/
abbrev sealTypedSpec (b n : ℕ) :=
  sealSpec n (Bytes 32) (Bytes b) (Bytes 16) (Bytes 32) (Bytes 16) (Bytes 32)

/-- The points of the two subkey oracles at leanSeal's types: a key and a nonce, for the
encryption subkey (left) or the MAC subkey (right). -/
abbrev SubkeyPoint := Bytes 32 × Bytes 16 ⊕ Bytes 32 × Bytes 16

/-! ## Inputs of the subkey points -/

section Input

/-- The SHA-256 input of a subkey point: that of `TH("leanseal/v1/enc", K ‖ η)` for the
encryption subkey and of `TH("leanseal/v1/mac", K ‖ η)` for the MAC subkey (SPEC §7). -/
@[expose]
def subkeyInput : SubkeyPoint → ByteArray
  | .inl (k, η) => labelled "leanseal/v1/enc" (k.toByteArray ++ η.toByteArray)
  | .inr (k, η) => labelled "leanseal/v1/mac" (k.toByteArray ++ η.toByteArray)

variable {b n : ℕ}

/-- The SHA-256 input of a point of `sealTypedSpec`: `hashInput` at the six typed oracles and
`subkeyInput` at the subkey oracles. -/
@[expose]
def sealInput : (sealTypedSpec b n).Domain → ByteArray
  | .inl t => hashInput t
  | .inr q => subkeyInput q

/-- The subkey point that the bytes `l` would be the input of, read from the length-prefixed
label and the two fixed-width fields without checking the other bytes. -/
@[expose]
def parseSubkey (l : List UInt8) : Option SubkeyPoint :=
  match unlabel l with
  | none => none
  | some (lab, r) =>
      if lab = labelBytes "leanseal/v1/enc" then some (.inl (Bytes.read r 0, Bytes.read r 32))
      else if lab = labelBytes "leanseal/v1/mac" then
        some (.inr (Bytes.read r 0, Bytes.read r 32))
      else none

/-- The point of `sealTypedSpec` a byte string is the input of, if any: a typed point read by
`route`, otherwise a subkey point read by `parseSubkey` and kept only if its input is the byte
string. -/
@[expose]
def sealRoute (x : ByteArray) : Option (sealTypedSpec b n).Domain :=
  match route (b := b) (n := n) x with
  | some t => some (.inl t)
  | none =>
      match parseSubkey x.data.toList with
      | some q => if subkeyInput q = x then some (.inr q) else none
      | none => none

lemma sealInput_of_sealRoute_eq_some {x : ByteArray} {t : (sealTypedSpec b n).Domain}
    (h : sealRoute x = some t) : sealInput t = x := by
  unfold sealRoute at h
  split at h
  · cases h
    exact hashInput_of_route_eq_some (by assumption)
  · split at h
    · split_ifs at h with hx
      cases h
      exact hx
    · cases h

lemma data_toList_subkeyInput_inl (k : Bytes 32) (η : Bytes 16) :
    (subkeyInput (.inl (k, η))).data.toList =
      (15 : UInt8) :: (labelBytes "leanseal/v1/enc" ++ (k.toList ++ η.toList)) := by
  simp only [subkeyInput, data_toList_labelled, String.toUTF8_eq_toByteArray,
    String.size_toByteArray, Nat.toUInt8_eq, ByteArray.data_append, Array.toList_append,
    data_toList_toByteArray, List.cons.injEq, and_true]
  decide

lemma data_toList_subkeyInput_inr (k : Bytes 32) (η : Bytes 16) :
    (subkeyInput (.inr (k, η))).data.toList =
      (15 : UInt8) :: (labelBytes "leanseal/v1/mac" ++ (k.toList ++ η.toList)) := by
  simp only [subkeyInput, data_toList_labelled, String.toUTF8_eq_toByteArray,
    String.size_toByteArray, Nat.toUInt8_eq, ByteArray.data_append, Array.toList_append,
    data_toList_toByteArray, List.cons.injEq, and_true]
  decide

/-- A subkey input is 64 bytes long. -/
lemma size_subkeyInput (q : SubkeyPoint) : (subkeyInput q).size = 64 := by
  rw [← ByteArray.size_data, ← Array.length_toList]
  rcases q with ⟨k, η⟩ | ⟨k, η⟩
  · rw [data_toList_subkeyInput_inl]
    simp [length_labelBytes, show "leanseal/v1/enc".utf8ByteSize = 15 by decide]
  · rw [data_toList_subkeyInput_inr]
    simp [length_labelBytes, show "leanseal/v1/mac".utf8ByteSize = 15 by decide]

/-- A subkey input is read as no typed point: it is 64 bytes long, not 52, and its label is none
of the puzzle labels. -/
lemma parsePoint_subkeyInput (q : SubkeyPoint) :
    parsePoint (b := b) (n := n) (subkeyInput q).data.toList = none := by
  rcases q with ⟨k, η⟩ | ⟨k, η⟩
  · rw [data_toList_subkeyInput_inl, parsePoint]
    simp only [List.length_cons, List.length_append, Bytes.length_toList, length_labelBytes,
      show "leanseal/v1/enc".utf8ByteSize = 15 by decide, Nat.reduceAdd, Nat.reduceEqDiff,
      ↓reduceIte]
    rw [unlabel_cons _ _ _ (by rw [length_labelBytes]; decide)]
    simp only [labelBytes_ne (show "leanseal/v1/enc" ≠ "leanseal/v1/start" by decide),
      labelBytes_ne (show "leanseal/v1/enc" ≠ "leanseal/v1/mask" by decide),
      labelBytes_ne (show "leanseal/v1/enc" ≠ "leanseal/v1/acc" by decide),
      labelBytes_ne (show "leanseal/v1/enc" ≠ "leanseal/v1/key" by decide),
      labelBytes_ne (show "leanseal/v1/enc" ≠ "leanseal/v1/commit" by decide), ↓reduceIte]
  · rw [data_toList_subkeyInput_inr, parsePoint]
    simp only [List.length_cons, List.length_append, Bytes.length_toList, length_labelBytes,
      show "leanseal/v1/mac".utf8ByteSize = 15 by decide, Nat.reduceAdd, Nat.reduceEqDiff,
      ↓reduceIte]
    rw [unlabel_cons _ _ _ (by rw [length_labelBytes]; decide)]
    simp only [labelBytes_ne (show "leanseal/v1/mac" ≠ "leanseal/v1/start" by decide),
      labelBytes_ne (show "leanseal/v1/mac" ≠ "leanseal/v1/mask" by decide),
      labelBytes_ne (show "leanseal/v1/mac" ≠ "leanseal/v1/acc" by decide),
      labelBytes_ne (show "leanseal/v1/mac" ≠ "leanseal/v1/key" by decide),
      labelBytes_ne (show "leanseal/v1/mac" ≠ "leanseal/v1/commit" by decide), ↓reduceIte]

/-- A subkey input is the hash input of no typed point. -/
lemma route_subkeyInput (q : SubkeyPoint) : route (b := b) (n := n) (subkeyInput q) = none := by
  simp [route, parsePoint_subkeyInput]

/-- `parseSubkey` reads every subkey point back from its input. -/
lemma parseSubkey_subkeyInput (q : SubkeyPoint) :
    parseSubkey (subkeyInput q).data.toList = some q := by
  rcases q with ⟨k, η⟩ | ⟨k, η⟩
  · rw [data_toList_subkeyInput_inl, parseSubkey,
      unlabel_cons _ _ _ (by rw [length_labelBytes]; decide)]
    simp [Bytes.read_append_left, Bytes.read_append_right]
  · rw [data_toList_subkeyInput_inr, parseSubkey,
      unlabel_cons _ _ _ (by rw [length_labelBytes]; decide)]
    simp only [labelBytes_ne (show "leanseal/v1/mac" ≠ "leanseal/v1/enc" by decide), ↓reduceIte]
    simp [Bytes.read_append_left, Bytes.read_append_right]

/-- `sealRoute` reads every point of `sealTypedSpec` back from its input, for fewer than `2^32`
chains. -/
theorem sealRoute_sealInput (hn : n < 2 ^ 32) (t : (sealTypedSpec b n).Domain) :
    sealRoute (sealInput t) = some t := by
  rcases t with t | q
  · simp [sealRoute, sealInput, route_hashInput hn]
  · simp [sealRoute, sealInput, route_subkeyInput, parseSubkey_subkeyInput]

/-- **The extended input map is injective.** For fewer than `2^32` chains, distinct points of
`sealTypedSpec` have distinct SHA-256 inputs: subkey inputs are no hash inputs of typed points,
the two subkey labels differ, and the fixed-width payload `K ‖ η` determines the subkey point. -/
theorem sealInput_injective (hn : n < 2 ^ 32) :
    Function.Injective (sealInput (b := b) (n := n)) := fun t t' h =>
  Option.some.inj ((sealRoute_sealInput hn t).symm.trans
    ((congrArg sealRoute h).trans (sealRoute_sealInput hn t')))

/-- `sealRoute` recognizes exactly the inputs of points of `sealTypedSpec`: it returns `none` on
every other byte string. -/
theorem sealRoute_eq_none_iff (hn : n < 2 ^ 32) (x : ByteArray) :
    sealRoute (b := b) (n := n) x = none ↔ ∀ t, sealInput (b := b) (n := n) t ≠ x := by
  refine ⟨fun h t ht => ?_, fun h => ?_⟩
  · subst ht
    simp [sealRoute_sealInput hn] at h
  · cases hr : sealRoute (b := b) (n := n) x with
    | none => rfl
    | some t => exact absurd (sealInput_of_sealRoute_eq_some hr) (h t)

end Input

/-! ## The extended encoding -/

section Encoding

variable {b n : ℕ}

/-- The part of a 32-byte answer that the typed answer at a point of `sealTypedSpec` does not
carry: as for `typedSpec` at a typed point, nothing at a subkey point. -/
@[expose]
def sealTail (b : ℕ) : (sealTypedSpec b n).Domain → Type
  | .inl t => Tail b t
  | .inr _ => Unit

instance (t : (sealTypedSpec b n).Domain) : SampleableType (sealTail b t) :=
  match t with
  | .inl t => inferInstanceAs (SampleableType (Tail b t))
  | .inr _ => inferInstanceAs (SampleableType Unit)

/-- A 32-byte answer split into the typed answer at a point of `sealTypedSpec` and the tail: by
`split` at a typed point, and whole at a subkey point. -/
@[expose]
def sealSplit (hb : b ≤ 32) :
    (t : (sealTypedSpec b n).Domain) → Bytes 32 ≃ (sealTypedSpec b n).Range t × sealTail b t
  | .inl t => split hb t
  | .inr (.inl _) => (Equiv.prodPUnit (Bytes 32)).symm
  | .inr (.inr _) => (Equiv.prodPUnit (Bytes 32)).symm

/-- **The extended encoding** of `sealTypedSpec` into the single oracle `byteSpec`, for a link
width `b ≤ 32` and fewer than `2^32` chains: typed points at their hash inputs, subkey points at
`TH("leanseal/v1/enc" | "leanseal/v1/mac", K ‖ η)`, mask answers truncated to `b` bytes and every
other answer whole. -/
@[expose]
noncomputable def sealEncoding (hb : b ≤ 32) (hn : n < 2 ^ 32) :
    RandomOracleEncoding (sealTypedSpec b n) ByteArray (Bytes 32) :=
  RandomOracleEncoding.ofSplit sealInput sealRoute sealInput_of_sealRoute_eq_some
    (fun t => by rw [sealRoute_sealInput hn]; rfl) (sealSplit hb)

variable (hb : b ≤ 32) (hn : n < 2 ^ 32)

@[simp] lemma sealEncoding_encode : (sealEncoding hb hn).encode = sealInput := rfl

@[simp] lemma sealEncoding_route : (sealEncoding hb hn).route = sealRoute := rfl

@[simp] lemma sealEncoding_trunc_inl (t : TypedPoint b n) (w : Bytes 32) :
    (sealEncoding hb hn).trunc (.inl t) w = truncate t w := by
  cases t <;> rfl

@[simp] lemma sealEncoding_trunc_enc (q : Bytes 32 × Bytes 16) (w : Bytes 32) :
    (sealEncoding hb hn).trunc (.inr (.inl q)) w = w := rfl

@[simp] lemma sealEncoding_trunc_mac (q : Bytes 32 × Bytes 16) (w : Bytes 32) :
    (sealEncoding hb hn).trunc (.inr (.inr q)) w = w := rfl

/-- No two cached points of `sealTypedSpec` share an input: the extended encoding has no clash. -/
theorem not_clash_sealEncoding (c : (sealTypedSpec b n).QueryCache) :
    ¬ (sealEncoding hb hn).Clash c := by
  rintro ⟨q, q', hne, -, -, he⟩
  exact hne (sealInput_injective hn he)

end Encoding

/-! ## The typed scheme and envelope, and the refinements -/

section Refinement

variable {b n : ℕ}

variable (b n) in
/-- The typed time-lock encryption scheme at leanSeal's types: the pointer-chain puzzle at the
context `ctx` with `initAcc = id`, lifted to `sealTypedSpec`. -/
abbrev typedSealScheme (m : ℕ) [NeZero n] :
    TimeLockPuzzle (sealTypedSpec b n) (Puzzle b n) (Bytes 32) :=
  sealScheme n m (ctx b n m) id (Bytes 16) (Bytes 32) (L := Bytes b)

variable (b n) in
/-- The typed envelope at leanSeal's types: HMAC-SHA256, 16-byte nonces encoded as themselves, and
the puzzle encoding of SPEC §6.1. -/
abbrev typedSealDEM (m : ℕ) :
    DEMScheme (OracleComp (unifSpec + sealTypedSpec b n)) (Puzzle b n × Bytes 32) Plaintext
      ByteArray :=
  sealDEM (n := n) (Ctx := Bytes 32) hmacPRF (FixedCodec.bytes 16) (encode m)

/-- A round query whose list is rewritten by an equation, its answer cast back. -/
private lemma map_liftM_query_inr_of_eq {β : Type} {l l' : List ByteArray} (h : l = l')
    (f : byteSpec.batch.Range l → β) :
    f <$> (liftM ((unifSpec + byteSpec.batch).query (.inr l)) :
        OracleComp (unifSpec + byteSpec.batch) _) =
      (fun us : byteSpec.batch.Range l' => f (cast (by rw [h]) us)) <$>
        (liftM ((unifSpec + byteSpec.batch).query (.inr l')) :
          OracleComp (unifSpec + byteSpec.batch) _) := by
  subst h
  rfl

variable (hb : b ≤ 32) (hn : n < 2 ^ 32)

/-- **Generator refinement.** The generator of the byte-level puzzle is the typed generator lifted
to `sealTypedSpec`, its rounds translated by the extended encoding. -/
theorem byteScheme_gen_eq (m : ℕ) [NeZero n] :
    (byteScheme b n m).gen =
      simulateQ (sealEncoding hb hn).roundImpl (typedSealScheme b n m).gen := by
  rw [typedSealScheme, sealScheme, liftSpec, liftComp_def, ← QueryImpl.simulateQ_compose]
  change simulateQ roundImpl _ = _
  congr 1
  funext t
  rcases t with k | ts
  · rfl
  · simp only [roundImpl, QueryImpl.apply_compose]
    change _ = simulateQ (sealEncoding hb hn).roundImpl
      (SubSpec.batchOnResponse (inferInstance : typedSpec b n ⊂ₒ sealTypedSpec b n) ts <$>
        liftM ((unifSpec + (sealTypedSpec b n).batch).query (.inr (ts.map Sum.inl))))
    rw [simulateQ_map, simulateQ_spec_query]
    simp only [RandomOracleEncoding.roundImpl, Functor.map_map]
    have hl : (ts.map Sum.inl).map (sealEncoding hb hn).encode = ts.map hashInput := by
      rw [List.map_map]
      rfl
    rw [map_liftM_query_inr_of_eq hl]
    congr 1
    funext us j
    rw [SubSpec.batchOnResponse_apply]
    simp only [RandomOracleEncoding.truncRound, truncateRound]
    have hcast : ∀ {l l' : List ByteArray} (_ : l = l')
        (hc : byteSpec.batch.Range l' = byteSpec.batch.Range l) (us : byteSpec.batch.Range l')
        (k : ℕ) (hk : k < l.length) (hk' : k < l'.length),
        (cast hc us) ⟨k, hk⟩ = us ⟨k, hk'⟩ := by
      rintro l _ rfl hc us k hk hk'
      rfl
    have htrunc : ∀ {t' : (sealTypedSpec b n).Domain} (_ : t' = .inl ts[j]) (w : Bytes 32)
        (hc : (sealTypedSpec b n).Range t' = (sealTypedSpec b n).Range (.inl ts[j])),
        cast hc ((sealEncoding hb hn).trunc t' w) = truncate ts[j] w := by
      rintro _ rfl w hc
      exact sealEncoding_trunc_inl hb hn _ w
    rw [hcast hl _ us j _ (by simp)]
    exact (htrunc (List.getElem_map ..) _ _).symm

/-- **Encryption refinement.** The encryption of the byte-level envelope is the typed envelope's
encryption with its queries sent to their inputs under the extended encoding: the nonce draw is
the same, the two subkey derivations become the queries of `subkeysQuery`, and nothing else
queries the oracle. -/
theorem byteEnvelope_encrypt_eq (m : ℕ) (key : Puzzle b n × Bytes 32) (msg : Plaintext) :
    (byteEnvelope b n m).encrypt key msg =
      simulateQ ((sealEncoding hb hn).encodeImpl ∘ₛ RandomOracleEncoding.typedLift)
        ((typedSealDEM b n m).encrypt key msg) := by
  have hcoin : simulateQ ((sealEncoding hb hn).encodeImpl ∘ₛ RandomOracleEncoding.typedLift)
      (liftM ($ᵗ Bytes 16) : OracleComp (unifSpec + sealTypedSpec b n) (Bytes 16)) =
        (liftM ($ᵗ Bytes 16) : OracleComp (unifSpec + byteSpec) (Bytes 16)) := by
    rw [← liftComp_eq_liftM, QueryImpl.simulateQ_liftComp_left_eq_of_apply _
      (fun k => (liftM (unifSpec.query k) : OracleComp (unifSpec + byteSpec) _)) (fun k => rfl),
      ← liftComp_def, liftComp_eq_liftM]
  have hderive : ∀ nonce,
      simulateQ ((sealEncoding hb hn).encodeImpl ∘ₛ RandomOracleEncoding.typedLift)
        (liftM (sealDerive (n := n) (L := Bytes b) (Salt := Bytes 16) (Ctx := Bytes 32) key.2
          nonce) : OracleComp (unifSpec + sealTypedSpec b n) _) =
        (liftM (subkeysQuery key.2 nonce) : OracleComp (unifSpec + byteSpec) _) := by
    intro nonce
    rw [← liftComp_eq_liftM]
    refine (QueryImpl.simulateQ_liftComp_right_eq_of_apply (spec₁' := unifSpec)
      (spec₂' := sealTypedSpec b n) _ _ (fun t => rfl) _).trans ?_
    simp only [QueryImpl.apply_compose, RandomOracleEncoding.typedLift,
      RandomOracleEncoding.encodeImpl, sealEncoding_encode, sealDerive, simulateQ_bind,
      simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, subkeysQuery, liftM_bind,
      liftM_map, bind_pure_comp]
    rfl
  simp only [byteEnvelope, typedSealDEM, sealDEM, dem, simulateQ_bind, hcoin, hderive,
    simulateQ_pure]

end Refinement

end PointerChainPuzzle.LeanSeal
