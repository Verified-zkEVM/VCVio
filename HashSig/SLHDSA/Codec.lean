/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Quang Dao
-/

module
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Prod
public import HashSig.SLHDSA.Encoding
public import HashSig.SLHDSA.FipsParams
public import HashSig.SLHDSA.Scheme

/-!
# Strict structured SLH-DSA wire codecs

This module owns the FIPS 205 byte boundary for the canonical structured public keys, secret
keys, and signatures. An abstract primitive context supplies bijections between each atomic
carrier and exactly `n` bytes. The codecs compose those bijections in the normative order

`PK.seed || PK.root`,
`SK.seed || SK.prf || PK.seed || PK.root`, and
`R || k * (FORS.sk || FORS.auth[a]) || d * (WOTS[len] || XMSS.auth[h'])`.

Malformed input is rejected once, at the exact total width, before the resulting intrinsically
shaped value reaches the proof-level algorithms. No unchecked indexing or default padding is
used by the decoder.

## References

- NIST FIPS 205, Figures 16 and 17
- NIST FIPS 205, Algorithms 18--20
-/

@[expose] public section

namespace SLHDSA

/-! ## Compositional exact-width codecs -/

/-- A bijection between a semantic value and exactly `width` bytes. -/
structure WireCodec (α : Type) (width : ℕ) where
  /-- The canonical fixed-width byte representation. -/
  equiv : α ≃ Bytes width

namespace WireCodec

/-- Array-backed vectors are equivalent to functions on their intrinsic finite index. -/
def vectorEquivFin (α : Type) (n : ℕ) : Vector α n ≃ (Fin n → α) where
  toFun := fun xs i => xs[i.val]
  invFun := fun f => Vector.ofFn f
  left_inv := by intro xs; exact Vector.ofFn_getElem
  right_inv := by intro f; funext i; simp

/-- Concatenation is a bijection between two fixed-width byte strings and their combined wire. -/
def appendBytesEquiv (m n : ℕ) : Bytes m × Bytes n ≃ Bytes (m + n) :=
  (Equiv.prodCongr (vectorEquivFin Byte m) (vectorEquivFin Byte n)).trans
    ((Fin.appendEquiv m n).trans (vectorEquivFin Byte (m + n)).symm)

/-- Reinterpret a fixed-width byte string across a proved equality of widths. -/
def castBytesEquiv {m n : ℕ} (h : m = n) : Bytes m ≃ Bytes n where
  toFun := Vector.cast h
  invFun := Vector.cast h.symm
  left_inv := by subst h; intro bytes; rfl
  right_inv := by subst h; intro bytes; rfl

/-- Split a nonempty vector into its first element and remaining elements. -/
def headTailEquiv (α : Type) (count : ℕ) : Vector α (count + 1) ≃ α × Vector α count where
  toFun values := (values[0], Vector.ofFn fun i => values[i.val + 1])
  invFun fields := Vector.ofFn fun i =>
    if h : i.val = 0 then fields.1 else fields.2[i.val - 1]'(by omega)
  left_inv := by
    intro values
    apply Vector.ext
    intro i hi
    by_cases h : i = 0
    · subst i
      simp
    · have hi_pos : 0 < i := Nat.pos_of_ne_zero h
      have hidx : i - 1 + 1 = i := Nat.sub_add_cancel hi_pos
      simp [h, hidx]
  right_inv := by
    intro fields
    apply Prod.ext
    · simp
    · apply Vector.ext
      intro i hi
      simp

/-- Flatten canonically encoded elements recursively in increasing vector-index order.
The recursion ensures that encoding computes each component once, instead of reconstructing an
entire component for every output byte. -/
def repeatBytesEquiv {α : Type} {width : ℕ} (element : α ≃ Bytes width) :
    (count : ℕ) → Vector α count ≃ Bytes (count * width)
  | 0 =>
      { toFun := fun _ => (#v[] : Bytes 0).cast (by simp)
        invFun := fun _ => (Vector.ofFn Fin.elim0 : Vector α 0)
        left_inv := by intro values; apply Vector.ext; omega
        right_inv := by intro bytes; apply Vector.ext; omega }
  | count + 1 =>
      (headTailEquiv α count).trans <|
        (Equiv.prodCongr element (repeatBytesEquiv element count)).trans <|
          (appendBytesEquiv width (count * width)).trans <|
            castBytesEquiv (by ring)

/-- The identity codec for a byte carrier already known to have the required width. -/
def bytes (width : ℕ) : WireCodec (Bytes width) width := ⟨Equiv.refl _⟩

/-- Transport the semantic side of a codec through an equivalence. -/
def precompose {α β : Type} {width : ℕ} (e : α ≃ β) (codec : WireCodec β width) :
    WireCodec α width :=
  ⟨e.trans codec.equiv⟩

/-- Concatenate two canonical codecs. -/
def product {α β : Type} {leftWidth rightWidth : ℕ}
    (left : WireCodec α leftWidth) (right : WireCodec β rightWidth) :
    WireCodec (α × β) (leftWidth + rightWidth) :=
  ⟨(Equiv.prodCongr left.equiv right.equiv).trans
    (appendBytesEquiv leftWidth rightWidth)⟩

/-- Flatten a fixed-size vector of canonically encoded elements. -/
def vector {α : Type} {width : ℕ} (element : WireCodec α width) (count : ℕ) :
    WireCodec (Vector α count) (count * width) :=
  ⟨repeatBytesEquiv element.equiv count⟩

/-- Transport the wire side of a codec through a proved equality of widths. -/
def castWidth {α : Type} {m n : ℕ} (codec : WireCodec α m) (h : m = n) :
    WireCodec α n :=
  ⟨codec.equiv.trans (castBytesEquiv h)⟩

/-- Encode a value to its canonical byte list. -/
def encode {α : Type} {width : ℕ} (codec : WireCodec α width) (value : α) : List Byte :=
  (codec.equiv value).toList

/-- Reject a non-exact input, then decode all bytes into the semantic value. -/
def decode {α : Type} {width : ℕ} (codec : WireCodec α width) (raw : List Byte) :
    Except CodecError α :=
  (decodeExact width raw).map codec.equiv.symm

@[simp] theorem decode_encode {α : Type} {width : ℕ} (codec : WireCodec α width)
    (value : α) : codec.decode (codec.encode value) = .ok value := by
  unfold decode encode
  change Except.map _ (decodeExact width (encodeExact (codec.equiv value))) = _
  rw [decodeExact_encode]
  exact congrArg Except.ok (codec.equiv.symm_apply_apply value)

@[simp] theorem encode_length {α : Type} {width : ℕ} (codec : WireCodec α width)
    (value : α) : (codec.encode value).length = width := by
  simp [encode]

/-- Canonical encodings are injective. -/
theorem encode_injective {α : Type} {width : ℕ} (codec : WireCodec α width) :
    Function.Injective codec.encode := by
  intro left right h
  apply codec.equiv.injective
  apply Vector.toList_inj.mp
  exact h

/-- Every non-exact input is rejected before the semantic equivalence is applied. -/
theorem decode_eq_error_of_length_ne {α : Type} {width : ℕ} (codec : WireCodec α width)
    (raw : List Byte) (h : raw.length ≠ width) :
    codec.decode raw = .error (.invalidLength width raw.length) := by
  rw [decode, decodeExact_eq_error_of_length_ne width raw h]
  rfl

/-- Decoder success is exactly canonical full consumption of the supplied input. -/
theorem decode_eq_ok_iff {α : Type} {width : ℕ} (codec : WireCodec α width)
    (raw : List Byte) (value : α) :
    codec.decode raw = .ok value ↔ raw = codec.encode value := by
  constructor
  · intro h
    unfold decode at h
    cases hbytes : decodeExact width raw with
    | error error =>
        rw [hbytes] at h
        cases h
    | ok bytes =>
        simp only [hbytes, Except.map, Except.ok.injEq] at h
        rw [decodeExact_eq_ok_iff] at hbytes
        rw [hbytes, ← h]
        simp [encode]
  · intro h
    subst raw
    exact decode_encode codec value

end WireCodec

/-! ## Atomic primitive-carrier boundary -/

/-- Exact `n`-byte codecs for every carrier that appears in an SLH-DSA key or signature.
Concrete SHA2 and SHAKE suites instantiate this structure with byte-vector identity codecs. -/
structure CoreWireCodec (p : Params) (core : CorePrimitives p) where
  /-- Codec for `PK.seed`. -/
  pkSeed : WireCodec core.PkSeed p.n
  /-- Codec for `SK.seed`. -/
  skSeed : WireCodec core.SkSeed p.n
  /-- Codec for `SK.prf`. -/
  skPrf : WireCodec core.SkPrf p.n
  /-- Codec for randomizers, WOTS values, FORS values, and tree nodes. -/
  y : WireCodec core.Y p.n

/-! ## FIPS component widths and offsets -/

namespace WireLayout

/-- One FORS tree signature contains one secret node and `a` authentication nodes. -/
def forsTreeBytes (p : Params) : ℕ := (1 + p.a) * p.n

/-- The complete FORS signature contains exactly `k` tree signatures. -/
def forsBytes (p : Params) : ℕ := p.k * forsTreeBytes p

/-- One hypertree layer contains `len` WOTS values and `h'` authentication nodes. -/
def xmssBytes (p : Params) : ℕ := (p.len + p.hp) * p.n

/-- The complete hypertree signature contains exactly `d` XMSS signatures. -/
def hypertreeBytes (p : Params) : ℕ := p.d * xmssBytes p

/-- Byte offset of the message randomizer `R`. -/
def randomnessOffset (_p : Params) : ℕ := 0

/-- Byte offset of the complete FORS signature. -/
def forsOffset (p : Params) : ℕ := p.n

/-- Byte offset of FORS tree signature `tree`. -/
def forsTreeOffset (p : Params) (tree : ℕ) : ℕ := forsOffset p + tree * forsTreeBytes p

/-- Byte offset of the revealed secret in FORS tree `tree`. -/
def forsSecretOffset (p : Params) (tree : ℕ) : ℕ := forsTreeOffset p tree

/-- Byte offset of authentication node `node` in FORS tree `tree`. -/
def forsAuthOffset (p : Params) (tree node : ℕ) : ℕ :=
  forsTreeOffset p tree + (1 + node) * p.n

/-- Byte offset of the complete hypertree signature. -/
def hypertreeOffset (p : Params) : ℕ := forsOffset p + forsBytes p

/-- Byte offset of XMSS signature `layer`. -/
def xmssOffset (p : Params) (layer : ℕ) : ℕ :=
  hypertreeOffset p + layer * xmssBytes p

/-- Byte offset of WOTS chain value `chain` at hypertree `layer`. -/
def wotsOffset (p : Params) (layer chain : ℕ) : ℕ :=
  xmssOffset p layer + chain * p.n

/-- Byte offset of authentication node `node` at hypertree `layer`. -/
def xmssAuthOffset (p : Params) (layer node : ℕ) : ℕ :=
  xmssOffset p layer + (p.len + node) * p.n

/-- For valid parameters, the structured component widths cover exactly the FIPS signature. -/
theorem total_eq_signatureBytes (vp : ValidatedParams) :
    vp.params.n + (forsBytes vp.params + hypertreeBytes vp.params) =
      vp.params.signatureBytes := by
  simp only [Params.signatureBytes, forsBytes, forsTreeBytes, hypertreeBytes, xmssBytes]
  rw [show vp.params.h = vp.params.d * vp.params.hp from vp.valid.h_eq_layers]
  ring

end WireLayout

/-! ## Structured key and signature codecs -/

def publicKeyFieldsEquiv {p : Params} {core : CorePrimitives p} :
    PublicKeyCore core ≃ core.PkSeed × core.Y where
  toFun key := (key.pkSeed, key.pkRoot)
  invFun fields := ⟨fields.1, fields.2⟩
  left_inv := by intro key; cases key; rfl
  right_inv := by intro fields; cases fields; rfl

def secretKeyFieldsEquiv {p : Params} {core : CorePrimitives p} :
    SecretKeyCore core ≃ core.SkSeed × (core.SkPrf × (core.PkSeed × core.Y)) where
  toFun key := (key.skSeed, key.skPrf, key.pkSeed, key.pkRoot)
  invFun fields := ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2⟩
  left_inv := by intro key; cases key; rfl
  right_inv := by intro fields; rcases fields with ⟨_, _, _, _⟩; rfl

def forsTreeFieldsEquiv {p : Params} {core : CorePrimitives p} :
    ForsTreeSigCore p core ≃ core.Y × Vector core.Y p.a where
  toFun signature := (signature.sk, signature.auth)
  invFun fields := ⟨fields.1, fields.2⟩
  left_inv := by intro signature; cases signature; rfl
  right_inv := by intro fields; cases fields; rfl

def xmssFieldsEquiv {p : Params} {core : CorePrimitives p} :
    XmssSigCore p core ≃ Vector core.Y p.len × Vector core.Y p.hp where
  toFun signature := (signature.wots, signature.auth)
  invFun fields := ⟨fields.1, fields.2⟩
  left_inv := by intro signature; cases signature; rfl
  right_inv := by intro fields; cases fields; rfl

def signatureFieldsEquiv {p : Params} {core : CorePrimitives p} :
    SignatureCore p core ≃ core.Y × (ForsSigCore p core × HtSigCore p core) where
  toFun signature := (signature.randomness, signature.fors, signature.hypertree)
  invFun fields := ⟨fields.1, fields.2.1, fields.2.2⟩
  left_inv := by intro signature; cases signature; rfl
  right_inv := by intro fields; rcases fields with ⟨_, _, _⟩; rfl

theorem publicKeyWidth (p : Params) : p.n + p.n = p.publicKeyBytes := by
  simp only [Params.publicKeyBytes]
  omega

theorem secretKeyWidth (p : Params) :
    p.n + (p.n + (p.n + p.n)) = p.secretKeyBytes := by
  simp only [Params.secretKeyBytes]
  omega

theorem forsTreeWidth (p : Params) :
    p.n + p.a * p.n = WireLayout.forsTreeBytes p := by
  simp [WireLayout.forsTreeBytes]
  ring

theorem xmssWidth (p : Params) :
    p.len * p.n + p.hp * p.n = WireLayout.xmssBytes p := by
  simp [WireLayout.xmssBytes]
  ring

/-- Strict codec for `PK.seed || PK.root`. -/
def publicKeyCodec {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core) :
    WireCodec (PublicKeyCore core) p.publicKeyBytes :=
  WireCodec.castWidth
    (WireCodec.precompose publicKeyFieldsEquiv (WireCodec.product atomic.pkSeed atomic.y))
    (publicKeyWidth p)

/-- Strict codec for `SK.seed || SK.prf || PK.seed || PK.root`. -/
def secretKeyCodec {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core) :
    WireCodec (SecretKeyCore core) p.secretKeyBytes :=
  WireCodec.castWidth
    (WireCodec.precompose secretKeyFieldsEquiv
      (WireCodec.product atomic.skSeed
        (WireCodec.product atomic.skPrf (WireCodec.product atomic.pkSeed atomic.y))))
    (secretKeyWidth p)

/-- Strict codec for one `FORS.sk || FORS.auth[a]` tree signature. -/
def forsTreeCodec {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core) :
    WireCodec (ForsTreeSigCore p core) (WireLayout.forsTreeBytes p) :=
  WireCodec.castWidth
    (WireCodec.precompose forsTreeFieldsEquiv
      (WireCodec.product atomic.y (WireCodec.vector atomic.y p.a)))
    (forsTreeWidth p)

/-- Strict codec for all `k` FORS tree signatures in increasing tree order. -/
def forsCodec {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core) :
    WireCodec (ForsSigCore p core) (WireLayout.forsBytes p) :=
  WireCodec.vector (forsTreeCodec atomic) p.k

/-- Strict codec for one `WOTS[len] || XMSS.auth[h']` signature. -/
def xmssCodec {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core) :
    WireCodec (XmssSigCore p core) (WireLayout.xmssBytes p) :=
  WireCodec.castWidth
    (WireCodec.precompose xmssFieldsEquiv
      (WireCodec.product (WireCodec.vector atomic.y p.len)
        (WireCodec.vector atomic.y p.hp)))
    (xmssWidth p)

/-- Strict codec for all `d` XMSS signatures in increasing hypertree-layer order. -/
def hypertreeCodec {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core) :
    WireCodec (HtSigCore p core) (WireLayout.hypertreeBytes p) :=
  WireCodec.vector (xmssCodec atomic) p.d

/-- Strict FIPS Figure 17 codec for the canonical structured signature. -/
def signatureCodec (vp : ValidatedParams) {core : CorePrimitives vp.params}
    (atomic : CoreWireCodec vp.params core) :
    WireCodec (SignatureCore vp.params core) vp.params.signatureBytes :=
  WireCodec.castWidth
    (WireCodec.precompose signatureFieldsEquiv
      (WireCodec.product atomic.y
        (WireCodec.product (forsCodec atomic) (hypertreeCodec atomic))))
    (WireLayout.total_eq_signatureBytes vp)

/-! ## Public checked byte interfaces -/

/-- Encode a canonical structured public key. -/
def encodePublicKey {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core)
    (key : PublicKeyCore core) : List Byte :=
  (publicKeyCodec atomic).encode key

/-- Decode a public key, rejecting every length other than `2n`. -/
def decodePublicKey {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core)
    (raw : List Byte) : Except CodecError (PublicKeyCore core) :=
  (publicKeyCodec atomic).decode raw

/-- Encode a canonical structured secret key. -/
def encodeSecretKey {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core)
    (key : SecretKeyCore core) : List Byte :=
  (secretKeyCodec atomic).encode key

/-- Decode a secret key, rejecting every length other than `4n`. -/
def decodeSecretKey {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core)
    (raw : List Byte) : Except CodecError (SecretKeyCore core) :=
  (secretKeyCodec atomic).decode raw

/-- Encode the canonical structured `R || SIG_FORS || SIG_HT` signature. -/
def encodeSignature (vp : ValidatedParams) {core : CorePrimitives vp.params}
    (atomic : CoreWireCodec vp.params core)
    (signature : SignatureCore vp.params core) : List Byte :=
  (signatureCodec vp atomic).encode signature

/-- Decode a complete signature, rejecting short, long, or partially consumed input. -/
def decodeSignature (vp : ValidatedParams) {core : CorePrimitives vp.params}
    (atomic : CoreWireCodec vp.params core) (raw : List Byte) :
    Except CodecError (SignatureCore vp.params core) :=
  (signatureCodec vp atomic).decode raw

@[simp] theorem decodePublicKey_encode {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) (key : PublicKeyCore core) :
    decodePublicKey atomic (encodePublicKey atomic key) = .ok key := by
  exact WireCodec.decode_encode _ _

@[simp] theorem decodeSecretKey_encode {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) (key : SecretKeyCore core) :
    decodeSecretKey atomic (encodeSecretKey atomic key) = .ok key := by
  exact WireCodec.decode_encode _ _

@[simp] theorem decodeSignature_encode (vp : ValidatedParams)
    {core : CorePrimitives vp.params} (atomic : CoreWireCodec vp.params core)
    (signature : SignatureCore vp.params core) :
    decodeSignature vp atomic (encodeSignature vp atomic signature) = .ok signature := by
  exact WireCodec.decode_encode _ _

/-- Public-key decoding succeeds exactly when the entire input is the canonical encoding. -/
theorem decodePublicKey_eq_ok_iff {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) (raw : List Byte) (key : PublicKeyCore core) :
    decodePublicKey atomic raw = .ok key ↔ raw = encodePublicKey atomic key := by
  exact WireCodec.decode_eq_ok_iff _ _ _

/-- Secret-key decoding succeeds exactly when the entire input is the canonical encoding. -/
theorem decodeSecretKey_eq_ok_iff {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) (raw : List Byte) (key : SecretKeyCore core) :
    decodeSecretKey atomic raw = .ok key ↔ raw = encodeSecretKey atomic key := by
  exact WireCodec.decode_eq_ok_iff _ _ _

/-- Signature decoding succeeds exactly when the entire input is the canonical encoding. -/
theorem decodeSignature_eq_ok_iff (vp : ValidatedParams)
    {core : CorePrimitives vp.params} (atomic : CoreWireCodec vp.params core)
    (raw : List Byte) (signature : SignatureCore vp.params core) :
    decodeSignature vp atomic raw = .ok signature ↔
      raw = encodeSignature vp atomic signature := by
  exact WireCodec.decode_eq_ok_iff _ _ _

/-- Canonical structured public-key encoding is injective. -/
theorem encodePublicKey_injective {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) : Function.Injective (encodePublicKey atomic) :=
  WireCodec.encode_injective _

/-- Canonical structured secret-key encoding is injective. -/
theorem encodeSecretKey_injective {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) : Function.Injective (encodeSecretKey atomic) :=
  WireCodec.encode_injective _

/-- Canonical structured signature encoding is injective. -/
theorem encodeSignature_injective (vp : ValidatedParams)
    {core : CorePrimitives vp.params} (atomic : CoreWireCodec vp.params core) :
    Function.Injective (encodeSignature vp atomic) :=
  WireCodec.encode_injective _

@[simp] theorem encodePublicKey_length {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) (key : PublicKeyCore core) :
    (encodePublicKey atomic key).length = p.publicKeyBytes := by
  exact WireCodec.encode_length _ _

@[simp] theorem encodeSecretKey_length {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) (key : SecretKeyCore core) :
    (encodeSecretKey atomic key).length = p.secretKeyBytes := by
  exact WireCodec.encode_length _ _

@[simp] theorem encodeSignature_length (vp : ValidatedParams)
    {core : CorePrimitives vp.params} (atomic : CoreWireCodec vp.params core)
    (signature : SignatureCore vp.params core) :
    (encodeSignature vp atomic signature).length = vp.params.signatureBytes := by
  exact WireCodec.encode_length _ _

end SLHDSA
