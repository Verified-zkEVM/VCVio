/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Encoding

/-!
# Complete signature codec guarantees

Canonical encoding fixes the entire signature width, and complete parsing inverts encoding
on every structured signature. The representation equivalence retains every signature field.
-/

public section

namespace SLHDSA.SHAKE128s

/-- FORS tree signatures with equal fields are equal. -/
theorem ForsTreeSignature.ext {left right : ForsTreeSignature}
    (hsecret : left.secret = right.secret)
    (hauthentication : left.authentication = right.authentication) : left = right := by
  cases left
  cases right
  simp_all

/-- XMSS signatures with equal fields are equal. -/
theorem XmssSignature.ext {left right : XmssSignature}
    (hwots : left.wots = right.wots)
    (hauthentication : left.authentication = right.authentication) : left = right := by
  cases left
  cases right
  simp_all

/-- A serialized array of `size` digests has `size * n` bytes. -/
@[simp] theorem digestArrayBytes_length {size : Nat} (values : Fin size → Digest) :
    (digestArrayBytes values).length = size * n := by
  induction size with
  | zero => simp [digestArrayBytes]
  | succ size ih =>
    simp only [digestArrayBytes, List.ofFn_succ, List.flatten_cons, List.length_append,
      Bridge.length_bytesBE]
    change n + (digestArrayBytes (fun i => values i.succ)).length = _
    rw [ih]
    simp [Nat.succ_mul, Nat.add_comm]

/-- Every complete encoded signature has the fixed canonical byte width. -/
@[simp] theorem Signature.toBytes_length (signature : Signature) :
    signature.toBytes.length = signatureBytes := by
  simpa only [Signature.toBytes, Bridge.params_signatureBytes] using
    encodeSignature_length FIPS205.params Bridge.wireCodec (Bridge.sigToCore signature)

/-- Complete parsing returns every encoded structured signature. -/
@[simp] theorem Signature.fromBytes_toBytes (signature : Signature) :
    fromBytes? signature.toBytes = some signature := by
  rw [Signature.toBytes, Bridge.fromBytes?_encodeSignature]
  exact congrArg some (Bridge.signatureEquiv.apply_symm_apply signature)

end SLHDSA.SHAKE128s
