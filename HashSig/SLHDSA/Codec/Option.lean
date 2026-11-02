/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Codec

/-!
# Successful optional canonical signature decoding

A successful optional decode characterizes the entire canonical signature encoding.
-/

public section

namespace SLHDSA

/-- Optional decoding succeeds exactly on the complete canonical encoding of its result. -/
theorem decodeSignature_toOption_eq_some_iff (vp : ValidatedParams)
    {core : CorePrimitives vp.params} (atomic : CoreWireCodec vp.params core)
    (wire : List Byte) (signature : SignatureCore vp.params core) :
    (decodeSignature vp atomic wire).toOption = some signature ↔
      wire = encodeSignature vp atomic signature := by
  rw [← decodeSignature_eq_ok_iff vp atomic wire signature]
  cases decodeSignature vp atomic wire <;> simp [Except.toOption]

end SLHDSA
