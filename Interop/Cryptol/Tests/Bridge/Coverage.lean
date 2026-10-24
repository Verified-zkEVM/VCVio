/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Interop.Cryptol.Bridge.CompressionCertificate
import Interop.Cryptol.Bridge.KeccakCodec
import Interop.Cryptol.Bridge.CRCUpdate
import VCVio.Algorithms.Keccak

/-! # Public declarations named by the Foundation coverage catalogue -/

example := Cryptol.Bridge.compiledCompress_eq
example := Cryptol.Bridge.compression_byte_contract_iff
example := @Cryptol.Bridge.KeccakCodec.offset_val
example := @Cryptol.Bridge.KeccakCodec.toString_toState
example := @Cryptol.Bridge.KeccakCodec.toState_toString
example := Cryptol.Bridge.CRC.encode_append
example := Cryptol.Bridge.CRC.pack_append
example := Cryptol.Bridge.CRC.update_append
example := @Cryptol.Bridge.CRC.finalize_update_append
example := VCVio.Algorithms.Keccak.sha3Digest224
example := VCVio.Algorithms.Keccak.sha3Digest256
example := VCVio.Algorithms.Keccak.sha3Digest384
example := VCVio.Algorithms.Keccak.sha3Digest512
example := VCVio.Algorithms.Keccak.shake128
example := VCVio.Algorithms.Keccak.shake256
example := VCVio.Algorithms.Sha2.compress
example := VCVio.Algorithms.Sha2.sha224
example := VCVio.Algorithms.Sha2.sha256
example := VCVio.Algorithms.Sha2.sha384
example := VCVio.Algorithms.Sha2.sha512
example := VCVio.Algorithms.Sha2.sha512Trunc224
example := VCVio.Algorithms.Sha2.sha512Trunc256
