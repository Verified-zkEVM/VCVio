/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

import all Extern.Falcon.Instance
import all LatticeCrypto.Falcon.Concrete.FPR
public import LatticeCrypto.Falcon.Concrete.FPR
public import LatticeCrypto.Falcon.Scheme
public import LatticeCrypto.Falcon.Concrete.Encoding
public import Extern.Falcon.Instance

/-!
# Concrete Falcon verification

`concrete_verify_eq_verify`: the concrete verifier agrees with the abstract one. This module is
independent of the floating-point error bounds.
-/

public section

namespace Falcon.Concrete.FPRBridge

open Falcon.Concrete.FPR

noncomputable section

/-! ## Verification-only concrete primitives -/

/-- Concrete primitive bundle restricted to the fields used by `Falcon.verify`.
The sampler and FFT bridge fields are dummy placeholders because verification never
invokes them. -/
def verifyPrimitives (p : Falcon.Params) (hn : p.n = 2 ^ p.logn) : Falcon.Primitives p where
  publicKeyBytes := fun h => Falcon.Concrete.publicKeyBytes p.logn h
  hashToPoint := fun salt pkBytes msg => Falcon.Concrete.hashToPoint p.n salt pkBytes msg
  samplerZ := fun _ _ => pure 0
  fftTarget := fun _ => 0
  fftInt := fun _ => 0
  ifftRound := fun _ => 0
  compress := Falcon.Concrete.compress p.n
  decompress := Falcon.Concrete.decompress p.n
  nttOps := hn ▸ Falcon.Concrete.concreteNTTRingOps p.logn

/-! ## End-to-end correctness -/

/-- The concrete Falcon verifier agrees with the abstract verifier once the concrete signature
and public-key codecs round-trip. The fast `UInt32`/`Int64` arithmetic kernels are no longer
assumed equal to their specification-level counterparts: that is now discharged by
`Falcon.Concrete.negacyclicMulU32_eq_negacyclicMul` (unconditional) and
`Falcon.Concrete.pairL2NormSqU32_eq_pairL2NormSq` (under the `UInt64` no-overflow bound
`hn_ovf`, which holds with vast headroom for every Falcon degree). The abstract verifier is
instantiated with the same concrete verification fields. -/
theorem concrete_verify_eq_verify
    (p : Falcon.Params) (hn : p.n = 2 ^ p.logn) (hsbytelen : 0 < p.sbytelen)
    (hn_ovf : 2 * p.n * (Falcon.modulus / 2) ^ 2 < 2 ^ 64) (hn4 : 4 ∣ p.n)
    (pk : Falcon.PublicKey p) (msg : List Falcon.Byte) (sig : Falcon.Signature) :
    let prims := verifyPrimitives p hn;
    Falcon.Concrete.concreteVerify p (prims.publicKeyBytes pk.h) msg
      (Falcon.Concrete.sigEncode sig.salt sig.compressedS2 p.logn) =
        Falcon.verify p prims pk msg sig := by
  dsimp
  by_cases hcomp : sig.compressedS2 = []
  · have hdecomp : (verifyPrimitives p hn).decompress [] p.sbytelen = none := by
      simp [verifyPrimitives, Falcon.Concrete.decompress, hsbytelen.ne]
    have hleft :
        Falcon.Concrete.concreteVerify p ((verifyPrimitives p hn).publicKeyBytes pk.h) msg
          (Falcon.Concrete.sigEncode sig.salt [] p.logn) = false := by
      exact Falcon.Concrete.concreteVerify_sigEncode_nil_eq_false p
        ((verifyPrimitives p hn).publicKeyBytes pk.h) sig.salt msg
    have hright : Falcon.verify p (verifyPrimitives p hn) pk msg sig = false := by
      simp [Falcon.verify, hcomp, hdecomp]
    simpa [hcomp] using hleft.trans hright.symm
  · have hsig := Falcon.Concrete.sigDecode_sigEncode sig.salt sig.compressedS2 p.logn hcomp
    have hpk : Falcon.Concrete.pkDecode p.n
        ((Falcon.Concrete.publicKeyBytes p.logn pk.h).extract 1
          (Falcon.Concrete.publicKeyBytes p.logn pk.h).size) = some pk.h := by
      rw [Falcon.Concrete.publicKeyBytes_extract, Falcon.Concrete.pkDecode_pkEncode p.n pk.h hn4]
    simp [Falcon.Concrete.concreteVerify, Falcon.verify,
      hsig, Falcon.Primitives.hashToPointForPublicKey,
      verifyPrimitives, hpk, Falcon.Concrete.negacyclicMulU32_eq_negacyclicMul,
      Falcon.Concrete.pairL2NormSqU32_eq_pairL2NormSq hn_ovf]
    rfl

end

end Falcon.Concrete.FPRBridge
