/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
import all Extern.Falcon.Instance
import all Extern.Falcon.FPR.Verify
import Extern.Falcon.VerifyBridge
public import Extern.Falcon.FPR.Verify
public import LatticeCrypto.Falcon.Security
public import LatticeCrypto.Falcon.Coset

/-!
# Verification correctness at the concrete Falcon primitives

`Falcon.verify_sign_correct` takes two facts about the primitives: the codec round-trips and the
trapdoor sampler lands on the coset. At `Falcon.Concrete.FPRBridge.verifyPrimitives` and
`Falcon.Concrete.concretePrimitives` the codec is the concrete Golomb-Rice codec, whose round-trip
`Falcon.Concrete.decompress_compress` is a theorem, so only the coset condition `hpreimage`
remains. `Falcon.hpreimage_of_landsOnLattice` reduces that condition to the lattice-point
condition `Falcon.LandsOnLattice` on the FFT fields together with the key relations (the
`_of_landsOnLattice` variants), and at `concretePrimitives`, whose FFT fields are the exact packed
FFT, `Falcon.hpreimage_of_exactFFT` discharges it:
`verify_sign_correct_concretePrimitives_of_validKeyPair` needs only a valid key pair with `f`
invertible modulo `q`.

## Byte-level correctness

The two bundles agree on every field `verify` reads, so the abstract verifiers at
`concretePrimitives` and at `FPRBridge.verifyPrimitives` coincide
(`verify_concretePrimitives_eq_verifyPrimitives`). Composing the structured theorem with the
verify bridge `FPRBridge.concrete_verify_eq_verify_of_logn` gives
`concreteVerify_sign_correct_of_validKeyPair`: the executable byte-level verifier
`concreteVerify` accepts the `sigEncode` encoding of every honest signature under the
`publicKeyBytes` encoding of the public key, at every degree `n = 2 ^ logn` with
`2 ≤ logn ≤ 10`. The bridge needs a positive compressed-signature length, which the signer
supplies: its payload is a successful compression (`exists_compress_eq_of_mem_support_sign`),
and a successful compression is a nonempty string of exactly `p.sbytelen` bytes
(`ne_nil_of_compress_eq_some`, `length_eq_of_compress_eq_some`).
-/

public section

open OracleComp OracleSpec Falcon

namespace Falcon.Concrete

/-- Verification correctness at the FPR-backed verification primitives, given only that the
trapdoor sampler lands on the coset. -/
theorem verify_sign_correct_verifyPrimitives
    (p : Params) (hn : p.n = 2 ^ p.logn) (pk : PublicKey p) (sk : SecretKey p)
    (msg : List Byte) (maxAttempts : ℕ) (sig : Signature)
    (hpreimage : ∀ (c : Rq p.n) (x : Rq p.n × Rq p.n),
      x ∈ support ((falconPSF p (FPRBridge.verifyPrimitives p hn)).trapdoorSample pk sk c) →
        (falconPSF p (FPRBridge.verifyPrimitives p hn)).eval pk x = c)
    (hsig : some sig ∈ support (sign p (FPRBridge.verifyPrimitives p hn) pk sk msg maxAttempts)) :
    verify p (FPRBridge.verifyPrimitives p hn) pk msg sig = true :=
  verify_sign_correct p (FPRBridge.verifyPrimitives p hn) pk sk msg maxAttempts sig
    (fun s slen bytes h => decompress_compress p.n s slen bytes h) hpreimage hsig

/-- Verification correctness at the concrete primitives bundle, given only that the trapdoor
sampler lands on the coset. -/
theorem verify_sign_correct_concretePrimitives
    (p : Params) (hn : p.n = 2 ^ p.logn) (pk : PublicKey p) (sk : SecretKey p)
    (msg : List Byte) (maxAttempts : ℕ) (sig : Signature)
    (hpreimage : ∀ (c : Rq p.n) (x : Rq p.n × Rq p.n),
      x ∈ support ((falconPSF p (concretePrimitives p hn)).trapdoorSample pk sk c) →
        (falconPSF p (concretePrimitives p hn)).eval pk x = c)
    (hsig : some sig ∈ support (sign p (concretePrimitives p hn) pk sk msg maxAttempts)) :
    verify p (concretePrimitives p hn) pk msg sig = true :=
  verify_sign_correct p (concretePrimitives p hn) pk sk msg maxAttempts sig
    (fun s slen bytes h => decompress_compress p.n s slen bytes h) hpreimage hsig

/-- Verification correctness at the concrete primitives bundle from key validity, invertibility
of `f` modulo `q`, and the lattice-point condition on the FFT conversion fields. -/
theorem verify_sign_correct_concretePrimitives_of_landsOnLattice
    (p : Params) (hn : p.n = 2 ^ p.logn) (pk : PublicKey p) (sk : SecretKey p)
    (hvalid : validKeyPair p pk sk = true)
    (hunit : ∃ u : Rq p.n, negacyclicMul (IntPoly.toRq sk.f) u = 1)
    (hz : ∀ c : Rq p.n, ∀ z ∈ support (Primitives.ffSampling (concretePrimitives p hn)
      p.fftDepth (toFFTTarget p (concretePrimitives p hn) c sk) sk.tree),
      LandsOnLattice p (concretePrimitives p hn) sk z)
    (msg : List Byte) (maxAttempts : ℕ) (sig : Signature)
    (hsig : some sig ∈ support (sign p (concretePrimitives p hn) pk sk msg maxAttempts)) :
    verify p (concretePrimitives p hn) pk msg sig = true := by
  have hpos : 0 < p.n := by rw [hn]; positivity
  have hkey := (validKeyPair_eq_true_iff p pk sk).mp hvalid |>.2
  exact verify_sign_correct_concretePrimitives p hn pk sk msg maxAttempts sig
    (hpreimage_of_landsOnLattice p (concretePrimitives p hn) hpos pk sk hkey
      (capRelation_of_validKeyPair p hpos pk sk hvalid hunit) hz) hsig

/-- The same at the FPR-backed verification primitives. -/
theorem verify_sign_correct_verifyPrimitives_of_landsOnLattice
    (p : Params) (hn : p.n = 2 ^ p.logn) (pk : PublicKey p) (sk : SecretKey p)
    (hvalid : validKeyPair p pk sk = true)
    (hunit : ∃ u : Rq p.n, negacyclicMul (IntPoly.toRq sk.f) u = 1)
    (hz : ∀ c : Rq p.n, ∀ z ∈ support (Primitives.ffSampling (FPRBridge.verifyPrimitives p hn)
      p.fftDepth (toFFTTarget p (FPRBridge.verifyPrimitives p hn) c sk) sk.tree),
      LandsOnLattice p (FPRBridge.verifyPrimitives p hn) sk z)
    (msg : List Byte) (maxAttempts : ℕ) (sig : Signature)
    (hsig : some sig ∈ support
      (sign p (FPRBridge.verifyPrimitives p hn) pk sk msg maxAttempts)) :
    verify p (FPRBridge.verifyPrimitives p hn) pk msg sig = true := by
  have hpos : 0 < p.n := by rw [hn]; positivity
  have hkey := (validKeyPair_eq_true_iff p pk sk).mp hvalid |>.2
  exact verify_sign_correct_verifyPrimitives p hn pk sk msg maxAttempts sig
    (hpreimage_of_landsOnLattice p (FPRBridge.verifyPrimitives p hn) hpos pk sk hkey
      (capRelation_of_validKeyPair p hpos pk sk hvalid hunit) hz) hsig

/-- **Verification correctness at the concrete primitives** from key validity and invertibility
of `f` modulo `q` alone. The coset condition is a theorem at the exact packed FFT
(`hpreimage_of_exactFFT`); `hlogn` excludes the degenerate degree `n = 1`. -/
theorem verify_sign_correct_concretePrimitives_of_validKeyPair
    (p : Params) (hn : p.n = 2 ^ p.logn) (hlogn : 1 ≤ p.logn) (pk : PublicKey p)
    (sk : SecretKey p) (hvalid : validKeyPair p pk sk = true)
    (hunit : ∃ u : Rq p.n, negacyclicMul (IntPoly.toRq sk.f) u = 1)
    (msg : List Byte) (maxAttempts : ℕ) (sig : Signature)
    (hsig : some sig ∈ support (sign p (concretePrimitives p hn) pk sk msg maxAttempts)) :
    verify p (concretePrimitives p hn) pk msg sig = true := by
  have h : 2 * 2 ^ p.fftDepth = p.n := by
    rw [hn, Params.fftDepth, ← pow_succ', Nat.sub_add_cancel hlogn]
  have hpos : 0 < p.n := by rw [hn]; positivity
  have hkey := (validKeyPair_eq_true_iff p pk sk).mp hvalid |>.2
  exact verify_sign_correct_concretePrimitives p hn pk sk msg maxAttempts sig
    (hpreimage_of_exactFFT p (concretePrimitives p hn) h (concretePrimitives_exactFFT p hn h)
      pk sk hkey (capRelation_of_validKeyPair p hpos pk sk hvalid hunit)) hsig

/-! ## Byte-level correctness -/

/-- The abstract verifiers at `concretePrimitives` and at `FPRBridge.verifyPrimitives` coincide:
the two bundles share the decompressor, the hash to the point and the public-key encoder, which
are the only fields `verify` reads. -/
theorem verify_concretePrimitives_eq_verifyPrimitives (p : Params) (hn : p.n = 2 ^ p.logn) :
    verify p (concretePrimitives p hn) = verify p (FPRBridge.verifyPrimitives p hn) := by
  rfl

/-- **Byte-level verification correctness at the concrete primitives.** For a valid key pair with
`f` invertible modulo `q`, the executable verifier `concreteVerify` accepts every signature the
signer at `concretePrimitives` returns, given as its `sigEncode` byte encoding, under the
`publicKeyBytes` byte encoding of the public key. The degree range `2 ≤ logn ≤ 10` is that of
`FPRBridge.concrete_verify_eq_verify_of_logn`; it contains both Falcon parameter sets. -/
theorem concreteVerify_sign_correct_of_validKeyPair
    (p : Params) (hn : p.n = 2 ^ p.logn) (hlo : 2 ≤ p.logn) (hhi : p.logn ≤ 10)
    (pk : PublicKey p) (sk : SecretKey p) (hvalid : validKeyPair p pk sk = true)
    (hunit : ∃ u : Rq p.n, negacyclicMul (IntPoly.toRq sk.f) u = 1)
    (msg : List Byte) (maxAttempts : ℕ) (sig : Signature)
    (hsig : some sig ∈ support (sign p (concretePrimitives p hn) pk sk msg maxAttempts)) :
    concreteVerify p (publicKeyBytes p.logn pk.h) msg
      (sigEncode sig.salt sig.compressedS2 p.logn) = true := by
  have hpos : 0 < p.n := by rw [hn]; positivity
  obtain ⟨s, hcomp⟩ := exists_compress_eq_of_mem_support_sign p _ hsig
  replace hcomp : compress p.n s p.sbytelen = some sig.compressedS2 := hcomp
  have hsbytelen : 0 < p.sbytelen := by
    rw [← length_eq_of_compress_eq_some hcomp]
    exact List.length_pos_iff.mpr (ne_nil_of_compress_eq_some hpos hcomp)
  refine (FPRBridge.concrete_verify_eq_verify_of_logn p hn hsbytelen hlo hhi pk msg sig).trans ?_
  rw [← verify_concretePrimitives_eq_verifyPrimitives]
  exact verify_sign_correct_concretePrimitives_of_validKeyPair p hn (by omega) pk sk hvalid hunit
    msg maxAttempts sig hsig

end Falcon.Concrete

end
