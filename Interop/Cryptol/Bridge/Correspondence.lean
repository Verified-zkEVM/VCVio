/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Bridge.Foundation
public import VCVio.Algorithms.Sha2

/-!
# Foundation and VCVio SHA-256 word correspondence

The source description is generated from Foundation's typed AST. These theorems
relate its total native interpretation, its lowering into the lazy core, and the
existing pure VCVio implementation. They assume no probability or hash security.
-/

public section

namespace Interop.Cryptol.Bridge

open Interop.Cryptol Interop.Cryptol.Finite

/-- The extracted function, executed through the independent source interpreter. -/
@[expose] def foundationSigma (x : UInt32) : UInt32 :=
  UInt32.ofBitVec (Foundation.sigma256Zero.denote Env.empty x.toBitVec)

/-- All 32-bit inputs agree with VCVio's existing implementation. -/
theorem foundationSigma_eq (x : UInt32) : foundationSigma x = VCVio.Algorithms.Sha2.bsig0 x := by
  apply UInt32.toBitVec_inj.mp
  simp only [foundationSigma]
  change x.toBitVec.rotateRight 2 ^^^ x.toBitVec.rotateRight 13 ^^^
    x.toBitVec.rotateRight 22 = _
  simp only [VCVio.Algorithms.Sha2.bsig0, VCVio.Algorithms.Sha2.rotr,
    UInt32.toBitVec_xor, UInt32.toBitVec_or, UInt32.toBitVec_shiftRight,
    UInt32.toBitVec_shiftLeft, BitVec.rotateRight_def]
  rfl

/-- Every bit of the lowered Foundation output represents VCVio's result. -/
theorem sigma256Zero_correct (x : UInt32) :
    (Expr.app Foundation.sigma256Zero.lower (.word x.toBitVec)).denote Environment.empty =
      .value (wordValue (VCVio.Algorithms.Sha2.bsig0 x).toBitVec) := by
  rw [Term.denote_apply_word]
  exact congrArg (fun y : UInt32 => DomainResult.value (wordValue y.toBitVec))
    (foundationSigma_eq x)

/-- Foundation's rotation property at the first SHA-256 rotation. -/
theorem rotateLaw2_true (x : BitVec 32) : Foundation.rotateLaw2.denote Env.empty x = true := by
  change (x.rotateRight 2 == ((x >>> 2) ||| (x <<< 30))) = true
  simp [BitVec.rotateRight_def]

/-- Foundation's rotation property at the second SHA-256 rotation. -/
theorem rotateLaw13_true (x : BitVec 32) : Foundation.rotateLaw13.denote Env.empty x = true := by
  change (x.rotateRight 13 == ((x >>> 13) ||| (x <<< 19))) = true
  simp [BitVec.rotateRight_def]

/-- Foundation's rotation property at the third SHA-256 rotation. -/
theorem rotateLaw22_true (x : BitVec 32) : Foundation.rotateLaw22.denote Env.empty x = true := by
  change (x.rotateRight 22 == ((x >>> 22) ||| (x <<< 10))) = true
  simp [BitVec.rotateRight_def]

end Interop.Cryptol.Bridge
