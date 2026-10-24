/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Bridge.ImportedScalar
public import Interop.Cryptol.Bridge.Probability

/-!
# From an imported Cryptol function to VCVio clients

An ordinary-import walk-through on Foundation's `sigma_256_0`. The kernel-checked
import is `ImportedScalar.certificate`, and native evaluation of its result certifies
it against VCVio's `ssig0` (`ImportedScalar.compiled`). This file uses the
certificate's function on words, moves an algebraic property and a pre/post contract
across, and swaps it inside every adaptive oracle client.
-/

public section

namespace Cryptol.Consumer.Demo

open Cryptol Cryptol.Bridge OracleComp OracleSpec
open VCVio.Algorithms.Sha2 (ssig0)

/-- The certificate's native function, on 32-bit words. -/
noncomputable def importedSigma (x : UInt32) : UInt32 :=
  UInt32.ofBitVec (ImportedScalar.compiled.implementation x.toBitVec)

/-- It is VCVio's implementation. -/
theorem importedSigma_eq : importedSigma = ssig0 := by
  funext x
  rw [importedSigma, ImportedScalar.compiled, Resolved.dataCertificate_implementation,
    UInt32.ofBitVec_toBitVec, UInt32.ofBitVec_toBitVec]

/-- The lazy meaning of the imported source agrees at every defined input. -/
theorem source_meaning (x : UInt32) :
    DomainResult.applyContinuous
        (Resolved.denote Foundation.wordSource1In Environment.empty)
        (.value (wordValue x.toBitVec)) =
      .value (wordValue (importedSigma x).toBitVec) := by
  rw [ImportedScalar.core_correct, importedSigma_eq]

/-- An algebraic fact proved once about VCVio's implementation. -/
theorem ssig0_xor (x y : UInt32) : ssig0 (x ^^^ y) = ssig0 x ^^^ ssig0 y := by
  apply UInt32.toBitVec_inj.mp
  change (x.toBitVec ^^^ y.toBitVec).rotateRight 7 ^^^
      (x.toBitVec ^^^ y.toBitVec).rotateRight 18 ^^^ ((x.toBitVec ^^^ y.toBitVec) >>> 3) =
    (x.toBitVec.rotateRight 7 ^^^ x.toBitVec.rotateRight 18 ^^^ (x.toBitVec >>> 3)) ^^^
      (y.toBitVec.rotateRight 7 ^^^ y.toBitVec.rotateRight 18 ^^^ (y.toBitVec >>> 3))
  simp only [Expr.bitvec_rotateRight_xor, BitVec.ushiftRight_xor_distrib]
  ac_rfl

/-- The same fact for the imported function, by rewriting. -/
theorem importedSigma_xor (x y : UInt32) :
    importedSigma (x ^^^ y) = importedSigma x ^^^ importedSigma y := by
  rw [importedSigma_eq, ssig0_xor]

/-- A pre/post contract on the imported source, discharged against VCVio. -/
example : DataContract (.word 32) (.word 32)
    (Resolved.denote Foundation.wordSource1In Environment.empty)
    (fun x : BitVec 32 => x = 0) (fun _ (r : BitVec 32) => r = 0) := by
  rw [ImportedScalar.core_contract_iff]
  rintro x rfl
  decide

/-- Any adaptive client may use the imported function in place of `ssig0`. -/
theorem client_eq {α : Type} (client : OracleComp wordSpec α) (calls : Nat) :
    (simulateQ (wordHandler importedSigma) client).run calls =ᵈ
      (simulateQ (wordHandler ssig0) client).run calls := by
  rw [importedSigma_eq]

end Cryptol.Consumer.Demo
