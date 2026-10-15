/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Bridge.Correspondence
public import Interop.Cryptol.Translation.Contracts

/-!
# Pulling rotation specifications and pushing linearity

Imported Foundation properties and a VCVio algebraic law become semantic
claims about the same lowered programs. Arbitrary Lean predicates transport
through the contract API; the exported linearity statement is finite syntax.
-/

public section

namespace Interop.Cryptol.Bridge

open Interop.Cryptol Interop.Cryptol.Finite

/-- The existing pure VCVio implementation distributes over exclusive-or. -/
theorem bsig0_xor (x y : UInt32) :
    VCVio.Algorithms.Sha2.bsig0 (x ^^^ y) =
      VCVio.Algorithms.Sha2.bsig0 x ^^^ VCVio.Algorithms.Sha2.bsig0 y := by
  apply UInt32.toBitVec_inj.mp
  change (x.toBitVec ^^^ y.toBitVec).rotateRight 2 ^^^
    (x.toBitVec ^^^ y.toBitVec).rotateRight 13 ^^^
    (x.toBitVec ^^^ y.toBitVec).rotateRight 22 =
      (x.toBitVec.rotateRight 2 ^^^ x.toBitVec.rotateRight 13 ^^^ x.toBitVec.rotateRight 22) ^^^
      (y.toBitVec.rotateRight 2 ^^^ y.toBitVec.rotateRight 13 ^^^ y.toBitVec.rotateRight 22)
  simp only [Expr.bitvec_rotateRight_xor]
  ac_rfl

/-- Transport VCVio's algebraic property to the actual imported description. -/
theorem sigma_xor (x y : BitVec 32) :
    Foundation.sigma256Zero.evalWord (x ^^^ y) =
      Foundation.sigma256Zero.evalWord x ^^^ Foundation.sigma256Zero.evalWord y := by
  have h := congrArg UInt32.toBitVec (bsig0_xor (UInt32.ofBitVec x) (UInt32.ofBitVec y))
  simp only [← foundationSigma_eq, foundationSigma, UInt32.toBitVec_xor] at h
  exact h

/-- A finite Boolean description of the transported two-input property. -/
@[expose] def linearity : Term [] (.arrow (.word 32) (.arrow (.word 32) .bit)) :=
  .letE Foundation.sigma256Zero (.lam (.lam
    (.wordEq
      (.app (.var (.succ (.succ .zero))) (.wordOp .xor (.var (.succ .zero)) (.var .zero)))
      (.wordOp .xor
        (.app (.var (.succ (.succ .zero))) (.var (.succ .zero)))
        (.app (.var (.succ (.succ .zero))) (.var .zero))))))

/-- The finite exported description is true at all input pairs. -/
theorem linearity_true (x y : BitVec 32) : linearity.denote Env.empty x y = true := by
  change (Foundation.sigma256Zero.evalWord (x ^^^ y) ==
    (Foundation.sigma256Zero.evalWord x ^^^
      Foundation.sigma256Zero.evalWord y)) = true
  rw [sigma_xor]
  exact beq_self_eq_true _

/-- The property remains true when executed in the lazy core. -/
theorem linearity_lower_true (x y : BitVec 32) :
    (Expr.app (.app linearity.lower (.word x)) (.word y)).denote Environment.empty =
      .value ⟨true⟩ := by
  have h := (Term.app (.app linearity (.word x)) (.word y)).lower_correct
    Env.empty Environment.empty envRepresents_empty
  simpa only [Term.lower_app, Term.lower_word, Term.denote_app, Term.denote_word,
    Represents, linearity_true] using h

/-- Pull Foundation's rotation property into a lazy-core assertion. -/
theorem rotateLaw2_lower_true (x : BitVec 32) :
    (Expr.app Foundation.rotateLaw2.lower (.word x)).denote Environment.empty =
      .value ⟨true⟩ := by
  rw [Term.denote_apply_bit, rotateLaw2_true]

/-- Total pre/post specifications transfer in both directions. -/
theorem sigma_contract_iff (pre : BitVec 32 → Prop) (post : BitVec 32 → BitVec 32 → Prop) :
    TotalContract Foundation.sigma256Zero.lower pre post ↔
      ∀ x, pre x → post x (VCVio.Algorithms.Sha2.bsig0 (UInt32.ofBitVec x)).toBitVec := by
  apply Term.totalContract_iff
  intro x
  exact congrArg UInt32.toBitVec (foundationSigma_eq (UInt32.ofBitVec x))

end Interop.Cryptol.Bridge
