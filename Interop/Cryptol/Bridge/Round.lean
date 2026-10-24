/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Bridge.Correspondence
public import PolyFunCryptol.Translation.DataCertificate
public import PolyFunCryptol.Model.Laws
import Mathlib.Tactic.FinCases

/-!
# The extracted SHA-256 round and captured lookups

The actual Foundation local round is specialized to a state, constant and
schedule word. Its native interpretation agrees with the helper used by VCVio's
compression loop for every input. Captured lookup specialization is conditional
on the values of `K @ t` and `W @ t`; it does not verify schedule generation.
-/

public section

namespace Cryptol.Bridge

open Cryptol Cryptol.Finite
open VCVio.Algorithms.Sha2

/-- Big sigma one agrees on every input. -/
theorem sigma256One_eq (x : UInt32) :
    Foundation.sigma256One.denote Env.empty x.toBitVec = (bsig1 x).toBitVec := by
  change x.toBitVec.rotateRight 6 ^^^ x.toBitVec.rotateRight 11 ^^^
    x.toBitVec.rotateRight 25 = _
  simp only [bsig1, rotr, UInt32.toBitVec_xor, UInt32.toBitVec_or,
    UInt32.toBitVec_shiftRight, UInt32.toBitVec_shiftLeft, BitVec.rotateRight_def]
  rfl

/-- Small sigma zero agrees on every input. -/
theorem smallSigma256Zero_eq (x : UInt32) :
    Foundation.smallSigma256Zero.denote Env.empty x.toBitVec = (ssig0 x).toBitVec := by
  change x.toBitVec.rotateRight 7 ^^^ x.toBitVec.rotateRight 18 ^^^ (x.toBitVec >>> 3) = _
  simp only [ssig0, rotr, UInt32.toBitVec_xor, UInt32.toBitVec_or,
    UInt32.toBitVec_shiftRight, UInt32.toBitVec_shiftLeft, BitVec.rotateRight_def]
  rfl

/-- Small sigma one agrees on every input. -/
theorem smallSigma256One_eq (x : UInt32) :
    Foundation.smallSigma256One.denote Env.empty x.toBitVec = (ssig1 x).toBitVec := by
  change x.toBitVec.rotateRight 17 ^^^ x.toBitVec.rotateRight 19 ^^^ (x.toBitVec >>> 10) = _
  simp only [ssig1, rotr, UInt32.toBitVec_xor, UInt32.toBitVec_or,
    UInt32.toBitVec_shiftRight, UInt32.toBitVec_shiftLeft, BitVec.rotateRight_def]
  rfl

/-- Choice agrees on every triple of words. -/
theorem choose256_eq (x y z : UInt32) :
    Foundation.choose256.denote Env.empty (x.toBitVec, y.toBitVec, z.toBitVec) =
      (ch x y z).toBitVec := by
  change (x.toBitVec &&& y.toBitVec) ^^^ (~~~x.toBitVec &&& z.toBitVec) = _
  simp [ch]

/-- Majority agrees on every triple of words. -/
theorem majority256_eq (x y z : UInt32) :
    Foundation.majority256.denote Env.empty (x.toBitVec, y.toBitVec, z.toBitVec) =
      (maj x y z).toBitVec := by
  change (x.toBitVec &&& y.toBitVec) ^^^ (x.toBitVec &&& z.toBitVec) ^^^
    (y.toBitVec &&& z.toBitVec) = _
  simp [maj]

/-- The input and output data types of one round. -/
abbrev RoundOutput : Finite.Ty := .seq 8 (.word 32)

/-- Tupled state, round constant and schedule word. -/
abbrev RoundInput : Finite.Ty := .prod RoundOutput (.prod (.word 32) (.word 32))

/-- The eight registers in Foundation's sequence order. -/
@[expose] def stateBits (s : RoundState) : Fin 8 → BitVec 32 :=
  ![s.a.toBitVec, s.b.toBitVec, s.c.toBitVec, s.d.toBitVec,
    s.e.toBitVec, s.f.toBitVec, s.g.toBitVec, s.h.toBitVec]

/-- Construct VCVio's registers from a finite sequence of words. -/
@[expose] def stateOfBits (xs : Fin 8 → BitVec 32) : RoundState :=
  ⟨.ofBitVec (xs 0), .ofBitVec (xs 1), .ofBitVec (xs 2), .ofBitVec (xs 3),
    .ofBitVec (xs 4), .ofBitVec (xs 5), .ofBitVec (xs 6), .ofBitVec (xs 7)⟩

@[simp] theorem stateBits_stateOfBits (xs : Fin 8 → BitVec 32) :
    stateBits (stateOfBits xs) = xs := by
  funext i
  fin_cases i <;> rfl

/-- All states and round words agree with the helper called by `compress`. -/
theorem round256_eq (s : RoundState) (kt wt : UInt32) :
    Foundation.round256.denote Env.empty (stateBits s, kt.toBitVec, wt.toBitVec) =
      stateBits (round256 s kt wt) := by
  rw [Foundation.round256_denote]
  funext i
  fin_cases i <;>
    simp [Foundation.round256Native, stateBits, round256, bsig0, bsig1, rotr, ch, maj,
      BitVec.rotateRight_def]

/-- VCVio's round expressed at the native finite-data boundary. -/
@[expose] def nativeRound (x : RoundInput.Native) : RoundOutput.Native :=
  stateBits (round256 (stateOfBits x.1) (.ofBitVec x.2.1) (.ofBitVec x.2.2))

/-- Native agreement without representation side conditions. -/
theorem round256_native_eq (x : RoundInput.Native) :
    Foundation.round256.denote Env.empty x = nativeRound x := by
  rcases x with ⟨xs, kt, wt⟩
  simpa only [nativeRound, stateBits_stateOfBits, UInt32.toBitVec_ofBitVec] using
    round256_eq (stateOfBits xs) (.ofBitVec kt) (.ofBitVec wt)

/-- The fully defined output shape. -/
@[expose] def roundOutputShape : DataShape RoundOutput := .seq 8 (.word 32)

/-- The fully defined tupled input shape. -/
@[expose] def roundInputShape : DataShape RoundInput :=
  .prod roundOutputShape (.prod (.word 32) (.word 32))

/-- The extracted round at its represented input and output types. -/
@[expose] def roundTerm : Finite.Term [] (.arrow RoundInput RoundOutput) := Foundation.round256

/-- The extracted round's compact source translation, certified against `nativeRound`. -/
@[expose] noncomputable def roundCertificate : DataCertificate roundInputShape roundOutputShape :=
  (Finite.Term.dataCertificate roundInputShape roundOutputShape roundTerm).congr
    fun x => (congrFun (Finite.Term.dataCertificate_implementation _ _ _) x).trans
      (round256_native_eq x)

/-- Arbitrary preconditions and postconditions transfer in either direction. -/
theorem round_contract_iff (pre : RoundInput.Native → Prop)
    (post : RoundInput.Native → RoundOutput.Native → Prop) :
    DataContract roundInputShape roundOutputShape
      (Resolved.denote (roundTerm.source) Environment.empty) pre post ↔
        ∀ x, pre x → post x (nativeRound x) :=
  roundCertificate.contract_iff pre post

/-- Closure conversion restores exactly the two captured lookups of the extracted round. -/
@[expose] def roundCaptured (state : ClosedExpr [] RoundOutput.core)
    (k w : ClosedExpr [] (.seq (.finite 64) (wordTy 32)))
    (t : ClosedExpr [] .integer) : ClosedExpr [] RoundOutput.core :=
  .app Foundation.round256.lower (.pair state (.pair (.index k t) (.index w t)))

/-- Lookup specialization is valid even when the surrounding tables or state are partial. -/
theorem roundCaptured_specialize (state : ClosedExpr [] RoundOutput.core)
    (k w : ClosedExpr [] (.seq (.finite 64) (wordTy 32)))
    (t : ClosedExpr [] .integer) (kt wt : BitVec 32)
    (hk : (Expr.index k t).denote Environment.empty = .value (wordValue kt))
    (hw : (Expr.index w t).denote Environment.empty = .value (wordValue wt)) :
    (roundCaptured state k w t).denote Environment.empty =
      (Expr.app Foundation.round256.lower (.pair state (.pair (.word kt) (.word wt)))).denote
        Environment.empty := by
  unfold roundCaptured
  generalize Foundation.round256.lower = f
  simp only [Expr.denote_app]
  erw [Expr.denote_pair, Expr.denote_pair, Expr.denote_pair, Expr.denote_pair]
  rw [hk, hw, Expr.denote_word, Expr.denote_word]

/-- Total state and lookup hypotheses yield the entire represented VCVio round output. -/
theorem roundCaptured_correct (state : ClosedExpr [] RoundOutput.core)
    (k w : ClosedExpr [] (.seq (.finite 64) (wordTy 32)))
    (t : ClosedExpr [] .integer) (xs : Fin 8 → BitVec 32) (kt wt : BitVec 32)
    (hs : state.denote Environment.empty = encodeData roundOutputShape xs)
    (hk : (Expr.index k t).denote Environment.empty = .value (wordValue kt))
    (hw : (Expr.index w t).denote Environment.empty = .value (wordValue wt)) :
    (roundCaptured state k w t).denote Environment.empty =
      encodeData roundOutputShape (nativeRound (xs, kt, wt)) := by
  rw [roundCaptured_specialize state k w t kt wt hk hw, Expr.denote_app]
  have hi : (Expr.pair state (.pair (.word kt) (.word wt))).denote Environment.empty =
      encodeData roundInputShape (xs, kt, wt) := by
    erw [Expr.denote_pair, Expr.denote_pair]
    rw [hs, Expr.denote_word, Expr.denote_word]
    rfl
  rw [hi, Term.denote_apply_data roundInputShape roundOutputShape,
    round256_native_eq]

end Cryptol.Bridge
