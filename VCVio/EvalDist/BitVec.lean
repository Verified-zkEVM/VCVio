/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Monad.Map

/-!
# Evaluation Distributions of Computations with `BitVec`

Lemmas about `probOutput` involving `BitVec`, generic over any monad `m` with `[MonadLiftT m SPMF]`.

The `SampleableType (BitVec n)` instance is defined in
`VCVio.OracleComp.Constructions.SampleableType`.
-/

@[expose] public section

open BitVec

variable {α β γ : Type _} {m : Type _ → Type _} [Monad m] [LawfulMonad m]
  [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadAttach m] [ExactMonadAttach m] [EvalDistCompatible m]

omit [MonadAttach m] [ExactMonadAttach m] [EvalDistCompatible m] in
@[simp, grind =]
lemma probOutput_ofFin_map {n : ℕ} (mx : m (Fin (2 ^ n))) (x : BitVec n) :
    Pr[= x | ofFin <$> mx] = Pr[= toFin x | mx] := by
  have hinj : Function.Injective (ofFin : Fin (2 ^ n) → BitVec n) := fun a b h => by
    simpa only [toFin_ofFin] using congrArg BitVec.toFin h
  simpa only [ofFin_toFin] using probOutput_map_injective mx hinj (toFin x)

omit [MonadAttach m] [ExactMonadAttach m] [EvalDistCompatible m] in
@[simp, grind =]
lemma probOutput_bitVec_toFin_map {n : ℕ} (mx : m (BitVec n)) (x : Fin (2 ^ n)) :
    Pr[= x | toFin <$> mx] = Pr[= ofFin x | mx] := by
  simpa only [toFin_ofFin] using
    probOutput_map_injective mx (fun a b h => by
      simpa only [ofFin_toFin] using congrArg BitVec.ofFin h) (ofFin x)

omit [MonadAttach m] [ExactMonadAttach m] [EvalDistCompatible m] in
@[simp]
lemma probOutput_xor_map {n : ℕ} (mx : m (BitVec n)) (x y : BitVec n) :
    Pr[= y | (x ^^^ ·) <$> mx] = Pr[= x ^^^ y | mx] := by
  have hinj : Function.Injective (x ^^^ ·) := fun a b h => by simpa using congrArg (x ^^^ ·) h
  conv_lhs => rw [show y = x ^^^ (x ^^^ y) by simp]
  exact probOutput_map_injective mx hinj (x ^^^ y)
