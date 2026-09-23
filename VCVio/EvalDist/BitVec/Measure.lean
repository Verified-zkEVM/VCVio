/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.Defs.Measure.Core
public import ToMathlib.MeasureTheory.Measure.UniformTable
public import ToMathlib.MeasureTheory.DiscreteInstances
public import Mathlib.Data.LawfulXor.Equiv

/-!
# Measure laws for XOR on bit vectors

XOR by a fixed bit vector is a permutation. A uniform output measure therefore remains
uniform after XOR, independently of how the original computation was implemented.
-/

public section

open MeasureTheory ProbabilityTheory

universe v

/-- XOR by a constant preserves any computation's uniform bit-vector distribution. -/
theorem evalDist_xor_uniform {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {n : ℕ}
    (mx : m (BitVec n)) (msg : BitVec n)
    (huniform : 𝒟[mx] = uniformOn Set.univ) :
    𝒟[(fun k : BitVec n => msg ^^^ k) <$> mx] = uniformOn Set.univ := by
  rw [evalDist_map_of_discrete, huniform]
  exact uniformOn_univ_map_equiv (Equiv.xor msg)

/-- The right-XOR form used by one-time-pad encryption. -/
theorem evalDist_xor_uniform_right {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {n : ℕ}
    (mx : m (BitVec n)) (msg : BitVec n)
    (huniform : 𝒟[mx] = uniformOn Set.univ) :
    𝒟[(fun k : BitVec n => k ^^^ msg) <$> mx] = uniformOn Set.univ := by
  have hmap : (fun k : BitVec n => k ^^^ msg) = (msg ^^^ ·) := by
    funext k
    exact BitVec.xor_comm k msg
  rw [hmap]
  exact evalDist_xor_uniform mx msg huniform

/-- A message-dependent XOR of an independent uniform key is independent of the message. -/
theorem evalDist_pair_xor_uniform {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] {n : ℕ}
    (mx : m α) (keys : m (BitVec n)) (message : α → BitVec n)
    (hkeys : 𝒟[keys] = uniformOn Set.univ) :
    𝒟[do
      let a ← mx
      let key ← keys
      return (a, message a ^^^ key)] =
        𝒟[mx].prod (uniformOn Set.univ : Measure (BitVec n)) := by
  rw [evalDist_bind_of_discrete]
  have hinner (a : α) :
      𝒟[keys >>= fun key => pure (a, message a ^^^ key)] =
        (uniformOn Set.univ : Measure (BitVec n)).map
          (fun key => (a, message a ^^^ key)) := by
    simpa only [map_eq_bind_pure_comp, Function.comp_def, hkeys] using
      (evalDist_map_of_discrete keys (fun key : BitVec n => (a, message a ^^^ key)))
  simp_rw [hinner]
  exact bind_uniformOn_map_equiv_eq_prod 𝒟[mx] (fun a => Equiv.xor (message a))

/-- Right-XOR form of the independent one-time-pad key law. -/
theorem evalDist_pair_xor_uniform_right {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] {n : ℕ}
    (mx : m α) (keys : m (BitVec n)) (message : α → BitVec n)
    (hkeys : 𝒟[keys] = uniformOn Set.univ) :
    𝒟[do
      let a ← mx
      let key ← keys
      return (a, key ^^^ message a)] =
        𝒟[mx].prod (uniformOn Set.univ : Measure (BitVec n)) := by
  simpa only [BitVec.xor_comm] using evalDist_pair_xor_uniform mx keys message hkeys

/-- A fresh uniform XOR key makes the ciphertext uniform after any lossless message draw. -/
theorem evalDist_bind_xor_uniform {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] {n : ℕ}
    (mx : m α) (keys : m (BitVec n)) (message : α → BitVec n)
    (hmx : 𝒟[mx] Set.univ = 1) (hkeys : 𝒟[keys] = uniformOn Set.univ) :
    𝒟[do
      let a ← mx
      let key ← keys
      return key ^^^ message a] = uniformOn Set.univ := by
  rw [evalDist_bind_of_discrete]
  have hinner (a : α) :
      𝒟[keys >>= fun key => pure (key ^^^ message a)] = uniformOn Set.univ := by
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using
      evalDist_xor_uniform_right keys (message a) hkeys
  simp_rw [hinner]
  rw [Measure.bind_const, hmx, one_smul]
