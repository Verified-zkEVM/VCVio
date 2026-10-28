/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.SignatureAlg
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.WeightedOracle
public import Mathlib.LinearAlgebra.BilinearMap

/-! # Proximity signatures

A message is a vector and a slot. Its hash is the slot's constant base plus the sum of its
coordinate bases weighted by the vector entries. The public key is `x • g₂`; the signature
is `x • H(vector, slot)`. Signing and verification use the same random-oracle cache.

This is the direct scheme from Gurkan's `Signatures/Proximity/Game.lean`. The random oracle
is indexed by optional coordinates and slots, without requiring a finite slot type.
-/

public section

open OracleComp OracleSpec GroupModel.LinearFunctional

namespace Proximity

/-- Vector messages with an explicit slot. -/
abbrev Message (F Slot : Type) (dimension : ℕ) := (Fin dimension → F) × Slot

/-- The constant base and coordinate bases of each slot. -/
abbrev Index (Slot : Type) (dimension : ℕ) := Option (Fin dimension) × Slot

/-- The constant base has weight one; coordinate bases have the message's entries as weights. -/
@[expose] def terms {F Slot : Type} [One F] {dimension : ℕ}
    (msg : Message F Slot dimension) : List (Index Slot dimension × F) :=
  ((none, msg.2), 1) :: List.ofFn (fun k : Fin dimension => ((some k, msg.2), msg.1 k))

/-- Hashing a message looks up one constant base and one base for every coordinate. -/
@[simp] theorem terms_length {F Slot : Type} [One F] {dimension : ℕ}
    (msg : Message F Slot dimension) : (terms msg).length = dimension + 1 := by
  simp [terms]

/-- The direct message hash over the oracle of slot and coordinate bases. -/
@[expose] def hash {F Slot G : Type} [Semiring F] [AddCommMonoid G] [Module F G]
    {dimension : ℕ} (msg : Message F Slot dimension) :
    OracleComp (unifSpec + (Index Slot dimension →ₒ G)) G := weightedQuery (terms msg)

/-- Fixed-table interpretation of the message hash is its constant base plus weighted bases. -/
theorem hash_table {F Slot G : Type} [Semiring F] [AddCommMonoid G] [Module F G]
    {dimension : ℕ} (table : Index Slot dimension → G) (msg : Message F Slot dimension) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn table)) (hash msg) =
      pure (table (none, msg.2) + ∑ k, msg.1 k • table (some k, msg.2)) := by
  rw [hash, weightedQuery_table]
  simp [terms, List.map_ofFn, List.sum_ofFn]

/-- Proximity's direct signature algorithm, with its verification key in the second source group. -/
@[expose] def scheme {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂) :
    SignatureAlg (OracleComp (unifSpec + (Index Slot dimension →ₒ G₁)))
      (Message F Slot dimension) G₂ F G₁ where
  keygen := do
    let x ← ($ᵗ F : ProbComp F)
    return (x • g₂, x)
  sign _ x msg := do
    let h ← hash msg
    return x • h
  verify pk msg σ := do
    let h ← hash msg
    return decide (e σ g₂ = e h pk)

/-- Honest signatures always verify under the standard shared lazy random-oracle runtime. -/
theorem perfectlyComplete {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ}
    [Field F] [SampleableType F] [DecidableEq Slot]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂) :
    (scheme (Slot := Slot) (dimension := dimension) e g₂).PerfectlyComplete
      (ProbCompRuntime.rom (Index Slot dimension →ₒ G₁)) := by
  intro msg
  rw [ProbCompRuntime.rom_evalDist]
  change 𝒟[(simulateQ (Index Slot dimension →ₒ G₁).romImpl _).run' ∅] {b | b = true} = 1
  rw [evalDist_apply_setOf_simulateQ_romImpl_run'_eq_one_iff]
  intro f _
  have hlift : ∀ {α : Type} (oa : ProbComp α),
      simulateQ (unifFwdAnswerImpl f) (liftM oa) = oa := by
    intro α oa
    change simulateQ (unifSpec.passthrough + f.liftTarget ProbComp)
      (OracleComp.liftComp oa (unifSpec + (Index Slot dimension →ₒ G₁))) = oa
    simpa using QueryImpl.simulateQ_add_liftComp_left
      (unifSpec.passthrough : QueryImpl unifSpec ProbComp) (f.liftTarget ProbComp) oa
  have hh := hash_table f msg
  change simulateQ (unifFwdAnswerImpl f) (hash msg) = _ at hh
  have hp (x : F) (v : G₁) : e (x • v) g₂ = e v (x • g₂) := by simp
  simp only [scheme, simulateQ_bind, simulateQ_pure, hlift, hh, bind_assoc, pure_bind, hp]
  simp

end Proximity
