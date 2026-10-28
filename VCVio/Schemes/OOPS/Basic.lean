/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.SignatureAlg
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.WeightedQuery
public import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Module.Torsion.Free

/-! # OOPS signatures with topic-indexed polynomial hashes

For degree `d`, the random oracle supplies independent bases `H(t, j)` for `j ≤ d`.
A message is a scalar/topic pair `(m, t)` and its hash is `∑ j, m^j • H(t, j)`.
The secret is a uniform scalar `x`, the public key is `x • g₂`, and the signature is
`x • ∑ j, m^j • H(t, j)`. Verification uses the pairing equation.

The scheme and terms follow `Signatures/OOPS/Spec/LazyAGM.lean` and
`Signatures/OOPS/Game.lean` in Gurkan's signature-security-lean at revision 3eaa8c4.
-/

public section

open OracleComp OracleSpec GroupModel.LinearFunctional

namespace OOPS

/-- The ordered polynomial hash bases and weights for a scalar/topic message. -/
@[expose] def terms {F T : Type} [Monoid F] (degree : ℕ) (mt : F × T) :
    List ((T × Fin (degree + 1)) × F) :=
  List.ofFn fun j : Fin (degree + 1) => ((mt.2, j), mt.1 ^ (j : ℕ))

/-- Every polynomial hash queries exactly `degree + 1` bases, counting repeated calls. -/
@[simp] theorem terms_length {F T : Type} [Monoid F] (degree : ℕ) (mt : F × T) :
    (terms degree mt).length = degree + 1 := by simp [terms]

/-- The polynomial hash obtained from one shared oracle on topic/degree labels. -/
@[expose] def hash {F T G : Type} [Monoid F] [AddMonoid G] [SMul F G]
    (degree : ℕ) (mt : F × T) : OracleComp ((T × Fin (degree + 1)) →ₒ G) G :=
  weightedQuery (terms degree mt)

/-- OOPS as a signature algorithm with a single public-key point in the second source group.
Uniform randomness and the polynomial-base random oracle are the two ambient interfaces. -/
@[expose] def scheme {F T G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂) (degree : ℕ) :
    SignatureAlg (OracleComp (unifSpec + ((T × Fin (degree + 1)) →ₒ G₁)))
      (F × T) G₂ F G₁ where
  keygen := do
    let x ← ($ᵗ F : ProbComp F)
    return (x • g₂, x)
  sign _ x mt := do
    let h ← liftM (hash (G := G₁) degree mt)
    return x • h
  verify pk mt σ := do
    let h ← liftM (hash (G := G₁) degree mt)
    return decide (e σ g₂ = e h pk)

/-- Bilinearity makes an honest OOPS signature satisfy the verification equation. -/
theorem pairing_smul_eq {F G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂) (x : F) (h : G₁) :
    e (x • h) g₂ = e h (x • g₂) := by simp

/-- OOPS is perfectly complete with the shared lazy random-oracle runtime. -/
theorem perfectlyComplete {F T G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq T]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂) (degree : ℕ) :
    (scheme (T := T) e g₂ degree).PerfectlyComplete
      (ProbCompRuntime.rom ((T × Fin (degree + 1)) →ₒ G₁)) := by
  intro mt
  rw [ProbCompRuntime.rom_evalDist]
  change 𝒟[(simulateQ ((T × Fin (degree + 1)) →ₒ G₁).romImpl _).run' ∅]
    {b | b = true} = 1
  rw [evalDist_apply_setOf_simulateQ_romImpl_run'_eq_one_iff]
  intro f _
  have hlift : ∀ {α : Type} (oa : ProbComp α),
      simulateQ (unifFwdAnswerImpl f) (liftM oa) = oa := by
    intro α oa
    change simulateQ (unifSpec.passthrough + f.liftTarget ProbComp)
      (OracleComp.liftComp oa (unifSpec + ((T × Fin (degree + 1)) →ₒ G₁))) = oa
    simpa using QueryImpl.simulateQ_add_liftComp_left
      (unifSpec.passthrough : QueryImpl unifSpec ProbComp) (f.liftTarget ProbComp) oa
  simp only [scheme, simulateQ_bind, simulateQ_pure, hlift]
  have hhash := simulateQ_unifFwd_weightedQuery (G := G₁)
    (fun i => f i) (terms degree mt)
  change simulateQ (unifFwdAnswerImpl f)
    (liftM (weightedQuery (G := G₁) (terms degree mt)) :
      OracleComp (unifSpec + ((T × Fin (degree + 1)) →ₒ G₁)) G₁) = _ at hhash
  simp only [hash, hhash, pure_bind]
  simp

end OOPS
