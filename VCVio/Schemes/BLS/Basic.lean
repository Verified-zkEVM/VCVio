/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.SignatureAlg
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Module.Torsion.Free

/-! # BLS signatures in the random oracle model

The signature scheme of Boneh, Lynn and Shacham, *Short Signatures from the Weil Pairing*
(ASIACRYPT 2001), in additive notation over two source modules and a target module.
The public key contains the secret scalar multiple of both generators, as required by the
Type 3 co-CDH experiment. Verification uses only the second component.

The standard lazy random-oracle runtime `ProbCompRuntime.rom` shares hash answers between
signing and verification. Completeness requires bilinearity alone; extraction additionally
uses a generating first source point and a nonzero pairing of the generators.
-/

public section

open OracleComp OracleSpec

namespace BLS

variable {F G₁ G₂ Gₜ M : Type}

/-- BLS with a Type 3 public key. The first component `x • g₁` is included so that the
reduction targets the co-CDH form of `CoCDH.experiment`; verification uses only `x • g₂`.
The left oracle summand supplies uniform randomness and the right one hashes messages. -/
@[expose] def scheme [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) :
    SignatureAlg (OracleComp (unifSpec + (M →ₒ G₁))) M (G₁ × G₂) F G₁ where
  keygen := do
    let x ← ($ᵗ F : ProbComp F)
    return ((x • g₁, x • g₂), x)
  sign _ x msg := do
    let h ← (M →ₒ G₁).query msg
    return x • h
  verify pk msg σ := do
    let h ← (M →ₒ G₁).query msg
    return decide (e σ g₂ = e h pk.2)

/-- Bilinearity makes an honestly formed BLS signature satisfy the verification equation. -/
private theorem pairing_smul_eq [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂) (x : F) (h : G₁) :
    e (x • h) g₂ = e h (x • g₂) := by
  simp

/-- A nonzero generator pairing makes the BLS verification equation determine the signature
uniquely. Surjectivity of scalar multiplication by `g₁` suffices for this algebraic step. -/
theorem pairing_eq_iff [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : Function.Surjective (· • g₁ : F → G₁)) (he : e g₁ g₂ ≠ 0)
    (x : F) (h σ : G₁) :
    e σ g₂ = e h (x • g₂) ↔ σ = x • h := by
  obtain ⟨a, rfl⟩ := hg₁ σ
  obtain ⟨b, rfl⟩ := hg₁ h
  constructor
  · intro hv
    have hab : a = x * b := smul_left_injective F he (by
      simpa [smul_smul, mul_comm] using hv)
    simp [hab, smul_smul]
  · intro hv
    rw [hv]
    exact pairing_smul_eq e g₂ x (b • g₁)

/-- BLS is perfectly complete under the standard lazy random-oracle runtime, for every
bilinear map, including degenerate maps. -/
theorem perfectlyComplete [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) :
    (scheme (M := M) e g₁ g₂).PerfectlyComplete (ProbCompRuntime.rom (M →ₒ G₁)) := by
  intro msg
  rw [ProbCompRuntime.rom_evalDist]
  change 𝒟[(simulateQ (M →ₒ G₁).romImpl _).run' ∅] {b | b = true} = 1
  rw [evalDist_apply_setOf_simulateQ_romImpl_run'_eq_one_iff]
  intro f _
  have hlift : ∀ {α : Type} (oa : ProbComp α),
      simulateQ (unifFwdAnswerImpl f) (liftM oa) = oa := by
    intro α oa
    change simulateQ (unifSpec.passthrough + f.liftTarget ProbComp)
      (OracleComp.liftComp oa (unifSpec + (M →ₒ G₁))) = oa
    simpa using QueryImpl.simulateQ_add_liftComp_left
      (unifSpec.passthrough : QueryImpl unifSpec ProbComp) (f.liftTarget ProbComp) oa
  simp only [scheme, simulateQ_bind, simulateQ_pure, hlift]
  have hquery : simulateQ (unifFwdAnswerImpl f)
      (liftM ((M →ₒ G₁).query msg)) = (pure (f msg) : ProbComp G₁) := by
    change simulateQ (unifSpec.passthrough + f.liftTarget ProbComp)
      (liftM ((M →ₒ G₁).query msg)) = _
    exact QueryImpl.simulateQ_add_liftM_query_right
      (unifSpec.passthrough : QueryImpl unifSpec ProbComp) (f.liftTarget ProbComp) msg
  simp only [hquery, pure_bind]
  simp

end BLS
