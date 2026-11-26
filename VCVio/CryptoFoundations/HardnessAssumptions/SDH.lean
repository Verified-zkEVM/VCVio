/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # Strong Diffie–Hellman problems

The two source groups receive powers of a trapdoor sampled uniformly among the nonzero
scalars; `SDH.srs` builds this reference string. The pairing is public. Boneh and Boyen's
`t`-SDH problem asks for an inverse shift; the adaptive rational strong Diffie–Hellman problem
of Chiesa, Guan, Knabenhans and Yu (Definition 9.6) asks for division by a vanishing
polynomial.
-/

public section

open OracleComp OracleSpec

namespace SDH

/-- Uniform sampling among the nonzero scalars of a finite field. -/
@[expose] noncomputable def sampleTrapdoor (F : Type) [Field F] [Fintype F]
    [DecidableEq F] : ProbComp F :=
  letI : Nonempty {x : F // x ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  letI := SampleableType.subtype F (· ≠ 0)
  Subtype.val <$> ($ᵗ {x : F // x ≠ 0})

/-- The powers-of-trapdoor reference string of degree `D`: the powers `τ ^ i • g₁` for
`i ≤ D` in the first source group, and `g₂` and `τ • g₂` in the second. -/
@[expose] def srs {F G₁ G₂ : Type} [Monoid F] [SMul F G₁] [SMul F G₂]
    (g₁ : G₁) (g₂ : G₂) (τ : F) (D : ℕ) : (Fin (D + 1) → G₁) × (Fin 2 → G₂) :=
  (fun i => τ ^ (i : ℕ) • g₁, ![g₂, τ • g₂])

section srs

variable {F G₁ G₂ : Type} [Monoid F] [SMul F G₁] [SMul F G₂]
  (g₁ : G₁) (g₂ : G₂) (τ : F) (D : ℕ)

/-- The first component of `srs` lists the powers of the trapdoor on `g₁`. -/
@[simp] theorem srs_fst : (srs g₁ g₂ τ D).1 = fun i : Fin (D + 1) => τ ^ (i : ℕ) • g₁ := rfl

/-- The second component of `srs` is `g₂` followed by `τ • g₂`. -/
@[simp] theorem srs_snd : (srs g₁ g₂ τ D).2 = ![g₂, τ • g₂] := rfl

end srs

end SDH

namespace TSDH

/-- A `t`-SDH adversary receives powers through `D` in the first source group and
through one in the second, and returns a scalar offset and a first-source element. -/
@[expose] def Adversary (F G₁ G₂ : Type) (D : ℕ) :=
  (Fin (D + 1) → G₁) → (Fin 2 → G₂) → ProbComp (F × G₁)

/-- Boneh and Boyen's `t`-SDH experiment with a uniform nonzero trapdoor and public pairing. -/
@[expose] noncomputable def experiment {F G₁ G₂ : Type} [Field F] [Fintype F]
    [DecidableEq F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂]
    {D : ℕ} (g₁ : G₁) (g₂ : G₂) (A : Adversary F G₁ G₂ D) : ProbComp Bool := by
  classical
  exact do
    let τ ← SDH.sampleTrapdoor F
    let (c, h) ← A (SDH.srs g₁ g₂ τ D).1 (SDH.srs g₁ g₂ τ D).2
    return decide (τ + c ≠ 0 ∧ h = (τ + c)⁻¹ • g₁)

end TSDH

namespace ARSDH

/-- An ARSDH adversary returns a set of scalars and two first-source elements after
receiving powers through `D` and one in the two respective source groups. -/
@[expose] def Adversary (F G₁ G₂ : Type) (D : ℕ) :=
  (Fin (D + 1) → G₁) → (Fin 2 → G₂) → ProbComp (Finset F × G₁ × G₁)

/-- The ARSDH experiment of Chiesa, Guan, Knabenhans and Yu, Definition 9.6.
The trapdoor is uniform among nonzero scalars and the pairing is public. -/
@[expose] noncomputable def experiment {F G₁ G₂ : Type} [Field F] [Fintype F]
    [DecidableEq F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂]
    {D : ℕ} (g₁ : G₁) (g₂ : G₂) (A : Adversary F G₁ G₂ D) : ProbComp Bool := by
  classical
  exact do
    let τ ← SDH.sampleTrapdoor F
    let (S, h₁, h₂) ← A (SDH.srs g₁ g₂ τ D).1 (SDH.srs g₁ g₂ τ D).2
    let Z : Polynomial F := ∏ s ∈ S, (Polynomial.X - Polynomial.C s)
    return decide (S.card = D + 1 ∧ Z.eval τ ≠ 0 ∧ h₁ ≠ 0 ∧ h₂ = (Z.eval τ)⁻¹ • h₁)

end ARSDH
