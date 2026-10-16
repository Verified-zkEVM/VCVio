/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.Hadamard

/-!
# Perfect simulation by the empty-sector extension

The repair note §3.1 observes that an ordinary execution never enters the decompressed empty
sector. The tabulate-and-compress isometry intertwines the extended ports with the purified
uniform random oracle. This proves P1 with zero error for every unitary empty-sector response,
without an exponent-two assumption or a flat-column assumption on that response.
-/

public section

open Matrix MeasureTheory Convexity
open scoped Kronecker ENNReal NNReal

universe uL vL w

namespace Quantum

section intertwine

variable {X Y T T' : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype T] [DecidableEq T] [Fintype T'] [DecidableEq T'] [AddCommGroup Y]

/-- Embedding total tables intertwines a table oracle with every empty-sector extension.
Only the values on the embedded tables matter; the matrix `W` is unrestricted. -/
theorem extendedTableOracle_mul_one_kronecker_basisMatrix (W : Matrix Y Y ℂ)
    {read : T → X → Y} {read' : T' → X → Option Y} {g : T → T'}
    (hg : ∀ t x, read' (g t) x = some (read t x)) :
    extendedTableOracle W read' * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ basisMatrix g) =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ basisMatrix g) * tableOracle read := by
  rw [one_kronecker_basisMatrix, tableOracle, ← basisMatrix_comp]
  ext ⟨⟨x, r⟩, d⟩ ⟨⟨z, s⟩, t⟩
  rw [mul_basisMatrix_apply, basisMatrix_apply]
  by_cases hx : x = z
  · subst z
    by_cases hd : d = g t
    · subst d
      simp [extendedTableOracle_apply, hg, emptyExtensionBlock, tableOracleEquiv_apply,
        oracleEquiv_apply]
    · simp [extendedTableOracle_apply, hd, tableOracleEquiv_apply, oracleEquiv_apply]
  · simp [extendedTableOracle_apply, hx, tableOracleEquiv_apply, oracleEquiv_apply]

end intertwine

section simulation

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] (W : Matrix Y Y ℂ) (hW : W ∈ unitaryGroup Y ℂ)

/-- Tabulation followed by compression intertwines every extended port with the purified
random oracle, with no condition on the empty-sector matrix. -/
theorem extendedVCPort_mul_one_kronecker (i : Fin k) :
    extendedVCPort k X Y W i *
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
          (compressDatabases k X Y * basisMatrix (ofFunDatabases k X Y))) =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
          (compressDatabases k X Y * basisMatrix (ofFunDatabases k X Y))) *
        tableOracle (fun H : Fin k → X → Y ↦ H i) := by
  have hE := extendedTableOracle_mul_one_kronecker_basisMatrix W
    (read := fun H : Fin k → X → Y ↦ H i)
    (read' := fun d : Fin k → Database X Y ↦ d i)
    (g := ofFunDatabases k X Y) (fun _ _ ↦ rfl)
  rw [extendedVCPort, ← one_kronecker_mul_one_kronecker]
  calc
    _ = ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressDatabases k X Y) *
        extendedTableOracle W (fun d : Fin k → Database X Y ↦ d i) *
        (((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressDatabases k X Y) *
          ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressDatabases k X Y)) *
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ basisMatrix (ofFunDatabases k X Y)) := by
          simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [one_kronecker_mul_one_kronecker, compressDatabases_mul_self,
        one_kronecker_one, Matrix.mul_one, Matrix.mul_assoc, hE, Matrix.mul_assoc]

/-- The simulation isometry sends the purified initial state to the empty databases. -/
theorem conj_compressDatabases_extendedVCOracle_init :
    MatrixMap.conj (compressDatabases k X Y * basisMatrix (ofFunDatabases k X Y))
        (purifiedVCOracle k X Y).init.matrix =
      (extendedVCOracle k X Y W hW).init.matrix :=
  conj_compressDatabases_mul_basisMatrix_init

variable {L : LocalSig.{uL, vL}} (I : L.Interp) {V : QReg → Type w} {A : QReg}
  {γ : Type*} [MeasurableSpace γ]

/-- Every coherent ordinary-oracle execution has the same observed law against the extended
witness and the purified uniform random oracle. This does not expose the extraction port. -/
theorem outcomeLawWith_coherent_extendedVCOracle_eq_purifiedVCOracle
    (x : QuantumComp L (EmulatedOracle.cohSpec (oIn k X Y)) V A) (ρ : SubState A)
    (f : (Σ u, V u) → γ) :
    (extendedVCOracle k X Y W hW).coherent.toRuntime.outcomeLawWith I x ρ f =
      (purifiedVCOracle k X Y).coherent.toRuntime.outcomeLawWith I x ρ f :=
  EmulatedOracle.outcomeLawWith_eq_of_intertwine _ _ _
    conjTranspose_compressDatabases_mul_basisMatrix_mul_self
    (fun _ ↦ EmulatedOracle.coherent_U_mul_one_kronecker _ _ _
      (extendedVCPort_mul_one_kronecker W))
    (conj_compressDatabases_extendedVCOracle_init W hW) I x ρ f

/-- The coherent extended witness simulates independent uniform random functions exactly. -/
theorem outcomeLawWith_coherent_extendedVCOracle
    (x : QuantumComp L (EmulatedOracle.cohSpec (oIn k X Y)) V A) (ρ : SubState A)
    (f : (Σ u, V u) → γ) :
    (extendedVCOracle k X Y W hW).coherent.toRuntime.outcomeLawWith I x ρ f =
      ∑ H : Fin k → X → Y, (Fintype.card (Fin k → X → Y) : ℝ≥0∞)⁻¹ •
        (romVCOracle k X Y H).coherent.toRuntime.outcomeLawWith I x ρ f := by
  rw [outcomeLawWith_coherent_extendedVCOracle_eq_purifiedVCOracle,
    outcomeLawWith_coherent_purifiedVCOracle]

end simulation

/-- P1 with zero error for the extended witness, against the same uniform weights as the
compressed oracle. The only hypothesis on `W` is unitarity. -/
theorem simulates_extendedVCOracle {k : ℕ} {X Y : Type}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
    (W : Matrix Y Y ℂ) (hW : W ∈ unitaryGroup Y ℂ) :
    Simulates (StdSimplex.barycenter : StdSimplex ℝ (Fin k → X → Y))
      (fun H ↦ (romVCOracle k X Y H).coherent.toRuntime) (extendedVCOracle k X Y W hW) 0 := by
  intro t A V x f ρ _
  rw [mixedLawWith_barycenter, outcomeLawWith_coherent_extendedVCOracle]
  simp only [Pi.zero_apply, add_zero, le_refl, and_self]

end Quantum
