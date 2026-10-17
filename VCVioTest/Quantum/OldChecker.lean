/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Merkle.OfflineOld

/-!
# Old-checker public API regression tests

Ordinary imports exercise the actual checker interface, the distinct-cell count across multiple
oracle indices, contradictory prescriptions, and the finite FIX (35) error at small budgets.
The numerical tests specify an error expression, not an offline security theorem.
-/

public section

open Quantum Quantum.CompressedReplay Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder ENNReal Kronecker

namespace VCVioTest.OldChecker

/-- A repeated prescription across two oracle databases, touching only one cell. -/
abbrev repeated : List ((Fin 2 × Bool) × ZMod 3) :=
  [((0, true), 1), ((0, true), 1)]

/-- Duplicate checks retain the one-cell squared discrepancy `5/9`. -/
example : ‖filledCheck repeated - partialCheck repeated‖ ^ 2 = 5 / 9 := by
  have hc : ConsistentIO repeated := by
    intro p hp q hq _
    simp only [repeated, List.mem_cons, List.not_mem_nil, or_false, or_self] at hp hq
    subst p
    subst q
    rfl
  rw [filled_partial_distance_sq repeated hc]
  norm_num [ioCells, repeated, ZMod.card]

/-- Equal addresses in distinct databases count as two cells, giving `65/81`. -/
example :
    ‖filledCheck ([((0, true), 1), ((1, true), 1)] : List ((Fin 2 × Bool) × ZMod 3)) -
      partialCheck [((0, true), 1), ((1, true), 1)]‖ ^ 2 = 65 / 81 := by
  have hc : ConsistentIO
      ([((0, true), 1), ((1, true), 1)] : List ((Fin 2 × Bool) × ZMod 3)) := by
    intro p hp q hq _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> rfl
  rw [filled_partial_distance_sq _ hc]
  norm_num [ioCells, ZMod.card]

/-- Conflicting prescriptions vanish even if one is the special zero answer. -/
example :
    filledCheck ([((0, true), 0), ((0, true), 1)] : List ((Fin 2 × Bool) × ZMod 3)) = 0 ∧
    partialCheck ([((0, true), 0), ((0, true), 1)] : List ((Fin 2 × Bool) × ZMod 3)) = 0 := by
  apply filled_partial_eq_zero_of_conflict
  intro h
  have he := h ((0, true), 0) (by simp) ((0, true), 1) (by simp) rfl
  exact (by decide : (0 : ZMod 3) ≠ 1) he

/-- The zero-answer sector satisfies the actual-versus-filled positive comparison. -/
example : (actualCheck ([((0, true), 0)] : List ((Fin 2 × Bool) × ZMod 3)) -
    filledCheck [((0, true), 0)]).PosSemidef :=
  (actual_sub_filled_supported_invalid _).1

/-- The generic operational checker theorem is accessible through an ordinary import. -/
example {P : Type} {In : P → QReg} {E : EmulatedOracle P In} {X Y : Type}
    [Fintype Y] [DecidableEq Y] (H : ProjectiveClassicalAnswers E X Y)
    (B : QReg) (io : List (X × Y)) :
    (E.toRuntime.run₂ .instruments
      ((checkIO io).toQuantumAt (H.classicalCall B))).branch true =
        H.transcriptBranch B io :=
  H.actual_accept_eq_projectorProduct B io

open Quantum.SaltedMerkle

/-- One call has zero accumulated leakage but a nonzero terminal invalid-sector allowance. -/
example : oldOfflineError 16 1 1 1 0 = 1 / 4 := by
  have hs : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [oldOfflineError, oldChangingFraction, Real.sqrt_div, hs]

/-- Four opened leaves at depth zero are four raw checks, including the leaf hashes. -/
example : oldMerkleOfflineError 64 0 0 0 0 4 = 1 / 4 := by
  have hs : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [oldMerkleOfflineError, oldOfflineError, Real.sqrt_div, hs]

/-- The leakage polynomial at two calls is one, so it is not rounded down by division. -/
example : oldLeakagePolynomial 2 = 1 := by
  norm_num [oldLeakagePolynomial]

/-- Large invalid-sector allowances are capped at one. -/
example : oldOfflineError 1 1 1 1 0 = 1 := by
  norm_num [oldOfflineError, oldChangingFraction]

/-- All four amplitude terms contribute, below the outer cap. -/
example : oldOfflineError 1000000 25 (1 / 1800) (1 / 9500) 1 = 9 / 1600 := by
  have h₁ : Real.sqrt 1000000 = 1000 := by
    rw [show (1000000 : ℝ) = 1000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h₂ : Real.sqrt 40000 = 200 := by
    rw [show (40000 : ℝ) = 200 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h₃ : Real.sqrt 49 = 7 := by
    rw [show (49 : ℝ) = 7 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [oldOfflineError, oldLeakagePolynomial, oldChangingFraction,
    Real.sqrt_div, h₁, h₂, h₃]

/-- The finite-sum formula includes the zero prefix and agrees with `T(3) = 7`. -/
example : (∑ j ∈ Finset.range 3, (j : ℝ) * (2 * j - 1)) = 7 := by
  rw [← oldLeakagePolynomial_eq_sum]
  norm_num [oldLeakagePolynomial]

/-- A zero leakage coefficient contributes zero even for infinite mass. -/
example :
    (∑ j ∈ Finset.range 1,
      (ENNReal.ofReal ((j : ℝ) * (2 * j - 1)) / 16 * (⊤ : ℝ≥0∞)) ^ (2⁻¹ : ℝ)) = 0 := by
  simp [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]

/-- Concatenation decodes a heterogeneous full tuple through the existing extraction decoder. -/
example {k : ℕ} {Dm : Fin k → Type} [∀ i, Fintype (Dm i)]
    (hk : 1 ≤ k) (t : TpDLen k Dm (TupleLen.full hk)) :
    (TpDCode.concat (Dm := Dm)).decodeAt (TupleLen.full hk)
      ((k : ZMod (k + 1)), fun i : Fin k ↦ TpDCode.concatCell (Dm := Dm) i (t i)) = some t := by
  rw [← TpDCode.concat_full hk t, TpDCode.decodeAt_enc]

/-- The factorization is a public matrix identity for general finite extractors. -/
example {k : ℕ} {Dm : Fin k → Type} [∀ i, Fintype (Dm i)]
    {Cm S : Type} [Fintype Cm] [DecidableEq Cm] [Fintype S] [DecidableEq S]
    (ME : MultiExtractor k Cm Dm S) (B A C : Finset (Fin k))
    (hBA : Disjoint B A) (hBC : Disjoint (B ∪ A) C)
    (hcover : B ∪ A ∪ C = Finset.univ) :
    extractUnitary ME TpDCode.concat =
      basisMatrix (TpDCode.responsePerm
        (TpDCode.lengthResponse (Dm := Dm) (Cm := Cm) (S := S))) *
        basisMatrix (TpDCode.responsePerm (TpDCode.partResponse ME B)) *
        basisMatrix (TpDCode.responsePerm (TpDCode.partResponse ME A)) *
        basisMatrix (TpDCode.responsePerm (TpDCode.partResponse ME C)) :=
  TpDCode.extractUnitary_concat_factor ME B A C hBA hBC hcover

/-- Original post-adversary population support is available for arbitrary local signatures
and dependent final registers through an ordinary public import. -/
example {k : ℕ} {X Y Cm Z : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm]
    [Fintype Z] [DecidableEq Z] [AddGroup Z] {Dm : Fin k → Type}
    (ME : MultiExtractor k Cm Dm (Fin k → Database X Y)) (code : TpDCode k Dm Z)
    {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}
    {x : QuantumComp L (EmulatedOracle.cohSpec (extIn k X Y Cm Z)) W A}
    {q : ℕ} (hx : x.IsQueryBound fun _ ↦ q) (ρ : SubState A) (p : Σ B, W B) :
    QuerySupportedOn
      (fun a : p.1 × (Fin k → Database X Y) ↦ databasePopulation a.2) (Set.Iic q)
      ((((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime.jointPost
        I x ρ p).matrix) :=
  databasePopulation_post_old ME code I hx ρ p

/-- A two-element unchanged set among three labels has exact squared distance one third. -/
example :
    ‖uniformSubsetProjector (Finset.univ : Finset (Fin 3)) -
      uniformSubsetProjector {0, 2}‖ ^ 2 = 1 / 3 := by
  rw [uniformSubsetProjector_distance_sq]
  norm_num

/-- An empty unchanged set is included in the projector distance formula. -/
example :
    ‖uniformSubsetProjector (Finset.univ : Finset Bool) -
      uniformSubsetProjector ∅‖ ^ 2 = 1 := by
  rw [uniformSubsetProjector_distance_sq]
  norm_num

/-- A constant label commutes exactly with the uniform projector for every ancilla unitary. -/
example {Z : Type} [Fintype Z] [DecidableEq Z]
    (U : Unit → Matrix Z Z ℂ) (hU : ∀ k, U k ∈ unitaryGroup Z ℂ) :
    let V := labelControlled (fun _ : Bool × Z ↦ ())
      (fun k ↦ (1 : Matrix Bool Bool ℂ) ⊗ₖ U k)
    V * (uniformSubsetProjector Finset.univ ⊗ₖ (1 : Matrix Z Z ℂ)) =
      (uniformSubsetProjector Finset.univ ⊗ₖ (1 : Matrix Z Z ℂ)) * V := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa using uniformProjector_commutator_le (fun _ : Bool ↦ ()) () U hU

/-- The checker Gram bound counts invalid cells, including repeated prescriptions. -/
example :
    ((invalidStack (k := 2) (X := Bool) (Y := ZMod 3))ᴴ * invalidStack -
      (actualCheck repeated - filledCheck repeated)ᴴ *
        (actualCheck repeated - filledCheck repeated)).PosSemidef :=
  actual_sub_filled_gram_le_invalidStack repeated

/-- The checker-potential comparison keeps an arbitrary entangled positive joint matrix. -/
example {A : Type} [Fintype A]
    {ρ : Matrix (A × (Fin 2 → Database Bool (ZMod 3)))
      (A × (Fin 2 → Database Bool (ZMod 3))) ℂ} (hρ : ρ.PosSemidef) :
    QuantumRuntime.potential (actualCheck repeated - filledCheck repeated) ρ ≤
      QuantumRuntime.potential (invalidStack (k := 2) (X := Bool) (Y := ZMod 3)) ρ :=
  actual_sub_filled_potential_le repeated hρ

/-- Two identity observables already have total weight two; the direct-sum bound still applies. -/
example (U : Matrix Bool Bool ℂ) (hU : Uᴴ * U = 1)
    {ρ : Matrix Bool Bool ℂ} (hρ : ρ.PosSemidef) :
    (∑' _ : Bool, ENNReal.ofReal (MatrixMap.conj (1 : Matrix Bool Bool ℂ)
      (MatrixMap.conj U ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
        (∑' _ : Bool, ENNReal.ofReal (MatrixMap.conj (1 : Matrix Bool Bool ℂ)
          ρ).trace.re) ^ (2⁻¹ : ℝ) := by
  simpa using MatrixMap.rpow_inv_two_tsum_conj_unitary_le
    (fun _ : Bool ↦ (1 : Matrix Bool Bool ℂ)) U hU hρ

/-- A single exceptional filled label among sixteen gives a quarter of the occupancy
projector as a uniform Gram bound, for any two response unitaries. -/
example {Z : Type} [Fintype Z] [DecidableEq Z] (U : Bool → Matrix Z Z ℂ)
    (hU : ∀ b, U b ∈ unitaryGroup Z ℂ) :
    let β := fun y : Option (Fin 16) ↦ decide (y = some 0)
    let V := filledCellControl β U
    let P := oldInvalidCell (Y := Fin 16) ⊗ₖ (1 : Matrix Z Z ℂ)
    ((1 / 4 : ℝ) • ((1 - cellEmpty (Y := Fin 16)) ⊗ₖ (1 : Matrix Z Z ℂ)) -
      (V * P - P * V)ᴴ * (V * P - P * V)).PosSemidef := by
  have h := oldInvalidCell_commutator_gram_le
    (fun y : Option (Fin 16) ↦ decide (y = some 0)) U hU
  have hc : (Finset.univ.filter fun x : Fin 16 ↦ x = 0) = {0} := by
    ext x
    simp
  norm_num [hc] at h
  simpa only [conjTranspose_sub, conjTranspose_mul] using h

/-- Zero-prefix coefficients annihilate infinite mass; the ENNReal bound needs no `toReal`. -/
example (mass : ℕ → ℝ≥0∞) :
    (∑ j ∈ Finset.range 1,
      (ENNReal.ofReal (4 * j * oldChangingFraction 16 j) * mass j) ^ (2⁻¹ : ℝ)) = 0 := by
  simp [oldChangingFraction]

/-- The actual invalid potential vanishes initially for any, possibly entangled, workspace. -/
example {A : Type} [Fintype A] (ρ : Matrix A A ℂ) :
    QuantumRuntime.potential (invalidStack (k := 2) (X := Bool) (Y := ZMod 3))
      (ρ ⊗ₖ (compressedVCOracle 2 Bool (ZMod 3)).init.matrix) = 0 :=
  invalidStack_initial_potential_zero ρ

/-- One total coherent call cannot create invalid weight, even with adaptive instruments
and a dependent result-register family. This exercises the actual runtime theorem. -/
example {X Y Msg Salt Z : Type} [Fintype X] [DecidableEq X] [LinearOrder Y] [Fintype Y]
    [AddCommGroup Y] [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
    [Fintype Z] [DecidableEq Z] [AddCommGroup Z]
    (enc : _root_.SaltedMerkle.Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ)
    (code : TpDCode k (DmOf (fun i ↦ 2 ^ d i) Msg
      (fun i ↦ _root_.SaltedMerkle.Td Y Salt (d i))) Z)
    {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}
    (x : QuantumComp L (EmulatedOracle.cohSpec (extIn k X Y Y Z)) W A)
    (ρ : SubState A) (hx : x.IsQueryBound fun _ ↦ 1) :
    let E := (compressedVCOracle k X Y).withExtract (_root_.SaltedMerkle.multiExtract enc d) code
    (∑' p, QuantumRuntime.potential invalidStack
      (E.coherent.toRuntime.jointPost I x ρ p).matrix) ^ (2⁻¹ : ℝ) = 0 := by
  have h := old_run_invalid_le enc d code I x ρ 1 hx
  simpa [oldLeakagePolynomial] using h

/-- Recording an infinite classical outcome type still isolates exactly one composite branch,
including when all three workspace registers differ. -/
example {L : LocalSig} {spec : QuantumOracleSpec} (R : QuantumRuntime spec) (I : L.Interp)
    {A B C : QReg} (f : QuantumComp₂ L spec A B ℕ)
    (g : ℕ → QuantumComp₂ L spec B C ℕ) (a b : ℕ) :
    (R.run₂ I (f.bind fun a ↦ (g a).map fun b ↦ (a, b))).branch (a, b) =
      (R.run₂ I (g a)).branch b ∘ₗ (R.run₂ I f).branch a :=
  R.run₂_bind_record I f g a b

/-- Discarding the first retained outcome recovers sequencing for infinite outcome types. -/
example {L : LocalSig} {spec : QuantumOracleSpec} {A B C : QReg}
    (f : QuantumComp₂ L spec A B ℕ) (g : ℕ → QuantumComp₂ L spec B C ℕ) :
    (f.bind fun a ↦ (g a).map fun b ↦ (a, b)).map Prod.snd = f.bind g :=
  QuantumRuntime.bind_record_map_snd f g

/-- A checker on the first component preserves the second component exactly, even when
its local conjugating operator mixes the first component's basis states. -/
example (p : Bool → Prop) [DecidablePred p] (C : Matrix Bool Bool ℂ) (hC : C * C = 1)
    (D D' : Fin 2 → Bool)
    (h : (piKron (fun _ : Fin 2 ↦ C) * diagonal
      (fun D : Fin 2 → Bool ↦ if ∀ i ∈ ({0} : Finset (Fin 2)), p (D i) then (1 : ℂ) else 0) *
        piKron (fun _ : Fin 2 ↦ C)) D D' ≠ 0) : D 1 = D' 1 := by
  have hs := conjugated_batch_support (fun _ : Fin 2 ↦ p) id {0} C hC D D'
  refine hs ?_ 1 (by simp)
  convert h using 1
  simp only [id_eq, Matrix.mul_apply, diagonal_apply]
  congr! 6

end VCVioTest.OldChecker
