/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Compressed
public import VCVio.Quantum.VC.Conditions
public import QuantumFoundations.MatrixMap.BlockNorm
public import VCVio.CryptoFoundations.MerkleTree.Salted.Extract

/-!
# Tests for the k compressed oracles and the conditions of Theorem 8.4

Checks of the public interface of `VCVio.Quantum.VC.Compressed`, `VCVio.Quantum.VC.Conditions`
and `QuantumFoundations.MatrixMap.BlockNorm` (ePrint 2025/2166, Lemma 9.2 and Theorem 8.4):

* unitarity and commutation of the ports of two compressed oracles on `Bool → ZMod 2`;
* smoke tests of the statements of the law equality and of P1 on a one-query adversary against
  the coherent compressed oracles. Its leaves carry no classical value, so these laws only record
  the preserved mass; they check that the statements elaborate on a concrete program;
* a semantic check that observes the answer: a classical call of port `0` on `|false, 0⟩`,
  followed by a computational-basis measurement of the answer register, returns each answer
  with probability `1 / 2` against the compressed oracles, while against the oracle answering
  `0` everywhere, whose ports are the identity, it returns `0` with certainty;
* the norm of an operator controlled by one classical bit is the larger norm of its two blocks;
* the salted Merkle scheme satisfies the conditions of Theorem 8.4 with `P_good` the
  collision-free databases, so `Quantum.Conditions` is not vacuous.
-/

public section

open Quantum Matrix MeasureTheory
open scoped ENNReal Kronecker Matrix.Norms.L2Operator

namespace VCVioTest.QuantumVCCompressed

open EmulatedOracle (cohSpec cohIn)

/-! ## Generic emulated-oracle intertwining -/

section

universe u uL vL w

variable {P : Type u} {In : P → QReg}

/-- The isometry law is available for arbitrary emulated oracles through ordinary imports. -/
example (E₁ E₂ : EmulatedOracle P In) (M : Matrix E₂.S E₁.S ℂ)
    (hM : Mᴴ * M = 1)
    (hU : ∀ i, E₂.U i * ((1 : Matrix (In i) (In i) ℂ) ⊗ₖ M) =
      ((1 : Matrix (In i) (In i) ℂ) ⊗ₖ M) * E₁.U i)
    (hinit : MatrixMap.conj M E₁.init.matrix = E₂.init.matrix) {L : LocalSig.{uL, vL}}
    (I : L.Interp) {W : QReg → Type w} {A : QReg} (x : QuantumComp L (uSpec P In) W A)
    (ρ : SubState A) {γ : Type*} [MeasurableSpace γ] (f : (Σ u, W u) → γ) :
    E₂.toRuntime.evalDistMap I x ρ f = E₁.toRuntime.evalDistMap I x ρ f :=
  EmulatedOracle.outcomeLawWith_eq_of_intertwine E₁ E₂ M hM hU hinit I x ρ f

end

/-! ## Unitarity and commutation on a small instance -/

/-- Two compressed oracles on `Bool → ZMod 2`. -/
local notation "E₂" => compressedVCOracle 2 Bool (ZMod 2)

/-- Every port of the small instance is unitary. -/
example (i : Fin 2) :
    (E₂).U i ∈ unitaryGroup ((Bool × ZMod 2) × (Fin 2 → Database Bool (ZMod 2))) ℂ :=
  compressedVCOracle_U_mem_unitaryGroup 2 Bool (ZMod 2) i

/-- The private register of the small instance is the pair of databases, started empty. -/
example : (E₂).S = QReg.of (Fin 2 → Database Bool (ZMod 2)) :=
  compressedVCOracle_S 2 Bool (ZMod 2)

/-- The two ports of the small instance commute, on two query registers. -/
example :
    onFactor (slotSnd (Bool × ZMod 2) (Bool × ZMod 2) (Fin 2 → Database Bool (ZMod 2)))
      ((E₂).U 0) *
        onFactor (slotFst (Bool × ZMod 2) (Bool × ZMod 2) (Fin 2 → Database Bool (ZMod 2)))
          ((E₂).U 1) =
      onFactor (slotFst (Bool × ZMod 2) (Bool × ZMod 2) (Fin 2 → Database Bool (ZMod 2)))
          ((E₂).U 1) *
        onFactor (slotSnd (Bool × ZMod 2) (Bool × ZMod 2) (Fin 2 → Database Bool (ZMod 2)))
          ((E₂).U 0) :=
  compressedVCOracle_commute 0 1

/-- The small instance satisfies the oracle commutation of Definition 7.3. -/
example : OraclesCommute E₂ :=
  oraclesCommute_compressedVCOracle

/-! ## Smoke tests: the law equality and P1 on a one-query adversary

The leaves of `oneQuery` carry no classical value, so every observation `f` below is constant
and the laws only record the preserved mass. These examples check that the general statements
apply to a concrete program; the answer-sensitive check is in the next section. -/

/-- The register of a one-query adversary: the coherent query register and nothing beside it. -/
local notation "Reg" => QReg.of (cohIn (oIn 2 Bool (ZMod 2)) × Unit)

/-- One coherent call of the two oracles. -/
noncomputable def oneQuery :=
  QuantumComp.query (L := LocalSig.instruments.{0}) (spec := cohSpec (oIn 2 Bool (ZMod 2)))
    (A := Reg) () (QReg.of Unit) (Equiv.refl _)

/-- The adversary makes one call. -/
theorem isQueryBound_oneQuery : oneQuery.IsQueryBound fun _ ↦ 1 :=
  (QuantumComp.isQueryBound_query_iff _ _ _ _).mpr Nat.one_pos

/-- **The law of the one-query adversary** against the coherent compressed oracles is the average
of its laws against the coherent random oracles `H : Fin 2 → Bool → ZMod 2`, for any input state
and any observation of its output. -/
example (ρ : SubState Reg) {γ : Type} [MeasurableSpace γ]
    (f : (Σ u, (fun u ↦ PSigma fun _ : u = QReg.of ((cohSpec (oIn 2 Bool (ZMod 2))).Out () ×
      QReg.of Unit) ↦ (cohSpec (oIn 2 Bool (ZMod 2))).Result ()) u) → γ) :
    (E₂).coherent.toRuntime.evalDistMap .instruments oneQuery ρ f =
      ∑ H : Fin 2 → Bool → ZMod 2,
        (Fintype.card (Fin 2 → Bool → ZMod 2) : ℝ≥0∞)⁻¹ •
        (romVCOracle 2 Bool (ZMod 2) H).coherent.toRuntime.evalDistMap .instruments oneQuery
          ρ f :=
  outcomeLawWith_coherent_compressedVCOracle _ _ _ _

/-- There are `2 ^ 4 = 16` random oracles in the average. -/
example : Fintype.card (Fin 2 → Bool → ZMod 2) = 16 := by
  simp [ZMod.card]

/-- **P1 with `κsim = 0` on the one-query adversary**: its probability of accepting against the
coherent compressed oracles is at most the averaged probability against the random oracles. -/
example (ρ : SubState Reg) (f : (Σ u, (fun u ↦ PSigma fun _ : u =
      QReg.of ((cohSpec (oIn 2 Bool (ZMod 2))).Out () × QReg.of Unit) ↦
        (cohSpec (oIn 2 Bool (ZMod 2))).Result ()) u) → Bool) :
    (E₂).coherent.toRuntime.evalDistMap .instruments oneQuery ρ f {true} ≤
      mixedLawWith
        (Convexity.StdSimplex.barycenter : Convexity.StdSimplex ℝ (Fin 2 → Bool → ZMod 2))
        (fun H ↦ (romVCOracle 2 Bool (ZMod 2) H).coherent.toRuntime) .instruments oneQuery ρ
        (fun _ ↦ f) {true} + 0 :=
  (simulates_compressedVCOracle.restrictOrdinary 1 oneQuery f ρ
    ((QuantumComp.isTotalQueryBound_iff_isQueryBound oneQuery 1).mpr isQueryBound_oneQuery)).1

/-! ## The measured answer of a classical call is uniform -/

/-- A classical call of port `0` on the input `|false, 0⟩`: measure the answer register in the
computational basis after the call, and return the measured answer. -/
noncomputable def answerCall :
    QComp (uSpec (Fin 2) (oIn 2 Bool (ZMod 2))) (QReg.of Unit) (QReg.of Unit) (ZMod 2) :=
  QComp.callBasis (spec := uSpec (Fin 2) (oIn 2 Bool (ZMod 2))) 0 (QReg.of Unit) (false, 0)
    fun o _ ↦ o.2

/-- The block `⟨o|U_0|false, 0⟩` of the random oracle `H` is one exactly at the output
`o = (false, H 0 false)`. -/
theorem block_romVCOracle (H : Fin 2 → Bool → ZMod 2) (o : Bool × ZMod 2) :
    (romVCOracle 2 Bool (ZMod 2) H).block 0 o (false, 0) =
      if o = (false, H 0 false) then 1 else 0 := by
  ext ⟨⟩ ⟨⟩
  by_cases h : o = (false, H 0 false) <;>
    simp only [romVCOracle, Fin.isValue, EmulatedOracle.block_apply, kroneckerMap_apply,
      oracleUnitary_apply, zero_add, h, ↓reduceIte, one_apply_eq, mul_one] <;> rfl

/-- Against the random oracle `H`, the call returns `H 0 false` with certainty. -/
theorem outcomeLaw₂_romVCOracle_answerCall (H : Fin 2 → Bool → ZMod 2) (y : ZMod 2) :
    (romVCOracle 2 Bool (ZMod 2) H).toRuntime.evalDist₂ .instruments answerCall
      (SubState.basis ()) {y} = if H 0 false = y then 1 else 0 := by
  rw [QuantumRuntime.evalDist₂_apply_singleton, QuantumRuntime.matrix_jointPost₂, answerCall,
    EmulatedOracle.branch_run₂_callBasis, Finset.sum_eq_single (false, H 0 false)
      (fun o _ ho ↦ by simp [block_romVCOracle, ho]) (by simp)]
  by_cases h : H 0 false = y
  · subst h
    simp only [block_romVCOracle, ↓reduceIte, one_kronecker_one, MatrixMap.conj_one]
    rw [LinearMap.id_apply]
    simp only [trace, romVCOracle, SubState.matrix_basis, diag_apply, kroneckerMap_apply,
      single_apply_same, mul_one, Finset.sum_const, nsmul_eq_mul, Complex.natCast_re,
      ENNReal.ofReal_natCast, Nat.cast_eq_one]
    rfl
  · simp [h]

/-- **The measured answer is uniform** against the compressed oracles: each `y : ZMod 2` has
probability `1 / 2`. By `Quantum.outcomeLawWith_compressedVCOracle` the law is the average over
the `16` random oracles `H`, of which `8` have `H 0 false = y`. -/
example (y : ZMod 2) :
    (E₂).toRuntime.evalDist₂ .instruments answerCall (SubState.basis ()) {y} = 2⁻¹ := by
  have h := outcomeLawWith_compressedVCOracle (k := 2) (X := Bool) (Y := ZMod 2) .instruments
    answerCall (SubState.basis ()) (QuantumComp₂.leafEquiv (QReg.of Unit) (ZMod 2)).symm
  rw [QuantumRuntime.evalDist₂_eq_evalDistMap, h, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, ← QuantumRuntime.evalDist₂_eq_evalDistMap, smul_eq_mul]
  rw [Finset.sum_congr rfl fun H _ ↦ by rw [outcomeLaw₂_romVCOracle_answerCall H y]]
  have h8 : (Finset.univ.filter fun H : Fin 2 → Bool → ZMod 2 ↦ H 0 false = y).card = 8 := by
    fin_cases y <;> decide
  have h16 : Fintype.card (Fin 2 → Bool → ZMod 2) = 8 * 2 := by
    simp [ZMod.card]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, h8, h16, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul, Nat.cast_ofNat]

/-- The oracle answering `0` everywhere has identity ports. -/
example (i : Fin 2) : (romVCOracle 2 Bool (ZMod 2) 0).U i = 1 := by
  ext ⟨m, ⟨⟩⟩ ⟨m', ⟨⟩⟩
  simp [romVCOracle, Matrix.one_apply]

/-- **The identity oracle has a different law**: against it the call never returns `1`, so the
measured answer tells the compressed oracles apart from the identity. -/
example :
    (romVCOracle 2 Bool (ZMod 2) 0).toRuntime.evalDist₂ .instruments answerCall
      (SubState.basis ()) {1} = 0 :=
  (outcomeLaw₂_romVCOracle_answerCall 0 1).trans (by simp)

/-! ## The norm of a classically controlled operator with two blocks -/

/-- **Two blocks.** The operator `|0⟩⟨0| ⊗ A + |1⟩⟨1| ⊗ B` controlled by one bit has
norm `max ‖A‖ ‖B‖`. -/
example {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A B : Matrix m n ℂ) :
    ‖single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) ⊗ₖ A +
      single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) ⊗ₖ B‖ =
      max ‖A‖ ‖B‖ := by
  have h := l2_opNorm_sum_single_kronecker (𝕜 := ℂ) ![A, B]
  rw [Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [h]
  have hbdd : BddAbove (Set.range fun c ↦ ‖(![A, B] : Fin 2 → Matrix m n ℂ) c‖) :=
    (Set.finite_range _).bddAbove
  refine le_antisymm (ciSup_le fun c ↦ ?_) (max_le ?_ ?_)
  · fin_cases c
    · exact le_max_left _ _
    · exact le_max_right _ _
  · simpa using le_ciSup hbdd 0
  · simpa using le_ciSup hbdd 1

/-- An empty control register gives norm zero even for nonempty rectangular blocks. -/
example (A : Empty → Matrix (Fin 2) (Fin 3) ℂ) :
    ‖∑ c, single c c (1 : ℂ) ⊗ₖ A c‖ = 0 := by
  rw [l2_opNorm_sum_single_kronecker, Real.iSup_of_isEmpty]

open scoped ComplexOrder in
/-- The public Gram-slack bound turns a rectangular contraction into positive slack. -/
example (K : Matrix (Fin 2) (Fin 3) ℂ) (hK : ‖K‖ ≤ 1) :
    ((1 : Matrix (Fin 3) (Fin 3) ℂ) - Kᴴ * K).PosSemidef := by
  have hsq : ‖K‖ ^ 2 ≤ (1 : ℝ) := by nlinarith [norm_nonneg K]
  simpa only [one_smul] using MatrixMap.posSemidef_scalar_sub_gram_of_norm_sq_le K hsq

/-! ## Non-vacuity: the salted Merkle scheme satisfies the conditions -/

section Merkle

open SaltedMerkle OracleComp

variable {X Y Msg Salt : Type} [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt] [SampleableType Salt]

/-- **The salted Merkle scheme satisfies the conditions of Theorem 8.4** (ePrint 2025/2166, §8.3,
p. 55): `MTMultiExtract` with the collision-free databases as `P_good` and the trees of
depths `d i`. Condition 1 is `SaltedMerkle.nonadaptiveCheck`; the opening is deterministic, so the
support conditions reduce to the deterministic binding and validity of `MTMultiExtract`. -/
theorem merkle_conditions (enc : MerkleTreeHashing.QueryEncoding X Unit Unit (Msg × Salt) Y)
    {k : ℕ} (d : Fin k → ℕ) :
    Conditions (fun i ↦ (scheme (Msg := Msg) enc (d i)).toVectorCommitment)
      (fun i ↦ nonadaptiveCheck enc (d i)) (multiExtract enc d) (fun _ ↦ tdBot)
        collisionFree where
  admissible := multiExtract_admissible enc d
  empty_mem := empty_mem_collisionFree
  binding hk idx hidx cm ans pf Ds hD h i := by
    have hb := multiExtract_binding enc d hk idx hidx cm ans pf Ds hD h i
    refine ⟨hb.1, fun pf' hpf' ↦ ?_⟩
    rw [← hb.2]
    exact eq_of_mem_support_pure hpf'
  valid hk idx hidx cm Ds i pf hpf := by
    rw [eq_of_mem_support_pure hpf]
    exact multiExtract_valid enc d hk idx hidx cm Ds i

/-- The query counts of the salted Merkle scheme: a check of `q` positions in a tree of depth
`d i` makes `q * (d i + 1)` queries, so `q2` is the largest `2 ^ d i * (d i + 1)`. -/
example (enc : MerkleTreeHashing.QueryEncoding X Unit Unit (Msg × Salt) Y)
    {k : ℕ} (d : Fin k → ℕ) (i : Fin k) :
    2 ^ d i * (d i + 1) ≤ q2 (VC := fun i ↦ (scheme (Msg := Msg) enc (d i)).toVectorCommitment)
      (fun i ↦ nonadaptiveCheck enc (d i)) :=
  qVC_le_q2 (fun i ↦ nonadaptiveCheck enc (d i)) i

/-- `q1` of the salted Merkle scheme is at least the count of a single check of the whole
budget. -/
example (enc : MerkleTreeHashing.QueryEncoding X Unit Unit (Msg × Salt) Y)
    {k : ℕ} (d : Fin k → ℕ) (i : Fin k) (qs : ℕ) :
    qs * (d i + 1) ≤ q1 (VC := fun i ↦ (scheme (Msg := Msg) enc (d i)).toVectorCommitment)
      (fun i ↦ nonadaptiveCheck enc (d i)) qs := by
  have h := sum_qVC_le_q1 (fun i ↦ nonadaptiveCheck enc (d i)) (qs := qs) (Pi.single i qs)
    (by simp)
  refine le_trans ?_ h
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj, nonadaptiveCheck]) (by simp)]
  simp [nonadaptiveCheck]

/-- The offline label of the salted Merkle scheme marks the collision-free databases. -/
example [Fintype X] [DecidablePred (· ∈ (collisionFree : Set (Database X Y)))]
    (D : Database X Y) : offlineLabel collisionFree D = true ↔ D ∈ collisionFree :=
  offlineLabel_eq_true_iff _ D

end Merkle

end VCVioTest.QuantumVCCompressed
