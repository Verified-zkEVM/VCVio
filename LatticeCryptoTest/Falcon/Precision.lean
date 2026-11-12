/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
import all LatticeCrypto.Falcon.SamplerMinEntropy
public import Extern.Falcon.Binary64Precision
public import LatticeCryptoTest.Falcon.Binary64Coset

/-!
# Witness for the Rényi precision transfer at the binary64 FFT primitives

Consistency check only: it shows that the hypotheses of
`Falcon.Concrete.idealExperiment_binary64_precision_falcon512` on the key, the tree and the
experiment hold together at Falcon-512 with nonzero data. It is not evidence about real keys,
real trees or the concrete sampler, and it does not bound `Falcon.preimageTailMass`.

- `precisionSk`: the key `f = 1`, `g`, `F = 2`, `G = 2 · g` of `unitSk` (its key relations with
  `unitPk ≠ 0` hold, the NTRU equation does not; the theorem uses neither), with the tree
  `halfTree`: every factor `ℓ` has all slots equal to `1/2`, every leaf is `3/2`, inside
  `[σmin, σmax]`.
- `oneSignature msg`: an experiment that makes one signing query and reports whether a
  signature came back.
- `precision_witness`: the Falcon-512 transfer for that key and that experiment, with one attempt
  per query; every hypothesis is discharged except the premise on the success probability with
  the binary64 fields.
-/

public section

open OracleComp OracleSpec Falcon Falcon.Concrete LatticeCrypto
  LatticeCryptoTest.FalconBinary64Coset
open scoped ENNReal

namespace LatticeCryptoTest.FalconPrecision

/-- A packed FFT polynomial with every slot equal to `1/2`. -/
noncomputable def halfSlots (k : ℕ) : RealFFTPoly k :=
  RealFFTPoly.pack (Vector.ofFn fun _ => 1 / 2) (Vector.ofFn fun _ => 0)

/-- A depth-`k` tree with every factor `halfSlots` and every leaf `3/2`. -/
noncomputable def halfTree : (k : ℕ) → FalconTree k
  | 0 => .leaf (3 / 2)
  | k + 1 => .node (halfSlots (k + 1)) (halfTree k) (halfTree k)

theorem norm_coord_halfSlots (k : ℕ) (j : Fin (2 ^ k)) :
    ‖RealFFTPoly.coord (halfSlots k) j‖ ≤ 1 / 2 := by
  rw [halfSlots, RealFFTPoly.coord_pack]
  simp only [Vector.get_ofFn]
  rw [show (⟨1 / 2, 0⟩ : ℂ) = ((1 / 2 : ℝ) : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs]
  norm_num

theorem halfTree_factorsLe {L : ℝ} (hL : 1 / 2 ≤ L) : ∀ k, (halfTree k).FactorsLe L
  | 0 => trivial
  | k + 1 => ⟨fun j => (norm_coord_halfSlots (k + 1) j).trans hL, halfTree_factorsLe hL k,
      halfTree_factorsLe hL k⟩

theorem halfTree_factorsLeRoot (k : ℕ) :
    (halfTree (k + 1)).FactorsLeRoot (240001 / 10000) (9923 / 10000) :=
  ⟨fun j => (norm_coord_halfSlots (k + 1) j).trans (by norm_num),
    halfTree_factorsLe (by norm_num) k, halfTree_factorsLe (by norm_num) k⟩

theorem halfTree_leavesIn : ∀ k, (halfTree k).LeavesIn falcon512.sigmaMin falcon512.sigmaMax
  | 0 => by
    change (12778336969128337 : ℝ) / 10000000000000000 ≤ 3 / 2 ∧ (3 / 2 : ℝ) ≤ 18205 / 10000
    norm_num
  | k + 1 => ⟨halfTree_leavesIn k, halfTree_leavesIn k⟩

/-- The key of `unitSk` with the tree `halfTree`. -/
noncomputable def precisionSk : SecretKey falcon512 := { unitSk with tree := halfTree _ }

theorem precisionSk_coeffs : KeyCoeffsLe127 precisionSk := unitSk_coeffs

/-- One signing query on `msg`; the output says whether a signature came back. -/
noncomputable def oneSignature (msg : List Byte) : OracleComp (unifSpec + signOracleSpec) Bool :=
  (liftM ((unifSpec + signOracleSpec).query (Sum.inr msg)) :
      OracleComp (unifSpec + signOracleSpec) (Option Signature)) >>= fun sig =>
    pure sig.isSome

theorem oneSignature_isQueryBoundP (msg : List Byte) :
    IsQueryBoundP (oneSignature msg) IsSignQuery 1 :=
  (isQueryBoundP_bind ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
    fun _ _ => isQueryBoundP_pure IsSignQuery _ 0).mono le_rfl

/-- **The Falcon-512 transfer at the witness**, consistency only: one signing query, one attempt,
`L = 1/2`. -/
theorem precision_witness (msg : List Byte) (T : ℝ≥0∞) (hT : 1 ≤ T)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((128 : ℕ) - 1 : ℝ)) <
      𝒟[idealExperiment falcon512 (binary64FFTPrimitives falcon512 rfl) unitPk precisionSk 1
        (oneSignature msg)] {true}) :
    T * (2 : ℝ≥0∞) ^ (-((128 : ℕ) : ℝ)) <
      𝒟[idealExperiment falcon512 (concretePrimitives falcon512 rfl) unitPk precisionSk 1
        (oneSignature msg)] {true} +
        (1 : ℕ) * (1 : ℕ) * preimageTailMass falcon512 (concretePrimitives falcon512 rfl)
          precisionSk 80000 :=
  idealExperiment_binary64_precision_falcon512 unitPk precisionSk precisionSk_coeffs
    (halfTree_leavesIn _) (halfTree_factorsLeRoot 7) 1 1 (by norm_num) (oneSignature msg)
    (oneSignature_isQueryBoundP msg) T hT (measurableSet_singleton _) hwin

end LatticeCryptoTest.FalconPrecision

end
