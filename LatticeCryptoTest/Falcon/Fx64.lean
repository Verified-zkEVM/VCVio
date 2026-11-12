/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
public import Extern.Falcon.Fx64Coset
public import LatticeCryptoTest.Falcon.Binary64Coset

/-!
# Witnesses for the coset condition at the fixed-point FFT primitives

Consistency checks only: they show that the hypotheses of the fixed-point coset theorems on the
arithmetic, the bundle, the key and the sampler can hold together at Falcon-512 parameters with
nonzero data. They are not evidence about any fixed-point implementation, about the concrete
sampler, or about real keys.

- `landsOnLattice_witness`: `Falcon.Concrete.landsOnLattice_of_fx64FFTFields` at Falcon-512 for
  round to nearest (`Falcon.FixedPoint.Arith64.nearest`), the key
  `LatticeCryptoTest.FalconBinary64Coset.cornerKey` with coefficients reaching `±127`, and a
  sampled pair with coefficients reaching `±2^33`, the corners of the regime of
  `Falcon.Concrete.fx64CosetDeviation_falcon512`.
- `quarterFx64`: the fixed-point FFT fields of `Arith64.nearest` with a sampler drawing uniformly
  from `{0, 1, 2, 3}`, whatever the centre (`LatticeCryptoTest.FalconBinary64Coset.quarterDraw`).
  That sampler is not Falcon's.
- `quarterFx64_verify`: for that bundle and the key `unitPk`, `unitSk` (key relations, `h ≠ 0`,
  not the NTRU equation), every signature `sign` returns verifies, with no remaining hypothesis on
  the bundle, key or sampler. That `sign` returns one here is not shown.
-/

public section

open OracleComp OracleSpec Falcon Falcon.Concrete Falcon.FixedPoint LatticeCrypto
open LatticeCryptoTest.FalconBinary64Coset

namespace LatticeCryptoTest.FalconFx64

/-! ## The lattice-point condition at the corners of the regime -/

/-- The coefficients of the first sampled polynomial: `2^33` at `0`, then values in `[-2, 2]`. -/
def zA (i : Fin (2 * 2 ^ 8)) : ℤ := if i.1 = 0 then 8589934592 else ((i.1 % 5 : ℕ) : ℤ) - 2

/-- The coefficients of the second sampled polynomial: `-2^33` at `1`, then values in
`[-1, 1]`. -/
def zB (i : Fin (2 * 2 ^ 8)) : ℤ := if i.1 = 1 then -8589934592 else ((i.1 % 3 : ℕ) : ℤ) - 1

theorem abs_zA_le (i : Fin (2 * 2 ^ 8)) : |(zA i : ℝ)| ≤ 2 ^ 33 := by
  have : |zA i| ≤ 8589934592 := by
    unfold zA; split_ifs <;> rw [abs_le] <;> constructor <;> omega
  calc |(zA i : ℝ)| ≤ 8589934592 := by exact_mod_cast this
    _ = 2 ^ 33 := by norm_num

theorem abs_zB_le (i : Fin (2 * 2 ^ 8)) : |(zB i : ℝ)| ≤ 2 ^ 33 := by
  have : |zB i| ≤ 8589934592 := by
    unfold zB; split_ifs <;> rw [abs_le] <;> constructor <;> omega
  calc |(zB i : ℝ)| ≤ 8589934592 := by exact_mod_cast this
    _ = 2 ^ 33 := by norm_num

/-- The fixed-point basis application with round to nearest lands on the lattice for the corner
key and the sampled pair `(zA, zB)` at Falcon-512. -/
theorem landsOnLattice_witness :
    LandsOnLattice falcon512 (fx64FFTPrimitives Arith64.nearest falcon512 rfl) cornerKey
      (RealFFTPoly.ofCoeffs 8 fun i => (zA i : ℝ), RealFFTPoly.ofCoeffs 8 fun i => (zB i : ℝ)) :=
  landsOnLattice_of_fx64FFTFields Arith64.nearest falcon512 rfl (by decide) _
    (fx64FFTPrimitives_fx64FFTFields Arith64.nearest falcon512 rfl) cornerKey cornerKey_coeffs
    (2 ^ 33) fx64CosetDeviation_falcon512 _ ⟨zA, zB, abs_zA_le, abs_zB_le, rfl, rfl⟩

/-! ## A sampler bounded independently of the centre -/

/-- The fixed-point FFT fields of round to nearest with the sampler `quarterDraw`. -/
noncomputable def quarterFx64 : Primitives falcon512 :=
  { fx64FFTPrimitives Arith64.nearest falcon512 rfl with samplerZ := fun _ _ => quarterDraw }

theorem quarterFx64_fields : Fx64FFTFields Arith64.nearest quarterFx64 := ⟨rfl, rfl⟩

theorem quarterFx64_sampledCoeffsLe (sk : SecretKey falcon512) {Z : ℝ} (hZ : 3 ≤ Z) :
    SampledCoeffsLe falcon512 quarterFx64 sk Z :=
  sampledCoeffsLe_of_samplerZ_le _ _ sk Z fun _ _ _ hx =>
    (abs_le_of_mem_support_quarterDraw hx).trans hZ

/-- For the bounded sampler, round to nearest and the key `unitPk`, `unitSk`, every signature
`sign` returns verifies. -/
theorem quarterFx64_verify (msg : List Byte) (maxAttempts : ℕ) (sig : Signature)
    (hsig : some sig ∈ support (sign falcon512 quarterFx64 unitPk unitSk msg maxAttempts)) :
    verify falcon512 quarterFx64 unitPk msg sig = true :=
  verify_sign_correct_falcon512_of_fx64FFTFields_of_sampledCoeffsLe Arith64.nearest quarterFx64
    quarterFx64_fields (fx64FFTPrimitives_decompress_compress Arith64.nearest falcon512 rfl)
    unitPk unitSk unitSk_key unitSk_cap unitSk_coeffs
    (quarterFx64_sampledCoeffsLe unitSk (by norm_num)) msg maxAttempts sig hsig

end LatticeCryptoTest.FalconFx64

end
