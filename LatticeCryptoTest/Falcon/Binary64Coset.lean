/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
public import Extern.Falcon.Binary64Coset
public import VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# Witnesses for the coset condition at the binary64 FFT primitives

Consistency checks only: they show that the hypotheses of the binary64 coset theorems on the
bundle, the key and the sampler can hold together at Falcon-512 parameters with nonzero data. They
are not evidence about the concrete sampler or about real keys.

- `landsOnLattice_witness`: `Falcon.Concrete.landsOnLattice_of_binary64FFTFields` at Falcon-512
  for a key with coefficients reaching `±127` and a sampled pair with coefficients reaching
  `±2^16`, the corners of the proved regime.
- `quarterBinary64`: the binary64 FFT fields with a sampler drawing uniformly from `{0, 1, 2, 3}`,
  whatever the centre. It satisfies `Falcon.SampledCoeffsLe` with `Z = 3` for every key
  (`quarterBinary64_sampledCoeffsLe`). That sampler is not Falcon's.
- `unitPk`, `unitSk`: the key `f = 1`, `g` nonzero with coefficients in `[-63, 63]`, `F = 2`,
  `G = 2 · g`, `h = g`. It satisfies the key relations `f · h = g` and `F · h = G` and has
  `h ≠ 0`, but not the NTRU equation, so it is not a valid Falcon key pair.
- `quarterBinary64_hpreimage` and `quarterBinary64_verify`: for that bundle and that key, the
  coset condition and verification correctness hold with no remaining hypothesis on the bundle,
  key or sampler. `quarterBinary64_verify` is about the signatures `sign` returns; that it returns
  one here is not shown, since the sampler ignores the target.
-/

public section

open OracleComp OracleSpec Falcon Falcon.Concrete LatticeCrypto

namespace LatticeCryptoTest.FalconBinary64Coset

/-- A depth-`k` tree with zero `ℓ` and unit leaves; `LandsOnLattice` does not read the tree. -/
noncomputable def unitTree : (k : ℕ) → FalconTree k
  | 0 => .leaf 1
  | k + 1 => .node 0 (unitTree k) (unitTree k)

/-! ## The lattice-point condition at the corners of the regime -/

/-- A key whose coefficients reach `±127`. Only the coefficient bound is used; the key relations
are not. -/
noncomputable def cornerKey : SecretKey falcon512 where
  f := Vector.ofFn fun i => ((i.1 % 255 : ℕ) : ℤ) - 127
  g := Vector.ofFn fun i => 127 - ((i.1 % 255 : ℕ) : ℤ)
  capF := Vector.ofFn fun i => ((i.1 % 254 : ℕ) : ℤ) - 127
  capG := Vector.ofFn fun i => 127 - ((i.1 % 254 : ℕ) : ℤ)
  tree := unitTree _

theorem cornerKey_coeffs : KeyCoeffsLe127 cornerKey := by
  intro i
  simp only [cornerKey, Vector.get_ofFn]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> omega

/-- The coefficients of the first sampled polynomial: `2^16` at `0`, then values in `[-2, 2]`. -/
def zA (i : Fin (2 * 2 ^ 8)) : ℤ := if i.1 = 0 then 65536 else ((i.1 % 5 : ℕ) : ℤ) - 2

/-- The coefficients of the second sampled polynomial: `-2^16` at `1`, then values in `[-1, 1]`. -/
def zB (i : Fin (2 * 2 ^ 8)) : ℤ := if i.1 = 1 then -65536 else ((i.1 % 3 : ℕ) : ℤ) - 1

theorem abs_zA_le (i : Fin (2 * 2 ^ 8)) : |(zA i : ℝ)| ≤ 2 ^ 16 := by
  have : |zA i| ≤ 65536 := by unfold zA; split_ifs <;> rw [abs_le] <;> constructor <;> omega
  calc |(zA i : ℝ)| ≤ 65536 := by exact_mod_cast this
    _ = 2 ^ 16 := by norm_num

theorem abs_zB_le (i : Fin (2 * 2 ^ 8)) : |(zB i : ℝ)| ≤ 2 ^ 16 := by
  have : |zB i| ≤ 65536 := by unfold zB; split_ifs <;> rw [abs_le] <;> constructor <;> omega
  calc |(zB i : ℝ)| ≤ 65536 := by exact_mod_cast this
    _ = 2 ^ 16 := by norm_num

/-- The binary64 basis application lands on the lattice for the corner key and the sampled pair
`(zA, zB)` at Falcon-512. -/
theorem landsOnLattice_witness :
    LandsOnLattice falcon512 (binary64FFTPrimitives falcon512 rfl) cornerKey
      (RealFFTPoly.ofCoeffs 8 fun i => (zA i : ℝ), RealFFTPoly.ofCoeffs 8 fun i => (zB i : ℝ)) :=
  landsOnLattice_of_binary64FFTFields falcon512 rfl (by decide) (by decide) _
    (binary64FFTPrimitives_binary64FFTFields falcon512 rfl) cornerKey cornerKey_coeffs (2 ^ 16)
    cosetDeviation_falcon512 _ ⟨zA, zB, abs_zA_le, abs_zB_le, rfl, rfl⟩

/-! ## A sampler bounded independently of the centre -/

/-- A uniform draw from `{0, 1, 2, 3}`. -/
def quarterDraw : ProbComp ℤ := (fun x : Fin 4 => (x.1 : ℤ)) <$> ($ᵗ Fin 4)

theorem abs_le_of_mem_support_quarterDraw {x : ℤ} (hx : x ∈ support quarterDraw) :
    |(x : ℝ)| ≤ 3 := by
  rw [quarterDraw, support_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  have : |(y.1 : ℤ)| ≤ 3 := by rw [abs_le]; have := y.2; constructor <;> omega
  change |((y.1 : ℤ) : ℝ)| ≤ 3
  exact_mod_cast this

/-- The binary64 FFT fields with the sampler `quarterDraw`. -/
noncomputable def quarterBinary64 : Primitives falcon512 :=
  { binary64FFTPrimitives falcon512 rfl with samplerZ := fun _ _ => quarterDraw }

theorem quarterBinary64_fields : Binary64FFTFields quarterBinary64 := ⟨rfl, rfl⟩

theorem quarterBinary64_sampledCoeffsLe (sk : SecretKey falcon512) {Z : ℝ} (hZ : 3 ≤ Z) :
    SampledCoeffsLe falcon512 quarterBinary64 sk Z :=
  sampledCoeffsLe_of_samplerZ_le _ _ sk Z fun _ _ _ hx =>
    (abs_le_of_mem_support_quarterDraw hx).trans hZ

/-! ## A key satisfying the key relations -/

/-- The constant polynomial `1`. -/
noncomputable def unitF : IntPoly falcon512.n := Vector.ofFn fun i => if i.1 = 0 then 1 else 0

/-- A nonzero polynomial with coefficients in `[-63, 63]`. -/
noncomputable def unitG : IntPoly falcon512.n := Vector.ofFn fun i => 63 - ((i.1 % 127 : ℕ) : ℤ)

/-- The public key `h = g`. -/
noncomputable def unitPk : PublicKey falcon512 := ⟨IntPoly.toRq unitG⟩

/-- The secret key `f = 1`, `g`, `F = 2`, `G = 2 · g`. -/
noncomputable def unitSk : SecretKey falcon512 where
  f := unitF
  g := unitG
  capF := unitF + unitF
  capG := unitG + unitG
  tree := unitTree _

private theorem falcon512_n_pos : 0 < falcon512.n := by decide

private theorem toRq_unitF : IntPoly.toRq unitF = (1 : Rq falcon512.n) := by
  apply Poly.ext_get_eq
  intro i
  rw [toRq_get]
  change _ = ((LatticeCrypto.vectorNegacyclicRing Coeff falcon512.n).one).get i
  rw [LatticeCrypto.vectorRing_one_get]
  simp only [unitF, Vector.get_ofFn]
  split_ifs <;> simp

theorem unitPk_ne_zero : unitPk.h ≠ 0 := by
  intro h
  have h0 : (IntPoly.toRq unitG : Rq falcon512.n).get ⟨0, falcon512_n_pos⟩ = 0 := by
    change unitPk.h.get _ = 0
    rw [h, Rq.get_zero]
  have hg : unitG.get ⟨0, falcon512_n_pos⟩ = 63 := by simp [unitG]
  rw [toRq_get, hg] at h0
  have h63 := Int.le_of_dvd (by norm_num) ((ZMod.intCast_zmod_eq_zero_iff_dvd 63 modulus).mp h0)
  norm_num [modulus] at h63

theorem unitSk_coeffs : KeyCoeffsLe127 unitSk := by
  intro i
  change |unitF.get i| ≤ 127 ∧ |unitG.get i| ≤ 127 ∧ |(unitF + unitF).get i| ≤ 127 ∧
    |(unitG + unitG).get i| ≤ 127
  rw [Poly.get_add, Poly.get_add]
  simp only [unitF, unitG, Vector.get_ofFn]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> rw [abs_le] <;> constructor <;> omega

theorem unitSk_key : negacyclicMul (IntPoly.toRq unitSk.f) unitPk.h = IntPoly.toRq unitSk.g := by
  change negacyclicMul (IntPoly.toRq unitF) (IntPoly.toRq unitG) = IntPoly.toRq unitG
  rw [toRq_unitF]
  apply quotientOf_injective falcon512_n_pos
  rw [quotientOf_mul, quotientOf_one, one_mul]

theorem unitSk_cap :
    negacyclicMul (IntPoly.toRq unitSk.capF) unitPk.h = IntPoly.toRq unitSk.capG := by
  change negacyclicMul (IntPoly.toRq (unitF + unitF)) (IntPoly.toRq unitG) =
    IntPoly.toRq (unitG + unitG)
  rw [toRq_add, toRq_add, toRq_unitF]
  apply quotientOf_injective falcon512_n_pos
  rw [quotientOf_mul, quotientOf_add, quotientOf_add, quotientOf_one]
  ring

/-! ## The coset condition and verification correctness with no remaining hypothesis -/

/-- For the bounded sampler and the key `unitPk`, `unitSk`, every output of the trapdoor sampler
is a preimage of its target. -/
theorem quarterBinary64_hpreimage :
    ∀ (c : Rq falcon512.n) (x : Rq falcon512.n × Rq falcon512.n),
      x ∈ support ((falconPSF falcon512 quarterBinary64).trapdoorSample unitPk unitSk c) →
        (falconPSF falcon512 quarterBinary64).eval unitPk x = c := by
  have hm : cosetDeviation falcon512.fftDepth 3 < 1 / 2 := by
    change cosetDeviation 8 3 < 1 / 2
    norm_num [cosetDeviation, Binary64.ifftDeviation, fftError, Binary64.etaF, Binary64.etaI,
      Binary64.u]
  exact hpreimage_of_binary64FFTFields_of_sampledCoeffsLe falcon512 rfl (by decide) (by decide)
    quarterBinary64 quarterBinary64_fields unitPk unitSk unitSk_key unitSk_cap unitSk_coeffs 3 hm
    (quarterBinary64_sampledCoeffsLe unitSk le_rfl)

/-- For the bounded sampler and the key `unitPk`, `unitSk`, every signature it returns
verifies. -/
theorem quarterBinary64_verify (msg : List Byte) (maxAttempts : ℕ) (sig : Signature)
    (hsig : some sig ∈ support (sign falcon512 quarterBinary64 unitPk unitSk msg maxAttempts)) :
    verify falcon512 quarterBinary64 unitPk msg sig = true :=
  verify_sign_correct_falcon512_of_binary64FFTFields_of_sampledCoeffsLe quarterBinary64
    quarterBinary64_fields (binary64FFTPrimitives_decompress_compress falcon512 rfl) unitPk
    unitSk unitSk_key unitSk_cap unitSk_coeffs
    (quarterBinary64_sampledCoeffsLe unitSk (by norm_num)) msg maxAttempts sig hsig

end LatticeCryptoTest.FalconBinary64Coset

end
