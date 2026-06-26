/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Concrete.Instance

/-!
# Concrete ML-DSA Primitive Laws

This file discharges the deterministically-provable fields of `MLDSA.Primitives.Laws` for the
concrete `concretePrimitives` instance built from the FIPS 204 rounding, NTT, and byte-encoding
layers, for any approved parameter set. Each provable field is banked as a standalone theorem
(`concrete_*`).

## What is proven

The eight rounding/transform fields follow directly from the verified concrete rounding lemmas
in `Concrete/Rounding.lean` and the concrete NTT laws in `Concrete/NTT.lean`, bridged across the
`polyNorm` / `LatticeCrypto.cInfNorm` definitional identity (`polyNorm_eq_cInfNorm`):

- `transform`, `high_low_decomp`, `lowBits_bound`, `hide_low`, `highBitsShift_injective`,
  `useHint_makeHint`, `power2Round_decomp`, `power2Round_bound`.

Two further fields are discharged from the concrete byte-encoding decode ranges and packer
roundtrip in `Concrete/Encoding.lean`:

- `expandMask_bound` (`concrete_expandMask_bound`): every `expandMask` coefficient is a value
  decoded by `polyZUnpack` over the range `[-γ₁ + 1, γ₁]`, so its centered infinity norm is at
  most `γ₁`. This is a property of the decoder's output window (`bitUnpackPoly_get`) and is
  independent of the opaque SHAKE byte stream. It matches the restated abstract bound `γ₁`.
- `w1Encode_injective` (`concrete_w1Encode_injOn`): on the valid commitment range — every
  component an actual `highBits` output — each coefficient lies in `[0, (q-1)/(2γ₂) - 1]`
  (`highBits_coeff_val_lt_m`), which fits the `w₁` packer's bit width, so `simpleBitPackPoly` is
  inverted by `simpleBitUnpackPoly` and `w1Encode` is injective. This matches the restated
  abstract `Set.InjOn` field, whose validity set is exactly the image of `highBits`.

Two further sampler-bound fields are discharged from the fuel-recursive rejection samplers in
`Concrete/Sampling.lean` (whose structural output ranges are now provable by fuel induction):

- `sampleInBall_norm` (`concrete_sampleInBall_norm`): `SampleInBall(c̃)`'s accumulator only ever
  holds the values `0`, `+1`, `-1`, so every coefficient has centered absolute value at most `1`.
- `expandS_bound` (`concrete_expandS_bound`): `ExpandS(ρ')` pushes only the centered `η`-bounded
  values (`2 - u` for `η = 2`, `4 - t` for `η = 4`; nothing otherwise), so every coefficient of
  both secret vectors has centered absolute value at most `η`.

A thirteenth field, the challenge-product bound, is also discharged from the convolution-norm
infrastructure now present in the tree:

- `sampleInBall_smul_bound` (`concrete_sampleInBall_smul_bound`): `SampleInBall(c̃)` has at most `τ`
  nonzero `±1` coefficients, so for `‖s‖∞ ≤ η` the challenge–secret product `c · s` satisfies
  `‖c · s‖∞ ≤ τ · η = β`. Assembled from the generic negacyclic-convolution infinity-norm bound
  `‖f · g‖∞ ≤ ‖f‖₁ · ‖g‖∞` (`LatticeCrypto.cInfNorm_mul_le`, whose proof tracks the *true integer*
  convolution sum to rule out modular wraparound, unconditional via a `q / 2` case split), the `ℓ₁`
  count `‖SampleInBall(c̃)‖₁ ≤ τ` (`sampleInBall_l1Norm`, a Fisher–Yates nonzero-count fuel
  induction), and the component law `(c • s).get j = c · sⱼ` (`coeffScalarVecMul_get`).

## What is NOT proven (and why)

One field remains, in a single honest category — there are no false-as-stated fields:

**Random-oracle modeling assumption** (inherent to the ML-DSA security model, not derivable
from any fixed deterministic instantiation — see its docstring in `Primitives.lean`):
- `keyVector_t0_determined`: a standard ROM idealization of the SHAKE XOFs
  (`ExpandSeed` / `ExpandS`). This is a model assumption, left abstract.

The abstract `Primitives.Laws` statement is **not** modified by this file; the banked `concrete_*`
theorems make explicit which concrete obligations are discharged and which remain.
-/


namespace MLDSA.Concrete

open MLDSA LatticeCrypto

set_option maxRecDepth 4000

/-- The ML-DSA centered infinity norm `polyNorm` agrees with the backend-generic
`LatticeCrypto.cInfNorm` on the canonical vector backend. This is the bridge that lets the
`polyNorm`-stated `Primitives.Laws` fields consume the `cInfNorm`-stated rounding lemmas. -/
theorem polyNorm_eq_cInfNorm (f : Rq) : polyNorm f = LatticeCrypto.cInfNorm f := by
  unfold polyNorm normOps LatticeCrypto.cInfNorm LatticeCrypto.zmodPolyNormOps
    LatticeCrypto.normOpsOfCenteredView
  rfl

variable (p : Params)

/-! ## Provable algebraic fields (banked) -/

/-- `Primitives.Laws.transform` for the concrete instance. -/
theorem concrete_transform : NTTRingLaws concreteNTTRingOps :=
  concreteNTTRingLaws

/-- `Primitives.Laws.high_low_decomp` for the concrete instance. -/
theorem concrete_high_low_decomp (r : Rq) :
    (concretePrimitives p).highBitsShift ((concretePrimitives p).highBits r)
      + (concretePrimitives p).lowBits r = r :=
  concreteRounding_high_low_decomp p r

/-- `Primitives.Laws.lowBits_bound` for the concrete instance (approved parameters). -/
theorem concrete_lowBits_bound (hp : p.isApproved) (r : Rq) :
    polyNorm ((concretePrimitives p).lowBits r) ≤ p.gamma2 := by
  rw [polyNorm_eq_cInfNorm]
  exact concreteRounding_lowBits_bound p (by rcases hp with rfl | rfl | rfl <;> decide)
    (by rcases hp with rfl | rfl | rfl <;> decide) r

/-- `Primitives.Laws.hide_low` for the concrete instance (approved parameters). -/
theorem concrete_hide_low (hp : p.isApproved) (r s : Rq) (b : ℕ)
    (hs : polyNorm s ≤ b)
    (hlow : polyNorm ((concretePrimitives p).lowBits r) + b < p.gamma2) :
    (concretePrimitives p).highBits (r + s) = (concretePrimitives p).highBits r := by
  apply concreteRounding_hide_low_of_isApproved p hp r s b
  · rwa [← polyNorm_eq_cInfNorm]
  · rw [← polyNorm_eq_cInfNorm]; exact hlow

/-- `Primitives.Laws.highBitsShift_injective` for the concrete instance (approved parameters). -/
theorem concrete_highBitsShift_injective (hp : p.isApproved) :
    Function.Injective (concretePrimitives p).highBitsShift :=
  highBitsShift_injective_of_isApproved p hp

/-- `Primitives.Laws.useHint_makeHint` for the concrete instance (approved parameters). -/
theorem concrete_useHint_makeHint (hp : p.isApproved) (z r : Rq) (hz : polyNorm z ≤ p.gamma2) :
    (concretePrimitives p).useHint ((concretePrimitives p).makeHint z r) r
      = (concretePrimitives p).highBits (r + z) := by
  apply concreteRounding_useHint_correct_of_isApproved p hp z r
  rwa [← polyNorm_eq_cInfNorm]

/-- `Primitives.Laws.power2Round_decomp` for the concrete instance. -/
theorem concrete_power2Round_decomp (r : Rq) :
    (concretePrimitives p).power2RoundShift ((concretePrimitives p).power2Round r).1
      + ((concretePrimitives p).power2Round r).2 = r :=
  concretePower2Round_high_low_decomp r

/-- `Primitives.Laws.power2Round_bound` for the concrete instance. -/
theorem concrete_power2Round_bound (r : Rq) :
    polyNorm ((concretePrimitives p).power2Round r).2 ≤ 2 ^ (droppedBits - 1) := by
  rw [polyNorm_eq_cInfNorm]
  change LatticeCrypto.cInfNorm (power2RoundLow r) ≤ 2 ^ (droppedBits - 1)
  rw [← concretePower2Round_remainder_eq_low]
  exact concretePower2Round_bound r

/-! ## `expandMask_bound` (restated to the FIPS-204 `z`-range, now provable)

The concrete `expandMask` decodes each coefficient through `polyZUnpack p`, i.e.
`bitUnpackPoly bytes (-γ₁ + 1) γ₁`. By the decode-range bound `bitUnpackPoly_get`, every coefficient
is `γ₁ - v` for a `width`-bit value `v` with `width = rangeWidth (-γ₁ + 1) γ₁`. For the approved
parameter sets `2 ^ width = 2 γ₁`, so `v ≤ 2 γ₁ - 1` and `γ₁ - v ∈ [-(γ₁ - 1), γ₁]`, whose centered
representative (since `2 γ₁ < q`) is `γ₁ - v` itself, of absolute value at most `γ₁`. The argument
is purely about the decoder's output range and independent of the opaque SHAKE byte stream. -/

/-- Decode-range infinity-norm bound for a `z`-range `bitUnpackPoly`: every coefficient of
`bitUnpackPoly bytes (-γ + 1) γ` has centered absolute value at most `γ`, provided the bit width
satisfies `2 ^ width = 2 γ` (true for FIPS-204 `γ₁`, a power of two) and `2 γ < q`. -/
theorem bitUnpackPoly_z_cInfNorm_le (bytes : ByteArray) (γ : ℕ)
    (hwidth : (2 : ℕ) ^ rangeWidth (-(γ : ℤ) + 1) (γ : ℤ) = 2 * γ)
    (hq : 2 * γ < modulus) :
    LatticeCrypto.cInfNorm (bitUnpackPoly bytes (-(γ : ℤ) + 1) (γ : ℤ)) ≤ γ := by
  rw [LatticeCrypto.cInfNorm_le_iff]
  intro i
  obtain ⟨v, hv, hget⟩ := bitUnpackPoly_get bytes (-(γ : ℤ) + 1) (γ : ℤ) i
  rw [hget, hwidth] at *
  have hbound : ((γ : ℤ) - (v : ℤ)).natAbs ≤ γ := by omega
  rw [LatticeCrypto.centeredRepr_intCast_eq_of_natAbs_le ((γ : ℤ) - (v : ℤ)) hbound (by omega)]
  exact hbound

/-- For each approved parameter set the `z`-range bit width satisfies `2 ^ width = 2 γ₁` (because
`γ₁` is a power of two) and `2 γ₁ < q`. -/
private theorem approved_gamma1_width (hp : p.isApproved) :
    (2 : ℕ) ^ rangeWidth (-(p.gamma1 : ℤ) + 1) (p.gamma1 : ℤ) = 2 * p.gamma1 ∧
      2 * p.gamma1 < modulus := by
  rcases hp with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

/-- `Primitives.Laws.expandMask_bound` (restated bound `γ₁`) for the concrete instance, at any
approved parameter set. -/
theorem concrete_expandMask_bound (hp : p.isApproved) (rhoDoublePrime : Bytes 64) (kappa : ℕ) :
    polyVecBounded ((concretePrimitives p).expandMask rhoDoublePrime kappa) p.gamma1 := by
  obtain ⟨hwidth, hq⟩ := approved_gamma1_width p hp
  rw [polyVecBounded, polyVecNorm, LatticeCrypto.PolyVec.cInfNorm_le_iff]
  intro j
  -- Each component is `polyZUnpack p (<opaque SHAKE stream>)`; the bound is a decode-range
  -- property, so generalize the opaque byte argument and apply the decoder bound.
  change polyNorm ((MLDSA.Concrete.expandMask rhoDoublePrime kappa p).get j) ≤ p.gamma1
  rw [polyNorm_eq_cInfNorm]
  unfold MLDSA.Concrete.expandMask
  rw [Vector.get_ofFn]
  -- The decoder argument is an opaque SHAKE stream; the bound holds for any byte input,
  -- since `polyZUnpack p bytes = bitUnpackPoly bytes (-γ₁ + 1) γ₁`.
  exact bitUnpackPoly_z_cInfNorm_le _ p.gamma1 hwidth hq

/-! ## `w1Encode_injective` (restated to `Set.InjOn` on the valid range, now provable)

The concrete `w1Encode` packs each `High` coefficient via `simpleBitPackPoly` at the bit width
`simpleWidth ((q-1)/(2γ₂) - 1)`. On the valid commitment range — every component an actual
`highBits` output — each coefficient lies in `[0, (q-1)/(2γ₂) - 1]` (`highBits_coeff_val_lt_m`),
which fits in that bit width, so the packer is inverted by `simpleBitUnpackPoly` and is injective.
This is exactly the `Set.InjOn` predicate of the restated abstract field, since the abstract
validity set is the image of `highBits`. -/

/-- Every approved-parameter `highBits` coefficient fits in the `w₁` packer's bit width. -/
private theorem highBits_coeff_val_lt_width (hp : p.isApproved) (r : Rq) (c : Fin ringDegree) :
    ((MLDSA.Concrete.highBits p r).get c).val
      < 2 ^ MLDSA.Concrete.simpleWidth ((modulus - 1) / (2 * p.gamma2) - 1) := by
  have hlt : ((MLDSA.Concrete.highBits p r).get c).val < (modulus - 1) / (2 * p.gamma2) :=
    MLDSA.Concrete.highBits_coeff_val_lt_m p hp r c
  -- `(q-1)/(2γ₂) ≤ 2 ^ simpleWidth ((q-1)/(2γ₂) - 1)`.
  have hwin : (modulus - 1) / (2 * p.gamma2)
      ≤ 2 ^ MLDSA.Concrete.simpleWidth ((modulus - 1) / (2 * p.gamma2) - 1) := by
    rcases hp with rfl | rfl | rfl <;> decide
  omega

/-- `Primitives.Laws.w1Encode_injective` (restated to `Set.InjOn`) for the concrete instance, at any
approved parameter set: `w1Encode` is injective on commitment vectors all of whose components are
`highBits` outputs. -/
theorem concrete_w1Encode_injOn (hp : p.isApproved) :
    Set.InjOn (concretePrimitives p).w1Encode
      { w : Vector (concretePrimitives p).High p.k |
          ∀ i : Fin p.k, w.get i ∈ Set.range (concretePrimitives p).highBits } := by
  -- The concrete validity set sits inside the bit-width set on which `w1Encode_injOn` applies.
  apply Set.InjOn.mono (s₂ := { w : Vector High p.k | ∀ i : Fin p.k, ∀ c : Fin ringDegree,
      ((w.get i).get c).val
        < 2 ^ MLDSA.Concrete.simpleWidth ((modulus - 1) / (2 * p.gamma2) - 1) })
  · intro w hw i c
    obtain ⟨r, hr⟩ := hw i
    rw [show w.get i = MLDSA.Concrete.highBits p r from hr.symm]
    exact highBits_coeff_val_lt_width p hp r c
  · exact MLDSA.Concrete.w1Encode_injOn p

/-! ## Sampler-bound fields (now provable from the fuel-recursive samplers)

The `sampleInBall` and `expandS` rejection samplers are defined by fuel-bounded structural recursion
(see `Concrete/Sampling.lean`), which exposes equation lemmas. Their structural output ranges are
banked as `sampleInBall_norm` and `expandS_bound` there; the `concrete_*` wrappers below state them
at the `concretePrimitives` interface. -/

/-- `Primitives.Laws.sampleInBall_norm` for the concrete instance: `SampleInBall(c̃)` has centered
infinity norm at most `1` (its coefficients lie in `{-1, 0, +1}`). -/
theorem concrete_sampleInBall_norm (cTilde : CommitHashBytes p) :
    polyNorm ((concretePrimitives p).sampleInBall cTilde) ≤ 1 :=
  MLDSA.Concrete.sampleInBall_norm p cTilde

/-- `Primitives.Laws.expandS_bound` for the concrete instance: `ExpandS(ρ')` produces secret vectors
with every coefficient bounded by `η`. -/
theorem concrete_expandS_bound (rhoPrime : Bytes 64) :
    polyVecBounded ((concretePrimitives p).expandS rhoPrime).1 p.eta ∧
      polyVecBounded ((concretePrimitives p).expandS rhoPrime).2 p.eta :=
  MLDSA.Concrete.expandS_bound rhoPrime p

/-- `Primitives.Laws.sampleInBall_smul_bound` for the concrete instance: the challenge–secret
product `c · sⱼ` has centered infinity norm at most `β = τ · η` whenever `‖s‖∞ ≤ η`. Assembled from
the generic negacyclic-convolution bound `‖c · sⱼ‖∞ ≤ ‖c‖₁ · ‖sⱼ‖∞` (`cInfNorm_mul_le`), the
challenge `ℓ₁` count `‖SampleInBall(c̃)‖₁ ≤ τ` (`sampleInBall_l1Norm`), and the component law
`(c • s).get j = c * sⱼ` (`coeffScalarVecMul_get`). -/
theorem concrete_sampleInBall_smul_bound
    (cTilde : CommitHashBytes p) {k : ℕ} (s : RqVec k)
    (hs : polyVecBounded s p.eta) :
    polyVecNorm (concreteNTTRingOps.coeffScalarVecMul
      ((concretePrimitives p).sampleInBall cTilde) s) ≤ p.beta := by
  rw [polyVecNorm, LatticeCrypto.PolyVec.cInfNorm_le_iff]
  intro j
  rw [LatticeCrypto.TransformOps.coeffScalarVecMul_get (laws := concreteNTTRingLaws)]
  change polyNorm _ ≤ p.beta
  rw [polyNorm_eq_cInfNorm]
  have hc : (concretePrimitives p).sampleInBall cTilde = MLDSA.Concrete.sampleInBall p cTilde := rfl
  rw [hc]
  refine le_trans
    (LatticeCrypto.cInfNorm_mul_le (MLDSA.Concrete.sampleInBall p cTilde) (s.get j)) ?_
  have hl1 : LatticeCrypto.l1Norm (MLDSA.Concrete.sampleInBall p cTilde) ≤ p.tau :=
    MLDSA.Concrete.sampleInBall_l1Norm p cTilde
  have hsj : LatticeCrypto.cInfNorm (s.get j) ≤ p.eta := by
    have := (LatticeCrypto.PolyVec.cInfNorm_le_iff (ops := normOps)).mp hs j
    rwa [← polyNorm_eq_cInfNorm]
  calc LatticeCrypto.l1Norm (MLDSA.Concrete.sampleInBall p cTilde)
        * LatticeCrypto.cInfNorm (s.get j)
      ≤ p.tau * p.eta := Nat.mul_le_mul hl1 hsj
    _ = p.beta := rfl

/-! ## `Primitives.Laws` status for `concretePrimitives` (no full witness — by design)

Thirteen `Primitives.Laws` fields are now **proven axiom-clean** for the concrete instance at any
approved parameter set: the eight algebraic fields (`concrete_transform`,
`concrete_high_low_decomp`, `concrete_lowBits_bound`, `concrete_hide_low`,
`concrete_highBitsShift_injective`, `concrete_useHint_makeHint`, `concrete_power2Round_decomp`,
`concrete_power2Round_bound`); the two byte-encoding fields `concrete_expandMask_bound` and
`concrete_w1Encode_injOn`; the two sampler-bound fields `concrete_sampleInBall_norm` and
`concrete_expandS_bound` (extracted by fuel induction from the structural-recursion samplers in
`Concrete/Sampling.lean`); and the challenge-product bound `concrete_sampleInBall_smul_bound`
(assembled from the generic negacyclic-convolution infinity-norm bound and the challenge `ℓ₁`
count). There are no longer any false-as-stated fields.

We deliberately do **not** assemble a full `Primitives.Laws (concretePrimitives p) …` witness here,
because one field remains undischarged for a reason that is not a statement bug:

* `keyVector_t0_determined`: an inherent ROM modeling assumption, left abstract (see its docstring
  in `Primitives.lean`).

A `sorry`-backed aggregate witness is intentionally omitted: it would assert the still-abstract ROM
field, which is unsound to bank. The thirteen proven `concrete_*` lemmas above stand on their own
and are safe to consume. A full `Primitives.Laws` witness is now inhabitable once the single
`keyVector_t0_determined` modeling assumption is supplied as a hypothesis (it is satisfiable, e.g.
when `ExpandSeed` is injective on the relevant data). -/

end MLDSA.Concrete
