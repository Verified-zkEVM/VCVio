/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import LatticeCrypto.Ring.VectorBackend

/-!
# Shared Certification Scaffolding For Concrete NTTs

This module provides the proof-facing structural route for concrete NTT
developments, used by ML-KEM, ML-DSA and Falcon. It avoids a dense matrix
certificate. A `ButterflyLayout` records a proof-relevant partition of a
coefficient index type into pairs. This lets concrete loop developments
separate the indexing proof (that an array loop implements a layout) from the
small ring calculation showing that matching forward and inverse butterflies
cancel. `ScaledStage` then composes those local facts and tracks the final
normalization factor.
-/

@[expose] public section



namespace LatticeCrypto.NTTCert

universe u

variable {Coeff : Type u} {backend : LatticeCrypto.PolyBackend Coeff}

/-! ## Coefficient-function transforms -/

/-- Lift a transformation on `Fin`-indexed coefficient functions to an
arbitrary polynomial backend.  Unlike unfolding a nested stage list through
`Vector.ofFn`, this boundary keeps wrapper proofs at constant elaboration
depth. -/
def applyCoeffTransform (backend : LatticeCrypto.PolyBackend Coeff)
    (transform : (Fin backend.degree → Coeff) → (Fin backend.degree → Coeff))
    (input : backend.Poly) : backend.Poly :=
  backend.build (transform (backend.coeff input))

/-- Lift a coefficient-level roundtrip through a polynomial backend. -/
theorem applyCoeffTransform_comp
    (forward inverse : (Fin backend.degree → Coeff) → (Fin backend.degree → Coeff))
    (hroundtrip : ∀ input, inverse (forward input) = input)
    (input : backend.Poly) :
    applyCoeffTransform backend inverse (applyCoeffTransform backend forward input) = input := by
  unfold applyCoeffTransform
  have hcoeff : backend.coeff (backend.build (forward (backend.coeff input))) =
      forward (backend.coeff input) := by
    funext coord
    exact backend.coeff_build _ coord
  rw [hcoeff, hroundtrip, backend.build_coeff]

/-- Lift additivity of a coefficient transformation through a backend whose
addition is pointwise on coefficients. -/
theorem applyCoeffTransform_add
    (transform : (Fin backend.degree → Coeff) → (Fin backend.degree → Coeff))
    [Add Coeff]
    [Add backend.Poly]
    (hcoeffAdd : ∀ left right : backend.Poly,
      backend.coeff (left + right) = backend.coeff left + backend.coeff right)
    (htransformAdd : ∀ left right, transform (left + right) =
      transform left + transform right)
    (left right : backend.Poly) :
    applyCoeffTransform backend transform (left + right) =
      applyCoeffTransform backend transform left + applyCoeffTransform backend transform right := by
  unfold applyCoeffTransform
  rw [hcoeffAdd left right, htransformAdd]
  rw [← backend.build_coeff
    (backend.build (transform (backend.coeff left)) +
      backend.build (transform (backend.coeff right)))]
  congr 1
  rw [hcoeffAdd]
  funext coord
  simp only [backend.coeff_build, Pi.add_apply]

/-- Lift subtraction preservation through a pointwise backend. -/
theorem applyCoeffTransform_sub
    (transform : (Fin backend.degree → Coeff) → (Fin backend.degree → Coeff))
    [Sub Coeff]
    [Sub backend.Poly]
    (hcoeffSub : ∀ left right : backend.Poly,
      backend.coeff (left - right) = backend.coeff left - backend.coeff right)
    (htransformSub : ∀ left right, transform (left - right) =
      transform left - transform right)
    (left right : backend.Poly) :
    applyCoeffTransform backend transform (left - right) =
      applyCoeffTransform backend transform left - applyCoeffTransform backend transform right := by
  unfold applyCoeffTransform
  rw [hcoeffSub left right, htransformSub]
  rw [← backend.build_coeff
    (backend.build (transform (backend.coeff left)) -
      backend.build (transform (backend.coeff right)))]
  congr 1
  rw [hcoeffSub]
  funext coord
  simp only [backend.coeff_build, Pi.sub_apply]

/-- Lift zero preservation through a pointwise backend. -/
theorem applyCoeffTransform_zero
    (transform : (Fin backend.degree → Coeff) → (Fin backend.degree → Coeff))
    [Zero Coeff]
    [Zero backend.Poly]
    (hcoeffZero : backend.coeff (0 : backend.Poly) = 0)
    (htransformZero : transform 0 = 0) :
    applyCoeffTransform backend transform 0 = 0 := by
  unfold applyCoeffTransform
  rw [hcoeffZero, htransformZero]
  calc
    backend.build 0 = backend.build (backend.coeff 0) := congrArg backend.build hcoeffZero.symm
    _ = 0 := backend.build_coeff 0

/-! ## Structural butterfly certificates -/

universe v w

variable {R : Type*} [CommRing R]

/-- A partition of the coefficient coordinates `Coord` into pairs indexed by
`Pair`.  `false` names the left coordinate and `true` the right coordinate.

Using an equivalence rather than separate index functions packages coverage,
disjointness, and uniqueness in the form needed by a butterfly-stage proof. -/
structure ButterflyLayout (Pair : Type v) (Coord : Type w) where
  /-- The coordinate of each pair's left (`false`) and right (`true`) side. -/
  equiv : Pair × Bool ≃ Coord

/-- The standard blocked NTT layout.  A pair is a block number and an offset
inside that block; its coordinates are
`group * (2 * len) + offset` and that index plus `len`.

This layout is directly usable by the nested `start`/`j` loops in the FIPS 203
and FIPS 204 kernels and packages their coverage/disjointness arithmetic. -/
def blockLayout (groups len : Nat) :
    ButterflyLayout (Fin groups × Fin len) (Fin (groups * (2 * len))) where
  equiv := (Equiv.prodAssoc (Fin groups) (Fin len) Bool).trans
    ((Equiv.refl (Fin groups)).prodCongr (Equiv.prodComm (Fin len) Bool) |>.trans
      ((Equiv.refl (Fin groups)).prodCongr
        ((finTwoEquiv.symm.prodCongr (Equiv.refl (Fin len))).trans finProdFinEquiv) |>.trans
          finProdFinEquiv))

@[simp] theorem blockLayout_left_val (groups len : Nat)
    (group : Fin groups) (offset : Fin len) :
    ((blockLayout groups len).equiv ((group, offset), false)).val =
      group.val * (2 * len) + offset.val := by
  have h : offset.val + 2 * len * group.val = group.val * (2 * len) + offset.val := by
    ac_rfl
  simpa [blockLayout, finProdFinEquiv, finTwoEquiv] using h

@[simp] theorem blockLayout_right_val (groups len : Nat)
    (group : Fin groups) (offset : Fin len) :
    ((blockLayout groups len).equiv ((group, offset), true)).val =
      group.val * (2 * len) + len + offset.val := by
  have h : offset.val + len + 2 * len * group.val =
      group.val * (2 * len) + len + offset.val := by
    ac_rfl
  simpa [blockLayout, finProdFinEquiv, finTwoEquiv] using h

/-- The forward two-coordinate butterfly `(u, v) ↦ (u + z*v, u - z*v)`. -/
def forwardButterfly (z u v : R) : Bool → R
  | false => u + z * v
  | true => u - z * v

/-- The inverse-oriented two-coordinate butterfly
`(x, y) ↦ (x + y, z⁻¹*(x - y))`.

Some concrete NTT specifications write the second coordinate as
`(-z⁻¹) * (y - x)`; that expression is propositionally equal to this one. -/
def inverseButterfly (zInv x y : R) : Bool → R
  | false => x + y
  | true => zInv * (x - y)

/-- Apply one forward butterfly to every pair in a layout. -/
def forwardStage {Pair : Type v} {Coord : Type w}
    (layout : ButterflyLayout Pair Coord) (z : Pair → R)
    (input : Coord → R) : Coord → R := fun coord =>
  let pairSide := layout.equiv.symm coord
  forwardButterfly (z pairSide.1)
    (input (layout.equiv (pairSide.1, false)))
    (input (layout.equiv (pairSide.1, true))) pairSide.2

/-- Apply one inverse butterfly to every pair in a layout. -/
def inverseStage {Pair : Type v} {Coord : Type w}
    (layout : ButterflyLayout Pair Coord) (zInv : Pair → R)
    (input : Coord → R) : Coord → R := fun coord =>
  let pairSide := layout.equiv.symm coord
  inverseButterfly (zInv pairSide.1)
    (input (layout.equiv (pairSide.1, false)))
    (input (layout.equiv (pairSide.1, true))) pairSide.2

/-- Pointwise scalar multiplication for coefficient functions. -/
def scaleCoeffs {Coord : Type w} (c : R) (input : Coord → R) : Coord → R :=
  fun coord => c * input coord

/-- A matching inverse butterfly cancels a forward butterfly up to the factor
`2` introduced by the unnormalised sum/difference convention. -/
theorem inverseButterfly_forwardButterfly
    (z zInv u v : R) (hz : zInv * z = 1) :
    inverseButterfly zInv (forwardButterfly z u v false)
        (forwardButterfly z u v true) =
      fun side => scaleCoeffs (2 : R) (fun b => if b then v else u) side := by
  funext side
  cases side <;>
    simp only [inverseButterfly, forwardButterfly, scaleCoeffs]
  · simp only [Bool.false_eq_true, ↓reduceIte]
    ring
  · calc
      zInv * (u + z * v - (u - z * v)) = zInv * (z * v + z * v) := by ring
      _ = (zInv * z) * v + (zInv * z) * v := by ring
      _ = 2 * v := by rw [hz]; ring

/-- Matching inverse and forward stages cancel pointwise up to multiplication
by `2`.  The only concrete algebraic obligation is the per-pair twiddle inverse
law; all schedule coverage and non-overlap follows from `layout.equiv`. -/
theorem inverseStage_forwardStage
    {Pair : Type v} {Coord : Type w} (layout : ButterflyLayout Pair Coord)
    (z zInv : Pair → R) (hz : ∀ pair, zInv pair * z pair = 1)
    (input : Coord → R) :
    inverseStage layout zInv (forwardStage layout z input) =
      scaleCoeffs (2 : R) input := by
  funext coord
  rw [← layout.equiv.apply_symm_apply coord]
  obtain ⟨pair, side⟩ := layout.equiv.symm coord
  cases side <;>
    simp only [inverseStage, forwardStage, inverseButterfly, forwardButterfly, scaleCoeffs,
      Equiv.symm_apply_apply]
  · ring
  · calc
      zInv pair *
          (input (layout.equiv (pair, false)) +
              z pair * input (layout.equiv (pair, true)) -
            (input (layout.equiv (pair, false)) -
              z pair * input (layout.equiv (pair, true)))) =
        zInv pair *
          (z pair * input (layout.equiv (pair, true)) +
            z pair * input (layout.equiv (pair, true))) := by ring
      _ =
          (zInv pair * z pair) * input (layout.equiv (pair, true)) +
            (zInv pair * z pair) * input (layout.equiv (pair, true)) := by ring
      _ = 2 * input (layout.equiv (pair, true)) := by rw [hz]; ring

/-- A stage commutes with pointwise scalar multiplication. -/
theorem inverseStage_scaleCoeffs
    {Pair : Type v} {Coord : Type w} (layout : ButterflyLayout Pair Coord)
    (zInv : Pair → R) (c : R) (input : Coord → R) :
    inverseStage layout zInv (scaleCoeffs c input) =
      scaleCoeffs c (inverseStage layout zInv input) := by
  funext coord
  rw [← layout.equiv.apply_symm_apply coord]
  obtain ⟨pair, side⟩ := layout.equiv.symm coord
  cases side <;>
    simp only [inverseStage, inverseButterfly, scaleCoeffs, Equiv.symm_apply_apply]
  <;> ring

/-- A forward butterfly stage is additive. -/
theorem forwardStage_add
    {Pair : Type v} {Coord : Type w} (layout : ButterflyLayout Pair Coord)
    (z : Pair → R) (left right : Coord → R) :
    forwardStage layout z (left + right) =
      forwardStage layout z left + forwardStage layout z right := by
  funext coord
  rw [← layout.equiv.apply_symm_apply coord]
  obtain ⟨pair, side⟩ := layout.equiv.symm coord
  cases side <;>
    simp only [forwardStage, forwardButterfly, Equiv.symm_apply_apply, Pi.add_apply]
  <;> ring

/-- A forward butterfly stage preserves subtraction. -/
theorem forwardStage_sub
    {Pair : Type v} {Coord : Type w} (layout : ButterflyLayout Pair Coord)
    (z : Pair → R) (left right : Coord → R) :
    forwardStage layout z (left - right) =
      forwardStage layout z left - forwardStage layout z right := by
  funext coord
  rw [← layout.equiv.apply_symm_apply coord]
  obtain ⟨pair, side⟩ := layout.equiv.symm coord
  cases side <;>
    simp only [forwardStage, forwardButterfly, Equiv.symm_apply_apply, Pi.sub_apply]
  <;> ring

/-- A forward butterfly stage preserves zero. -/
theorem forwardStage_zero
    {Pair : Type v} {Coord : Type w} (layout : ButterflyLayout Pair Coord)
    (z : Pair → R) :
    forwardStage layout z 0 = 0 := by
  funext coord
  rw [← layout.equiv.apply_symm_apply coord]
  obtain ⟨pair, side⟩ := layout.equiv.symm coord
  cases side <;>
    simp only [forwardStage, forwardButterfly, Equiv.symm_apply_apply, Pi.zero_apply, mul_zero,
      add_zero, sub_zero]

/-- Package the two laws needed to compose an unnormalised transform stage:
the inverse/forward roundtrip and compatibility of the inverse with a scalar
accumulated by inner stages. -/
structure ScaledStage (R : Type*) [CommRing R] (Coord : Type w) where
  /-- The forward stage map on coefficient vectors. -/
  forward : (Coord → R) → (Coord → R)
  /-- The inverse stage map, which undoes `forward` up to multiplication by `scalar`. -/
  inverse : (Coord → R) → (Coord → R)
  /-- The factor by which `inverse` composed with `forward` scales its input; a butterfly
  stage has factor `2`. -/
  scalar : R
  inverse_forward : ∀ input, inverse (forward input) = scaleCoeffs scalar input
  inverse_scale : ∀ c input,
    inverse (scaleCoeffs c input) = scaleCoeffs c (inverse input)
  forward_add : ∀ left right, forward (left + right) = forward left + forward right
  forward_sub : ∀ left right, forward (left - right) = forward left - forward right
  forward_zero : forward 0 = 0

/-- Build a composable stage certificate from a butterfly layout and matching
twiddle tables.  `zInv` is the coefficient multiplying `x - y` in the inverse
butterfly, so a loop written as `zRev * (y - x)` supplies `zInv = -zRev`; the
obligation is `zInv * z = 1`. -/
def butterflyStage {Pair : Type v} {Coord : Type w} (layout : ButterflyLayout Pair Coord)
    (z zInv : Pair → R) (hz : ∀ pair, zInv pair * z pair = 1) :
    ScaledStage R Coord where
  forward := forwardStage layout z
  inverse := inverseStage layout zInv
  scalar := 2
  inverse_forward := inverseStage_forwardStage layout z zInv hz
  inverse_scale := inverseStage_scaleCoeffs layout zInv
  forward_add := forwardStage_add layout z
  forward_sub := forwardStage_sub layout z
  forward_zero := forwardStage_zero layout z

/-- Apply a list of stages from left to right. -/
def forwardStages {Coord : Type w} : List (ScaledStage R Coord) →
    (Coord → R) → (Coord → R)
  | [], input => input
  | stage :: stages, input => forwardStages stages (stage.forward input)

/-- Apply the inverse stages in reverse order. -/
def inverseStages {Coord : Type w} : List (ScaledStage R Coord) →
    (Coord → R) → (Coord → R)
  | [], input => input
  | stage :: stages, input => stage.inverse (inverseStages stages input)

/-- Product of the scale factors introduced by a list of stages, in the order
in which the corresponding inverse stages expose them. -/
def stageScalar {Coord : Type w} : List (ScaledStage R Coord) → R
  | [] => 1
  | stage :: stages => stageScalar stages * stage.scalar

/-- A reverse sequence of certified inverse stages cancels its forward stage
sequence, accumulating only the product of the per-stage scale factors. -/
theorem inverseStages_forwardStages {Coord : Type w}
    (stages : List (ScaledStage R Coord)) (input : Coord → R) :
    inverseStages stages (forwardStages stages input) =
      scaleCoeffs (stageScalar stages) input := by
  induction stages generalizing input with
  | nil =>
      funext coord
      simp [inverseStages, forwardStages, stageScalar, scaleCoeffs]
  | cons stage stages ih =>
      simp only [forwardStages, inverseStages, stageScalar]
      rw [ih (stage.forward input), stage.inverse_scale, stage.inverse_forward]
      funext coord
      simp [scaleCoeffs]
      ring

/-- Normalize the accumulated stage factor.  Concrete NTT developments use
this with their final `nInv` constant, leaving only the small closed identity
`nInv * stageScalar stages = 1`. -/
theorem scale_inverseStages_forwardStages {Coord : Type w}
    (stages : List (ScaledStage R Coord)) (nInv : R)
    (hnorm : nInv * stageScalar stages = 1) (input : Coord → R) :
    scaleCoeffs nInv (inverseStages stages (forwardStages stages input)) = input := by
  rw [inverseStages_forwardStages]
  funext coord
  simp only [scaleCoeffs]
  rw [← mul_assoc, hnorm, one_mul]

/-- A sequence of certified forward stages is additive. -/
theorem forwardStages_add {Coord : Type w} (stages : List (ScaledStage R Coord))
    (left right : Coord → R) :
    forwardStages stages (left + right) =
      forwardStages stages left + forwardStages stages right := by
  induction stages generalizing left right with
  | nil => rfl
  | cons stage stages ih =>
      simp only [forwardStages]
      rw [stage.forward_add, ih]

/-- A sequence of certified forward stages preserves subtraction. -/
theorem forwardStages_sub {Coord : Type w} (stages : List (ScaledStage R Coord))
    (left right : Coord → R) :
    forwardStages stages (left - right) =
      forwardStages stages left - forwardStages stages right := by
  induction stages generalizing left right with
  | nil => rfl
  | cons stage stages ih =>
      simp only [forwardStages]
      rw [stage.forward_sub, ih]

/-- A sequence of certified forward stages preserves zero. -/
theorem forwardStages_zero {Coord : Type w} (stages : List (ScaledStage R Coord)) :
    forwardStages stages 0 = 0 := by
  induction stages with
  | nil => rfl
  | cons stage stages ih =>
      simp only [forwardStages]
      rw [stage.forward_zero, ih]

end LatticeCrypto.NTTCert
