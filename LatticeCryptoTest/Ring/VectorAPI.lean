/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import LatticeCrypto.Ring.VectorBackend

/-!
# Vector polynomial API consumers

Coefficient observations compose with the public representation and arithmetic laws.
The degree-two multiplication example distinguishes negacyclic multiplication from
pointwise vector multiplication.
-/

public section

namespace LatticeCryptoTest.Ring.VectorAPI

open LatticeCrypto

universe u

example {R : Type u} [CommRing R] {n : Nat} (f g : Fin n → R) :
    Poly.ofPi (fun i => f i + g i) = Poly.ofPi f + Poly.ofPi g := by
  apply Poly.ext_get_eq
  intro i
  simp

/-- The polynomial `X` in the degree-two negacyclic ring. -/
def variablePoly : Poly Int 2 := Poly.ofPi (fun i => if i = 1 then 1 else 0)

example : ((vectorNegacyclicRing Int 2).mul variablePoly variablePoly).get 0 = -1 := by
  simp [vectorNegacyclicRing_mul, vectorKernel_mul_get, negacyclicConvCoeff,
    variablePoly, Fintype.sum_prod_type, Fin.sum_univ_two]

end LatticeCryptoTest.Ring.VectorAPI
