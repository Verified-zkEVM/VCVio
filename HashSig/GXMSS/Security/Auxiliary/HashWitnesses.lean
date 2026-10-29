/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.HashInstance
public import HashSig.GXMSS.Encoding.Incomparable

/-!
# Common-domain collision witnesses and finite coordinate search

These deterministic witnesses support the chain and tree arguments of ePrint 2025/055.
They make no hardness or distribution claim.
-/

public section

namespace GXMSS.Security

/-- An ordered pair of raw same-tweak inputs. -/
structure HashCollision (T X : Type*) where
  /-- Common tweak used by both evaluations. -/
  tweak : T
  /-- First input. -/
  first : X
  /-- Second input. -/
  second : X

/-- The recorded inputs differ and collide under one public seed and tweak. -/
@[expose] def HashCollision.Sound {PP T X H : Type} (f : TweakableHash PP T X H)
    (pp : PP) (c : HashCollision T X) : Prop :=
  c.first ≠ c.second ∧ f.eval pp c.tweak c.first = f.eval pp c.tweak c.second

/-- Injective input embeddings transport a collision without requiring disjoint images. -/
theorem collision_embedding {PP T X H A : Type} (f : TweakableHash PP T X H)
    (pp : PP) (t : T) (embed : A ↪ X) {x y : A} (hne : x ≠ y)
    (heq : f.eval pp t (embed x) = f.eval pp t (embed y)) :
    (HashCollision.mk t (embed x) (embed y)).Sound f pp :=
  ⟨fun h => hne (embed.injective h), heq⟩

/-- Scan finite coordinates in increasing order for a decidable property. -/
@[expose] def findCoordinate {n : ℕ} (p : Fin n → Prop) [DecidablePred p] : Option (Fin n) :=
  (List.finRange n).find? (fun i => decide (p i))

/-- Every returned coordinate satisfies the searched property. -/
theorem findCoordinate_sound {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    {i : Fin n} (hi : findCoordinate p = some i) : p i := by
  have hp : decide (p i) = true := List.find?_some (p := fun j => decide (p j)) hi
  exact of_decide_eq_true hp

/-- A finite scan succeeds whenever any coordinate satisfies the property. -/
theorem findCoordinate_isSome {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (hp : ∃ i, p i) : (findCoordinate p).isSome := by
  simpa [findCoordinate] using hp

/-- Select a coordinate at which two finite vectors differ. -/
@[expose] def findUnequalCoordinate {H : Type*} [DecidableEq H] {n : ℕ}
    (x y : Fin n → H) : Option (Fin n) := findCoordinate (fun i => x i ≠ y i)

/-- The unequal-vector finder returns an actual disagreement. -/
theorem findUnequalCoordinate_sound {H : Type*} [DecidableEq H] {n : ℕ}
    (x y : Fin n → H) {i : Fin n} (hi : findUnequalCoordinate x y = some i) :
    x i ≠ y i := findCoordinate_sound _ hi

/-- Distinct vectors yield a coordinate, including empty-domain impossibility. -/
theorem findUnequalCoordinate_isSome {H : Type*} [DecidableEq H] {n : ℕ}
    (x y : Fin n → H) (hne : x ≠ y) : (findUnequalCoordinate x y).isSome := by
  apply findCoordinate_isSome
  by_contra h
  push Not at h
  exact hne (funext h)

/-- Select a coordinate where the second codeword is smaller than the first. -/
@[expose] def findSmallerCoordinate {n radix : ℕ}
    (x y : Encoding.Codeword n radix) : Option (Fin n) :=
  findCoordinate (fun i => y i < x i)

/-- A returned digit supplies the strict earlier-start inequality. -/
theorem findSmallerCoordinate_sound {n radix : ℕ}
    (x y : Encoding.Codeword n radix) {i : Fin n}
    (hi : findSmallerCoordinate x y = some i) : y i < x i :=
  findCoordinate_sound (fun j => y j < x j) hi

/-- Distinct successful words of the global incomparable code supply a smaller second digit. -/
theorem findSmallerCoordinate_isSome_of_successes {PP M R E : Type*} {n radix : ℕ}
    (enc : Encoding.IncomparableEncoding PP M R E n radix)
    (p p' : PP) (m m' : M) (r r' : R) (e e' : E)
    {x y : Encoding.Codeword n radix} (hx : enc.value p m r e = some x)
    (hy : enc.value p' m' r' e' = some y) (hne : x ≠ y) :
    (findSmallerCoordinate x y).isSome :=
  findCoordinate_isSome _ (enc.incomparableWords_of_successes p p' m m' r r' e e' hx hy hne).2

end GXMSS.Security
