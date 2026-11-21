/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.HashInstance

/-!
# Oriented common-domain hash witnesses

A same-tweak collision keeps its ordered input pair. Injective input embeddings preserve the
collision without a disjointness assumption on their images.
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

end GXMSS.Security
