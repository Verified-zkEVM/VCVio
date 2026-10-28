/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Oracle

/-!
# Encodings of table entries
-/

public section

open OracleComp OracleSpec

namespace GroupModel

variable {S : Type} {V W E : S → Type}

/-- An encoding query names a sort and a handle in that sort. -/
@[expose] def encSpec (E : S → Type) : OracleSpec (S × Handle) := fun q => E q.1

/-- Encode a table entry without changing the table. -/
@[expose] def encImpl [∀ s, Zero (V s)] {m : Type → Type} [Monad m]
    (enc : (s : S) → V s → E s) : QueryImpl (encSpec E) (StateT (Tbl V) m) :=
  fun q tbl => pure (enc q.1 (lookup tbl q.1 q.2), tbl)

/-- An encoding query returns the encoding of the lookup and preserves state. -/
@[simp] theorem encImpl_apply [∀ s, Zero (V s)] {m : Type → Type} [Monad m]
    (enc : (s : S) → V s → E s) (q : S × Handle) (tbl : Tbl V) :
    (encImpl (m := m) enc q).run tbl = pure (enc q.1 (lookup tbl q.1 q.2), tbl) := rfl

/-- Compatible encodings commute with transport along a model morphism. -/
theorem encImpl_map {F : Type} [CommSemiring F] {σ : Sig S}
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    [∀ s, AddCommMonoid (W s)] [∀ s, Module F (W s)]
    {M : Model F σ V} {N : Model F σ W} (φ : M.Hom N)
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (enc : (s : S) → V s → E s) (enc' : (s : S) → W s → E s)
    (henc : ∀ s, enc' s ∘ φ.toFun s = enc s) (q : S × Handle) (tbl : Tbl V) :
    Prod.map id (mapTbl fun s => φ.toFun s) <$> (encImpl (m := m) enc q).run tbl =
      (encImpl enc' q).run (mapTbl (fun s => φ.toFun s) tbl) := by
  change Prod.map id (mapTbl fun s => φ.toFun s) <$>
    (pure (enc q.1 (lookup tbl q.1 q.2), tbl) : m _) = _
  simp only [encImpl_apply, map_pure, Prod.map, id_eq, lookup_mapTbl]
  rw [show enc' q.1 (φ.toFun q.1 (lookup tbl q.1 q.2)) =
    enc q.1 (lookup tbl q.1 q.2) from congrFun (henc q.1) _]

end GroupModel
