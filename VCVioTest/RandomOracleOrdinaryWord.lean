/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.Ordinary

/-!
# A warm high row and cold low row at an ordinary input

At an input with only its high bit cached, the caller draws the low bit, reuses the high bit,
and keeps the pending graph cells.
-/

public section

open CanonicalGraph.PairedQueries OracleComp OracleSpec
open scoped OracleSpec.PrimitiveQuery
namespace VCVioTest.RandomOracleOrdinaryWord

/-- When only the high bit is cached, the low read draws a fresh bit before the high read
replays its stored value. The pending cells are unchanged. -/
theorem high_only (G : CanonicalGraph (PairedSpec Nat Bool) Nat Nat Bool)
    (off : OrdinaryAt G 7) (labels : ((Nat ⊕ Nat) →ₒ Bool).QueryCache) :
    let c := (∅ : (PairedSpec Nat Bool).QueryCache).cacheQuery (.inr 7) true
    let pending : List (Nat ⊕ Nat) := [.inl 3]
    ((callerImpl G (Equiv.refl (Bool × Bool)) (.inr 7)).run ((c, labels), pending)) =
      (fun lo => ((lo, true), (c.cacheQuery (.inl 7) lo, labels), pending)) <$> ($ᵗ Bool) := by
  intro c pending
  rw [ordinary_run G _ 7 off]
  simp [c, bind_map_left]

end VCVioTest.RandomOracleOrdinaryWord
