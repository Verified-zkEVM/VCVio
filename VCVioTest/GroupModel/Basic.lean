/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Projection
public import Mathlib.Data.ZMod.Basic

/-!
# Executable sorted group-model checks

The extra game oracle inserts values into the same table used by the group oracle.
The three-sort example checks linear transport and bilinear multiplication modulo seven.
-/

public section

open OracleComp OracleSpec

namespace GroupModel

/-- One-sort model over the field with seven elements. -/
def singleModel : Model (ZMod 7) groupSig (fun _ => ZMod 7) where
  lin := Empty.elim
  bil := Empty.elim

/-- A game query that returns a table handle. -/
abbrev gameSpec : OracleSpec Unit := fun _ => Handle

/-- Insert three into the one-sort table. -/
def singleGame : QueryImpl gameSpec (StateT (Tbl fun _ : Unit => ZMod 7) Id) :=
  fun _ => push () 3

/-- Insert, add, scale, and compare values in one sort. -/
def singleProgram : OracleComp (spec (ZMod 7) groupSig + gameSpec)
    (Handle × Handle × Handle × Bool × Bool) := do
  let g ← (spec (ZMod 7) groupSig + gameSpec).query (.inr ())
  let a ← (spec (ZMod 7) groupSig + gameSpec).query (.inl (.add () 0 g))
  let b ← (spec (ZMod 7) groupSig + gameSpec).query (.inl (.smul () 3 a))
  let same ← (spec (ZMod 7) groupSig + gameSpec).query (.inl (.eq () b 0))
  let different ← (spec (ZMod 7) groupSig + gameSpec).query (.inl (.eq () 0 g))
  pure (g, a, b, same, different)

/-- The one-sort run returns fresh handles and distinguishes unequal values. -/
theorem singleProgram_result :
    (run singleModel (fun _ => id) singleGame singleProgram (fun _ => [1])).1 =
  (1, 2, 3, false, false) := by decide

example : (run singleModel (fun _ => id) singleGame singleProgram (fun _ => [1])).2 () =
  [1, 3, 4, 5] := by decide

/-- Three-sort model with identity transport and field multiplication. -/
def pairingModel : Model (ZMod 7) pairingIsoSig (fun _ => ZMod 7) where
  lin _ := LinearMap.id
  bil _ := LinearMap.mul (ZMod 7) (ZMod 7)

/-- Initial tables for the three pairing sorts. -/
def pairingTable : Tbl (fun _ : PSort => ZMod 7)
  | .g₁ => [2]
  | .g₂ => [3]
  | .gₜ => []

/-- Insert four into the second source sort. -/
def pairingGame :
    QueryImpl gameSpec (StateT (Tbl fun _ : PSort => ZMod 7) Id) :=
  fun _ => push .g₂ 4

/-- Pairing queries together with a table-inserting game oracle. -/
abbrev pairingQueries := spec (ZMod 7) pairingIsoSig + gameSpec

/-- Transport and combine values across the three sorts. -/
def pairingProgram : OracleComp pairingQueries
    (Handle × Handle × Handle × Handle × Handle × Bool) := do
  let g ← pairingQueries.query (.inr ())
  let l ← pairingQueries.query (.inl (.lin () g))
  let a ← pairingQueries.query (.inl (.add .g₁ 0 l))
  let b ← pairingQueries.query (.inl (.smul .g₂ 2 0))
  let p ← pairingQueries.query (.inl (.bil () a b))
  let same ← pairingQueries.query (.inl (.eq .g₁ a b))
  pure (g, l, a, b, p, same)

example : (run pairingModel (fun _ => id) pairingGame pairingProgram pairingTable).1 =
  (1, 1, 2, 2, 0, true) := by decide

example : (run pairingModel (fun _ => id) pairingGame pairingProgram pairingTable).2 .g₁ =
  [2, 4, 6] := by decide

example : (run pairingModel (fun _ => id) pairingGame pairingProgram pairingTable).2 .g₂ =
  [3, 4, 6] := by decide

example : (run pairingModel (fun _ => id) pairingGame pairingProgram pairingTable).2 .gₜ =
  [1] := by decide

example : lookup pairingTable .g₁ 99 = 0 := by decide

end GroupModel
