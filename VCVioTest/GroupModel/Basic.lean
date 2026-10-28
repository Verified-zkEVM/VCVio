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

/-- Compare two distinct handles through the group oracle. -/
def equalityProgram : OracleComp (spec (ZMod 7) groupSig + gameSpec) Bool :=
  (spec (ZMod 7) groupSig + gameSpec).query (.inl (.eq () 0 1))

example : (run singleModel (fun _ => id) singleGame equalityProgram
    (fun _ => [3, 3])).1 = true := by decide

example : (run singleModel (fun _ _ => ()) singleGame equalityProgram
    (fun _ => [1, 3])).1 = true := by decide

/-! ## Product projection through ordinary imports -/

section ProductProjection

variable {F : Type} [CommSemiring F] {S : Type} [DecidableEq S] {σ : Sig S}
    {V W : S → Type} [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    [∀ s, AddCommMonoid (W s)] [∀ s, Module F (W s)]

example (M : Model F σ V) (N : Model F σ W) (s : S) (x : V s × W s) :
    (Model.Hom.snd M N).toFun s x = x.2 := rfl

example (M : Model F σ V) (N : Model F σ W) (s : S) (x : V s × W s) :
    (Model.Hom.fst M N).toFun s x = x.1 := by simp only [Model.Hom.fst_apply]

example (M : Model F σ V) (s : S) (x : V s) :
    ((Model.Hom.id M).comp (Model.Hom.id M)).toFun s x = x := by
  simp only [Model.Hom.comp_apply, Model.Hom.id_apply]

example (M : Model F σ V) (N : Model F σ W) (o : σ.Lin)
    (x : V (σ.lsrc o) × W (σ.lsrc o)) :
    (M.prod N).lin o x = (M.lin o x.1, N.lin o x.2) := by
  simp only [Model.prod_lin_apply]

example (M : Model F σ V) (N : Model F σ W) (o : σ.Bil)
    (x : V (σ.src₁ o) × W (σ.src₁ o)) (y : V (σ.src₂ o) × W (σ.src₂ o)) :
    (M.prod N).bil o x y = (M.bil o x.1 y.1, N.bil o x.2 y.2) := by
  simp only [Model.prod_bil_apply]

example [∀ s, DecidableEq (W s)] (M : Model F σ V) (N : Model F σ W) {α : Type}
    (oa : OracleComp (genSpec F σ) α) (tbl : Tbl fun s => V s × W s) :
    Prod.map id (mapTbl fun _ => Prod.snd) <$>
        runGen (M.prod N) (fun _ => Prod.snd) oa tbl =
      runGen N (fun _ => id) oa (mapTbl (fun _ => Prod.snd) tbl) := by
  have hsnd : (fun s => ⇑((Model.Hom.snd M N).toFun s)) =
      (fun _ => Prod.snd) := by
    funext s x
    simp only [Model.Hom.snd_apply]
  simpa only [hsnd, Function.comp_def, id_eq] using
    runGen_map (Model.Hom.snd M N) (fun _ => id) oa tbl

end ProductProjection

end GroupModel
