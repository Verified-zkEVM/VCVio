/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/
import VCVio.OracleComp.QueryTracking.RandomOracle.TouchRead.Children

/-! # Repeated and empty inputs of eager graph points -/

open OracleComp OracleSpec

namespace VCVioTest.RandomOracleChildren

variable {ι X K R : Type} {pub : OracleSpec ι} (G : CanonicalGraph pub X K R)
  [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)]

/-- The positions on either side of a distinct intervening read agree at a repeated child. -/
example (c d : X ⊕ K) (st later : RelabelState pub X K R) (x y z : R)
    (run : ([x, y, z], later) ∈ support ((simulateQ G.eagerImpl
      ([c, d, c].mapM fun k => readCell (some k))).run st)) :
    x = z ∧ later.2 d = some y := by
  have cells := (G.readCells_recorded [c, d, c] st run).2
  cases cells with
  | cons first rest =>
    cases rest with
    | cons middle rest =>
      cases rest with
      | cons last _ => exact ⟨Option.some.inj (first.symm.trans last), middle⟩

/-- A point with no children needs no touches before either output. -/
example (lo hi : K) (hl : G.ch lo = []) (hh : G.ch hi = []) :
    simulateQ G.eagerImpl (do
      let a ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt lo []))))
      let b ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt hi []))))
      pure (cast (G.range_eq lo []) a, cast (G.range_eq hi []) b)) =
    simulateQ G.eagerImpl (do
      let a ← readCell (some (.inr lo))
      let b ← readCell (some (.inr hi))
      pure (a, b)) := by
  simpa using G.simulateQ_eagerImpl_siblings lo hi [] hl hh

end VCVioTest.RandomOracleChildren
