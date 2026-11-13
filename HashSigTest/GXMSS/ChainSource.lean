/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.ChainSource
public import HashSigTest.GXMSS.FilteredView
import all HashSig.GXMSS.Security.Interval.Reductions.ChainSource
import HashSig.GXMSS.Security.Interval.Reductions.SplicedView
import HashSig.GXMSS.Security.Interval.Reductions.FilteredView
import HashSig.GXMSS.Security.Auxiliary.ChainSelection
import HashSigTest.GXMSS.SplicedView

/-!
# Joint start resampling and returned selected-mass controls

Two distinct table coordinates remain jointly observable after a selected cell refresh.
The actual low-word adaptive fixture is killed after its first retry; its good-event observation
returns false rather than becoming missing runtime mass.
-/

public section
namespace GXMSS.ChainSourceProbe
open GXMSS.Reductions GXMSS.Interval.Reductions GXMSS.IntervalMerkle
open GXMSS.SplicedViewProbe GXMSS.FilteredViewProbe OracleComp OracleSpec

/-- Read the refreshed cell together with a different epoch and chain. -/
private def jointObservation (table : Epoch 1 → Fin 2 → Bool) : ProbComp (Bool × Bool) :=
  pure (table 0 1, table 1 0)

/-- Coordinate refresh preserves the joint returned law, not merely each cell's marginal. -/
private theorem joint_resampling :
    let : MeasurableSpace (Bool × Bool) := ⊤
    𝒟[do
      let x ← ($ᵗ Bool : ProbComp Bool)
      let table ← GXMSS.sampleStarts Bool 1 2
      jointObservation (Function.update table 0 (Function.update (table 0) 1 x))] =
      𝒟[GXMSS.sampleStarts Bool 1 2 >>= jointObservation] := by
  let : MeasurableSpace (Bool × Bool) := ⊤
  exact sampleStarts_coordinate_resampling_bind (H := Bool) (h := 1) (v := 2)
    (0 : Epoch 1) (1 : Fin 2) jointObservation

/-- The refreshed coordinate and a distinct coordinate retain their exact index orientation. -/
private theorem joint_coordinates (table : Epoch 1 → Fin 2 → Bool) (x : Bool) :
    jointObservation (Function.update table 0 (Function.update (table 0) 1 x)) =
      pure (x, table 1 0) := by
  simp [jointObservation, Function.update]

/-- The actual absorbing adaptive run returns a false observation after one retry draw. -/
theorem killed_returned_false (response : Bool) :
    (fun out => out.elim false (fun _ => true)) <$>
      filteredChainSpliceView hash lowEncoding 1 middle adversary () guess guess response
        starts fillers = (do
          let _ ← ($ᵗ Unit : ProbComp Unit)
          pure false) := by
  rw [killed_adaptive_program]
  simp [map_eq_bind_pure_comp]

/-- The constant false event has zero true mass in the actual killed returned view. -/
private theorem killed_true_mass (response : Bool) :
    𝒟[(fun out => out.elim false (fun _ => true)) <$>
      filteredChainSpliceView hash lowEncoding 1 middle adversary () guess guess response
        starts fillers] {true} = 0 := by
  rw [killed_returned_false]
  simp

end GXMSS.ChainSourceProbe
