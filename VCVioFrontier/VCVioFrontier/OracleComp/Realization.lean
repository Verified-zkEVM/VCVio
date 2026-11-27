/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Computability.Probabilistic.Sampling

public import PolyFunFrontier.PFunctor.Free.Realization
public import VCVioFrontier.OracleComp.Measure

/-!
# Uniform machines for handled oracle programs

A machine realization implements one family of source programs closed by a probabilistic
handler. The same machine and polynomial clock give the encoded output law on each input and
bound the halting time on every input word. The law also holds in VCVio's measure semantics.
-/

public section

namespace PFunctor.FreeM.MachineRealization

open MeasureTheory VCVioFrontier

variable {P : PFunctor} {α β : Type} {H : Handler _root_.ProbComp P}
  {input : α ↪ List Bool} {encoding : β ↪ List Bool} {program : α → P.FreeM β}

/-- The measured output agrees with VCVio's evaluation of the encoded, handled source.
The word space can carry any measurable structure. -/
theorem output_measure (M : MachineRealization H input encoding program) (a : α)
    (words : MeasurableSpace (List Bool)) :
    let _ := words
    (M.output a).toMeasure = 𝒟[encoding <$> (program a).liftM H] := by
  let _ := words
  dsimp only
  rw [output, M.encoded_law, evalDist_eq_toMeasure, Cslib.ProbComp.eval_map]

end PFunctor.FreeM.MachineRealization
