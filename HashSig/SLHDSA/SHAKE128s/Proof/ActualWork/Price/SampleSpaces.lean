/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.Program

/-! # Discrete samples for the SHAKE-128s forgery bound

A block records both digest tapes and the terminal state of the execution that consumed them.
The probability estimates integrate over discrete public seeds and blocks.
-/

public section

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment

/-- The two sampled digest tapes together with the guarded execution's terminal state. -/
abbrev GuardedFill.Block := (List HashOutput × List HashOutput) × Native.NativeTerminal

namespace SampleSpaces

/-- The discrete measurable space on public seeds. -/
scoped instance : MeasurableSpace FIPS205.core.PkSeed := ⊤
/-- Every set of public seeds is measurable. -/
scoped instance : DiscreteMeasurableSpace FIPS205.core.PkSeed := ⟨fun _ => trivial⟩
/-- The discrete measurable space on terminal tape blocks. -/
scoped instance : MeasurableSpace GuardedFill.Block := ⊤
/-- Every set of terminal tape blocks is measurable. -/
scoped instance : DiscreteMeasurableSpace GuardedFill.Block := ⟨fun _ => trivial⟩

end SampleSpaces

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
