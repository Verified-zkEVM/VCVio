/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import HashSig.SLHDSA.Concrete.FIPS
public import HashSig.SLHDSA.FipsParams

/-!
# Fixed native SLH-DSA-SHAKE-128s carriers

The validated parameters and pure primitive context fix every structured field and the
complete30-byte oracle answer without selecting a signing experiment or interpreter.
-/

public section

namespace SLHDSA.SHAKE128s.FIPS205

open SLHDSA

/-- The validated SLH-DSA-SHAKE-128s parameters. -/
abbrev params : ValidatedParams := FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams

/-- The SHAKE256 primitive context at those parameters. -/
abbrev core : CorePrimitives params.params := (Concrete.shakePrimitives params.params).core

/-- The random oracle's answers: `m = 30` bytes. -/
abbrev Answer : Type := SLHDSA.Bytes params.params.m

end SLHDSA.SHAKE128s.FIPS205
