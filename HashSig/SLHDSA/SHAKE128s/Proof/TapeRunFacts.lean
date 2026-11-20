/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.DigestTape

/-!
# Full support for uniform digest tapes

Every finite list of hash outputs occurs in the support of a uniform padding block of its length.
-/

public section

open OracleComp

namespace SLHDSA.SHAKE128s.TapeRunFacts

open DigestTape

/-- Every finite tape is a possible padding block of its own length. -/
theorem mem_support_padding_of_length (tape : List HashOutput) :
    tape ∈ support (padding tape.length) :=
  (mem_support_padding_iff tape.length tape).2 rfl

end SLHDSA.SHAKE128s.TapeRunFacts
