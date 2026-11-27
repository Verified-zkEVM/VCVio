/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.ByteModel

/-!
# Prefix and suffix laws for complete byte answers

The complete-answer equivalence retains its exact prefix and remaining bytes. Splitting a uniform
full answer gives the joint distribution of independent uniform prefix and suffix draws. The
uniform law concerns the output distribution; interpreter state and private sampling observations
require their own transport laws.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.Security

variable {n m : Nat}

/-- The first component of the complete-answer split is the actual node prefix. -/
theorem splitBytes_fst (fits : n ≤ m) (answer : Bytes m) :
    (splitBytes fits answer).1 = prefixBytes n answer := rfl

/-- The second component contains exactly all bytes after the node prefix. -/
theorem toList_splitBytes_snd (fits : n ≤ m) (answer : Bytes m) :
    (splitBytes fits answer).2.toList = answer.toList.drop n := by
  change (bytesOfList (m - n) (answer.toList.drop n)).toList = _
  rw [toList_bytesOfList_of_le (by simp), List.take_of_length_le (by simp)]

/-- Splitting a uniform full answer gives independent uniform prefix and suffix components. -/
theorem splitBytes_uniformSample (fits : n ≤ m) :
    (splitBytes fits <$> ($ᵗ (Bytes m) : ProbComp (Bytes m))) =ᵈ
      (do let cell ← $ᵗ (Bytes n)
          let suffix ← $ᵗ (Bytes (m - n))
          pure (cell, suffix)) := by
  simpa only [SampleableType.uniformSample_prod_eq_bind] using
    SampleableType.map_uniformSample_evalDistEq_of_bijective (splitBytes fits).bijective

end SLHDSA.Security
