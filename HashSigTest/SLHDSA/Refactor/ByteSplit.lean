/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.ByteModel.Split
public import HashSig.SLHDSA.SHAKE128s.Bridge.Encodings

/-!
# Complete answer splitting at two FIPS parameter sets

The actual SHAKE-128s and SHAKE-192f answer dimensions instantiate the same prefix, suffix and
joint uniform laws. Concrete bytes and empty-component cases check the existing lossless split.
The actual 128s prefix agrees with the original bit-vector truncation.
-/

public section

open OracleComp OracleSpec SLHDSA.Security

namespace SLHDSA.Refactor.ByteSplitTest

local notation "p128" => FipsParameterSet.SLHDSA_SHAKE_128s.params
local notation "p192" => FipsParameterSet.SLHDSA_SHAKE_192f.params

/-- The actual 128s node cell is the first 16 bytes of its 30-byte answer. -/
theorem shake128s_prefix (answer : Bytes (p128).m) :
    (splitBytes (by decide : (p128).n ≤ (p128).m) answer).1 = prefixBytes (p128).n answer :=
  splitBytes_fst _ _

/-- The actual 128s suffix contains the remaining 14 bytes. -/
theorem shake128s_suffix (answer : Bytes (p128).m) :
    (splitBytes (by decide : (p128).n ≤ (p128).m) answer).2.toList =
      answer.toList.drop (p128).n :=
  toList_splitBytes_snd _ _

/-- A complete actual 128s uniform answer gives independent 16-byte and 14-byte components. -/
theorem shake128s_uniform_split :
    (splitBytes (by decide : (p128).n ≤ (p128).m) <$>
      ($ᵗ (Bytes (p128).m) : ProbComp (Bytes (p128).m))) =ᵈ
      (do let cell ← $ᵗ (Bytes (p128).n)
          let suffix ← $ᵗ (Bytes ((p128).m - (p128).n))
          pure (cell, suffix)) :=
  splitBytes_uniformSample _

/-- The actual 192f node cell is the first 24 bytes of its 42-byte answer. -/
theorem shake192f_prefix (answer : Bytes (p192).m) :
    (splitBytes (by decide : (p192).n ≤ (p192).m) answer).1 = prefixBytes (p192).n answer :=
  splitBytes_fst _ _

/-- The actual 192f suffix contains the remaining 18 bytes. -/
theorem shake192f_suffix (answer : Bytes (p192).m) :
    (splitBytes (by decide : (p192).n ≤ (p192).m) answer).2.toList =
      answer.toList.drop (p192).n :=
  toList_splitBytes_snd _ _

/-- A complete actual 192f uniform answer gives independent 24-byte and 18-byte components. -/
theorem shake192f_uniform_split :
    (splitBytes (by decide : (p192).n ≤ (p192).m) <$>
      ($ᵗ (Bytes (p192).m) : ProbComp (Bytes (p192).m))) =ᵈ
      (do let cell ← $ᵗ (Bytes (p192).n)
          let suffix ← $ᵗ (Bytes ((p192).m - (p192).n))
          pure (cell, suffix)) :=
  splitBytes_uniformSample _

example : ((p128).n, (p128).m - (p128).n) = (16, 14) := rfl
example : ((p192).n, (p192).m - (p192).n) = (24, 18) := rfl

example : splitBytes (by decide : 1 ≤ 3) (#v[17, 34, 51] : Bytes 3) =
    ((#v[17] : Bytes 1), (#v[34, 51] : Bytes 2)) := by decide

example : (splitBytes (by decide : 0 ≤ 3) (#v[17, 34, 51] : Bytes 3)).2 =
    (#v[17, 34, 51] : Bytes 3) := by decide

example : (splitBytes (by decide : 3 ≤ 3) (#v[17, 34, 51] : Bytes 3)).2 =
    (#v[] : Bytes 0) := by decide

example : (splitBytes (by decide : 0 ≤ 0) <$> ($ᵗ (Bytes 0) : ProbComp (Bytes 0))) =ᵈ
    (do let cell ← $ᵗ (Bytes 0)
        let suffix ← $ᵗ (Bytes 0)
        pure (cell, suffix)) :=
  splitBytes_uniformSample _

/-- The actual 128s prefix is the node value selected by the original bit-vector model. -/
theorem shake128s_original_truncation (answer : SHAKE128s.HashOutput) :
    (splitBytes (by decide : 16 ≤ 30) (SHAKE128s.Bridge.answerEquiv answer)).1 =
      SHAKE128s.Bridge.digestEquiv (SHAKE128s.Hashing.truncate answer) :=
  (splitBytes_fst _ _).trans (SHAKE128s.Bridge.prefixBytes_answerEquiv answer)

end SLHDSA.Refactor.ByteSplitTest
