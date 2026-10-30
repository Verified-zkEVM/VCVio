/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.HidingIdeal
public import VCVioTest.PointerChainPuzzle.HidingPRF

/-!
# Time-lock encryption with the pointer-chain puzzle: checks of the ideal PRF world

Checks through the public API, at the parameters, toy PRF and concrete hiding adversary of
`VCVioTest.PointerChainPuzzle.HidingPRF`:

* the keystream block counters of a 70-byte message, three blocks, are the distinct points
  `be 8 0`, `be 8 1` and `be 8 2` of the stream instance;
* independence of the hidden bit in the ideal world and the PRF step, at budgets `1` and `2`.

Loading this module enumerates no type.
-/

public section

open OracleComp OracleSpec PointerChainPuzzle PointerChainPuzzle.LeanSeal
  PointerChainPuzzle.LeanSeal.Envelope PRFScheme
open VCVioTest.PointerChainPuzzle.HidingPRF
open scoped ENNReal

namespace VCVioTest.PointerChainPuzzle.HidingIdeal

/-! ## The stream points of a multi-block message -/

/-- A message of 70 zero bytes: three keystream blocks. -/
@[expose]
def msg70 : Plaintext := ⟨⟨Array.replicate 70 0⟩, by decide⟩

/-- The 70-byte message has three keystream blocks. -/
theorem numBlocks_msg70 : (msg70.1.size + 31) / 32 = 3 := rfl

/-- The stream instance of an encryption of the 70-byte message is queried at three distinct
points. -/
theorem nodup_streamPoints_msg70 : [be 8 0, be 8 1, be 8 2].Nodup :=
  nodup_map_be_range msg70

/-! ## The ideal world and the PRF step at budgets `1` and `2` -/

variable (encodePuzzle : Puzzle 2 S L Salt → ByteArray)

/-- In the ideal world, `hidingAdv` against the indexed run at budget `1` outputs `true` with the
same probability at both hidden bits. -/
theorem prfIdealExperiment_indexedRun_one :
    Pr{let g ← (prfIdealExperiment
        (indexedRun 1 codec encodePuzzle 1 mkCtx initAcc hidingAdv true))}[g = true] =
      Pr{let g ← (prfIdealExperiment
        (indexedRun 1 codec encodePuzzle 1 mkCtx initAcc hidingAdv false))}[g = true] :=
  prfIdealExperiment_indexedRun_true_eq_false codec encodePuzzle 1 mkCtx initAcc hidingAdv

/-- In the ideal world, `hidingAdv` against the indexed run at budget `2` outputs `true` with the
same probability at both hidden bits. -/
theorem prfIdealExperiment_indexedRun_two :
    Pr{let g ← (prfIdealExperiment
        (indexedRun 1 codec encodePuzzle 2 mkCtx initAcc hidingAdv true))}[g = true] =
      Pr{let g ← (prfIdealExperiment
        (indexedRun 1 codec encodePuzzle 2 mkCtx initAcc hidingAdv false))}[g = true] :=
  prfIdealExperiment_indexedRun_true_eq_false codec encodePuzzle 2 mkCtx initAcc hidingAdv

/-- The PRF step for `hidingAdv` at budget `1`, against independent toy PRF keys. -/
theorem absDiff_indexed_le_prfAdvantage_one :
    ENNReal.absDiff
      (Pr{let g ← ((toyPRF.multiKey (Fin (2 * 1))).prfRealExperiment
        (indexedRun 1 codec encodePuzzle 1 mkCtx initAcc hidingAdv true))}[g = true])
      (Pr{let g ← ((toyPRF.multiKey (Fin (2 * 1))).prfRealExperiment
        (indexedRun 1 codec encodePuzzle 1 mkCtx initAcc hidingAdv false))}[g = true]) ≤
      2 * (toyPRF.multiKey (Fin (2 * 1))).prfAdvantage
        (hidingDistinguisher 1 codec encodePuzzle 1 mkCtx initAcc hidingAdv) :=
  absDiff_indexed_le_prfAdvantage codec encodePuzzle 1 mkCtx initAcc hidingAdv toyPRF

/-- The PRF step for `hidingAdv` at budget `2`, against independent toy PRF keys. -/
theorem absDiff_indexed_le_prfAdvantage_two :
    ENNReal.absDiff
      (Pr{let g ← ((toyPRF.multiKey (Fin (2 * 2))).prfRealExperiment
        (indexedRun 1 codec encodePuzzle 2 mkCtx initAcc hidingAdv true))}[g = true])
      (Pr{let g ← ((toyPRF.multiKey (Fin (2 * 2))).prfRealExperiment
        (indexedRun 1 codec encodePuzzle 2 mkCtx initAcc hidingAdv false))}[g = true]) ≤
      2 * (toyPRF.multiKey (Fin (2 * 2))).prfAdvantage
        (hidingDistinguisher 1 codec encodePuzzle 2 mkCtx initAcc hidingAdv) :=
  absDiff_indexed_le_prfAdvantage codec encodePuzzle 2 mkCtx initAcc hidingAdv toyPRF

end VCVioTest.PointerChainPuzzle.HidingIdeal
