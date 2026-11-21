/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.ChainPrograms
public import HashSigTest.GXMSS.SplicedView
public import HashSigTest.GXMSS.FilteredView
import all HashSig.GXMSS.Security.Interval.Reductions.ChainPrograms
import HashSig.GXMSS.Security.Interval.Reductions.SplicedView
import HashSig.GXMSS.Security.Interval.Reductions.FilteredView
import HashSig.GXMSS.Security.Interval.Reductions.SourcePartition
import HashSig.GXMSS.Security.Auxiliary.ChainSelection
import all HashSig.GXMSS.Chain
import all HashSig.GXMSS.Merkle

/-!
# Active chain selector and original-domain program controls

The inclusive two-epoch interval has six selectors at width two. The single-position UD boundary
has no earlier cut. PRE controls distinguish inactive fallback from an accepted unused epoch.
Private imports serve the actual implementation controls.
-/

public section
namespace GXMSS.ChainProgramProbe
open GXMSS.IntervalMerkle GXMSS.Interval.Reductions GXMSS.Interval.Reductions.Chain
open GXMSS.Reductions GXMSS.SplicedViewProbe GXMSS.FilteredViewProbe
open OracleComp OracleSpec SyncSignatureUnforgeability

/-- The first active offset is the interval's first epoch, with unchanged chain and cut. -/
private theorem first_selector :
    activeGuess middle ((0 : Fin 2), (0 : Fin 1), (⟨2, by decide⟩ : Fin (2 ^ 2 - 1))) =
      ((3 : Fin 8), (0 : Fin 1), (⟨2, by decide⟩ : Fin (2 ^ 2 - 1))) := rfl

/-- The last active offset is the inclusive upper endpoint. -/
private theorem last_selector :
    activeGuess middle ((1 : Fin 2), (0 : Fin 1), (⟨0, by decide⟩ : Fin (2 ^ 2 - 1))) =
      ((4 : Fin 8), (0 : Fin 1), (⟨0, by decide⟩ : Fin (2 ^ 2 - 1))) := rfl

/-- Two epochs, one chain and three positive positions give exactly six active selectors. -/
private theorem six_selectors : Fintype.card (ActiveSelector middle 2 1) = 6 := by
  rw [activeSelector_card]
  decide

/-- At width one, every sampled hybrid equals the selected cut and the UD output is false. -/
private theorem one_position_ud (state : ChainUDState Bool 3 1 1 middle) :
    (chainUndetectabilityReduction hash lowEncoding 1 middle
      (by decide) (by decide) adversary).distinguish state () = pure false := by
  simp [chainUndetectabilityReduction]

private def candidate (ep : Fin 8) : Result Unit Bool Bool Unit 3 1 :=
  let (pk, sk) := GXMSS.Interval.keys hash middle () starts fillers
  let sig := GXMSS.Interval.signatureOfWord hash middle sk ep ((fun _ => 0), ())
  ⟨pk, sk.complete, (ep, true, sig), emptyHistory⟩

/-- An inactive candidate takes the supplied true fallback, preserving that choice. -/
private theorem inactive_fallback :
    extractChainPreimageWithFallback hash lowEncoding 1 middle fillers guess true (candidate 2) =
      true := by
  decide

/-- An accepted unused epoch yields the final-chain predecessor false instead of the fallback. -/
private theorem unused_predecessor :
    extractChainPreimageWithFallback hash lowEncoding 1 middle fillers guess true (candidate 3) =
      false := by
  decide

/-- The actual primitive configurations keep one target on the original digest input domain. -/
theorem original_domain :
    (chainPREProblem hash).numTargets = 1 := rfl

end GXMSS.ChainProgramProbe
