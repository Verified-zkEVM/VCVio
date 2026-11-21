/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.ChainHybrid
public import HashSigTest.GXMSS.ChainPrograms
import all HashSig.GXMSS.Security.Interval.Reductions.ChainHybrid
import HashSig.GXMSS.Security.Interval.Reductions.ChainPrograms
import HashSig.GXMSS.Security.Interval.Reductions.SplicedView
import HashSig.GXMSS.Security.Auxiliary.ChainSelection
import HashSigTest.GXMSS.SplicedView

/-!
# Native PRE fallback and unconditioned winning controls

The two public strategies retain different fallback coordinates. The actual constant-hash native
PRE experiment can win regardless of the source observation; its advantage retains those wins.
-/

public section
namespace GXMSS.ChainHybridProbe
open ENNReal GXMSS.Reductions GXMSS.Interval.Reductions GXMSS.Interval.Reductions.Chain
open GXMSS.IntervalMerkle GXMSS.SplicedViewProbe GXMSS.FilteredViewProbe
open OracleComp OracleSpec TweakableHash

private def variedStarts (ep : Epoch 3) (_ : Fin 1) : Bool := decide (ep = 3)

private def refused : ChainPREState Bool 3 1 1 middle :=
  ⟨((0 : Fin 2), (0 : Fin 1), (⟨0, by decide⟩ : Fin (2 ^ 1 - 1))),
    none, variedStarts, fillers⟩

/-- A refused selected-coordinate strategy returns starts at the selected epoch. -/
private theorem selected_fallback :
    (selectedChainPreimageReduction hash lowEncoding 1 middle (by decide) (by decide)
      adversary).invert refused () = pure (0, true) := rfl

/-- The separate public fixed-coordinate strategy returns starts at epoch zero. -/
private theorem fixed_fallback :
    (chainPreimageReduction hash lowEncoding 1 middle (by decide) (by decide)
      adversary).invert refused () = pure (0, false) := rfl

/-- The entire actual native selected PRE experiment wins with unconditioned mass one here. -/
theorem selected_native_win :
    SM_DT_PRE_Advantage
      (selectedChainPreimageReduction hash lowEncoding 1 middle (by decide) (by decide)
        adversary) = 1 := by
  let : NeZero (2 ^ 1 - 1) := ⟨by decide⟩
  unfold SM_DT_PRE_Advantage
  rw [chainPREExperiment_eq_explicit hash lowEncoding 1 middle (by decide) (by decide) adversary]
  rw [← prEvent_eq_evalDist_singleton]
  apply OracleComp.prEvent_eq_one_of_forall_mem_support
  intro b hb
  simp only [chainPREExplicitProgram, mem_support_bind_iff] at hb
  rcases hb with ⟨pp, _, selector, _, starts, _, fillers, _, hidden, _, out, _, hb⟩
  simpa [GXMSS.SplicedViewProbe.hash, eq_comm] using hb

/-- The actual native fixed-fallback experiment retains the same incidental winning mass. -/
private theorem fixed_native_win :
    SM_DT_PRE_Advantage
      (chainPreimageReduction hash lowEncoding 1 middle (by decide) (by decide)
        adversary) = 1 := by
  let : NeZero (2 ^ 1 - 1) := ⟨by decide⟩
  unfold SM_DT_PRE_Advantage
  rw [fixedFallbackPREExperiment_eq_explicit hash lowEncoding 1 middle
    (by decide) (by decide) adversary]
  rw [← prEvent_eq_evalDist_singleton]
  apply OracleComp.prEvent_eq_one_of_forall_mem_support
  intro b hb
  simp only [fixedFallbackPREExplicitProgram, mem_support_bind_iff] at hb
  rcases hb with ⟨pp, _, selector, _, starts, _, fillers, _, hidden, _, out, _, hb⟩
  simpa [GXMSS.SplicedViewProbe.hash, eq_comm] using hb

end GXMSS.ChainHybridProbe
