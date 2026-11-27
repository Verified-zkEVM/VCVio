/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Encoding.ActivatedClash

/-! # Erasure of sampled tapes on the completed experiment -/

public section

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.GuardedFill

/-- The native tape block, the fill of its final graph, and the independently drawn secret. -/
@[expose] noncomputable def tapedFill (s : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK) (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) (L R : Nat) := do
  let block ← NoticingTape.blockRunOf (Native.nativeRun s adv reserve caps fallback) L R
  let filled ← RelabelState.endFill block.2.2.1.1.2.1
  let secret ← ($ᵗ Secret : ProbComp Secret)
  pure (block, filled, secret)

/-- Retaining the complete tape block after the graph fill and final secret draw preserves its
joint distribution, including the terminal output, cache and paid counters. -/
theorem fst_tapedFill (s : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK) (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) (L R : Nat) :
    Prod.fst <$> tapedFill s adv reserve caps fallback L R =ᵈ
      NoticingTape.blockRunOf (Native.nativeRun s adv reserve caps fallback) L R := by
  simp only [tapedFill, map_bind, map_pure]
  conv_rhs => rw [← id_map (NoticingTape.blockRunOf _ L R), map_eq_bind_pure_comp]
  apply EvalDistEq.bind_right
  intro block
  exact (OracleComp.EvalDistEq.bind_const _ _).trans (OracleComp.EvalDistEq.bind_const _ _)

/-- Forget both padded tapes and the prefix-use witness, retaining the complete guarded value
and deferred/final graph caches together with the final private draw. -/
def eraseTapes (r : (((List HashOutput × List HashOutput) × Native.NativeTerminal) ×
    LabState FIPS205.core × Secret)) : Filled :=
  let t := r.1.2
  (((((t.1, (PUnit.unit, t.2.2)), t.2.1.1.1), t.2.1.1.2.2), t.2.1.1.2.1), r.2)

/-- The complete filled law, including the actual losing and aborted states, is the marginal
of the same native block experiment for any independent initial tape lengths. -/
theorem eraseTapes_tapedFill (s : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK) (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) (L R : Nat) :
    eraseTapes <$> tapedFill s adv reserve caps fallback L R =ᵈ
      (slhGraph FIPS205.core s).deferredFillDraw ($ᵗ Secret)
        (labProgram s adv reserve true caps fallback) := by
  rw [labProgram_eq_native]
  have h := Native.native_deferred_marginal s adv reserve caps fallback L R
  dsimp only at h
  let extend := fun z : Value × LabState FIPS205.core × List (DeriveQuery FIPS205.core ⊕
        NodeKey FIPS205.core) => do
    let filled ← RelabelState.endFill z.2
    let secret ← ($ᵗ Secret : ProbComp Secret)
    pure (z, filled, secret)
  have joint := h.bind_left extend
  simpa only [tapedFill, eraseTapes, CanonicalGraph.deferredFillDraw, extend,
    bind_map_left, map_bind, map_pure] using joint

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.GuardedFill
