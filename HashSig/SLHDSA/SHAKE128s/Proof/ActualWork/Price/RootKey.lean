/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Filled
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.JointBudget
import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Observation

/-!
# Weak keys at the physical FIPS key sampler

The weak-key contribution is bounded using the distribution of the initial physical key pair.
The result transfers this bound to the comparison with the filled experiment.
-/

open OracleComp OracleSpec SignatureAlg MeasureTheory
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open scoped ENNReal
public section

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment

open Guarded (Raw Ev Native Common Meta encoding policy selectedRaw aux)

/-- The explicit weak winning escape uses the actual original physical key generation and
its same-cache continuation, after the one global public-seed draw. -/
theorem physical_source_weak_win_le_honest_address_mass
    (adv : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core)) :
    let physical := fun seed : FIPS205.core.PkSeed =>
      (eraseObsImpl (Ev := Ev) (Raw.romImpl ∘ₛ (encoding seed).encodeImpl) :
        QueryImpl Common (StateT Raw.QueryCache ProbComp))
    let source := do
      let seed ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
      let observed := (physical seed).extendState (aux (spec := Native) (selectedRaw seed))
      let out ← ((simulateQ (observed.withAddCost
        (Sum.elim (fun _ : Native.Domain => (0, 0)) (policy true seed)))
        (mixedSourceAt seed adv)).runAdd).run (∅, (0, .keygen))
      pure (seed, out)
    Pr{let sampled ← source}[
      SigningView.Wins id sampled.2.1.1.2 ∧
        IsWeakKey FIPS205.params sampled.2.1.1.1.1] ≤
      (1591788895347057694892543 : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  intro physical source
  let originalCost : Common.Domain → Game.Counted.SourceCounts :=
    Sum.elim (fun _ => 0) Game.Counted.sourcePolicy
  let originalFamily := do
    let seed ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
    let out ← ((simulateQ ((physical seed).withAddCost originalCost)
      (mixedSourceAt seed adv)).runAdd).run ∅
    pure (seed, out)
  have sameKeys (seed : FIPS205.core.PkSeed) :
      (fun out => out.1.1.1.1) <$>
          ((simulateQ ((physical seed).withAddCost originalCost)
            (mixedSourceAt seed adv)).runAdd).run ∅ =ᵈ
        (fun out => out.1.1.1.1) <$>
          ((simulateQ (((physical seed).extendState
            (aux (spec := Native) (selectedRaw seed))).withAddCost
              (Sum.elim (fun _ : Native.Domain => (0, 0)) (policy true seed)))
            (mixedSourceAt seed adv)).runAdd).run (∅, (0, .keygen)) := by
    exact OracleComp.ProgramLogic.Relational.evalDistEq_map_of_relTriple
      (OracleComp.ProgramLogic.Relational.relTriple_post_mono
        (physical_reserve_original_cost_relation seed (mixedSourceAt seed adv))
        (fun left right related => congrArg (fun alpha => alpha.1.1) related.1))
  have familyKeys : (fun sampled => sampled.2.1.1.1.1) <$> originalFamily =ᵈ
      (fun sampled => sampled.2.1.1.1.1) <$> source := by
    simp only [originalFamily, source, map_bind, map_pure]
    apply EvalDistEq.bind_right
    intro seed
    simpa only [bind_pure_comp] using sameKeys seed
  let rawHandler := SigningView.Events.handlerWithEvents (Request := Message) Raw.romImpl
  let view := Game.Counted.externalView FIPS205.scheme
  let marked := SigningView.Events.fullExperiment view (Game.Counted.externalMain adv)
  let rawCost : (Guarded.R + Guarded.O).Domain → Game.Counted.SourceCounts :=
    Sum.elim (fun _ => 0) Game.Counted.sourcePolicy
  let original := ((simulateQ (rawHandler.withAddCost rawCost) marked).runAdd).run ∅
  have chronological := physical_original_full_source_counts adv
  dsimp only at chronological
  have originalKeys : (fun sampled => sampled.2.1.1.1.1) <$> originalFamily =ᵈ
      (fun out => out.1.1.1.1) <$> original := by
    have projected := chronological.symm.map (fun sampled => sampled.2.1.1.1.1)
    simpa only [Functor.map_map, Function.comp_def] using projected
  have phaseErases {alpha : Type} (program : OracleComp Guarded.R alpha) :
      simulateQ rawHandler
          (simulateQ (SigningView.Events.phaseImpl Guarded.R Message .keygen) program) =
        simulateQ Raw.romImpl program := by
    apply QueryImpl.simulateQ_simulateQ_eq_of_apply
    intro input
    simp [rawHandler, SigningView.Events.phaseImpl, SigningView.Events.emit,
      SigningView.Events.handlerWithEvents]
  have eraseCounts : (fun result => (result.1.1, result.2)) <$> original =
      (simulateQ rawHandler marked).run ∅ := by
    have erased := congrArg (fun action => action.run (∅ : Raw.QueryCache))
      (QueryImpl.fst_map_run_withCost rawHandler
        (fun input => Multiplicative.ofAdd (rawCost input)) marked)
    simpa only [original, QueryImpl.withAddCost, AddWriterT.runAdd, Prod.map_fst, id_eq,
      StateT.run_map, Functor.map_map, Function.comp_def] using erased
  have rawKeyMarginal : (fun out => out.1.1.1.1) <$> original =ᵈ
      (fun generated => generated.1.2) <$>
        ((simulateQ Raw.romImpl FIPS205.scheme.keygen).run ∅) := by
    have erasedKeys := congrArg (fun action =>
      (fun out => out.1.1.1) <$> action) eraseCounts
    simp only [Functor.map_map] at erasedKeys
    rw [erasedKeys]
    simp only [marked, SigningView.Events.fullExperiment, simulateQ_bind,
      simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure]
    simp only [SigningView.Events.viewWithEvents]
    rw [phaseErases]
    simp only [view, Game.Counted.externalView, simulateQ_map, StateT.run_map,
      bind_map_left, Prod.swap]
    conv_rhs => rw [map_eq_bind_pure_comp]
    apply EvalDistEq.bind_right
    intro generated
    exact (EvalDistEq.bind_right _ (fun _ => OracleComp.EvalDistEq.bind_const _ _)).trans
      (OracleComp.EvalDistEq.bind_const _ _)
  have actualKeys := familyKeys.symm.trans (originalKeys.trans rawKeyMarginal)
  have weakKeyEvent := actualKeys.prEvent_eq (IsWeakKey FIPS205.params)
  have weak := prEvent_original_fips_keygen_then_isWeakKey_le
    (fun _ => (pure PUnit.unit : StateT Raw.QueryCache ProbComp PUnit))
  have originalWeak : Pr{let generated ←
        ((simulateQ Raw.romImpl FIPS205.scheme.keygen).run ∅)}[
          IsWeakKey FIPS205.params generated.1.2] ≤
      (1591788895347057694892543 : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
    simpa only [StateT.run_bind, StateT.run_pure, map_bind, map_pure,
      bind_pure_comp, RandomOracleModel.impl, OracleSpec.romImpl, StateT.run_map,
      prEvent_map, prEvent_norm] using weak
  calc
    _ ≤ Pr{let sampled ← source}[
        IsWeakKey FIPS205.params sampled.2.1.1.1.1] :=
      prEvent_mono source _ _ (fun _ winningWeak => winningWeak.2)
    _ = _ := by simpa only [prEvent_map] using weakKeyEvent
    _ ≤ _ := originalWeak

namespace Physical
open Guarded
/-- Under the work and signing caps, FIPS success is bounded by a win or a cache hazard in the
filled experiment, plus the honest address count divided by 2²⁵⁶. -/
theorem original_win_le_filled_add_address_mass (adv : Game.Adversary FIPS205.Answer PK) (q : Nat)
    (hlimit : Game.WithinSigningLimit FIPS205.scheme adv)
    (hbound : (Game.securityGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adv q)
    (fallback : (s : FIPS205.core.PkSeed) →
      (input : LabCommon.Domain) → LabCommon.Range input) :
    Pr{let out ← (Game.securityGame FIPS205.scheme).experiment () adv}[out.1 = true] ≤
    Pr{let s ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
       let r ← (slhGraph FIPS205.core s).deferredFillDraw ($ᵗ GuardedFill.Secret)
         (GuardedFill.labProgram s adv true true (32*q-1, 2^64) (fallback s))}[
      let obs := GuardedFill.observe r.1.1
      let G := slhGraph FIPS205.core s
      let E := secretEncoding FIPS205.core (Equiv.refl _) s
      let split := G.toSplitCache r.2.1
      ((∃ out, obs.2.1 = some out ∧ SigningView.Wins id out) ∨
        (encoding s).Clash (E.merge r.2.2 split)) ∨
        (∃ x, (split.1 (E.enc r.2.2 x)).isSome) ∨ G.Conflict r.2.1] +
    (1591788895347057694892543 : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  refine (original_win_le_filled_add_weak adv q hlimit hbound fallback).trans (add_le_add le_rfl ?_)
  simpa only [prEvent_norm] using physical_source_weak_win_le_honest_address_mass adv

end Physical
end SLHDSA.SHAKE128s.Bridge.SharedExperiment
end
