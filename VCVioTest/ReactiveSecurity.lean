/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.Interaction.UC.ReactiveSecurity
public import VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility

/-!
# Executed contextual-security counterexamples

A context obtains a Boolean from a real communicating component. The examples retain
unfinished prefixes and distinguish changes to the component's local operation interpreter.
-/

public section

namespace Interaction.UC.ReactiveSecurity.Tests

open PFunctor OracleComp ReactiveProcess ReactiveNetwork DynSystem MeasureTheory
open scoped ENNReal

@[expose] def bitEffect : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩
@[expose] def noEffect : PFunctor.{0, 0} := ⟨Empty, Empty.elim⟩
@[expose] def request : Interface := ⟨Unit, fun _ => Unit⟩
@[expose] def response : Interface := ⟨Unit, fun _ => Bool⟩
@[expose] def boundary : PortBoundary := ⟨request, response⟩

@[expose] def server (draw : ProbComp Bool) : System boundary :=
  HandledAssembly.atom (DynComputation.ofFreeM fun _ =>
    (FreeM.liftBind .receive fun _ =>
      .liftBind (.effect ()) fun bit =>
      .liftBind (.send ⟨(), bit⟩) fun _ => .pure (.returned bit) :
        FreeM (signature bitEffect boundary) (Outcome Bool))) fun _ => draw

@[expose] def receiver : System (PortBoundary.swap boundary) :=
  HandledAssembly.atom (DynComputation.ofFreeM fun _ =>
    (FreeM.liftBind (.send ⟨(), ()⟩) fun _ =>
      .liftBind .receive fun packet => .pure (.returned packet.2) :
        FreeM (signature noEffect (PortBoundary.swap boundary)) (Outcome Bool)))
    fun operation => operation.elim

@[expose] def context (fuel : ℕ) : Context boundary := ⟨receiver, (), fuel⟩

attribute [local implicit_reducible] signature Response HandledAssembly.plug HandledAssembly.atom
  HandledAssembly.ofDiagram HandledDiagram.plug HandledDiagram.atom
  HandledDiagram.network Diagram.plug Diagram.map Diagram.wire Diagram.atom
  bitEffect noEffect boundary request response DynComputation.ofFreeM PFunctor.Obj
  PFunctor.Idx HandledDiagram.closedPair Diagram.withEnvironment

/-- The actual communicating experiment exposes the server's sampled bit. -/
theorem experiment_server (draw : ProbComp Bool) :
    experiment (server draw) (context 5) = (fun bit => some (some bit)) <$> draw := by
  simp only [experiment, context, server, receiver, HandledAssembly.plug,
    HandledAssembly.atom, HandledAssembly.ofDiagram, HandledAssembly.tokenObservation,
    HandledDiagram.atom_plug_atom]
  simp only [HandledDiagram.closedPair, HandledDiagram.tokenObservation,
    HandledDiagram.handlers, HandledDiagram.network, Diagram.withEnvironment,
    Diagram.plug, Diagram.map, Diagram.wire, Diagram.atom,
    runToken, activate, initial, DynComputation.ofFreeM_init,
    DynComputation.view_ofFreeM_liftBind, DynComputation.view_ofFreeM_pure,
    DynComputation.ofFreeM_State, FreeM.pure_eq_pure, StateT.run,
    pure_bind, bind_pure, bind_map_left,
    Functor.map_map, outcome, Function.update, ↓reduceDIte, dispatch, zero_add,
    Function.update_idem, List.nil_append, Nat.reduceAdd, Function.update_eq_self,
    Sum.inl_ne_inr, Sum.inr_ne_inl, bind_pure_comp, observe]
  rfl

/-- A prefix before the final receive has not returned a bit. -/
example (value : Bool) : experiment (server (pure value)) (context 4) = pure none := by
  cases value <;> rfl

/-- Actual returned bits survive the observation encoding. -/
example (value : Bool) :
    experiment (server (pure value)) (context 5) = pure (some (some value)) := by
  rw [experiment_server]
  simp

/-- Changing the local handler changes the probability experiment despite identical routing. -/
example : experiment (server (pure false)) (context 5) ≠
    experiment (server (pure true)) (context 5) := by
  rw [experiment_server, experiment_server]
  simp

/-- A deterministic server gives the corresponding point mass under actual execution. -/
theorem law_server_pure (bit : Bool) :
    law (server (pure bit)) (context 5) = Measure.dirac (some (some bit)) := by
  simp [law_eq_evalDist, experiment_server]

/-- The uniform local operation gives an equal mixture of the two returned observations. -/
theorem law_server_uniform : law (server ($ᵗ Bool)) (context 5) =
    (2 : ℝ≥0∞)⁻¹ • Measure.dirac (some (some false)) +
      (2 : ℝ≥0∞)⁻¹ • Measure.dirac (some (some true)) := by
  have hcoin : 𝒟[$ᵗ Bool] =
      (2 : ℝ≥0∞)⁻¹ • Measure.dirac false + (2 : ℝ≥0∞)⁻¹ • Measure.dirac true := by
    apply Measure.ext_of_singleton
    intro bit
    rw [evalDist_uniformSample, ProbabilityTheory.uniformOn_univ]
    cases bit <;> simp
  rw [law_eq_evalDist, experiment_server, evalDist_map_of_discrete, hcoin]
  rw [Measure.map_add _ _ Measurable.of_discrete,
    Measure.map_smul _ Measurable.of_discrete.aemeasurable,
    Measure.map_smul _ Measurable.of_discrete.aemeasurable]
  simp [Measure.map_dirac' Measurable.of_discrete]

private theorem tvDist_dirac_half {α : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] (x y : α) (hxy : x ≠ y) :
    (Measure.dirac x).tvDist
      ((2 : ℝ≥0∞)⁻¹ • Measure.dirac x + (2 : ℝ≥0∞)⁻¹ • Measure.dirac y) = 1 / 2 := by
  have hdist : (Measure.dirac x).etvDist
      ((2 : ℝ≥0∞)⁻¹ • Measure.dirac x + (2 : ℝ≥0∞)⁻¹ • Measure.dirac y) = 2⁻¹ := by
    have hhalf : (2 : ℝ≥0∞)⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr (by norm_num)
    apply le_antisymm
    · refine iSup_le fun s => ?_
      by_cases hx : x ∈ s.1 <;> by_cases hy : y ∈ s.1 <;>
        simp [Measure.dirac_apply' _ s.2, hx, hy, ENNReal.absDiff,
          ENNReal.inv_two_add_inv_two, tsub_eq_zero_of_le hhalf]
    · have h := Measure.absDiff_apply_le_etvDist (Measure.dirac x)
        ((2 : ℝ≥0∞)⁻¹ • Measure.dirac x + (2 : ℝ≥0∞)⁻¹ • Measure.dirac y)
        (measurableSet_singleton x)
      simpa [Measure.dirac_apply', hxy, Ne.symm hxy, ENNReal.absDiff,
        tsub_eq_zero_of_le hhalf] using h
  simp [Measure.tvDist, hdist]

/-- Each adjacent executed comparison has error one half. -/
theorem advantage_pure_uniform (bit : Bool) :
    advantage (server (pure bit)) (server ($ᵗ Bool)) (context 5) = 1 / 2 := by
  rw [advantage_eq_tvDist, law_server_pure, law_server_uniform]
  cases bit
  · exact tvDist_dirac_half _ _ (by decide)
  · rw [add_comm]
    exact tvDist_dirac_half _ _ (by decide)

/-- The two deterministic communicating servers are perfectly distinguishable. -/
theorem advantage_false_true :
    advantage (server (pure false)) (server (pure true)) (context 5) = 1 := by
  rw [advantage_eq_tvDist, law_server_pure, law_server_pure]
  have hdist : (Measure.dirac (some (some false) : Result)).etvDist
      (Measure.dirac (some (some true))) = 1 := by
    apply le_antisymm
    · exact Measure.etvDist_le_one _ _ (by simp) (by simp)
    · simpa [ENNReal.absDiff] using Measure.absDiff_apply_le_etvDist
        (Measure.dirac (some (some false) : Result)) (Measure.dirac (some (some true)))
        (measurableSet_singleton (some (some false)))
  simp [Measure.tvDist, hdist]

/-- Reusing a positive error threshold under transitivity is unsound even for actual networks. -/
theorem fixed_error_not_transitive :
    ¬ (∀ first middle last : System boundary,
      advantage first middle (context 5) ≤ 1 / 2 →
      advantage middle last (context 5) ≤ 1 / 2 →
      advantage first last (context 5) ≤ 1 / 2) := by
  intro h
  have hleft := (advantage_pure_uniform false).le
  have hright : advantage (server ($ᵗ Bool)) (server (pure true)) (context 5) ≤ 1 / 2 := by
    simpa only [advantage_comm] using (advantage_pure_uniform true).le
  have hbad := h _ _ _ hleft hright
  rw [advantage_false_true] at hbad
  norm_num at hbad

/-- The graded API composes the two real comparisons with the required sum of errors. -/
theorem executed_graded_comparison :
    ContextualWithin (fun closing => closing = context 5) (1 / 2 + 1 / 2)
      (server (pure false)) (server (pure true)) := by
  apply ContextualWithin.trans (middle := server ($ᵗ Bool))
  · rintro _ rfl
    exact (advantage_pure_uniform false).le
  · rintro _ rfl
    rw [advantage_comm]
    exact (advantage_pure_uniform true).le

/-- The same allowed-context comparison fails if its error is left at one half. -/
theorem executed_half_comparison_false :
    ¬ ContextualWithin (fun closing => closing = context 5) (1 / 2)
      (server (pure false)) (server (pure true)) := by
  intro h
  have hbad := h (context 5) rfl
  rw [advantage_false_true] at hbad
  norm_num at hbad

@[expose] def abortingContext : Context boundary where
  system := HandledAssembly.atom
    (DynComputation.ofFreeM fun _ =>
      (.pure .aborted : FreeM (signature noEffect (PortBoundary.swap boundary)) (Outcome Bool)))
    fun operation => operation.elim
  environment := ()
  fuel := 0

/-- Explicit abort is an observed value even at an empty execution prefix. -/
example (system : System boundary) : experiment system abortingContext = pure (some none) := by
  rfl

/-- An unfinished exchange and an explicit abort remain distinct observed laws. -/
example : law (server (pure false)) (context 4) ≠
    law (server (pure false)) abortingContext := by
  rw [law_eq_evalDist, law_eq_evalDist]
  change 𝒟[(pure none : ProbComp Result)] ≠ 𝒟[(pure (some none) : ProbComp Result)]
  simp only [evalDist_pure]
  intro h
  have hevent := congrArg (fun μ : Measure Result => μ {none}) h
  simp at hevent

end Interaction.UC.ReactiveSecurity.Tests
