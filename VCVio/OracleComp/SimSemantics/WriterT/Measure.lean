/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import ToMathlib.Control.WriterT.State
public import VCVio.OracleComp.SimSemantics.WriterT.Core
public import VCVio.OracleComp.SimSemantics.StateT.Measure

/-!
# Joint append-log and service-state distributions

Local laws transport the entire chronological log and retained state through an adaptive fold.
Clipped laws compose when the complete retained state freezes after abort.
-/

public section

universe u v idx

open OracleComp OracleSpec

namespace OracleComp

/-- Local joint response, append-log and state laws lift to complete adaptive runs. -/
theorem evalDistEq_simulateQ_run_writerT_stateT_map :
  ∀ {ι : Type} {spec : OracleSpec ι} {σ τ ω ν α : Type}
    [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    [EmptyCollection ν] [Append ν] [LawfulAppend ν]
    (left : QueryImpl spec (WriterT ν (StateT τ ProbComp)))
    (right : QueryImpl spec (WriterT ω (StateT σ ProbComp)))
    (project : σ → τ) (mapLog : ω → ν),
    mapLog ∅ = ∅ →
    (∀ first second, mapLog (first ++ second) = mapLog first ++ mapLog second) →
    (∀ input state,
      (left input).run.run (project state) =ᵈ
        (fun output => ((output.1.1, mapLog output.1.2), project output.2)) <$>
          (right input).run.run state) →
    ∀ (program : OracleComp spec α) (state : σ),
      (simulateQ left program).run.run (project state) =ᵈ
        (fun output => ((output.1.1, mapLog output.1.2), project output.2)) <$>
          (simulateQ right program).run.run state := by
  intro ι spec σ τ ω ν α _ _ _ _ _ _ left right project mapLog hzero happ hstep program state
  have augmentedStep : ∀ input (current : σ × ω),
      (WriterT.appendToState (left input)).run (project current.1, mapLog current.2) =ᵈ
        Prod.map id (fun final => (project final.1, mapLog final.2)) <$>
          (WriterT.appendToState (right input)).run current := by
    intro input current
    have h := (hstep input current.1).map fun output =>
      (output.1.1, (output.2, mapLog current.2 ++ output.1.2))
    simpa only [WriterT.appendToState, StateT.run_mk, Functor.map_map, Function.comp_def,
      Prod.map, id_eq, happ] using h
  have h := OracleComp.evalDistEq_simulateQ_run_map
    (fun input => WriterT.appendToState (left input))
    (fun input => WriterT.appendToState (right input))
    (fun current => (project current.1, mapLog current.2)) augmentedStep
    program (state, (∅ : ω))
  rw [← writerToState_simulateQ, ← writerToState_simulateQ] at h
  have joint := h.map fun output : α × (τ × ν) =>
    ((output.1, output.2.2), output.2.1)
  simp only [WriterT.appendToState, StateT.run_mk, hzero,
    LawfulAppend.empty_append, Functor.map_map, Prod.map, id_eq,
    Prod.mk.eta] at joint
  have hid : (fun output : (α × ν) × τ => output) <$>
        (simulateQ left program).run.run (project state) =
      (simulateQ left program).run.run (project state) := by
    change id <$> (simulateQ left program).run.run (project state) = _
    exact id_map _
  rw [hid] at joint
  exact joint

/-- Clipped query laws compose while the complete physical state freezes after abort. -/
theorem evalDistEq_simulateQ_run_writerT_stateT_clip :
  ∀ {iota sigma alpha omega : Type} {spec : OracleSpec.{0, 0} iota}
    [EmptyCollection omega] [Append omega] [LawfulAppend omega]
    (aborted : sigma → Bool)
    (left right : QueryImpl spec (WriterT omega (StateT sigma ProbComp))),
    (∀ (input : spec.Domain) (state : sigma),
      let clip := fun result : ((spec.Range input × omega) × sigma) =>
        (if aborted result.2 then none else some result.1, result.2)
      (clip <$> ((left input).run).run state) =ᵈ
        (clip <$> ((right input).run).run state)) →
    (∀ (input : spec.Domain) (state : sigma), aborted state = true →
      ∀ result ∈ support (((left input).run).run state), result.2 = state) →
    (∀ (input : spec.Domain) (state : sigma), aborted state = true →
      ∀ result ∈ support (((right input).run).run state), result.2 = state) →
    ∀ (program : OracleComp spec alpha) (initial : sigma),
      let clip := fun result : ((alpha × omega) × sigma) =>
        (if aborted result.2 then none else some result.1, result.2)
      (clip <$> ((simulateQ left program).run).run initial) =ᵈ
        (clip <$> ((simulateQ right program).run).run initial) := by
  classical
  intro iota sigma alpha omega spec _ _ _ aborted left right step frozenLeft frozenRight
  let clip {beta : Type} (r : ((beta × omega) × sigma)) :=
    (if aborted r.2 then none else some r.1, r.2)
  have constant {beta : Type} (p : ProbComp ((beta × omega) × sigma)) (s : sigma)
      (hs : aborted s = true) (hp : ∀ r ∈ support p, r.2 = s) :
      (clip <$> p) =ᵈ (pure (none, s) : ProbComp (Option (beta × omega) × sigma)) := by
    rw [map_eq_bind_pure_comp]
    refine (OracleComp.EvalDistEq.bind_congr_of_support p (fun r hr => ?_)).trans
      (OracleComp.EvalDistEq.bind_const p (pure (none, s)))
    simp only [Function.comp_apply, clip, hp r hr, hs, ↓reduceIte]
    exact EvalDistEq.rfl
  have whole : ∀ (program : OracleComp spec alpha) (s : sigma),
      (aborted s = true → ∀ r ∈ support ((simulateQ left program).run.run s), r.2 = s) ∧
      (aborted s = true → ∀ r ∈ support ((simulateQ right program).run.run s), r.2 = s) ∧
      (clip <$> ((simulateQ left program).run.run s)) =ᵈ
        (clip <$> ((simulateQ right program).run.run s)) := by
    intro program
    induction program using OracleComp.inductionOn with
    | pure value =>
      intro s
      simp only [simulateQ_pure, WriterT.run_pure', StateT.run_pure, support_pure,
        Set.mem_singleton_iff, forall_eq, map_pure]
      exact ⟨fun _ => True.intro, fun _ => True.intro, EvalDistEq.rfl⟩
    | query_bind input next ih =>
      intro s
      let run := fun (impl : QueryImpl spec (WriterT omega (StateT sigma ProbComp)))
          (a : spec.Range input) (state : sigma) => (simulateQ impl (next a)).run.run state
      let add := fun (w : omega) (r : ((alpha × omega) × sigma)) =>
        ((r.1.1, w ++ r.1.2), r.2)
      have expand (impl : QueryImpl spec (WriterT omega (StateT sigma ProbComp))) :
          (simulateQ impl (query input >>= next)).run.run s =
            ((impl input).run.run s >>= fun z => add z.1.2 <$> run impl z.1.1 z.2) := by
        simp only [simulateQ_bind, simulateQ_HasQuery_query, WriterT.run_bind',
          StateT.run_bind, StateT.run_map, run, add]
        rfl
      have frozen (impl : QueryImpl spec (WriterT omega (StateT sigma ProbComp)))
          (hf : ∀ state, aborted state = true →
            ∀ r ∈ support ((impl input).run.run state), r.2 = state)
          (ht : ∀ a state, aborted state = true →
            ∀ r ∈ support (run impl a state), r.2 = state) :
          aborted s = true →
            ∀ r ∈ support ((simulateQ impl (query input >>= next)).run.run s), r.2 = s := by
        intro hs r hr
        rw [expand] at hr
        obtain ⟨z, hz, hr⟩ := mem_support_bind_peel _ _ hr
        obtain ⟨v, hv, rfl⟩ := mem_support_map_peel _ _ hr
        have hzstate := hf s hs z hz
        exact (ht z.1.1 z.2 (hzstate ▸ hs) v hv).trans hzstate
      refine ⟨frozen left (frozenLeft input) (fun a state => (ih a state).1),
        frozen right (frozenRight input) (fun a state => (ih a state).2.1), ?_⟩
      let resume : QueryImpl spec (WriterT omega (StateT sigma ProbComp)) →
          (Option (spec.Range input × omega) × sigma) →
          ProbComp (Option (alpha × omega) × sigma) := fun impl z =>
        match z.1 with
        | none => pure (none, z.2)
        | some (a, w) =>
          (fun r : Option (alpha × omega) × sigma =>
            (r.1.map (fun p : alpha × omega => (p.1, w ++ p.2)), r.2)) <$> (clip <$> run impl a z.2)
      have factor (impl : QueryImpl spec (WriterT omega (StateT sigma ProbComp)))
          (ht : ∀ a state, aborted state = true →
            ∀ r ∈ support (run impl a state), r.2 = state) :
          (clip <$> ((simulateQ impl (query input >>= next)).run.run s)) =ᵈ
            ((clip <$> (impl input).run.run s) >>= resume impl) := by
        rw [expand, map_bind, bind_map_left]
        refine EvalDistEq.bind_right _ fun z => ?_
        by_cases hz : aborted z.2 = true
        · have original : (clip <$> (add z.1.2 <$> run impl z.1.1 z.2)) =ᵈ
              (pure (none, z.2) : ProbComp (Option (alpha × omega) × sigma)) := by
            apply constant _ _ hz
            intro r hr
            obtain ⟨v, hv, rfl⟩ := mem_support_map_peel _ _ hr
            exact ht z.1.1 z.2 hz v hv
          simpa only [resume, clip, hz, Bool.true_eq, ↓reduceIte] using original
        · have hz' : aborted z.2 = false := Bool.eq_false_iff.mpr hz
          simp only [clip, hz', Bool.false_eq_true, ↓reduceIte, Functor.map_map]
          have heq : (fun x : ((alpha × omega) × sigma) =>
              (if aborted x.2 then none else some (add z.1.2 x).1, x.2)) =
              (fun x : ((alpha × omega) × sigma) =>
                ((if aborted x.2 then none else some x.1).map
                  (fun p => (p.1, z.1.2 ++ p.2)), x.2)) := by
            funext x
            cases aborted x.2 <;> simp [add]
          exact congrArg (fun f => f <$> run impl z.1.1 z.2) heq ▸ EvalDistEq.rfl
      refine (factor left (fun a state => (ih a state).1)).trans
        (((step input s).bind (fun z => ?_)).trans
          (factor right (fun a state => (ih a state).2.1)).symm)
      rcases z with ⟨_ | ⟨a, w⟩, state⟩
      · exact EvalDistEq.rfl
      · exact (ih a state).2.2.map _
  intro program initial
  exact (whole program initial).2.2


end OracleComp
