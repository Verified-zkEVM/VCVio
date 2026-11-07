/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Counted observations and passive query meters

A phase-independent ambient policy with zero attempt charges counts the same primitive queries
as a passive state extension.
The exact run equation retains the entire observation and underlying state at the same client.
-/

public section

namespace SignatureAlg.SigningView

open OracleComp OracleSpec

universe v

variable {ι Request PK SK Sig Reply σ : Type} {spec : OracleSpec.{0, 0} ι}
  {m : Type → Type v} [Monad m] [LawfulMonad m]

-- These two closure laws use only the existing writer's sequencing and output maps.
private theorem runAdd_bind_meter (weight : spec.Domain → Nat)
    (impl : QueryImpl spec (StateT σ m)) {α β : Type}
    (left : CostM spec Nat α) (next : α → CostM spec Nat β)
    (hleft : ∀ initial start,
      (simulateQ (impl.extendState (fun t _ _ _ n => n + weight t)) left.runAdd).run
        (initial, start) =
      (fun z : (α × Nat) × σ => (z.1, (z.2, start + z.1.2))) <$>
        (simulateQ impl left.runAdd).run initial)
    (hnext : ∀ value initial start,
      (simulateQ (impl.extendState (fun t _ _ _ n => n + weight t))
        (next value).runAdd).run (initial, start) =
      (fun z : (β × Nat) × σ => (z.1, (z.2, start + z.1.2))) <$>
        (simulateQ impl (next value).runAdd).run initial)
    (initial : σ) (start : Nat) :
    (simulateQ (impl.extendState (fun t _ _ _ n => n + weight t))
      (left >>= next).runAdd).run (initial, start) =
      (fun z : (β × Nat) × σ => (z.1, (z.2, start + z.1.2))) <$>
        (simulateQ impl (left >>= next).runAdd).run initial := by
  simp only [AddWriterT.runAdd_bind, simulateQ_bind, simulateQ_map, StateT.run_bind,
    StateT.run_map]
  rw [hleft initial start]
  simp only [bind_map_left, map_bind, Functor.map_map]
  apply bind_congr
  rintro ⟨⟨value, cost⟩, final⟩
  rw [hnext value final (start + cost)]
  simp [Functor.map_map, Prod.map, Nat.add_assoc]

private theorem runAdd_map_meter (weight : spec.Domain → Nat)
    (impl : QueryImpl spec (StateT σ m)) {α β : Type}
    (action : CostM spec Nat α) (f : α → β) (initial : σ) (start : Nat)
    (h : (simulateQ (impl.extendState (fun t _ _ _ n => n + weight t))
      action.runAdd).run (initial, start) =
      (fun z : (α × Nat) × σ => (z.1, (z.2, start + z.1.2))) <$>
        (simulateQ impl action.runAdd).run initial) :
    (simulateQ (impl.extendState (fun t _ _ _ n => n + weight t))
      (f <$> action).runAdd).run (initial, start) =
      (fun z : (β × Nat) × σ => (z.1, (z.2, start + z.1.2))) <$>
        (simulateQ impl (f <$> action).runAdd).run initial := by
  have mapped := congrArg
    (fun result : m ((α × Nat) × (σ × Nat)) =>
      (fun z => ((f z.1.1, z.1.2), z.2)) <$> result) h
  simpa only [AddWriterT.runAdd_map, simulateQ_map, StateT.run_map,
    Functor.map_map, Prod.map, id_eq] using mapped

private theorem costed_extendState_weight_run
    (policy : Event spec Request → Nat) (weight : spec.Domain → Nat)
    (ambient : ∀ phase input, policy (.ambient phase input) = weight input)
    (impl : QueryImpl spec (StateT σ m)) (phase : Phase) {α : Type}
    (body : OracleComp spec α) (initial : σ) (start : Nat) :
    (simulateQ (impl.extendState (fun t _ _ _ n => n + weight t))
      (costed policy phase body).runAdd).run (initial, start) =
      (fun z : (α × Nat) × σ => (z.1, (z.2, start + z.1.2))) <$>
        (simulateQ impl (costed policy phase body).runAdd).run initial := by
  have charged (input : spec.Domain) :
      (costed policy phase (liftM (spec.query input))).runAdd =
        (fun reply => (reply, weight input)) <$>
          (liftM (spec.query input) : OracleComp spec (spec.Range input)) := by
    rw [costed_query]
    simp [ambient, AddWriterT.runAdd, WriterT.run_bind, AddWriterT.addTell,
      Functor.map_map, Prod.map]
  induction body using OracleComp.inductionOn generalizing initial start with
  | pure value => simp
  | query_bind input next ih =>
    simp only [costed_bind, AddWriterT.runAdd_bind, charged, simulateQ_bind,
      simulateQ_map, simulateQ_spec_query, StateT.run_bind, StateT.run_map,
      QueryImpl.extendState_apply, map_bind, bind_map_left, bind_assoc, pure_bind,
      Functor.map_map]
    apply bind_congr
    rintro ⟨reply, final⟩
    simp [ih, Prod.map, Nat.add_assoc]

private theorem countedPhase_extendState_weight_run
    (policy : Event spec Request → Nat) (weight : spec.Domain → Nat)
    (ambient : ∀ phase input, policy (.ambient phase input) = weight input)
    (attempt0 : ∀ request, policy (.signingAttempt request) = 0)
    (impl : QueryImpl spec (StateT σ m))
    (view : SigningView (OracleComp spec) Request PK SK Sig Reply)
    (pk : PK) (sk : SK) {α : Type}
    (body : OracleComp (spec + (Request →ₒ Reply)) α) (initial : σ) (start : Nat) :
    (simulateQ (impl.extendState (fun t _ _ _ n => n + weight t))
      (countedPhase policy view pk sk body).runAdd).run (initial, start) =
      (fun z : ((α × QueryLog (Request →ₒ Reply)) × Nat) × σ =>
        (z.1, (z.2, start + z.1.2))) <$>
        (simulateQ impl (countedPhase policy view pk sk body).runAdd).run initial := by
  have ambientQuery (input : spec.Domain) :
      countedPhase policy view pk sk
        (liftM ((spec + (Request →ₒ Reply)).query (.inl input))) =
      (fun reply => (reply, ([] : QueryLog (Request →ₒ Reply)))) <$>
        costed policy .adversary (liftM (spec.query input)) := by
    simp only [countedPhase, countedPhaseUsing, simulateQ_spec_query,
      countedHandlerUsing, QueryImpl.add_apply_inl,
      QueryImpl.liftTarget_apply, WriterT.run_monadLift']
    rw [costed, simulateQ_spec_query]
    rfl
  have signingQuery (request : Request) :
      countedPhase policy view pk sk
        (liftM ((spec + (Request →ₒ Reply)).query (.inr request))) =
      (fun reply => (reply, ([⟨request, reply⟩] : QueryLog (Request →ₒ Reply)))) <$>
        costed policy .signer (view.sign pk sk request) := by
    rw [countedPhase_signingQuery, attempt0]
    apply WriterT.ext
    simp [AddWriterT.addTell, WriterT.run_bind]
  have queryCase (input : (spec + (Request →ₒ Reply)).Domain) (state : σ) (counter : Nat) :
      (simulateQ (impl.extendState (fun t _ _ _ n => n + weight t))
        (countedPhase policy view pk sk
          (liftM ((spec + (Request →ₒ Reply)).query input))).runAdd).run (state, counter) =
      (fun z : (((spec + (Request →ₒ Reply)).Range input ×
          QueryLog (Request →ₒ Reply)) × Nat) × σ =>
        (z.1, (z.2, counter + z.1.2))) <$>
        (simulateQ impl (countedPhase policy view pk sk
          (liftM ((spec + (Request →ₒ Reply)).query input))).runAdd).run state := by
    cases input with
    | inl input =>
      rw [ambientQuery]
      exact runAdd_map_meter weight impl _ _ state counter
        (costed_extendState_weight_run policy weight ambient impl .adversary _ state counter)
    | inr request =>
      rw [signingQuery]
      exact runAdd_map_meter weight impl _ _ state counter
        (costed_extendState_weight_run policy weight ambient impl .signer _ state counter)
  induction body using OracleComp.inductionOn generalizing initial start with
  | pure value => simp [countedPhase, countedPhaseUsing]
  | query_bind input next ih =>
    rw [countedPhase_bind]
    apply runAdd_bind_meter
    · exact queryCase input
    · rintro ⟨reply, leftLog⟩ state counter
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using
        runAdd_map_meter weight impl _ (fun (b, right) => (b, leftLog ++ right))
          state counter (ih reply state counter)

/-- A passive primitive-query meter records the observation's cost beside the same full state.

Ambient weights are independent of phase, and signing attempts have no separate charge.
The base monad needs no probability or completion assumption.
-/
theorem countedExperiment_extendState_weight_run
    (policy : Event spec Request → Nat) (weight : spec.Domain → Nat)
    (ambient : ∀ phase input, policy (.ambient phase input) = weight input)
    (attempt0 : ∀ request, policy (.signingAttempt request) = 0)
    (view : SigningView (OracleComp spec) Request PK SK Sig Reply)
    (A : PK → OracleComp (spec + (Request →ₒ Reply)) (Request × Sig))
    (impl : QueryImpl spec (StateT σ m)) (initial : σ) (start : Nat) :
    (simulateQ (impl.extendState (fun t _ _ _ n => n + weight t))
      (countedExperiment policy view A)).run (initial, start) =
      (fun z : Observation Request Sig Reply Nat × σ =>
        (z.1, (z.2, start + z.1.cost))) <$>
        (simulateQ impl (countedExperiment policy view A)).run initial := by
  have after (pk : PK) (sk : SK) (state : σ) (counter : Nat) :
      (simulateQ (impl.extendState (fun t _ _ _ n => n + weight t))
        (countedAfterKeygen policy view pk sk A).runAdd).run (state, counter) =
      (fun z : (Outcome Request Sig Reply × Nat) × σ =>
        (z.1, (z.2, counter + z.1.2))) <$>
        (simulateQ impl (countedAfterKeygen policy view pk sk A).runAdd).run state := by
    unfold countedAfterKeygen
    apply runAdd_bind_meter
    · exact countedPhase_extendState_weight_run policy weight ambient attempt0 impl view pk sk _
    · rintro ⟨forgery, rawLog⟩
      apply runAdd_bind_meter
      · exact costed_extendState_weight_run policy weight ambient impl .verification _
      · intro verified state counter
        simp
  have complete := runAdd_bind_meter weight impl (costed policy .keygen view.keygen)
    (fun keys => countedAfterKeygen policy view keys.1 keys.2 A)
    (costed_extendState_weight_run policy weight ambient impl .keygen _)
    (fun keys => after keys.1 keys.2) initial start
  have mapped := congrArg
    (fun result : m ((Outcome Request Sig Reply × Nat) × (σ × Nat)) =>
      (fun z => (({ toOutcome := z.1.1, cost := z.1.2 } :
        Observation Request Sig Reply Nat), z.2)) <$> result) complete
  simpa only [countedExperiment, simulateQ_map, StateT.run_map,
    Functor.map_map] using mapped

/-- Complete supported endpoints retain the same observation, full base state and exact meter. -/
theorem mem_support_countedExperiment_extendState_weight_run_iff
    [MonadAttach m] [ExactMonadAttach m]
    (policy : Event spec Request → Nat) (weight : spec.Domain → Nat)
    (ambient : ∀ phase input, policy (.ambient phase input) = weight input)
    (attempt0 : ∀ request, policy (.signingAttempt request) = 0)
    (view : SigningView (OracleComp spec) Request PK SK Sig Reply)
    (A : PK → OracleComp (spec + (Request →ₒ Reply)) (Request × Sig))
    (impl : QueryImpl spec (StateT σ m)) (initial : σ) (start : Nat)
    (observation : Observation Request Sig Reply Nat) (final : σ) (counter : Nat) :
    (observation, (final, counter)) ∈ support
      ((simulateQ (impl.extendState (fun t _ _ _ n => n + weight t))
        (countedExperiment policy view A)).run (initial, start)) ↔
      (observation, final) ∈ support
        ((simulateQ impl (countedExperiment policy view A)).run initial) ∧
          counter = start + observation.cost := by
  rw [countedExperiment_extendState_weight_run policy weight ambient attempt0]
  simp only [MonadAttach.support_map, Set.mem_image]
  constructor
  · rintro ⟨⟨observed, state⟩, h, equal⟩
    cases equal
    exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨(observation, final), h, rfl⟩

end SignatureAlg.SigningView
