/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.SimSemantics.QueryImpl.Constructions.Core
public import VCVio.OracleComp.SimSemantics.Append.Core
public import VCVio.OracleComp.EvalDist.Measure

/-!
# `StateT` Invariant Theory

Support-based invariant reasoning for shared, stateful oracle simulations
(ROM/AGM/hybrids) whose handlers live in `StateT σ m`, in particular `StateT σ ProbComp`. A
user-supplied predicate `Inv : σ → Prop` is preserved by an implementation when every reachable
post-state satisfies it.

Reachability controls pathwise invariants. Output independence uses the successful-output
measure directly; uniform oracle computations are lossless.

The `WriterT` analogue of this theory lives in
`SimSemantics/WriterT/PreservesInv.lean`.

## Main definitions

- `QueryImpl.PreservesInv` — every oracle query implementation step preserves `Inv`;
  `QueryImpl.PreservesInv.add` / `preservesInv_add_iff` split it over a sum of implementations,
  and `QueryImpl.PreservesInv.extendState` carries it through a passive state extension
- `OracleComp.simulateQ_run_preservesInv` — simulating any oracle computation
  with a preserving implementation preserves `Inv` on the final state;
  `OracleComp.simulateQ_run_simulateQ_run_preservesInv` is the version for a relation between the
  states of an inner and an outer handler, run one inside the other
- `InitSatisfiesInv` — every sampled initial state satisfies the invariant
- `StateT.StatePreserving` — computation never changes the state
- `StateT.PreservesInv` — computation preserves an invariant on the state; the structural
  rules `preservesInv_pure`/`_monadLift`/`_map`/`_bind`/`_get_bind`/`_set_of`/`_mapM` check a
  handler written in `do` notation clause by clause
- `StateT.OutputIndependent` — output distribution is independent of the initial state
  under an invariant
- `StateT.outputIndependent_after_preservesInv` — non-interference: output-independent
  computation remains so after sequencing with an invariant-preserving computation
-/

@[expose] public section

noncomputable section

open OracleComp OracleSpec MeasureTheory

open scoped OracleSpec.PrimitiveQuery

universe u v w

namespace StateT

/-- `PreservesInv mx Inv` means that starting from any state satisfying `Inv`, every reachable
post-state (support-wise) also satisfies `Inv`. -/
def PreservesInv {m : Type → Type v} [MonadAttach m] {σ α : Type}
    (mx : StateT σ m α) (Inv : σ → Prop) : Prop :=
  ∀ σ0, Inv σ0 → ∀ z ∈ support (mx.run σ0), Inv z.2

end StateT

namespace QueryImpl

/-- `PreservesInv impl Inv` means every oracle query implementation step preserves `Inv`
on all reachable post-states (support-based): each `impl t` is a `StateT.PreservesInv`
computation. -/
def PreservesInv {m : Type → Type v} [MonadAttach m]
    {ι : Type u} {spec : OracleSpec.{u, 0} ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ m)) (Inv : σ → Prop) : Prop :=
  ∀ t, StateT.PreservesInv (impl t) Inv

variable {m : Type → Type v} [MonadAttach m]

lemma preservesInv_iff {ι : Type u} {spec : OracleSpec.{u, 0} ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ m)) (Inv : σ → Prop) :
    PreservesInv impl Inv ↔ ∀ t, StateT.PreservesInv (impl t) Inv :=
  Iff.rfl

lemma PreservesInv.trivial {ι : Type u} {spec : OracleSpec.{u, 0} ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ m)) :
    PreservesInv impl (fun _ => True) :=
  fun _ _ _ _ _ => True.intro

lemma PreservesInv.and {ι : Type u} {spec : OracleSpec.{u, 0} ι} {σ : Type}
    {impl : QueryImpl spec (StateT σ m)} {P Q : σ → Prop}
    (hP : PreservesInv impl P) (hQ : PreservesInv impl Q) :
    PreservesInv impl (fun s => P s ∧ Q s) :=
  fun t σ0 ⟨hp, hq⟩ z hz => ⟨hP t σ0 hp z hz, hQ t σ0 hq z hz⟩

lemma PreservesInv.of_forall {ι : Type u} {spec : OracleSpec.{u, 0} ι} {σ : Type}
    {impl : QueryImpl spec (StateT σ m)} {Inv : σ → Prop}
    (h : ∀ t σ0 z, z ∈ support ((impl t).run σ0) → Inv z.2) :
    PreservesInv impl Inv :=
  fun t σ0 _ z hz => h t σ0 z hz

/-- A sum of implementations preserves `Inv` when both summands do. -/
lemma PreservesInv.add {ι₁ ι₂ : Type u} {spec₁ : OracleSpec.{u, 0} ι₁}
    {spec₂ : OracleSpec.{u, 0} ι₂} {σ : Type}
    {impl₁ : QueryImpl spec₁ (StateT σ m)} {impl₂ : QueryImpl spec₂ (StateT σ m)}
    {Inv : σ → Prop} (h₁ : PreservesInv impl₁ Inv) (h₂ : PreservesInv impl₂ Inv) :
    PreservesInv (impl₁ + impl₂) Inv
  | .inl t => by rw [add_apply_inl]; exact h₁ t
  | .inr t => by rw [add_apply_inr]; exact h₂ t

lemma preservesInv_add_iff {ι₁ ι₂ : Type u} {spec₁ : OracleSpec.{u, 0} ι₁}
    {spec₂ : OracleSpec.{u, 0} ι₂} {σ : Type} (impl₁ : QueryImpl spec₁ (StateT σ m))
    (impl₂ : QueryImpl spec₂ (StateT σ m)) (Inv : σ → Prop) :
    PreservesInv (impl₁ + impl₂) Inv ↔ PreservesInv impl₁ Inv ∧ PreservesInv impl₂ Inv :=
  ⟨fun h => ⟨fun t => by simpa only [add_apply_inl] using h (.inl t),
    fun t => by simpa only [add_apply_inr] using h (.inr t)⟩, fun h => h.1.add h.2⟩

/-- A handler preserving an invariant still preserves it, read on the base state, after being
extended by a passive auxiliary state. -/
theorem PreservesInv.extendState [Monad m] [LawfulMonad m] [LawfulMonadAttach m]
    {ι : Type} {spec : OracleSpec ι} {σ Q : Type}
    {impl : QueryImpl spec (StateT σ m)} {Inv : σ → Prop} (h : PreservesInv impl Inv)
    (aux : (t : spec.Domain) → σ → spec.Range t → σ → Q → Q) :
    PreservesInv (impl.extendState aux) fun st ↦ Inv st.1 := by
  intro t st hst z hz
  rw [extendState_apply] at hz
  obtain ⟨w, hw, hz⟩ := LawfulMonadAttach.canReturn_bind_imp' hz
  rw [← LawfulMonadAttach.eq_of_canReturn_pure hz]
  exact h t st.1 hst w hw

end QueryImpl

namespace OracleComp

open QueryImpl

/-- If `impl` preserves `Inv`, then simulating *any* oracle computation with `simulateQ impl`
preserves `Inv` on the final state (support-wise). -/
theorem simulateQ_run_preservesInv
    {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
    {ι : Type u} {spec : OracleSpec.{u, 0} ι} {σ α : Type}
    (impl : QueryImpl spec (StateT σ m)) (Inv : σ → Prop)
    (himpl : QueryImpl.PreservesInv impl Inv) :
    ∀ oa : OracleComp spec α,
    ∀ σ0, Inv σ0 →
      ∀ z ∈ support ((simulateQ impl oa).run σ0), Inv z.2 := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro σ0 hσ0 z hz
    simp only [simulateQ_pure, StateT.run_pure, MonadAttach.mem_support] at hz
    rw [← LawfulMonadAttach.eq_of_canReturn_pure hz]
    exact hσ0
  | query_bind t oa ih =>
    intro σ0 hσ0 z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run_bind, MonadAttach.mem_support] at hz
    obtain ⟨us, hus, hz⟩ := LawfulMonadAttach.canReturn_bind_imp' hz
    exact ih us.1 us.2 (himpl t σ0 hσ0 us hus) z hz

/-- A relation `Inv` between the state of an inner handler and the state of an outer handler is
preserved by running a computation through the inner handler and then the result through the
outer one, when it is preserved by running each inner step through the outer handler. -/
theorem simulateQ_run_simulateQ_run_preservesInv {ι₀ ι₁ ι₂ : Type} {spec₀ : OracleSpec ι₀}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {σ τ α : Type}
    (outer : QueryImpl spec₁ (StateT τ (OracleComp spec₂)))
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁))) (Inv : σ → τ → Prop)
    (hstep : ∀ t s q, Inv s q →
      ∀ z ∈ support ((simulateQ outer ((inner t).run s)).run q), Inv z.1.2 z.2)
    (oa : OracleComp spec₀ α) (s : σ) (q : τ) (h : Inv s q) {z : (α × σ) × τ}
    (hz : z ∈ support ((simulateQ outer ((simulateQ inner oa).run s)).run q)) :
    Inv z.1.2 z.2 := by
  induction oa using OracleComp.inductionOn generalizing s q with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact h
  | query_bind t k ih =>
    rw [run_simulateQ_query_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    exact ih y.1.1 y.1.2 y.2 (hstep t s q h y hy) hz

end OracleComp

namespace QueryImpl

/-- If `so'` preserves `Inv`, then `so' ∘ₛ so` also preserves `Inv` for any `so`. -/
lemma PreservesInv.compose {m : Type → Type v} [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m] {ι : Type u} {ι' : Type w}
    {spec : OracleSpec.{u, 0} ι} {spec' : OracleSpec.{w, 0} ι'}
    {σ : Type} {so' : QueryImpl spec' (StateT σ m)}
    {so : QueryImpl spec (OracleComp spec')} {Inv : σ → Prop}
    (h : PreservesInv so' Inv) :
    PreservesInv (so' ∘ₛ so) Inv :=
  fun t σ0 hσ0 z hz =>
    OracleComp.simulateQ_run_preservesInv so' Inv h (so t) σ0 hσ0 z
      (by simpa [apply_compose] using hz)

end QueryImpl

/-- `InitSatisfiesInv init Inv` means every possible initial state sampled by `init`
satisfies `Inv` (support-based). -/
def InitSatisfiesInv {m : Type → Type v} [MonadAttach m] {σ : Type}
    (init : m σ) (Inv : σ → Prop) : Prop :=
  ∀ σ0 ∈ support init, Inv σ0

/-! ## StateT invariant properties

These properties are useful for **non-interference** arguments in sequential composition proofs.
Support-based properties work over any lawful attached monad. Output independence below uses
`ProbComp` measures. -/

namespace StateT

/-- `StatePreserving mx` means `mx` never changes the state: for every starting state `σ0`,
every outcome in the support of `mx.run σ0` has final state equal to `σ0`. -/
def StatePreserving {m : Type → Type v} [MonadAttach m] {σ α : Type}
    (mx : StateT σ m α) : Prop :=
  ∀ σ0, ∀ z ∈ support (mx.run σ0), z.2 = σ0

/-- `OutputIndependent mx Inv` means the output distribution of `mx` does not depend on the
initial state, as long as the initial state satisfies `Inv`.

This is distributional equality of `run'` (which discards the final state). -/
def OutputIndependent {σ α : Type} [MeasurableSpace α]
    (mx : StateT σ ProbComp α) (Inv : σ → Prop) : Prop :=
  ∀ σ0 σ1, Inv σ0 → Inv σ1 →
    𝒟[mx.run' σ0] = 𝒟[mx.run' σ1]

section Support

variable {m : Type → Type v} [MonadAttach m]

@[simp] lemma statePreserving_pure [Monad m] [LawfulMonad m] [LawfulMonadAttach m]
    {σ α : Type} (a : α) :
    StatePreserving (pure a : StateT σ m α) := by
  intro σ0 z hz
  rw [← LawfulMonadAttach.eq_of_canReturn_pure hz]

lemma statePreserving_bind [Monad m] [LawfulMonad m] [LawfulMonadAttach m]
    {σ α β : Type}
    (mx : StateT σ m α) (my : α → StateT σ m β)
    (h₁ : StatePreserving mx) (h₂ : ∀ a, StatePreserving (my a)) :
    StatePreserving (mx >>= my) := by
  intro σ0 z hz
  rw [StateT.run_bind] at hz
  obtain ⟨us, hus, hcont⟩ := LawfulMonadAttach.canReturn_bind_imp' hz
  rw [h₂ us.1 us.2 z (by simpa using hcont), h₁ σ0 us hus]

lemma preservesInv_of_statePreserving {σ α : Type}
    (mx : StateT σ m α) (Inv : σ → Prop) (h : StatePreserving mx) :
    PreservesInv mx Inv := by
  intro σ0 hσ0 z hz
  simp [h σ0 z hz, hσ0]

lemma preservesInv_bind [Monad m] [LawfulMonad m] [LawfulMonadAttach m]
    {σ α β : Type}
    (mx : StateT σ m α) (my : α → StateT σ m β)
    (Inv : σ → Prop) (h₁ : PreservesInv mx Inv) (h₂ : ∀ a, PreservesInv (my a) Inv) :
    PreservesInv (mx >>= my) Inv := by
  intro σ0 hσ0 z hz
  rw [StateT.run_bind] at hz
  obtain ⟨us, hus, hcont⟩ := LawfulMonadAttach.canReturn_bind_imp' hz
  exact h₂ us.1 us.2 (h₁ σ0 hσ0 us hus) z hcont

lemma preservesInv_pure [Monad m] [LawfulMonad m] [LawfulMonadAttach m]
    {σ α : Type} (a : α) (Inv : σ → Prop) :
    PreservesInv (pure a : StateT σ m α) Inv :=
  preservesInv_of_statePreserving _ _ (statePreserving_pure a)

lemma statePreserving_monadLift [Monad m] [LawfulMonad m] [LawfulMonadAttach m]
    {σ α : Type} (mx : m α) :
    StatePreserving (monadLift mx : StateT σ m α) := by
  intro σ0 z hz
  rw [StateT.run_monadLift] at hz
  obtain ⟨_, _, hz⟩ := LawfulMonadAttach.canReturn_bind_imp' hz
  rw [← LawfulMonadAttach.eq_of_canReturn_pure hz]

lemma preservesInv_monadLift [Monad m] [LawfulMonad m] [LawfulMonadAttach m]
    {σ α : Type} (mx : m α) (Inv : σ → Prop) :
    PreservesInv (monadLift mx : StateT σ m α) Inv :=
  preservesInv_of_statePreserving _ _ (statePreserving_monadLift mx)

lemma preservesInv_map [Monad m] [LawfulMonad m] [LawfulMonadAttach m]
    {σ α β : Type} (f : α → β) {mx : StateT σ m α} {Inv : σ → Prop}
    (h : PreservesInv mx Inv) : PreservesInv (f <$> mx) Inv := by
  intro σ0 hσ0 z hz
  rw [StateT.run_map] at hz
  obtain ⟨y, hy, rfl⟩ := LawfulMonadAttach.canReturn_map_imp' hz
  exact h σ0 hσ0 y hy

/-- Reading the state first: the continuation only has to preserve `Inv` from states that
satisfy it, so a `get`-then-`match` handler is checked branch by branch. -/
lemma preservesInv_get_bind [Monad m] [LawfulMonad m] {σ α : Type}
    {my : σ → StateT σ m α} (Inv : σ → Prop)
    (h : ∀ s, Inv s → PreservesInv (my s) Inv) : PreservesInv (get >>= my) Inv := by
  intro σ0 hσ0 z hz
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hz
  exact h σ0 hσ0 σ0 hσ0 z hz

lemma preservesInv_set_of [Monad m] [LawfulMonad m] [LawfulMonadAttach m]
    {σ : Type} {s' : σ} (Inv : σ → Prop) (h : Inv s') :
    PreservesInv (set s' : StateT σ m PUnit) Inv := by
  intro σ0 _ z hz
  rw [StateT.run_set] at hz
  rw [← LawfulMonadAttach.eq_of_canReturn_pure hz]
  exact h

lemma preservesInv_mapM [Monad m] [LawfulMonad m] [LawfulMonadAttach m]
    {σ α β : Type} {f : α → StateT σ m β} (Inv : σ → Prop)
    (hf : ∀ a, PreservesInv (f a) Inv) (l : List α) : PreservesInv (l.mapM f) Inv := by
  induction l with
  | nil => simpa only [List.mapM_nil] using preservesInv_pure _ Inv
  | cons a l ih =>
    rw [List.mapM_cons]
    exact preservesInv_bind _ _ _ (hf a) fun _ =>
      preservesInv_bind _ _ _ ih fun _ => preservesInv_pure _ Inv

end Support

@[simp] lemma outputIndependent_pure {σ α : Type} [MeasurableSpace α] (Inv : σ → Prop) (a : α) :
    OutputIndependent (pure a : StateT σ ProbComp α) Inv := by
  intro σ0 σ1 _ _
  simp

/-- An invariant-preserving prefix leaves the measure of a subsequent output-independent
computation unchanged. Uniform oracle computations are lossless. -/
lemma outputIndependent_after_preservesInv {σ α β : Type}
    [MeasurableSpace α]
    (mx : StateT σ ProbComp α) (my : StateT σ ProbComp β) (Inv : σ → Prop)
    (hmx : OutputIndependent mx Inv)
    (hmyInv : PreservesInv my Inv) :
    ∀ σ0, Inv σ0 →
      𝒟[(my.run σ0) >>= fun us => mx.run' us.2] = 𝒟[mx.run' σ0] := by
  intro σ0 hσ0
  rw [OracleComp.evalDist_bind_congr_of_support (my.run σ0)
    (fun us => mx.run' us.2) (fun _ => mx.run' σ0)
    (fun us hus => hmx us.2 σ0 (hmyInv σ0 hσ0 us hus) hσ0)]
  exact OracleComp.evalDist_bind_const (my.run σ0) (mx.run' σ0)

end StateT
