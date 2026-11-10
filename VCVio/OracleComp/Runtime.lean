/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.SimSemantics.StateT.StateSeparating
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.EvalDist.Monad.Disagreement.Measure

/-! # Persistent oracle runtimes

A runtime initializes its state once, then interprets surface computations sequentially.
Run results keep each output together with its final state and ordered surface query log.
The carrier does not certify provenance: `OracleRuntime.GeneratedBy` records membership in
an actual runner's support. Import queries made by setup or handlers are not surface queries.
This interface uses small types, as do the sequential query-logging laws.
-/

public section

/-- An explicitly initialized, persistent interpretation of a surface oracle. -/
structure OracleRuntime {ι κ : Type} (Import : OracleSpec ι) (Surface : OracleSpec κ) where
  /-- Private world state retained between completed execution phases. -/
  State : Type
  /-- Initialization, performed once by `run` before interpreting the program. -/
  setup : OracleComp Import State
  /-- Stateful implementation of surface queries using the import interface. -/
  handler : QueryImpl.Stateful Import Surface State

/-- Paired runner output. Construction is controlled by the runtime API; sampling provenance
is a separate support-membership obligation. -/
structure RunResult {ι κ : Type} {Import : OracleSpec ι} {Surface : OracleSpec κ}
    (Γ : OracleRuntime Import Surface) (α : Type) where
  private mk ::
  /-- Returned value of the completed phase. -/
  output : α
  /-- World state after the completed phase. -/
  state : Γ.State
  /-- Ordered surface queries and answers, accumulated across resumed phases. -/
  trace : OracleSpec.QueryLog Surface

/-- Run results agree when all three paired observations agree. -/
@[ext] theorem RunResult.ext {ι κ : Type} {Import : OracleSpec ι}
    {Surface : OracleSpec κ} {Γ : OracleRuntime Import Surface} {α : Type}
    {a b : RunResult Γ α} (output : a.output = b.output)
    (state : a.state = b.state) (trace : a.trace = b.trace) : a = b := by
  cases a
  cases b
  simp_all

namespace OracleRuntime

variable {ι κ : Type} {Import : OracleSpec ι} {Surface : OracleSpec κ}
    (Γ : OracleRuntime Import Surface) {α β : Type}

/-- Run from a supplied state, recording only the surface query/answer sequence. -/
def runFrom (s : Γ.State) (program : OracleComp Surface α) :
    OracleComp Import (RunResult Γ α) :=
  (fun p => RunResult.mk p.1.1 p.2 p.1.2) <$>
    Γ.handler.runState s program.withQueryLog

/-- Initialize once and retain the paired output, final state, and surface log. -/
def run (program : OracleComp Surface α) :
    OracleComp Import (RunResult Γ α) :=
  Γ.setup >>= fun s => Γ.runFrom s program

/-- Continue a completed phase from its final state, retaining the ordered accumulated log. -/
def resume (previous : RunResult Γ α) (next : α → OracleComp Surface β) :
    OracleComp Import (RunResult Γ β) :=
  (fun result => RunResult.mk result.output result.state
    (previous.trace ++ result.trace)) <$> Γ.runFrom previous.state (next previous.output)

/-- Membership in structural runner support, not positive probability for arbitrary specs. -/
def GeneratedBy (program : OracleComp Surface α) (result : RunResult Γ α) : Prop :=
  result ∈ support (Γ.run program)

/-- Public introduction and elimination rule for the otherwise opaque provenance predicate. -/
theorem generatedBy_iff_mem_support (program : OracleComp Surface α)
    (result : RunResult Γ α) :
    Γ.GeneratedBy program result ↔ result ∈ support (Γ.run program) :=
  Iff.rfl

/-- Initialization is performed before the first phase. -/
theorem run_eq (program : OracleComp Surface α) :
    Γ.run program = Γ.setup >>= fun s => Γ.runFrom s program := by
  simp [run]

/-- All observations are extracted together from one logged stateful execution. -/
theorem runFrom_observe (s : Γ.State) (program : OracleComp Surface α) :
    (fun a => (a.output, a.state, a.trace)) <$> Γ.runFrom s program =
      (fun p => (p.1.1, p.2, p.1.2)) <$>
        Γ.handler.runState s program.withQueryLog := by
  simp [runFrom, Functor.map_map]

/-- A pure phase returns its input without changing state or adding queries. -/
@[simp] theorem runFrom_pure (s : Γ.State) (x : α) :
    (fun a => (a.output, a.state, a.trace)) <$> Γ.runFrom s (pure x) =
      pure (x, s, []) := by
  simp [runFrom]

/-- Erasing the surface log retains the ordinary stateful execution. -/
theorem runFrom_eraseTrace (s : Γ.State) (program : OracleComp Surface α) :
    (fun a => (a.output, a.state)) <$> Γ.runFrom s program =
      Γ.handler.runState s program := by
  have erase : Prod.fst <$> program.withQueryLog = program := by
    exact loggingOracle.fst_map_run_simulateQ program
  have h := congrArg (Γ.handler.runState s) erase
  simpa [runFrom, QueryImpl.Stateful.runState, monad_norm] using h

/-- Sequential phases share state and concatenate their logs in execution order. -/
theorem runFrom_bind (s : Γ.State) (program : OracleComp Surface α)
    (next : α → OracleComp Surface β) :
    Γ.runFrom s (program >>= next) = Γ.runFrom s program >>= fun a => Γ.resume a next := by
  simp [runFrom, resume, OracleComp.withQueryLog_bind, QueryImpl.Stateful.runState,
    monad_norm]

/-- Resumption does not repeat setup. -/
theorem run_bind (program : OracleComp Surface α)
    (next : α → OracleComp Surface β) :
    Γ.run (program >>= next) =
      Γ.run program >>= fun a => Γ.resume a next := by
  simp only [run, runFrom_bind, bind_assoc]

/-- A generated result's output and surface log belong to the original logged program's
possible outputs. Stateful interpretation may restrict possible answers, but cannot invent a
surface execution. No probability-spec assumption is required. -/
theorem mem_support_logged_of_generatedBy (program : OracleComp Surface α)
    (result : RunResult Γ α) (generated : Γ.GeneratedBy program result) :
    (result.output, result.trace) ∈ support program.withQueryLog := by
  rw [GeneratedBy, run_eq, mem_support_bind_iff] at generated
  obtain ⟨s, _, reached⟩ := generated
  have observed : (result.output, result.state, result.trace) ∈ support
      ((fun a : RunResult Γ α => (a.output, a.state, a.trace)) <$> Γ.runFrom s program) := by
    rw [support_map]
    exact Set.mem_image_of_mem _ reached
  rw [runFrom_observe, support_map] at observed
  obtain ⟨⟨⟨out, trace⟩, finalState⟩, hrun, heq⟩ := observed
  have hlogged : (out, trace) ∈ support program.withQueryLog := by
    apply OracleComp.support_simulateQ_run'_subset Γ.handler program.withQueryLog s
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst hrun
  have same : (out, trace) = (result.output, result.trace) := by
    simpa only [Prod.mk.injEq] using congrArg (fun p => (p.1, p.2.2)) heq
  exact same ▸ hlogged

section successBounds

open MeasureTheory
open scoped ENNReal

variable {X : Type} [EvalDistSemantics (OracleComp Import)]
  [LawfulEvalDistSemantics (OracleComp Import)]

/-- Average actual resumed success over the joint prefix result. The fixed continuation
receives only the returned value; the runtime retains state and history internally. Analytic
exceptional and error predicates may inspect the full joint result. No independence or
normalization is assumed. -/
theorem run_bind_success_le (first : OracleComp Surface α) (next : α → OracleComp Surface X)
    (Exceptional : RunResult Γ α → Prop) (Success : X → Prop)
    (error : RunResult Γ α → ENNReal)
    (hsuffix : letI : MeasurableSpace (RunResult Γ α) := ⊤
      (∫⁻ b in {b | ¬ Exceptional b},
        Pr{let result ← Γ.resume b next}[Success result.output] ∂𝒟[Γ.run first]) ≤
      ∫⁻ b in {b | ¬ Exceptional b}, error b ∂𝒟[Γ.run first]) :
    let : MeasurableSpace (RunResult Γ α) := ⊤
    Pr{let result ← Γ.run (first >>= next)}[Success result.output] ≤
      Pr{let b ← Γ.run first}[Exceptional b] +
        ∫⁻ b in {b | ¬ Exceptional b}, error b ∂𝒟[Γ.run first] := by
  let : MeasurableSpace (RunResult Γ α) := ⊤
  rw [Γ.run_bind]
  exact (prEvent_bind_le_prEvent_add_lintegral_ae (Γ.run first)
    (fun b => Γ.resume b next) Exceptional (fun result => Success result.output)
    (fun b => Pr{let result ← Γ.resume b next}[Success result.output])
    (Filter.Eventually.of_forall (fun _ _ => le_rfl))).trans (add_le_add le_rfl hsuffix)

/-- A stronger pointwise almost-everywhere premise implies the joint average bound. -/
theorem run_bind_success_le_ae (first : OracleComp Surface α) (next : α → OracleComp Surface X)
    (Exceptional : RunResult Γ α → Prop) (Success : X → Prop)
    (error : RunResult Γ α → ENNReal)
    (hsuffix : letI : MeasurableSpace (RunResult Γ α) := ⊤
      ∀ᵐ b ∂𝒟[Γ.run first], ¬ Exceptional b →
        Pr{let result ← Γ.resume b next}[Success result.output] ≤ error b) :
    let : MeasurableSpace (RunResult Γ α) := ⊤
    Pr{let result ← Γ.run (first >>= next)}[Success result.output] ≤
      Pr{let b ← Γ.run first}[Exceptional b] +
        ∫⁻ b in {b | ¬ Exceptional b}, error b ∂𝒟[Γ.run first] := by
  let : MeasurableSpace (RunResult Γ α) := ⊤
  rw [Γ.run_bind]
  exact prEvent_bind_le_prEvent_add_lintegral_ae (Γ.run first)
    (fun b => Γ.resume b next) Exceptional (fun result => Success result.output) error hsuffix

/-- A uniform actual-resume bound yields a uniform error term, even with missing mass. -/
theorem run_bind_success_le_uniform (first : OracleComp Surface α)
    (next : α → OracleComp Surface X)
    (Exceptional : RunResult Γ α → Prop) (Success : X → Prop) (error : ENNReal)
    (hsuffix : letI : MeasurableSpace (RunResult Γ α) := ⊤
      ∀ᵐ b ∂𝒟[Γ.run first], ¬ Exceptional b →
        Pr{let result ← Γ.resume b next}[Success result.output] ≤ error) :
    Pr{let result ← Γ.run (first >>= next)}[Success result.output] ≤
      Pr{let b ← Γ.run first}[Exceptional b] + error := by
  let : MeasurableSpace (RunResult Γ α) := ⊤
  apply (Γ.run_bind_success_le_ae first next Exceptional Success (fun _ => error)
    hsuffix).trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∫⁻ _, error ∂𝒟[Γ.run first] := by
      simpa only [Measure.restrict_univ] using
        (lintegral_mono_set (f := fun _ => error)
          (μ := 𝒟[Γ.run first]) (Set.subset_univ {b | ¬ Exceptional b}))
    _ = error * 𝒟[Γ.run first] Set.univ := lintegral_const error
    _ ≤ error := mul_le_of_le_one_right' (evalDist_apply_univ_le_one (Γ.run first))

end successBounds

end OracleRuntime
