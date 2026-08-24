/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.Asymptotics.RankedRun

/-!
# Finite-workload regressions for ranked resource certificates

These checks use genuine free oracle programs and explicit-state realizations. Backend code and its
costs remain explicit parameters: the tests exercise the generic semantic and resource APIs without
assigning artificial costs to unimplemented functions.
-/

@[expose] public section

namespace OracleComp.Complexity.RankedRunTest

open PFunctor
open PFunctor.DynSystem
open PFunctor.DynSystem.DynComputation

#check RankedRun.ResourcePotentialCertificate
#check RankedRun.ResourcePotentialCertificate.runsWithinUnder
#check RankedPPTCertificate
#check RankedPPTCertificate.isOraclePPTBy

/-! ## Two fair coins and XOR -/

inductive TwoCoinState where
  | first
  | second (first : Bool)
  | done (result : Bool)

def twoCoinView : TwoCoinState → Bool ⊕ coinSpec.toPFunctor.Obj TwoCoinState
  | .first => Sum.inr ⟨(), fun answer ↦ .second answer⟩
  | .second first => Sum.inr ⟨(), fun answer ↦ .done (Bool.xor first answer)⟩
  | .done result => Sum.inl result

def twoCoinMachine : DynComputation coinSpec.toPFunctor Unit Bool where
  State := TwoCoinState
  toDynSystem :=
    (fun state ↦ (Resumption.pack (twoCoinView state)).1) ⇆
      fun state ↦ (Resumption.pack (twoCoinView state)).2
  init := fun _ ↦ .first

@[simp]
theorem twoCoinMachine_init (input : Unit) : twoCoinMachine.init input = .first :=
  rfl

@[simp]
theorem twoCoinMachine_view_first : twoCoinMachine.view .first =
    Sum.inr ⟨(), fun answer ↦ .second answer⟩ := by
  change Resumption.unpack (Resumption.pack (twoCoinView .first)) = _
  exact Resumption.unpack_pack _

@[simp]
theorem twoCoinMachine_view_second (first : Bool) : twoCoinMachine.view (.second first) =
    Sum.inr ⟨(), fun answer ↦ .done (Bool.xor first answer)⟩ := by
  change Resumption.unpack (Resumption.pack (twoCoinView (.second first))) = _
  exact Resumption.unpack_pack _

@[simp]
theorem twoCoinMachine_view_done (result : Bool) : twoCoinMachine.view (.done result) =
    Sum.inl result := by
  change Resumption.unpack (Resumption.pack (twoCoinView (.done result))) = _
  exact Resumption.unpack_pack _

def twoCoinProgram (_ : Unit) : FreeM coinSpec.toPFunctor Bool :=
  FreeM.liftBind () fun first ↦
    FreeM.liftBind () fun second ↦ FreeM.pure (Bool.xor first second)

inductive TwoCoinResidual : TwoCoinState → FreeM coinSpec.toPFunctor Bool → Prop where
  | first : TwoCoinResidual .first (twoCoinProgram ())
  | second (first : Bool) : TwoCoinResidual (.second first)
      (FreeM.liftBind () fun second ↦ FreeM.pure (Bool.xor first second))
  | done (result : Bool) : TwoCoinResidual (.done result) (FreeM.pure result)

theorem twoCoinSimulation : IsSimulation twoCoinMachine.toDynSystem
    (DynComputation.ofFreeM twoCoinProgram).toDynSystem TwoCoinResidual where
  expose_eq := by
    intro state residual related
    cases related <;> rfl
  update_rel := by
    intro state residual related direction
    cases related with
    | first => exact TwoCoinResidual.second direction
    | second first => exact TwoCoinResidual.done (Bool.xor first direction)
    | done result => exact PEmpty.elim direction

theorem twoCoinMachine_implements : twoCoinMachine.Implements twoCoinProgram := by
  apply implements_of_isSimulation twoCoinMachine twoCoinProgram TwoCoinResidual twoCoinSimulation
  intro input
  cases input
  exact TwoCoinResidual.first

def twoCoinRemaining : TwoCoinState → ℕ
  | .first => 2
  | .second _ => 1
  | .done _ => 0

/-! ## Adaptive one-or-two-query program -/

inductive AdaptiveState where
  | first
  | second
  | done (result : Bool)

def adaptiveView : AdaptiveState → Bool ⊕ coinSpec.toPFunctor.Obj AdaptiveState
  | .first => Sum.inr ⟨(), fun answer ↦ if answer then .second else .done false⟩
  | .second => Sum.inr ⟨(), fun answer ↦ .done answer⟩
  | .done result => Sum.inl result

def adaptiveMachine : DynComputation coinSpec.toPFunctor Unit Bool where
  State := AdaptiveState
  toDynSystem :=
    (fun state ↦ (Resumption.pack (adaptiveView state)).1) ⇆
      fun state ↦ (Resumption.pack (adaptiveView state)).2
  init := fun _ ↦ .first

@[simp]
theorem adaptiveMachine_init (input : Unit) : adaptiveMachine.init input = .first :=
  rfl

@[simp]
theorem adaptiveMachine_view_first : adaptiveMachine.view .first =
    Sum.inr ⟨(), fun answer ↦ if answer then .second else .done false⟩ := by
  change Resumption.unpack (Resumption.pack (adaptiveView .first)) = _
  exact Resumption.unpack_pack _

@[simp]
theorem adaptiveMachine_view_second : adaptiveMachine.view .second =
    Sum.inr ⟨(), fun answer ↦ .done answer⟩ := by
  change Resumption.unpack (Resumption.pack (adaptiveView .second)) = _
  exact Resumption.unpack_pack _

@[simp]
theorem adaptiveMachine_view_done (result : Bool) : adaptiveMachine.view (.done result) =
    Sum.inl result := by
  change Resumption.unpack (Resumption.pack (adaptiveView (.done result))) = _
  exact Resumption.unpack_pack _

def adaptiveProgram (_ : Unit) : FreeM coinSpec.toPFunctor Bool :=
  FreeM.liftBind () fun first ↦
    if first then FreeM.liftBind () fun second ↦ FreeM.pure second else FreeM.pure false

inductive AdaptiveResidual : AdaptiveState → FreeM coinSpec.toPFunctor Bool → Prop where
  | first : AdaptiveResidual .first (adaptiveProgram ())
  | second : AdaptiveResidual .second (FreeM.liftBind () fun answer ↦ FreeM.pure answer)
  | done (result : Bool) : AdaptiveResidual (.done result) (FreeM.pure result)

theorem adaptiveSimulation : IsSimulation adaptiveMachine.toDynSystem
    (DynComputation.ofFreeM adaptiveProgram).toDynSystem AdaptiveResidual where
  expose_eq := by
    intro state residual related
    cases related <;> rfl
  update_rel := by
    intro state residual related direction
    cases related with
    | first =>
        cases direction
        · exact AdaptiveResidual.done false
        · exact AdaptiveResidual.second
    | second => exact AdaptiveResidual.done direction
    | done result => exact PEmpty.elim direction

theorem adaptiveMachine_implements : adaptiveMachine.Implements adaptiveProgram := by
  apply implements_of_isSimulation adaptiveMachine adaptiveProgram AdaptiveResidual
    adaptiveSimulation
  intro input
  cases input
  exact AdaptiveResidual.first

def adaptiveRemaining : AdaptiveState → ℕ
  | .first => 2
  | .second => 1
  | .done _ => 0

/-! ## Uniform `n`-coin parity -/

/-- The free fair-coin loop with an explicit remaining-query counter and parity accumulator. -/
def parityFrom : ℕ → Bool → FreeM coinSpec.toPFunctor Bool
  | 0, parity => FreeM.pure parity
  | remaining + 1, parity =>
      FreeM.liftBind () fun answer ↦ parityFrom remaining (Bool.xor parity answer)

def parityProgram (queries : ℕ) : FreeM coinSpec.toPFunctor Bool :=
  parityFrom queries false

def parityView : (ℕ × Bool) → Bool ⊕ coinSpec.toPFunctor.Obj (ℕ × Bool)
  | (0, parity) => Sum.inl parity
  | (remaining + 1, parity) =>
      Sum.inr ⟨(), fun answer ↦ (remaining, Bool.xor parity answer)⟩

/-- One fixed machine handles the whole input-indexed family, rather than selecting a machine for
each query bound. -/
def parityMachine : DynComputation coinSpec.toPFunctor ℕ Bool where
  State := ℕ × Bool
  toDynSystem :=
    (fun state ↦ (Resumption.pack (parityView state)).1) ⇆
      fun state ↦ (Resumption.pack (parityView state)).2
  init := fun queries ↦ (queries, false)

@[simp]
theorem parityMachine_init (queries : ℕ) : parityMachine.init queries = (queries, false) :=
  rfl

@[simp]
theorem parityMachine_view_zero (parity : Bool) : parityMachine.view (0, parity) =
    Sum.inl parity := by
  change Resumption.unpack (Resumption.pack (parityView (0, parity))) = _
  exact Resumption.unpack_pack _

@[simp]
theorem parityMachine_view_succ (remaining : ℕ) (parity : Bool) :
    parityMachine.view (remaining + 1, parity) =
      Sum.inr ⟨(), fun answer ↦ (remaining, Bool.xor parity answer)⟩ := by
  change Resumption.unpack (Resumption.pack (parityView (remaining + 1, parity))) = _
  exact Resumption.unpack_pack _

def ParityResidual (state : ℕ × Bool) (residual : FreeM coinSpec.toPFunctor Bool) : Prop :=
  residual = parityFrom state.1 state.2

theorem paritySimulation : IsSimulation parityMachine.toDynSystem
    (DynComputation.ofFreeM parityProgram).toDynSystem ParityResidual where
  expose_eq := by
    intro state residual related
    rcases state with ⟨remaining, parity⟩
    cases related
    cases remaining <;> rfl
  update_rel := by
    intro state residual related direction
    rcases state with ⟨remaining, parity⟩
    cases related
    cases remaining with
    | zero => exact PEmpty.elim direction
    | succ remaining => rfl

theorem parityMachine_implements : parityMachine.Implements parityProgram := by
  apply implements_of_isSimulation parityMachine parityProgram ParityResidual paritySimulation
  intro queries
  rfl

def parityRemaining (state : ℕ × Bool) : ℕ :=
  state.1

/-! ## Honest quantitative packaging -/

section Quantitative

variable {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass C}
  {bd : Boundary C coinSpec.toPFunctor Unit Bool}

/-- Package explicit backend code for the two-coin state machine. -/
def twoCoinRealization (state : C.Str TwoCoinState)
    (initCode : Q.Realizer bd.input state twoCoinMachine.init)
    (headCode : Q.Realizer state bd.head twoCoinMachine.head)
    (updateCode : Q.Realizer (bd.stateIdx state) (StepClass.HasOption.option state)
      twoCoinMachine.update?) : QuantitativeRealization Q bd where
  machine := twoCoinMachine
  state := state
  initCode := initCode
  headCode := headCode
  updateCode := updateCode

/-- Package explicit backend code for the adaptive one-or-two-query state machine. -/
def adaptiveRealization (state : C.Str AdaptiveState)
    (initCode : Q.Realizer bd.input state adaptiveMachine.init)
    (headCode : Q.Realizer state bd.head adaptiveMachine.head)
    (updateCode : Q.Realizer (bd.stateIdx state) (StepClass.HasOption.option state)
      adaptiveMachine.update?) : QuantitativeRealization Q bd where
  machine := adaptiveMachine
  state := state
  initCode := initCode
  headCode := headCode
  updateCode := updateCode

/-- Package explicit backend code for the uniform `n`-coin parity machine. -/
def parityRealization {parityBd : Boundary C coinSpec.toPFunctor ℕ Bool}
    (state : C.Str (ℕ × Bool))
    (initCode : Q.Realizer parityBd.input state parityMachine.init)
    (headCode : Q.Realizer state parityBd.head parityMachine.head)
    (updateCode : Q.Realizer (parityBd.stateIdx state) (StepClass.HasOption.option state)
      parityMachine.update?) : QuantitativeRealization Q parityBd where
  machine := parityMachine
  state := state
  initCode := initCode
  headCode := headCode
  updateCode := updateCode

theorem twoCoinRemaining_lt_of_view_query
    {state : TwoCoinState} {position : coinSpec.Domain}
    {next : coinSpec.Range position → TwoCoinState}
    (view_eq : twoCoinMachine.view state = Sum.inr ⟨position, next⟩)
    (direction : coinSpec.Range position) :
    twoCoinRemaining (next direction) < twoCoinRemaining state := by
  cases state with
  | first =>
      rw [twoCoinMachine_view_first] at view_eq
      have query_eq := Sum.inr.inj view_eq
      cases position
      have next_eq : (fun answer : Bool ↦ TwoCoinState.second answer) = next :=
        eq_of_heq (Sigma.ext_iff.mp query_eq).2
      cases next_eq
      change 1 < 2
      decide
  | second first =>
      rw [twoCoinMachine_view_second] at view_eq
      have query_eq := Sum.inr.inj view_eq
      cases position
      have next_eq :
          (fun answer : Bool ↦ TwoCoinState.done (Bool.xor first answer)) = next :=
        eq_of_heq (Sigma.ext_iff.mp query_eq).2
      cases next_eq
      change 0 < 1
      decide
  | done result =>
      rw [twoCoinMachine_view_done] at view_eq
      exact nomatch view_eq

theorem adaptiveRemaining_lt_of_view_query
    {state : AdaptiveState} {position : coinSpec.Domain}
    {next : coinSpec.Range position → AdaptiveState}
    (view_eq : adaptiveMachine.view state = Sum.inr ⟨position, next⟩)
    (direction : coinSpec.Range position) :
    adaptiveRemaining (next direction) < adaptiveRemaining state := by
  cases state with
  | first =>
      rw [adaptiveMachine_view_first] at view_eq
      have query_eq := Sum.inr.inj view_eq
      cases position
      have next_eq :
          (fun answer : Bool ↦ if answer then AdaptiveState.second else .done false) = next :=
        eq_of_heq (Sigma.ext_iff.mp query_eq).2
      cases next_eq
      cases direction
      · change 0 < 2
        decide
      · change 1 < 2
        decide
  | second =>
      rw [adaptiveMachine_view_second] at view_eq
      have query_eq := Sum.inr.inj view_eq
      cases position
      have next_eq : (fun answer : Bool ↦ AdaptiveState.done answer) = next :=
        eq_of_heq (Sigma.ext_iff.mp query_eq).2
      cases next_eq
      change 0 < 1
      decide
  | done result =>
      rw [adaptiveMachine_view_done] at view_eq
      exact nomatch view_eq

theorem parityRemaining_lt_of_view_query
    {machineState : ℕ × Bool} {position : coinSpec.Domain}
    {next : coinSpec.Range position → ℕ × Bool}
    (view_eq : parityMachine.view machineState = Sum.inr ⟨position, next⟩)
    (direction : coinSpec.Range position) :
    parityRemaining (next direction) < parityRemaining machineState := by
  rcases machineState with ⟨remaining, parity⟩
  cases remaining with
  | zero =>
      rw [parityMachine_view_zero] at view_eq
      exact nomatch view_eq
  | succ remaining =>
      rw [parityMachine_view_succ] at view_eq
      have query_eq := Sum.inr.inj view_eq
      cases position
      have next_eq :
          (fun answer : Bool ↦ (remaining, Bool.xor parity answer)) = next :=
        eq_of_heq (Sigma.ext_iff.mp query_eq).2
      cases next_eq
      change remaining < remaining + 1
      omega

/-- The reusable ranked constructor for two fair-coin queries.

Every resource inequality mentions the actual packaged realization. In particular, the two local
query hypotheses charge both enabled transitions and their encoded boundary traffic. -/
def twoCoinResourcePotentialCertificate
    (state : C.Str TwoCoinState)
    (initCode : Q.Realizer bd.input state twoCoinMachine.init)
    (headCode : Q.Realizer state bd.head twoCoinMachine.head)
    (updateCode : Q.Realizer (bd.stateIdx state) (StepClass.HasOption.option state)
      twoCoinMachine.update?)
    (potential : TwoCoinState → ExecutionCost) (bound : ExecutionCost)
    (terminal_le : ∀ machineState,
      RankedRun.terminalCost (twoCoinRealization state initCode headCode updateCode) machineState ≤
        potential machineState)
    (first_le : ∀ answer,
      RankedRun.queryStepCost (twoCoinRealization state initCode headCode updateCode)
          .first () answer + potential (.second answer) ≤ potential .first)
    (second_le : ∀ first answer,
      RankedRun.queryStepCost (twoCoinRealization state initCode headCode updateCode)
          (.second first) () answer + potential (.done (Bool.xor first answer)) ≤
        potential (.second first))
    (init_le : ExecutionCost.ofWork (Q.cost initCode ()) + potential .first ≤ bound)
    (queries_le : 2 ≤ bound.queries) :
    RankedRun.ResourcePotentialCertificate (twoCoinRealization state initCode headCode updateCode)
      (fun _ _ ↦ True) (fun _ ↦ bound) where
  toRankedRunCertificate := {
    rank := twoCoinRemaining
    returns_of_rank_zero := by
      intro machineState rank_eq
      cases machineState with
      | first => simp [twoCoinRemaining] at rank_eq
      | second first => simp [twoCoinRemaining] at rank_eq
      | done result => exact ⟨result, twoCoinMachine_view_done result⟩
    decreases := by
      intro machineState position next view_eq direction _
      change twoCoinMachine.view machineState = Sum.inr ⟨position, next⟩ at view_eq
      exact twoCoinRemaining_lt_of_view_query view_eq direction
    progress := by
      intro machineState position next view_eq
      exact ⟨false, trivial⟩ }
  potential := potential
  terminal_le := terminal_le
  query_le := by
    intro machineState position next view_eq direction _
    change twoCoinMachine.view machineState = Sum.inr ⟨position, next⟩ at view_eq
    cases machineState with
    | first =>
        rw [twoCoinMachine_view_first] at view_eq
        have query_eq := Sum.inr.inj view_eq
        cases position
        have next_eq : (fun answer : Bool ↦ TwoCoinState.second answer) = next :=
          eq_of_heq (Sigma.ext_iff.mp query_eq).2
        cases next_eq
        exact first_le direction
    | second first =>
        rw [twoCoinMachine_view_second] at view_eq
        have query_eq := Sum.inr.inj view_eq
        cases position
        have next_eq :
            (fun answer : Bool ↦ TwoCoinState.done (Bool.xor first answer)) = next :=
          eq_of_heq (Sigma.ext_iff.mp query_eq).2
        cases next_eq
        exact second_le first direction
    | done result =>
        rw [twoCoinMachine_view_done] at view_eq
        exact nomatch view_eq
  init_le := by
    intro input
    cases input
    exact init_le
  rank_init_le := by
    intro input
    cases input
    exact queries_le

/-- The reusable ranked constructor for the adaptive one-or-two-query workload. -/
def adaptiveResourcePotentialCertificate
    (state : C.Str AdaptiveState)
    (initCode : Q.Realizer bd.input state adaptiveMachine.init)
    (headCode : Q.Realizer state bd.head adaptiveMachine.head)
    (updateCode : Q.Realizer (bd.stateIdx state) (StepClass.HasOption.option state)
      adaptiveMachine.update?)
    (potential : AdaptiveState → ExecutionCost) (bound : ExecutionCost)
    (terminal_le : ∀ machineState,
      RankedRun.terminalCost (adaptiveRealization state initCode headCode updateCode) machineState ≤
        potential machineState)
    (first_false_le :
      RankedRun.queryStepCost (adaptiveRealization state initCode headCode updateCode)
          .first () false + potential (.done false) ≤ potential .first)
    (first_true_le :
      RankedRun.queryStepCost (adaptiveRealization state initCode headCode updateCode)
          .first () true + potential .second ≤ potential .first)
    (second_le : ∀ answer,
      RankedRun.queryStepCost (adaptiveRealization state initCode headCode updateCode)
          .second () answer + potential (.done answer) ≤ potential .second)
    (init_le : ExecutionCost.ofWork (Q.cost initCode ()) + potential .first ≤ bound)
    (queries_le : 2 ≤ bound.queries) :
    RankedRun.ResourcePotentialCertificate (adaptiveRealization state initCode headCode updateCode)
      (fun _ _ ↦ True) (fun _ ↦ bound) where
  toRankedRunCertificate := {
    rank := adaptiveRemaining
    returns_of_rank_zero := by
      intro machineState rank_eq
      cases machineState with
      | first => simp [adaptiveRemaining] at rank_eq
      | second => simp [adaptiveRemaining] at rank_eq
      | done result => exact ⟨result, adaptiveMachine_view_done result⟩
    decreases := by
      intro machineState position next view_eq direction _
      change adaptiveMachine.view machineState = Sum.inr ⟨position, next⟩ at view_eq
      exact adaptiveRemaining_lt_of_view_query view_eq direction
    progress := by
      intro machineState position next view_eq
      exact ⟨false, trivial⟩ }
  potential := potential
  terminal_le := terminal_le
  query_le := by
    intro machineState position next view_eq direction _
    change adaptiveMachine.view machineState = Sum.inr ⟨position, next⟩ at view_eq
    cases machineState with
    | first =>
        rw [adaptiveMachine_view_first] at view_eq
        have query_eq := Sum.inr.inj view_eq
        cases position
        have next_eq :
            (fun answer : Bool ↦ if answer then AdaptiveState.second else .done false) = next :=
          eq_of_heq (Sigma.ext_iff.mp query_eq).2
        cases next_eq
        cases direction
        · exact first_false_le
        · exact first_true_le
    | second =>
        rw [adaptiveMachine_view_second] at view_eq
        have query_eq := Sum.inr.inj view_eq
        cases position
        have next_eq : (fun answer : Bool ↦ AdaptiveState.done answer) = next :=
          eq_of_heq (Sigma.ext_iff.mp query_eq).2
        cases next_eq
        exact second_le direction
    | done result =>
        rw [adaptiveMachine_view_done] at view_eq
        exact nomatch view_eq
  init_le := by
    intro input
    cases input
    exact init_le
  rank_init_le := by
    intro input
    cases input
    exact queries_le

/-- A nonconstant-bound regression: one realization handles every `n`, and the visible-query
component of the input-indexed bound must dominate `n` itself. -/
def parityResourcePotentialCertificate
    {bd : Boundary C coinSpec.toPFunctor ℕ Bool}
    (state : C.Str (ℕ × Bool))
    (initCode : Q.Realizer bd.input state parityMachine.init)
    (headCode : Q.Realizer state bd.head parityMachine.head)
    (updateCode : Q.Realizer (bd.stateIdx state) (StepClass.HasOption.option state)
      parityMachine.update?)
    (potential : (ℕ × Bool) → ExecutionCost) (bound : ℕ → ExecutionCost)
    (terminal_le : ∀ machineState,
      RankedRun.terminalCost (parityRealization state initCode headCode updateCode) machineState ≤
        potential machineState)
    (query_le : ∀ remaining parity answer,
      RankedRun.queryStepCost (parityRealization state initCode headCode updateCode)
          (remaining + 1, parity) () answer +
        potential (remaining, Bool.xor parity answer) ≤
          potential (remaining + 1, parity))
    (init_le : ∀ queries,
      ExecutionCost.ofWork (Q.cost initCode queries) + potential (queries, false) ≤ bound queries)
    (queries_le : ∀ queries, queries ≤ (bound queries).queries) :
    RankedRun.ResourcePotentialCertificate (parityRealization state initCode headCode updateCode)
      (fun _ _ ↦ True) bound where
  toRankedRunCertificate := {
    rank := parityRemaining
    returns_of_rank_zero := by
      intro machineState rank_eq
      rcases machineState with ⟨remaining, parity⟩
      cases remaining with
      | zero => exact ⟨parity, parityMachine_view_zero parity⟩
      | succ remaining => simp [parityRemaining] at rank_eq
    decreases := by
      intro machineState position next view_eq direction _
      change parityMachine.view machineState = Sum.inr ⟨position, next⟩ at view_eq
      exact parityRemaining_lt_of_view_query view_eq direction
    progress := by
      intro machineState position next view_eq
      exact ⟨false, trivial⟩ }
  potential := potential
  terminal_le := terminal_le
  query_le := by
    intro machineState position next view_eq direction _
    change parityMachine.view machineState = Sum.inr ⟨position, next⟩ at view_eq
    rcases machineState with ⟨remaining, parity⟩
    cases remaining with
    | zero =>
        rw [parityMachine_view_zero] at view_eq
        exact nomatch view_eq
    | succ remaining =>
        rw [parityMachine_view_succ] at view_eq
        have query_eq := Sum.inr.inj view_eq
        cases position
        have next_eq :
            (fun answer : Bool ↦ (remaining, Bool.xor parity answer)) = next :=
          eq_of_heq (Sigma.ext_iff.mp query_eq).2
        cases next_eq
        exact query_le remaining parity direction
  init_le := init_le
  rank_init_le := queries_le

end Quantitative

end OracleComp.Complexity.RankedRunTest
