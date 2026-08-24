/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Coinductive.SecurityFamily
public import PolyFun.Complexity.SecondOrderPolynomial
public import PolyFun.Realizability.Quantitative
public import PolyFun.Realizability.Quantitative.Polynomial

/-!
# Strict polynomial time for syntactic oracle computations

This file gives VCVio's backend-relative, worst-case notion of polynomial time. It combines four
pieces which remain explicit in every statement:

1. one `DynComputation` implementing the whole input family;
2. Type-valued executable evidence for its `init`, `head`, and enabled `update?` maps;
3. exact resource accounting for every finite, typed query-answer prefix; and
4. second-order polynomial bounds in the encoded input size and oracle response-length functions.

The generic definition is deliberately named `IsOraclePPTBy`: a `QuantitativeStepClass` supplies an
operational backend, but only a backend-specific adequacy theorem can identify that cost with a
standard machine model. VCVio does not turn an arbitrary cost annotation into an unqualified
claim of PPT.

Random sampling is just another syntactic oracle interaction. Consequently the strict predicate
quantifies over every contract-conforming answer branch, including every coin outcome and branches
having probability zero under a later semantics. Expected polynomial time is a different
probabilistic notion and is not smuggled into this pathwise definition.
-/

@[expose] public section

universe u v w x y

namespace OracleComp.Complexity

open PFunctor
open PFunctor.DynSystem.DynComputation

/-! ## Open resource polynomials -/

/-- A second-order polynomial upper bound for every tracked execution resource. -/
structure ResourcePolynomial (label : Type x) where
  /-- Backend-relative local work. -/
  work : _root_.Complexity.SecondOrderPolynomial label
  /-- Number of visible oracle queries. -/
  queries : _root_.Complexity.SecondOrderPolynomial label
  /-- Total encoded query-answer traffic. -/
  traffic : _root_.Complexity.SecondOrderPolynomial label
  /-- Peak encoded hidden-state size. -/
  peakStateSize : _root_.Complexity.SecondOrderPolynomial label
  /-- Peak encoded one-step readout size. -/
  peakHeadSize : _root_.Complexity.SecondOrderPolynomial label
  deriving DecidableEq, Repr

namespace ResourcePolynomial

variable {label : Type x}

/-- Regard an ordinary first-order polynomial as a second-order polynomial which does not inspect
its oracle-length environment. -/
def ofFirstOrder (bound : _root_.Complexity.FirstOrderPolynomial) :
    _root_.Complexity.SecondOrderPolynomial label :=
  bound.reindex PEmpty.elim

@[simp]
theorem eval_ofFirstOrder (bound : _root_.Complexity.FirstOrderPolynomial)
    (length : label → ℕ → ℕ) (inputSize : ℕ) :
    (ofFirstOrder bound : _root_.Complexity.SecondOrderPolynomial label).eval length inputSize =
      bound.eval inputSize := by
  unfold ofFirstOrder
  rw [_root_.Complexity.SecondOrderPolynomial.eval_reindex]
  change _ = _root_.Complexity.SecondOrderPolynomial.eval PEmpty.elim inputSize bound
  congr 1
  funext interface
  exact interface.elim

/-- Evaluate every resource component at an input size and oracle length environment. -/
def eval (bound : ResourcePolynomial label) (length : label → ℕ → ℕ)
    (inputSize : ℕ) : ExecutionCost where
  work := bound.work.eval length inputSize
  queries := bound.queries.eval length inputSize
  traffic := bound.traffic.eval length inputSize
  peakStateSize := bound.peakStateSize.eval length inputSize
  peakHeadSize := bound.peakHeadSize.eval length inputSize

/-- A constant resource bound. -/
def const (cost : ExecutionCost) : ResourcePolynomial label where
  work := .const cost.work
  queries := .const cost.queries
  traffic := .const cost.traffic
  peakStateSize := .const cost.peakStateSize
  peakHeadSize := .const cost.peakHeadSize

/-- A conservative sequential sum of two resource bounds.

The three additive components add exactly. Peak components also use polynomial addition, which
upper-bounds the `max` used by `ExecutionCost`. -/
def add (left right : ResourcePolynomial label) : ResourcePolynomial label where
  work := .add left.work right.work
  queries := .add left.queries right.queries
  traffic := .add left.traffic right.traffic
  peakStateSize := .add left.peakStateSize right.peakStateSize
  peakHeadSize := .add left.peakHeadSize right.peakHeadSize

instance : Add (ResourcePolynomial label) := ⟨add⟩

/-- Replace the base input-size variable in every resource component. -/
def comp (bound : ResourcePolynomial label)
    (inputBound : _root_.Complexity.SecondOrderPolynomial label) :
    ResourcePolynomial label where
  work := bound.work.comp inputBound
  queries := bound.queries.comp inputBound
  traffic := bound.traffic.comp inputBound
  peakStateSize := bound.peakStateSize.comp inputBound
  peakHeadSize := bound.peakHeadSize.comp inputBound

/-- Relabel every oracle-resource symbol in a resource bound. -/
def reindex {target : Type y} (bound : ResourcePolynomial label) (map : label → target) :
    ResourcePolynomial target where
  work := bound.work.reindex map
  queries := bound.queries.reindex map
  traffic := bound.traffic.reindex map
  peakStateSize := bound.peakStateSize.reindex map
  peakHeadSize := bound.peakHeadSize.reindex map

/-- Substitute a second-order resource transformer for every oracle-resource symbol. -/
def subst {target : Type y} (bound : ResourcePolynomial label)
    (replacement : label → _root_.Complexity.SecondOrderPolynomial target) :
    ResourcePolynomial target where
  work := bound.work.subst replacement
  queries := bound.queries.subst replacement
  traffic := bound.traffic.subst replacement
  peakStateSize := bound.peakStateSize.subst replacement
  peakHeadSize := bound.peakHeadSize.subst replacement

@[simp]
theorem eval_const (cost : ExecutionCost) (length : label → ℕ → ℕ) (inputSize : ℕ) :
    (const cost : ResourcePolynomial label).eval length inputSize = cost :=
  rfl

@[simp]
theorem eval_comp (bound : ResourcePolynomial label)
    (inputBound : _root_.Complexity.SecondOrderPolynomial label)
    (length : label → ℕ → ℕ) (inputSize : ℕ) :
    (bound.comp inputBound).eval length inputSize =
      bound.eval length (inputBound.eval length inputSize) := by
  ext <;> simp [eval, comp]

@[simp]
theorem eval_reindex {target : Type y} (bound : ResourcePolynomial label)
    (map : label → target) (length : target → ℕ → ℕ) (inputSize : ℕ) :
    (bound.reindex map).eval length inputSize =
      bound.eval (fun symbol ↦ length (map symbol)) inputSize := by
  ext <;> simp [eval, reindex]

@[simp]
theorem eval_subst {target : Type y} (bound : ResourcePolynomial label)
    (replacement : label → _root_.Complexity.SecondOrderPolynomial target)
    (length : target → ℕ → ℕ) (inputSize : ℕ) :
    (bound.subst replacement).eval length inputSize =
      bound.eval (fun symbol size ↦ (replacement symbol).eval length size) inputSize := by
  ext <;> simp [eval, subst]

/-- Sequentially accumulated costs fit the conservative polynomial sum. -/
theorem add_eval_le_eval_add (left right : ResourcePolynomial label)
    (length : label → ℕ → ℕ) (inputSize : ℕ) :
    left.eval length inputSize + right.eval length inputSize ≤
      (left + right).eval length inputSize := by
  rw [ExecutionCost.le_iff]
  exact ⟨le_rfl, le_rfl, le_rfl, max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _),
    max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)⟩

/-- Resource-bound evaluation is monotone in encoded input size. -/
theorem eval_mono_input (bound : ResourcePolynomial label) {length : label → ℕ → ℕ}
    (hLength : _root_.Complexity.SecondOrderPolynomial.MonotoneLengths length)
    {smaller larger : ℕ} (hle : smaller ≤ larger) :
    bound.eval length smaller ≤ bound.eval length larger := by
  rw [ExecutionCost.le_iff]
  exact ⟨bound.work.eval_monotone hLength hle, bound.queries.eval_monotone hLength hle,
    bound.traffic.eval_monotone hLength hle,
    bound.peakStateSize.eval_monotone hLength hle,
    bound.peakHeadSize.eval_monotone hLength hle⟩

/-- Resource-bound evaluation is monotone under enlargement of oracle length functions. -/
theorem eval_mono_lengths (bound : ResourcePolynomial label)
    {smaller larger : label → ℕ → ℕ}
    (hLarger : _root_.Complexity.SecondOrderPolynomial.MonotoneLengths larger)
    (hle : ∀ interface size, smaller interface size ≤ larger interface size)
    (inputSize : ℕ) :
    bound.eval smaller inputSize ≤ bound.eval larger inputSize := by
  rw [ExecutionCost.le_iff]
  exact ⟨bound.work.eval_mono_lengths hLarger hle inputSize,
    bound.queries.eval_mono_lengths hLarger hle inputSize,
    bound.traffic.eval_mono_lengths hLarger hle inputSize,
    bound.peakStateSize.eval_mono_lengths hLarger hle inputSize,
    bound.peakHeadSize.eval_mono_lengths hLarger hle inputSize⟩

end ResourcePolynomial

/-! ## Oracle resource contracts -/

variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
  [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq p.A]
  {Q : QuantitativeStepClass.{u, v, w} C} {input output : Type u}
  {bd : Boundary C p input output} {interface : InterfaceBoundary C p} {label : Type x}

/-- The response-length function variable exposed for each open oracle interface.

Handler work and state growth are deliberately absent. They are not charged by an open caller's
trace and may enter a closed bound only through a future resource-substitution theorem that proves
how a concrete handler is executed. -/
inductive OracleModulus (label : Type x) where
  /-- Encoded tagged-response length as a function of encoded query length. -/
  | responseSize (interface : label)
  deriving DecidableEq, Repr

/-- One admissible family of open-oracle response relations and length moduli.

`allows` is load-bearing. An open oracle over an unbounded response carrier, such as an adversary
state, generally promises a size bound only for the answers it may return. Quantifying over every
inhabitant would make such a promise impossible; quantifying over no answers would make a runtime
claim vacuous. `RunsWithinUnder` therefore combines this relation with reachable progress.

`responseSize_le` bounds the encoded tagged answer `p.Idx`, not merely its payload, whenever that
answer is allowed. This matches the bytes actually charged by `ExecutionTrace` and makes any
pairing/tagging overhead visible.

Handler work and state are deliberately absent. A later interface-closing theorem must consume a
separate certificate that packages a concrete handler execution with proved resource bounds;
unverified numeric claims do not belong in the open caller contract. -/
structure OracleResourceModel (Q : QuantitativeStepClass.{u, v, w} C)
    (interface : InterfaceBoundary C p) (labelOf : p.A → label) where
  /-- The replies admitted at each typed query position. -/
  allows : ∀ position : p.A, p.B position → Prop
  /-- Encoded response length for each interface. -/
  responseSize : label → ℕ → ℕ
  /-- Response-size moduli are monotone. -/
  responseSize_monotone : ∀ interface, Monotone (responseSize interface)
  /-- Every allowed answer fits its interface's response-size envelope. -/
  responseSize_le : ∀ (position : p.A) (answer : p.B position), allows position answer →
    Q.size interface.idx ⟨position, answer⟩ ≤
      responseSize (labelOf position) (Q.size interface.pos position)

namespace OracleResourceModel

variable {labelOf : p.A → label} (model : OracleResourceModel Q interface labelOf)

/-- Expose response-length moduli to the second-order bound on an open caller. -/
def modulus : OracleModulus label → ℕ → ℕ
  | .responseSize interface => model.responseSize interface

omit [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq p.A] in
/-- Every response-length modulus exposed to the open bound is monotone. -/
theorem modulus_monotone :
    _root_.Complexity.SecondOrderPolynomial.MonotoneLengths model.modulus := by
  intro symbol
  cases symbol with
  | responseSize interface => exact model.responseSize_monotone interface

end OracleResourceModel

/-- A pinned classification of query positions into oracle interfaces and a nonempty collection of
admissible resource models.

The admissibility predicate is part of the contract: it is what fixes or constrains response-size
moduli. The nonemptiness field prevents universal quantification over compatible models from
proving a complexity statement vacuously when one query admits unbounded encoded answers of the
same size.

Admissibility and nonemptiness are explicit relative assumptions. They do not prove that an
envelope is tight or that the oracle is efficiently implementable. A closed, non-relative
complexity predicate must therefore pin an independently justified canonical contract. -/
structure OracleContract (Q : QuantitativeStepClass.{u, v, w} C)
    (interface : InterfaceBoundary C p) (label : Type x) where
  /-- Interface label of each syntactic query position. -/
  labelOf : p.A → label
  /-- Resource environments admitted by this contract. -/
  admissible : OracleResourceModel Q interface labelOf → Prop
  /-- The contract admits at least one global finite resource envelope. -/
  model_nonempty : ∃ model, admissible model

namespace OracleContract

variable (contract : OracleContract Q interface label)

/-- The type of resource environments compatible with a contract. -/
abbrev Model := { model : OracleResourceModel Q interface contract.labelOf //
  contract.admissible model }

namespace Model

variable {contract : OracleContract Q interface label}

/-- Forget that a resource environment satisfies its contract. -/
abbrev resourceModel (model : contract.Model) :
    OracleResourceModel Q interface contract.labelOf :=
  model.1

/-- The second-order length environment supplied by a compatible resource model. -/
abbrev modulus (model : contract.Model) : OracleModulus label → ℕ → ℕ :=
  model.resourceModel.modulus

omit [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq p.A] in
/-- Every compatible resource model supplies monotone second-order length functions. -/
theorem modulus_monotone (model : contract.Model) :
    _root_.Complexity.SecondOrderPolynomial.MonotoneLengths model.modulus :=
  model.resourceModel.modulus_monotone

end Model

end OracleContract

/-! ## Backend-relative strict PPT -/

/-- Inspectable evidence that an oracle program is strict polynomial-time relative to one
quantitative backend and pinned boundary.

One realization must work for all inputs and one second-order polynomial must bound every finite
typed interaction prefix under every compatible oracle-length model. -/
structure StrictPPTWitness (Q : QuantitativeStepClass.{u, v, w} C)
    (bd : Boundary C p input output) (contract : OracleContract Q bd.interface label)
    (program : input → FreeM p output) where
  /-- The single executable realization for the entire input family. -/
  realization : QuantitativeRealization Q bd
  /-- The realization implements the given free interaction syntax. -/
  implements : realization.machine.Implements program
  /-- One response-length-relative polynomial bound, independent of the input and length model. -/
  polynomial : ResourcePolynomial (OracleModulus label)
  /-- Every contract-conforming finite answer prefix obeys the polynomial bound. -/
  runsWithin : ∀ model : contract.Model,
    realization.RunsWithinUnder model.resourceModel.allows fun value ↦
      polynomial.eval model.modulus (Q.size bd.input value)

/-! ## Certified immediately returning programs -/

/-- The executable code needed by an immediately returning program.

The result function is explicit, so an arbitrary host-language function cannot enter this
constructor without a backend realizer. The readout certificate is polynomially bounded because
its encoded sum tag and work are part of every execution. The transition realizer is required for
type-correct executability but needs no bound because a pure machine never invokes it. -/
structure PureCertificate
    (Q : QuantitativeStepClass.{u, v, w} C) (bd : Boundary C p input output)
    (function : input → output) where
  /-- Executable result computation with polynomial work and output growth. -/
  result : Q.PolyRealizer bd.input bd.out function
  /-- Executable resolved-state readout, including its sum tag and encoded-size growth. -/
  head : Q.PolyRealizer bd.out bd.head
    (Sum.inl : output → output ⊕ p.A)
  /-- Executable evidence for the pure machine's necessarily absent transition.

  This is requested directly instead of requiring the backend's whole option-closure suite. -/
  update : Q.Realizer (bd.stateIdx bd.out) (StepClass.HasOption.option bd.out)
    (PFunctor.DynSystem.DynComputation.ofFn (p := p) function).update?

namespace PureCertificate

variable {function : input → output}

/-- Build a certified pure program from one polynomial result realizer and an explicit polynomial
model.

The model supplies the resolved left-sum readout and the necessarily absent transition. Its
structural choices are installed locally and remain visible in the result type, so this constructor
cannot silently mix a boundary assembled with different product, sum, or option representations. -/
def ofPolyRealizer (model : Q.PolynomialModel)
    (result : Q.PolyRealizer bd.input bd.out function) :
    letI := model.kernel.cProd
    letI := model.kernel.cSum
    letI := model.kernel.cOption
    PureCertificate Q bd function := by
  letI := model.category
  letI := model.kernel.cProd
  letI := model.kernel.cSum
  letI := model.kernel.cOption
  exact
    { result := result
      head := model.structural.inl bd.out bd.pos
      update :=
        (model.structural.optionNone (bd.stateIdx bd.out) bd.out).code.castFunction (by
          funext step
          exact (PFunctor.DynSystem.DynComputation.update?_of_view_return
            (PFunctor.DynSystem.DynComputation.ofFn (p := p) function)
            (PFunctor.DynSystem.DynComputation.view_ofFn function step.1) step.2).symm) }

/-- Quantitative realization assembled from the two certified pure-program primitives. -/
def realization (certificate : PureCertificate Q bd function) :
    QuantitativeRealization Q bd where
  machine := PFunctor.DynSystem.DynComputation.ofFn (p := p) function
  state := bd.out
  initCode := certificate.result.code
  headCode := certificate.head.code
  updateCode := certificate.update

/-- The first-order work and size certificates lifted into the five-component resource bound. -/
def polynomial {label : Type x} (certificate : PureCertificate Q bd function) :
    ResourcePolynomial (OracleModulus label) where
  work := ResourcePolynomial.ofFirstOrder <|
    _root_.Complexity.FirstOrderPolynomial.add certificate.result.work <|
      _root_.Complexity.FirstOrderPolynomial.comp certificate.head.work
        certificate.result.outputSize
  queries := .const 0
  traffic := .const 0
  peakStateSize := ResourcePolynomial.ofFirstOrder certificate.result.outputSize
  peakHeadSize := ResourcePolynomial.ofFirstOrder <|
    _root_.Complexity.FirstOrderPolynomial.comp certificate.head.outputSize
      certificate.result.outputSize

/-- The assembled pure realization implements the expected `FreeM.pure` program. -/
theorem implements (certificate : PureCertificate Q bd function) :
    certificate.realization.machine.Implements fun input ↦ FreeM.pure (function input) := by
  change (PFunctor.DynSystem.DynComputation.ofFn (p := p) function).Implements _
  intro input
  rw [denote_ofFn]
  simp

/-- Every finite prefix of the pure realization satisfies its derived polynomial bound. -/
theorem runsWithin {label : Type x} (certificate : PureCertificate Q bd function)
    (allows : ∀ position, p.B position → Prop)
    (length : OracleModulus label → ℕ → ℕ) :
    certificate.realization.RunsWithinUnder allows fun input ↦
      (certificate.polynomial (label := label)).eval length
        (Q.size bd.input input) := by
  refine ⟨?_, ?_, ?_⟩
  · intro input finish trace _
    cases trace with
    | nil state =>
        rw [ExecutionCost.le_iff]
        simp only [QuantitativeRealization.executionCost,
          QuantitativeRealization.ExecutionTrace.cost,
          PureCertificate.realization, PureCertificate.polynomial,
          ResourcePolynomial.eval, ResourcePolynomial.eval_ofFirstOrder,
          _root_.Complexity.FirstOrderPolynomial.eval_add,
          _root_.Complexity.FirstOrderPolynomial.eval_comp,
          ExecutionCost.ofWork, ExecutionCost.observe, ExecutionCost.work_add,
          ExecutionCost.queries_add, ExecutionCost.traffic_add,
          ExecutionCost.peakStateSize_add, ExecutionCost.peakHeadSize_add,
          add_zero, max_zero, zero_max]
        refine ⟨?_, le_rfl, le_rfl, ?_, ?_⟩
        · exact Nat.add_le_add (certificate.result.work_le input) <|
            (certificate.head.work_le (function input)).trans <|
              certificate.head.work.eval_monotone (certificate.result.outputSize_le input)
        · exact certificate.result.outputSize_le input
        · exact (certificate.head.outputSize_le (function input)).trans <|
            certificate.head.outputSize.eval_monotone
              (certificate.result.outputSize_le input)
    | query view_eq direction tail =>
        change Sum.inl _ = Sum.inr _ at view_eq
        exact nomatch view_eq
  · intro input
    exact resolvesInUnder_return _ _ 0 _ _ (view_ofFn function (function input))
  · intro input state trace _ position next view_eq
    change Sum.inl state =
      Sum.inr (⟨position, next⟩ : p.Obj certificate.realization.machine.State) at view_eq
    exact nomatch view_eq

/-- Build the complete strict-PPT witness for an immediately returning program under any contract.

The contract is irrelevant to the numeric bound because the program makes no queries, but it
remains fixed in the resulting type so this constructor composes with open programs without
changing their interface policy. -/
def strictPPTWitness {label : Type x} (certificate : PureCertificate Q bd function)
    (contract : OracleContract Q bd.interface label) :
    StrictPPTWitness Q bd contract fun input ↦ FreeM.pure (function input) where
  realization := certificate.realization
  implements := certificate.implements
  polynomial := certificate.polynomial
  runsWithin model := certificate.runsWithin model.resourceModel.allows model.modulus

end PureCertificate

/-- Strict, worst-case oracle PPT relative to an explicit quantitative backend.

The `By` suffix is intentional: using this proposition as conventional machine-model PPT requires
an adequacy theorem for `Q`. It is also relative to the supplied `OracleContract`; a closed alias
must pin an honest canonical contract rather than quantify over or accept an arbitrary one. -/
def IsOraclePPTBy (Q : QuantitativeStepClass.{u, v, w} C)
    (bd : Boundary C p input output) (contract : OracleContract Q bd.interface label)
    (program : input → FreeM p output) : Prop :=
  Nonempty (StrictPPTWitness Q bd contract program)

/-- An explicit synonym emphasizing that the generic oracle predicate is strict and pathwise. -/
abbrev IsStrictPPTBy := @IsOraclePPTBy

/-- An immediately returning function with explicit polynomial code is strict oracle PPT. -/
theorem PureCertificate.isOraclePPTBy {function : input → output} {label : Type x}
    (certificate : PureCertificate Q bd function)
    (contract : OracleContract Q bd.interface label) :
    IsOraclePPTBy Q bd contract fun input ↦ FreeM.pure (function input) :=
  ⟨certificate.strictPPTWitness contract⟩

namespace StrictPPTWitness

variable {contract : OracleContract Q bd.interface label} {program : input → FreeM p output}

/-- Transport a strict-PPT witness across extensional equality of whole program families.

The realization, operational costs, and resource polynomial are unchanged. Only the semantic
program index is transported, so this constructor cannot manufacture executable evidence. -/
def congrProgram {program' : input → FreeM p output}
    (witness : StrictPPTWitness Q bd contract program) (hprogram : program = program') :
    StrictPPTWitness Q bd contract program' :=
  hprogram ▸ witness

/-- A strict PPT witness retains quantitative realizability when bounds are forgotten. -/
theorem isQuantitativelyRealizableBy (witness : StrictPPTWitness Q bd contract program) :
    IsQuantitativelyRealizableBy Q bd program :=
  ⟨witness.realization, witness.implements⟩

/-- Specialize a strict PPT witness to one concrete oracle-length environment. -/
theorem isQuantitativelyRealizableWithinUnder
    (witness : StrictPPTWitness Q bd contract program) (model : contract.Model) :
    IsQuantitativelyRealizableWithinUnder Q bd model.resourceModel.allows program
      (fun value ↦ witness.polynomial.eval model.modulus (Q.size bd.input value)) :=
  ⟨witness.realization, witness.implements, witness.runsWithin model⟩

/-- When a model admits every typed reply, its query component bounds the full free syntax. -/
theorem isTotalRollBound (witness : StrictPPTWitness Q bd contract program)
    (model : contract.Model)
    (hAllows : ∀ position answer, model.resourceModel.allows position answer)
    (value : input) :
    (program value).IsTotalRollBound
      (witness.polynomial.eval model.modulus (Q.size bd.input value)).queries := by
  have hAllowsEq : model.resourceModel.allows = fun _ _ ↦ True := by
    funext position answer
    apply propext
    exact ⟨fun _ ↦ trivial, fun _ ↦ hAllows position answer⟩
  have hRuns : witness.realization.RunsWithin fun input ↦
      witness.polynomial.eval model.modulus (Q.size bd.input input) := by
    change witness.realization.RunsWithinUnder (fun _ _ ↦ True) _
    rw [← hAllowsEq]
    exact witness.runsWithin model
  exact hRuns.isTotalRollBound witness.implements value

end StrictPPTWitness

namespace IsOraclePPTBy

variable {contract : OracleContract Q bd.interface label} {program : input → FreeM p output}

/-- Strict oracle PPT is invariant under extensional equality of whole program families. -/
theorem congrProgram {program' : input → FreeM p output}
    (h : IsOraclePPTBy Q bd contract program) (hprogram : program = program') :
    IsOraclePPTBy Q bd contract program' := by
  obtain ⟨witness⟩ := h
  exact ⟨witness.congrProgram hprogram⟩

/-- Strict PPT implies backend-relative quantitative realizability. -/
theorem isQuantitativelyRealizableBy (h : IsOraclePPTBy Q bd contract program) :
    IsQuantitativelyRealizableBy Q bd program := by
  obtain ⟨witness⟩ := h
  exact witness.isQuantitativelyRealizableBy

/-- Strict PPT erases all the way to qualitative realizability. -/
theorem isRealizableBy (h : IsOraclePPTBy Q bd contract program) :
    IsRealizableBy C bd program :=
  h.isQuantitativelyRealizableBy.isRealizableBy

end IsOraclePPTBy

/-! ## OracleComp and uniform-family facades -/

/-- Strict oracle PPT for a VCVio `OracleComp` program, via its definitional `FreeM` syntax. -/
def OracleProgram.IsOraclePPTBy {index : Type u} {spec : OracleSpec.{u, u} index}
    {input output : Type u} {C : StepClass.{u, v}}
    [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq spec.Domain]
    (Q : QuantitativeStepClass.{u, v, w} C)
    (bd : Boundary C spec.toPFunctor input output)
    {label : Type x} (contract : OracleContract Q bd.interface label)
    (program : input → OracleComp spec output) : Prop :=
  OracleComp.Complexity.IsOraclePPTBy Q bd contract fun value ↦
    (program value).toFreeM

/-- Canonical finite resource model for the explicit fair-coin interface.

The response envelope is the larger encoded tagged-answer size of the two Boolean outcomes. This
contract concerns only the open computation's answer lengths; efficient fair-bit generation is a
separate sampler/handler certificate. -/
def fairCoinResourceModel {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (interface : InterfaceBoundary C coinSpec.toPFunctor) :
    OracleResourceModel Q interface (fun _ ↦ PUnit.unit) where
  allows := fun _ _ ↦ True
  responseSize := fun _ _ ↦
    max (Q.size interface.idx ⟨PUnit.unit, false⟩)
      (Q.size interface.idx ⟨PUnit.unit, true⟩)
  responseSize_monotone := fun _ _ _ _ ↦ le_rfl
  responseSize_le := fun position answer _ ↦ by
    cases position
    cases answer
    · exact Nat.le_max_left _ _
    · exact Nat.le_max_right _ _

/-- Both Boolean replies are admitted by the canonical fair-coin resource model. -/
@[simp]
theorem fairCoinResourceModel_allows {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (interface : InterfaceBoundary C coinSpec.toPFunctor)
    (position : coinSpec.Domain) (answer : coinSpec.Range position) :
    (fairCoinResourceModel Q interface).allows position answer :=
  trivial

/-- Contract admitting exactly the canonical finite fair-coin resource model. -/
def fairCoinContract {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (interface : InterfaceBoundary C coinSpec.toPFunctor) :
    OracleContract Q interface Unit where
  labelOf _ := PUnit.unit
  admissible model := model = fairCoinResourceModel Q interface
  model_nonempty := ⟨fairCoinResourceModel Q interface, rfl⟩

/-- A model compatible with `fairCoinContract` is the canonical fair-coin model. -/
@[simp]
theorem fairCoinContract_admissible_iff {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (interface : InterfaceBoundary C coinSpec.toPFunctor)
    (model : OracleResourceModel Q interface (fairCoinContract Q interface).labelOf) :
    (fairCoinContract Q interface).admissible model ↔
      model = fairCoinResourceModel Q interface :=
  Iff.rfl

/-- The canonical resource model packaged with its fair-coin contract evidence. -/
def fairCoinModel {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (interface : InterfaceBoundary C coinSpec.toPFunctor) :
    (fairCoinContract Q interface).Model :=
  ⟨fairCoinResourceModel Q interface, rfl⟩

/-- The fair-coin contract admits no resource model other than the canonical one. -/
theorem fairCoinModel_eq {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (interface : InterfaceBoundary C coinSpec.toPFunctor)
    (model : (fairCoinContract Q interface).Model) :
    model = fairCoinModel Q interface := by
  apply Subtype.ext
  exact model.2

/-- Strict probabilistic polynomial time, specialized to the explicit fair-coin interface.

The backend and every boundary representation remain explicit, while the oracle contract is fixed
to `fairCoinContract`. Fairness belongs to VCVio's probability interpretation of `coinSpec`;
strict cost still quantifies over both Boolean answers. -/
def IsPPTBy {input output : Type} {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (bd : Boundary C coinSpec.toPFunctor input output)
    (program : input → OracleComp coinSpec output) : Prop :=
  OracleProgram.IsOraclePPTBy Q bd (fairCoinContract Q bd.interface) program

/-- Strict PPT for a security-indexed family means strict PPT of its one packed program.

This requires one realization and one polynomial for every security parameter. It is strictly
stronger than choosing unrelated witnesses pointwise. -/
def SecurityFamily.IsOraclePPTBy
    {index : ℕ → Type u} {spec : (n : ℕ) → OracleSpec.{u, u} (index n)}
    {input output : ℕ → Type u} {C : StepClass.{u, v}}
    [C.HasProd] [C.HasSum] [C.HasOption]
    [DecidableEq (SecurityFamily.Spec spec).Domain]
    (Q : QuantitativeStepClass.{u, v, w} C)
    (bd : Boundary C (SecurityFamily.Spec spec).toPFunctor
      (SecurityFamily.Input input) (SecurityFamily.Output output))
    {label : Type x} (contract : OracleContract Q bd.interface label)
    (program : (n : ℕ) → input n → OracleComp (spec n) (output n)) : Prop :=
  OracleProgram.IsOraclePPTBy Q bd contract (SecurityFamily.packProgram program)

/-- An explicit synonym emphasizing strict pathwise bounds for a packed oracle family. -/
abbrev SecurityFamily.IsStrictPPTBy := @SecurityFamily.IsOraclePPTBy

/-- Uniform strict oracle PPT for a packed security family whose only syntactic interaction is a
fair coin.

The explicit contract must additionally control how the packed security parameter contributes to
the boundary's encoded query and tagged-answer sizes. Deriving that contract requires a
quantitative encoding-growth certificate and cannot be done from an arbitrary `Boundary` alone. -/
def SecurityFamily.IsCoinPPTByUnder
    {input output : ℕ → Type} {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    [DecidableEq (SecurityFamily.Spec (fun _ : ℕ ↦ coinSpec)).Domain]
    (Q : QuantitativeStepClass C)
    (bd : Boundary C (SecurityFamily.Spec (fun _ : ℕ ↦ coinSpec)).toPFunctor
      (SecurityFamily.Input input) (SecurityFamily.Output output))
    {label : Type x} (contract : OracleContract Q bd.interface label)
    (program : (n : ℕ) → input n → OracleComp coinSpec (output n)) : Prop :=
  SecurityFamily.IsOraclePPTBy Q bd contract program

end OracleComp.Complexity
