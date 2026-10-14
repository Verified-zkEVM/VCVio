/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.Basic
public import VCVio.Quantum.Oracle.Basis

/-!
# Runtimes and the execution of quantum programs

A runtime interprets the ports of a signature. It owns a private register `D`, which starts in
the substate `init` and persists from one call to the next, and it answers a call of port `i`
with a subinstrument `step i` from `In i × D` to `Out i × D` with outcomes in `Result i`. The
program has no command that acts on `D`: it reaches `D` only through calls.

Running a program `x : QuantumComp L spec X A` under an interpretation `I` of its local
operations and against a runtime `R` gives a dependent subinstrument `R.run I x` from `A × R.D`
whose outcomes are the leaves `⟨u, y⟩` of `x`, with output register `u × R.D` on the leaf
`⟨u, y⟩`. It is defined by recursion on the program tree:

* a local operation `o` applies `I o` to the program register, framed by `D`;
* a call of port `i` through `ℓ : A ≃ In i × E` relabels `A × D` to `(In i × D) × E`, applies
  `step i` framed by `E`, and relabels `(Out i × D) × E` to `(Out i × E) × D`
  (`Quantum.QuantumRuntime.queryStep`).

`run` sends McBride sequencing of programs to sequencing of dependent subinstruments
(`Quantum.QuantumRuntime.run_bind`).

## Programs on a fixed final register

A program `x : QuantumComp₂ L spec A B α` has its leaves on `B`, so its run is a subinstrument
`R.run₂ I x` from `A × R.D` to `B × R.D` with outcomes in `α`: the run of `x` restricted to the
leaves `⟨B, rfl, a⟩` (`Quantum.DSubInstrument.comap`) and read through the equivalence between
subinstruments and dependent subinstruments with a constant output register. Its branch at `a`
is the branch of `R.run I x` at that leaf (`Quantum.QuantumRuntime.branch_run₂`), and it is a
morphism of indexed monads (`Quantum.QuantumRuntime.run₂_bind`).

## Observation

A program is observed from a substate `ρ` of its starting register, with the runtime's register
in `init`, that is from the product substate `ρ ⊗ init`:

* `Quantum.QuantumRuntime.jointPost R I x ρ p`: the joint substate of `u × D` after the run
  reports the leaf `p = ⟨u, y⟩`. Its trace is the weight of `p`.
* `Quantum.QuantumRuntime.reducedPost R I x ρ p`: its reduced substate on the program register
  `u`, which is all a later program can act on.
* `Quantum.QuantumRuntime.outcomeLaw R I x ρ`: the law of the leaf reached, a subprobability
  measure whose missing mass is failure.
* `Quantum.QuantumRuntime.outcomeLawWith R I x ρ f`: the law of an observation `f` of the leaf
  reached, as a sum of weighted point masses, so that `f` need not be measurable.

The fixed-register versions `jointPost₂`, `reducedPost₂` and `outcomeLaw₂` observe `R.run₂ I x`,
and agree with the general ones at the leaves `⟨B, rfl, a⟩`; the law of the value of a
fixed-register program is the general law observed through the value of the leaf
(`Quantum.QuantumRuntime.outcomeLaw₂_eq_outcomeLawWith`).

## Main definitions

* `Quantum.QuantumRuntime spec`: a private register, its initial substate and a step per port.
* `Quantum.QuantumRuntime.queryStep`, `Quantum.QuantumRuntime.run` and
  `Quantum.QuantumRuntime.run₂`.
* `Quantum.QuantumRuntime.jointPost`, `Quantum.QuantumRuntime.reducedPost`,
  `Quantum.QuantumRuntime.outcomeLaw` and `Quantum.QuantumRuntime.outcomeLawWith`, with the
  fixed-register versions.

## Main statements

* `Quantum.QuantumRuntime.run_pure`, `run_primBind`, `run_queryBind` and `run_bind`.
* `Quantum.QuantumRuntime.branch_run₂`: the fixed-register run agrees with the general run.
* `Quantum.QuantumRuntime.run₂_pure`, `run₂_queryBind`, `run₂_bind`, `run₂_map`, and for programs
  over instruments `run₂_act` and `run₂_act_bind`.
* `Quantum.QuantumRuntime.lossless_run`: a lossless program against lossless steps runs to a
  lossless dependent subinstrument.
-/

public section

open IPFunctor MeasureTheory
open scoped Kronecker

universe u v u₁ v₁ w w₁

namespace Quantum

/-- A runtime for the signature `spec`: a private register `D` with initial substate `init`, and
for each port the subinstrument that answers a call of it. -/
structure QuantumRuntime (spec : QuantumOracleSpec.{u₁, v₁}) where
  /-- The runtime's private register, which persists across calls. -/
  D : QReg
  /-- The initial substate of the private register. -/
  init : SubState D
  /-- The subinstrument that answers a call of port `i`, acting on the port's input register
  and the private register. -/
  step : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)

namespace QuantumRuntime

/-! ## The relabellings of a call -/

/-- The bijection that brings a port's input register next to the runtime register before a
call: `A × D ≃ (I × D) × E` for `ℓ : A ≃ I × E`. -/
@[expose]
def queryEquivIn {A I E : Type*} (ℓ : A ≃ I × E) (D : Type*) : A × D ≃ (I × D) × E :=
  (ℓ.prodCongr (Equiv.refl D)).trans
    ((Equiv.prodAssoc I E D).trans
      ((Equiv.prodCongr (Equiv.refl I) (Equiv.prodComm E D)).trans
        (Equiv.prodAssoc I D E).symm))

/-- The bijection that puts the program's remainder register back after a call:
`(O × D) × E ≃ (O × E) × D`. -/
@[expose]
def queryEquivOut (O D E : Type*) : (O × D) × E ≃ (O × E) × D :=
  (Equiv.prodAssoc O D E).trans
    ((Equiv.prodCongr (Equiv.refl O) (Equiv.prodComm D E)).trans (Equiv.prodAssoc O E D).symm)

/-- `queryEquivIn` on a basis element. -/
@[simp]
theorem queryEquivIn_apply {A I E : Type*} (ℓ : A ≃ I × E) (D : Type*) (x : A × D) :
    queryEquivIn ℓ D x = (((ℓ x.1).1, x.2), (ℓ x.1).2) :=
  rfl

/-- `queryEquivOut` on a basis element. -/
@[simp]
theorem queryEquivOut_apply (O D E : Type*) (x : (O × D) × E) :
    queryEquivOut O D E x = ((x.1.1, x.2), x.1.2) :=
  rfl

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {X : QReg → Type w} {Y : QReg → Type w₁} {A B C : QReg} {α : Type w}
  {β : Type w₁}

/-- One call of port `i`, with the rest `E` of the program register carried along: relabel
`A × D` to `(In i × D) × E`, apply the port's step framed by `E`, and relabel back. -/
@[expose]
noncomputable def queryStep (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E) :
    SubInstrument (A × R.D) ((spec.Out i × E) × R.D) (spec.Result i) :=
  (SubInstrument.relabel (queryEquivIn ℓ R.D)).bind fun _ ↦
    ((R.step i).frame E).bind fun r ↦
      (SubInstrument.relabel (queryEquivOut (spec.Out i) R.D E)).bind fun _ ↦
        SubInstrument.pure r

/-- A call against a lossless step is lossless. -/
theorem lossless_queryStep {i : spec.Port} (hi : (R.step i).Lossless) (E : QReg)
    (ℓ : A ≃ spec.In i × E) : (R.queryStep i E ℓ).Lossless :=
  (SubInstrument.lossless_relabel _).bind fun _ ↦ (hi.frame E).bind fun _ ↦
    (SubInstrument.lossless_relabel _).bind fun _ ↦ SubInstrument.lossless_pure _

/-! ## Execution -/

/-- Execution of a program tree, by recursion on the tree. -/
@[expose]
noncomputable def runAux :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor L spec) X A →
      DSubInstrument (A × R.D) (Σ u, X u) fun p ↦ p.1 × R.D
  | _, .pure x => DSubInstrument.ret (fun p : Σ u, X u ↦ p.1 × R.D) ⟨_, x⟩
  | _, .liftBind (.prim o) k => ((I o).frame R.D).bind fun b ↦ runAux (k (ULift.up b))
  | _, .liftBind (.query i E ℓ) k =>
      (SubInstrument.toD (R.queryStep i E ℓ)).bind fun r ↦ runAux (k (ULift.up r))

/-- **Execution.** A program run under the interpretation `I` against the runtime `R` is a
dependent subinstrument on the joint register of the program and the runtime, whose outcomes are
the leaves `⟨u, y⟩` of the program, with output register `u × R.D` on the leaf `⟨u, y⟩`. -/
@[expose]
noncomputable def run (x : QuantumComp L spec X A) :
    DSubInstrument (A × R.D) (Σ u, X u) fun p ↦ p.1 × R.D :=
  R.runAux I x

/-- Running a program that stops at once reaches its leaf and leaves the state unchanged. -/
@[simp]
theorem run_pure (x : X A) :
    R.run I (QuantumComp.pure (L := L) (spec := spec) x) =
      DSubInstrument.ret (fun p : Σ u, X u ↦ p.1 × R.D) ⟨A, x⟩ :=
  rfl

/-- Running a local operation followed by a continuation applies the operation's interpretation
framed by the runtime register, then the run of the continuation. -/
@[simp]
theorem run_primBind (o : L.Op A) (k : (b : L.Outcome o) → QuantumComp L spec X (L.next o b)) :
    R.run I (QuantumComp.primBind o k) = ((I o).frame R.D).bind fun b ↦ R.run I (k b) :=
  rfl

/-- Running a call followed by a continuation applies `queryStep`, then the run of the
continuation. -/
@[simp]
theorem run_queryBind (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E))) :
    R.run I (QuantumComp.queryBind i E ℓ k) =
      (SubInstrument.toD (R.queryStep i E ℓ)).bind fun r ↦ R.run I (k r) :=
  rfl

/-- Running the generic local operation followed by a continuation. -/
theorem run_prim_bind (o : L.Op A) (k : ∀ u, L.OutcomeAt o u → QuantumComp L spec Y u) :
    R.run I ((QuantumComp.prim o).bind k) =
      ((I o).frame R.D).bind fun b ↦ R.run I (k _ ⟨b, rfl⟩) :=
  rfl

/-- Running the generic call followed by a continuation. -/
theorem run_query_bind (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : ∀ u, (PSigma fun _ : u = QReg.of (spec.Out i × E) ↦ spec.Result i) →
      QuantumComp L spec Y u) :
    R.run I ((QuantumComp.query i E ℓ).bind k) =
      (SubInstrument.toD (R.queryStep i E ℓ)).bind fun r ↦ R.run I (k _ ⟨rfl, r⟩) :=
  rfl

/-- **`run` respects sequencing.** Running `x.bind k` runs `x`, and on the leaf `⟨u, y⟩` runs
`k u y` from the register `u × R.D` that the leaf leaves. -/
theorem run_bind (x : QuantumComp L spec X A) (k : ∀ u, X u → QuantumComp L spec Y u) :
    R.run I (x.bind k) = (R.run I x).bind fun p ↦ R.run I (k p.1 p.2) := by
  induction x using QuantumComp.inductionOn with
  | pure _ y =>
    exact (DSubInstrument.ret_bind (⟨_, y⟩ : Σ u, X u) fun p ↦ R.run I (k p.1 p.2)).symm
  | primBind _ o k' ih =>
    rw [QuantumComp.primBind_bind, run_primBind, run_primBind, DSubInstrument.bind_assoc]
    exact congrArg _ (funext ih)
  | queryBind _ i E ℓ k' ih =>
    rw [QuantumComp.queryBind_bind, run_queryBind, run_queryBind, DSubInstrument.bind_assoc]
    exact congrArg _ (funext ih)

/-- A lossless program run against a runtime whose steps are lossless is lossless. -/
theorem lossless_run {x : QuantumComp L spec X A} (hx : x.Lossless I)
    (hR : ∀ i, (R.step i).Lossless) : (R.run I x).Lossless := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => exact DSubInstrument.lossless_ret _ _
  | primBind _ o k ih => exact (hx.1.frame R.D).bind fun b ↦ ih b (hx.2 b)
  | queryBind _ i E ℓ k ih =>
    exact (SubInstrument.lossless_toD_iff.mpr (R.lossless_queryStep (hR i) E ℓ)).bind
      fun r ↦ ih r (hx r)

/-! ## Execution of programs on a fixed final register -/

/-- **Execution of a fixed-register program.** The run of `x`, restricted to the leaves
`⟨B, rfl, a⟩` and read as a subinstrument from `A × R.D` to `B × R.D` with outcomes in `α`.
Every leaf of `x` has this form, so nothing is dropped. -/
@[expose]
noncomputable def run₂ (x : QuantumComp₂ L spec A B α) : SubInstrument (A × R.D) (B × R.D) α :=
  DSubInstrument.toSubInstrument
    ((R.run I x).comap (QuantumComp₂.leafEquiv B α) (QuantumComp₂.leafEquiv B α).injective)

/-- **Agreement of the two runs.** The branch at `a` of the fixed-register run is the branch of
the general run at the leaf `⟨B, rfl, a⟩`. -/
theorem branch_run₂ (x : QuantumComp₂ L spec A B α) (a : α) :
    (R.run₂ I x).branch a = (R.run I x).branch ⟨B, rfl, a⟩ :=
  rfl

/-- The dependent form of the fixed-register run is the general run restricted to the leaves on
`B`. -/
theorem toD_run₂ (x : QuantumComp₂ L spec A B α) :
    SubInstrument.toD (R.run₂ I x) =
      (R.run I x).comap (QuantumComp₂.leafEquiv B α) (QuantumComp₂.leafEquiv B α).injective :=
  rfl

/-- Running a program that returns `a` returns `a` and leaves the state unchanged. -/
@[simp]
theorem run₂_pure (a : α) :
    R.run₂ I (QuantumComp₂.pure a : QuantumComp₂ L spec A A α) = SubInstrument.pure a := by
  refine SubInstrument.ext (funext fun a' ↦ ?_)
  change (DSubInstrument.ret (fun p : Σ u, QuantumComp₂.Leaf A α u ↦ p.1 × R.D)
    ⟨A, rfl, a⟩).branch ⟨A, rfl, a'⟩ = _
  obtain rfl | h := eq_or_ne a' a
  · rw [DSubInstrument.branch_ret_self, SubInstrument.branch_pure_self]
  · rw [DSubInstrument.branch_ret_of_ne _ fun h' ↦
      h (congrArg (fun p : Σ u, QuantumComp₂.Leaf A α u ↦ p.2.2) h'),
      SubInstrument.branch_pure_of_ne h]

/-- Running a call followed by a continuation applies `queryStep`, then the runs of the
continuation. -/
@[simp]
theorem run₂_queryBind (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp₂ L spec (QReg.of (spec.Out i × E)) B α) :
    R.run₂ I (QuantumComp₂.queryBind i E ℓ k) =
      (R.queryStep i E ℓ).bind fun r ↦ R.run₂ I (k r) := by
  refine SubInstrument.ext (funext fun a ↦ LinearMap.ext fun ρ ↦ ?_)
  change ((SubInstrument.toD (R.queryStep i E ℓ)).bind fun r ↦ R.run I (k r)).branch
    ⟨B, rfl, a⟩ ρ = _
  rw [DSubInstrument.branch_bind_apply, SubInstrument.branch_bind_apply]
  rfl

/-- Running a call followed by a continuation. -/
theorem run₂_query_bind (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp₂ L spec (QReg.of (spec.Out i × E)) B α) :
    R.run₂ I ((QuantumComp₂.query i E ℓ).bind k) =
      (R.queryStep i E ℓ).bind fun r ↦ R.run₂ I (k r) :=
  R.run₂_queryBind I i E ℓ k

/-- Running a call applies `queryStep`. -/
theorem run₂_query (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E) :
    R.run₂ I (QuantumComp₂.query (L := L) i E ℓ) =
      (R.queryStep i E ℓ).bind fun r ↦ SubInstrument.pure r := by
  have h := R.run₂_queryBind I i E ℓ QuantumComp₂.pure
  simp only [run₂_pure] at h
  exact h

/-- Running a local operation followed by a continuation, in dependent form: the operation's
interpretation framed by the runtime register, then the runs of the continuation. -/
theorem toD_run₂_primBind (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp₂ L spec (L.next o b) B α) :
    SubInstrument.toD (R.run₂ I (QuantumComp₂.primBind o k)) =
      ((I o).frame R.D).bind fun b ↦ SubInstrument.toD (R.run₂ I (k b)) := by
  refine DSubInstrument.ext (funext fun a ↦ LinearMap.ext fun ρ ↦ ?_)
  change (((I o).frame R.D).bind fun b ↦ R.run I (k b)).branch ⟨B, rfl, a⟩ ρ = _
  rw [DSubInstrument.branch_bind_apply, DSubInstrument.branch_bind_apply]
  rfl

/-- **`run₂` is a morphism of indexed monads**: running a sequence of fixed-register programs
is sequencing their runs. -/
theorem run₂_bind (x : QuantumComp₂ L spec A B α) (k : α → QuantumComp₂ L spec B C β) :
    R.run₂ I (x.bind k) = (R.run₂ I x).bind fun a ↦ R.run₂ I (k a) := by
  refine QuantumComp₂.inductionOn (motive := fun A B x ↦ ∀ {C : QReg}
    (k : α → QuantumComp₂ L spec B C β),
      R.run₂ I (x.bind k) = (R.run₂ I x).bind fun a ↦ R.run₂ I (k a)) ?_ ?_ ?_ x k
  · intro _ a _ k
    rw [QuantumComp₂.pure_bind, run₂_pure, SubInstrument.pure_bind]
  · intro _ _ o k' ih _ k
    refine SubInstrument.toD_injective ?_
    rw [QuantumComp₂.primBind_bind, toD_run₂_primBind, SubInstrument.toD_bind,
      toD_run₂_primBind, DSubInstrument.bind_assoc]
    refine congrArg _ (funext fun b ↦ ?_)
    rw [ih b k, SubInstrument.toD_bind]
  · intro _ _ i E ℓ k' ih _ k
    rw [QuantumComp₂.queryBind_bind, run₂_queryBind, run₂_queryBind, SubInstrument.bind_assoc]
    exact congrArg _ (funext fun r ↦ ih r k)

/-- Running a program with a relabelled return value relabels the outcomes of its run. -/
theorem run₂_map (f : α → β) (x : QuantumComp₂ L spec A B α) :
    R.run₂ I (x.map f) = (R.run₂ I x).map f := by
  rw [QuantumComp₂.map_eq_bind_pure, run₂_bind, SubInstrument.map_eq_bind_pure]
  simp only [run₂_pure]

/-- A lossless fixed-register program run against a runtime whose steps are lossless is
lossless. -/
theorem lossless_run₂ {x : QuantumComp₂ L spec A B α} (hx : x.Lossless I)
    (hR : ∀ i, (R.step i).Lossless) : (R.run₂ I x).Lossless :=
  SubInstrument.lossless_toD_iff.mp
    ((R.lossless_run I hx hR).comap (QuantumComp₂.leafEquiv B α).bijective)

/-- Running a local subinstrument followed by a continuation applies it framed by the runtime
register, then the runs of the continuation. -/
@[simp]
theorem run₂_act_bind {α β : Type w} (p : SubInstrument A B β) (k : β → QComp spec B C α) :
    R.run₂ .instruments ((QComp.act p).bind k) =
      (p.frame R.D).bind fun b ↦ R.run₂ .instruments (k b) := by
  refine SubInstrument.toD_injective ?_
  rw [QComp.act_bind, toD_run₂_primBind, SubInstrument.toD_bind, SubInstrument.toD_frame]
  rfl

/-- Running a local subinstrument applies it framed by the runtime register. -/
theorem run₂_act (p : SubInstrument A B α) :
    R.run₂ .instruments (QComp.act (spec := spec) p) =
      (p.frame R.D).bind fun a ↦ SubInstrument.pure a := by
  have h := R.run₂_act_bind p QuantumComp₂.pure
  simp only [QuantumComp₂.bind_pure, run₂_pure] at h
  exact h

/-! ## Observation -/

/-- The joint substate of the program register `u` and the runtime register after running `x`
from `ρ ⊗ init` and reaching the leaf `p = ⟨u, y⟩`. Its trace is the weight of `p`. -/
@[expose]
noncomputable def jointPost (x : QuantumComp L spec X A) (ρ : SubState A) (p : Σ u, X u) :
    SubState (p.1 × R.D) :=
  (R.run I x).post (ρ.prod R.init) p

/-- The substate of the program register after running `x` from `ρ ⊗ init` and reaching the leaf
`p = ⟨u, y⟩`, with the runtime register traced out. -/
@[expose]
noncomputable def reducedPost (x : QuantumComp L spec X A) (ρ : SubState A) (p : Σ u, X u) :
    SubState p.1 :=
  (R.jointPost I x ρ p).traceRight

/-- The law of the leaf reached by `x` run from `ρ ⊗ init`: a subprobability measure whose
missing mass is the weight of failure. -/
@[expose]
noncomputable def outcomeLaw [MeasurableSpace (Σ u, X u)] (x : QuantumComp L spec X A)
    (ρ : SubState A) : Measure (Σ u, X u) :=
  (R.run I x).outcomeMeasure (ρ.prod R.init)

/-- The matrix of the joint post-state. -/
@[simp]
theorem matrix_jointPost (x : QuantumComp L spec X A) (ρ : SubState A) (p : Σ u, X u) :
    (R.jointPost I x ρ p).matrix = (R.run I x).branch p (ρ.matrix ⊗ₖ R.init.matrix) :=
  rfl

/-- The reduced post-state has the trace of the joint post-state. -/
theorem trace_reducedPost (x : QuantumComp L spec X A) (ρ : SubState A) (p : Σ u, X u) :
    (R.reducedPost I x ρ p).matrix.trace = (R.jointPost I x ρ p).matrix.trace :=
  MatrixMap.trace_traceRight _

/-- Outcome laws are subprobability measures. -/
instance [MeasurableSpace (Σ u, X u)] (x : QuantumComp L spec X A) (ρ : SubState A) :
    IsSubprobabilityMeasure (R.outcomeLaw I x ρ) :=
  DSubInstrument.outcomeMeasure.instIsSubprobabilityMeasure _ _

/-- The weight of a single leaf is the trace of the joint post-state. -/
theorem outcomeLaw_apply_singleton [MeasurableSpace (Σ u, X u)]
    [MeasurableSingletonClass (Σ u, X u)] (x : QuantumComp L spec X A) (ρ : SubState A)
    (p : Σ u, X u) :
    R.outcomeLaw I x ρ {p} = ENNReal.ofReal (R.jointPost I x ρ p).matrix.trace.re :=
  DSubInstrument.outcomeMeasure_apply_singleton _ _ p

/-- When the run is lossless, the outcome law has the product of the traces of `ρ` and `init`
as its total mass. -/
theorem outcomeLaw_apply_univ_of_lossless [MeasurableSpace (Σ u, X u)]
    {x : QuantumComp L spec X A} (hx : (R.run I x).Lossless) (ρ : SubState A) :
    R.outcomeLaw I x ρ Set.univ =
      ENNReal.ofReal (ρ.matrix.trace.re * R.init.matrix.trace.re) := by
  rw [outcomeLaw, hx.outcomeMeasure_apply_univ, SubState.trace_re_prod]

/-- The law of the observation `f` of the leaf reached by `x` run from `ρ ⊗ init`: each leaf `p`
contributes its weight, the trace of the joint post-state, at the point `f p`. It is a sum of
weighted point masses, so `f` need not be measurable. -/
@[expose]
noncomputable def outcomeLawWith {γ : Type*} [MeasurableSpace γ] (x : QuantumComp L spec X A)
    (ρ : SubState A) (f : (Σ u, X u) → γ) : Measure γ :=
  Measure.sum fun p ↦ ENNReal.ofReal (R.jointPost I x ρ p).matrix.trace.re • Measure.dirac (f p)

/-- The observed law of a measurable set sums the weights of the leaves observed in it. -/
theorem outcomeLawWith_apply {γ : Type*} [MeasurableSpace γ] (x : QuantumComp L spec X A)
    (ρ : SubState A) (f : (Σ u, X u) → γ) {s : Set γ} (hs : MeasurableSet s) :
    R.outcomeLawWith I x ρ f s =
      ∑' p, ENNReal.ofReal (R.jointPost I x ρ p).matrix.trace.re * s.indicator 1 (f p) := by
  simp only [outcomeLawWith, Measure.sum_apply _ hs, Measure.smul_apply,
    Measure.dirac_apply' _ hs, smul_eq_mul]

/-- Observing the leaf itself gives the outcome law. -/
theorem outcomeLawWith_id [MeasurableSpace (Σ u, X u)] (x : QuantumComp L spec X A)
    (ρ : SubState A) : R.outcomeLawWith I x ρ (fun p ↦ p) = R.outcomeLaw I x ρ :=
  rfl

/-- The total mass of an observed law is the trace functional of the run at `ρ ⊗ init`, whatever
the observation. -/
theorem outcomeLawWith_apply_univ {γ : Type*} [MeasurableSpace γ] (x : QuantumComp L spec X A)
    (ρ : SubState A) (f : (Σ u, X u) → γ) :
    R.outcomeLawWith I x ρ f Set.univ =
      ENNReal.ofReal
        (MatrixMap.familyTrace (R.run I x).branch (ρ.prod R.init).matrix).re := by
  let : MeasurableSpace (Σ u, X u) := ⊤
  rw [outcomeLawWith_apply _ _ _ _ _ MeasurableSet.univ,
    ← DSubInstrument.outcomeMeasure_apply_univ,
    DSubInstrument.outcomeMeasure_apply _ _ MeasurableSet.univ]
  rfl

/-- The weights of all leaves sum to the trace functional of the run at `ρ ⊗ init`. -/
theorem tsum_jointPost_trace (x : QuantumComp L spec X A) (ρ : SubState A) :
    ∑' p, ENNReal.ofReal (R.jointPost I x ρ p).matrix.trace.re =
      ENNReal.ofReal
        (MatrixMap.familyTrace (R.run I x).branch (ρ.prod R.init).matrix).re := by
  let : MeasurableSpace (Σ u, X u) := ⊤
  rw [← R.outcomeLawWith_apply_univ I x ρ (fun p ↦ p),
    R.outcomeLawWith_apply I x ρ _ MeasurableSet.univ]
  simp

/-! ### Observation of programs on a fixed final register -/

/-- The joint substate of `B` and the runtime register after running the fixed-register program
`x` from `ρ ⊗ init` and observing the outcome `a`. Its trace is the weight of `a`. -/
@[expose]
noncomputable def jointPost₂ (x : QuantumComp₂ L spec A B α) (ρ : SubState A) (a : α) :
    SubState (B × R.D) :=
  (R.run₂ I x).post (ρ.prod R.init) a

/-- The substate of `B` after running the fixed-register program `x` from `ρ ⊗ init` and
observing the outcome `a`, with the runtime register traced out. -/
@[expose]
noncomputable def reducedPost₂ (x : QuantumComp₂ L spec A B α) (ρ : SubState A) (a : α) :
    SubState B :=
  (R.jointPost₂ I x ρ a).traceRight

/-- The law of the value returned by the fixed-register program `x` run from `ρ ⊗ init`: a
subprobability measure whose missing mass is the weight of failure. -/
@[expose]
noncomputable def outcomeLaw₂ [MeasurableSpace α] (x : QuantumComp₂ L spec A B α)
    (ρ : SubState A) : Measure α :=
  (R.run₂ I x).outcomeMeasure (ρ.prod R.init)

/-- The joint post-state of a fixed-register program at `a` is the general joint post-state at
the leaf `⟨B, rfl, a⟩`. -/
theorem jointPost₂_eq_jointPost (x : QuantumComp₂ L spec A B α) (ρ : SubState A) (a : α) :
    R.jointPost₂ I x ρ a = R.jointPost I x ρ ⟨B, rfl, a⟩ :=
  rfl

/-- The reduced post-state of a fixed-register program at `a` is the general reduced post-state
at the leaf `⟨B, rfl, a⟩`. -/
theorem reducedPost₂_eq_reducedPost (x : QuantumComp₂ L spec A B α) (ρ : SubState A) (a : α) :
    R.reducedPost₂ I x ρ a = R.reducedPost I x ρ ⟨B, rfl, a⟩ :=
  rfl

/-- The outcome law of a fixed-register program is the general outcome law read through the
equivalence between leaves and values, for any measurable structure on the leaves for which that
equivalence is measurable. -/
theorem outcomeLaw₂_eq_map [MeasurableSpace α] [MeasurableSpace (Σ u, QuantumComp₂.Leaf B α u)]
    (hm : Measurable (QuantumComp₂.leafEquiv B α).symm) (x : QuantumComp₂ L spec A B α)
    (ρ : SubState A) :
    R.outcomeLaw₂ I x ρ = (R.outcomeLaw I x ρ).map (QuantumComp₂.leafEquiv B α).symm := by
  ext s hs
  rw [Measure.map_apply hm hs]
  change (R.run₂ I x).outcomeMeasure (ρ.prod R.init) s =
    (R.run I x).outcomeMeasure (ρ.prod R.init) ((QuantumComp₂.leafEquiv B α).symm ⁻¹' s)
  rw [SubInstrument.outcomeMeasure_apply _ _ hs, DSubInstrument.outcomeMeasure_apply _ _ (hm hs)]
  conv_rhs => rw [← (QuantumComp₂.leafEquiv B α).tsum_eq]
  refine tsum_congr fun a ↦ congrArg₂ (· * ·) rfl ?_
  classical
  simp only [Set.indicator_apply, Set.mem_preimage, Equiv.symm_apply_apply, Pi.one_apply]

/-- The law of a relabelled value of a fixed-register program is the general observed law, read
through the value `(leafEquiv B α).symm p` of each leaf `p`. No measurability is needed. -/
theorem outcomeLaw₂_map_eq_outcomeLawWith {γ : Type*} [MeasurableSpace γ] (g : α → γ)
    (x : QuantumComp₂ L spec A B α) (ρ : SubState A) :
    R.outcomeLaw₂ I (x.map g) ρ =
      R.outcomeLawWith I x ρ fun p ↦ g ((QuantumComp₂.leafEquiv B α).symm p) := by
  rw [outcomeLaw₂, run₂_map, SubInstrument.outcomeMeasure_map]
  exact Measure.sum_comp_equiv (QuantumComp₂.leafEquiv B α) fun p ↦
    ENNReal.ofReal (R.jointPost I x ρ p).matrix.trace.re •
      Measure.dirac (g ((QuantumComp₂.leafEquiv B α).symm p))

/-- The law of the value of a fixed-register program is the general observed law, read through
the value of each leaf. No measurability is needed. -/
theorem outcomeLaw₂_eq_outcomeLawWith [MeasurableSpace α] (x : QuantumComp₂ L spec A B α)
    (ρ : SubState A) :
    R.outcomeLaw₂ I x ρ = R.outcomeLawWith I x ρ (QuantumComp₂.leafEquiv B α).symm := by
  have h := R.outcomeLaw₂_map_eq_outcomeLawWith I id x ρ
  rw [QuantumComp₂.map_id] at h
  exact h

/-- The matrix of the joint post-state of a fixed-register program. -/
@[simp]
theorem matrix_jointPost₂ (x : QuantumComp₂ L spec A B α) (ρ : SubState A) (a : α) :
    (R.jointPost₂ I x ρ a).matrix = (R.run₂ I x).branch a (ρ.matrix ⊗ₖ R.init.matrix) :=
  rfl

/-- The reduced post-state has the trace of the joint post-state. -/
theorem trace_reducedPost₂ (x : QuantumComp₂ L spec A B α) (ρ : SubState A) (a : α) :
    (R.reducedPost₂ I x ρ a).matrix.trace = (R.jointPost₂ I x ρ a).matrix.trace :=
  MatrixMap.trace_traceRight _

/-- Outcome laws of fixed-register programs are subprobability measures. -/
instance [MeasurableSpace α] (x : QuantumComp₂ L spec A B α) (ρ : SubState A) :
    IsSubprobabilityMeasure (R.outcomeLaw₂ I x ρ) :=
  SubInstrument.outcomeMeasure.instIsSubprobabilityMeasure _ _

/-- The weight of a single value is the trace of the joint post-state. -/
theorem outcomeLaw₂_apply_singleton [MeasurableSpace α] [MeasurableSingletonClass α]
    (x : QuantumComp₂ L spec A B α) (ρ : SubState A) (a : α) :
    R.outcomeLaw₂ I x ρ {a} = ENNReal.ofReal (R.jointPost₂ I x ρ a).matrix.trace.re :=
  SubInstrument.outcomeMeasure_apply_singleton _ _ a

/-- When the run is lossless, the outcome law has the product of the traces of `ρ` and `init`
as its total mass. -/
theorem outcomeLaw₂_apply_univ_of_lossless [MeasurableSpace α] {x : QuantumComp₂ L spec A B α}
    (hx : (R.run₂ I x).Lossless) (ρ : SubState A) :
    R.outcomeLaw₂ I x ρ Set.univ =
      ENNReal.ofReal (ρ.matrix.trace.re * R.init.matrix.trace.re) := by
  rw [outcomeLaw₂, hx.outcomeMeasure_apply_univ, SubState.trace_re_prod]

end QuantumRuntime

end Quantum
