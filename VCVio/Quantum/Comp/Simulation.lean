/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.Runtime

/-!
# Simulation of runtimes

Two runtimes `R₁` and `R₂` for the same signature are related by a linear map
`V : MatrixMap R₁.D R₂.D` between the operators on their registers when every step of `R₂`
after `id ⊗ V` is `id ⊗ V` after the matching step of `R₁`:

`(R₂.step i).branch r ∘ₗ (id ⊗ V) = (id ⊗ V) ∘ₗ (R₁.step i).branch r`.

Then every program, under any interpretation of its local operations, run against `R₂` after
`id ⊗ V` is `id ⊗ V` after its run against `R₁`, on every leaf `⟨u, y⟩`, with `id ⊗ V` on the
register `u` of that leaf (`Quantum.QuantumRuntime.simulation`). A program has no command on the
runtime register, so the proof is an induction on the program tree. The statement asks nothing of
`V` beyond linearity.

When `V` is trace preserving and sends the initial operator of `R₁` to that of `R₂`, no
observation by the program can tell the runtimes apart: the reduced post-states and the outcome
laws agree (`Quantum.QuantumRuntime.reducedPost_eq_of_simulation` and
`Quantum.QuantumRuntime.outcomeLaw_eq_of_simulation`). An example is a runtime that also counts
the calls in a counter register, against the same runtime without the counter: `V` forgets the
counter by the partial trace over it, from the counting runtime to the stateless one.

A second comparison asks less of the steps: they need only agree on the operators that the
calls of one particular run receive (`Quantum.QuantumRuntime.ForallQueries`). Then the two runs
agree on that input (`Quantum.QuantumRuntime.run_branch_apply_eq_of_forallQueries`).

Each statement is proved for general programs, with the fixed-register forms (`simulation₂`,
`outcomeLaw₂_eq_of_simulation`, ...) as corollaries at the leaves `⟨B, rfl, a⟩`.

## Main definitions

* `Quantum.SubInstrument.Intertwines L₁ L₂ p p'`: on every outcome, `p'` after `L₁` is `L₂`
  after `p`; `Quantum.DSubInstrument.Intertwines` is the dependent form, with a map `L₂ i` on
  the output register of each outcome `i`.
* `Quantum.QuantumRuntime.ForallQueries R I P x ρ`: every call along every branch of the run of
  `x` from `ρ` receives an operator satisfying `P`.

## Main statements

* `Quantum.QuantumRuntime.simulation`.
* `Quantum.QuantumRuntime.reducedPost_eq_of_simulation`,
  `Quantum.QuantumRuntime.outcomeLaw_eq_of_simulation`.
* `Quantum.QuantumRuntime.run_branch_apply_eq_of_forallQueries`: two runtimes whose steps agree
  on the operators the calls of a run receive give the same run on that input. This is the
  general form of "the oracle is only seen where it is queried".
-/

public section

open MeasureTheory
open scoped Kronecker

universe u v u₁ v₁ w

namespace Quantum

namespace SubInstrument

variable {X X' Y Y' Z Z' : Type*} [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y'] [Fintype Z]
  [Fintype Z'] {α β : Type*}

/-! ## Intertwining -/

/-- `p'` simulates `p` through `L₁` on inputs and `L₂` on outputs: on every outcome `a`,
`p'.branch a ∘ₗ L₁ = L₂ ∘ₗ p.branch a`. -/
@[expose]
def Intertwines (L₁ : MatrixMap X X') (L₂ : MatrixMap Y Y') (p : SubInstrument X Y α)
    (p' : SubInstrument X' Y' α) : Prop :=
  ∀ a, p'.branch a ∘ₗ L₁ = L₂ ∘ₗ p.branch a

/-- A step, then a step without outcome, then returning the first outcome: the branch at `a` is
the second step after the branch of the first at `a`. -/
theorem branch_bind_bind_unit_pure (p : SubInstrument X Y α) (u : SubInstrument Y Z Unit)
    (a : α) :
    (p.bind fun a' ↦ u.bind fun _ ↦ SubInstrument.pure a').branch a =
      u.branch () ∘ₗ p.branch a :=
  LinearMap.ext fun ρ ↦ by
    rw [branch_bind_apply, tsum_eq_single a fun a' ha' ↦ by
        rw [branch_bind_unit, branch_pure_of_ne (Ne.symm ha'), LinearMap.zero_comp,
          LinearMap.zero_apply],
      branch_bind_unit, branch_pure_self, LinearMap.id_comp, LinearMap.comp_apply]

/-- Two subinstruments whose branches leave operators of the same trace on two substates, on
every outcome, have the same outcome measures on them. -/
theorem outcomeMeasure_congr [MeasurableSpace α] {p : SubInstrument X Y α}
    {p' : SubInstrument X' Y' α} {ρ : SubState X} {ρ' : SubState X'}
    (h : ∀ a, (p.branch a ρ.matrix).trace = (p'.branch a ρ'.matrix).trace) :
    p.outcomeMeasure ρ = p'.outcomeMeasure ρ' := by
  rw [outcomeMeasure_eq_sum, outcomeMeasure_eq_sum]
  exact congrArg Measure.sum <| funext fun a ↦ by rw [h a]

namespace Intertwines

/-- `pure a` intertwines with itself through any map. -/
theorem pure (L : MatrixMap X X') (a : α) :
    Intertwines L L (SubInstrument.pure a) (SubInstrument.pure a) := fun a' ↦ by
  obtain rfl | h := eq_or_ne a' a
  · rw [branch_pure_self, branch_pure_self, LinearMap.id_comp, LinearMap.comp_id]
  · rw [branch_pure_of_ne h, branch_pure_of_ne h, LinearMap.zero_comp, LinearMap.comp_zero]

/-- Intertwining is preserved by sequencing. -/
theorem bind {L₁ : MatrixMap X X'} {L₂ : MatrixMap Y Y'} {L₃ : MatrixMap Z Z'}
    {p : SubInstrument X Y α} {p' : SubInstrument X' Y' α} {k : α → SubInstrument Y Z β}
    {k' : α → SubInstrument Y' Z' β} (hp : Intertwines L₁ L₂ p p')
    (hk : ∀ a, Intertwines L₂ L₃ (k a) (k' a)) :
    Intertwines L₁ L₃ (p.bind k) (p'.bind k') := fun b ↦ LinearMap.ext fun ρ ↦ by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, branch_bind_apply, branch_bind_apply,
    MatrixMap.map_tsum L₃ (f := fun a ↦ (k a).branch b (p.branch a ρ))
      ((p.isCPTNIFamily.comp_eval (fun a ↦ (k a).isCPTNIFamily) b).summable_apply ρ)]
  refine tsum_congr fun a ↦ ?_
  have h₁ := LinearMap.congr_fun (hp a) ρ
  have h₂ := LinearMap.congr_fun (hk a b) (p.branch a ρ)
  simp only [LinearMap.comp_apply] at h₁ h₂
  rw [h₁, h₂]

/-- Framing by a common ancilla preserves intertwining. -/
theorem frame {L₁ : MatrixMap X X'} {L₂ : MatrixMap Y Y'} {p : SubInstrument X Y α}
    {p' : SubInstrument X' Y' α} (h : Intertwines L₁ L₂ p p') (E : Type*) [Fintype E] :
    Intertwines (L₁.amplify E) (L₂.amplify E) (p.frame E) (p'.frame E) := fun a ↦ by
  rw [branch_frame_apply, branch_frame_apply, ← MatrixMap.amplify_comp, h a,
    MatrixMap.amplify_comp]

/-- A subinstrument framed by two ancillas intertwines through a map `id ⊗ V` between the
ancillas. -/
theorem frame_amplifyLeft (p : SubInstrument X Y α) {R S : Type*} [Fintype R] [Fintype S]
    (V : MatrixMap R S) :
    Intertwines (V.amplifyLeft X) (V.amplifyLeft Y) (p.frame R) (p.frame S) := fun a ↦ by
  rw [branch_frame_apply, branch_frame_apply, MatrixMap.amplify_comp_amplifyLeft]

end Intertwines


end SubInstrument

namespace DSubInstrument

variable {X X' : Type*} [Fintype X] [Fintype X'] {ι κ : Type*} {B B' : ι → Type*}
  [∀ i, Fintype (B i)] [∀ i, Fintype (B' i)] {C C' : κ → Type*} [∀ c, Fintype (C c)]
  [∀ c, Fintype (C' c)]

/-! ## Intertwining of dependent subinstruments -/

/-- `p'` simulates `p` through `L₁` on inputs and `L₂ i` on the output register of each outcome
`i`: on every outcome, `p'.branch i ∘ₗ L₁ = L₂ i ∘ₗ p.branch i`. -/
@[expose]
def Intertwines (L₁ : MatrixMap X X') (L₂ : ∀ i, MatrixMap (B i) (B' i))
    (p : DSubInstrument X ι B) (p' : DSubInstrument X' ι B') : Prop :=
  ∀ i, p'.branch i ∘ₗ L₁ = L₂ i ∘ₗ p.branch i

/-- Two dependent subinstruments whose branches leave operators of the same trace on two
substates, on every outcome, have the same outcome measures on them. -/
theorem outcomeMeasure_congr [MeasurableSpace ι] {p : DSubInstrument X ι B}
    {p' : DSubInstrument X' ι B'} {ρ : SubState X} {ρ' : SubState X'}
    (h : ∀ i, (p.branch i ρ.matrix).trace = (p'.branch i ρ'.matrix).trace) :
    p.outcomeMeasure ρ = p'.outcomeMeasure ρ' := by
  rw [outcomeMeasure_eq_sum, outcomeMeasure_eq_sum]
  exact congrArg Measure.sum <| funext fun i ↦ by rw [h i]

namespace Intertwines

/-- `ret i` intertwines with itself through any family of maps. -/
theorem ret (L : ∀ i, MatrixMap (B i) (B' i)) (i : ι) :
    Intertwines (L i) L (DSubInstrument.ret B i) (DSubInstrument.ret B' i) := fun j ↦ by
  obtain rfl | h := eq_or_ne j i
  · rw [branch_ret_self, branch_ret_self, LinearMap.id_comp, LinearMap.comp_id]
  · rw [branch_ret_of_ne B h, branch_ret_of_ne B' h, LinearMap.zero_comp, LinearMap.comp_zero]

/-- Intertwining is preserved by sequencing. -/
theorem bind {L₁ : MatrixMap X X'} {L₂ : ∀ i, MatrixMap (B i) (B' i)}
    {L₃ : ∀ c, MatrixMap (C c) (C' c)} {p : DSubInstrument X ι B} {p' : DSubInstrument X' ι B'}
    {k : (i : ι) → DSubInstrument (B i) κ C} {k' : (i : ι) → DSubInstrument (B' i) κ C'}
    (hp : Intertwines L₁ L₂ p p') (hk : ∀ i, Intertwines (L₂ i) L₃ (k i) (k' i)) :
    Intertwines L₁ L₃ (p.bind k) (p'.bind k') := fun c ↦ LinearMap.ext fun ρ ↦ by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, branch_bind_apply, branch_bind_apply,
    MatrixMap.map_tsum (L₃ c) (f := fun i ↦ (k i).branch c (p.branch i ρ))
      ((p.isCPTNIFamily.comp_eval (fun i ↦ (k i).isCPTNIFamily) c).summable_apply ρ)]
  refine tsum_congr fun i ↦ ?_
  have h₁ := LinearMap.congr_fun (hp i) ρ
  have h₂ := LinearMap.congr_fun (hk i c) (p.branch i ρ)
  simp only [LinearMap.comp_apply] at h₁ h₂
  rw [h₁, h₂]

/-- A dependent subinstrument framed by two ancillas intertwines through a map `id ⊗ V` between
the ancillas. -/
theorem frame_amplifyLeft (p : DSubInstrument X ι B) {R S : Type*} [Fintype R] [Fintype S]
    (V : MatrixMap R S) :
    Intertwines (V.amplifyLeft X) (fun i ↦ V.amplifyLeft (B i)) (p.frame R) (p.frame S) :=
  fun i ↦ by rw [branch_frame_apply, branch_frame_apply, MatrixMap.amplify_comp_amplifyLeft]

end Intertwines

end DSubInstrument

/-- Intertwining subinstruments have intertwining dependent forms. -/
theorem SubInstrument.Intertwines.toD {X X' Y Y' : Type*} [Fintype X] [Fintype X'] [Fintype Y]
    [Fintype Y'] {α : Type*} {L₁ : MatrixMap X X'} {L₂ : MatrixMap Y Y'}
    {p : SubInstrument X Y α} {p' : SubInstrument X' Y' α} (h : Intertwines L₁ L₂ p p') :
    DSubInstrument.Intertwines L₁ (fun _ ↦ L₂) (SubInstrument.toD p) (SubInstrument.toD p') :=
  h

namespace QuantumRuntime

open SubInstrument

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} (I : L.Interp)
  {X : QReg → Type w} {A B : QReg} {α : Type w}

section relabel

variable {R S : Type*} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
  (V : MatrixMap R S)

/-- The relabelling before a call intertwines through `id ⊗ V` on both sides. -/
theorem intertwines_relabel_queryEquivIn {A I E : Type*} [Fintype A] [Fintype I] [Fintype E]
    [DecidableEq A] [DecidableEq I] [DecidableEq E] (ℓ : A ≃ I × E) :
    Intertwines (V.amplifyLeft A) ((V.amplifyLeft I).amplify E)
      (relabel (queryEquivIn ℓ R)) (relabel (queryEquivIn ℓ S)) := fun u ↦ by
  refine LinearMap.ext fun ρ ↦ ?_
  ext x y
  simp only [LinearMap.comp_apply, relabel_branch_apply]
  rfl

/-- The relabelling after a call intertwines through `id ⊗ V` on both sides. -/
theorem intertwines_relabel_queryEquivOut (O E : Type*) [Fintype O] [Fintype E] [DecidableEq O]
    [DecidableEq E] :
    Intertwines ((V.amplifyLeft O).amplify E) (V.amplifyLeft (O × E))
      (relabel (queryEquivOut O R E)) (relabel (queryEquivOut O S E)) := fun u ↦ by
  refine LinearMap.ext fun ρ ↦ ?_
  ext x y
  simp only [LinearMap.comp_apply, relabel_branch_apply]
  rfl

end relabel

variable {R₁ R₂ : QuantumRuntime spec} {V : MatrixMap R₁.D R₂.D}

/-- A call intertwines through `id ⊗ V` when the port's steps do. -/
theorem intertwines_queryStep {i : spec.Port}
    (h : Intertwines (V.amplifyLeft (spec.In i)) (V.amplifyLeft (spec.Out i)) (R₁.step i)
      (R₂.step i))
    (E : QReg) (ℓ : A ≃ spec.In i × E) :
    Intertwines (V.amplifyLeft A) (V.amplifyLeft (QReg.of (spec.Out i × E)))
      (R₁.queryStep i E ℓ) (R₂.queryStep i E ℓ) :=
  (intertwines_relabel_queryEquivIn V ℓ).bind fun _ ↦ (h.frame E).bind fun r ↦
    (intertwines_relabel_queryEquivOut V (spec.Out i) E).bind fun _ ↦ Intertwines.pure _ r

/-! ## Simulation -/

/-- The runs of a program against two runtimes intertwine through `id ⊗ V`, with `id ⊗ V` on the
register of each leaf. -/
theorem intertwines_run
    (h : ∀ i r, (R₂.step i).branch r ∘ₗ V.amplifyLeft (spec.In i) =
      V.amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    (x : QuantumComp L spec X A) :
    DSubInstrument.Intertwines (V.amplifyLeft A) (fun p : Σ u, X u ↦ V.amplifyLeft p.1)
      (R₁.run I x) (R₂.run I x) := by
  induction x using QuantumComp.inductionOn with
  | pure _ y =>
    exact DSubInstrument.Intertwines.ret (B := fun p : Σ u, X u ↦ p.1 × R₁.D)
      (B' := fun p : Σ u, X u ↦ p.1 × R₂.D) (fun p ↦ V.amplifyLeft p.1) ⟨_, y⟩
  | primBind _ o k ih =>
    rw [run_primBind, run_primBind]
    exact (DSubInstrument.Intertwines.frame_amplifyLeft (I o) V).bind ih
  | queryBind _ i E ℓ k ih =>
    rw [run_queryBind, run_queryBind]
    exact (intertwines_queryStep (fun r ↦ h i r) E ℓ).toD.bind ih

/-- **Simulation.** If every step of `R₂` after `id ⊗ V` is `id ⊗ V` after the matching step of
`R₁`, then every program run against `R₂` after `id ⊗ V` is `id ⊗ V` after its run against
`R₁`, on every leaf `⟨u, y⟩`, with `id ⊗ V` on the register `u` of that leaf. -/
theorem simulation
    (h : ∀ i r, (R₂.step i).branch r ∘ₗ V.amplifyLeft (spec.In i) =
      V.amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    (x : QuantumComp L spec X A) (p : Σ u, X u) :
    (R₂.run I x).branch p ∘ₗ V.amplifyLeft A = V.amplifyLeft p.1 ∘ₗ (R₁.run I x).branch p :=
  intertwines_run I h x p

/-- **Simulation**, for fixed-register programs: on every outcome `a`, the run against `R₂` after
`id ⊗ V` is `id ⊗ V` after the run against `R₁`. -/
theorem simulation₂
    (h : ∀ i r, (R₂.step i).branch r ∘ₗ V.amplifyLeft (spec.In i) =
      V.amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    (x : QuantumComp₂ L spec A B α) (a : α) :
    (R₂.run₂ I x).branch a ∘ₗ V.amplifyLeft A = V.amplifyLeft B ∘ₗ (R₁.run₂ I x).branch a :=
  simulation I h x ⟨B, rfl, a⟩

/-- Under a simulation, the joint post-state against `R₂` is `id ⊗ V` of the joint post-state
against `R₁`, when `V` sends the initial operator of `R₁` to that of `R₂`. -/
theorem matrix_jointPost_of_simulation
    (h : ∀ i r, (R₂.step i).branch r ∘ₗ V.amplifyLeft (spec.In i) =
      V.amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    (hinit : V R₁.init.matrix = R₂.init.matrix) (x : QuantumComp L spec X A) (ρ : SubState A)
    (p : Σ u, X u) :
    (R₂.jointPost I x ρ p).matrix = V.amplifyLeft p.1 (R₁.jointPost I x ρ p).matrix := by
  rw [matrix_jointPost, matrix_jointPost, ← hinit, ← MatrixMap.amplifyLeft_kronecker,
    ← LinearMap.comp_apply, simulation I h x p, LinearMap.comp_apply]

/-- **Indistinguishability.** Under a simulation through a trace-preserving `V` that sends the
initial operator of `R₁` to that of `R₂`, the reduced post-states of every program agree on
every leaf. -/
theorem reducedPost_eq_of_simulation
    (h : ∀ i r, (R₂.step i).branch r ∘ₗ V.amplifyLeft (spec.In i) =
      V.amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    (hV : V.IsTP) (hinit : V R₁.init.matrix = R₂.init.matrix) (x : QuantumComp L spec X A)
    (ρ : SubState A) (p : Σ u, X u) : R₂.reducedPost I x ρ p = R₁.reducedPost I x ρ p :=
  SubState.ext <| by
    rw [reducedPost, reducedPost, SubState.matrix_traceRight, SubState.matrix_traceRight,
      matrix_jointPost_of_simulation I h hinit x ρ p, ← LinearMap.comp_apply,
      MatrixMap.traceRight_comp_amplifyLeft hV]

/-- Under the hypotheses of `reducedPost_eq_of_simulation`, the joint post-states of every
program have the same trace. -/
theorem trace_jointPost_eq_of_simulation
    (h : ∀ i r, (R₂.step i).branch r ∘ₗ V.amplifyLeft (spec.In i) =
      V.amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    (hV : V.IsTP) (hinit : V R₁.init.matrix = R₂.init.matrix) (x : QuantumComp L spec X A)
    (ρ : SubState A) (p : Σ u, X u) :
    (R₂.jointPost I x ρ p).matrix.trace = (R₁.jointPost I x ρ p).matrix.trace := by
  rw [← trace_reducedPost, ← trace_reducedPost, reducedPost_eq_of_simulation I h hV hinit]

/-- **Indistinguishability.** Under a simulation through a trace-preserving `V` that sends the
initial operator of `R₁` to that of `R₂`, the outcome laws of every program agree. -/
theorem outcomeLaw_eq_of_simulation [MeasurableSpace (Σ u, X u)]
    (h : ∀ i r, (R₂.step i).branch r ∘ₗ V.amplifyLeft (spec.In i) =
      V.amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    (hV : V.IsTP) (hinit : V R₁.init.matrix = R₂.init.matrix) (x : QuantumComp L spec X A)
    (ρ : SubState A) : R₂.outcomeLaw I x ρ = R₁.outcomeLaw I x ρ :=
  DSubInstrument.outcomeMeasure_congr fun p ↦ trace_jointPost_eq_of_simulation I h hV hinit x ρ p

/-- Under a simulation, the joint post-state of a fixed-register program against `R₂` is
`id ⊗ V` of the joint post-state against `R₁`, when `V` sends the initial operator of `R₁` to
that of `R₂`. -/
theorem matrix_jointPost₂_of_simulation
    (h : ∀ i r, (R₂.step i).branch r ∘ₗ V.amplifyLeft (spec.In i) =
      V.amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    (hinit : V R₁.init.matrix = R₂.init.matrix) (x : QuantumComp₂ L spec A B α) (ρ : SubState A)
    (a : α) : (R₂.jointPost₂ I x ρ a).matrix = V.amplifyLeft B (R₁.jointPost₂ I x ρ a).matrix :=
  matrix_jointPost_of_simulation I h hinit x ρ ⟨B, rfl, a⟩

/-- **Indistinguishability** for fixed-register programs: the reduced post-states agree. -/
theorem reducedPost₂_eq_of_simulation
    (h : ∀ i r, (R₂.step i).branch r ∘ₗ V.amplifyLeft (spec.In i) =
      V.amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    (hV : V.IsTP) (hinit : V R₁.init.matrix = R₂.init.matrix) (x : QuantumComp₂ L spec A B α)
    (ρ : SubState A) (a : α) : R₂.reducedPost₂ I x ρ a = R₁.reducedPost₂ I x ρ a :=
  reducedPost_eq_of_simulation I h hV hinit x ρ ⟨B, rfl, a⟩

/-- **Indistinguishability** for fixed-register programs: the laws of the returned value
agree. -/
theorem outcomeLaw₂_eq_of_simulation [MeasurableSpace α]
    (h : ∀ i r, (R₂.step i).branch r ∘ₗ V.amplifyLeft (spec.In i) =
      V.amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    (hV : V.IsTP) (hinit : V R₁.init.matrix = R₂.init.matrix) (x : QuantumComp₂ L spec A B α)
    (ρ : SubState A) : R₂.outcomeLaw₂ I x ρ = R₁.outcomeLaw₂ I x ρ :=
  SubInstrument.outcomeMeasure_congr fun a ↦
    trace_jointPost_eq_of_simulation I h hV hinit x ρ ⟨B, rfl, a⟩

/-! ## Agreement on the states presented to the calls -/

section forallQueries

variable (R : QuantumRuntime spec)

/-- A predicate `P` holds of the operator presented to every call along every branch of the run
from `ρ`: before a call of port `i` with remainder `E`, the operator on `(In i × D) × E` that the
port's step receives. -/
@[expose]
def forallQueriesAux
    (P : ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop) :
    {A : QReg} → IPFunctor.IFreeM (QuantumComp.toIPFunctor L spec) X A →
      Matrix (A × R.D) (A × R.D) ℂ → Prop
  | _, .pure _, _ => True
  | _, .liftBind (.prim o) k, ρ =>
      ∀ b, forallQueriesAux P (k (ULift.up b)) (((I o).frame R.D).branch b ρ)
  | _, .liftBind (.query i E ℓ) k, ρ =>
      P i E ((relabel (queryEquivIn ℓ R.D)).branch () ρ) ∧
        ∀ r, forallQueriesAux P (k (ULift.up r)) ((R.queryStep i E ℓ).branch r ρ)

/-- Every call along every branch of the run of `x` under `I` from the operator `ρ` on `A × D`,
including branches reached with weight zero, receives an operator satisfying `P`. When `ρ` is
positive semidefinite, a branch of weight zero receives the zero operator, so the condition is
then also asked of zero. -/
@[expose]
def ForallQueries
    (P : ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop)
    (x : QuantumComp L spec X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) : Prop :=
  R.forallQueriesAux I P x ρ

variable {R}
variable {P : ∀ (i : spec.Port) (E : QReg),
  Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop}

/-- A program that stops at once makes no call. -/
@[simp]
theorem forallQueries_pure (y : X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.ForallQueries I P (QuantumComp.pure (L := L) y) ρ :=
  trivial

/-- After a local operation, the condition is checked on every branch. -/
theorem forallQueries_primBind_iff (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L spec X (L.next o b))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.ForallQueries I P (QuantumComp.primBind o k) ρ ↔
      ∀ b, R.ForallQueries I P (k b) (((I o).frame R.D).branch b ρ) :=
  Iff.rfl

/-- A call checks the condition on the operator it presents to the port, and then on every
branch. -/
theorem forallQueries_queryBind_iff (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E)))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.ForallQueries I P (QuantumComp.queryBind i E ℓ k) ρ ↔
      P i E ((relabel (queryEquivIn ℓ R.D)).branch () ρ) ∧
        ∀ r, R.ForallQueries I P (k r) ((R.queryStep i E ℓ).branch r ρ) :=
  Iff.rfl

/-- After a local subinstrument of a program over instruments, the condition is checked on every
branch. -/
theorem forallQueries_act_bind_iff {C : QReg} {β : Type w} (p : SubInstrument A B β)
    (k : β → QComp spec B C α) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.ForallQueries .instruments P ((QComp.act p).bind k) ρ ↔
      ∀ b, R.ForallQueries .instruments P (k b) ((p.frame R.D).branch b ρ) :=
  Iff.rfl

/-- A weaker condition on the presented operators also holds. -/
theorem ForallQueries.mono {P' : ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop}
    (hP : ∀ i E σ, P i E σ → P' i E σ) {x : QuantumComp L spec X A}
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hx : R.ForallQueries I P x ρ) :
    R.ForallQueries I P' x ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => trivial
  | primBind _ o k ih => exact fun b ↦ ih b (hx b)
  | queryBind _ i E ℓ k ih => exact ⟨hP i E _ hx.1, fun r ↦ ih r (hx.2 r)⟩

/-- A call applied to an operator: relabel, apply the port's step framed by the remainder, and
relabel back. -/
theorem queryStep_branch_apply (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (r : spec.Result i) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    (R.queryStep i E ℓ).branch r ρ =
      (relabel (queryEquivOut (spec.Out i) R.D E)).branch ()
        (((R.step i).frame E).branch r ((relabel (queryEquivIn ℓ R.D)).branch () ρ)) := by
  rw [queryStep, branch_bind_unit, branch_bind_bind_unit_pure]
  rfl

/-- A call on a basis state `|a, d⟩` of `A × D`: the port's step acts on the exposed factor
`(ℓ a).1` and the runtime register, the remainder `(ℓ a).2` is carried along, and the result is
relabelled back. -/
theorem queryStep_branch_single (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (r : spec.Result i) (a : A) (d : R.D) :
    (R.queryStep i E ℓ).branch r (Matrix.single (a, d) (a, d) 1) =
      (relabel (queryEquivOut (spec.Out i) R.D E)).branch ()
        ((R.step i).branch r (Matrix.single ((ℓ a).1, d) ((ℓ a).1, d) 1) ⊗ₖ
          Matrix.single (ℓ a).2 (ℓ a).2 1) := by
  rw [queryStep_branch_apply, branch_relabel (queryEquivIn ℓ R.D),
    conj_basisMatrix_equiv_single, queryEquivIn_apply, branch_frame_single]

end forallQueries

/-- **Only the presented operators matter.** Two runtimes on the same register whose steps,
framed by any remainder, agree on every operator satisfying `P`, run a program to the same
branches on an operator `ρ` from which every call of the run against the first runtime receives
an operator satisfying `P`. -/
theorem run_branch_apply_eq_of_forallQueries {D : QReg} {σ₁ σ₂ : SubState D}
    {s₁ s₂ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
    {P : ∀ (i : spec.Port) (E : QReg), Matrix ((spec.In i × D) × E) ((spec.In i × D) × E) ℂ → Prop}
    (hs : ∀ i E σ, P i E σ → ∀ r, ((s₁ i).frame E).branch r σ = ((s₂ i).frame E).branch r σ)
    {x : QuantumComp L spec X A} {ρ : Matrix (A × D) (A × D) ℂ}
    (hx : (QuantumRuntime.mk D σ₁ s₁).ForallQueries I P x ρ) (p : Σ u, X u) :
    ((QuantumRuntime.mk D σ₁ s₁).run I x).branch p ρ =
      ((QuantumRuntime.mk D σ₂ s₂).run I x).branch p ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => rfl
  | primBind _ o k ih =>
    rw [run_primBind, run_primBind, DSubInstrument.branch_bind_apply,
      DSubInstrument.branch_bind_apply]
    exact tsum_congr fun b ↦ ih b (hx b)
  | queryBind _ i E ℓ k ih =>
    rw [run_queryBind, run_queryBind, DSubInstrument.branch_bind_apply,
      DSubInstrument.branch_bind_apply]
    refine tsum_congr fun r ↦ ?_
    have hq : ((QuantumRuntime.mk D σ₁ s₁).queryStep i E ℓ).branch r ρ =
        ((QuantumRuntime.mk D σ₂ s₂).queryStep i E ℓ).branch r ρ := by
      rw [queryStep_branch_apply, queryStep_branch_apply]
      exact congrArg _ (hs i E _ hx.1 r)
    rw [branch_toD_apply, branch_toD_apply, ← hq]
    exact ih r (hx.2 r)

/-- **Only the presented operators matter**, for fixed-register programs. -/
theorem run₂_branch_apply_eq_of_forallQueries {D : QReg} {σ₁ σ₂ : SubState D}
    {s₁ s₂ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
    {P : ∀ (i : spec.Port) (E : QReg), Matrix ((spec.In i × D) × E) ((spec.In i × D) × E) ℂ → Prop}
    (hs : ∀ i E σ, P i E σ → ∀ r, ((s₁ i).frame E).branch r σ = ((s₂ i).frame E).branch r σ)
    {x : QuantumComp₂ L spec A B α} {ρ : Matrix (A × D) (A × D) ℂ}
    (hx : (QuantumRuntime.mk D σ₁ s₁).ForallQueries I P x ρ) (a : α) :
    ((QuantumRuntime.mk D σ₁ s₁).run₂ I x).branch a ρ =
      ((QuantumRuntime.mk D σ₂ s₂).run₂ I x).branch a ρ :=
  run_branch_apply_eq_of_forallQueries (σ₂ := σ₂) I hs hx ⟨B, rfl, a⟩

/-- The condition on the presented operators transfers between two runtimes whose steps agree
on the operators satisfying it. -/
theorem ForallQueries.of_congr {D : QReg} {σ₁ σ₂ : SubState D}
    {s₁ s₂ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
    {P : ∀ (i : spec.Port) (E : QReg), Matrix ((spec.In i × D) × E) ((spec.In i × D) × E) ℂ → Prop}
    (hs : ∀ i E σ, P i E σ → ∀ r, ((s₁ i).frame E).branch r σ = ((s₂ i).frame E).branch r σ)
    {x : QuantumComp L spec X A} {ρ : Matrix (A × D) (A × D) ℂ}
    (hx : (QuantumRuntime.mk D σ₁ s₁).ForallQueries I P x ρ) :
    (QuantumRuntime.mk D σ₂ s₂).ForallQueries I P x ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => trivial
  | primBind _ o k ih => exact fun b ↦ ih b (hx b)
  | queryBind _ i E ℓ k ih =>
    refine ⟨hx.1, fun (r : spec.Result i) ↦ ?_⟩
    have hq : ((QuantumRuntime.mk D σ₁ s₁).queryStep i E ℓ).branch r ρ =
        ((QuantumRuntime.mk D σ₂ s₂).queryStep i E ℓ).branch r ρ := by
      rw [queryStep_branch_apply, queryStep_branch_apply]
      exact congrArg _ (hs i E _ hx.1 r)
    rw [← hq]
    exact ih r (hx.2 r)

/-- Under the hypotheses of `run_branch_apply_eq_of_forallQueries` from the joint substate
`ρ ⊗ init`, with the same initial substate, the outcome laws agree. -/
theorem outcomeLaw_eq_of_forallQueries [MeasurableSpace (Σ u, X u)] {D : QReg} {σ : SubState D}
    {s₁ s₂ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
    {P : ∀ (i : spec.Port) (E : QReg), Matrix ((spec.In i × D) × E) ((spec.In i × D) × E) ℂ → Prop}
    (hs : ∀ i E σ, P i E σ → ∀ r, ((s₁ i).frame E).branch r σ = ((s₂ i).frame E).branch r σ)
    {x : QuantumComp L spec X A} {ρ : SubState A}
    (hx : (QuantumRuntime.mk D σ s₁).ForallQueries I P x (ρ.prod σ).matrix) :
    (QuantumRuntime.mk D σ s₁).outcomeLaw I x ρ = (QuantumRuntime.mk D σ s₂).outcomeLaw I x ρ :=
  DSubInstrument.outcomeMeasure_congr fun p ↦ by
    rw [run_branch_apply_eq_of_forallQueries (σ₂ := σ) I hs hx p]

/-- Under the hypotheses of `outcomeLaw_eq_of_forallQueries`, the joint post-states agree. -/
theorem jointPost_eq_of_forallQueries {D : QReg} {σ : SubState D}
    {s₁ s₂ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
    {P : ∀ (i : spec.Port) (E : QReg), Matrix ((spec.In i × D) × E) ((spec.In i × D) × E) ℂ → Prop}
    (hs : ∀ i E σ, P i E σ → ∀ r, ((s₁ i).frame E).branch r σ = ((s₂ i).frame E).branch r σ)
    {x : QuantumComp L spec X A} {ρ : SubState A}
    (hx : (QuantumRuntime.mk D σ s₁).ForallQueries I P x (ρ.prod σ).matrix) (p : Σ u, X u) :
    (QuantumRuntime.mk D σ s₁).jointPost I x ρ p = (QuantumRuntime.mk D σ s₂).jointPost I x ρ p :=
  SubState.ext <| run_branch_apply_eq_of_forallQueries (σ₂ := σ) I hs hx p

/-- Under the hypotheses of `run_branch_apply_eq_of_forallQueries` from the joint substate
`ρ ⊗ init`, with the same initial substate, the laws of the value returned by a fixed-register
program agree. -/
theorem outcomeLaw₂_eq_of_forallQueries [MeasurableSpace α] {D : QReg} {σ : SubState D}
    {s₁ s₂ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
    {P : ∀ (i : spec.Port) (E : QReg), Matrix ((spec.In i × D) × E) ((spec.In i × D) × E) ℂ → Prop}
    (hs : ∀ i E σ, P i E σ → ∀ r, ((s₁ i).frame E).branch r σ = ((s₂ i).frame E).branch r σ)
    {x : QuantumComp₂ L spec A B α} {ρ : SubState A}
    (hx : (QuantumRuntime.mk D σ s₁).ForallQueries I P x (ρ.prod σ).matrix) :
    (QuantumRuntime.mk D σ s₁).outcomeLaw₂ I x ρ =
      (QuantumRuntime.mk D σ s₂).outcomeLaw₂ I x ρ :=
  SubInstrument.outcomeMeasure_congr fun a ↦ by
    rw [run₂_branch_apply_eq_of_forallQueries (σ₂ := σ) I hs hx a]

/-- Under the hypotheses of `outcomeLaw₂_eq_of_forallQueries`, the joint post-states of the
fixed-register program agree. -/
theorem jointPost₂_eq_of_forallQueries {D : QReg} {σ : SubState D}
    {s₁ s₂ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
    {P : ∀ (i : spec.Port) (E : QReg), Matrix ((spec.In i × D) × E) ((spec.In i × D) × E) ℂ → Prop}
    (hs : ∀ i E σ, P i E σ → ∀ r, ((s₁ i).frame E).branch r σ = ((s₂ i).frame E).branch r σ)
    {x : QuantumComp₂ L spec A B α} {ρ : SubState A}
    (hx : (QuantumRuntime.mk D σ s₁).ForallQueries I P x (ρ.prod σ).matrix) (a : α) :
    (QuantumRuntime.mk D σ s₁).jointPost₂ I x ρ a =
      (QuantumRuntime.mk D σ s₂).jointPost₂ I x ρ a :=
  jointPost_eq_of_forallQueries I hs hx ⟨B, rfl, a⟩

end QuantumRuntime

end Quantum
