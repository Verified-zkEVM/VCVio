/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.DSubInstrument

/-!
# Subinstruments and quantum computations

A quantum computation that reports classical outcomes is described by an *instrument*: one
completely positive map per outcome. Run on a state `ρ`, it reports outcome `a` and leaves the
state `branch a ρ`. This state is unnormalized: its trace is the probability of `a`. A computation
that may fail loses trace instead of reporting a failure outcome, so its branches need only be
jointly trace nonincreasing. Such a family is a *subinstrument*, and the trace it loses is the
probability of failure. A subinstrument whose branches sum to a trace-preserving map is
*lossless*, and is an instrument in the usual sense.

`Quantum.SubInstrument A B α` has input system `A`, output system `B` and outcomes in `α`.
It is a countably supported, possibly lossy extension of the finite instruments of Watrous
(see the module references).

## How computations compose

On a fixed register `M`, `SubInstrument M M` is a lawful monad, and the operations mean what they
mean for `OracleComp`, with completely positive maps in place of probabilities. `OracleComp`
is free-monad syntax interpreted by `simulateQ`; subinstruments are semantic state
transformations, observed as measures by `outcomeMeasure` in `VCVio.Quantum.Observe`:

* `pure a` reports `a` and leaves the state unchanged.
* `p.bind k` runs `p`, and on outcome `a` runs `k a` on the state `p` left behind:
  `(p.bind k).branch b ρ = ∑' a, (k a).branch b (p.branch a ρ)`.
* `map f p` relabels outcomes. Outcomes with the same image are merged by adding their branches.
  This coarse-graining forgets classical information; it is not quantum interference.
* `fail` reports nothing: every branch is zero.
* `p.frame R` extends each branch by the identity on a right reference `R`, as `branch a ⊗ id_R`.
  Entanglement can change the outcome-conditioned reference state.

`bind` passes the residual quantum state to the continuation. This is why a quantum computation
cannot be summarized by the probabilities of its outcomes.

## Infinitely many outcomes

The branches form an arbitrary function on `α`, not a finitely supported one. Trace nonincrease
of the finite partial sums makes the family summable on every input
(`Quantum.MatrixMap.IsCPTNIFamily.summable_apply`), only countably many branches are nonzero
(`Quantum.DSubInstrument.countable_support_branch`), and the sum `Quantum.DSubInstrument.total` is
completely positive and trace nonincreasing. No countability assumption is made on `α`.

Infinitely many outcomes are what loops produce. At each round, prepare a fresh `|+⟩`, measure it in
the computational basis, and stop on `0`, returning the number of rounds: the loop stops after round
`n` with probability `2^{-n}`, so every positive `n : ℕ` is an outcome. Loops are not defined in
this library. Their semantics would be the limit of their finite unrollings, and a limit of finitely
supported instruments need not be finitely supported, which is why the model does not require finite
support. A family that vanishes outside a finite set `s` has total map the finite sum over `s`
(`Quantum.DSubInstrument.total_eq_sum`), and `pure`, `ofMap` and `ofKraus` over a finite type
produce such families.

## Main definitions

* `Quantum.SubInstrument A B α`, with `pure`, `bind`, `map`, `fail` and `frame`.
* `Quantum.DSubInstrument.total`: the sum of the branches, which is the action when the outcome
  is discarded.
* `Quantum.DSubInstrument.Lossless`: the total map is trace preserving.
* `Quantum.SubInstrument.ofMap`: the one-outcome subinstrument of a completely positive
  trace-nonincreasing map.
* `Quantum.DSubInstrument.ofKraus`: the measurement with Kraus operators `K a`, one per outcome of a
  finite type, satisfying `∑ a, (K a)† * K a = 1`.

Every branch has a finite Kraus representation (`Quantum.DSubInstrument.exists_kraus_branch`),
even when the outcome type is infinite. For finitely many outcomes,
`Quantum.DSubInstrument.exists_kraus_of_fintype` gives a joint completeness inequality, and
`Quantum.DSubInstrument.Lossless.exists_kraus` gives equality, with operators indexed by
`B × A` on each outcome in the constant-codomain case. For two stages with finitely many
intermediate outcomes,
`Quantum.DSubInstrument.branch_bind_eq_sum_conj_mul` expresses each final branch as a sum of
Kraus maps along paths, with the later operator multiplying on the left.

## Outcome-dependent output systems

`SubInstrument A B α` is an abbreviation for `DSubInstrument A α (fun _ ↦ B)`.
The dependent type is an indexed monad: `ret B i` has input system `B i`.
The exposed reducible `SubInstrument.pure`, `bind`, `frame`, `map`, `fail` and `ofKraus`
facades keep constant-codomain results headed by `SubInstrument`. This lets field notation
infer the output system in composites such as `(p.bind k).map g` and `(p.frame R).map f`.
The constant `SubInstrument.Lossless.bind`, `frame` and `map` lemmas likewise support
proof chains such as `(hp.bind hk).map g` without output-family annotations.

Dependent lemmas apply through these facades by `simp`, and by `rw` unless the rewritten
left side is headed by a facade. Constant restatements such as `SubInstrument.bind_pure`
and `SubInstrument.frame_bind` provide those head-sensitive rewrites; their proofs delegate
to the dependent API. Constant-output operations such as `total` live in `DSubInstrument`
and support field notation on composites. Constructors and the fixed-register `Monad`
instance live in `SubInstrument`.

## References

* J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018.
  Finite instruments and conditional states: equations (2.258)–(2.261), printed p. 112,
  [full PDF p. 120](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf#page=120).
  PDF pages are 1-based. Countable support and possible trace loss extend that finite definition.
-/

public section

open scoped ComplexOrder
open Matrix

universe u w

namespace Quantum

/-- A subinstrument with a fixed output system, the constant-codomain dependent subinstrument. -/
abbrev SubInstrument (A B : Type*) [Fintype A] [Fintype B] (α : Type*) :=
  DSubInstrument A α fun _ ↦ B

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] {α β : Type*}

namespace DSubInstrument

/-- Every finite sum of branches is trace nonincreasing. -/
theorem isTNI_sum (p : DSubInstrument A α (fun _ ↦ B)) (s : Finset α) :
    (∑ a ∈ s, p.branch a).IsTNI :=
  p.isCPTNIFamily.isTNI_sum s

end DSubInstrument

namespace SubInstrument

/-- Construct a subinstrument from completely positive branches with trace-nonincreasing sums. -/
@[expose]
def ofIsTNISum (branch : α → MatrixMap A B) (hcp : ∀ a, (branch a).IsCP)
    (htni : ∀ s : Finset α, (∑ a ∈ s, branch a).IsTNI) : SubInstrument A B α where
  branch := branch
  isCP_branch := hcp
  trace_le := (MatrixMap.IsCPTNIFamily.of_isTNI_sum hcp htni).sum_trace_re_le

/-- The subinstrument that leaves the state unchanged and returns `a`. -/
@[expose, reducible]
protected noncomputable def pure (a : α) : SubInstrument A A α :=
  DSubInstrument.ret (fun _ ↦ A) a

/-- Sequence constant-output subinstruments, passing each outcome to its continuation. -/
@[expose, reducible]
protected noncomputable def bind (p : SubInstrument A B α)
    (k : α → SubInstrument B C β) : SubInstrument A C β :=
  DSubInstrument.bind p k

/-- Extend a constant-output subinstrument by the identity on a right reference system. -/
@[expose, reducible]
noncomputable def frame (p : SubInstrument A B α) (R : Type*) [Fintype R] :
    SubInstrument (A × R) (B × R) α :=
  DSubInstrument.frame p R

/-- The constant-output subinstrument that fails on every input. -/
@[expose, reducible]
protected noncomputable def fail : SubInstrument A B α :=
  DSubInstrument.fail

/-- A constant-output measurement specified by Kraus operators satisfying completeness. -/
@[expose, reducible]
noncomputable def ofKraus [Fintype α] [DecidableEq A] (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) : SubInstrument A B α :=
  DSubInstrument.ofKraus K hK

/-- Relabel outcomes while keeping the output system fixed. -/
@[expose, reducible]
protected noncomputable def map (f : α → β) (p : SubInstrument A B α) : SubInstrument A B β :=
  DSubInstrument.map (C := fun _ ↦ B) f p

/-- Losslessness of a constant-output subinstrument, expressed by its dependent trace law. -/
abbrev Lossless (p : SubInstrument A B α) : Prop := DSubInstrument.Lossless p

/-- Sequencing lossless constant-output subinstruments preserves losslessness. -/
theorem Lossless.bind {p : SubInstrument A B α} {k : α → SubInstrument B C β}
    (hp : p.Lossless) (hk : ∀ a, (k a).Lossless) : (p.bind k).Lossless :=
  DSubInstrument.Lossless.bind hp hk

/-- Framing a constant-output subinstrument preserves losslessness. -/
theorem Lossless.frame {p : SubInstrument A B α} (hp : p.Lossless)
    (R : Type*) [Fintype R] : (p.frame R).Lossless :=
  DSubInstrument.Lossless.frame hp R

/-- Relabelling outcomes preserves losslessness for a fixed output system. -/
theorem Lossless.map {p : SubInstrument A B α} (hp : p.Lossless) (f : α → β) :
    (p.map f).Lossless :=
  DSubInstrument.Lossless.map (C := fun _ ↦ B) hp

/-- Returning the outcome after a computation leaves that computation unchanged. -/
theorem bind_pure (p : SubInstrument A B α) : p.bind SubInstrument.pure = p :=
  DSubInstrument.bind_ret p

/-- Sequencing a returned value applies the continuation to that value. -/
theorem pure_bind (a : α) (k : α → SubInstrument A B β) :
    (SubInstrument.pure a).bind k = k a :=
  DSubInstrument.ret_bind a k

/-- Sequencing constant-output subinstruments is associative. -/
theorem bind_assoc {D γ : Type*} [Fintype D] (p : SubInstrument A B α)
    (k : α → SubInstrument B C β) (l : β → SubInstrument C D γ) :
    (p.bind k).bind l = p.bind fun a ↦ (k a).bind l :=
  DSubInstrument.bind_assoc p k l

/-- Relabelling outcomes is sequencing with return at the relabelled value. -/
theorem map_eq_bind_pure (f : α → β) (p : SubInstrument A B α) :
    p.map f = p.bind fun a ↦ SubInstrument.pure (f a) := by
  simpa only [SubInstrument.map, SubInstrument.bind, SubInstrument.pure] using
    DSubInstrument.map_eq_bind_ret (C := fun _ ↦ B) f p

/-- Failure absorbs every constant-output continuation. -/
theorem fail_bind (k : α → SubInstrument B C β) :
    (SubInstrument.fail : SubInstrument A B α).bind k = SubInstrument.fail :=
  DSubInstrument.fail_bind k

/-- Sequencing with failing constant-output continuations fails. -/
theorem bind_fail (p : SubInstrument A B α) :
    (p.bind fun _ ↦ SubInstrument.fail : SubInstrument A C β) = SubInstrument.fail :=
  DSubInstrument.bind_fail p

/-- Framing commutes with constant-output sequencing. -/
theorem frame_bind (R : Type*) [Fintype R] (p : SubInstrument A B α)
    (k : α → SubInstrument B C β) :
    (p.bind k).frame R = (p.frame R).bind fun a ↦ (k a).frame R :=
  DSubInstrument.frame_bind R p k

/-- Framing return gives return on the extended register. -/
theorem frame_pure (R : Type*) [Fintype R] (a : α) :
    (SubInstrument.pure a : SubInstrument A A α).frame R =
      (SubInstrument.pure a : SubInstrument (A × R) (A × R) α) :=
  DSubInstrument.frame_ret R a

/-- Framing commutes with relabelling constant-output outcomes. -/
theorem frame_map (R : Type*) [Fintype R] (f : α → β) (p : SubInstrument A B α) :
    (p.map f).frame R = (p.frame R).map f := by
  simpa only using DSubInstrument.frame_map (C := fun _ ↦ B) R f p

/-- Framing the failing constant-output subinstrument gives the failing subinstrument. -/
theorem frame_fail (R : Type*) [Fintype R] :
    (SubInstrument.fail : SubInstrument A B α).frame R = SubInstrument.fail :=
  DSubInstrument.frame_fail R

end SubInstrument

namespace DSubInstrument

/-- The branches of a subinstrument are summable on every input. -/
theorem summable_branch_apply (p : DSubInstrument A α (fun _ ↦ B)) (ρ : Matrix A A ℂ) :
    Summable fun a ↦ p.branch a ρ :=
  p.isCPTNIFamily.summable_apply ρ

/-- The sum of the branches of a subinstrument: its action on the state when the classical
outcome is discarded. -/
@[expose]
noncomputable def total (p : DSubInstrument A α (fun _ ↦ B)) : MatrixMap A B :=
  MatrixMap.familySum p.branch

/-- The total map is the pointwise sum of the branches. -/
theorem total_apply (p : DSubInstrument A α (fun _ ↦ B)) (ρ : Matrix A A ℂ) :
    p.total ρ = ∑' a, p.branch a ρ :=
  p.isCPTNIFamily.familySum_apply ρ

/-- The total map as a finite sum over any finite set of outcomes outside which the branches
vanish. -/
theorem total_eq_sum (p : DSubInstrument A α (fun _ ↦ B)) {s : Finset α}
    (hs : ∀ a ∉ s, p.branch a = 0) :
    p.total = ∑ a ∈ s, p.branch a :=
  MatrixMap.familySum_eq_sum_of_forall_notMem hs

/-- The total map as a sum over a finite type of outcomes. -/
theorem total_eq_sum_univ [Fintype α] (p : DSubInstrument A α (fun _ ↦ B)) :
    p.total = ∑ a, p.branch a :=
  MatrixMap.familySum_eq_sum_univ p.branch

/-- The trace of the total map is the sum of the traces of the branches. -/
theorem trace_total_apply (p : DSubInstrument A α (fun _ ↦ B)) (ρ : Matrix A A ℂ) :
    (p.total ρ).trace = ∑' a, (p.branch a ρ).trace :=
  MatrixMap.trace_familySum_apply p.summable_branch_apply ρ

/-- The real part of the trace of the total map is the sum of the real parts of the traces of
the branches. -/
theorem trace_re_total_apply (p : DSubInstrument A α (fun _ ↦ B)) (ρ : Matrix A A ℂ) :
    (p.total ρ).trace.re = ∑' a, (p.branch a ρ).trace.re := by
  rw [trace_total_apply, p.isCPTNIFamily.re_tsum_trace_apply]

/-- The total map of a subinstrument is trace nonincreasing on positive semidefinite inputs. -/
theorem isTNI_total (p : DSubInstrument A α (fun _ ↦ B)) : p.total.IsTNI :=
  p.isCPTNIFamily.isTNI_familySum

/-- The total map of a subinstrument is completely positive. -/
theorem isCP_total (p : DSubInstrument A α (fun _ ↦ B)) : p.total.IsCP :=
  MatrixMap.isCP_familySum p.isCP_branch

/-- For a fixed output system, losslessness is trace preservation of the total map. -/
theorem lossless_iff_isTP_total (p : DSubInstrument A α (fun _ ↦ B)) : p.Lossless ↔ p.total.IsTP :=
  (MatrixMap.isTP_familySum_iff p.summable_branch_apply).symm

/-- The branch trace functional is the trace after the total map. -/
theorem familyTrace_branch (p : DSubInstrument A α (fun _ ↦ B)) :
    MatrixMap.familyTrace p.branch = Matrix.traceLinearMap B ℂ ℂ ∘ₗ p.total :=
  MatrixMap.familyTrace_eq_trace_familySum p.summable_branch_apply

/-- On a positive semidefinite input, each branch has trace at most that of the total map. -/
theorem trace_re_branch_apply_le_total (p : DSubInstrument A α (fun _ ↦ B)) (a : α)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) : (p.branch a ρ).trace.re ≤ (p.total ρ).trace.re := by
  simpa only [familyTrace_branch, LinearMap.comp_apply, Matrix.traceLinearMap_apply] using
    p.trace_re_branch_apply_le_familyTrace a hρ

end DSubInstrument

namespace SubInstrument

/-- The branch of `pure a` at `a` is the identity map. -/
theorem branch_pure_self (a : α) :
    (SubInstrument.pure a : SubInstrument A A α).branch a = LinearMap.id := by
  classical
  exact Pi.single_eq_same a _

/-- The branch of `pure a` away from `a` is zero. -/
theorem branch_pure_of_ne {a a' : α} (h : a' ≠ a) :
    (SubInstrument.pure a : SubInstrument A A α).branch a' = 0 := by
  classical
  exact Pi.single_eq_of_ne h _

/-- The branch family of `pure a` is the identity map at `a` and zero elsewhere. -/
theorem branch_pure [DecidableEq α] (a : α) :
    (SubInstrument.pure a : SubInstrument A A α).branch = Pi.single a LinearMap.id := by
  funext a'
  obtain rfl | h := eq_or_ne a' a
  · rw [branch_pure_self, Pi.single_eq_same]
  · rw [branch_pure_of_ne h, Pi.single_eq_of_ne h]

/-- Relabelling with a fixed output system sums the branches in each fibre. -/
theorem branch_map_apply (f : α → β) (p : SubInstrument A B α) (b : β)
    (ρ : Matrix A A ℂ) :
    (p.map f).branch b ρ = ∑' a : f ⁻¹' {b}, p.branch a ρ := by
  simpa only [cast_eq] using DSubInstrument.branch_map_apply (C := fun _ ↦ B) f p b ρ

end SubInstrument

namespace DSubInstrument

/-- The total map of `pure a` is the identity map. -/
@[simp]
theorem total_pure (a : α) : (SubInstrument.pure a : SubInstrument A A α).total = LinearMap.id := by
  rw [total_eq_sum _ (s := {a}) fun a' ha' ↦
    SubInstrument.branch_pure_of_ne (Finset.notMem_singleton.mp ha'),
    Finset.sum_singleton, SubInstrument.branch_pure_self]

/-- The total map of a composite sums, over the outcomes of the first subinstrument, the total
map of the continuation after the corresponding branch. -/
theorem total_bind (p : DSubInstrument A α (fun _ ↦ B)) (k : α → DSubInstrument B β (fun _ ↦ C)) :
    (p.bind k).total = MatrixMap.familySum fun a ↦ (k a).total ∘ₗ p.branch a :=
  MatrixMap.familySum_familyBind p.isCPTNIFamily fun a ↦ (k a).isCPTNIFamily

/-- Relabelling outcomes does not change the total map. -/
@[simp]
theorem total_map (f : α → β) (p : DSubInstrument A α (fun _ ↦ B)) :
    total (p.map (C := fun _ ↦ B) f) = p.total := by
  rw [DSubInstrument.map_eq_bind_ret, total_bind]
  change MatrixMap.familySum (fun a ↦
    (SubInstrument.pure (f a) : SubInstrument B B β).total ∘ₗ p.branch a) = p.total
  simp only [total_pure, LinearMap.id_comp]
  rfl

/-- The total map of the failing subinstrument is zero. -/
@[simp]
theorem total_fail : total (DSubInstrument.fail : DSubInstrument A α (fun _ ↦ B)) = 0 :=
  MatrixMap.familySum_zero

end DSubInstrument

namespace SubInstrument

/-- A completely positive, trace-nonincreasing map as a subinstrument with one outcome. -/
@[expose]
noncomputable def ofMap (Φ : MatrixMap A B) (hcp : Φ.IsCP) (htni : Φ.IsTNI) :
    SubInstrument A B PUnit :=
  have h : MatrixMap.IsCPTNIFamily fun _ : PUnit ↦ Φ :=
    .of_fintype (fun _ ↦ hcp) fun ρ hρ ↦ by
      rw [Fintype.sum_unique]
      exact htni ρ hρ
  { branch := fun _ ↦ Φ
    isCP_branch := h.isCP
    trace_le := h.sum_trace_re_le }

/-- The branch family of `ofMap Φ` is `Φ` at the unique outcome. -/
@[simp]
theorem branch_ofMap (Φ : MatrixMap A B) (hcp : Φ.IsCP) (htni : Φ.IsTNI) :
    (ofMap Φ hcp htni).branch = fun _ ↦ Φ :=
  rfl

end SubInstrument

namespace DSubInstrument

/-- The total map of `ofMap Φ` is `Φ`. -/
@[simp]
theorem total_ofMap (Φ : MatrixMap A B) (hcp : Φ.IsCP) (htni : Φ.IsTNI) :
    (SubInstrument.ofMap Φ hcp htni).total = Φ := by
  rw [total_eq_sum_univ, Fintype.sum_unique]
  rfl

end DSubInstrument

namespace SubInstrument

/-- The subinstrument of a completely positive, trace-preserving map is lossless. -/
theorem lossless_ofMap {Φ : MatrixMap A B} (hcp : Φ.IsCP) (htp : Φ.IsTP) :
    (ofMap Φ hcp htp.isTNI).Lossless := by
  exact (DSubInstrument.lossless_iff_isTP_total _).mpr (by
    simpa only [DSubInstrument.total_ofMap] using htp)

end SubInstrument

namespace DSubInstrument

/-- The total map of a Kraus measurement sums the Kraus maps of its operators. -/
theorem total_ofKraus [Fintype α] [DecidableEq A] (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) :
    total (DSubInstrument.ofKraus K hK) = ∑ a, MatrixMap.conj (K a) :=
  total_eq_sum_univ _

section frame

variable (R : Type*) [Fintype R]

/-- The total map of a framed subinstrument is the amplified total map. -/
@[simp]
theorem total_frame (p : DSubInstrument A α (fun _ ↦ B)) :
    (p.frame R).total = p.total.amplify R :=
  (MatrixMap.amplify_familySum p.branch R).symm

end frame

end DSubInstrument

/-! ## The monad of subinstruments on a fixed register -/

namespace SubInstrument

variable {M : Type u} [Fintype M] {α β : Type w}

/-- Subinstruments from a register `M` to itself form a monad under
`Quantum.SubInstrument.pure` and `Quantum.SubInstrument.bind`, with `Quantum.SubInstrument.map`
as functorial action. This monad is the semantic domain of quantum programs on `M`. -/
noncomputable instance : Monad (SubInstrument M M) where
  pure := SubInstrument.pure
  bind := SubInstrument.bind
  map := SubInstrument.map

/-- Monadic `pure` on `SubInstrument M M` is `Quantum.SubInstrument.pure`. -/
@[simp]
theorem pure_eq (a : α) : (pure a : SubInstrument M M α) = SubInstrument.pure a :=
  rfl

/-- Monadic bind on `SubInstrument M M` is `Quantum.SubInstrument.bind`. -/
@[simp]
theorem bind_eq (p : SubInstrument M M α) (k : α → SubInstrument M M β) : p >>= k = p.bind k :=
  rfl

/-- Functorial map on `SubInstrument M M` is `Quantum.SubInstrument.map`. -/
@[simp]
theorem map_eq (f : α → β) (p : SubInstrument M M α) : f <$> p = p.map f :=
  rfl

/-- The monad of subinstruments on a fixed register is lawful. -/
instance : LawfulMonad (SubInstrument M M) :=
  LawfulMonad.mk' _
    (id_map := fun p ↦ DSubInstrument.map_id p)
    (pure_bind := fun a k ↦ DSubInstrument.ret_bind (B := fun _ ↦ M) a k)
    (bind_assoc := fun p k l ↦ DSubInstrument.bind_assoc p k l)
    (bind_pure_comp := fun _ _ ↦ rfl)

end SubInstrument

end Quantum
