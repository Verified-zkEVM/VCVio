/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.MatrixMap.Family

/-!
# Subinstruments and quantum computations

A subinstrument from the system with basis `A` to the system with basis `B`, with classical
outcomes in `α`, is a family of completely positive maps `branch a : MatrixMap A B`, one for each
outcome, whose finite partial sums are trace nonincreasing on positive semidefinite inputs.
Running it on a state `ρ` yields outcome `a` together with the unnormalized state `branch a ρ`,
whose trace is the weight of that outcome; trace lost by the sum of all branches is the weight of
failure.

## Summable outcome families

The branch family is an arbitrary function on `α`, not a finitely supported one. Trace
nonincrease of the finite partial sums makes it summable on every input
(`Quantum.MatrixMap.IsCPTNIFamily.summable_apply`), its support is countable
(`Quantum.SubInstrument.countable_support_branch`), and its sum `Quantum.SubInstrument.total` is
completely positive and trace nonincreasing. No countability assumption is made on `α`.

Infinitely many outcomes are needed for loops. A loop with a classical guard, such as "measure
`|+⟩` until the outcome is `0` and return the number of rounds", has outcomes on all of `ℕ`, and
its semantics is the limit of its finite unrollings. A limit of finitely supported instruments
need not be finitely supported, so finite support is not closed under the constructions a loop
needs. Finitely supported instruments remain the special case: a family that vanishes outside a
finite set `s` has total map the finite sum over `s` (`Quantum.SubInstrument.total_eq_sum`), and
every finite construction here (`pure`, `ofMap`, `ofKraus` over a finite type) produces one.

Sequencing is Kleisli composition of branch families,
`(p.bind k).branch b ρ = ∑' a, (k a).branch b (p.branch a ρ)`, with unit the single identity
branch. Associativity exchanges two summations; the joint summability it needs comes from
positivity (`Quantum.MatrixMap.IsCPTNIFamily.prod`).

## Main definitions

* `Quantum.SubInstrument A B α`: subinstruments, with `pure`, `bind`, `map`, `fail`.
* `Quantum.SubInstrument.total`: the sum of the branches, the action when the outcome is
  discarded.
* `Quantum.SubInstrument.Lossless`: the total map is trace preserving.
* `Quantum.SubInstrument.ofMap`, `Quantum.SubInstrument.ofKraus`: a single completely positive
  map, and the measurement given by a complete family of Kraus operators.
* `Quantum.SubInstrument.frame`: the action on a system extended by an untouched ancilla.
* `Quantum.SubInstrument M M`: subinstruments from a register `M` to itself form a lawful monad,
  the semantic domain of quantum programs on that register.

## Outcome-dependent output systems

Here every branch has the same output system `B`. `Quantum.DSubInstrument A ι B`, in
`VCVio.Quantum.DSubInstrument`, lets the output system `B i` depend on the outcome `i`.
Subinstruments are exactly its constant-codomain case: `Quantum.SubInstrument.equivD` is an
equivalence `SubInstrument A B α ≃ DSubInstrument A α (fun _ ↦ B)` that commutes with `pure`,
`bind`, `map`, `fail` and `frame`.
-/

public section

open scoped ComplexOrder
open Matrix

universe u w

namespace Quantum

/-- A subinstrument from the system with basis `A` to the system with basis `B` with classical
outcomes in `α`: a family of completely positive maps, one for each outcome, whose finite partial
sums are trace nonincreasing on positive semidefinite inputs. -/
@[ext]
structure SubInstrument (A B : Type*) [Fintype A] [Fintype B] (α : Type*) where
  /-- The map applied to the state on outcome `a`. -/
  branch : α → MatrixMap A B
  /-- Every branch is completely positive. -/
  isCP_branch : ∀ a, (branch a).IsCP
  /-- Every finite partial sum of the branches is trace nonincreasing on positive semidefinite
  inputs. -/
  isTNI_sum : ∀ s : Finset α, (∑ a ∈ s, branch a).IsTNI

namespace SubInstrument

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] {α β γ : Type*}

/-! ## Summability and the total map -/

/-- The branch family of a subinstrument is completely positive with trace-nonincreasing partial
sums. -/
theorem isCPTNIFamily (p : SubInstrument A B α) : MatrixMap.IsCPTNIFamily p.branch :=
  .of_isTNI_sum p.isCP_branch p.isTNI_sum

/-- The branches of a subinstrument are summable on every input. -/
theorem summable_branch_apply (p : SubInstrument A B α) (ρ : Matrix A A ℂ) :
    Summable fun a ↦ p.branch a ρ :=
  p.isCPTNIFamily.summable_apply ρ

/-- Only countably many branches of a subinstrument are nonzero. -/
theorem countable_support_branch (p : SubInstrument A B α) :
    (Function.support p.branch).Countable :=
  p.isCPTNIFamily.countable_support

/-- The sum of the branches of a subinstrument: its action on the state when the classical
outcome is discarded. -/
@[expose]
noncomputable def total (p : SubInstrument A B α) : MatrixMap A B :=
  MatrixMap.familySum p.branch

/-- The total map is the pointwise sum of the branches. -/
theorem total_apply (p : SubInstrument A B α) (ρ : Matrix A A ℂ) :
    p.total ρ = ∑' a, p.branch a ρ :=
  p.isCPTNIFamily.familySum_apply ρ

/-- The total map as a finite sum over any finite set of outcomes outside which the branches
vanish. -/
theorem total_eq_sum (p : SubInstrument A B α) {s : Finset α} (hs : ∀ a ∉ s, p.branch a = 0) :
    p.total = ∑ a ∈ s, p.branch a :=
  MatrixMap.familySum_eq_sum_of_forall_notMem hs

/-- The total map as a sum over a finite type of outcomes. -/
theorem total_eq_sum_univ [Fintype α] (p : SubInstrument A B α) : p.total = ∑ a, p.branch a :=
  MatrixMap.familySum_eq_sum_univ p.branch

/-- The trace of the total map is the sum of the traces of the branches. -/
theorem trace_total_apply (p : SubInstrument A B α) (ρ : Matrix A A ℂ) :
    (p.total ρ).trace = ∑' a, (p.branch a ρ).trace :=
  MatrixMap.trace_familySum_apply p.summable_branch_apply ρ

/-- The real part of the trace of the total map is the sum of the real parts of the traces of
the branches. -/
theorem trace_re_total_apply (p : SubInstrument A B α) (ρ : Matrix A A ℂ) :
    (p.total ρ).trace.re = ∑' a, (p.branch a ρ).trace.re := by
  rw [trace_total_apply, p.isCPTNIFamily.re_tsum_trace_apply]

/-- The total map of a subinstrument is trace nonincreasing on positive semidefinite inputs. -/
theorem isTNI_total (p : SubInstrument A B α) : p.total.IsTNI :=
  p.isCPTNIFamily.isTNI_familySum

/-- The total map of a subinstrument is trace nonincreasing on positive semidefinite inputs. -/
theorem isTNI_total' (p : SubInstrument A B α) : p.total.IsTNI :=
  p.isTNI_total

/-- A subinstrument is lossless when the sum of its branches is trace preserving: it never
fails. -/
@[expose]
def Lossless (p : SubInstrument A B α) : Prop :=
  p.total.IsTP

/-- The total map of a subinstrument is completely positive. -/
theorem isCP_total (p : SubInstrument A B α) : p.total.IsCP :=
  MatrixMap.isCP_familySum p.isCP_branch

/-- Each branch sends positive semidefinite matrices to positive semidefinite matrices. -/
theorem posSemidef_branch_apply (p : SubInstrument A B α) (a : α) {ρ : Matrix A A ℂ}
    (hρ : ρ.PosSemidef) : (p.branch a ρ).PosSemidef :=
  (p.isCP_branch a).posSemidef hρ

/-- On a positive semidefinite input, each branch has nonnegative trace. -/
theorem trace_re_branch_apply_nonneg (p : SubInstrument A B α) (a : α) {ρ : Matrix A A ℂ}
    (hρ : ρ.PosSemidef) : 0 ≤ (p.branch a ρ).trace.re :=
  (p.posSemidef_branch_apply a hρ).trace_re_nonneg

/-- On a positive semidefinite input, each branch has trace at most that of the total map. -/
theorem trace_re_branch_apply_le_total (p : SubInstrument A B α) (a : α) {ρ : Matrix A A ℂ}
    (hρ : ρ.PosSemidef) : (p.branch a ρ).trace.re ≤ (p.total ρ).trace.re :=
  p.isCPTNIFamily.trace_re_apply_le_familySum a hρ

/-- On a positive semidefinite input, each branch has trace at most that of the input. -/
theorem trace_re_branch_apply_le (p : SubInstrument A B α) (a : α) {ρ : Matrix A A ℂ}
    (hρ : ρ.PosSemidef) : (p.branch a ρ).trace.re ≤ ρ.trace.re :=
  (p.trace_re_branch_apply_le_total a hρ).trans (p.isTNI_total ρ hρ)

/-! ## Monad operations -/

open Classical in
/-- The subinstrument that leaves the state unchanged and returns `a`. -/
@[expose]
protected noncomputable def pure (a : α) : SubInstrument A A α :=
  have h := MatrixMap.isCPTNIFamily_single (B := fun _ : α ↦ A) a MatrixMap.IsCP.id
    MatrixMap.IsTNI.id
  { branch := Pi.single a LinearMap.id
    isCP_branch := h.isCP
    isTNI_sum := h.isTNI_sum }

/-- The branch of `pure a` at `a` is the identity map. -/
@[simp]
theorem branch_pure_self (a : α) :
    (SubInstrument.pure a : SubInstrument A A α).branch a = LinearMap.id := by
  classical
  exact Pi.single_eq_same a _

/-- The branch of `pure a` away from `a` is zero. -/
@[simp]
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

/-- Sequencing of subinstruments: run `p`, then the continuation selected by its outcome. The
branch at `b` is `ρ ↦ ∑' a, (k a).branch b (p.branch a ρ)`. -/
@[expose]
protected noncomputable def bind (p : SubInstrument A B α) (k : α → SubInstrument B C β) :
    SubInstrument A C β :=
  have h := p.isCPTNIFamily.familyBind fun a ↦ (k a).isCPTNIFamily
  { branch := MatrixMap.familyBind p.branch fun a ↦ (k a).branch
    isCP_branch := h.isCP
    isTNI_sum := h.isTNI_sum }

/-- Relabel the outcomes of a subinstrument along `f`, summing the branches of outcomes with
the same image. -/
@[expose]
protected noncomputable def map (f : α → β) (p : SubInstrument A B α) : SubInstrument A B β :=
  p.bind fun a ↦ SubInstrument.pure (f a)

/-- The subinstrument with no branches: it fails on every input. -/
@[expose]
protected noncomputable def fail : SubInstrument A B α where
  branch := 0
  isCP_branch := MatrixMap.isCPTNIFamily_zero.isCP
  isTNI_sum := MatrixMap.isCPTNIFamily_zero.isTNI_sum

/-- The branch family of a composite is the Kleisli composite of the branch families. -/
theorem branch_bind (p : SubInstrument A B α) (k : α → SubInstrument B C β) :
    (p.bind k).branch = MatrixMap.familyBind p.branch fun a ↦ (k a).branch :=
  rfl

/-- The branch of a composite at `b` sums, over the outcomes `a` of the first subinstrument, the
branch of the continuation at `b` after the branch at `a`. -/
theorem branch_bind_apply (p : SubInstrument A B α) (k : α → SubInstrument B C β) (b : β)
    (ρ : Matrix A A ℂ) : (p.bind k).branch b ρ = ∑' a, (k a).branch b (p.branch a ρ) :=
  MatrixMap.familyBind_apply p.isCPTNIFamily (fun a ↦ (k a).isCPTNIFamily) b ρ

/-- The branch of a composite at `b`, as a finite sum over any finite set of outcomes outside
which the branches of the first subinstrument vanish. -/
theorem branch_bind_apply_of_forall_notMem (p : SubInstrument A B α)
    (k : α → SubInstrument B C β) {s : Finset α} (hs : ∀ a ∉ s, p.branch a = 0) (b : β) :
    (p.bind k).branch b = ∑ a ∈ s, (k a).branch b ∘ₗ p.branch a :=
  MatrixMap.familyBind_apply_of_forall_notMem _ hs b

/-- The branch of a composite at `b` as a sum over a finite type of intermediate outcomes. -/
theorem branch_bind_apply_univ [Fintype α] (p : SubInstrument A B α)
    (k : α → SubInstrument B C β) (b : β) :
    (p.bind k).branch b = ∑ a, (k a).branch b ∘ₗ p.branch a :=
  MatrixMap.familyBind_apply_univ _ _ b

/-- The branch of a relabelled subinstrument at `b` sums the branches over the fibre of `f`
at `b`. -/
theorem branch_map_apply (f : α → β) (p : SubInstrument A B α) (b : β) (ρ : Matrix A A ℂ) :
    (p.map f).branch b ρ = ∑' a : f ⁻¹' {b}, p.branch a ρ := by
  rw [SubInstrument.map, branch_bind_apply, tsum_subtype (f ⁻¹' {b}) fun a ↦ p.branch a ρ]
  refine tsum_congr fun a ↦ ?_
  by_cases h : f a = b
  · rw [Set.indicator_of_mem (show a ∈ f ⁻¹' {b} from h), h, branch_pure_self, LinearMap.id_apply]
  · rw [Set.indicator_of_notMem (show a ∉ f ⁻¹' {b} from h), branch_pure_of_ne (Ne.symm h),
      LinearMap.zero_apply]

/-- The branch of a relabelled subinstrument at `b` is the sum of the branches over the fibre of
`f` at `b`. -/
theorem branch_map (f : α → β) (p : SubInstrument A B α) (b : β) :
    (p.map f).branch b = MatrixMap.familySum fun a : f ⁻¹' {b} ↦ p.branch a :=
  LinearMap.ext fun ρ ↦ by
    rw [branch_map_apply, MatrixMap.familySum_apply fun ρ ↦ (p.summable_branch_apply ρ).subtype _]

/-- The failing subinstrument has no branches. -/
@[simp]
theorem branch_fail : (SubInstrument.fail : SubInstrument A B α).branch = 0 :=
  rfl

/-- The total map of `pure a` is the identity map. -/
@[simp]
theorem total_pure (a : α) : (SubInstrument.pure a : SubInstrument A A α).total = LinearMap.id := by
  rw [total_eq_sum _ (s := {a}) fun a' ha' ↦ branch_pure_of_ne (Finset.notMem_singleton.mp ha'),
    Finset.sum_singleton, branch_pure_self]

/-- The total map of a composite sums, over the outcomes of the first subinstrument, the total
map of the continuation after the corresponding branch. -/
theorem total_bind (p : SubInstrument A B α) (k : α → SubInstrument B C β) :
    (p.bind k).total = MatrixMap.familySum fun a ↦ (k a).total ∘ₗ p.branch a :=
  MatrixMap.familySum_familyBind p.isCPTNIFamily fun a ↦ (k a).isCPTNIFamily

/-- Relabelling outcomes does not change the total map. -/
@[simp]
theorem total_map (f : α → β) (p : SubInstrument A B α) : (p.map f).total = p.total := by
  rw [SubInstrument.map, total_bind]
  simp only [total_pure, LinearMap.id_comp]
  rfl

/-- The total map of the failing subinstrument is zero. -/
@[simp]
theorem total_fail : (SubInstrument.fail : SubInstrument A B α).total = 0 :=
  MatrixMap.familySum_zero

/-! ## Monad laws -/

/-- Left unit law: returning `a` and then running `k` is `k a`. -/
@[simp]
protected theorem pure_bind (a : α) (k : α → SubInstrument A B β) :
    (SubInstrument.pure a).bind k = k a :=
  SubInstrument.ext <| funext fun b ↦ by
    rw [branch_bind_apply_of_forall_notMem _ k (s := {a})
      fun a' ha' ↦ branch_pure_of_ne (Finset.notMem_singleton.mp ha'), Finset.sum_singleton,
      branch_pure_self, LinearMap.comp_id]

/-- Right unit law: running `p` and then returning its outcome is `p`. -/
@[simp]
protected theorem bind_pure (p : SubInstrument A B α) : p.bind SubInstrument.pure = p :=
  SubInstrument.ext <| funext fun b ↦ by
    rw [branch_bind, MatrixMap.familyBind, MatrixMap.familySum_eq_sum_of_forall_notMem (s := {b})
      fun a ha ↦ by
        rw [branch_pure_of_ne (Ne.symm (Finset.notMem_singleton.mp ha)), LinearMap.zero_comp],
      Finset.sum_singleton, branch_pure_self, LinearMap.id_comp]

/-- Sequencing of subinstruments is associative. -/
protected theorem bind_assoc (p : SubInstrument A B α) (k : α → SubInstrument B C β)
    (l : β → SubInstrument C D γ) :
    (p.bind k).bind l = p.bind fun a ↦ (k a).bind l :=
  SubInstrument.ext <| MatrixMap.familyBind_assoc p.isCPTNIFamily (fun a ↦ (k a).isCPTNIFamily)
    fun b ↦ (l b).isCPTNIFamily

/-- Relabelling outcomes along `f` is sequencing with `fun a ↦ pure (f a)`. -/
theorem map_eq_bind_pure (f : α → β) (p : SubInstrument A B α) :
    p.map f = p.bind fun a ↦ SubInstrument.pure (f a) :=
  rfl

/-- Relabelling outcomes along the identity changes nothing. -/
@[simp]
protected theorem map_id (p : SubInstrument A B α) : p.map id = p :=
  SubInstrument.bind_pure p

/-- Failure absorbs every continuation. -/
@[simp]
theorem fail_bind (k : α → SubInstrument B C β) :
    (SubInstrument.fail : SubInstrument A B α).bind k = SubInstrument.fail :=
  SubInstrument.ext <| MatrixMap.zero_familyBind fun a ↦ (k a).branch

/-! ## Losslessness -/

/-- Returning a value is lossless. -/
theorem lossless_pure (a : α) : (SubInstrument.pure a : SubInstrument A A α).Lossless := by
  rw [Lossless, total_pure]
  exact .id

/-- Sequencing lossless subinstruments is lossless. -/
theorem Lossless.bind {p : SubInstrument A B α} {k : α → SubInstrument B C β}
    (hp : p.Lossless) (hk : ∀ a, (k a).Lossless) : (p.bind k).Lossless := fun ρ ↦ by
  have h : MatrixMap.IsCPTNIFamily fun a ↦ (k a).total ∘ₗ p.branch a :=
    p.isCPTNIFamily.comp (fun a ↦ (k a).isCP_total) fun a ↦ (k a).isTNI_total
  rw [total_bind, MatrixMap.trace_familySum_apply h.summable_apply, ← hp ρ, trace_total_apply]
  exact tsum_congr fun a ↦ hk a _

/-- Relabelling the outcomes of a lossless subinstrument is lossless. -/
theorem Lossless.map {p : SubInstrument A B α} (hp : p.Lossless) (f : α → β) :
    (p.map f).Lossless := by
  rwa [Lossless, total_map]

/-! ## Single maps and measurements -/

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
    isTNI_sum := h.isTNI_sum }

/-- The branch family of `ofMap Φ` is `Φ` at the unique outcome. -/
@[simp]
theorem branch_ofMap (Φ : MatrixMap A B) (hcp : Φ.IsCP) (htni : Φ.IsTNI) :
    (ofMap Φ hcp htni).branch = fun _ ↦ Φ :=
  rfl

/-- The total map of `ofMap Φ` is `Φ`. -/
@[simp]
theorem total_ofMap (Φ : MatrixMap A B) (hcp : Φ.IsCP) (htni : Φ.IsTNI) :
    (ofMap Φ hcp htni).total = Φ := by
  rw [total_eq_sum_univ, Fintype.sum_unique]
  rfl

/-- The subinstrument of a completely positive, trace-preserving map is lossless. -/
theorem lossless_ofMap {Φ : MatrixMap A B} (hcp : Φ.IsCP) (htp : Φ.IsTP) :
    (ofMap Φ hcp htp.isTNI).Lossless := by
  rwa [Lossless, total_ofMap]

/-- The measurement with Kraus operators `K a`, one per outcome, subject to the completeness
relation `∑ a, (K a)ᴴ * K a = 1`. The branch at `a` is `ρ ↦ K a * ρ * (K a)ᴴ`. -/
@[expose]
noncomputable def ofKraus [Fintype α] [DecidableEq A] (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) : SubInstrument A B α :=
  have h : MatrixMap.IsCPTNIFamily fun a ↦ MatrixMap.conj (K a) :=
    .of_fintype (fun a ↦ MatrixMap.isCP_conj (K a)) fun ρ hρ ↦ by
      simpa only [MatrixMap.trace_re_sum_apply] using (MatrixMap.isTP_sum_conj hK).isTNI ρ hρ
  { branch := fun a ↦ MatrixMap.conj (K a)
    isCP_branch := h.isCP
    isTNI_sum := h.isTNI_sum }

/-- The branch of a Kraus measurement at `a` is the Kraus map of `K a`. -/
@[simp]
theorem branch_ofKraus_apply [Fintype α] [DecidableEq A] (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) (a : α) :
    (ofKraus K hK).branch a = MatrixMap.conj (K a) :=
  rfl

/-- The total map of a Kraus measurement sums the Kraus maps of its operators. -/
theorem total_ofKraus [Fintype α] [DecidableEq A] (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) : (ofKraus K hK).total = ∑ a, MatrixMap.conj (K a) :=
  total_eq_sum_univ _

/-- A measurement with a complete family of Kraus operators is lossless. -/
theorem lossless_ofKraus [Fintype α] [DecidableEq A] (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) : (ofKraus K hK).Lossless := by
  rw [Lossless, total_ofKraus]
  exact MatrixMap.isTP_sum_conj hK

/-! ## Framing by an ancilla -/

/-- The action of a subinstrument on a system extended by an ancilla with basis `R` that it
leaves untouched: every branch is amplified by `R`. -/
@[expose]
noncomputable def frame (p : SubInstrument A B α) (R : Type*) [Fintype R] :
    SubInstrument (A × R) (B × R) α where
  branch a := (p.branch a).amplify R
  isCP_branch a := (p.isCP_branch a).amplify
  isTNI_sum s := by
    change (∑ a ∈ s, (p.branch a).amplify R).IsTNI
    rw [← MatrixMap.amplify_sum]
    exact (p.isTNI_sum s).amplify

section frame

variable (R : Type*) [Fintype R]

/-- Each branch of a framed subinstrument is the amplified branch. -/
@[simp]
theorem branch_frame_apply (p : SubInstrument A B α) (a : α) :
    (p.frame R).branch a = (p.branch a).amplify R :=
  rfl

/-- The total map of a framed subinstrument is the amplified total map. -/
@[simp]
theorem total_frame (p : SubInstrument A B α) : (p.frame R).total = p.total.amplify R :=
  (MatrixMap.amplify_familySum p.branch R).symm

/-- Framing `pure a` gives `pure a` on the extended system. -/
@[simp]
theorem frame_pure (a : α) :
    (SubInstrument.pure a : SubInstrument A A α).frame R = SubInstrument.pure a :=
  SubInstrument.ext <| funext fun a' ↦ by
    rw [branch_frame_apply]
    obtain rfl | h := eq_or_ne a' a
    · rw [branch_pure_self, branch_pure_self, MatrixMap.amplify_id]
    · rw [branch_pure_of_ne h, branch_pure_of_ne h, MatrixMap.amplify_zero]

/-- Framing commutes with sequencing. -/
theorem frame_bind (p : SubInstrument A B α) (k : α → SubInstrument B C β) :
    (p.bind k).frame R = (p.frame R).bind fun a ↦ (k a).frame R :=
  SubInstrument.ext <| MatrixMap.familyBind_mapRange_amplify R p.branch fun a ↦ (k a).branch

/-- Framing commutes with relabelling outcomes. -/
theorem frame_map (f : α → β) (p : SubInstrument A B α) :
    (p.map f).frame R = (p.frame R).map f := by
  simp only [map_eq_bind_pure, frame_bind, frame_pure]

/-- Framing the failing subinstrument gives the failing subinstrument. -/
@[simp]
theorem frame_fail : (SubInstrument.fail : SubInstrument A B α).frame R = SubInstrument.fail :=
  SubInstrument.ext <| funext fun _ ↦ MatrixMap.amplify_zero

/-- Framing a lossless subinstrument is lossless. -/
theorem Lossless.frame {p : SubInstrument A B α} (hp : p.Lossless) : (p.frame R).Lossless := by
  rw [Lossless, total_frame]
  exact hp.amplify

end frame

end SubInstrument

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
    (id_map := SubInstrument.map_id)
    (pure_bind := SubInstrument.pure_bind)
    (bind_assoc := SubInstrument.bind_assoc)
    (bind_pure_comp := fun f p ↦ (SubInstrument.map_eq_bind_pure f p).symm)

end SubInstrument

end Quantum
