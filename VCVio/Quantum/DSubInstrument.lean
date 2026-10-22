/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.MatrixMap.Family
public import VCVio.Quantum.MatrixMap.Kraus

/-!
# Dependent subinstruments

A dependent-output subinstrument from the system with basis `A`, with classical outcomes `i : ι`,
has output system `B i` on outcome `i`: after a measurement the register may depend on the outcome,
for example a qubit kept on one outcome and discarded on another. It is a family of completely
positive maps `branch i : MatrixMap A (B i)` such that, on positive semidefinite inputs, the
traces of the branches over every finite set of outcomes sum to at most the trace of the input.
As for `Quantum.SubInstrument`, the family is summable rather than finitely supported, and no
countability assumption is made on `ι`; only countably many branches are nonzero
(`Quantum.DSubInstrument.countable_support_branch`). The finite-instrument reference is in the
module doc of `VCVio.Quantum.SubInstrument`; outcome dependence, countable support and possible
trace loss extend that finite textbook definition.

The branches have different codomains, so they cannot be summed as maps. Trace nonincrease is
stated through traces, and the trace functional `Quantum.MatrixMap.familyTrace`,
`ρ ↦ ∑' i, trace (branch i ρ)`, plays the role of the trace of the total map. With finitely many
outcomes, a dependent subinstrument is one completely positive, trace-nonincreasing map into the
block-diagonal algebra `⊕ i, M_{B i}`. With infinitely many outcomes its outputs are families of
blocks with summable traces, and this file works with the families directly rather than with a
completed direct sum. In either case there are no off-diagonal blocks between different
outcomes: outcomes are classical alternatives and cannot interfere. In particular a dependent
subinstrument is not an arbitrary map into the full matrix algebra on the disjoint union
`Σ i, B i`.

Sequencing is Kleisli composition of branch families (`Quantum.MatrixMap.familyBind`), with unit
the single identity branch `Quantum.DSubInstrument.ret`. The unit and associativity laws are
equalities of structures.

Every branch has a finite Kraus representation (`Quantum.DSubInstrument.exists_kraus_branch`),
even when the outcome type is infinite. For finitely many outcomes,
`Quantum.DSubInstrument.exists_kraus_of_fintype` gives a joint completeness inequality, and
`Quantum.DSubInstrument.Lossless.exists_kraus` gives equality, with operators indexed by
`B i × A` on outcome `i`. For two stages with finitely many intermediate outcomes,
`Quantum.DSubInstrument.branch_bind_eq_sum_conj_mul` expresses each final branch as a sum of
Kraus maps along paths, with the later operator multiplying on the left.

## The constant-codomain case

`Quantum.SubInstrument A B α` is defined in `VCVio.Quantum.SubInstrument` as an abbreviation
for `DSubInstrument A α (fun _ ↦ B)`. This API applies to it directly. Only the total map,
the one-outcome `ofMap` constructor and the fixed-register `Monad` instance need a constant
codomain. In general this is an indexed monad, since `ret B i` changes the input system to `B i`.

## Main definitions

* `Quantum.DSubInstrument A ι B`: dependent subinstruments, with `ret`, `bind`, `map`, `fail`,
  `frame`, `ofKraus` and the restriction `comap` along an injective map of outcomes.
* `Quantum.DSubInstrument.Lossless`: the trace functional is the trace.
-/

public section

open scoped ComplexOrder
open Matrix

namespace Quantum

/-! ## Dependent subinstruments -/

/-- A subinstrument whose output system depends on the outcome: completely positive maps
`branch i : M_A → M_{B i}` with `∑ i ∈ s, tr (branch i ρ) ≤ tr ρ` for every finite set `s` and
every positive semidefinite `ρ`. For example, a measurement may keep a qubit on one outcome and
discard it on another (output system `Unit`, which is one-dimensional).

Only countably many branches are nonzero. Outcomes are classical: there are no off-diagonal blocks
between different output systems. `SubInstrument` abbreviates the case of a constant
output system. -/
@[ext]
structure DSubInstrument (A : Type*) [Fintype A] (ι : Type*) (B : ι → Type*)
    [∀ i, Fintype (B i)] where
  /-- The map applied to the state on outcome `i`. -/
  branch : (i : ι) → MatrixMap A (B i)
  /-- Every branch is completely positive. -/
  isCP_branch : ∀ i, (branch i).IsCP
  /-- On positive semidefinite inputs, the traces of the branches over a finite set of outcomes
  sum to at most the trace of the input. -/
  trace_le : ∀ (s : Finset ι) (ρ : Matrix A A ℂ), ρ.PosSemidef →
    ∑ i ∈ s, (branch i ρ).trace.re ≤ ρ.trace.re

namespace DSubInstrument

variable {A : Type*} [Fintype A] {ι κ μ : Type*} {B : ι → Type*} [∀ i, Fintype (B i)]
  {C : κ → Type*} [∀ c, Fintype (C c)] {E : μ → Type*} [∀ m, Fintype (E m)]

/-! ### Trace bounds -/

/-- The branch family of a dependent subinstrument is completely positive with
trace-nonincreasing partial sums. -/
theorem isCPTNIFamily (p : DSubInstrument A ι B) : MatrixMap.IsCPTNIFamily p.branch :=
  ⟨p.isCP_branch, p.trace_le⟩

/-- Each branch sends positive semidefinite matrices to positive semidefinite matrices. -/
theorem posSemidef_branch_apply (p : DSubInstrument A ι B) (i : ι) {ρ : Matrix A A ℂ}
    (hρ : ρ.PosSemidef) : (p.branch i ρ).PosSemidef :=
  (p.isCP_branch i).posSemidef hρ

/-- On a positive semidefinite input, each branch has nonnegative trace. -/
theorem trace_re_branch_apply_nonneg (p : DSubInstrument A ι B) (i : ι) {ρ : Matrix A A ℂ}
    (hρ : ρ.PosSemidef) : 0 ≤ (p.branch i ρ).trace.re :=
  (p.posSemidef_branch_apply i hρ).trace_re_nonneg

/-- On a positive semidefinite input, the traces of the branches over any finite set of outcomes
sum to at most the trace of the input. -/
theorem sum_trace_re_le (p : DSubInstrument A ι B) (s : Finset ι) {ρ : Matrix A A ℂ}
    (hρ : ρ.PosSemidef) : ∑ i ∈ s, (p.branch i ρ).trace.re ≤ ρ.trace.re :=
  p.trace_le s ρ hρ

/-- On a positive semidefinite input, the traces of all the branches sum to at most the trace of
the input. -/
theorem tsum_trace_re_le (p : DSubInstrument A ι B) {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    ∑' i, (p.branch i ρ).trace.re ≤ ρ.trace.re :=
  p.isCPTNIFamily.tsum_trace_re_apply_le hρ

/-- On a positive semidefinite input, each branch trace is bounded by the family trace. -/
theorem trace_re_branch_apply_le_familyTrace (p : DSubInstrument A ι B) (i : ι)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    (p.branch i ρ).trace.re ≤ (MatrixMap.familyTrace p.branch ρ).re := by
  rw [p.isCPTNIFamily.familyTrace_apply, p.isCPTNIFamily.re_tsum_trace_apply]
  exact (p.isCPTNIFamily.summable_trace_re_apply hρ).le_tsum i
    fun j _ ↦ p.trace_re_branch_apply_nonneg j hρ

/-- On a positive semidefinite input, each branch has trace at most that of the input. -/
theorem trace_re_branch_apply_le (p : DSubInstrument A ι B) (i : ι) {ρ : Matrix A A ℂ}
    (hρ : ρ.PosSemidef) : (p.branch i ρ).trace.re ≤ ρ.trace.re :=
  p.isCPTNIFamily.isTNI i ρ hρ

/-- Only countably many branches of a dependent subinstrument are nonzero, whatever the outcome
type. -/
theorem countable_support_branch (p : DSubInstrument A ι B) :
    {i | p.branch i ≠ 0}.Countable :=
  p.isCPTNIFamily.countable_support

/-! ### Return -/

section ret

variable (B)

open Classical in
/-- **Return.** The dependent subinstrument on `B i` with the single outcome `i` and the identity
branch. -/
@[expose]
noncomputable def ret (i : ι) : DSubInstrument (B i) ι B :=
  have h := MatrixMap.isCPTNIFamily_single (B := B) i MatrixMap.IsCP.id MatrixMap.IsTNI.id
  { branch := Pi.single (M := fun j ↦ MatrixMap (B i) (B j)) i LinearMap.id
    isCP_branch := h.isCP
    trace_le := h.sum_trace_re_le }

/-- The branch of `ret B i` at `i` is the identity map. -/
@[simp]
theorem branch_ret_self (i : ι) : (ret B i).branch i = LinearMap.id := by
  classical
  exact Pi.single_eq_same (M := fun j ↦ MatrixMap (B i) (B j)) i _

/-- The branch of `ret B i` away from `i` is zero. -/
@[simp]
theorem branch_ret_of_ne {i j : ι} (h : j ≠ i) : (ret B i).branch j = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun j ↦ MatrixMap (B i) (B j)) h _

/-- The branch family of `ret B i` is the identity map at `i` and zero elsewhere. -/
theorem branch_ret [DecidableEq ι] (i : ι) :
    (ret B i).branch = Pi.single (M := fun j ↦ MatrixMap (B i) (B j)) i LinearMap.id := by
  funext j
  obtain rfl | h := eq_or_ne j i
  · rw [branch_ret_self, Pi.single_eq_same]
  · rw [branch_ret_of_ne B h, Pi.single_eq_of_ne h]

end ret

/-! ### Sequencing -/

/-- **Sequencing.** Run `p`; on outcome `i`, run `k i` on the system `B i`. The branch at `c` is
`ρ ↦ ∑' i, (k i).branch c (p.branch i ρ)`. -/
@[expose]
protected noncomputable def bind (p : DSubInstrument A ι B)
    (k : (i : ι) → DSubInstrument (B i) κ C) : DSubInstrument A κ C :=
  have h := p.isCPTNIFamily.familyBind fun i ↦ (k i).isCPTNIFamily
  { branch := MatrixMap.familyBind p.branch fun i ↦ (k i).branch
    isCP_branch := h.isCP
    trace_le := h.sum_trace_re_le }

/-- The branch family of a composite is the Kleisli composite of the branch families. -/
theorem branch_bind (p : DSubInstrument A ι B) (k : (i : ι) → DSubInstrument (B i) κ C) :
    (p.bind k).branch = MatrixMap.familyBind p.branch fun i ↦ (k i).branch :=
  rfl

/-- The branch of a composite at `c`, as a finite sum over any finite set outside which the
branches of the first subinstrument vanish. -/
theorem branch_bind_apply_of_forall_notMem (p : DSubInstrument A ι B)
    (k : (i : ι) → DSubInstrument (B i) κ C) {s : Finset ι} (hs : ∀ i ∉ s, p.branch i = 0)
    (c : κ) : (p.bind k).branch c = ∑ i ∈ s, (k i).branch c ∘ₗ p.branch i :=
  MatrixMap.familyBind_apply_of_forall_notMem _ hs c

/-- The branch of a composite at `c` sums, over the outcomes `i` of the first subinstrument, the
branch of the continuation at `c` after the branch at `i`. -/
theorem branch_bind_apply (p : DSubInstrument A ι B) (k : (i : ι) → DSubInstrument (B i) κ C)
    (c : κ) (ρ : Matrix A A ℂ) : (p.bind k).branch c ρ = ∑' i, (k i).branch c (p.branch i ρ) :=
  MatrixMap.familyBind_apply p.isCPTNIFamily (fun i ↦ (k i).isCPTNIFamily) c ρ

/-- The branch of a composite at `c` as a sum over a finite type of intermediate outcomes. -/
theorem branch_bind_apply_univ [Fintype ι] (p : DSubInstrument A ι B)
    (k : (i : ι) → DSubInstrument (B i) κ C) (c : κ) :
    (p.bind k).branch c = ∑ i, (k i).branch c ∘ₗ p.branch i :=
  MatrixMap.familyBind_apply_univ _ _ c

/-- The trace functional of a composite sums, over the outcomes of the first subinstrument, the
trace functional of the continuation after the corresponding branch. -/
theorem familyTrace_bind (p : DSubInstrument A ι B) (k : (i : ι) → DSubInstrument (B i) κ C)
    (ρ : Matrix A A ℂ) :
    MatrixMap.familyTrace (p.bind k).branch ρ =
      ∑' i, MatrixMap.familyTrace (k i).branch (p.branch i ρ) :=
  MatrixMap.familyTrace_familyBind p.isCPTNIFamily (fun i ↦ (k i).isCPTNIFamily) ρ

/-! ### Monad laws -/

/-- Left unit law: returning `i` and then running `k` is `k i`. -/
@[simp]
theorem ret_bind (i : ι) (k : (j : ι) → DSubInstrument (B j) κ C) : (ret B i).bind k = k i := by
  classical
  ext1
  rw [branch_bind, branch_ret]
  exact MatrixMap.single_id_familyBind i _

/-- Right unit law: running `p` and then returning its outcome is `p`. -/
@[simp]
theorem bind_ret (p : DSubInstrument A ι B) : p.bind (ret B) = p := by
  classical
  ext1
  rw [branch_bind]
  simp only [branch_ret]
  exact MatrixMap.familyBind_single_id _

/-- Sequencing of dependent subinstruments is associative. -/
theorem bind_assoc (p : DSubInstrument A ι B) (k : (i : ι) → DSubInstrument (B i) κ C)
    (l : (c : κ) → DSubInstrument (C c) μ E) :
    (p.bind k).bind l = p.bind fun i ↦ (k i).bind l :=
  DSubInstrument.ext <| MatrixMap.familyBind_assoc p.isCPTNIFamily
    (fun i ↦ (k i).isCPTNIFamily) fun c ↦ (l c).isCPTNIFamily

/-! ### Reindexing outcomes -/

/-- Reindex the outcomes of `p` along `f : ι → κ` when its output system on outcome `i` is
`C (f i)`: outcome `i` is reported as `f i`, and the branches of outcomes with the same image are
summed. This is coarse-graining of the classical outcomes. -/
@[expose]
protected noncomputable def map (f : ι → κ) (p : DSubInstrument A ι fun i ↦ C (f i)) :
    DSubInstrument A κ C :=
  p.bind fun i ↦ ret C (f i)

/-- Reindexing along `f` is sequencing with `fun i ↦ ret C (f i)`. -/
theorem map_eq_bind_ret (f : ι → κ) (p : DSubInstrument A ι fun i ↦ C (f i)) :
    p.map f = p.bind fun i ↦ ret C (f i) :=
  rfl

/-- The branch at `c` sums the branches in its fibre, transported to the system `C c`. -/
theorem branch_map_apply (f : ι → κ) (p : DSubInstrument A ι fun i ↦ C (f i))
    (c : κ) (ρ : Matrix A A ℂ) :
    (p.map f).branch c ρ = ∑' i : f ⁻¹' {c},
      cast (congrArg (fun j ↦ Matrix (C j) (C j) ℂ) i.property) (p.branch i ρ) := by
  rw [map_eq_bind_ret, branch_bind_apply]
  calc
    _ = ∑' i : f ⁻¹' {c}, (ret C (f i)).branch c (p.branch i ρ) := by
      rw [tsum_subtype (f ⁻¹' {c})
        (fun i ↦ (ret C (f i)).branch c (p.branch i ρ))]
      apply tsum_congr
      intro i
      by_cases h : f i = c
      · rw [Set.indicator_of_mem (show i ∈ f ⁻¹' {c} from h)]
      · rw [Set.indicator_of_notMem (show i ∉ f ⁻¹' {c} from h),
          branch_ret_of_ne C (Ne.symm h), LinearMap.zero_apply]
    _ = _ := by
      apply tsum_congr
      intro ⟨i, hi⟩
      change f i = c at hi
      subst c
      simp only [branch_ret_self, LinearMap.id_apply, cast_eq]

/-- The branch at `c` is the sum of its fibre of branch maps, transported to `C c`. -/
theorem branch_map (f : ι → κ) (p : DSubInstrument A ι fun i ↦ C (f i)) (c : κ) :
    (p.map f).branch c = MatrixMap.familySum (fun i : f ⁻¹' {c} ↦
      cast (congrArg (fun j ↦ MatrixMap A (C j)) i.property) (p.branch i)) := by
  have he (i : f ⁻¹' {c}) :
      (cast (congrArg (fun j ↦ MatrixMap A (C j)) i.property) (p.branch i) : MatrixMap A (C c)) =
        (ret C (f i)).branch c ∘ₗ p.branch i := by
    obtain ⟨i, hi⟩ := i
    dsimp at hi ⊢
    subst c
    simp only [branch_ret_self, LinearMap.id_comp, cast_eq]
  simp_rw [he]
  apply LinearMap.ext
  intro ρ
  rw [MatrixMap.familySum_apply
    (fun ρ ↦ ((p.isCPTNIFamily.comp_eval
      (fun i ↦ (ret C (f i)).isCPTNIFamily) c).summable_apply ρ).subtype _)]
  rw [branch_map_apply]
  apply tsum_congr
  intro ⟨i, hi⟩
  dsimp at hi ⊢
  subst c
  simp only [branch_ret_self, LinearMap.id_apply, cast_eq]

/-- Reindexing along the identity changes nothing. -/
@[simp]
theorem map_id (p : DSubInstrument A ι B) : p.map (C := B) id = p :=
  bind_ret p

/-- Reindexing twice is reindexing along the composite. -/
theorem map_map {ν : Type*} {F : ν → Type*} [∀ n, Fintype (F n)] (f : ι → κ) (g : κ → ν)
    (p : DSubInstrument A ι fun i ↦ F (g (f i))) :
    (p.map (C := fun c ↦ F (g c)) f).map g = p.map (C := F) (g ∘ f) := by
  simp only [map_eq_bind_ret, bind_assoc, ret_bind, Function.comp_apply]

/-- Reindexing `ret` along `f` is `ret` at the image. -/
@[simp]
theorem map_ret (f : ι → κ) (i : ι) : (ret (fun i ↦ C (f i)) i).map (C := C) f = ret C (f i) :=
  ret_bind i _

/-- Reindexing after sequencing is sequencing with reindexed continuations. -/
theorem map_bind {ν : Type*} {F : ν → Type*} [∀ n, Fintype (F n)] (f : κ → ν)
    (p : DSubInstrument A ι B) (k : (i : ι) → DSubInstrument (B i) κ fun c ↦ F (f c)) :
    (p.bind k).map f = p.bind fun i ↦ (k i).map f :=
  bind_assoc _ _ _

/-! ### Failure -/

/-- The dependent subinstrument with no branches: it fails on every input. -/
@[expose]
protected noncomputable def fail : DSubInstrument A ι B where
  branch := 0
  isCP_branch := MatrixMap.isCPTNIFamily_zero.isCP
  trace_le := MatrixMap.isCPTNIFamily_zero.sum_trace_re_le

/-- The failing subinstrument has no branches. -/
@[simp]
theorem branch_fail : (DSubInstrument.fail : DSubInstrument A ι B).branch = 0 :=
  rfl

/-- Failure absorbs every continuation. -/
@[simp]
theorem fail_bind (k : (i : ι) → DSubInstrument (B i) κ C) :
    (DSubInstrument.fail : DSubInstrument A ι B).bind k = DSubInstrument.fail :=
  DSubInstrument.ext <| MatrixMap.zero_familyBind _

/-- Sequencing with failing continuations fails. -/
@[simp]
theorem bind_fail (p : DSubInstrument A ι B) :
    (p.bind fun _ ↦ DSubInstrument.fail : DSubInstrument A κ C) = DSubInstrument.fail :=
  DSubInstrument.ext <| MatrixMap.familyBind_zero _

/-! ### Framing by an ancilla -/

/-- Extend each branch by the identity on a right-hand reference system `R`:
the branch at `i` is `p.branch i ⊗ id_R`, from `A × R` to `B i × R`.
No operation acts directly on `R`, but its outcome-conditioned state may change through
entanglement with the system. -/
@[expose]
noncomputable def frame (p : DSubInstrument A ι B) (R : Type*) [Fintype R] :
    DSubInstrument (A × R) ι fun i ↦ B i × R where
  branch i := (p.branch i).amplify R
  isCP_branch := (p.isCPTNIFamily.amplify R).isCP
  trace_le := (p.isCPTNIFamily.amplify R).sum_trace_re_le

section frame

variable (R : Type*) [Fintype R]

/-- Each branch of a framed dependent subinstrument is the amplified branch. -/
@[simp]
theorem branch_frame_apply (p : DSubInstrument A ι B) (i : ι) :
    (p.frame R).branch i = (p.branch i).amplify R :=
  rfl

/-- Framing `ret B i` gives `ret` on the extended systems. -/
@[simp]
theorem frame_ret (i : ι) : (ret B i).frame R = ret (fun j ↦ B j × R) i := by
  refine DSubInstrument.ext <| funext fun j ↦ ?_
  rw [branch_frame_apply]
  obtain rfl | h := eq_or_ne j i
  · rw [branch_ret_self, branch_ret_self, MatrixMap.amplify_id]
  · rw [branch_ret_of_ne B h, branch_ret_of_ne _ h, MatrixMap.amplify_zero]

/-- Framing commutes with sequencing. -/
theorem frame_bind (p : DSubInstrument A ι B) (k : (i : ι) → DSubInstrument (B i) κ C) :
    (p.bind k).frame R = (p.frame R).bind fun i ↦ (k i).frame R :=
  DSubInstrument.ext <| MatrixMap.familyBind_mapRange_amplify R p.branch fun i ↦ (k i).branch

/-- Framing commutes with reindexing outcomes. -/
theorem frame_map (f : ι → κ) (p : DSubInstrument A ι fun i ↦ C (f i)) :
    (p.map f).frame R = (p.frame R).map (C := fun c ↦ C c × R) f := by
  simp only [map_eq_bind_ret, frame_bind, frame_ret]

/-- Framing the failing subinstrument gives the failing subinstrument. -/
@[simp]
theorem frame_fail :
    (DSubInstrument.fail : DSubInstrument A ι B).frame R = DSubInstrument.fail :=
  DSubInstrument.ext <| funext fun _ ↦ MatrixMap.amplify_zero

end frame

/-! ### Losslessness -/

/-- A dependent subinstrument is lossless when its trace functional is the trace: the traces of
its branches sum to the trace of the input, so it never fails. For a constant codomain this is
trace preservation of the total map. -/
@[expose]
def Lossless (p : DSubInstrument A ι B) : Prop :=
  ∀ ρ : Matrix A A ℂ, MatrixMap.familyTrace p.branch ρ = ρ.trace

variable (B) in
/-- Returning a value is lossless. -/
theorem lossless_ret (i : ι) : (ret B i).Lossless := fun ρ ↦ by
  classical
  rw [branch_ret, MatrixMap.familyTrace_single]
  rfl

/-- Sequencing lossless dependent subinstruments is lossless. -/
theorem Lossless.bind {p : DSubInstrument A ι B} {k : (i : ι) → DSubInstrument (B i) κ C}
    (hp : p.Lossless) (hk : ∀ i, (k i).Lossless) : (p.bind k).Lossless := fun ρ ↦ by
  rw [familyTrace_bind p k, ← hp ρ, p.isCPTNIFamily.familyTrace_apply]
  exact tsum_congr fun i ↦ hk i _

/-- Reindexing the outcomes of a lossless dependent subinstrument is lossless. -/
theorem Lossless.map {f : ι → κ} {p : DSubInstrument A ι fun i ↦ C (f i)} (hp : p.Lossless) :
    (p.map f).Lossless :=
  hp.bind fun i ↦ lossless_ret C (f i)

/-- Framing a lossless dependent subinstrument is lossless. -/
theorem Lossless.frame {p : DSubInstrument A ι B} (hp : p.Lossless) (R : Type*) [Fintype R] :
    (p.frame R).Lossless := fun ρ ↦ by
  rw [MatrixMap.trace_eq_sum_trace_submatrix ρ]
  exact (MatrixMap.familyTrace_mapRange_amplify p.isCPTNIFamily.summable_trace_apply ρ).trans
    (Finset.sum_congr rfl fun r _ ↦ hp _)

/-- A lossless dependent subinstrument satisfies its trace condition with equality. -/
theorem Lossless.tsum_trace_eq {p : DSubInstrument A ι B} (hp : p.Lossless) (ρ : Matrix A A ℂ) :
    ∑' i, (p.branch i ρ).trace = ρ.trace := by
  rw [← p.isCPTNIFamily.familyTrace_apply, hp ρ]

/-- A lossless dependent subinstrument whose branches vanish outside a finite set satisfies its
trace condition on that set with equality. -/
theorem Lossless.sum_trace_eq {p : DSubInstrument A ι B} (hp : p.Lossless) {s : Finset ι}
    (hs : ∀ i ∉ s, p.branch i = 0) (ρ : Matrix A A ℂ) :
    ∑ i ∈ s, (p.branch i ρ).trace = ρ.trace := by
  rw [← MatrixMap.familyTrace_apply_of_forall_notMem hs, hp ρ]

/-! ### Measurements -/

/-- The finite measurement with Kraus operators `K i : Matrix (B i) A ℂ`, one per outcome,
whose output system depends on the outcome, subject to the completeness relation
`∑ i, (K i)ᴴ * K i = 1`. The branch at `i` is `ρ ↦ K i * ρ * (K i)ᴴ`. -/
@[expose]
noncomputable def ofKraus [Fintype ι] [DecidableEq A] (K : (i : ι) → Matrix (B i) A ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) : DSubInstrument A ι B :=
  have h : MatrixMap.IsCPTNIFamily fun i ↦ MatrixMap.conj (K i) :=
    .of_fintype (fun i ↦ MatrixMap.isCP_conj (K i)) fun ρ _ ↦ by
      rw [← Complex.re_sum]
      refine (congrArg Complex.re ?_).le
      simp_rw [MatrixMap.trace_conj_apply]
      rw [← Matrix.trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]
  { branch := fun i ↦ MatrixMap.conj (K i)
    isCP_branch := h.isCP
    trace_le := h.sum_trace_re_le }

/-- The branch of a Kraus measurement at `i` is the Kraus map of `K i`. -/
@[simp]
theorem branch_ofKraus_apply [Fintype ι] [DecidableEq A] (K : (i : ι) → Matrix (B i) A ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (i : ι) : (ofKraus K hK).branch i = MatrixMap.conj (K i) :=
  rfl

/-- A measurement with a complete family of Kraus operators is lossless. -/
theorem lossless_ofKraus [Fintype ι] [DecidableEq A] (K : (i : ι) → Matrix (B i) A ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) : (ofKraus K hK).Lossless := fun ρ ↦ by
  rw [MatrixMap.familyTrace_apply_univ]
  simp_rw [branch_ofKraus_apply, MatrixMap.trace_conj_apply]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]

/-- Each branch of a dependent subinstrument has Kraus operators from `ℂ^A` to `ℂ^(B i)`, indexed
by `B i × A`. The output system may depend on the outcome, and the outcome type need not be finite
or countable. -/
theorem exists_kraus_branch (p : DSubInstrument A ι B) (i : ι) :
    ∃ K : B i × A → Matrix (B i) A ℂ, p.branch i = ∑ k, MatrixMap.conj (K k) :=
  p.isCPTNIFamily.exists_kraus i

/-- Finitely many dependent branches have joint Kraus operators, with the sum of their
squared operators bounded by the identity in the positive semidefinite order. -/
theorem exists_kraus_of_fintype [Fintype ι] [DecidableEq A] (p : DSubInstrument A ι B) :
    ∃ K : (i : ι) → B i × A → Matrix (B i) A ℂ,
      (∀ i, p.branch i = ∑ k, MatrixMap.conj (K i k)) ∧
      (1 - ∑ i, ∑ k, (K i k)ᴴ * K i k).PosSemidef :=
  p.isCPTNIFamily.exists_kraus_of_fintype

/-- A lossless dependent subinstrument with finitely many outcomes has joint Kraus operators
whose squared operators sum to the identity. -/
theorem Lossless.exists_kraus [Fintype ι] [DecidableEq A] {p : DSubInstrument A ι B}
    (hp : p.Lossless) :
    ∃ K : (i : ι) → B i × A → Matrix (B i) A ℂ,
      (∀ i, p.branch i = ∑ k, MatrixMap.conj (K i k)) ∧
      ∑ i, ∑ k, (K i k)ᴴ * K i k = 1 := by
  classical
  choose K hK using p.exists_kraus_branch
  refine ⟨K, hK, ?_⟩
  have ht (ρ : Matrix A A ℂ) :
      ((∑ i, ∑ k, (K i k)ᴴ * K i k) * ρ).trace = ρ.trace := by
    have h := hp.tsum_trace_eq ρ
    simpa only [tsum_fintype, hK, MatrixMap.trace_sum_conj_apply,
      Finset.sum_mul, Matrix.trace_sum] using h
  ext a a'
  have h := ht (single a' a 1)
  rw [Matrix.trace_mul_single] at h
  by_cases ha : a = a'
  · subst ha
    simpa [Matrix.trace_single_eq_same] using h
  · simpa [Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm ha), Matrix.one_apply_ne ha] using h

/-- Kraus operators of dependent sequencing are path products, with the later operator on
the left. Intermediate outcomes are finite; final outcomes need not be finite. Paths are
classical alternatives, so their output matrices add. -/
theorem branch_bind_eq_sum_conj_mul [Fintype ι] {ν ξ : Type*} [Fintype ν] [Fintype ξ]
    (p : DSubInstrument A ι B) (k : (i : ι) → DSubInstrument (B i) κ C)
    {K : (i : ι) → ν → Matrix (B i) A ℂ}
    {L : (i : ι) → (c : κ) → ξ → Matrix (C c) (B i) ℂ}
    (hK : ∀ i, p.branch i = ∑ j, MatrixMap.conj (K i j))
    (hL : ∀ i c, (k i).branch c = ∑ j, MatrixMap.conj (L i c j)) (c : κ) :
    (p.bind k).branch c = ∑ x : ι × ν × ξ,
      MatrixMap.conj (L x.1 c x.2.2 * K x.1 x.2.1) := by
  simp only [branch_bind_apply_univ, Fintype.sum_prod_type, MatrixMap.conj_mul, hK, hL]
  refine Finset.sum_congr rfl fun i _ ↦ LinearMap.ext fun ρ ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]

/-! ### Restricting the outcomes -/

/-- The restriction of a dependent subinstrument along an injective map `f : κ → ι` of outcomes:
the branch at `k` is the branch of `p` at `f k`, and the branches of `p` outside the range of `f`
are dropped. -/
@[expose]
noncomputable def comap (f : κ → ι) (hf : Function.Injective f) (p : DSubInstrument A ι B) :
    DSubInstrument A κ fun k ↦ B (f k) where
  branch k := p.branch (f k)
  isCP_branch k := p.isCP_branch (f k)
  trace_le s ρ hρ := by
    have h := p.trace_le (s.map ⟨f, hf⟩) ρ hρ
    rwa [Finset.sum_map] at h

/-- The branch of a restriction at `k` is the branch at `f k`. -/
@[simp]
theorem branch_comap (f : κ → ι) (hf : Function.Injective f) (p : DSubInstrument A ι B) (k : κ) :
    (p.comap f hf).branch k = p.branch (f k) :=
  rfl

/-- Restricting a lossless dependent subinstrument along a bijection of outcomes is lossless. -/
theorem Lossless.comap {p : DSubInstrument A ι B} (hp : p.Lossless) {f : κ → ι}
    (hf : Function.Bijective f) : (p.comap f hf.injective).Lossless := fun ρ ↦ by
  rw [(p.comap f hf.injective).isCPTNIFamily.familyTrace_apply, ← hp.tsum_trace_eq ρ]
  exact (Equiv.ofBijective f hf).tsum_eq fun i ↦ (p.branch i ρ).trace

end DSubInstrument

end Quantum
