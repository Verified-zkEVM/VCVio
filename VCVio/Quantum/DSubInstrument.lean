/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.SubInstrument

/-!
# Dependent subinstruments

A dependent subinstrument from the system with basis `A`, with classical outcomes `i : ι`, has
output system `B i` on outcome `i`: after a measurement the register may depend on the outcome,
for example a qubit kept on one outcome and discarded on another. It is a family of completely
positive maps `branch i : MatrixMap A (B i)` such that, on positive semidefinite inputs, the
traces of the branches over every finite set of outcomes sum to at most the trace of the input.
As for `Quantum.SubInstrument`, the family is summable rather than finitely supported, and no
countability assumption is made on `ι`.

The branches have different codomains, so they cannot be summed as maps. Trace nonincrease is
stated through traces, and the trace functional `Quantum.MatrixMap.familyTrace`,
`ρ ↦ ∑' i, trace (branch i ρ)`, plays the role of the trace of the total map. Mathematically a
dependent subinstrument is one completely positive, trace-nonincreasing map into the direct sum
`⊕ i, M_{B i}` of matrix algebras. It is not a map into the matrix algebra on the disjoint union
`Σ i, B i`, which would allow coherences between outcomes.

Sequencing is Kleisli composition of branch families (`Quantum.MatrixMap.familyBind`), with unit
the single identity branch `Quantum.DSubInstrument.ret`. The unit and associativity laws are
equalities of structures.

## The constant-codomain case

`Quantum.SubInstrument A B α` is exactly the case of a constant output system:
`Quantum.SubInstrument.equivD : SubInstrument A B α ≃ DSubInstrument A α (fun _ ↦ B)`, which keeps
the branch family unchanged. The equivalence sends `pure`, `bind`, `map`, `fail`, `frame` and
`ofKraus` to `ret`, `bind`, `map`, `fail`, `frame` and `ofKraus` (`Quantum.SubInstrument.toD_pure`,
`toD_bind`, `toD_map`, `toD_fail`, `toD_frame`, `toD_ofKraus`), and losslessness to losslessness
(`Quantum.SubInstrument.lossless_toD_iff`). For a constant codomain the trace functional of a
branch family is the trace after the total map (`Quantum.SubInstrument.familyTrace_branch`).

## Main definitions

* `Quantum.DSubInstrument A ι B`: dependent subinstruments, with `ret`, `bind`, `map`, `fail`,
  `frame` and `ofKraus`.
* `Quantum.DSubInstrument.Lossless`: the trace functional is the trace.
* `Quantum.SubInstrument.toD`, `Quantum.DSubInstrument.toSubInstrument`,
  `Quantum.SubInstrument.equivD`: the constant-codomain case.
-/

public section

open scoped ComplexOrder
open Matrix

namespace Quantum

/-! ## Dependent subinstruments -/

/-- A dependent subinstrument from the system with basis `A`, with classical outcomes `i : ι` and
output system `B i` on outcome `i`: a family of completely positive maps
`branch i : MatrixMap A (B i)` such that, on positive semidefinite inputs, the traces of the
branches over every finite set of outcomes sum to at most the trace of the input. It is one
completely positive, trace-nonincreasing map into the direct sum `⊕ i, M_{B i}`. -/
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

/-- On a positive semidefinite input, each branch has trace at most that of the input. -/
theorem trace_re_branch_apply_le (p : DSubInstrument A ι B) (i : ι) {ρ : Matrix A A ℂ}
    (hρ : ρ.PosSemidef) : (p.branch i ρ).trace.re ≤ ρ.trace.re :=
  p.isCPTNIFamily.isTNI i ρ hρ

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
summed. -/
@[expose]
protected noncomputable def map (f : ι → κ) (p : DSubInstrument A ι fun i ↦ C (f i)) :
    DSubInstrument A κ C :=
  p.bind fun i ↦ ret C (f i)

/-- Reindexing along `f` is sequencing with `fun i ↦ ret C (f i)`. -/
theorem map_eq_bind_ret (f : ι → κ) (p : DSubInstrument A ι fun i ↦ C (f i)) :
    p.map f = p.bind fun i ↦ ret C (f i) :=
  rfl

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

/-- The action of a dependent subinstrument on a system extended by an ancilla with basis `R`
that it leaves untouched, on the right as in `Quantum.SubInstrument.frame`: every branch is
amplified by `R`. -/
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
  DSubInstrument.ext <| MatrixMap.familyBind_mapRange_amplify R p.isCPTNIFamily
    fun i ↦ (k i).isCPTNIFamily

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
its branches sum to the trace of the input, so it never fails. This is the analogue of
`Quantum.SubInstrument.Lossless`, trace preservation of the total map. -/
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

/-- The measurement with Kraus operators `K i : Matrix (B i) A ℂ`, one per outcome, whose output
system depends on the outcome, subject to the completeness relation `∑ i, (K i)ᴴ * K i = 1`. The
branch at `i` is `ρ ↦ K i * ρ * (K i)ᴴ`. -/
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

end DSubInstrument

/-! ## Subinstruments are the constant-codomain case -/

namespace SubInstrument

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] {α β : Type*}

/-- For a constant codomain, the trace functional of the branch family of a subinstrument is the
trace after its total map. -/
theorem familyTrace_branch (p : SubInstrument A B α) :
    MatrixMap.familyTrace p.branch = Matrix.traceLinearMap B ℂ ℂ ∘ₗ p.total :=
  MatrixMap.familyTrace_eq_trace_familySum p.summable_branch_apply

/-- A subinstrument as a dependent subinstrument with constant output system. -/
@[expose]
def toD (p : SubInstrument A B α) : DSubInstrument A α fun _ ↦ B where
  branch := p.branch
  isCP_branch := p.isCP_branch
  trace_le := p.isCPTNIFamily.sum_trace_re_le

/-- The branch family of `toD p` is the branch family of `p`. -/
@[simp]
theorem branch_toD (p : SubInstrument A B α) : (toD p).branch = p.branch :=
  rfl

/-- The branch of `toD p` at `a` is the branch of `p` at `a`. -/
theorem branch_toD_apply (p : SubInstrument A B α) (a : α) : (toD p).branch a = p.branch a :=
  rfl

end SubInstrument

namespace DSubInstrument

variable {A B : Type*} [Fintype A] [Fintype B] {α : Type*}

/-- A dependent subinstrument with constant output system as a subinstrument. -/
@[expose]
def toSubInstrument (q : DSubInstrument A α fun _ ↦ B) : SubInstrument A B α where
  branch := q.branch
  isCP_branch := q.isCP_branch
  isTNI_sum := q.isCPTNIFamily.isTNI_sum

/-- The branch of `q.toSubInstrument` at `a` is the branch of `q` at `a`. -/
@[simp]
theorem branch_toSubInstrument_apply (q : DSubInstrument A α fun _ ↦ B) (a : α) :
    q.toSubInstrument.branch a = q.branch a :=
  rfl

end DSubInstrument

namespace SubInstrument

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] {α β : Type*}

/-- **Subinstruments are the constant-codomain case of dependent subinstruments.** The
equivalence keeps the branch family. -/
@[expose]
def equivD : SubInstrument A B α ≃ DSubInstrument A α fun _ ↦ B where
  toFun := toD
  invFun := DSubInstrument.toSubInstrument
  left_inv _ := rfl
  right_inv _ := rfl

/-- The equivalence `equivD` is `toD`. -/
@[simp]
theorem equivD_apply (p : SubInstrument A B α) : equivD p = toD p :=
  rfl

/-- The inverse of `equivD` is `toSubInstrument`. -/
@[simp]
theorem equivD_symm_apply (q : DSubInstrument A α fun _ ↦ B) :
    equivD.symm q = q.toSubInstrument :=
  rfl

/-- `toSubInstrument` is a left inverse of `toD`. -/
@[simp]
theorem toSubInstrument_toD (p : SubInstrument A B α) : (toD p).toSubInstrument = p :=
  rfl

/-- `toD` is a left inverse of `toSubInstrument`. -/
@[simp]
theorem toD_toSubInstrument (q : DSubInstrument A α fun _ ↦ B) : toD q.toSubInstrument = q :=
  rfl

/-- `toD` is injective. -/
theorem toD_injective : Function.Injective (toD : SubInstrument A B α → _) :=
  equivD.injective

/-- `toD` is injective. -/
@[simp]
theorem toD_inj {p q : SubInstrument A B α} : toD p = toD q ↔ p = q :=
  toD_injective.eq_iff

/-- `toD` sends `pure a` to `ret` at `a`. -/
@[simp]
theorem toD_pure (a : α) :
    toD (SubInstrument.pure a : SubInstrument A A α) = DSubInstrument.ret (fun _ ↦ A) a := by
  refine DSubInstrument.ext <| funext fun a' ↦ ?_
  rw [branch_toD]
  obtain rfl | h := eq_or_ne a' a
  · rw [branch_pure_self, DSubInstrument.branch_ret_self]
  · rw [branch_pure_of_ne h, DSubInstrument.branch_ret_of_ne _ h]

/-- `toD` sends sequencing to sequencing. -/
theorem toD_bind (p : SubInstrument A B α) (k : α → SubInstrument B C β) :
    toD (p.bind k) = (toD p).bind fun a ↦ toD (k a) :=
  rfl

/-- `toD` sends relabelling outcomes to reindexing outcomes. -/
theorem toD_map (f : α → β) (p : SubInstrument A B α) :
    toD (p.map f) = (toD p).map (C := fun _ ↦ B) f := by
  rw [map_eq_bind_pure, toD_bind]
  simp only [toD_pure]
  rfl

/-- `toD` sends failure to failure. -/
@[simp]
theorem toD_fail : toD (SubInstrument.fail : SubInstrument A B α) = DSubInstrument.fail :=
  rfl

/-- `toD` commutes with framing by an ancilla. -/
@[simp]
theorem toD_frame (p : SubInstrument A B α) (R : Type*) [Fintype R] :
    toD (p.frame R) = (toD p).frame R :=
  rfl

/-- `toD` sends a Kraus measurement to the Kraus measurement with constant output system. -/
@[simp]
theorem toD_ofKraus [Fintype α] [DecidableEq A] (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) :
    toD (ofKraus K hK) = DSubInstrument.ofKraus (B := fun _ ↦ B) K hK :=
  rfl

/-- `toD p` is lossless exactly when `p` is. -/
@[simp]
theorem lossless_toD_iff {p : SubInstrument A B α} : (toD p).Lossless ↔ p.Lossless :=
  (MatrixMap.isTP_familySum_iff p.summable_branch_apply).symm

end SubInstrument

end Quantum
