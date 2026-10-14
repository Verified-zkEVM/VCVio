/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import ToMathlib.Algebra.Module.FinsuppKleisli
public import VCVio.Quantum.MatrixMap

/-!
# Subinstruments and quantum computations

A subinstrument from the system with basis `A` to the system with basis `B`, with classical
outcomes in `α`, is a finitely supported family of completely positive maps
`branch a : MatrixMap A B` whose sum is trace nonincreasing on positive semidefinite inputs.
Running it on a state `ρ` yields outcome `a` together with the unnormalized state `branch a ρ`,
whose trace is the weight of that outcome; trace lost by the sum is the weight of failure.

Sequencing is Kleisli composition of branch families, `(p.bind k).branch b = ∑ a, (k a).branch b
∘ₗ p.branch a`, with unit the single identity branch. The monad laws hold for families of
arbitrary linear maps (`Finsupp.lbind`); complete positivity and trace nonincrease of the
composite are the content of `Quantum.SubInstrument.bind`.

## Main definitions

* `Quantum.SubInstrument A B α`: subinstruments, with `pure`, `bind`, `map`, `fail`.
* `Quantum.SubInstrument.Lossless`: the sum of the branches is trace preserving.
* `Quantum.SubInstrument.ofMap`, `Quantum.SubInstrument.ofKraus`: a single completely positive
  map, and the measurement given by a complete family of Kraus operators.
* `Quantum.SubInstrument.frame`: the action on a system extended by an untouched ancilla.
* `Quantum.SubInstrument M M`: subinstruments from a register `M` to itself form a lawful monad,
  the semantic domain of quantum programs on that register.
-/

public section

open scoped ComplexOrder
open Matrix

universe u w

namespace Quantum

/-- A subinstrument from the system with basis `A` to the system with basis `B` with classical
outcomes in `α`: a finitely supported family of completely positive maps whose sum is trace
nonincreasing on positive semidefinite inputs. -/
@[ext]
structure SubInstrument (A B : Type*) [Fintype A] [Fintype B] (α : Type*) where
  /-- The map applied to the state on outcome `a`; zero outside finitely many outcomes. -/
  branch : α →₀ MatrixMap A B
  /-- Every branch is completely positive. -/
  isCP_branch : ∀ a, (branch a).IsCP
  /-- The sum of the branches is trace nonincreasing on positive semidefinite inputs. -/
  isTNI_total : MatrixMap.IsTNI (Finsupp.ltotal branch)

namespace SubInstrument

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] {α β γ : Type*}

/-! ## Total map and trace bounds -/

/-- The sum of the branches of a subinstrument: its action on the state when the classical
outcome is discarded. -/
@[expose]
noncomputable def total (p : SubInstrument A B α) : MatrixMap A B :=
  Finsupp.ltotal p.branch

/-- The total map as a sum over the support of the branch family. -/
theorem total_eq_sum (p : SubInstrument A B α) : p.total = ∑ a ∈ p.branch.support, p.branch a :=
  rfl

/-- The total map as a sum over a finite type of outcomes. -/
theorem total_eq_sum_univ [Fintype α] (p : SubInstrument A B α) : p.total = ∑ a, p.branch a :=
  Finsupp.ltotal_eq_sum_univ p.branch

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
  .sum _ fun a _ ↦ p.isCP_branch a

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
    (hρ : ρ.PosSemidef) : (p.branch a ρ).trace.re ≤ (p.total ρ).trace.re := by
  by_cases ha : a ∈ p.branch.support
  · exact MatrixMap.trace_re_apply_le_sum _ (fun a _ ↦ p.isCP_branch a) hρ ha
  · rw [Finsupp.notMem_support_iff.mp ha]
    simpa using (p.isCP_total.posSemidef hρ).trace_re_nonneg

/-- On a positive semidefinite input, each branch has trace at most that of the input. -/
theorem trace_re_branch_apply_le (p : SubInstrument A B α) (a : α) {ρ : Matrix A A ℂ}
    (hρ : ρ.PosSemidef) : (p.branch a ρ).trace.re ≤ ρ.trace.re :=
  (p.trace_re_branch_apply_le_total a hρ).trans (p.isTNI_total ρ hρ)

/-! ## Monad operations -/

/-- The subinstrument that leaves the state unchanged and returns `a`. -/
@[expose]
protected noncomputable def pure (a : α) : SubInstrument A A α where
  branch := Finsupp.single a LinearMap.id
  isCP_branch a' := by
    classical
    rw [Finsupp.single_apply]
    split_ifs
    · exact .id
    · exact .zero
  isTNI_total := by
    rw [Finsupp.ltotal_single]
    exact .id

/-- Sequencing of subinstruments: run `p`, then the continuation selected by its outcome. The
branch at `b` is `∑ a, (k a).branch b ∘ₗ p.branch a`. -/
@[expose]
protected noncomputable def bind (p : SubInstrument A B α) (k : α → SubInstrument B C β) :
    SubInstrument A C β where
  branch := p.branch.lbind fun a ↦ (k a).branch
  isCP_branch b := by
    rw [Finsupp.lbind_apply_eq_sum]
    exact .sum _ fun a _ ↦ ((k a).isCP_branch b).comp (p.isCP_branch a)
  isTNI_total := by
    rw [Finsupp.ltotal_lbind]
    exact .sum_comp _ (fun a _ ↦ p.isCP_branch a) (fun a _ ↦ (k a).isTNI_total) p.isTNI_total

/-- Relabel the outcomes of a subinstrument along `f`, summing the branches of outcomes with
the same image. -/
@[expose]
protected noncomputable def map (f : α → β) (p : SubInstrument A B α) : SubInstrument A B β where
  branch := p.branch.mapDomain f
  isCP_branch b := by
    rw [← Finsupp.lbind_single_id_comp]
    exact (p.bind fun a ↦ SubInstrument.pure (f a)).isCP_branch b
  isTNI_total := by
    rw [Finsupp.ltotal_mapDomain]
    exact p.isTNI_total

/-- The subinstrument with no branches: it fails on every input. -/
@[expose]
protected noncomputable def fail : SubInstrument A B α where
  branch := 0
  isCP_branch _ := .zero
  isTNI_total := by
    rw [Finsupp.ltotal_zero]
    exact .zero

/-- The branch family of `pure a` is the identity map at `a` and zero elsewhere. -/
@[simp]
theorem branch_pure (a : α) :
    (SubInstrument.pure a : SubInstrument A A α).branch = Finsupp.single a LinearMap.id :=
  rfl

/-- The branch family of a composite is the Kleisli composite of the branch families. -/
theorem branch_bind (p : SubInstrument A B α) (k : α → SubInstrument B C β) :
    (p.bind k).branch = p.branch.lbind fun a ↦ (k a).branch :=
  rfl

/-- The branch of a composite at `b` sums, over the outcomes `a` of the first subinstrument, the
branch of the continuation at `b` after the branch at `a`. -/
theorem branch_bind_apply (p : SubInstrument A B α) (k : α → SubInstrument B C β) (b : β) :
    (p.bind k).branch b = ∑ a ∈ p.branch.support, (k a).branch b ∘ₗ p.branch a :=
  Finsupp.lbind_apply_eq_sum ..

/-- The branch of a composite at `b` as a sum over a finite type of intermediate outcomes. -/
theorem branch_bind_apply_univ [Fintype α] (p : SubInstrument A B α)
    (k : α → SubInstrument B C β) (b : β) :
    (p.bind k).branch b = ∑ a, (k a).branch b ∘ₗ p.branch a :=
  Finsupp.lbind_apply_eq_sum_univ ..

/-- The branch family of a relabelled subinstrument is the pushforward of the branch family. -/
@[simp]
theorem branch_map (f : α → β) (p : SubInstrument A B α) :
    (p.map f).branch = p.branch.mapDomain f :=
  rfl

/-- The failing subinstrument has no branches. -/
@[simp]
theorem branch_fail : (SubInstrument.fail : SubInstrument A B α).branch = 0 :=
  rfl

/-- The total map of `pure a` is the identity map. -/
@[simp]
theorem total_pure (a : α) : (SubInstrument.pure a : SubInstrument A A α).total = LinearMap.id :=
  Finsupp.ltotal_single ..

/-- The total map of a composite sums, over the outcomes of the first subinstrument, the total
map of the continuation after the corresponding branch. -/
theorem total_bind (p : SubInstrument A B α) (k : α → SubInstrument B C β) :
    (p.bind k).total = ∑ a ∈ p.branch.support, (k a).total ∘ₗ p.branch a :=
  Finsupp.ltotal_lbind ..

/-- Relabelling outcomes does not change the total map. -/
@[simp]
theorem total_map (f : α → β) (p : SubInstrument A B α) : (p.map f).total = p.total :=
  Finsupp.ltotal_mapDomain ..

/-- The total map of the failing subinstrument is zero. -/
@[simp]
theorem total_fail : (SubInstrument.fail : SubInstrument A B α).total = 0 :=
  Finsupp.ltotal_zero

/-! ## Monad laws -/

/-- Left unit law: returning `a` and then running `k` is `k a`. -/
@[simp]
protected theorem pure_bind (a : α) (k : α → SubInstrument A B β) :
    (SubInstrument.pure a).bind k = k a :=
  SubInstrument.ext <| Finsupp.single_id_lbind ..

/-- Right unit law: running `p` and then returning its outcome is `p`. -/
@[simp]
protected theorem bind_pure (p : SubInstrument A B α) : p.bind SubInstrument.pure = p :=
  SubInstrument.ext <| Finsupp.lbind_single_id _

/-- Sequencing of subinstruments is associative. -/
protected theorem bind_assoc (p : SubInstrument A B α) (k : α → SubInstrument B C β)
    (l : β → SubInstrument C D γ) :
    (p.bind k).bind l = p.bind fun a ↦ (k a).bind l :=
  SubInstrument.ext <| Finsupp.lbind_assoc ..

/-- Relabelling outcomes along `f` is sequencing with `fun a ↦ pure (f a)`. -/
theorem map_eq_bind_pure (f : α → β) (p : SubInstrument A B α) :
    p.map f = p.bind fun a ↦ SubInstrument.pure (f a) :=
  SubInstrument.ext (Finsupp.lbind_single_id_comp _ f).symm

/-- Relabelling outcomes along the identity changes nothing. -/
@[simp]
protected theorem map_id (p : SubInstrument A B α) : p.map id = p :=
  SubInstrument.ext Finsupp.mapDomain_id

/-- Failure absorbs every continuation. -/
@[simp]
theorem fail_bind (k : α → SubInstrument B C β) :
    (SubInstrument.fail : SubInstrument A B α).bind k = SubInstrument.fail :=
  SubInstrument.ext <| Finsupp.zero_lbind (X := Matrix A A ℂ) fun a ↦ (k a).branch

/-! ## Losslessness -/

/-- Returning a value is lossless. -/
theorem lossless_pure (a : α) : (SubInstrument.pure a : SubInstrument A A α).Lossless := by
  rw [Lossless, total_pure]
  exact .id

/-- Sequencing lossless subinstruments is lossless. -/
theorem Lossless.bind {p : SubInstrument A B α} {k : α → SubInstrument B C β}
    (hp : p.Lossless) (hk : ∀ a, (k a).Lossless) : (p.bind k).Lossless := by
  rw [Lossless, total_bind]
  exact .sum_comp _ (fun a _ ↦ hk a) hp

/-- Relabelling the outcomes of a lossless subinstrument is lossless. -/
theorem Lossless.map {p : SubInstrument A B α} (hp : p.Lossless) (f : α → β) :
    (p.map f).Lossless := by
  rwa [Lossless, total_map]

/-! ## Single maps and measurements -/

/-- A completely positive, trace-nonincreasing map as a subinstrument with one outcome. -/
@[expose]
noncomputable def ofMap (Φ : MatrixMap A B) (hcp : Φ.IsCP) (htni : Φ.IsTNI) :
    SubInstrument A B PUnit where
  branch := Finsupp.single PUnit.unit Φ
  isCP_branch _ := by rwa [Finsupp.single_eq_same]
  isTNI_total := by rwa [Finsupp.ltotal_single]

/-- The branch family of `ofMap Φ` is `Φ` at the unique outcome. -/
@[simp]
theorem branch_ofMap (Φ : MatrixMap A B) (hcp : Φ.IsCP) (htni : Φ.IsTNI) :
    (ofMap Φ hcp htni).branch = Finsupp.single PUnit.unit Φ :=
  rfl

/-- The total map of `ofMap Φ` is `Φ`. -/
@[simp]
theorem total_ofMap (Φ : MatrixMap A B) (hcp : Φ.IsCP) (htni : Φ.IsTNI) :
    (ofMap Φ hcp htni).total = Φ :=
  Finsupp.ltotal_single ..

/-- The subinstrument of a completely positive, trace-preserving map is lossless. -/
theorem lossless_ofMap {Φ : MatrixMap A B} (hcp : Φ.IsCP) (htp : Φ.IsTP) :
    (ofMap Φ hcp htp.isTNI).Lossless := by
  rwa [Lossless, total_ofMap]

/-- The measurement with Kraus operators `K a`, one per outcome, subject to the completeness
relation `∑ a, (K a)ᴴ * K a = 1`. The branch at `a` is `ρ ↦ K a * ρ * (K a)ᴴ`. -/
@[expose]
noncomputable def ofKraus [Fintype α] [DecidableEq A] (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) : SubInstrument A B α where
  branch := Finsupp.equivFunOnFinite.symm fun a ↦ MatrixMap.conj (K a)
  isCP_branch a := MatrixMap.isCP_conj (K a)
  isTNI_total := by
    rw [Finsupp.ltotal_eq_sum_univ]
    exact (MatrixMap.isTP_sum_conj hK).isTNI

/-- The branch of a Kraus measurement at `a` is the Kraus map of `K a`. -/
@[simp]
theorem branch_ofKraus_apply [Fintype α] [DecidableEq A] (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) (a : α) :
    (ofKraus K hK).branch a = MatrixMap.conj (K a) :=
  rfl

/-- The total map of a Kraus measurement sums the Kraus maps of its operators. -/
theorem total_ofKraus [Fintype α] [DecidableEq A] (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) : (ofKraus K hK).total = ∑ a, MatrixMap.conj (K a) :=
  Finsupp.ltotal_eq_sum_univ _

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
  branch := p.branch.mapRange (fun Φ : MatrixMap A B ↦ Φ.amplify R) MatrixMap.amplify_zero
  isCP_branch a := (p.isCP_branch a).amplify
  isTNI_total := by
    rw [Finsupp.ltotal_mapRange _ _ MatrixMap.amplify_add]
    exact p.isTNI_total.amplify

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
  Finsupp.ltotal_mapRange _ MatrixMap.amplify_zero MatrixMap.amplify_add _

/-- Framing `pure a` gives `pure a` on the extended system. -/
@[simp]
theorem frame_pure (a : α) :
    (SubInstrument.pure a : SubInstrument A A α).frame R = SubInstrument.pure a :=
  SubInstrument.ext <|
    (Finsupp.mapRange_single (hf := MatrixMap.amplify_zero)).trans <|
      congrArg _ MatrixMap.amplify_id

/-- Framing commutes with sequencing. -/
theorem frame_bind (p : SubInstrument A B α) (k : α → SubInstrument B C β) :
    (p.bind k).frame R = (p.frame R).bind fun a ↦ (k a).frame R :=
  SubInstrument.ext <| Finsupp.mapRange_lbind _ _ _ MatrixMap.amplify_zero
    MatrixMap.amplify_zero MatrixMap.amplify_zero MatrixMap.amplify_add MatrixMap.amplify_comp _ _

/-- Framing commutes with relabelling outcomes. -/
theorem frame_map (f : α → β) (p : SubInstrument A B α) :
    (p.map f).frame R = (p.frame R).map f := by
  simp only [map_eq_bind_pure, frame_bind, frame_pure]

/-- Framing the failing subinstrument gives the failing subinstrument. -/
@[simp]
theorem frame_fail : (SubInstrument.fail : SubInstrument A B α).frame R = SubInstrument.fail :=
  SubInstrument.ext <| Finsupp.mapRange_zero (hf := MatrixMap.amplify_zero)

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
