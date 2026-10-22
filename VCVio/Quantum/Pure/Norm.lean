/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import ToMathlib.Analysis.Normed.Ring.Commutator
public import VCVio.Quantum.Pure.Vector

/-!
# Norm estimates for state vectors

The estimates that vector-level query-complexity arguments are assembled from, for operators
`Matrix B A ℂ` with the operator norm `Matrix.Norms.L2Operator` acting on `EuclideanSpace ℂ A`.
Vector, adjoint, and matrix-order conventions are in `VCVio.Quantum.Pure.Vector`.

## Main results

* `Quantum.abs_norm_applyVec_sub_norm_applyVec_le`: the norm of the image of a vector is
  Lipschitz in the vector, with constant the operator norm.
* `Quantum.abs_norm_sq_applyVec_sub_norm_sq_applyVec_le`,
  `Quantum.abs_sum_norm_sq_applyVec_sub_sum_norm_sq_applyVec_le`: squared norms of images under
  a contraction, or under a jointly contractive family (`∑ i, ‖K i •ᵥ χ‖² ≤ ‖χ‖²`), differ by
  at most `(‖ψ‖ + ‖φ‖) * ‖ψ - φ‖`, hence by at most `2 * ‖ψ - φ‖` on subnormalized vectors.
* `Quantum.norm_commutator_mul_le`, `Quantum.norm_commutator_list_prod_le`: the Leibniz bound
  for the commutator `⁅A, B⁆ = A * B - B * A` and its telescoped form.
* `Quantum.queryState`, `Quantum.norm_queryState_sub_queryState_le`: the state of an alternating
  product of fixed operators and oracle calls, and the hybrid bound comparing two oracles.
-/

public section

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator
open Matrix WithLp

namespace Quantum

variable {A B ι : Type*} [Fintype A] [DecidableEq A] [Fintype B]

/-! ## Perturbing the vector -/

/-- The difference of two squares of nonnegative reals, bounded through bounds on the reals and
on their difference. -/
private theorem abs_sq_sub_sq_le {x y a b d : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxa : x ≤ a) (hyb : y ≤ b)
    (hd : |x - y| ≤ d) : |x ^ 2 - y ^ 2| ≤ (a + b) * d := by
  have h : x ^ 2 - y ^ 2 = (x + y) * (x - y) := by ring
  rw [h, abs_mul, abs_of_nonneg (add_nonneg hx hy)]
  exact mul_le_mul (add_le_add hxa hyb) hd (abs_nonneg _) (add_nonneg (hx.trans hxa) (hy.trans hyb))

/-- The norm of the image of a vector is Lipschitz in the vector, with constant the operator
norm. -/
theorem abs_norm_applyVec_sub_norm_applyVec_le (K : Matrix B A ℂ) (ψ φ : EuclideanSpace ℂ A) :
    |‖K •ᵥ ψ‖ - ‖K •ᵥ φ‖| ≤ ‖K‖ * ‖ψ - φ‖ := by
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [← map_sub]
  exact norm_applyVec_le K _

/-- For a contraction `K`, the norms of the images of two vectors differ by at most the distance
between the vectors. -/
theorem abs_norm_applyVec_sub_norm_applyVec_le_of_norm_le_one {K : Matrix B A ℂ} (hK : ‖K‖ ≤ 1)
    (ψ φ : EuclideanSpace ℂ A) : |‖K •ᵥ ψ‖ - ‖K •ᵥ φ‖| ≤ ‖ψ - φ‖ :=
  (abs_norm_applyVec_sub_norm_applyVec_le K ψ φ).trans
    (mul_le_of_le_one_left (norm_nonneg _) hK)

/-- For a contraction `K`, the squared norms of the images of two vectors differ by at most
`(‖ψ‖ + ‖φ‖) * ‖ψ - φ‖`. -/
theorem abs_norm_sq_applyVec_sub_norm_sq_applyVec_le {K : Matrix B A ℂ} (hK : ‖K‖ ≤ 1)
    (ψ φ : EuclideanSpace ℂ A) :
    |‖K •ᵥ ψ‖ ^ 2 - ‖K •ᵥ φ‖ ^ 2| ≤ (‖ψ‖ + ‖φ‖) * ‖ψ - φ‖ :=
  abs_sq_sub_sq_le (norm_nonneg _) (norm_nonneg _) (norm_applyVec_le_of_norm_le_one hK ψ)
    (norm_applyVec_le_of_norm_le_one hK φ)
    (abs_norm_applyVec_sub_norm_applyVec_le_of_norm_le_one hK ψ φ)

/-- For a contraction `K` and subnormalized vectors, the squared norms of the images differ by
at most twice the distance between the vectors. -/
theorem abs_norm_sq_applyVec_sub_norm_sq_applyVec_le_two_mul {K : Matrix B A ℂ} (hK : ‖K‖ ≤ 1)
    {ψ φ : EuclideanSpace ℂ A} (hψ : ‖ψ‖ ≤ 1) (hφ : ‖φ‖ ≤ 1) :
    |‖K •ᵥ ψ‖ ^ 2 - ‖K •ᵥ φ‖ ^ 2| ≤ 2 * ‖ψ - φ‖ :=
  (abs_norm_sq_applyVec_sub_norm_sq_applyVec_le hK ψ φ).trans <|
    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

/-- For a family of operators that is jointly contractive on a finite set `s` of indices, the
total squared norms of the images of two vectors over `s` differ by at most
`(‖ψ‖ + ‖φ‖) * ‖ψ - φ‖`. -/
theorem abs_sum_norm_sq_applyVec_sub_sum_norm_sq_applyVec_le (s : Finset ι)
    (K : ι → Matrix B A ℂ)
    (hK : ∀ χ : EuclideanSpace ℂ A, ∑ i ∈ s, ‖K i •ᵥ χ‖ ^ 2 ≤ ‖χ‖ ^ 2)
    (ψ φ : EuclideanSpace ℂ A) :
    |∑ i ∈ s, ‖K i •ᵥ ψ‖ ^ 2 - ∑ i ∈ s, ‖K i •ᵥ φ‖ ^ 2| ≤ (‖ψ‖ + ‖φ‖) * ‖ψ - φ‖ := by
  let v (χ : EuclideanSpace ℂ A) : PiLp 2 (fun _ : s ↦ EuclideanSpace ℂ B) :=
    toLp 2 fun i ↦ K i •ᵥ χ
  have hv (χ : EuclideanSpace ℂ A) : ‖v χ‖ ^ 2 = ∑ i ∈ s, ‖K i •ᵥ χ‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_coe_sort s fun i ↦ ‖K i •ᵥ χ‖ ^ 2
  have hle (χ : EuclideanSpace ℂ A) : ‖v χ‖ ≤ ‖χ‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ((hv χ).trans_le (hK χ))
  have hsub : v ψ - v φ = v (ψ - φ) := by
    refine (WithLp.toLp_sub 2 _ _).symm.trans (congrArg (toLp 2) (funext fun i ↦ ?_))
    exact (map_sub (Matrix.toEuclideanLin (K i)) ψ φ).symm
  rw [← hv, ← hv]
  exact abs_sq_sub_sq_le (norm_nonneg _) (norm_nonneg _) (hle ψ) (hle φ)
    ((abs_norm_sub_norm_le _ _).trans (hsub ▸ hle _))

/-- Over any finite set of indices, the squared norms of the branches of a complete family of
Kraus operators sum to at most the squared norm of the input. -/
theorem sum_norm_sq_applyVec_le [Fintype ι] {K : ι → Matrix B A ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (s : Finset ι) (ψ : EuclideanSpace ℂ A) :
    ∑ i ∈ s, ‖K i •ᵥ ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
  rw [← sum_norm_sq_applyVec hK ψ]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun _ _ _ ↦ sq_nonneg _

/-! ## Commutators -/

/-- Leibniz bound for the commutator with a product of operators: `norm_lie_mul_le`
specialized to the induced ℓ² operator norm. -/
theorem norm_commutator_mul_le (X Y Z : Matrix A A ℂ) :
    ‖⁅X, Y * Z⁆‖ ≤ ‖⁅X, Y⁆‖ * ‖Z‖ + ‖Y‖ * ‖⁅X, Z⁆‖ :=
  norm_lie_mul_le X Y Z

/-- Leibniz bound for the commutator of a product of operators: `norm_mul_lie_le`
specialized to the induced ℓ² operator norm. -/
theorem norm_mul_commutator_le (X Y Z : Matrix A A ℂ) :
    ‖⁅X * Y, Z⁆‖ ≤ ‖X‖ * ‖⁅Y, Z⁆‖ + ‖⁅X, Z⁆‖ * ‖Y‖ :=
  norm_mul_lie_le X Y Z

/-- Telescoped Leibniz bound: the commutator of `X` with a product of contractions is bounded by
the sum of the norms of the commutators of `X` with the factors. This is `norm_lie_list_prod_le`
specialized to the induced ℓ² operator norm. -/
theorem norm_commutator_list_prod_le (X : Matrix A A ℂ) (l : List (Matrix A A ℂ))
    (hl : ∀ Y ∈ l, ‖Y‖ ≤ 1) : ‖⁅X, l.prod⁆‖ ≤ (l.map fun Y ↦ ‖⁅X, Y⁆‖).sum :=
  norm_lie_list_prod_le X l hl

/-- The action of a commutator on a vector. -/
theorem commutator_applyVec (X Y : Matrix A A ℂ) (ψ : EuclideanSpace ℂ A) :
    ⁅X, Y⁆ •ᵥ ψ = X •ᵥ Y •ᵥ ψ - Y •ᵥ X •ᵥ ψ := by
  rw [Ring.lie_def, sub_applyVec, mul_applyVec, mul_applyVec]

/-! ## The hybrid bound -/

/-- The state vector of a sequence of operators alternating with oracle calls, just before call
`i`: `ψ₀ = U₀ ψ` and `ψᵢ₊₁ = Uᵢ₊₁ (Oᵢ ψᵢ)`. It is also the final state of the sequence stopped
after `i` calls and the operator that follows them.

The operators are arbitrary matrices; unitary ones give the usual model of a quantum query
algorithm, with the oracle as the unitaries `Oᵢ`. This is a tool for vector proofs, not a
definition of quantum adversaries. -/
@[expose]
noncomputable def queryState (U O : ℕ → Matrix A A ℂ) (ψ : EuclideanSpace ℂ A) :
    ℕ → EuclideanSpace ℂ A
  | 0 => U 0 •ᵥ ψ
  | i + 1 => U (i + 1) •ᵥ O i •ᵥ queryState U O ψ i

/-- Before the first query the state is `U 0 •ᵥ ψ`. -/
@[simp]
theorem queryState_zero (U O : ℕ → Matrix A A ℂ) (ψ : EuclideanSpace ℂ A) :
    queryState U O ψ 0 = U 0 •ᵥ ψ :=
  rfl

/-- Each further step applies the oracle call and then the next operator. -/
@[simp]
theorem queryState_succ (U O : ℕ → Matrix A A ℂ) (ψ : EuclideanSpace ℂ A) (i : ℕ) :
    queryState U O ψ (i + 1) = U (i + 1) •ᵥ O i •ᵥ queryState U O ψ i :=
  rfl

/-- If the operators and the oracle calls are contractions, the state of a query algorithm has
norm at most that of the initial vector. -/
theorem norm_queryState_le (U O : ℕ → Matrix A A ℂ) (ψ : EuclideanSpace ℂ A) (q : ℕ)
    (hU : ∀ i ≤ q, ‖U i‖ ≤ 1) (hO : ∀ i < q, ‖O i‖ ≤ 1) : ‖queryState U O ψ q‖ ≤ ‖ψ‖ := by
  induction q with
  | zero => exact norm_applyVec_le_of_norm_le_one (hU 0 le_rfl) ψ
  | succ q ih =>
    rw [queryState_succ]
    exact (norm_applyVec_le_of_norm_le_one (hU _ le_rfl) _).trans <|
      (norm_applyVec_le_of_norm_le_one (hO q q.lt_succ_self) _).trans <|
        ih (fun i hi ↦ hU i (hi.trans q.le_succ)) fun i hi ↦ hO i (hi.trans q.lt_succ_self)

/-- The hybrid bound. Two runs of the same operators `U` from the same vector `ψ`, one calling the
oracles `O` and the other `O'`, end after `q` calls at distance
`‖ψ_q - ψ'_q‖ ≤ ∑ i < q, ‖(O i - O' i) •ᵥ ψᵢ‖`, where `ψᵢ` is the state before call `i` in the run
with `O`.

Each call adds its own discrepancy, and the later operators, which are contractions, do not
enlarge it. Only `U 1, …, U q` and `O' 0, …, O' (q - 1)` need be contractions. This is the
telescoping step of the hybrid argument of Bennett, Bernstein, Brassard and Vazirani (arXiv
quant-ph/9701001, Theorem 3.3, PDF pp. 7–8), for contractions in place of unitaries. -/
theorem norm_queryState_sub_queryState_le (U O O' : ℕ → Matrix A A ℂ) (ψ : EuclideanSpace ℂ A)
    (q : ℕ) (hU : ∀ i < q, ‖U (i + 1)‖ ≤ 1) (hO' : ∀ i < q, ‖O' i‖ ≤ 1) :
    ‖queryState U O ψ q - queryState U O' ψ q‖ ≤
      ∑ i ∈ Finset.range q, ‖(O i - O' i) •ᵥ queryState U O ψ i‖ := by
  induction q with
  | zero => simp
  | succ q ih =>
    have ih' := ih (fun i hi ↦ hU i (hi.trans q.lt_succ_self))
      fun i hi ↦ hO' i (hi.trans q.lt_succ_self)
    have hsplit : queryState U O ψ (q + 1) - queryState U O' ψ (q + 1) =
        U (q + 1) •ᵥ (O' q •ᵥ (queryState U O ψ q - queryState U O' ψ q) +
          (O q - O' q) •ᵥ queryState U O ψ q) := by
      rw [queryState_succ, queryState_succ, sub_applyVec,
        map_sub (Matrix.toEuclideanLin (O' q)), sub_add_sub_cancel',
        map_sub (Matrix.toEuclideanLin (U (q + 1)))]
    rw [hsplit, Finset.sum_range_succ]
    refine (norm_applyVec_le_of_norm_le_one (hU q q.lt_succ_self) _).trans ?_
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact (norm_applyVec_le_of_norm_le_one (hO' q q.lt_succ_self) _).trans ih'

/-- Hybrid bound for a single pair of oracles `O` and `O'` called at every query. -/
theorem norm_queryState_const_sub_queryState_const_le (U : ℕ → Matrix A A ℂ)
    (O O' : Matrix A A ℂ) (ψ : EuclideanSpace ℂ A) (q : ℕ) (hU : ∀ i < q, ‖U (i + 1)‖ ≤ 1)
    (hO' : ‖O'‖ ≤ 1) :
    ‖queryState U (fun _ ↦ O) ψ q - queryState U (fun _ ↦ O') ψ q‖ ≤
      ∑ i ∈ Finset.range q, ‖(O - O') •ᵥ queryState U (fun _ ↦ O) ψ i‖ :=
  norm_queryState_sub_queryState_le U _ _ ψ q hU fun _ _ ↦ hO'

end Quantum
