/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Computability.BitEncoding
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.FinEnum

/-!
# Counting Polynomial-Size Turing Machines

The combinatorial core of the non-triviality certificate for the machine-grounded
polynomial-time model (`VCVio.OracleComp.Coinductive.PolyTimeNontrivial`): only
sub-doubly-exponentially many predicates `BitVec n → Bool` are realizable by
`d`-state single-tape machines, while there are `2 ^ (2 ^ n)` such predicates.

The pieces, each isolated so the diagonalization argument reads as pure counting:

* **Canonical `d`-state machines** (`Turing.SingleTapeTM.TMTable`): a transition table
  `Fin d → Option Bool → Stmt Bool × Option (Fin d)` together with an initial state.
  These are a `Fintype` with an explicit, provable cardinality
  (`card_tmTable`, bounded by `Turing.SingleTapeTM.B`), and `reify` packages one back
  into a `SingleTapeTM Bool`. The `Fintype`/`DecidableEq` instances for the underlying
  `Turing.Dir` and `SingleTapeTM.Stmt Bool` are supplied here.
* **State normalization** (`exists_tmTable_of_card_le`, an isolated `sorry`): any
  `SingleTapeTM Bool` with at most `d` states computes the same string function as
  `reify` of some `TMTable d`.
* **Realizable predicates** (`Computability.RealizableLE`): the predicates realizable by
  an input/output `EncPolyTime` pair of description size at most `d`. This set is covered
  by a `Finset` of cardinality at most `B d ^ 2` (`exists_realizableLE_covering`, the
  isolated counting `sorry`: the surjection `TMTable d × TMTable d → RealizableLE n d`
  built from state normalization), and it is monotone in `d` (`realizableLE_mono`).
* **Growth bounds**: every polynomial is eventually dominated by `2 ^ (n / 4)`
  (`Computability.eventually_poly_le`), while the machine count stays below the function
  count (`Computability.eventually_count_lt`).
* **The function space** has cardinality `2 ^ (2 ^ n)` (`Computability.card_bitVec_fun`),
  and a `Finset` family of subexponential cardinality misses a diagonal predicate
  eventually (`Computability.exists_diagonal`).
-/

@[expose] public section

open Filter Asymptotics

namespace Turing.SingleTapeTM

/-! ## Finiteness of statements and directions -/

/-- A `SingleTapeTM.Stmt` is a pair of an optional write symbol and an optional move. -/
def stmtProdEquiv : SingleTapeTM.Stmt Bool ≃ (Option Bool × Option Turing.Dir) where
  toFun s := (s.symbol, s.movement)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Turing.Dir :=
  ⟨{Turing.Dir.left, Turing.Dir.right}, fun d => by cases d <;> decide⟩

instance : DecidableEq (SingleTapeTM.Stmt Bool) :=
  fun _ _ => decidable_of_iff _ stmtProdEquiv.injective.eq_iff

noncomputable instance : Fintype (SingleTapeTM.Stmt Bool) :=
  Fintype.ofEquiv _ stmtProdEquiv.symm

theorem card_dir : Fintype.card Turing.Dir = 2 := by decide

theorem card_stmt : Fintype.card (SingleTapeTM.Stmt Bool) = 9 := by
  rw [Fintype.card_congr stmtProdEquiv]; decide

/-! ## Canonical `d`-state machines -/

/-- A canonical `d`-state single-tape machine over `Bool`: a transition table on states
`Fin d` together with an initial state. Every machine with at most `d` states computes,
after relabeling, the same function as `reify` of one of these (`exists_tmTable_of_card_le`),
so `TMTable d` is the finite index of `d`-state machines used for counting. -/
abbrev TMTable (d : ℕ) : Type :=
  (Fin d → Option Bool → SingleTapeTM.Stmt Bool × Option (Fin d)) × Fin d

noncomputable instance (d : ℕ) : Fintype (TMTable d) := inferInstance

instance (d : ℕ) : DecidableEq (TMTable d) := inferInstance

/-- A crude closed-form upper bound on the number of `d`-state machines: the exact
cardinality `card_tmTable`. -/
def B (d : ℕ) : ℕ := (9 * (d + 1)) ^ (3 * d) * d

/-- The exact number of canonical `d`-state machines: each of the `d` states maps each of
the `3` head symbols (`Option Bool`) to one of the `9 * (d + 1)` statement/next-state
pairs, and there are `d` choices of initial state. -/
theorem card_tmTable (d : ℕ) : Fintype.card (TMTable d) = B d := by
  simp only [B, TMTable, Fintype.card_prod, Fintype.card_fun, card_stmt,
    Fintype.card_option, Fintype.card_fin, Fintype.card_bool, ← pow_mul]

theorem card_tmTable_le (d : ℕ) : Fintype.card (TMTable d) ≤ B d :=
  (card_tmTable d).le

/-- Package a canonical table back into a `SingleTapeTM Bool` on state space `Fin d`. -/
def reify {d : ℕ} (t : TMTable d) : SingleTapeTM Bool where
  State := Fin d
  q₀ := t.2
  tr := t.1

/-! ## State normalization -/

/-- **[Isolated crux, `sorry`]** Every `SingleTapeTM Bool` computing a string function
with at most `d` states computes the same function as `reify` of some `TMTable d` — the
state space is relabeled to `Fin d` along `Fintype.equivFin`, preserving the `Outputs`
relation. Discharging this is the Cslib-internal run-preservation-under-state-relabeling
lemma; it needs an induction over `SingleTapeTM.step` / `RelatesInSteps` transported along
the relabeling. It is the machine-theoretic input to `exists_realizableLE_covering`. -/
theorem exists_tmTable_of_card_le {f : List Bool → List Bool} (h : PolyTimeComputable f)
    {d : ℕ} (hd : Fintype.card h.tm.State ≤ d) :
    ∃ t : TMTable d, ∀ l l', (reify t).Outputs l l' ↔ h.tm.Outputs l l' := by
  sorry

end Turing.SingleTapeTM

namespace Computability

open Turing.SingleTapeTM

/-! ## Realizable predicates -/

/-- The predicates `BitVec n → Bool` realizable at description size at most `d`: those
computed by an initialization witness into some state encoding followed by an output
witness, both `EncPolyTime` machines of description size at most `d`, against the canonical
`BitVec`/`Option Bool` boundary encodings. An implementing machine adversary at these
boundaries lands its computed predicate here (its `initF`/`outputF` witnesses), and the
count of such predicates is controlled by counting the underlying machines
(`exists_realizableLE_covering`). -/
def RealizableLE (n d : ℕ) : Set (BitVec n → Bool) :=
  {g | ∃ (σ : Type) (es : σ → List Bool) (init : BitVec n → σ) (output : σ → Option Bool)
        (_i : EncPolyTime (BitEncFam.bitVecX.enc n) es init)
        (_o : EncPolyTime es (BitEncFam.bool.option.enc n) output),
      _i.size ≤ d ∧ _o.size ≤ d ∧ ∀ x, output (init x) = some (g x)}

/-- Realizability at a larger description size is a weaker requirement. -/
theorem realizableLE_mono {n : ℕ} {d d' : ℕ} (h : d ≤ d') :
    RealizableLE n d ⊆ RealizableLE n d' := by
  rintro g ⟨σ, es, init, output, i, o, hi, ho, hg⟩
  exact ⟨σ, es, init, output, i, o, hi.trans h, ho.trans h, hg⟩

/-- **[Isolated counting crux, `sorry`]** The realizable predicates at description size at
most `d` are covered by a `Finset` of cardinality at most `B d ^ 2`. Discharging this uses
state normalization (`exists_tmTable_of_card_le`) to reduce each realizing pair of witness
machines to a pair `TMTable d × TMTable d` of canonical `d`-state tables; the realized
predicate factors through the two tables (decode the output encoding of the composite run),
giving a surjection from `TMTable d × TMTable d` onto `RealizableLE n d`, whence
`card ≤ Fintype.card (TMTable d × TMTable d) = B d ^ 2` (`card_tmTable`). -/
theorem exists_realizableLE_covering (n d : ℕ) :
    ∃ s : Finset (BitVec n → Bool), RealizableLE n d ⊆ ↑s ∧ s.card ≤ B d ^ 2 := by
  sorry

/-! ## Cardinality of the predicate space -/

/-- There are exactly `2 ^ (2 ^ n)` predicates `BitVec n → Bool`. -/
theorem card_bitVec_fun (n : ℕ) : Fintype.card (BitVec n → Bool) = 2 ^ (2 ^ n) := by
  rw [Fintype.card_fun, Fintype.card_bool, ← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

/-! ## Polynomial versus exponential growth -/

/-- Any fixed power is eventually dominated by `2 ^ n`. -/
theorem nat_pow_le_two_pow (k : ℕ) : ∀ᶠ n in atTop, n ^ k ≤ 2 ^ n := by
  have h : (fun n : ℕ => (n : ℝ) ^ k) =o[atTop] fun n : ℕ => (2 : ℝ) ^ n :=
    isLittleO_pow_const_const_pow_of_one_lt k (by norm_num)
  refine h.eventuallyLE.mono fun n hn => ?_
  simp only [Real.norm_eq_abs] at hn
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hn
  exact_mod_cast (by push_cast; exact hn : ((n ^ k : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ))

/-- A constant multiple of any fixed power of `n + 1` is eventually dominated by `2 ^ n`. -/
theorem const_mul_pow_le_two_pow (C k : ℕ) : ∀ᶠ m in atTop, C * (m + 1) ^ k ≤ 2 ^ m := by
  filter_upwards [eventually_ge_atTop (C * 2 ^ k), eventually_ge_atTop 1,
    nat_pow_le_two_pow (k + 1)] with m hm hm1 hm3
  calc C * (m + 1) ^ k ≤ C * (2 * m) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)
    _ = C * 2 ^ k * m ^ k := by rw [mul_pow]; ring
    _ ≤ m * m ^ k := Nat.mul_le_mul_right _ hm
    _ = m ^ (k + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ m := hm3

/-- **Polynomials are eventually dominated by `2 ^ (n / 4)`.** The exponent `n / 4` is the
threshold fed to the machine count: fast enough to eventually exceed every polynomial
description bound (this lemma), yet slow enough that the resulting machine count stays below
`2 ^ (2 ^ n)` (`eventually_count_lt`). -/
theorem eventually_poly_le (p : Polynomial ℕ) :
    ∀ᶠ n in atTop, p.eval n ≤ 2 ^ (n / 4) := by
  obtain ⟨C, k, hCk⟩ : ∃ C k : ℕ, ∀ n : ℕ, p.eval n ≤ C * (n + 1) ^ k := by
    refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i, p.natDegree, fun n => ?_⟩
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) i).trans
      (Nat.pow_le_pow_right (by omega) (by omega)))
  have htend : Tendsto (fun n : ℕ => n / 4) atTop atTop :=
    Nat.tendsto_div_const_atTop (by norm_num)
  filter_upwards [htend.eventually (const_mul_pow_le_two_pow (C * 4 ^ k) k)] with n hn
  calc p.eval n ≤ C * (n + 1) ^ k := hCk n
    _ ≤ C * 4 ^ k * (n / 4 + 1) ^ k := by
        rw [mul_assoc, ← mul_pow]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)
    _ ≤ 2 ^ (n / 4) := hn

/-- A crude closed-form bound on the squared machine count: for `9 * (d + 1) ≤ 2 ^ d` and
`d ≥ 1`, `B d ^ 2 ≤ 2 ^ (8 * d ^ 2)`. Uses `9 * (d + 1) ≤ 2 ^ d` on the statement/next-state
base and `d ^ 2 ≤ 2 ^ (2 * d)` on the initial-state factor. -/
theorem B_sq_le (d : ℕ) (hd : 9 * (d + 1) ≤ 2 ^ d) (hd1 : 1 ≤ d) :
    B d ^ 2 ≤ 2 ^ (8 * d ^ 2) := by
  have hd2 : d ^ 2 ≤ 2 ^ (2 * d) := by
    calc d ^ 2 ≤ (2 ^ d) ^ 2 := Nat.pow_le_pow_left (Nat.le_of_lt d.lt_two_pow_self) 2
      _ = 2 ^ (2 * d) := by rw [← pow_mul, Nat.mul_comm]
  calc B d ^ 2 = ((9 * (d + 1)) ^ (3 * d)) ^ 2 * d ^ 2 := by rw [B, mul_pow]
    _ = (9 * (d + 1)) ^ (6 * d) * d ^ 2 := by rw [← pow_mul]; ring_nf
    _ ≤ (2 ^ d) ^ (6 * d) * 2 ^ (2 * d) := Nat.mul_le_mul (Nat.pow_le_pow_left hd _) hd2
    _ = 2 ^ (6 * d ^ 2) * 2 ^ (2 * d) := by rw [← pow_mul]; ring_nf
    _ = 2 ^ (6 * d ^ 2 + 2 * d) := by rw [← pow_add]
    _ ≤ 2 ^ (8 * d ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith [hd1])

/-- **The squared machine count at the threshold size `2 ^ (n / 4)` stays below the
predicate count `2 ^ (2 ^ n)` eventually.** The count at size `d = 2 ^ (n / 4)` is at most
`2 ^ (8 * d ^ 2)` (`B_sq_le`, whose hypothesis `9 * (d + 1) ≤ 2 ^ d` holds cofinitely as
`d → ∞`), and its exponent `8 * d ^ 2 = 2 ^ (3 + n / 4 * 2)` is eventually below `2 ^ n`. -/
theorem eventually_count_lt :
    ∀ᶠ n in atTop, B (2 ^ (n / 4)) ^ 2 < 2 ^ (2 ^ n) := by
  have htwo : Tendsto (fun m : ℕ => 2 ^ m) atTop atTop :=
    tendsto_atTop_mono (fun m => (Nat.lt_two_pow_self).le) tendsto_id
  have htend : Tendsto (fun n : ℕ => 2 ^ (n / 4)) atTop atTop :=
    htwo.comp (Nat.tendsto_div_const_atTop (by norm_num))
  filter_upwards [htend.eventually (const_mul_pow_le_two_pow 9 1),
    eventually_ge_atTop 8] with n ha hn
  rw [pow_one] at ha
  refine lt_of_le_of_lt (B_sq_le _ ha Nat.one_le_two_pow) ?_
  apply Nat.pow_lt_pow_right (by norm_num)
  calc 8 * (2 ^ (n / 4)) ^ 2
      = 2 ^ (3 + n / 4 * 2) := by rw [show (8 : ℕ) = 2 ^ 3 from rfl, ← pow_mul, ← pow_add]
    _ < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-! ## The diagonal predicate -/

/-- A `Finset` family of subexponential cardinality misses a predicate eventually: if
`(S n).card < 2 ^ (2 ^ n)` cofinitely, some family `f` has `f n ∉ S n` cofinitely. -/
theorem exists_diagonal (S : (n : ℕ) → Finset (BitVec n → Bool))
    (hS : ∀ᶠ n in atTop, (S n).card < 2 ^ (2 ^ n)) :
    ∃ f : (n : ℕ) → BitVec n → Bool, ∀ᶠ n in atTop, f n ∉ S n := by
  classical
  have key : ∀ n, (S n).card < 2 ^ (2 ^ n) → ∃ g : BitVec n → Bool, g ∉ S n := by
    intro n hn
    have hlt : (S n).card < (Finset.univ : Finset (BitVec n → Bool)).card := by
      rw [Finset.card_univ, card_bitVec_fun]; exact hn
    obtain ⟨e, -, he⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    exact ⟨e, he⟩
  refine ⟨fun n => if h : (S n).card < 2 ^ (2 ^ n) then (key n h).choose else default, ?_⟩
  refine hS.mono fun n hn => ?_
  simp only [dif_pos hn]
  exact (key n hn).choose_spec

end Computability
