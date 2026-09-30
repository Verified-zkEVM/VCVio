/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Tactics.PrVCGen
public import VCVio.ProgramLogic.Unary.HandlerSpecs

/-!
# `prvcgen`: core `vcgen` on events under the four readings

Each reading of `OracleComp` is exercised through `prvcgen`, two statements each:

* structural: probability one, over draws and over queries, and a support condition;
* angelic: positive probability, with a named witness per draw, and a possible output;
* expectation lower bounds: an event on every path, and an averaged draw;
* expectation upper bounds: probability zero, an averaged draw, a union bound over a loop as an
  invariant, and a union bound over the queries of an adversary as a ranked handler potential
  (`simulateQ_triple_ranked`);
* triples already stated, quantitative and structural, and their unfolded form, with the
  configuration passed to `vcgen`.

Equations split by antisymmetry: every-outcome rules and a loop potential settle both halves
outright, the averaging rules leave sums that `simp` evaluates, and an equation between two
programs is refused. The scope canaries check that a file-level reading does not reach `prvcgen`,
that the upper-bound reading is required for its triples (a bare `vcgen` fails), and that an
unsupported goal is refused.
-/

public section

open OracleSpec OracleComp Std.WP ENNReal OrderDual OracleComp.ProgramLogic

set_option experimental.vcgen true

namespace VCVioTest.ProgramLogic.PrVCGen

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-! ## Structural reading -/

example : Pr{let b ← $ᵗ Bool; let c ← $ᵗ Bool}[(b || c) = (c || b)] = 1 := by
  prvcgen
  exact Bool.or_comm _ _

example [spec.IsUniformMeasureSpec] (t : spec.Domain) (f : spec.Range t → ℕ) :
    Pr{let u ← (query t : OracleComp spec _); let v ← (query t : OracleComp spec _)}[
      f u + f v = f v + f u] = 1 := by
  prvcgen
  omega

example (n : ℕ) :
    ∀ x ∈ support (do let b ← $ᵗ Bool; pure (if b then n else n) : ProbComp ℕ), x = n := by
  prvcgen
  split <;> rfl

/-! ## Angelic reading -/

/-- Each draw leaves an existential; the witness is named and `prvcgen` continues. -/
example : 0 < Pr{let x ← $ᵗ (Fin 5); let y ← $ᵗ (Fin 5)}[x.val + y.val = 7] := by
  prvcgen
  refine ⟨3, ?_⟩
  prvcgen
  exact ⟨4, rfl⟩

example : ∃ x ∈ support ($ᵗ Bool), x = true := by
  prvcgen
  exact ⟨true, rfl⟩

/-! ## Expectation lower bounds -/

example : (1 : ℝ≥0∞) ≤ Pr{let b ← $ᵗ Bool}[(b || !b) = true] := by
  prvcgen
  simp

example : (1 / 2 : ℝ≥0∞) ≤ Pr{let b ← $ᵗ Bool}[b = true] := by
  prvcgen [OracleComp.Quantitative.Spec.uniformSample_sum]
  simp

/-! ## Expectation upper bounds -/

example : Pr{let b ← $ᵗ Bool; let c ← $ᵗ Bool}[(b && c) ≠ (c && b)] ≤ 0 := by
  prvcgen
  simp [Bool.and_comm]

example : Pr{let b ← $ᵗ Bool; let c ← $ᵗ Bool}[(b && c) ≠ (c && b)] = 0 := by
  prvcgen
  simp [Bool.and_comm]

example : Pr{let b ← $ᵗ Bool}[b = true] ≤ 1 / 2 := by
  prvcgen [OracleComp.Upper.Spec.uniformSample_avg]
  simp

/-- Averaging a flag update over a finite uniform draw: the union bound's one step. -/
theorem avg_or_le {β : Type} [Fintype β] [Nonempty β] (P : β → Prop) [DecidablePred P]
    (b : Bool) (c : ℝ≥0∞) :
    (∑ x, (propInd ((b || decide (P x)) = true) + c)) / (Fintype.card β : ℝ≥0∞) ≤
      propInd (b = true) + ((Finset.univ.filter P).card / (Fintype.card β : ℝ≥0∞) + c) := by
  have hc0 : (Fintype.card β : ℝ≥0∞) ≠ 0 := by simp
  have hct : (Fintype.card β : ℝ≥0∞) ≠ ⊤ := by simp
  rw [Finset.sum_add_distrib, ENNReal.add_div, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_comm, ENNReal.mul_div_cancel_right hc0 hct, ← add_assoc]
  gcongr
  cases b
  · simp [propInd_eq_ite]
  · simp [propInd_eq_ite, ENNReal.div_self hc0 hct]

/-- `q` rounds, each drawing from `Fin (n + 1)` and flagging a draw of `0`. -/
def hits (n q : ℕ) : ProbComp Bool :=
  (List.range q).foldlM (fun acc _ => do
    let x ← $ᵗ (Fin (n + 1))
    pure (acc || decide (x = 0))) false

/-- A union bound over a loop: the invariant is the flag's indicator plus the budget of the
remaining rounds. -/
example (n q : ℕ) : Pr{let b ← hits n q}[b = true] ≤ q * (n + 1 : ℝ≥0∞)⁻¹ := by
  prvcgen =>
    vcgen [hits, OracleComp.Upper.Spec.uniformSample_avg] invariants
    · fun _pref suff b => toDual (propInd (b = true) + suff.length * (n + 1 : ℝ≥0∞)⁻¹)
  case vc1 => simp
  case vc2 => simp
  case vc3 =>
    simp only [MeasureProgramLogic.wp_pure]
    refine (avg_or_le (fun x : Fin (n + 1) => x = 0) _ _).trans_eq ?_
    simp [add_mul, add_comm, Finset.filter_eq']

section RankedPotential

open scoped OracleComp.Upper

variable {D R : Type} [DecidableEq D] [SampleableType R] [Fintype R] [DecidableEq R]

/-- A lazily sampled random oracle that records whether a fresh answer lands in `T`. -/
def hitOracle (T : Finset R) : QueryImpl (D →ₒ R) (StateT ((D → Option R) × Bool) ProbComp) :=
  fun t => do
    let st ← get
    match st.1 t with
    | some u => pure u
    | none => do
      let u ← ($ᵗ R : ProbComp R)
      set (Function.update st.1 t (some u), st.2 || decide (u ∈ T))
      pure u

/-- The potential: the flag's indicator plus the budget of `k` remaining queries. -/
noncomputable def potential (T : Finset R) (k : ℕ) (st : (D → Option R) × Bool) : ℝ≥0∞ᵒᵈ :=
  toDual (propInd (st.2 = true) + k * (T.card / Fintype.card R))

/-- One query spends one unit of the budget. -/
theorem hitOracle_step [Nonempty R] (T : Finset R) (t : D) (k : ℕ) :
    ⦃ potential T (k + 1) ⦄ hitOracle (D := D) T t ⦃ fun _ => potential T k ⦄ := by
  unfold hitOracle potential
  vcgen [OracleComp.Upper.Spec.uniformSample_avg]
  · simp only [OracleComp.Upper.rel_iff, ofDual_toDual]
    gcongr
    simp
  · simp only [OracleComp.Upper.rel_iff, ofDual_toDual, binderNameHint, StateT.wp_apply_eq,
      StateT.run_bind, StateT.run_set, StateT.run_pure, ExactWPMonad.wp_bind,
      ExactWPMonad.wp_pure]
    refine (avg_or_le (· ∈ T) _ _).trans_eq ?_
    simp [add_mul, add_comm]

/-- `q` adaptive queries: the fresh answers land in `T` with probability at most
`q * |T| / |R|`. -/
example [Nonempty R] (T : Finset R) {α : Type} (adv : OracleComp (D →ₒ R) α) (q : ℕ)
    (hq : adv.IsTotalQueryBound q) :
    Pr{let z ← (simulateQ (hitOracle T) adv).run (fun _ => none, false)}[z.2.2 = true] ≤
      q * (T.card / Fintype.card R) := by
  have h := (simulateQ_triple_ranked (hitOracle T) (potential T) (hitOracle_step T)
    (fun k st => by simp only [OracleComp.Upper.rel_iff, potential, ofDual_toDual]; simp) adv q
    hq).le_wp (fun _ => none, false)
  rw [OracleComp.Upper.rel_iff] at h
  simpa [potential, StateT.wp_apply_eq, OracleComp.Upper.wp_eq] using h

end RankedPotential

/-! ## Triples

A triple already stated runs in the reading of its assertion type, and so does the unfolded form
`pre ⊑ wp oa post epost`. The configuration is passed to `vcgen`. -/

section Triples

variable [spec.IsMeasureSpec] {α β : Type}

/-- A quantitative triple: `vcgen` composes the triples of the two programs in the context. -/
example {oa : OracleComp spec α} {f : α → OracleComp spec β}
    {pre : ℝ≥0∞} {cut : α → ℝ≥0∞} {post : β → ℝ≥0∞}
    (hoa : ⦃ pre ⦄ oa ⦃ cut ⦄) (hf : ∀ x, ⦃ cut x ⦄ f x ⦃ post ⦄) :
    ⦃ pre ⦄ (oa >>= f) ⦃ post ⦄ := by
  prvcgen

open Lean.Order in
/-- The same triple, unfolded. -/
example {oa : OracleComp spec α} {f : α → OracleComp spec β}
    {pre : ℝ≥0∞} {cut : α → ℝ≥0∞} {post : β → ℝ≥0∞}
    (hoa : ⦃ pre ⦄ oa ⦃ cut ⦄) (hf : ∀ x, ⦃ cut x ⦄ f x ⦃ post ⦄) :
    pre ⊑ Std.WP.wp (oa >>= f) post Lean.Order.bot := by
  prvcgen

/-- A program without a rule stops `vcgen`, unless `errorOnMissingSpec := false` leaves its
weakest precondition as the verification condition. -/
example (oa : OracleComp spec α) (post : α → ℝ≥0∞) (pre : ℝ≥0∞) (h : pre ≤ wp⟦oa⟧ post) :
    ⦃ pre ⦄ (do let x ← oa; pure x) ⦃ post ⦄ := by
  fail_if_success prvcgen
  prvcgen (errorOnMissingSpec := false)
  exact h

end Triples

section StructuralTriple

open scoped OracleComp.Qualitative

/-- A triple with assertions in `Prop`, under the structural reading. -/
example : ⦃ True ⦄ (do let b ← $ᵗ Bool; pure (b || !b) : ProbComp Bool) ⦃ fun r => r = true ⦄ := by
  prvcgen
  simp

end StructuralTriple

/-! ## Scope canaries -/

section FileLevelReading

open scoped OracleComp.Qualitative

/-- A file-level structural reading does not reach `prvcgen`'s lower-bound reading. -/
example : (1 : ℝ≥0∞) ≤ Pr{let b ← $ᵗ Bool}[(b || !b) = true] := by
  prvcgen
  simp

end FileLevelReading

/-- An upper-bound triple needs its reading: a bare `vcgen` fails to build its rules, and does
not fall back to the global lower-bound reading. -/
example : Pr{let b ← $ᵗ Bool; let c ← (pure b : ProbComp Bool)}[b ≠ c] ≤ 0 := by
  rw [OracleComp.Upper.wp_le_iff_triple]
  fail_if_success vcgen
  open scoped OracleComp.Upper.Dispatch in vcgen
  all_goals simp

/-- A strict inequality other than positivity is not a triple of any reading. -/
example : Pr{let b ← $ᵗ Bool}[b = true] < 1 := by
  fail_if_success prvcgen
  simp [Finset.filter_eq']

/-! ## Equations, by antisymmetry

An equation `Pr{…}[p] = c` splits into the upper bound (dual reading) and the lower bound
(expectation reading); the rules, invariants and tail go to both halves, each half keeping the
rules stated in its reading. -/

/-- Every-outcome rules settle both halves. -/
example : 𝔼{let b ← $ᵗ Bool; let c ← $ᵗ Bool}[if (b && c) = (c && b) then (3 : ℝ≥0∞) else 7] =
    3 := by
  prvcgen
  all_goals simp [Bool.and_comm]

/-- A loop whose value a potential pins exactly: one invariant, stated without a carrier, serves
both halves. -/
def count (q : ℕ) : ProbComp ℕ :=
  (List.range q).foldlM (fun c _ => do
    let _ ← $ᵗ Bool
    pure (c + 1)) 0

example (q : ℕ) : 𝔼{let c ← count q}[(c : ℝ≥0∞)] = q := by
  prvcgen [count] invariants
    · fun _ suff c => ↑c + ↑suff.length
  all_goals
    apply le_of_eq
    push_cast [List.length_cons, List.length_range, List.length_nil]
    ring

/-- The averaging rules of both readings, passed together: each half ends in a sum that the
normal form's `simp` evaluates. -/
example : Pr{let b ← $ᵗ Bool}[b = true] = 1 / 2 := by
  prvcgen [OracleComp.Upper.Spec.uniformSample_avg, OracleComp.Quantitative.Spec.uniformSample_sum]
  all_goals simp

example : Pr{let b ← $ᵗ Bool; let c ← $ᵗ Bool}[(b && c) = true] = 1 / 4 := by
  prvcgen [OracleComp.Upper.Spec.uniformSample_avg, OracleComp.Quantitative.Spec.uniformSample_sum]
  all_goals simp [Finset.filter_eq', ENNReal.div_eq_inv_mul, ← ENNReal.mul_inv]
  all_goals norm_num

/-- Without uniform answers the structural bridge for `= 1` does not apply; the equation splits,
the upper half closes on the indicator's range, and the lower half leaves the event. -/
example [spec.IsMeasureSpec] (t : spec.Domain) (f : spec.Range t → ℕ) :
    Pr{let u ← (query t : OracleComp spec _); let v ← (query t : OracleComp spec _)}[
      f u + f v = f v + f u] = 1 := by
  prvcgen
  omega

/-- An equation between two programs' probabilities is a program equality, not a triple. -/
example : Pr{let b ← $ᵗ Bool}[b = true] = Pr{let b ← $ᵗ Bool}[b = true] := by
  fail_if_success prvcgen
  rfl

end VCVioTest.ProgramLogic.PrVCGen
