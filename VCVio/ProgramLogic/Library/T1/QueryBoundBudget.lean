/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.WP
public import PolyFun.Control.Monad.Algebra.WP
public import PolyFun.Control.Do.Spec
public import VCVio.ProgramLogic.Library.T1.QueryBound

/-!
# The budget reading: query bounds as core triples

A reading of oracle computations whose assertions are `ℕ → Prop`, indexed by the number of
queries left: a query needs a positive budget and continues at one less (`budgetSpec`, a
PolyFun `OpSpec` folded by `OpSpec.toMAlgOrdered`). `open scoped OracleComp.Budget` selects it.

`isTotalQueryBound_iff_triple` states `IsTotalQueryBound oa n` as
`⦃ fun k => n ≤ k ⦄ oa ⦃ fun _ _ => True ⦄`, and core's `vcgen` then steps through a `do`
program query by query, carrying the remaining budget as the state argument. The registered
rules are the exact rules of a query (`Spec.query`, `Spec.monadLift_query`). An opaque
sub-program with a known bound enters through `Spec.ofBound h`: it needs `L` queries left and
continues at every budget `j ≥ n - L`. The verification conditions are linear arithmetic, which
`omega` closes (`vcgen … with lia` does not use the truncated subtractions).
-/

@[expose] public section

open OracleSpec Std.WP PFunctor

namespace OracleComp.Budget

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}

/-- The budget reading: with `n` queries left, a query needs `0 < n` and continues at `n - 1`. -/
def budgetSpec (spec : OracleSpec.{0, 0} ι) : OpSpec spec.toPFunctor (ℕ → Prop) :=
  fun _ k n => 0 < n ∧ ∀ b, k b (n - 1)

/-- The budget reading is monotone in its continuation. -/
theorem budgetSpec_mono : (budgetSpec spec).Monotone :=
  fun _ _ _ h _ hn => ⟨hn.1, fun b => h b _ (hn.2 b)⟩

/-- The budget reading of oracle computations, as a core interpretation. -/
noncomputable scoped instance (priority := 1200) instWP :
    WPMonad (OracleComp spec) (ℕ → Prop) EStack⟨⟩ :=
  letI := (budgetSpec spec).toMAlgOrdered budgetSpec_mono
  MAlgOrdered.toWPMonad

open scoped OracleComp.Budget

/-- The weakest precondition of the budget reading is the budget fold. -/
theorem wp_eq (oa : OracleComp spec α) (Q : α → ℕ → Prop) (E : EStack⟨⟩) :
    wp oa Q E = FreeM.wpFold (budgetSpec spec) oa Q :=
  FreeM.toMAlgOrdered_μ_bind_pure _ budgetSpec_mono oa Q

/-- With every leaf accepted, the budget fold is the total query bound. -/
theorem wpFold_true_iff (oa : OracleComp spec α) (n : ℕ) :
    FreeM.wpFold (budgetSpec spec) oa (fun _ _ => True) n ↔ IsTotalQueryBound oa n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => exact iff_of_true trivial trivial
  | query_bind t mx ih =>
    rw [isTotalQueryBound_query_bind_iff]
    exact and_congr_right fun _ => forall_congr' fun u => ih u (n - 1)

/-- A total query bound is a triple of the budget reading at the trivial postcondition:
`rw [isTotalQueryBound_iff_triple]` turns a query-bound goal into a `vcgen` goal. -/
theorem isTotalQueryBound_iff_triple (oa : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound oa n ↔ ⦃ fun k => n ≤ k ⦄ oa ⦃ fun _ _ => True ⦄ := by
  rw [Triple.iff, wp_eq]
  exact ⟨fun h k hk => (wpFold_true_iff oa k).2 (h.mono hk),
    fun h => (wpFold_true_iff oa n).1 (h n le_rfl)⟩

/-- The exact rule of a primitive query, with lattice connectives that `vcgen` splits. -/
@[spec]
theorem Spec.query (t : spec.Domain) (Q : spec.Range t → ℕ → Prop) {E : EStack⟨⟩} :
    ⦃ Lean.Order.meet (fun n => 0 < n) (Lean.Order.iInf fun u => fun n => Q u (n - 1)) ⦄
      (query t : OracleComp spec (spec.Range t)) ⦃ Q; E ⦄ := by
  constructor
  rw [wp_eq]
  intro n h
  simp only [MAlgOrdered.meet_eq_inf, MAlgOrdered.iInf_eq_iInf, Pi.inf_apply, iInf_apply,
    inf_Prop_eq, iInf_Prop_eq] at h
  exact h

/-- `Spec.query` for a lifted primitive query, the form `vcgen` reaches inside a handler. -/
@[spec]
theorem Spec.monadLift_query (t : spec.Domain) (Q : spec.Range t → ℕ → Prop) {E : EStack⟨⟩} :
    ⦃ Lean.Order.meet (fun n => 0 < n) (Lean.Order.iInf fun u => fun n => Q u (n - 1)) ⦄
      (MonadLift.monadLift (liftM (OracleSpec.query t) : OracleQuery spec (spec.Range t)) :
        OracleComp spec (spec.Range t)) ⦃ Q; E ⦄ :=
  Spec.query t Q

/-- A program within budget `L` runs from any budget `n ≥ L` and leaves at least `n - L`. -/
theorem wpFold_of_isTotalQueryBound {x : OracleComp spec α} {L : ℕ}
    (h : IsTotalQueryBound x L) (Q : α → ℕ → Prop) (n : ℕ) (hn : L ≤ n)
    (hQ : ∀ a j, n - L ≤ j → Q a j) : FreeM.wpFold (budgetSpec spec) x Q n := by
  induction x using OracleComp.inductionOn generalizing n L with
  | pure x => exact hQ x n (Nat.sub_le n L)
  | query_bind t mx ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    exact ⟨by omega, fun u => ih u (h.2 u) (n - 1) (by omega) fun a j hj => hQ a j (by omega)⟩

/-- An opaque sub-program within budget `L`: it needs `L` queries left and continues at every
budget `j ≥ n - L`. Not registered, since it needs the bound: `vcgen [Spec.ofBound h]`. -/
theorem Spec.ofBound {x : OracleComp spec α} {L : ℕ} (h : IsTotalQueryBound x L)
    (Q : α → ℕ → Prop) {E : EStack⟨⟩} :
    ⦃ Lean.Order.meet (fun n => L ≤ n) (Lean.Order.iInf fun a => Lean.Order.iInf fun j =>
        Lean.Order.himp (fun n => n - L ≤ j) fun _ => Q a j) ⦄
      x ⦃ Q; E ⦄ := by
  constructor
  rw [wp_eq]
  intro n hn
  simp only [MAlgOrdered.meet_eq_inf, MAlgOrdered.iInf_eq_iInf, Pi.inf_apply, inf_Prop_eq,
    _root_.iInf_apply, iInf_Prop_eq, Lean.Order.himp_apply, Lean.Order.himp_prop_eq_imp] at hn
  exact wpFold_of_isTotalQueryBound h Q n hn.1 hn.2

end OracleComp.Budget
