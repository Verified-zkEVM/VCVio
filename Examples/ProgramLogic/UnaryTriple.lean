/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Tactics.PrVCGen
public import VCVio.OracleComp.Constructions.Replicate.Basic

/-!
# Quantitative triples with `prvcgen`

`prvcgen` runs core's `vcgen` on a quantitative triple `⦃ pre ⦄ oa ⦃ post ⦄` of an oracle
computation, whose assertions are expectations in `ℝ≥0∞`. `vcgen` steps through binds, branches
and matches, applies triples of sub-programs found in the local context, and uses the registered
`@[spec]` rules; a loop takes an invariant, as an explicit rule such as `triple_replicate` or as
`invariants` for `List.foldlM`. An opaque sub-program is bounded on its support by
`OracleComp.Quantitative.Spec.ofSupport`.
-/

@[expose] public section

open ENNReal OracleSpec OracleComp
open Lean.Order
open OracleComp.ProgramLogic
open scoped OracleComp.ProgramLogic Std.WP
open scoped OracleComp.Quantitative

universe u

variable {ι : Type u} {spec : OracleSpec ι}
variable [OracleSpec.IsMeasureSpec spec]
variable {α β γ : Type}

/-! ## Binds -/

example {oa : OracleComp spec α} {f : α → OracleComp spec β}
    {pre : ℝ≥0∞} {cut : α → ℝ≥0∞} {post : β → ℝ≥0∞}
    (hoa : ⦃ pre ⦄ oa ⦃ cut ⦄)
    (hob : ∀ x, ⦃ cut x ⦄ f x ⦃ post ⦄) :
    ⦃ pre ⦄ (oa >>= f) ⦃ post ⦄ := by
  prvcgen

example {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {oc : β → OracleComp spec γ}
    {cut1 : α → ℝ≥0∞} {cut2 : β → ℝ≥0∞} {post : γ → ℝ≥0∞}
    (h1 : ⦃ 1 ⦄ oa ⦃ cut1 ⦄)
    (h2 : ∀ x, ⦃ cut1 x ⦄ ob x ⦃ cut2 ⦄)
    (h3 : ∀ y, ⦃ cut2 y ⦄ oc y ⦃ post ⦄) :
    ⦃ 1 ⦄ (do
      let x ← oa
      let y ← ob x
      oc y) ⦃ post ⦄ := by
  prvcgen

example {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {post : β → ℝ≥0∞}
    (h : ⦃ 1 ⦄ oa ⦃ fun x => wp⟦ob x⟧ post ⦄) :
    ⦃ 1 ⦄ (oa >>= ob) ⦃ post ⦄ := by
  prvcgen

example (x : α) (post : α → ℝ≥0∞) :
    ⦃ post x ⦄ (pure x : OracleComp spec α) ⦃ post ⦄ := by
  prvcgen

/-- A continuation specified only on the support of the first program: the triple of
`Spec.ofSupport oa` bounds `oa` by the infimum of the continuation's triples over its support. -/
example (oa : OracleComp spec α) (f : α → OracleComp spec Bool)
    (h : ∀ x ∈ support oa, Pr{let y ← f x}[y = true] = 1) :
    ⦃ 1 ⦄ (do
      let x ← oa
      f x) ⦃ fun y => if y = true then 1 else 0 ⦄ := by
  classical
  have h' (x : α) (hx : x ∈ support oa) : ⦃ 1 ⦄ f x ⦃ fun y => if y = true then 1 else 0 ⦄ := by
    simpa [propInd_eq_ite] using triple_prEvent_eq_one (oa := f x) (p := (· = true)) (h x hx)
  prvcgen [OracleComp.Quantitative.Spec.ofSupport oa, h']
  exact Subtype.property _

/-! ## Branches -/

example (c : Prop) [Decidable c] {oa ob : OracleComp spec α}
    {pre : ℝ≥0∞} {post : α → ℝ≥0∞}
    (ht : ⦃ pre ⦄ oa ⦃ post ⦄) (hf : ⦃ pre ⦄ ob ⦃ post ⦄) :
    ⦃ pre ⦄ (if c then oa else ob) ⦃ post ⦄ := by
  prvcgen

example (n : ℕ) {oa : n > 0 → OracleComp spec α} {ob : ¬(n > 0) → OracleComp spec α}
    {pre : ℝ≥0∞} {post : α → ℝ≥0∞}
    (ht : ∀ h, ⦃ pre ⦄ oa h ⦃ post ⦄) (hf : ∀ h, ⦃ pre ⦄ ob h ⦃ post ⦄) :
    ⦃ pre ⦄ (dite (n > 0) oa ob) ⦃ post ⦄ := by
  prvcgen

example {f : α → OracleComp spec β} {g : OracleComp spec β}
    (x : Option α) {pre : ℝ≥0∞} {post : β → ℝ≥0∞}
    (hsome : ∀ a, ⦃ pre ⦄ f a ⦃ post ⦄) (hnone : ⦃ pre ⦄ g ⦃ post ⦄) :
    ⦃ pre ⦄ (match x with | some a => f a | none => g) ⦃ post ⦄ := by
  prvcgen

/-! ## Loops

One unrolling of a loop is its evaluation equation (`expect_eval`); a loop as a whole takes an
invariant. -/

example (oa : OracleComp spec α) (n : ℕ) (pre : ℝ≥0∞) (post : List α → ℝ≥0∞)
    (h :
      pre ≤ wp⟦oa⟧ (fun x => wp⟦oa.replicate n⟧ (fun xs => post (x :: xs)))) :
    ⦃ pre ⦄ oa.replicate (n + 1) ⦃ post ⦄ := by
  rw [← le_wp_iff_triple]
  simpa only [expect_norm, expect_eval] using h

example (x : α) (xs : List α) (f : α → OracleComp spec β)
    (pre : ℝ≥0∞) (post : List β → ℝ≥0∞)
    (h : pre ≤ wp⟦f x⟧ (fun y => wp⟦xs.mapM f⟧ (fun ys => post (y :: ys)))) :
    ⦃ pre ⦄ (x :: xs).mapM f ⦃ post ⦄ := by
  rw [← le_wp_iff_triple]
  simpa only [expect_norm, expect_eval] using h

example (x : α) (xs : List α) (f : β → α → OracleComp spec β)
    (init : β) (pre : ℝ≥0∞) (post : β → ℝ≥0∞)
    (h : pre ≤ wp⟦f init x⟧ (fun s => wp⟦xs.foldlM f s⟧ post)) :
    ⦃ pre ⦄ (x :: xs).foldlM f init ⦃ post ⦄ := by
  rw [← le_wp_iff_triple]
  simpa only [expect_norm, expect_eval] using h

example {oa : OracleComp spec α} {I : ℝ≥0∞} {n : ℕ}
    {pre : ℝ≥0∞} {post : List α → ℝ≥0∞}
    (hpre : pre ≤ I) (hpost : ∀ xs, I ≤ post xs)
    (hstep : ⦃ I ⦄ oa ⦃ fun _ => I ⦄) :
    ⦃ pre ⦄ oa.replicate n ⦃ post ⦄ := by
  prvcgen [triple_replicate_inv hstep]
  all_goals simp_all

example {σ : Type} {f : σ → α → OracleComp spec σ} {l : List α} {s₀ : σ}
    {I : σ → ℝ≥0∞}
    (hstep : ∀ s x, x ∈ l → ⦃ I s ⦄ f s x ⦃ I ⦄) :
    ⦃ I s₀ ⦄ l.foldlM f s₀ ⦃ I ⦄ := by
  prvcgen invariants · fun _ _ s => I s
  all_goals simp_all

example {σ : Type} {f : σ → α → OracleComp spec σ} {l : List α} {s₀ : σ}
    {I : σ → ℝ≥0∞} {pre : ℝ≥0∞} {post : σ → ℝ≥0∞}
    (hpre : pre ≤ I s₀) (hpost : ∀ s, I s ≤ post s)
    (hstep : ∀ s x, x ∈ l → ⦃ I s ⦄ f s x ⦃ I ⦄) :
    ⦃ pre ⦄ l.foldlM f s₀ ⦃ post ⦄ := by
  prvcgen invariants · fun _ _ s => I s
  all_goals simp_all

/-! ## Constant bounds

Every run of an oracle computation terminates, so a constant is a lower bound of the expectation
of itself; `Spec.ofSupport` states it for any program. -/

example {oa : OracleComp spec α} {I : ℝ≥0∞} {n : ℕ} :
    ⦃ I ⦄ oa.replicate n ⦃ fun _ => I ⦄ := by
  prvcgen [OracleComp.Quantitative.Spec.ofSupport (OracleComp.replicate n oa)]

example {f : α → OracleComp spec β} {l : List α} {I : ℝ≥0∞} :
    ⦃ I ⦄ l.mapM f ⦃ fun _ => I ⦄ := by
  prvcgen [OracleComp.Quantitative.Spec.ofSupport (l.mapM f : OracleComp spec (List β))]
