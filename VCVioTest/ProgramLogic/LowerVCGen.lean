/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Unary.WP.LowerSpecs
public import PolyFun.Control.Do.Spec
public import VCVio.ProgramLogic.Unary.HandlerSpecs
public import VCVio.ProgramLogic.Tactics.PrVCGen

/-!
# Core `vcgen` under the lower-bound reading

Every registered rule of `OracleComp.Lower`, its unregistered averaging and support rules, its
bridges from lower bounds on events and expectations (including the generic bridge for an event of
a transformer stack), the transformer rules and a simulation under this reading, each with a bare
core `vcgen` inside `open scoped OracleComp.Lower`.

A lower-bound triple `⦃ r ⦄ oa ⦃ post ⦄` states `r ≤ wp⟦oa⟧ post`: the registered rules state that a
bound holding for every outcome holds in expectation, with core's indexed infimum, so the
verification conditions range over the outcomes; the averaging rules leave the exact sums.
-/

public section

open OracleSpec OracleComp Std.WP ENNReal OracleComp.ProgramLogic

namespace VCVioTest.ProgramLogic.LowerVCGen

open scoped OracleComp.Lower

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-! ## Rules -/

section Rules

variable [spec.AnswerMeasure]

/-- `Spec.monadLift_query`: a query, through the global `query` unfold. -/
example (t : spec.Domain) (f : spec.Range t → ℕ) :
    ⦃ 1 ⦄ (do let u ← (query t : OracleComp spec _); pure (f u == f u) : OracleComp spec Bool)
      ⦃ fun b => propInd (b = true) ⦄ := by
  vcgen
  simp [Lean.Order.rel_eq_le, propInd_eq_ite]

/-- `Spec.uniformSample`: a uniform draw, bounded on every outcome. -/
example : ⦃ 1 ⦄ (do let b ← $ᵗ Bool; pure (b || !b) : ProbComp Bool)
    ⦃ fun r => propInd (r = true) ⦄ := by
  vcgen
  simp [Lean.Order.rel_eq_le, propInd_eq_ite]

/-- `Spec.uniformFin`: a draw from `$[0..n]`. -/
example : ⦃ 1 ⦄ (do let i ← $[0..3]; pure i.val : ProbComp ℕ) ⦃ fun k => propInd (k ≤ 3) ⦄ := by
  vcgen
  simp [Lean.Order.rel_eq_le, propInd_eq_ite, Nat.lt_succ_iff.mp i.isLt]

/-- `Spec.replicate`: every list of possible outputs. -/
example : ⦃ 1 ⦄ (($ᵗ Bool).replicate 2 : ProbComp (List Bool))
    ⦃ fun l => propInd (l.length = 2) ⦄ := by
  vcgen
  rename_i xs
  simp [Lean.Order.rel_eq_le, propInd_eq_ite, xs.2.1]

/-- `Spec.uniformSample_sum`, passed: the exact average of a finite uniform draw. -/
example : ⦃ 1 / 2 ⦄ ($ᵗ Bool : ProbComp Bool) ⦃ fun b => propInd (b = true) ⦄ := by
  vcgen [OracleComp.Lower.Spec.uniformSample_sum]
  simp

/-- `Spec.ofSupport`, passed for an opaque sub-program: the bound on its support. -/
example (gen : OracleComp spec ℕ) (hg : ∀ n ∈ support gen, n ≤ 3) :
    ⦃ 1 ⦄ (do let n ← gen; pure (n ≤ 3 : Bool) : OracleComp spec Bool)
      ⦃ fun b => propInd (b = true) ⦄ := by
  vcgen [OracleComp.Lower.Spec.ofSupport gen]
  rename_i n
  simp [Lean.Order.rel_eq_le, propInd_eq_ite, hg n.1 n.2]

/-- `Spec.ofNecessary`, passed with a fact about the support in place of the support itself. -/
example (gen : OracleComp spec ℕ) (hg : ∀ n ∈ support gen, n ≤ 3) :
    ⦃ 1 ⦄ (do let n ← gen; pure (n ≤ 3 : Bool) : OracleComp spec Bool)
      ⦃ fun b => propInd (b = true) ⦄ := by
  vcgen [OracleComp.Lower.Spec.ofNecessary gen (· ≤ 3) hg]
  rename_i n
  simp [Lean.Order.rel_eq_le, propInd_eq_ite, n.2]

/-- `Spec.liftComp` into a sum: the inclusion preserves the answer measures, so neither
specification needs uniform answers. -/
example {τ : Type} {spec₂ : OracleSpec.{0, 0} τ} [spec₂.AnswerMeasure] (oa : OracleComp spec ℕ)
    (hg : ∀ n ∈ support oa, n ≤ 3) :
    1 ≤ Pr{let n ← liftComp oa (spec + spec₂)}[n ≤ 3] := by
  prvcgen [OracleComp.Lower.Spec.ofSupport oa]
  rename_i n
  simp [hg n.1 n.2]

end Rules

section Uniform

variable [spec.UniformAnswerMeasure]

/-- `Spec.query_uniform`, passed: the exact average of a uniform query. -/
example (t : spec.Domain) [Fintype (spec.Range t)] [DecidableEq (spec.Range t)]
    (u₀ : spec.Range t) :
    (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ ≤ Pr{let u ← (query t : OracleComp spec _)}[u = u₀] := by
  rw [le_prEvent_iff_triple]
  vcgen [OracleComp.Lower.Spec.query_uniform]
  simp only [lower_readback, propInd_eq_ite, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- `Spec.liftComp`: a lift between specifications with uniform answers on both. -/
example {τ : Type} {superSpec : OracleSpec.{0, 0} τ} [superSpec.UniformAnswerMeasure]
    [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec] (t : spec.Domain) (f : spec.Range t → ℕ) :
    ⦃ 1 ⦄
      (do
        let p ← liftComp (do let u ← query t; pure (f u, f u) : OracleComp spec _) superSpec
        pure (p.1 == p.2) : OracleComp superSpec Bool)
      ⦃ fun b => propInd (b = true) ⦄ := by
  vcgen
  simp [Lean.Order.rel_eq_le, propInd_eq_ite]

/-- `Spec.monadLift_liftComp`: the same lift written `liftM`. -/
example {τ : Type} {superSpec : OracleSpec.{0, 0} τ} [superSpec.UniformAnswerMeasure]
    [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec] (t : spec.Domain) (f : spec.Range t → ℕ) :
    ⦃ 1 ⦄
      (do
        let p ← (liftM (do let u ← query t; pure (f u, f u) : OracleComp spec _) :
          OracleComp superSpec _)
        pure (p.1 == p.2) : OracleComp superSpec Bool)
      ⦃ fun b => propInd (b = true) ⦄ := by
  vcgen
  simp [Lean.Order.rel_eq_le, propInd_eq_ite]

end Uniform

/-! ## Bridges -/

/-- A lower bound on an event is a triple on its indicator. -/
example : (1 : ℝ≥0∞) ≤ Pr{let b ← ($ᵗ Bool : ProbComp Bool)}[(b || !b) = true] := by
  rw [le_prEvent_iff_triple]
  vcgen
  simp [Lean.Order.rel_eq_le, propInd_eq_ite]

/-- A lower bound on an expectation is a triple on the function. -/
example : (3 : ℝ≥0∞) ≤ wp⟦($ᵗ Bool : ProbComp Bool)⟧ fun b => if b then 3 else 5 := by
  rw [le_wp_iff_triple]
  vcgen
  rename_i b
  cases b <;> simp [Lean.Order.rel_eq_le]
  norm_num

/-- `triple_add_frame` adds a constant to a triple of an adversary. -/
example (adv : ProbComp Bool) (r : ℝ≥0∞) (hadv : ⦃ r ⦄ adv ⦃ fun b => propInd (b = true) ⦄) :
    ⦃ 1 + r ⦄ (do let b ← adv; pure b) ⦃ fun b => propInd (b = true) + 1 ⦄ := by
  vcgen [triple_add_frame 1 hadv]
  simp [Lean.Order.rel_eq_le, add_comm]

/-- The infimum of the postcondition bounds the expectation. -/
example (g : Bool → ℝ≥0∞) : ⨅ b, g b ≤ wp⟦($ᵗ Bool : ProbComp Bool)⟧ g :=
  iInf_le_wp _ _

/-- `triple_const_mul` scales a triple of an adversary. -/
example (adv : ProbComp Bool) (r : ℝ≥0∞) (hadv : ⦃ r ⦄ adv ⦃ fun b => propInd (b = true) ⦄) :
    ⦃ 2⁻¹ * r ⦄ (do let b ← adv; let c ← $ᵗ Bool; pure (b && c))
      ⦃ fun b => propInd (b = true) ⦄ := by
  vcgen [triple_const_mul 2⁻¹ hadv, OracleComp.Lower.Spec.uniformSample_sum]
  cases b <;> simp [Lean.Order.rel_eq_le, ENNReal.div_eq_inv_mul]

/-! ## Transformers, loops and simulations -/

/-- `StateT.lift` through the base draw. -/
example : ⦃ fun _ => 1 ⦄ (StateT.lift ($ᵗ Bool) : StateT ℕ ProbComp Bool)
    ⦃ fun b _ => propInd ((b || !b) = true) ⦄ := by
  vcgen
  simp [Lean.Order.rel_eq_le, propInd_eq_ite]

/-- A handler written with `StateT.mk` runs its body at the incoming state. -/
example : ⦃ fun _ => 1 ⦄
    (StateT.mk fun s => (fun b => (b, s + 1)) <$> ($ᵗ Bool) : StateT ℕ ProbComp Bool)
    ⦃ fun _ s => propInd (0 < s) ⦄ := by
  vcgen
  simp [Lean.Order.rel_eq_le, propInd_eq_ite]

/-- Running a `StateT` program at a state, with the final state discarded. -/
example : ⦃ 1 ⦄ ((do
      let b ← StateT.lift ($ᵗ Bool)
      set (1 : ℕ)
      pure b : StateT ℕ ProbComp Bool).run' 0) ⦃ fun b => propInd ((b || !b) = true) ⦄ := by
  vcgen
  simp [Lean.Order.rel_eq_le, propInd_eq_ite]

/-- An `OptionT` lift succeeds; running it observes the option. -/
example : ⦃ 1 ⦄ (OptionT.lift ($ᵗ Bool) : OptionT ProbComp Bool).run
    ⦃ fun o => propInd (o ≠ none) ⦄ := by
  vcgen
  simp [Lean.Order.rel_eq_le, propInd_eq_ite]

/-- `OptionT.mk` is read through the option its body returns. -/
example : ⦃ 1 ⦄ (OptionT.mk ((fun b => some b) <$> ($ᵗ Bool)) : OptionT ProbComp Bool).run
    ⦃ fun o => propInd (o ≠ none) ⦄ := by
  vcgen
  simp [Lean.Order.rel_eq_le, propInd_eq_ite, Lean.Order.pushOption]

/-- `guard` on a true condition continues, through `Spec.guard_OptionT_iInf`. -/
example : ⦃ 1 ⦄ (do guard (1 < 2); OptionT.lift ($ᵗ Bool) : OptionT ProbComp Bool).run
    ⦃ fun o => propInd (o ≠ none) ⦄ := by
  vcgen
  · simp [Lean.Order.rel_eq_le, propInd_eq_ite]
  · rename_i h
    exact absurd h.down (by decide)

/-- An `ExceptT` lift succeeds; running it observes the result. -/
example : ⦃ 1 ⦄ (ExceptT.lift ($ᵗ Bool) : ExceptT String ProbComp Bool).run
    ⦃ fun r => propInd (∀ e, r ≠ .error e) ⦄ := by
  vcgen
  simp [Lean.Order.rel_eq_le, propInd_eq_ite]

/-- `ExceptT.mk` is read through the result its body returns. -/
example : ⦃ 1 ⦄ (ExceptT.mk ((fun b => .ok b) <$> ($ᵗ Bool)) : ExceptT String ProbComp Bool).run
    ⦃ fun r => propInd (∀ e, r ≠ .error e) ⦄ := by
  vcgen
  simp [Lean.Order.rel_eq_le, propInd_eq_ite, Lean.Order.pushExcept]

/-- `List.mapM` with an invariant relating the outputs so far to the elements consumed. -/
example : ⦃ 1 ⦄ ([1, 2, 3].mapM fun n => (fun b => if b then n else 0) <$> ($ᵗ Bool) :
    ProbComp (List ℕ)) ⦃ fun bs => propInd (bs.length = 3) ⦄ := by
  vcgen invariants
    · fun pref _ bs => propInd (bs.length = pref.length)
  all_goals simp [Lean.Order.rel_eq_le, propInd_eq_ite]

/-- The sequence combinators keep the first, respectively the second, value. -/
example : ⦃ 1 ⦄ (($ᵗ Bool) <* ($ᵗ Bool) : ProbComp Bool)
    ⦃ fun b => propInd ((b || !b) = true) ⦄ := by
  vcgen
  simp [Lean.Order.rel_eq_le, propInd_eq_ite]

example : ⦃ 1 ⦄ (($ᵗ Bool) *> ($ᵗ Bool) : ProbComp Bool)
    ⦃ fun b => propInd ((b || !b) = true) ⦄ := by
  vcgen
  simp [Lean.Order.rel_eq_le, propInd_eq_ite]

/-- A handler that resets its state after every query. -/
def resetHandler : QueryImpl (Unit →ₒ Bool) (StateT ℕ ProbComp) := fun _ => do
  let b ← StateT.lift ($ᵗ Bool)
  set (0 : ℕ)
  pure b

/-- `Spec.simulateQ`: an invariant stated as an indicator is kept by every query. -/
example {α : Type} (oa : OracleComp (Unit →ₒ Bool) α) :
    ⦃ fun s => propInd (s = 0) ⦄ (simulateQ resetHandler oa : StateT ℕ ProbComp α)
      ⦃ fun _ s => propInd (s = 0) ⦄ := by
  vcgen [resetHandler] invariants
    · fun s => propInd (s = 0)
  simp only [Lean.Order.rel_eq_le, propInd_eq_ite]
  split <;> simp

end VCVioTest.ProgramLogic.LowerVCGen
