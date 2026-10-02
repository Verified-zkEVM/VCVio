/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Unary.WP.Upper
public import PolyFun.Control.Do.Spec
public import VCVio.ProgramLogic.Unary.HandlerSpecs
public import VCVio.ProgramLogic.Tactics.PrVCGen

/-!
# Core `vcgen` under the upper-bound reading

Every registered rule of `OracleComp.Upper`, its unregistered averaging and support rules, its
bridges from upper bounds on events and expectations (including the bridges for `OptionT` and
`ExceptT` programs, which supply the exception postcondition), the frame and scaling rules, the
transformer rules and a simulation under this reading, each with a bare core `vcgen` inside
`open scoped OracleComp.Upper`; and a triple of the reading through `prvcgen`.

An upper-bound triple `⦃ toDual ε ⦄ oa ⦃ post ⦄` states `wp⟦oa⟧ (ofDual ∘ post) ≤ ε`. The
verification conditions are read back through `OracleComp.Upper.rel_iff`, or the simp set
`upper_readback` that collects it with the `ofDual` pushes, before any other `simp` touches the
dual numerals.
-/

public section

open OracleSpec OracleComp Std.WP ENNReal OrderDual OracleComp.ProgramLogic

namespace VCVioTest.ProgramLogic.UpperVCGen

open scoped OracleComp.Upper

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-! ## Rules -/

section Rules

variable [spec.AnswerMeasure]

/-- `Spec.monadLift_query`: a query, through the global `query` unfold. -/
example (t : spec.Domain) (f : spec.Range t → ℕ) :
    ⦃ toDual 0 ⦄
      (do let u ← (query t : OracleComp spec _); pure (f u == f u) : OracleComp spec Bool)
      ⦃ fun b => toDual (propInd (b = false)) ⦄ := by
  vcgen
  simp [propInd_eq_ite]

/-- `Spec.uniformSample`: a uniform draw, bounded on every outcome. -/
example : ⦃ toDual 0 ⦄ (do let b ← $ᵗ Bool; pure (b && !b) : ProbComp Bool)
    ⦃ fun r => toDual (propInd (r = true)) ⦄ := by
  vcgen
  simp [propInd_eq_ite]

/-- `Spec.uniformFin`: a draw from `$[0..n]`. -/
example : ⦃ toDual 0 ⦄ (do let i ← $[0..3]; pure i.val : ProbComp ℕ)
    ⦃ fun k => toDual (propInd (4 ≤ k)) ⦄ := by
  vcgen
  simp [propInd_eq_ite, Nat.not_le.mpr i.isLt]

/-- `Spec.replicate`: every list of possible outputs. -/
example : ⦃ toDual 0 ⦄ (($ᵗ Bool).replicate 2 : ProbComp (List Bool))
    ⦃ fun l => toDual (propInd (l.length ≠ 2)) ⦄ := by
  vcgen
  rename_i xs
  simp [propInd_eq_ite, xs.2.1]

/-- `Spec.uniformSample_avg`, passed: the exact average of a finite uniform draw. -/
example : ⦃ toDual (1 / 2) ⦄ ($ᵗ Bool : ProbComp Bool)
    ⦃ fun b => toDual (propInd (b = true)) ⦄ := by
  vcgen [OracleComp.Upper.Spec.uniformSample_avg]
  simp

/-- `Spec.ofSupport`, passed for an opaque sub-program: the bound on its support. -/
example (gen : OracleComp spec ℕ) (hg : ∀ n ∈ support gen, n ≤ 3) :
    ⦃ toDual 0 ⦄ (do let n ← gen; pure n : OracleComp spec ℕ)
      ⦃ fun n => toDual (propInd (4 ≤ n)) ⦄ := by
  vcgen [OracleComp.Upper.Spec.ofSupport gen]
  rename_i n
  simp [propInd_eq_ite, Nat.not_le.mpr (Nat.lt_succ_of_le (hg n.1 n.2))]

/-- `Spec.ofNecessary`, passed with a fact about the support in place of the support itself. -/
example (gen : OracleComp spec ℕ) (hg : ∀ n ∈ support gen, n ≤ 3) :
    ⦃ toDual 0 ⦄ (do let n ← gen; pure n : OracleComp spec ℕ)
      ⦃ fun n => toDual (propInd (4 ≤ n)) ⦄ := by
  vcgen [OracleComp.Upper.Spec.ofNecessary gen (· ≤ 3) hg]
  rename_i n
  simp [propInd_eq_ite, Nat.not_le.mpr (Nat.lt_succ_of_le n.2)]

/-- `Spec.ofNecessary_stateT`, passed with a handler triple of the necessary reading read on the
support: from a cache above `cache₀`, the answer is cached with certainty. -/
example [DecidableEq ι] (t : spec.Domain) (cache₀ : QueryCache spec) :
    ⦃ fun cache => toDual (propInd (¬ cache₀ ≤ cache)) ⦄
      (do let v ← cachingOracle t; pure v :
        StateT (QueryCache spec) (OracleComp spec) (spec.Range t))
      ⦃ fun v cache' => toDual (propInd (cache' t ≠ some v)) ⦄ := by
  vcgen [OracleComp.Upper.Spec.ofNecessary_stateT (cachingOracle t)
    (fun cache v cache' => cache₀ ≤ cache → cache' t = some v)
    (fun cache z hz hle => ((triple_stateT_iff_forall_support _ _ _ ⟨⟩).1
      (cachingOracle_triple t cache₀) cache hle z.1 z.2 hz).2)]
  rename_i s z
  simp only [upper_readback]
  by_cases hle : cache₀ ≤ s
  · simp [z.2 hle]
  · simpa [hle] using propInd_le_one _

/-- `Spec.liftComp` into a sum: the inclusion preserves the answer measures, so neither
specification needs uniform answers. -/
example {τ : Type} {spec₂ : OracleSpec.{0, 0} τ} [spec₂.AnswerMeasure] (oa : OracleComp spec ℕ)
    (ε : ℝ≥0∞) (h : Pr{let n ← oa}[n = 0] ≤ ε) :
    Pr{let n ← liftComp oa (spec + spec₂)}[n = 0] ≤ ε := by
  prvcgen [OracleComp.Upper.Spec.ofWp oa]
  simpa using h

/-- `wp_liftComp` into a sum, as an expectation equation. -/
example {τ : Type} {spec₂ : OracleSpec.{0, 0} τ} [spec₂.AnswerMeasure] (oa : OracleComp spec ℕ)
    (g : ℕ → ℝ≥0∞) : wp⟦liftComp oa (spec + spec₂)⟧ g = wp⟦oa⟧ g := by
  simp only [expect_eval]

/-- The output measure of a lift into a sum. -/
example {τ : Type} {spec₂ : OracleSpec.{0, 0} τ} [spec₂.AnswerMeasure] (oa : OracleComp spec ℕ) :
    𝒟[liftComp oa (spec + spec₂)] = 𝒟[oa] :=
  evalDist_liftComp oa

/-- `Spec.ofWp`, passed for an opaque draw: its expectation stays in the condition, for the
hypothesis on it to close. -/
example (gen : OracleComp spec ℕ) (ε : ℝ≥0∞) (hg : Pr{let n ← gen}[n = 0] ≤ ε) :
    ⦃ toDual ε ⦄ (do let n ← gen; pure (n + 0) : OracleComp spec ℕ)
      ⦃ fun n => toDual (propInd (n = 0)) ⦄ := by
  vcgen [OracleComp.Upper.Spec.ofWp gen]
  simp only [upper_readback]
  simpa using hg

/-- `Spec.bind_of_bad`, passed with its event: the bad event of the first draw is charged, the
bound on the postcondition and the continuations off the event, on the support, are the
conditions, and a triple in the context serves the continuations. -/
example (gen : OracleComp spec ℕ) (f : ℕ → OracleComp spec Bool) (ε : ℝ≥0∞)
    (hf : ∀ n ∈ support gen, n ≠ 0 →
      ⦃ toDual ε ⦄ f n ⦃ fun b => toDual (propInd (b = true)) ⦄) :
    ⦃ toDual (Pr{let n ← gen}[n = 0] + ε) ⦄ (gen >>= f)
      ⦃ fun b => toDual (propInd (b = true)) ⦄ := by
  vcgen [OracleComp.Upper.Spec.bind_of_bad gen f (· = 0)]
  · simp only [upper_readback]
  all_goals assumption

end Rules

section Uniform

variable [spec.UniformAnswerMeasure]

/-- `Spec.query_avg`, passed: the exact average of a uniform query. -/
example (t : spec.Domain) [Fintype (spec.Range t)] [DecidableEq (spec.Range t)]
    (u₀ : spec.Range t) :
    Pr{let u ← (query t : OracleComp spec _)}[u = u₀] ≤ (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ := by
  rw [OracleComp.Upper.prEvent_le_iff_triple]
  vcgen [OracleComp.Upper.Spec.query_avg]
  rw [OracleComp.Upper.rel_iff]
  simp only [ofDual_toDual, predInd_apply, propInd_eq_ite, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, le_refl]

/-- `Spec.monadLift_query_avg`, passed: the same average on the lifted query. -/
example (t : spec.Domain) [Fintype (spec.Range t)] [DecidableEq (spec.Range t)]
    (u₀ : spec.Range t) :
    Pr{let u ← (query t : OracleComp spec _)}[u = u₀] ≤ (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ := by
  rw [OracleComp.Upper.prEvent_le_iff_triple]
  vcgen [OracleComp.Upper.Spec.monadLift_query_avg]
  rw [OracleComp.Upper.rel_iff]
  simp only [ofDual_toDual, predInd_apply, propInd_eq_ite, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, le_refl]

/-- `Spec.liftComp`: a lift between specifications with uniform answers on both. -/
example {τ : Type} {superSpec : OracleSpec.{0, 0} τ} [superSpec.UniformAnswerMeasure]
    [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec] (t : spec.Domain) (f : spec.Range t → ℕ) :
    ⦃ toDual 0 ⦄
      (do
        let p ← liftComp (do let u ← query t; pure (f u, f u) : OracleComp spec _) superSpec
        pure (p.1 == p.2) : OracleComp superSpec Bool)
      ⦃ fun b => toDual (propInd (b = false)) ⦄ := by
  vcgen
  simp [propInd_eq_ite]

/-- `Spec.monadLift_liftComp`: the same lift written `liftM`. -/
example {τ : Type} {superSpec : OracleSpec.{0, 0} τ} [superSpec.UniformAnswerMeasure]
    [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec] (t : spec.Domain) (f : spec.Range t → ℕ) :
    ⦃ toDual 0 ⦄
      (do
        let p ← (liftM (do let u ← query t; pure (f u, f u) : OracleComp spec _) :
          OracleComp superSpec _)
        pure (p.1 == p.2) : OracleComp superSpec Bool)
      ⦃ fun b => toDual (propInd (b = false)) ⦄ := by
  vcgen
  simp [propInd_eq_ite]

end Uniform

/-! ## Bridges -/

/-- An upper bound on an expectation is a triple on the dual of the function. -/
example : wp⟦($ᵗ Bool : ProbComp Bool)⟧ (fun b => if b then 3 else 5) ≤ 5 := by
  rw [OracleComp.Upper.wp_le_iff_triple]
  vcgen
  rename_i b
  cases b <;> simp only [upper_readback] <;> simp
  norm_num

/-- An event of an `OptionT` program: the bridge charges a failure `0`. -/
example : Pr{let b ← (do guard (1 < 2); OptionT.lift ($ᵗ Bool) : OptionT ProbComp Bool)}[
    (b && !b) = true] ≤ 0 := by
  rw [OracleComp.Upper.OptionT.wp_le_iff_triple]
  vcgen
  all_goals simp [propInd_eq_ite]

/-- An event of an `ExceptT` program: an exception is charged `0`, so only the successful
outputs count. -/
example : Pr{let b ← (do
      let b ← ExceptT.lift ($ᵗ Bool)
      if b then throw "stop" else pure b : ExceptT String ProbComp Bool)}[b = true] ≤ 0 := by
  rw [OracleComp.Upper.ExceptT.wp_le_iff_triple]
  vcgen
  all_goals simp_all [propInd_eq_ite]

/-- The expectation is at most the supremum of the postcondition. -/
example (g : Bool → ℝ≥0∞) : wp⟦($ᵗ Bool : ProbComp Bool)⟧ g ≤ ⨆ b, g b :=
  OracleComp.Upper.wp_le_iSup _ _

/-- `triple_add_frame` adds a budget to a triple of an adversary; `triple_const_mul` scales it. -/
example (adv : ProbComp Bool) (ε : ℝ≥0∞)
    (hadv : ⦃ toDual ε ⦄ adv ⦃ fun b => toDual (propInd (b = true)) ⦄) :
    ⦃ toDual (1 + ε) ⦄ (do let b ← adv; pure b) ⦃ fun b => toDual (1 + propInd (b = true)) ⦄ := by
  vcgen [OracleComp.Upper.triple_add_frame 1 hadv]
  all_goals simp

example (adv : ProbComp Bool) (ε : ℝ≥0∞)
    (hadv : ⦃ toDual ε ⦄ adv ⦃ fun b => toDual (propInd (b = true)) ⦄) :
    ⦃ toDual (2 * ε) ⦄ (do let b ← adv; pure b) ⦃ fun b => toDual (2 * propInd (b = true)) ⦄ := by
  vcgen [OracleComp.Upper.triple_const_mul 2 hadv]
  all_goals simp

/-! ## Transformers, loops and simulations -/

/-- `StateT.lift` through the base draw. -/
example : ⦃ fun _ => toDual 0 ⦄ (StateT.lift ($ᵗ Bool) : StateT ℕ ProbComp Bool)
    ⦃ fun b _ => toDual (propInd ((b && !b) = true)) ⦄ := by
  vcgen
  simp [propInd_eq_ite]

/-- A handler written with `StateT.mk` runs its body at the incoming state. -/
example : ⦃ fun _ => toDual 0 ⦄
    (StateT.mk fun s => (fun b => (b, s + 1)) <$> ($ᵗ Bool) : StateT ℕ ProbComp Bool)
    ⦃ fun _ s => toDual (propInd (s = 0)) ⦄ := by
  vcgen
  simp [propInd_eq_ite]

/-- Running a `StateT` program at a state, with the final state discarded. -/
example : ⦃ toDual 0 ⦄ ((do
      let b ← StateT.lift ($ᵗ Bool)
      set (1 : ℕ)
      pure b : StateT ℕ ProbComp Bool).run' 0)
    ⦃ fun b => toDual (propInd ((b && !b) = true)) ⦄ := by
  vcgen
  simp [propInd_eq_ite]

/-- An `OptionT` lift never fails; running it observes the option. -/
example : ⦃ toDual 0 ⦄ (OptionT.lift ($ᵗ Bool) : OptionT ProbComp Bool).run
    ⦃ fun o => toDual (propInd (o = none)) ⦄ := by
  vcgen
  simp [propInd_eq_ite]

/-- `OptionT.mk` is read through the option its body returns. -/
example : ⦃ toDual 0 ⦄ (OptionT.mk ((fun b => some b) <$> ($ᵗ Bool)) : OptionT ProbComp Bool).run
    ⦃ fun o => toDual (propInd (o = none)) ⦄ := by
  vcgen
  simp [propInd_eq_ite, Lean.Order.pushOption]

/-- `guard` on a false condition fails: with the exception postcondition written, the failure
costs nothing. -/
example : ⦃ toDual 0 ⦄ (do guard (2 < 1); OptionT.lift ($ᵗ Bool) : OptionT ProbComp Bool)
    ⦃ fun b => toDual (propInd (b = true)); (fun _ => toDual 0, Lean.Order.bot) ⦄ := by
  vcgen
  rename_i h _
  exact absurd h.down (by decide)

/-- An `ExceptT` lift never throws; running it observes the result. -/
example : ⦃ toDual 0 ⦄ (ExceptT.lift ($ᵗ Bool) : ExceptT String ProbComp Bool).run
    ⦃ fun r => toDual (propInd (∃ e, r = .error e)) ⦄ := by
  vcgen
  simp [propInd_eq_ite]

/-- `ExceptT.mk` is read through the result its body returns. -/
example : ⦃ toDual 0 ⦄
    (ExceptT.mk ((fun b => .ok b) <$> ($ᵗ Bool)) : ExceptT String ProbComp Bool).run
    ⦃ fun r => toDual (propInd (∃ e, r = .error e)) ⦄ := by
  vcgen
  simp [propInd_eq_ite, Lean.Order.pushExcept]

/-- `List.mapM` with a potential: the outputs so far are as many as the elements consumed. -/
example : ⦃ toDual 0 ⦄ ([1, 2, 3].mapM fun n => (fun b => if b then n else 0) <$> ($ᵗ Bool) :
    ProbComp (List ℕ)) ⦃ fun bs => toDual (propInd (bs.length ≠ 3)) ⦄ := by
  vcgen invariants
    · fun pref _ bs => toDual (propInd (bs.length ≠ pref.length))
  all_goals simp [propInd_eq_ite]

/-- The sequence combinators keep the first, respectively the second, value. -/
example : ⦃ toDual 0 ⦄ (($ᵗ Bool) <* ($ᵗ Bool) : ProbComp Bool)
    ⦃ fun b => toDual (propInd ((b && !b) = true)) ⦄ := by
  vcgen
  simp [propInd_eq_ite]

example : ⦃ toDual 0 ⦄ (($ᵗ Bool) *> ($ᵗ Bool) : ProbComp Bool)
    ⦃ fun b => toDual (propInd ((b && !b) = true)) ⦄ := by
  vcgen
  simp [propInd_eq_ite]

/-- A handler that never raises its flag. -/
def quietHandler : QueryImpl (Unit →ₒ Bool) (StateT Bool ProbComp) := fun _ =>
  StateT.lift ($ᵗ Bool)

/-- `Spec.simulateQ`: a potential on the handler state, here the probability that the flag is
up, is not raised by any query. -/
example {α : Type} (oa : OracleComp (Unit →ₒ Bool) α) :
    ⦃ fun s => toDual (propInd (s = true)) ⦄ (simulateQ quietHandler oa : StateT Bool ProbComp α)
      ⦃ fun _ s => toDual (propInd (s = true)) ⦄ := by
  vcgen [quietHandler] invariants
    · fun s => toDual (propInd (s = true))

/-! ## The reading through `prvcgen` -/

/-- A triple whose assertions are in `ℝ≥0∞ᵒᵈ` is run in the upper-bound reading. -/
example : ⦃ toDual 0 ⦄ (do let b ← $ᵗ Bool; pure (b && !b) : ProbComp Bool)
    ⦃ fun r => toDual (propInd (r = true)) ⦄ := by
  prvcgen
  simp [propInd_eq_ite]

/-! ## The generic dual reading

A bound over a monad with lawful measure semantics other than `OracleComp` is read by
`ExpectationWP.Upper`: the bridge states the triple with the scope's instance, core's rules read
`pure` and `bind`, and an opaque draw passes through `ExpectationWP.Upper.Spec.ofWp`. -/

section GenericMonad

variable {m : Type → Type} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]

/-- A guess against an opaque challenge, over any monad with measure semantics. -/
example (challenge : m ℕ) (ε : ℝ≥0∞) (hs : ∀ guess, Pr{let s ← challenge}[guess = s] ≤ ε)
    (guess : ℕ) :
    Pr{let s ← challenge; let _ ← (pure () : m Unit)}[guess = s] ≤ ε := by
  prvcgen [ExpectationWP.Upper.Spec.ofWp challenge]
  simpa using hs guess

/-- A guess drawn by an opaque prover, then an opaque challenge: the prover's draw is bounded by
its largest value (`ExpectationWP.Upper.Spec.ofSup`), leaving one condition per guess for the
challenge's per-guess bound. -/
example (prover challenge : m ℕ) (ε : ℝ≥0∞)
    (hs : ∀ guess, Pr{let s ← challenge}[guess = s] ≤ ε) :
    Pr{let guess ← prover; let s ← challenge}[guess = s] ≤ ε := by
  prvcgen [ExpectationWP.Upper.Spec.ofSup prover, ExpectationWP.Upper.Spec.ofWp challenge]
  rename_i guess
  simpa using hs guess

end GenericMonad

end VCVioTest.ProgramLogic.UpperVCGen
