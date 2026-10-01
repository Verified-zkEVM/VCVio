/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Unary.WP.QualitativeSpecs
public import VCVio.ProgramLogic.Unary.WP.QuantitativeSpecs
public import VCVio.ProgramLogic.Unary.WP.Coherence
public import VCVio.ProgramLogic.Unary.HandlerSpecs

/-!
# Core `vcgen` on oracle computations

Each `@[spec]` rule for oracle computations, and each bridge between events and triples, is
exercised with a bare core `vcgen`:

* structural reading (`open scoped OracleComp.Qualitative`): uniform draws `$ᵗ` and `$[0..n]`,
  `replicate`, `liftComp`, an opaque sub-program through `Spec.ofSupport`, a sum handler lifted to
  a whole simulation into `ProbComp`, and an append-log handler lifted to a whole simulation;
* events as structural triples: probability one, mass one on `true`, and probability zero;
* quantitative reading (the global instance): lower bounds through queries and `$ᵗ`, an event
  normal form, a support-conditioned bind, and a scaled adversary spec;
* the transformers' constructors, lifts and runners, `List.mapM` with an invariant, the sequence
  combinators, a query inside a transformer through the `query` unfold, and a simulation with a
  handler invariant.
-/

public section

open OracleSpec OracleComp Std.WP ENNReal OracleComp.ProgramLogic

namespace VCVioTest.ProgramLogic.CoreVCGen

/-! ## Structural reading -/

section Structural

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

example (α : Type) [SampleableType α] (f : α → ℕ) :
    ⦃ True ⦄ (do let u ← $ᵗ α; let v ← $ᵗ α; pure (f u + f v, f v + f u) : ProbComp (ℕ × ℕ))
      ⦃ fun p => p.1 = p.2 ⦄ := by
  vcgen
  omega

example (n : ℕ) :
    ⦃ True ⦄ (do let i ← $[0..n]; pure i.val : ProbComp ℕ) ⦃ fun k => k ≤ n ⦄ := by
  vcgen
  exact Nat.lt_succ_iff.mp (Fin.isLt _)

example (α : Type) [SampleableType α] (n : ℕ) :
    ⦃ True ⦄ (do let x ← $ᵗ α; let xs ← ($ᵗ α).replicate n; pure (x :: xs) : ProbComp (List α))
      ⦃ fun l => l.length = n + 1 ⦄ := by
  vcgen with finish

example {τ : Type} {superSpec : OracleSpec.{0, 0} τ} [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec]
    (t : spec.Domain) (f : spec.Range t → ℕ) :
    ⦃ True ⦄
      (do
        let p ← liftComp (do let u ← query t; pure (f u, f u) : OracleComp spec _) superSpec
        pure p.1 : OracleComp superSpec ℕ)
      ⦃ fun n => ∃ u, n = f u ⦄ := by
  vcgen with finish

/-- The same lift written `liftM`, the form `simp` gives `liftComp`. -/
example {τ : Type} {superSpec : OracleSpec.{0, 0} τ} [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec]
    (t : spec.Domain) (f : spec.Range t → ℕ) :
    ⦃ True ⦄
      (do
        let p ← (liftM (do let u ← query t; pure (f u, f u) : OracleComp spec _) :
          OracleComp superSpec _)
        pure p.1 : OracleComp superSpec ℕ)
      ⦃ fun n => ∃ u, n = f u ⦄ := by
  vcgen with finish

/-- An opaque sub-program is specified by its support. -/
example (keygen : OracleComp spec (ℕ × ℕ)) (hk : ∀ k ∈ support keygen, k.1 ≤ k.2) :
    ⦃ True ⦄ (do let k ← keygen; pure (k.2 - k.1 + k.1) : OracleComp spec ℕ)
      ⦃ fun n => ∃ k ∈ support keygen, n = k.2 ⦄ := by
  vcgen [OracleComp.Qualitative.Spec.ofSupport keygen]
  rename_i hk'
  exact ⟨k, hk', by have := hk k hk'; omega⟩

/-- A handler that samples a coin and raises its flag on heads. -/
def flagImpl : QueryImpl (Unit →ₒ Bool) (StateT Bool ProbComp) := fun _ => do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let s ← get
  set (s || b)
  return b

/-- A handler that reports its flag. -/
def readImpl : QueryImpl (Unit →ₒ Bool) (StateT Bool ProbComp) := fun _ => do
  let s ← get
  return s

/-- The two handlers as one sum handler, into `ProbComp`. -/
def flagReadImpl : QueryImpl ((Unit →ₒ Bool) + (Unit →ₒ Bool)) (StateT Bool ProbComp) :=
  flagImpl + readImpl

/-- A raised flag stays raised through any simulation: a sum handler into another oracle world,
lifted to the whole simulation. -/
example {α : Type} (oa : OracleComp ((Unit →ₒ Bool) + (Unit →ₒ Bool)) α) :
    ⦃ fun s => s = true ⦄ simulateQ flagReadImpl oa ⦃ fun _ s' => s' = true ⦄ := by
  refine simulateQ_triple_preserves_invariant flagReadImpl (· = true) ?_ oa
  rintro (u | u)
  · vcgen [flagReadImpl, flagImpl] with finish
  · vcgen [flagReadImpl, readImpl]

open scoped WriterT.AppendWP in
/-- The log of `loggingOracle` only grows through any simulation. -/
example {α : Type} (log₀ : QueryLog spec) (oa : OracleComp spec α) :
    ⦃ fun log => log₀ <+: log ⦄
      (simulateQ loggingOracle oa : WriterT (QueryLog spec) (OracleComp spec) α)
    ⦃ fun _ log' => log₀ <+: log' ⦄ :=
  simulateQ_writerT_append_triple_preserves_invariant loggingOracle _
    (fun _ => by vcgen [loggingOracle_triple] with finish) oa

end Structural

/-! ## Events as structural triples -/

section Bridges

/-- A program with two draws whose output pair always agrees. -/
def agreeProg (α : Type) [SampleableType α] (f : α → ℕ) : ProbComp (ℕ × ℕ) := do
  let u ← $ᵗ α
  let v ← $ᵗ α
  pure (f u + f v, f v + f u)

example (α : Type) [SampleableType α] (f : α → ℕ) :
    Pr{let p ← agreeProg α f}[p.1 = p.2] = 1 := by
  rw [OracleComp.Qualitative.prEvent_eq_one_iff_triple]
  vcgen [agreeProg]
  omega

example (α : Type) [SampleableType α] (f : α → ℕ) :
    Pr{let p ← agreeProg α f}[p.1 = p.2] = 1 :=
  OracleComp.Qualitative.prEvent_eq_one_of_triple (by vcgen [agreeProg]; omega)

example (α : Type) [SampleableType α] (f : α → ℕ) :
    𝒟[(fun p : ℕ × ℕ => decide (p.1 = p.2)) <$> agreeProg α f] {true} = 1 := by
  rw [OracleComp.Qualitative.evalDist_true_eq_one_iff_triple]
  vcgen [agreeProg]
  simp only [decide_eq_true_eq]
  omega

example (α : Type) [SampleableType α] (f : α → ℕ) :
    Pr{let p ← agreeProg α f}[p.1 < p.2] = 0 := by
  rw [OracleComp.Qualitative.prEvent_eq_zero_iff_triple]
  vcgen [agreeProg]
  omega

end Bridges

/-! ## Quantitative reading -/

section Quantitative

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} [spec.IsMeasureSpec] {α : Type}

open scoped OracleComp.Quantitative

/-- Probability one through two queries. -/
example (t : spec.Domain) (f : spec.Range t → ℕ) :
    ⦃ 1 ⦄ (do let u ← query t; let v ← query t; pure (f u + f v, f v + f u) : OracleComp spec _)
      ⦃ predInd fun p => p.1 = p.2 ⦄ := by
  vcgen
  simp [Nat.add_comm]

/-- An event's normal form, stated through `le_wp_iff_triple`. -/
example (β : Type) [SampleableType β] (f : β → ℕ) :
    1 ≤ Pr{let u ← $ᵗ β; let v ← $ᵗ β}[f u + f v = f v + f u] := by
  rw [le_wp_iff_triple]
  vcgen
  simp [Nat.add_comm]

/-- A named program through `le_prEvent_iff_triple`, with the exact rule on the last draw. -/
example : (1 : ℝ≥0∞) / 2 ≤ Pr{let b ← ($ᵗ Bool : ProbComp Bool)}[b = true] := by
  rw [le_prEvent_iff_triple]
  vcgen [OracleComp.Quantitative.Spec.uniformSample_sum]
  simp

/-- A support-conditioned bind: the continuation's bound on the support of the prefix. -/
example (gen : OracleComp spec α) (f : α → OracleComp spec Bool) (r : ℝ≥0∞)
    (hf : ∀ k ∈ support gen, ⦃ r ⦄ f k ⦃ predInd (· = true) ⦄) :
    ⦃ r ⦄ (do let k ← gen; f k) ⦃ predInd (· = true) ⦄ := by
  vcgen [OracleComp.Quantitative.Spec.ofSupport gen]
  exact ‹{a // a ∈ support gen}›.2

/-- A post-processed adversary keeps its success bound. -/
example (adv : ProbComp α) (win : α → Prop) (r : ℝ≥0∞) (g : α → Bool)
    (hg : ∀ a, win a → g a = true) (hadv : ⦃ r ⦄ adv ⦃ predInd win ⦄) :
    ⦃ r ⦄ (do let a ← adv; pure (g a)) ⦃ predInd (· = true) ⦄ := by
  vcgen [hadv]
  exact propInd_mono (hg _)

/-- Guessing a fair coin after the adversary halves its success bound: a scaled spec for the
adversary and the exact rule for the coin. -/
example (adv : ProbComp α) (win : α → Prop) [DecidablePred win] (r : ℝ≥0∞)
    (hadv : ⦃ r ⦄ adv ⦃ predInd win ⦄) :
    ⦃ 2⁻¹ * r ⦄ (do let a ← adv; let b ← $ᵗ Bool; pure (decide (win a) && b))
      ⦃ predInd (· = true) ⦄ := by
  vcgen [triple_const_mul 2⁻¹ hadv, OracleComp.Quantitative.Spec.uniformSample_sum]
  rename_i a
  by_cases h : win a <;> simp [h, ENNReal.div_eq_inv_mul]

end Quantitative

/-! ## Transformers, loops and simulations -/

section Transformers

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- `StateT.lift` through the base draw. -/
example : ⦃ fun _ => True ⦄ (StateT.lift ($ᵗ Bool) : StateT ℕ ProbComp Bool)
    ⦃ fun b _ => (b || !b) = true ⦄ := by
  vcgen
  simp

/-- A handler written with `StateT.mk` runs its body at the incoming state. -/
example : ⦃ fun _ => True ⦄
    (StateT.mk fun s => (fun b => (b, s + 1)) <$> ($ᵗ Bool) : StateT ℕ ProbComp Bool)
    ⦃ fun _ s => 0 < s ⦄ := by
  vcgen
  simp

/-- Running a `StateT` program at a state, with the final state discarded. -/
example : ⦃ True ⦄ ((do
      let b ← StateT.lift ($ᵗ Bool)
      set (1 : ℕ)
      pure b : StateT ℕ ProbComp Bool).run' 0) ⦃ fun b => (b || !b) = true ⦄ := by
  vcgen
  simp

/-- An `OptionT` lift succeeds; running it observes the option. -/
example : ⦃ True ⦄ (OptionT.lift ($ᵗ Bool) : OptionT ProbComp Bool).run ⦃ fun o => o ≠ none ⦄ := by
  vcgen
  simp

/-- `OptionT.mk` is read through the option its body returns. -/
example : ⦃ True ⦄ (OptionT.mk (pure (some true)) : OptionT ProbComp Bool).run
    ⦃ fun o => o = some true ⦄ := by
  vcgen
  simp [Lean.Order.pushOption]

/-- An `ExceptT` lift succeeds; running it observes the result. -/
example : ⦃ True ⦄ (ExceptT.lift ($ᵗ Bool) : ExceptT String ProbComp Bool).run
    ⦃ fun r => ∀ e, r ≠ .error e ⦄ := by
  vcgen
  simp

/-- `ExceptT.mk` is read through the result its body returns. -/
example : ⦃ True ⦄ (ExceptT.mk (pure (.ok true)) : ExceptT String ProbComp Bool).run
    ⦃ fun r => r = .ok true ⦄ := by
  vcgen
  simp [Lean.Order.pushExcept]

/-- `List.mapM` with an invariant relating the outputs so far to the elements consumed. -/
example : ⦃ True ⦄ ([1, 2, 3].mapM fun n => (fun b => if b then n else 0) <$> ($ᵗ Bool) :
    ProbComp (List ℕ)) ⦃ fun bs => bs.length = 3 ⦄ := by
  vcgen invariants
    · fun pref _ bs => bs.length = pref.length
  all_goals simp_all

/-- The sequence combinators keep the first, respectively the second, value. -/
example : ⦃ True ⦄ (($ᵗ Bool) <* ($ᵗ Bool) : ProbComp Bool) ⦃ fun b => (b || !b) = true ⦄ := by
  vcgen
  simp

example : ⦃ True ⦄ (($ᵗ Bool) *> ($ᵗ Bool) : ProbComp Bool) ⦃ fun b => (b || !b) = true ⦄ := by
  vcgen
  simp

/-- A query inside a transformer reaches the primitive query through the `query` unfold and
core's lift rule. -/
example (t : spec.Domain) (p : spec.Range t → Prop) (h : ∀ u, p u) :
    ⦃ fun _ => True ⦄ (do let u ← (query t : StateT ℕ (OracleComp spec) _); pure u)
      ⦃ fun u _ => p u ⦄ := by
  vcgen
  simp [h]

/-- A handler that resets its state after every query. -/
def resetHandler : QueryImpl (Unit →ₒ Bool) (StateT ℕ ProbComp) := fun _ => do
  let b ← StateT.lift ($ᵗ Bool)
  set (0 : ℕ)
  pure b

/-- A simulation preserves a handler invariant that every query preserves: the per-query
triples are the verification conditions, continued into the handler's body. -/
example {α : Type} (oa : OracleComp (Unit →ₒ Bool) α) :
    ⦃ fun s => s = 0 ⦄ (simulateQ resetHandler oa : StateT ℕ ProbComp α) ⦃ fun _ s => s = 0 ⦄ := by
  vcgen [resetHandler] invariants
    · fun s => s = 0

end Transformers

end VCVioTest.ProgramLogic.CoreVCGen
