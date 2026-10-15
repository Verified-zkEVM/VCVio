/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Tactics.PrVCGen
public import VCVio.ProgramLogic.Unary.SimulateQ
public import VCVio.OracleComp.Constructions.Replicate.Basic
public import VCVio.OracleComp.Constructions.ReplicateMeasure
public import VCVio.OracleComp.Coercions.SubSpec.Basic
public import VCVio.OracleComp.Coercions.SubSpec.Measure

/-!
# Unary verification-condition examples

One-program statements about oracle computations and the tools that prove them:

* `simp only [expect_norm, expect_eval]` states an expectation `wp⟦oa⟧ post` through the
  unfolding of `oa` (binds, conditionals, loops) or through its value (a query, a uniform draw);
* `prvcgen` runs core's `vcgen` on a triple over `OracleComp spec` or over a `StateT`, `ReaderT`,
  `WriterT`, `OptionT` or `ExceptT` stack on it, leaving an opaque sub-program as a verification
  condition under `(errorOnMissingSpec := false)`;
* local `@[spec]` rules state the triple of an opaque program for `prvcgen` to use;
* `wp_simulateQ_eq` and `wp_liftComp` transport an expectation across a simulation or a lift.
-/

@[expose] public section

open scoped Std.WP WriterT.MonoidWP

open ENNReal OracleSpec OracleComp
open Lean.Order
open Std.WP
open OracleComp.ProgramLogic
open scoped OracleComp.ProgramLogic
open scoped OracleComp.Lower

universe u

variable {ι : Type u} {spec : OracleSpec ι}
variable [OracleSpec.UniformAnswerMeasure spec]
variable {α β : Type}

/-! ## Evaluating an expectation

`simp only [expect_norm, expect_eval]` rewrites an expectation along the structure of the program
and evaluates a query or a uniform draw. An equation between an expectation and a value that is
not one, such as `post x`, is also a goal of `prvcgen`, which takes the equations of the loop
combinators it should unfold in brackets. -/

example (oa : OracleComp spec α) (f : α → OracleComp spec β) (post : β → ℝ≥0∞) :
    wp⟦oa >>= f⟧ post = wp⟦oa⟧ (fun u => wp⟦f u⟧ post) := by
  simp only [expect_norm, expect_eval]

example (x : α) (post : α → ℝ≥0∞) :
    wp⟦(pure x : OracleComp spec α)⟧ post = post x := by
  prvcgen

example (c : Prop) [Decidable c] (a b : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦if c then a else b⟧ post = if c then wp⟦a⟧ post else wp⟦b⟧ post := by
  simp only [expect_norm, expect_eval]

example (oa : OracleComp spec α) (n : ℕ) (post : List α → ℝ≥0∞) :
    wp⟦oa.replicate (n + 1)⟧ post =
      wp⟦oa⟧ (fun x => wp⟦oa.replicate n⟧ (fun xs => post (x :: xs))) := by
  simp only [expect_norm, expect_eval]

example (oa : OracleComp spec α) (post : List α → ℝ≥0∞) :
    wp⟦oa.replicate 0⟧ post = post [] := by
  prvcgen [replicate_zero]

example (x : α) (xs : List α) (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp⟦(x :: xs).mapM f⟧ post =
      wp⟦f x⟧ (fun y => wp⟦xs.mapM f⟧ (fun ys => post (y :: ys))) := by
  simp only [expect_norm, expect_eval]

example (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp⟦([].mapM f : OracleComp spec (List β))⟧ post = post [] := by
  prvcgen [List.mapM_nil]

example (x : α) (xs : List α) (f : β → α → OracleComp spec β)
    (init : β) (post : β → ℝ≥0∞) :
    wp⟦(x :: xs).foldlM f init⟧ post =
      wp⟦f init x⟧ (fun s => wp⟦xs.foldlM f s⟧ post) := by
  simp only [expect_norm, expect_eval]

example (f : β → α → OracleComp spec β) (init : β) (post : β → ℝ≥0∞) :
    wp⟦([].foldlM f init : OracleComp spec β)⟧ post = post init := by
  prvcgen [List.foldlM_nil]

example (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) :
    wp⟦(query t : OracleComp spec (spec.Range t))⟧ post =
      ∫⁻ u, post u ∂OracleSpec.AnswerMeasure.toMeasure t := by
  simp only [expect_norm, expect_eval]

example (c : Prop) [Decidable c]
    (a : c → OracleComp spec α) (b : ¬c → OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦dite c a b⟧ post = if h : c then wp⟦a h⟧ post else wp⟦b h⟧ post := by
  simp only [expect_norm, expect_eval]

example [SampleableType α] (post : α → ℝ≥0∞) :
    wp⟦($ᵗ α : ProbComp α)⟧ post =
      ∫⁻ y, y ∂𝒟[post <$> ($ᵗ α : ProbComp α)] := by
  simp only [expect_norm, expect_eval]

example (f : α → β) (oa : OracleComp spec α) (post : β → ℝ≥0∞) :
    wp⟦f <$> oa⟧ post = wp⟦oa⟧ (post ∘ f) := by
  simp only [expect_norm, expect_eval]

/-! ## `StateT (OracleComp spec)` transformer triples

`prvcgen` runs `vcgen` on a triple of a transformer stack over `OracleComp spec`. With
`(errorOnMissingSpec := false)`, a lifted sub-program `oa` without a rule is left as a verification
condition `pre ≤ wp oa k` whose continuation `k` still holds the rest of the program;
`simp only [expect_norm, le_refl]` evaluates the continuation and closes it. -/

example (post : Nat → Nat → ℝ≥0∞) :
    ⦃fun s => post s s⦄
      (MonadStateOf.get : StateT Nat (OracleComp spec) Nat)
    ⦃post⦄ := by
  prvcgen

example (s' : Nat) (post : PUnit → Nat → ℝ≥0∞) :
    ⦃fun _ => post ⟨⟩ s'⦄
      (MonadStateOf.set s' : StateT Nat (OracleComp spec) PUnit)
    ⦃post⦄ := by
  prvcgen

example (f : Nat → α × Nat) (post : α → Nat → ℝ≥0∞) :
    ⦃fun s => post (f s).1 (f s).2⦄
      (MonadStateOf.modifyGet f : StateT Nat (OracleComp spec) α)
    ⦃post⦄ := by
  prvcgen

example (oa : OracleComp spec α) (post : α → Nat → ℝ≥0∞) :
    ⦃fun s => wp⟦oa⟧ (fun a => post a s)⦄
      (MonadLift.monadLift oa : StateT Nat (OracleComp spec) α)
    ⦃post⦄ := by
  prvcgen

example (oa : OracleComp spec α) (post : Nat × α → Nat → ℝ≥0∞) :
    ⦃fun s => wp⟦oa⟧ (fun a => post (s, a) (s + 1))⦄
      (do
        let s ← (MonadStateOf.get : StateT Nat (OracleComp spec) Nat)
        MonadStateOf.set (s + 1)
        let a ← (MonadLift.monadLift oa : StateT Nat (OracleComp spec) α)
        pure (s, a))
    ⦃post⦄ := by
  prvcgen (errorOnMissingSpec := false)
  simp only [expect_norm, le_refl]

example (s' : Nat) (oa : OracleComp spec α) (post : α → Nat → ℝ≥0∞) :
    ⦃fun _ => wp⟦oa⟧ (fun a => post a s')⦄
      (do
        MonadStateOf.set s'
        MonadLift.monadLift oa : StateT Nat (OracleComp spec) α)
    ⦃post⦄ := by
  prvcgen

example (f : Nat → α × Nat) (post : α → Nat → ℝ≥0∞) :
    ⦃fun s => post (f s).1 (f s).2⦄
      (do
        let a ← (MonadStateOf.modifyGet f : StateT Nat (OracleComp spec) α)
        pure a)
    ⦃post⦄ := by
  prvcgen

/-! ## `OptionT (OracleComp spec)` transformer triples -/

example (oa : OracleComp spec α) (post : α → ℝ≥0∞) (nonePost : Unit → ℝ≥0∞) :
    ⦃wp⟦oa⟧ post⦄ (MonadLift.monadLift oa : OptionT (OracleComp spec) α)
      ⦃post; estack⟨nonePost⟩⦄ := by
  prvcgen (errorOnMissingSpec := false)

example (oa : OracleComp spec α) (post : α → ℝ≥0∞) (nonePost : Unit → ℝ≥0∞) :
    ⦃wp⟦oa⟧ post⦄
      (do
        let a ← (MonadLift.monadLift oa : OptionT (OracleComp spec) α)
        pure a)
      ⦃post; estack⟨nonePost⟩⦄ := by
  prvcgen (errorOnMissingSpec := false)

example (post : α → ℝ≥0∞) (nonePost : Unit → ℝ≥0∞) :
    ⦃nonePost ()⦄ (failure : OptionT (OracleComp spec) α) ⦃post; estack⟨nonePost⟩⦄ := by
  prvcgen

/-! ## `ExceptT (OracleComp spec)` transformer triples -/

example (oa : OracleComp spec α) (post : α → ℝ≥0∞) (errPost : String → ℝ≥0∞) :
    ⦃wp⟦oa⟧ post⦄ (MonadLift.monadLift oa : ExceptT String (OracleComp spec) α)
      ⦃post; estack⟨errPost⟩⦄ := by
  prvcgen (errorOnMissingSpec := false)

example (oa : OracleComp spec α) (post : α → ℝ≥0∞) (errPost : String → ℝ≥0∞) :
    ⦃wp⟦oa⟧ post⦄
      (do
        let a ← (MonadLift.monadLift oa : ExceptT String (OracleComp spec) α)
        pure a)
      ⦃post; estack⟨errPost⟩⦄ := by
  prvcgen (errorOnMissingSpec := false)

example (err : String) (post : α → ℝ≥0∞) (errPost : String → ℝ≥0∞) :
    ⦃errPost err⦄ (throw err : ExceptT String (OracleComp spec) α) ⦃post; estack⟨errPost⟩⦄ := by
  prvcgen

/-! ## `ReaderT (OracleComp spec)` transformer triples -/

example (oa : OracleComp spec α) (post : α → String → ℝ≥0∞) :
    ⦃fun r => wp⟦oa⟧ (fun a => post a r)⦄
      (MonadLift.monadLift oa : ReaderT String (OracleComp spec) α)
    ⦃post⦄ := by
  prvcgen

example (oa : OracleComp spec α) (post : String × α → String → ℝ≥0∞) :
    ⦃fun r => wp⟦oa⟧ (fun a => post (r, a) r)⦄
      (do
        let r ← (MonadReaderOf.read : ReaderT String (OracleComp spec) String)
        let a ← (MonadLift.monadLift oa : ReaderT String (OracleComp spec) α)
        pure (r, a))
    ⦃post⦄ := by
  prvcgen (errorOnMissingSpec := false)
  simp only [expect_norm, le_refl]

/-! ## Mixed transformer stack triples -/

example (oa : OracleComp spec α) (post : Nat × α → Nat → ℝ≥0∞) (nonePost : Unit → ℝ≥0∞) :
    ⦃fun s => wp⟦oa⟧ (fun a => post (s, a) (s + 1))⦄
      (do
        let s ← (MonadStateOf.get : StateT Nat (OptionT (OracleComp spec)) Nat)
        (MonadStateOf.set (s + 1) : StateT Nat (OptionT (OracleComp spec)) PUnit)
        let a ← (MonadLift.monadLift (OptionT.lift oa) :
          StateT Nat (OptionT (OracleComp spec)) α)
        pure (s, a))
      ⦃post; estack⟨nonePost⟩⦄ := by
  prvcgen (errorOnMissingSpec := false)
  simp only [expect_norm, le_refl]

/-! ## `WriterT (OracleComp spec)` transformer triples -/

example (oa : OracleComp spec α) (post : α → Multiplicative Nat → ℝ≥0∞) :
    ⦃fun w => wp⟦oa⟧ (fun a => post a w)⦄
      (MonadLift.monadLift oa : WriterT (Multiplicative Nat) (OracleComp spec) α)
    ⦃post⦄ := by
  prvcgen

example (out : Multiplicative Nat) (post : PUnit → Multiplicative Nat → ℝ≥0∞) :
    ⦃fun w => post ⟨⟩ (w * out)⦄
      (MonadWriter.tell out : WriterT (Multiplicative Nat) (OracleComp spec) PUnit)
    ⦃post⦄ := by
  prvcgen

example (oa : OracleComp spec α) (out : Multiplicative Nat)
    (post : PUnit × α → Multiplicative Nat → ℝ≥0∞) :
    ⦃fun w => wp⟦oa⟧ (fun a => post (PUnit.unit, a) (w * out))⦄
      (do
        MonadWriter.tell out
        let a ← (MonadLift.monadLift oa : WriterT (Multiplicative Nat) (OracleComp spec) α)
        pure (PUnit.unit, a))
    ⦃post⦄ := by
  prvcgen (errorOnMissingSpec := false)
  simp only [expect_norm, le_refl]

example (oa : OracleComp spec α) (out : Multiplicative Nat)
    (post : Nat × α → Nat → Multiplicative Nat → ℝ≥0∞) :
    ⦃fun s w => wp⟦oa⟧ (fun a => post (s, a) (s + 1) (w * out))⦄
      ((do
        let s ← (MonadStateOf.get :
          StateT Nat (WriterT (Multiplicative Nat) (OracleComp spec)) Nat)
        (MonadStateOf.set (s + 1) :
          StateT Nat (WriterT (Multiplicative Nat) (OracleComp spec)) PUnit)
        (MonadLift.monadLift
          (MonadWriter.tell out : WriterT (Multiplicative Nat) (OracleComp spec) PUnit) :
          StateT Nat (WriterT (Multiplicative Nat) (OracleComp spec)) PUnit)
        let a ← (MonadLift.monadLift
          (MonadLift.monadLift oa : WriterT (Multiplicative Nat) (OracleComp spec) α) :
          StateT Nat (WriterT (Multiplicative Nat) (OracleComp spec)) α)
        (pure (s, a) :
          StateT Nat (WriterT (Multiplicative Nat) (OracleComp spec)) (Nat × α))) :
        StateT Nat (WriterT (Multiplicative Nat) (OracleComp spec)) (Nat × α))
    ⦃post⦄ := by
  prvcgen (errorOnMissingSpec := false)
  simp only [expect_norm, le_refl]

example (oa : OracleComp spec α) (out : Multiplicative Nat)
    (post : String × α → String → Multiplicative Nat → ℝ≥0∞) :
    ⦃fun r w => wp⟦oa⟧ (fun a => post (r, a) r (w * out))⦄
      ((do
        let r ← (MonadReaderOf.read :
          ReaderT String (WriterT (Multiplicative Nat) (OracleComp spec)) String)
        (MonadLift.monadLift
          (MonadWriter.tell out : WriterT (Multiplicative Nat) (OracleComp spec) PUnit) :
          ReaderT String (WriterT (Multiplicative Nat) (OracleComp spec)) PUnit)
        let a ← (MonadLift.monadLift
          (MonadLift.monadLift oa : WriterT (Multiplicative Nat) (OracleComp spec) α) :
          ReaderT String (WriterT (Multiplicative Nat) (OracleComp spec)) α)
        (pure (r, a) :
          ReaderT String (WriterT (Multiplicative Nat) (OracleComp spec)) (String × α))) :
        ReaderT String (WriterT (Multiplicative Nat) (OracleComp spec)) (String × α))
    ⦃post⦄ := by
  prvcgen (errorOnMissingSpec := false)
  simp only [expect_norm, le_refl]

/-! ## Lower bounds by evaluation

`expect_eval` contains `le_refl`, so the same simp call proves that an expectation is bounded
below by its unfolding or its value; `prvcgen` proves the bound for `pure` as a triple. -/

example (x : α) (post : α → ℝ≥0∞) :
    post x ≤ wp⟦(pure x : OracleComp spec α)⟧ post := by
  prvcgen

example (f : α → β) (oa : OracleComp spec α) (post : β → ℝ≥0∞) :
    wp⟦oa⟧ (post ∘ f) ≤ wp⟦f <$> oa⟧ post := by
  simp only [expect_norm, expect_eval]

example (c : Prop) [Decidable c] (a b : OracleComp spec α) (post : α → ℝ≥0∞) :
    (if c then wp⟦a⟧ post else wp⟦b⟧ post) ≤ wp⟦if c then a else b⟧ post := by
  simp only [expect_norm, expect_eval]

example (c : Prop) [Decidable c]
    (a : c → OracleComp spec α) (b : ¬c → OracleComp spec α) (post : α → ℝ≥0∞) :
    (if h : c then wp⟦a h⟧ post else wp⟦b h⟧ post) ≤ wp⟦dite c a b⟧ post := by
  simp only [expect_norm, expect_eval]

example (oa : OracleComp spec α) (n : ℕ) (post : List α → ℝ≥0∞) :
    wp⟦oa⟧ (fun x => wp⟦oa.replicate n⟧ (fun xs => post (x :: xs))) ≤
      wp⟦oa.replicate (n + 1)⟧ post := by
  simp only [expect_norm, expect_eval]

example (x : α) (xs : List α) (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp⟦f x⟧ (fun y => wp⟦xs.mapM f⟧ (fun ys => post (y :: ys))) ≤
      wp⟦(x :: xs).mapM f⟧ post := by
  simp only [expect_norm, expect_eval]

example (x : α) (xs : List α) (f : β → α → OracleComp spec β)
    (init : β) (post : β → ℝ≥0∞) :
    wp⟦f init x⟧ (fun s => wp⟦xs.foldlM f s⟧ post) ≤
      wp⟦(x :: xs).foldlM f init⟧ post := by
  simp only [expect_norm, expect_eval]

example (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) :
    (∫⁻ u, post u ∂OracleSpec.AnswerMeasure.toMeasure t) ≤
      wp⟦(query t : OracleComp spec (spec.Range t))⟧ post := by
  simp only [expect_norm, expect_eval]

example [SampleableType α] (post : α → ℝ≥0∞) :
    (∫⁻ y, y ∂𝒟[post <$> ($ᵗ α : ProbComp α)]) ≤
      wp⟦($ᵗ α : ProbComp α)⟧ post := by
  simp only [expect_norm, expect_eval]

/-! ## Local `@[spec]` rules

An irreducible program is opaque to `vcgen`; a `@[local spec]` triple states what `prvcgen` may
use about it, and a rule passed in brackets is used for that call alone. When the goal's
postcondition differs from the rule's, the verification condition compares the two at each output.
A goal stated as `pre ⊑ wp oa post epost` is an unfolded triple, and `prvcgen` takes it as one. -/

@[irreducible] def wrappedTrue : OracleComp spec Bool := pure true

@[local spec] theorem triple_wrappedTrue :
    ⦃ 1 ⦄ wrappedTrue (spec := spec) ⦃ fun y => if y = true then 1 else 0 ⦄ := by
  simpa [wrappedTrue] using
    (Spec.pure (m := OracleComp spec) (post := fun y => if y = true then 1 else 0) true)

example :
    ⦃ (1 : ℝ≥0∞) ⦄ (wrappedTrue (spec := spec))
      ⦃ fun y => if y = true then (1 : ℝ≥0∞) else 0 ⦄ := by
  prvcgen

example :
    ⦃ (1 : ℝ≥0∞) ⦄ (wrappedTrue (spec := spec)) ⦃ fun _ => (1 : ℝ≥0∞) ⦄ := by
  prvcgen
  split <;> simp

@[local spec] theorem triple_wrappedTrue' :
    Std.WP.Triple (wrappedTrue (spec := spec)) (1 : ℝ≥0∞)
      (fun y => if y = true then (1 : ℝ≥0∞) else 0) estack⟨⟩ := by
  exact triple_wrappedTrue (spec := spec)

example :
    ⦃ (1 : ℝ≥0∞) ⦄ (wrappedTrue (spec := spec)) ⦃ fun _ => (1 : ℝ≥0∞) ⦄ := by
  prvcgen [triple_wrappedTrue']
  split <;> simp

example :
    Std.WP.Triple (wrappedTrue (spec := spec)) (1 : ℝ≥0∞)
      (fun _ => (1 : ℝ≥0∞)) estack⟨⟩ := by
  prvcgen
  split <;> simp

example :
    (1 : ℝ≥0∞) ⊑
      Std.WP.wp (wrappedTrue (spec := spec))
        (fun y => if y = true then (1 : ℝ≥0∞) else 0) estack⟨⟩ := by
  prvcgen

example :
    (1 : ℝ≥0∞) ⊑
      Std.WP.wp (wrappedTrue (spec := spec)) (fun _ => (1 : ℝ≥0∞)) estack⟨⟩ := by
  prvcgen
  split <;> simp

@[irreducible] def wrappedTrueStep : OracleComp spec Bool := pure true

@[local spec] theorem triple_wrappedTrueStep (_haux : True) :
    ⦃ 1 ⦄ wrappedTrueStep (spec := spec) ⦃ fun y => if y = true then 1 else 0 ⦄ := by
  simpa [wrappedTrueStep] using
    (Spec.pure (m := OracleComp spec) (post := fun y => if y = true then 1 else 0) true)

example :
    ⦃ (1 : ℝ≥0∞) ⦄ (wrappedTrueStep (spec := spec))
      ⦃ fun y => if y = true then (1 : ℝ≥0∞) else 0 ⦄ := by
  prvcgen

example :
    ⦃ 1 ⦄ wrappedTrueStep (spec := spec) ⦃ fun y => if y = true then 1 else 0 ⦄ := by
  prvcgen [triple_wrappedTrueStep]

/-! ## `simulateQ` and `liftComp`

A simulation that answers each query in distribution as the query itself, and the lift of a
computation to a larger specification, both preserve its expectations. -/

example (impl : QueryImpl spec (OracleComp spec))
    (hImpl : ∀ (t : spec.Domain),
      impl t =ᵈ (liftM (OracleSpec.query t) : OracleComp spec (spec.Range t)))
    (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦simulateQ impl oa⟧ post = wp⟦oa⟧ post := by
  simpa using OracleComp.ProgramLogic.wp_simulateQ_eq impl hImpl oa post

section LiftComp

variable {ι' : Type} {superSpec : OracleSpec ι'}
variable [OracleSpec.UniformAnswerMeasure superSpec]
variable [h : spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec]

example (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦liftComp oa superSpec⟧ post = wp⟦oa⟧ post := by
  simpa using OracleComp.ProgramLogic.wp_liftComp
    (spec := spec) (superSpec := superSpec) oa post

end LiftComp
