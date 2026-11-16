/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Tactics.Unary
public import VCVio.ProgramLogic.Unary.SimulateQ
public import VCVio.OracleComp.Constructions.Replicate.Basic

/-!
# Step coverage of `vcstep` and `pvcgen`

Quantitative triples over monad-transformer stacks on `OracleComp`, and raw `wp` equalities and
bounds, each closed by a single tactic call. A goal is closed by one `vcstep` when that suffices,
and by `pvcgen` otherwise.

The transformer primitives (`StateT`, `ReaderT`, `WriterT`, `OptionT`, `ExceptT`, lifted `throw`
and `tryCatch`, `.run`) close through the transformer-layer peeler of the unary step planner and
core's and PolyFun's `@[spec]` rules: VCVio's `@[vcspec]` registry carries only the
oracle-computation leaves. The raw `wp` goals are rewritten by the fixed `wpStepRules` table.
Goals neither tactic closes in one call (`withReader`, a `StateT.run` triple, a `tryCatch` lifted
through `StateT`) are not recorded here.
-/

public section

namespace VCVioTest.ProgramLogic.StepCoverage

open scoped Std.WP OracleComp.Lower WriterT.MonoidWP OracleComp.ProgramLogic
open ENNReal OracleSpec OracleComp OracleComp.ProgramLogic Std.WP

universe u

variable {ι : Type u} {spec : OracleSpec ι} [OracleSpec.UniformAnswerMeasure spec] {α β : Type}

/-! ## State, reader and writer layers -/

example (post : Nat → Nat → ℝ≥0∞) :
    ⦃fun s => post s s⦄ (MonadStateOf.get : StateT Nat (OracleComp spec) Nat) ⦃post⦄ := by
  vcstep

example (s' : Nat) (post : PUnit → Nat → ℝ≥0∞) :
    ⦃fun _ => post ⟨⟩ s'⦄ (MonadStateOf.set s' : StateT Nat (OracleComp spec) PUnit) ⦃post⦄ := by
  vcstep

example (f : Nat → α × Nat) (post : α → Nat → ℝ≥0∞) :
    ⦃fun s => post (f s).1 (f s).2⦄
      (MonadStateOf.modifyGet f : StateT Nat (OracleComp spec) α) ⦃post⦄ := by
  vcstep

example (post : PUnit → Nat → ℝ≥0∞) :
    ⦃fun s => post ⟨⟩ (s + 1)⦄ (modify (· + 1) : StateT Nat (OracleComp spec) PUnit) ⦃post⦄ := by
  vcstep

example (oa : OracleComp spec α) (post : α → Nat → ℝ≥0∞) :
    ⦃fun s => wp⟦oa⟧ (fun a => post a s)⦄
      (MonadLift.monadLift oa : StateT Nat (OracleComp spec) α) ⦃post⦄ := by
  vcstep

example (post : PUnit → Nat → ℝ≥0∞) :
    ⦃fun s => post ⟨⟩ (s + 1)⦄
      (do let s ← (MonadStateOf.get : StateT Nat (OracleComp spec) Nat); MonadStateOf.set (s + 1))
      ⦃post⦄ := by
  vcstep

example (oa : OracleComp spec α) (post : α → Nat → ℝ≥0∞) :
    ⦃fun s => wp⟦oa⟧ (fun a => post a (s + 1))⦄
      (do modify (· + 1); (MonadLift.monadLift oa : StateT Nat (OracleComp spec) α)) ⦃post⦄ := by
  vcstep

example (post : String → String → ℝ≥0∞) :
    ⦃fun r => post r r⦄ (MonadReaderOf.read : ReaderT String (OracleComp spec) String) ⦃post⦄ := by
  vcstep

example (oa : OracleComp spec α) (post : α → String → ℝ≥0∞) :
    ⦃fun r => wp⟦oa⟧ (fun a => post a r)⦄
      (MonadLift.monadLift oa : ReaderT String (OracleComp spec) α) ⦃post⦄ := by
  vcstep

example (out : Multiplicative Nat) (post : PUnit → Multiplicative Nat → ℝ≥0∞) :
    ⦃fun w => post ⟨⟩ (w * out)⦄
      (MonadWriter.tell out : WriterT (Multiplicative Nat) (OracleComp spec) PUnit) ⦃post⦄ := by
  vcstep

example (oa : OracleComp spec α) (post : α → Multiplicative Nat → ℝ≥0∞) :
    ⦃fun w => wp⟦oa⟧ (fun a => post a w)⦄
      (MonadLift.monadLift oa : WriterT (Multiplicative Nat) (OracleComp spec) α) ⦃post⦄ := by
  vcstep

/-! ## Option and exception layers -/

example (post : α → ℝ≥0∞) (nonePost : Unit → ℝ≥0∞) :
    ⦃nonePost ()⦄ (failure : OptionT (OracleComp spec) α) ⦃post; estack⟨nonePost⟩⦄ := by
  vcstep

example (oa : OracleComp spec α) (post : α → ℝ≥0∞) (nonePost : Unit → ℝ≥0∞) :
    ⦃wp⟦oa⟧ post⦄ (MonadLift.monadLift oa : OptionT (OracleComp spec) α)
      ⦃post; estack⟨nonePost⟩⦄ := by
  vcstep

example (y : OptionT (OracleComp spec) α) (post : α → ℝ≥0∞) (nonePost : Unit → ℝ≥0∞)
    (pre : ℝ≥0∞) (h : ⦃ pre ⦄ y ⦃ post; estack⟨nonePost⟩ ⦄) :
    ⦃pre⦄ ((failure : OptionT (OracleComp spec) α) <|> y) ⦃post; estack⟨nonePost⟩⦄ := by
  vcstep

example (err : String) (post : α → ℝ≥0∞) (errPost : String → ℝ≥0∞) :
    ⦃errPost err⦄ (throw err : ExceptT String (OracleComp spec) α) ⦃post; estack⟨errPost⟩⦄ := by
  vcstep

example (oa : OracleComp spec α) (post : α → ℝ≥0∞) (errPost : String → ℝ≥0∞) :
    ⦃wp⟦oa⟧ post⦄ (MonadLift.monadLift oa : ExceptT String (OracleComp spec) α)
      ⦃post; estack⟨errPost⟩⦄ := by
  vcstep

example (e : String) (h : String → ExceptT String (OracleComp spec) α) (post : α → ℝ≥0∞)
    (errPost : String → ℝ≥0∞) (pre : ℝ≥0∞) (hh : ⦃ pre ⦄ h e ⦃ post; estack⟨errPost⟩ ⦄) :
    ⦃pre⦄ (tryCatch (throw e) h : ExceptT String (OracleComp spec) α)
      ⦃post; estack⟨errPost⟩⦄ := by
  vcstep

example (err : String) (post : α → Nat → ℝ≥0∞) (errPost : String → ℝ≥0∞) :
    ⦃fun _ => errPost err⦄ (throw err : StateT Nat (ExceptT String (OracleComp spec)) α)
      ⦃post; estack⟨errPost⟩⦄ := by
  vcstep

example (err : String) (post : α → Nat → ℝ≥0∞) (errPost : String → ℝ≥0∞) :
    ⦃fun _ => errPost err⦄ (throw err : ReaderT Nat (ExceptT String (OracleComp spec)) α)
      ⦃post; estack⟨errPost⟩⦄ := by
  vcstep

example (oa : OracleComp spec α) (post : Nat × α → Nat → ℝ≥0∞) (nonePost : Unit → ℝ≥0∞) :
    ⦃fun s => wp⟦oa⟧ (fun a => post (s, a) (s + 1))⦄
      (do
        let s ← (MonadStateOf.get : StateT Nat (OptionT (OracleComp spec)) Nat)
        (MonadStateOf.set (s + 1) : StateT Nat (OptionT (OracleComp spec)) PUnit)
        let a ← (MonadLift.monadLift (OptionT.lift oa) : StateT Nat (OptionT (OracleComp spec)) α)
        pure (s, a))
      ⦃post; estack⟨nonePost⟩⦄ := by
  vcstep

/-! ## Oracle computations -/

example (x : α) (post : α → ℝ≥0∞) : ⦃post x⦄ (pure x : OracleComp spec α) ⦃post⦄ := by
  vcstep

example (oa : OracleComp spec α) (n : ℕ) (post : List α → ℝ≥0∞) :
    ⦃wp⟦oa⟧ (fun x => wp⟦oa.replicate n⟧ (fun xs => post (x :: xs)))⦄
      oa.replicate (n + 1) ⦃post⦄ := by
  vcstep

/-! ## Raw `wp` rewriting -/

example (oa : OracleComp spec α) (f : α → OracleComp spec β) (post : β → ℝ≥0∞) :
    wp⟦oa >>= f⟧ post = wp⟦oa⟧ (fun u => wp⟦f u⟧ post) := by
  vcstep

example (f : α → β) (oa : OracleComp spec α) (post : β → ℝ≥0∞) :
    wp⟦f <$> oa⟧ post = wp⟦oa⟧ (post ∘ f) := by
  vcstep

example (c : Prop) [Decidable c] (a b : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦if c then a else b⟧ post = if c then wp⟦a⟧ post else wp⟦b⟧ post := by
  vcstep

example (oa : OracleComp spec α) (n : ℕ) (post : List α → ℝ≥0∞) :
    wp⟦oa.replicate (n + 1)⟧ post =
      wp⟦oa⟧ (fun x => wp⟦oa.replicate n⟧ (fun xs => post (x :: xs))) := by
  vcstep

example (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) :
    wp⟦(query t : OracleComp spec (spec.Range t))⟧ post =
      ∫⁻ u, post u ∂OracleSpec.AnswerMeasure.toMeasure t := by
  vcstep

example [SampleableType α] (post : α → ℝ≥0∞) :
    wp⟦($ᵗ α : ProbComp α)⟧ post = ∫⁻ y, y ∂𝒟[post <$> ($ᵗ α : ProbComp α)] := by
  vcstep

example (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp⟦([] : List α).mapM f⟧ post = post [] := by
  vcstep

/-! ## Goals closed by the exhaustive driver

A single `vcstep` makes no progress on these; `pvcgen` closes them. -/

example (a : α) (h : String → ExceptT String (OracleComp spec) α) (post : α → ℝ≥0∞)
    (errPost : String → ℝ≥0∞) :
    ⦃post a⦄ (tryCatch (pure a) h : ExceptT String (OracleComp spec) α)
      ⦃post; estack⟨errPost⟩⦄ := by
  pvcgen

example (x : OptionT (OracleComp spec) α) (post : Option α → ℝ≥0∞) (pre : ℝ≥0∞)
    (hx : ⦃ pre ⦄ x ⦃ fun a => post (some a); estack⟨fun _ => post none⟩ ⦄) :
    ⦃pre⦄ x.run ⦃post⦄ := by
  pvcgen

example (x : ExceptT String (OracleComp spec) α) (post : Except String α → ℝ≥0∞) (pre : ℝ≥0∞)
    (hx : ⦃ pre ⦄ x ⦃ fun a => post (.ok a); estack⟨fun e => post (.error e)⟩ ⦄) :
    ⦃pre⦄ x.run ⦃post⦄ := by
  pvcgen

example (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) :
    ⦃∫⁻ u, post u ∂OracleSpec.AnswerMeasure.toMeasure t⦄
      (query t : OracleComp spec (spec.Range t)) ⦃post⦄ := by
  pvcgen

example (oa : OracleComp spec α) (f : α → OracleComp spec β) (post : β → ℝ≥0∞) :
    wp⟦oa⟧ (fun u => wp⟦f u⟧ post) ≤ wp⟦oa >>= f⟧ post := by
  pvcgen

/-! ## Multi-step stacks under `pvcgen` -/

example (oa : OracleComp spec α) (post : Nat × α → Nat → ℝ≥0∞) (nonePost : Unit → ℝ≥0∞) :
    ⦃fun s => wp⟦oa⟧ (fun a => post (s, a) (s + 1))⦄
      (do
        let s ← (MonadStateOf.get : StateT Nat (OptionT (OracleComp spec)) Nat)
        (MonadStateOf.set (s + 1) : StateT Nat (OptionT (OracleComp spec)) PUnit)
        let a ← (MonadLift.monadLift (OptionT.lift oa) : StateT Nat (OptionT (OracleComp spec)) α)
        pure (s, a))
      ⦃post; estack⟨nonePost⟩⦄ := by
  pvcgen

example (oa : OracleComp spec α) (n : ℕ) (post : List α → ℝ≥0∞) :
    ⦃wp⟦oa⟧ (fun x => wp⟦oa.replicate n⟧ (fun xs => post (x :: xs)))⦄
      oa.replicate (n + 1) ⦃post⦄ := by
  pvcgen

end VCVioTest.ProgramLogic.StepCoverage
