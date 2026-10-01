/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Unary.WP.Possible
public import VCVio.ProgramLogic.Unary.WP.TransformerSpecs
public import VCVio.ProgramLogic.Unary.HandlerSpecs
public import VCVio.ProgramLogic.Tactics.PrVCGen

/-!
# Core `vcgen` under the possible reading

Every registered rule of `OracleComp.Possible`, its unregistered support rule, its bridges from
positive probability, possible outputs and weakest preconditions, the transformer rules and a
simulation under this reading, each with a bare core `vcgen` inside
`open scoped OracleComp.Possible`; and a triple of the reading through `prvcgen`, which reads the
triple's interpretation off its instance.

A possible-reading triple `⦃ pre ⦄ oa ⦃ post ⦄` states that some possible output satisfies `post`:
each draw leaves an existential over its outcome. When the draw has a continuation, the witness
is named, the `binderNameHint` that `vcgen` leaves on the continuation's weakest precondition is
unfolded, and `prvcgen` continues from that weakest precondition.
-/

public section

open OracleSpec OracleComp Std.WP ENNReal OracleComp.ProgramLogic

namespace VCVioTest.ProgramLogic.PossibleVCGen

open scoped OracleComp.Possible

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-! ## Rules -/

/-- `Spec.uniformSample`: a uniform draw leaves an existential over its outcome. -/
example : ⦃ True ⦄ ($ᵗ Bool : ProbComp Bool) ⦃ fun b => b = true ⦄ := by
  vcgen
  exact ⟨true, rfl⟩

/-- `Spec.uniformFin`: a draw from `$[0..n]`. -/
example : ⦃ True ⦄ ($[0..3] : ProbComp (Fin 4)) ⦃ fun i => i.val = 2 ⦄ := by
  vcgen
  exact ⟨2, rfl⟩

/-- `Spec.monadLift_query`: a query, through the global `query` unfold. -/
example (t : spec.Domain) (u₀ : spec.Range t) :
    ⦃ True ⦄ (query t : OracleComp spec (spec.Range t)) ⦃ fun u => u = u₀ ⦄ := by
  vcgen
  exact ⟨u₀, rfl⟩

/-- `Spec.replicate`: some list of possible outputs. -/
example : ⦃ True ⦄ (($ᵗ Bool).replicate 2 : ProbComp (List Bool))
    ⦃ fun l => l = [true, true] ⦄ := by
  vcgen
  exact ⟨[true, true], rfl, by simp, rfl⟩

/-- `Spec.liftComp`: a lift between specifications is read through the lifted program. -/
example {τ : Type} {superSpec : OracleSpec.{0, 0} τ} [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec]
    (t : spec.Domain) (u₀ : spec.Range t) :
    ⦃ True ⦄ (liftComp (query t : OracleComp spec (spec.Range t)) superSpec)
      ⦃ fun u => u = u₀ ⦄ := by
  vcgen
  exact ⟨u₀, rfl⟩

/-- `Spec.monadLift_liftComp`: the same lift written `liftM`. -/
example {τ : Type} {superSpec : OracleSpec.{0, 0} τ} [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec]
    (t : spec.Domain) (u₀ : spec.Range t) :
    ⦃ True ⦄ (liftM (query t : OracleComp spec (spec.Range t)) : OracleComp superSpec _)
      ⦃ fun u => u = u₀ ⦄ := by
  vcgen
  exact ⟨u₀, rfl⟩

/-- `Spec.ofSupport`, passed for an opaque sub-program: some possible output of it. -/
example (keygen : OracleComp spec (ℕ × ℕ)) (hk : ∃ k ∈ support keygen, k.1 = 0) :
    ⦃ True ⦄ keygen ⦃ fun k => k.1 = 0 ⦄ := by
  vcgen [OracleComp.Possible.Spec.ofSupport keygen]
  exact hk

/-- A draw with a continuation: the witness is named and the continuation's weakest
precondition is continued by `prvcgen`, one draw at a time. -/
example : ⦃ True ⦄ (do let b ← $ᵗ Bool; let c ← $ᵗ Bool; pure (b && c) : ProbComp Bool)
    ⦃ fun r => r = true ⦄ := by
  vcgen
  refine ⟨true, ?_⟩
  simp only [binderNameHint]
  prvcgen
  refine ⟨true, ?_⟩
  simp only [binderNameHint]
  prvcgen
  rfl

/-! ## Bridges -/

/-- A possible output is a triple of the reading. -/
example : ∃ x ∈ support ($ᵗ Bool : ProbComp Bool), x = true := by
  rw [OracleComp.Possible.exists_mem_support_iff_triple]
  vcgen
  exact ⟨true, rfl⟩

/-- Positive probability is a triple of the reading, under uniform answers. -/
example : 0 < Pr{let b ← ($ᵗ Bool : ProbComp Bool)}[b = true] := by
  rw [OracleComp.Possible.prEvent_pos_iff_triple]
  vcgen
  exact ⟨true, rfl⟩

/-- A weakest precondition of the reading is a triple of it. -/
example : Std.WP.wp ($ᵗ Bool : ProbComp Bool) (fun b => b = true) Lean.Order.bot := by
  rw [OracleComp.Possible.wp_iff_triple]
  vcgen
  exact ⟨true, rfl⟩

/-! ## Transformers, loops and simulations -/

/-- `StateT.lift` through the base draw. -/
example : ⦃ fun _ => True ⦄ (StateT.lift ($ᵗ Bool) : StateT ℕ ProbComp Bool)
    ⦃ fun b _ => b = true ⦄ := by
  vcgen
  exact ⟨true, rfl⟩

/-- A handler written with `StateT.mk` runs its body at the incoming state. -/
example : ⦃ fun _ => True ⦄
    (StateT.mk fun s => (fun b => (b, s + 1)) <$> ($ᵗ Bool) : StateT ℕ ProbComp Bool)
    ⦃ fun b s => b = true ∧ 0 < s ⦄ := by
  vcgen
  exact ⟨true, rfl, by omega⟩

/-- Running a `StateT` program at a state, with the final state discarded. -/
example : ⦃ True ⦄ ((do
      set (1 : ℕ)
      StateT.lift ($ᵗ Bool) : StateT ℕ ProbComp Bool).run' 0) ⦃ fun b => b = true ⦄ := by
  vcgen
  exact ⟨true, rfl⟩

/-- An `OptionT` lift may succeed with any draw; running it observes the option. -/
example : ⦃ True ⦄ (OptionT.lift ($ᵗ Bool) : OptionT ProbComp Bool).run
    ⦃ fun o => o = some true ⦄ := by
  vcgen
  exact ⟨true, rfl⟩

/-- `OptionT.mk` is read through the option its body returns. -/
example : ⦃ True ⦄ (OptionT.mk ((fun b => some b) <$> ($ᵗ Bool)) : OptionT ProbComp Bool).run
    ⦃ fun o => o = some true ⦄ := by
  vcgen
  exact ⟨true, rfl⟩

/-- `guard` on a true condition continues; the failing branch is refuted. -/
example : ⦃ True ⦄ (do guard (1 < 2); OptionT.lift ($ᵗ Bool) : OptionT ProbComp Bool).run
    ⦃ fun o => o = some true ⦄ := by
  vcgen
  · exact ⟨true, rfl⟩
  · exact absurd ‹¬1 < 2› (by decide)

/-- An `ExceptT` lift may succeed with any draw; running it observes the result. -/
example : ⦃ True ⦄ (ExceptT.lift ($ᵗ Bool) : ExceptT String ProbComp Bool).run
    ⦃ fun r => r = .ok true ⦄ := by
  vcgen
  exact ⟨true, rfl⟩

/-- `ExceptT.mk` is read through the result its body returns. -/
example : ⦃ True ⦄ (ExceptT.mk ((fun b => .ok b) <$> ($ᵗ Bool)) : ExceptT String ProbComp Bool).run
    ⦃ fun r => r = .ok true ⦄ := by
  vcgen
  exact ⟨true, rfl⟩

/-- `List.mapM` with an invariant on the outputs so far: each step picks the draw that keeps it. -/
example : ⦃ True ⦄ ([1, 2].mapM fun n => (fun b => if b then n else 0) <$> ($ᵗ Bool) :
    ProbComp (List ℕ)) ⦃ fun bs => bs = [1, 2] ⦄ := by
  vcgen invariants
    · fun pref _ bs => bs = pref
  all_goals simp_all

/-- The sequence combinators keep the first, respectively the second, draw. -/
example : ⦃ True ⦄ (($ᵗ Bool) <* ($ᵗ Bool) : ProbComp Bool) ⦃ fun b => b = true ⦄ := by
  vcgen
  refine ⟨true, ?_⟩
  prvcgen
  exact ⟨true, rfl⟩

example : ⦃ True ⦄ (($ᵗ Bool) *> ($ᵗ Bool) : ProbComp Bool) ⦃ fun b => b = true ⦄ := by
  vcgen
  refine ⟨true, ?_⟩
  prvcgen
  exact ⟨true, rfl⟩

/-- A handler that resets its state before every query. -/
def resetHandler : QueryImpl (Unit →ₒ Bool) (StateT ℕ ProbComp) := fun _ => do
  set (0 : ℕ)
  StateT.lift ($ᵗ Bool)

/-- `Spec.simulateQ`: some run of every query keeps the handler invariant. -/
example {α : Type} (oa : OracleComp (Unit →ₒ Bool) α) :
    ⦃ fun s => s = 0 ⦄ (simulateQ resetHandler oa : StateT ℕ ProbComp α) ⦃ fun _ s => s = 0 ⦄ := by
  vcgen [resetHandler] invariants
    · fun s => s = 0
  exact ⟨true, rfl⟩

/-! ## The reading through `prvcgen` -/

/-- A triple whose interpretation is the possible reading is run in it. -/
example : ⦃ True ⦄ ($ᵗ Bool : ProbComp Bool) ⦃ fun b => b = true ⦄ := by
  prvcgen
  exact ⟨true, rfl⟩

end VCVioTest.ProgramLogic.PossibleVCGen
