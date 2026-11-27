/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.SimSemantics.OptionT.Basic
public import VCVio.OracleComp.SimSemantics.StateT.Compensated

/-!
# Optional replies and stopped adaptive callers

An optional reply permits the handler to stop after retaining the state of its last query.
Keeping refusal in the response type allows ordinary stateful estimates on the stopped caller.
-/

public section

namespace OracleComp.OptionalAnswer

open OracleSpec
open scoped ENNReal

variable {ι α : Type} {spec : OracleSpec ι}

/-- The original query domain, with an optional reply at each query. -/
abbrev Spec (spec : OracleSpec ι) : OracleSpec ι := fun t => Option (spec.Range t)

/-- A refusal stops the caller before the next adaptive query. -/
@[expose] def program (p : OracleComp spec α) : OracleComp (Spec spec) (Option α) :=
  (simulateQ (spec := spec) (r := OptionT (OracleComp (Spec spec)))
    (fun t => OptionT.mk (liftM ((Spec spec).query t))) p).run

/-- Returning the optional reply through the ordinary handler gives the exact stopped run. -/
theorem simulate_program {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec (OptionT m)) (p : OracleComp spec α) :
    simulateQ (spec := Spec spec) (fun t => (impl t).run) (program p) = (simulateQ impl p).run := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [program]
  | query_bind t next ih =>
    simp only [program] at ih ⊢
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, OptionT.run_mk]
    apply bind_congr
    rintro (_ | a)
    · simp
    · exact ih a

/-- If each query bounds the expected increase in value by the expected increase in reserve,
the same bound holds at return. A refusal contributes the state reached by its query. -/
theorem run_compensated {σ : Type} (impl : QueryImpl spec (OptionT (StateT σ ProbComp)))
    (I : σ → Prop)
    (preserves : (show QueryImpl (Spec spec) (StateT σ ProbComp) from fun t =>
      (impl t).run).PreservesInv I)
    (value reserve : σ → ℝ≥0∞) (finite : ∀ s, I s → reserve s ≠ ⊤)
    (step : ∀ t s, I s →
      (∑' z, Pr{let u ← ((impl t).run).run s}[u = z] * value z.2) + reserve s ≤
        value s + ∑' z, Pr{let u ← ((impl t).run).run s}[u = z] * reserve z.2)
    (caller : OracleComp spec α) (s : σ) (initial : I s) :
    let run := ((simulateQ impl caller).run).run s
    (∑' z, Pr{let u ← run}[u = z] * value z.2) + reserve s ≤
      value s + ∑' z, Pr{let u ← run}[u = z] * reserve z.2 := by
  rw [← simulate_program]
  exact QueryImpl.run_compensated _ I preserves value reserve finite step _ s initial

end OracleComp.OptionalAnswer
