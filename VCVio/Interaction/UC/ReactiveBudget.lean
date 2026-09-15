/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.ReactiveNetwork.Budget
public import VCVio.Interaction.UC.ReactiveRuntime
public import VCVio.OracleComp.CanReturn

/-!
# Activation certificates for probabilistic reactive execution

Global token certificates apply to the actual syntactic support of every finite probabilistic
run. The setup-sampled experiment consequently has no unfinished output when its fuel covers
the certified rank at every supported setup. These statements bound activations; interpreter
and runtime implementation costs remain separate obligations.
-/

public section

namespace Interaction.UC.ReactiveRuntime

open PFunctor ReactiveProcess ReactiveNetwork OracleComp

variable {Node result S : Type} {boundary : PortBoundary}
  {network : Network Node boundary result} [DecidableEq Node]
  {impl : (node : Node) → Handler (StateT S ProbComp) (network.effect node)}
  {invariant : State network S → Prop}

/-- The generic rank bound covers every syntactically possible probabilistic execution. -/
theorem token_terminal_of_mem_support
    (certificate : TokenBudgetCertificate impl invariant)
    (fuel : ℕ) (state next : State network S) (hinv : invariant state)
    (hbound : certificate.rank state ≤ fuel) (hnext : next ∈ support (runToken impl fuel state)) :
    ∃ value, outcome network.environment next = some value :=
  certificate.runToken_terminal fuel state next hinv hbound
    ((canReturn_iff_mem_support _ _).mpr hnext)

/-- A uniform fuel bound over the sampled initial states excludes an unfinished observation. -/
theorem tokenExperiment_not_unfinished
    (certificate : TokenBudgetCertificate impl invariant) (setup : ProbComp S) (fuel : ℕ)
    (hinv : ∀ service ∈ support setup, invariant (initial network service))
    (hbound : ∀ service ∈ support setup, certificate.rank (initial network service) ≤ fuel) :
    none ∉ support (tokenExperiment network impl setup fuel) := by
  simp only [tokenExperiment, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff]
  rintro ⟨service, hservice, next, hnext, hout⟩
  obtain ⟨value, hvalue⟩ := token_terminal_of_mem_support certificate fuel _ _
    (hinv service hservice) (hbound service hservice) hnext
  rw [hvalue] at hout
  cases hout

/-- An activation certificate assigns zero observation measure to unfinished execution. -/
theorem tokenLaw_unfinished_zero [MeasurableSpace (Option (Outcome result))]
    [MeasurableSingletonClass (Option (Outcome result))]
    (certificate : TokenBudgetCertificate impl invariant) (setup : ProbComp S) (fuel : ℕ)
    (hinv : ∀ service ∈ support setup, invariant (initial network service))
    (hbound : ∀ service ∈ support setup, certificate.rank (initial network service) ≤ fuel) :
    tokenLaw network impl setup fuel {none} = 0 := by
  rw [tokenLaw_eq_evalDist, evalDist_apply_singleton]
  exact probOutput_eq_zero_of_not_mem_support
    (tokenExperiment_not_unfinished certificate setup fuel hinv hbound)

/-- Every supported run keeps its full consumed activation count. -/
theorem token_elapsed_of_mem_support (fuel : ℕ) (state next : State network S)
    (hnext : next ∈ support (runToken impl fuel state)) :
    next.elapsed = state.elapsed + fuel :=
  elapsed_runToken impl fuel state next ((canReturn_iff_mem_support _ _).mpr hnext)

end Interaction.UC.ReactiveRuntime
