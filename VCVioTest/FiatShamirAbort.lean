/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.ExpectedCost

/-!
# Native aborting Fiat-Shamir regressions

Retry analysis observes only abort markers and query counts. Its exact identities require a
lossless abort observation, while its upper bounds also apply to failing handlers.
-/

public section

open MeasureTheory OracleComp OracleSpec

namespace VCVioTest.FiatShamirAbort

section Generic

variable {m : Type → Type} [Monad m] [LawfulMonad m] [MonadLiftT ProbComp m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  {Stmt Wit Commit PrvState Chal Resp M : Type} {rel : Stmt → Wit → Bool}
  (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel)
  (handler : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)

example [IsProbabilityMeasure 𝒟[FiatShamirWithAbort.signAttemptAborts
    ids M handler pk sk msg]] (n : ℕ) :
    ExpectedQueries[(FiatShamirWithAbort ids hr M n).sign pk sk msg in handler] =
      ∑ i ∈ Finset.range n,
        FiatShamirWithAbort.signAttemptAbortProbability ids M handler pk sk msg ^ i :=
  FiatShamirWithAbort.sign_expectedQueries_eq_sum_signAttemptAbortProbability_powers
    ids M hr handler pk sk msg n

example (n : ℕ) :
    ExpectedQueries[(FiatShamirWithAbort ids hr M n).sign pk sk msg in handler] ≤
      (1 - FiatShamirWithAbort.signAttemptAbortProbability ids M handler pk sk msg)⁻¹ :=
  FiatShamirWithAbort.sign_expectedQueries_le_geometric ids M hr handler pk sk msg n

end Generic

/-- A prover whose response always aborts. -/
def abortingIds : IdenSchemeWithAbort Unit Unit Unit Unit Unit Unit (fun _ _ ↦ true) where
  commit _ _ := pure ((), ())
  respond _ _ _ _ := pure none
  verify _ _ _ _ := true

/-- The unique key pair satisfies the relation. -/
def keys : GenerableRelation Unit Unit (fun _ _ ↦ true) where
  gen := pure ((), ())
  gen_sound _ _ _ := rfl

/-- A handler that fails before producing a challenge. -/
def failingHandler : QueryImpl (Unit × Unit →ₒ Unit) (OptionT ProbComp) :=
  fun _ ↦ failure

example : FiatShamirWithAbort.signAttemptAbortProbability
    abortingIds Unit failingHandler () () () = 0 := by
  simp [FiatShamirWithAbort.signAttemptAbortProbability, FiatShamirWithAbort.signAttemptAborts,
    HasQuery.Program.eval, fsAbortSignAttempt, failingHandler]

example : Pr{
    let q ← HasQuery.queryCountDist
      (fun [HasQuery (Unit × Unit →ₒ Unit) (AddWriterT ℕ (OptionT ProbComp))] ↦
        (FiatShamirWithAbort abortingIds keys Unit 1).sign () () ())
      failingHandler}[0 < q] = 0 := by
  simp [HasQuery.queryCountDist, HasQuery.Program.withAddCost, FiatShamirWithAbort,
    fsAbortSignLoop, fsAbortSignAttempt, failingHandler, abortingIds,
    QueryImpl.withAddCost_apply]

example : FiatShamirWithAbort.signAttemptAbortProbability
    abortingIds Unit failingHandler () () () ^ 0 = 1 := pow_zero _

end VCVioTest.FiatShamirAbort
