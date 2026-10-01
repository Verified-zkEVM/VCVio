/-
Copyright (c) 2026 Devon Tuma, Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import ToMathlib.Algebra.BigOperators.Finset
public import ToMathlib.Control.Functor.Prod
public import ToMathlib.Algebra.BigOperators.List
public import ToMathlib.Data.Fin.Basic
public import ToMathlib.Data.Vector.ListVector
public import ToMathlib.Logic.Basic
public import ToMathlib.Data.List.Count
public import ToMathlib.Data.Vector.Count
public import ToMathlib.Data.BitVec
public import ToMathlib.Data.Vector.Induction
public import ToMathlib.Topology.Algebra.InfiniteSum.Option
public import ToMathlib.Control.Monad.Fold
public meta import ToMathlib.Lint.LegacyProbability

/-!
# Shared utilities and semantic normalization

General finite-data utilities and proof attributes used by oracle programs, measure semantics,
and program logic.
-/

public section

declare_aesop_rule_sets [UnfoldEvalDist]

/-- Rewrite rules bringing an expectation into the normal form of `𝔼{…}[…]` and `Pr{…}[…]`:
nested expectations of the draws, with no `bind`, `map`, `pure` or branch left at the head of a
drawn computation. Two expectations written differently become syntactically equal after
`simp only [expect_norm]`. -/
register_simp_attr expect_norm

/-- Equations evaluating an expectation in normal form one step further: the unfolding of a loop
(`replicate`, `List.mapM`, `List.foldlM`), the value of a query or a uniform draw, the pointwise
form of a composed observation, and the steps of a simulation (`simulateQ`). Used as
`simp only [expect_norm, expect_eval]` on an equation between an expectation and its value. -/
register_simp_attr expect_eval

/-- Linearity of expectation and the algebra of indicators (`wp_add`, `wp_const_mul`,
`propInd_and`, …), the arithmetic the tactic `expect_arith` normalizes with. -/
register_simp_attr expect_arith

/-- VCVio-specific extension of PolyFun's `handler_nf` normalization set. -/
register_simp_attr handler_simp
