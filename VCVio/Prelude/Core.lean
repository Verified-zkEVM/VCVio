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

/-- Simp set for game-hopping proofs of program and semantic equations. -/
register_simp_attr game_rule

/-- VCVio-specific extension of PolyFun's `handler_nf` normalization set. -/
register_simp_attr handler_simp
