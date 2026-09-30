/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Tactic.Attr.Register

/-!
# The `expect_norm` and `expect_eval` simp sets

`expect_norm` rewrites an expectation into the normal form `𝔼{…}[…]` and `Pr{…}[…]` elaborate
to: nested expectations of the draws, with no `bind`, `map`, `pure` or branch left at the head of
a drawn computation. Two expectations written differently, for example through an intermediate
pair or a composed map, become syntactically equal after `simp only [expect_norm]`.

`expect_eval` continues the evaluation: it unfolds loops and gives the value of a query or a
uniform draw, so `simp only [expect_norm, expect_eval]` states an expectation through the answer
measures of its draws.

The sets are registered here, apart from their lemmas, because `register_simp_attr` does not take
effect in the file that declares it.
-/

public section

/-- Rewrite rules bringing an expectation into the normal form of `𝔼{…}[…]` and `Pr{…}[…]`. -/
register_simp_attr expect_norm

/-- Equations evaluating an expectation in normal form one step further: the unfolding of a loop
(`replicate`, `List.mapM`, `List.foldlM`), the value of a query or a uniform draw, and the
pointwise form of a composed observation. Used as `simp only [expect_norm, expect_eval]` on an
equation between an expectation and its value. -/
register_simp_attr expect_eval
