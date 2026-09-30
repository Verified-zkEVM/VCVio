/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Tactic.Attr.Register

/-!
# The `expect_norm` simp set

`expect_norm` rewrites an expectation into the normal form `𝔼{…}[…]` and `Pr{…}[…]` elaborate
to: nested expectations of the draws, with no `bind`, `map`, `pure` or branch left at the head of
a drawn computation. Two expectations written differently, for example through an intermediate
pair or a composed map, become syntactically equal after `simp only [expect_norm]`. The set is
registered here, apart from its lemmas, because `register_simp_attr` does not take effect in the
file that declares it.
-/

public section

/-- Rewrite rules bringing an expectation into the normal form of `𝔼{…}[…]` and `Pr{…}[…]`. -/
register_simp_attr expect_norm
