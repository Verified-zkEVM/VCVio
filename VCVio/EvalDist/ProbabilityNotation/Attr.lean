/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Tactic.Attr.Register

/-!
# The `prEvent_norm` simp set

`prEvent_norm` rewrites an event computation into the form `Pr{…}[…]` elaborates to: a chain of
binds ending in a map of the final selector. Two events written differently, for example through
an intermediate pair or a composed map, become syntactically equal after
`simp only [prEvent_norm]`. The set is registered here, apart from its lemmas, because
`register_simp_attr` does not take effect in the file that declares it.
-/

public section

/-- Rewrite rules bringing an event computation into the normal form of `Pr{…}[…]`. -/
register_simp_attr prEvent_norm
