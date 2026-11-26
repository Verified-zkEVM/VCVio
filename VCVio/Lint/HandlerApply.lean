/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public meta import PolyFun.Lint.HandlerApply

/-!
# Application lemmas for query implementations

PolyFun's check on handlers, for `QueryImpl`: a query implementation built by its constructor is
used through the equation for its application, so it needs an application lemma (`@[simps]`
generates one) and must not be reducible.
-/

public meta section

open Batteries.Tactic.Lint

namespace VCVio.Lint

/-- Report query implementations built by the constructor of `QueryImpl` that have no application
lemma or are reducible. -/
@[env_linter] def queryImplApply : Linter :=
  PolyFun.Lint.handlerApplyFor [(`QueryImpl, `QueryImpl.toFun)]

end VCVio.Lint
