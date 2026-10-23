/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.SensitiveQuery

/-!
# Bind congruence for equal laws

This file holds the one congruence lemma that `RedrawCell` uses to compare presentations of the
same run: binding a common continuation after two computations of the same law gives the same
law.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.LazyBridge

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- **Bind congruence.** Binding a common continuation after two computations of the same law
gives the same law. -/
theorem evalDist_bind_congr_right {α β : Type} {oa ob : ProbComp α} (hlaw : 𝒟[oa] = 𝒟[ob])
    (k : α → ProbComp β) : 𝒟[oa >>= k] = 𝒟[ob >>= k] := by
  rw [evalDist_bind, evalDist_bind, hlaw]

end SlhDsaSecurity.LazyBridge
