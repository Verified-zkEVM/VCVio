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

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s.LazyBridge

/-- **Bind congruence.** Binding a common continuation after two computations of the same law
gives the same law. -/
theorem evalDist_bind_congr_right {α β : Type} {oa ob : ProbComp α} (hlaw : oa =ᵈ ob)
    (k : α → ProbComp β) : oa >>= k =ᵈ ob >>= k := by
  exact hlaw.bind_left k

end SLHDSA.SHAKE128s.LazyBridge
