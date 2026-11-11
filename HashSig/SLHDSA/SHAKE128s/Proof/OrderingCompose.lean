/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ClassGrowth
public import HashSig.SLHDSA.SHAKE128s.Proof.PhaseFusion

/-!
# The fused handler's two steps

The two query steps of `PhaseFusion.fuseServing`, the adversary's phase under a bracketed
handler, as equations. Both are `rfl`; they are restated here so that this file depends on
`PhaseFusion` alone.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s.OrderingCompose

open Security PhaseFusion

variable {σ : Type} {ω : Type} [Monoid ω]

/-- **The fused handler on a world query**: run the inner handler's step under the outer
handler, multiply its count into the running one, and leave the bracket state as the outer
handler leaves it. -/
theorem fuseServing_run_inl (outer : QueryImpl OracleWorld (StateT σ ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (after : σ → σ) (world : OracleWorld.Domain)
    (state : ω × SigningLog × σ) :
    ((fuseServing outer inner before after) (Sum.inl world)).run state =
      (simulateQ outer (((inner (Sum.inl world)).run).run state.2.1)).run state.2.2 >>=
        fun step => (pure (step.1.1.1, (state.1 * step.1.1.2, step.1.2, step.2)) :
          ProbComp _) := rfl

/-- **The fused handler on a signing request**: advance the bracket state by `before`, run the
inner handler's step under the outer handler, multiply its count into the running one, and
close the bracket with `after`. -/
theorem fuseServing_run_inr (outer : QueryImpl OracleWorld (StateT σ ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (after : σ → σ) (request : Message)
    (state : ω × SigningLog × σ) :
    ((fuseServing outer inner before after) (Sum.inr request)).run state =
      (simulateQ outer (((inner (Sum.inr request)).run).run state.2.1)).run
          (before request state.2.2) >>= fun step =>
        (pure (step.1.1.1, (state.1 * step.1.1.2, step.1.2, after step.2)) :
          ProbComp _) := rfl

end SLHDSA.SHAKE128s.OrderingCompose
