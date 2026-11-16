/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# `simulateQ` normal forms after `simp`

`simp` distributes `simulateQ` over the monad operations and leaves every piece
`simulateQ`-headed, so a later `rw` with a `simulateQ`-headed lemma or hypothesis still finds its
pattern. The `PFunctor.FreeM.liftM` simp lemmas of CSLib do not rewrite `simulateQ` terms.
-/

public section

open OracleComp

namespace VCVioTest.OracleComp.SimulateQ

variable {ι : Type} {spec : OracleSpec ι} {r : Type → Type} [Monad r] [LawfulMonad r]
  {α β : Type}

/-- `simp` splits a simulated bind into `simulateQ`-headed parts. -/
example (impl : QueryImpl spec r) (oa : OracleComp spec α) (k : α → OracleComp spec β)
    (x : r α) (h : simulateQ impl oa = x) :
    simulateQ impl (oa >>= k) = x >>= fun a => simulateQ impl (k a) := by
  simp
  guard_target =ₛ
    (simulateQ impl oa >>= fun a => simulateQ impl (k a)) = x >>= fun a => simulateQ impl (k a)
  simp [h]

/-- After `simp` splits a simulated bind, the query its first part stands for is still simulated
by `simulateQ`, so `simulateQ_spec_query` rewrites it. -/
example (impl : QueryImpl spec r) (t : spec.Domain) (oa : OracleComp spec (spec.Range t))
    (k : spec.Range t → OracleComp spec β) (h : oa = liftM (spec.query t)) :
    simulateQ impl (oa >>= k) = impl t >>= fun u => simulateQ impl (k u) := by
  conv_lhs => simp
  rw [h, simulateQ_spec_query]

/-- A hypothesis about `simulateQ impl oa` rewrites the first part `simp` splits off a bind. -/
example (impl : QueryImpl spec r) (oa : OracleComp spec α) (k : α → OracleComp spec β)
    (x : r α) (h : simulateQ impl oa = x) :
    simulateQ impl (oa >>= k) = x >>= fun a => simulateQ impl (k a) := by
  conv_lhs => simp
  rw [h]

/-- A hypothesis about `simulateQ impl oa` rewrites the computation `simp` pulls out of a map. -/
example (impl : QueryImpl spec r) (oa : OracleComp spec α) (f : α → β) (x : r α)
    (h : simulateQ impl oa = x) :
    simulateQ impl (f <$> oa) = f <$> x := by
  conv_lhs => simp
  rw [h]

/-- CSLib's `PFunctor.FreeM.liftM_bind` does not rewrite a `simulateQ` term; the
`simulateQ`-headed lemmas do. -/
example (impl : QueryImpl spec r) (t : spec.Domain) (k : spec.Range t → OracleComp spec β) :
    simulateQ impl (liftM (spec.query t) >>= k) = impl t >>= fun u => simulateQ impl (k u) := by
  fail_if_success simp only [PFunctor.FreeM.liftM_bind]
  rw [simulateQ_bind, simulateQ_spec_query]

end VCVioTest.OracleComp.SimulateQ
