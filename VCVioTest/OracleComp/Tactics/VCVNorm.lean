/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module
public import VCVio.OracleComp.Tactics.VCVNorm

/-!
# The `loggingStrip` simproc

The simproc removes a `loggingOracle` run whose log the continuation ignores, at any nesting depth.
It leaves a run alone when the continuation reads the log, and when the left side of the bind only
contains a logged run instead of being one.
-/

open OracleComp OracleSpec

public section

namespace VCVNormTest

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β γ δ : Type}

-- A run whose log is ignored strips.
example (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    ((simulateQ loggingOracle oa).run >>= fun x => ob x.1) = oa >>= ob := by
  vcv_strip_log

-- `vcv_norm` strips through the same simproc.
example (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    ((simulateQ loggingOracle oa).run >>= fun x => ob x.1) = oa >>= ob := by
  vcv_norm

-- Two nested logged runs both strip.
example (oa : OracleComp spec α) (ob : α → OracleComp spec β) (k : α → β → γ) :
    ((simulateQ loggingOracle oa).run >>= fun p =>
      (simulateQ loggingOracle (ob p.1)).run >>= fun q => pure (k p.1 q.1)) =
      oa >>= fun a => ob a >>= fun b => pure (k a b) := by
  vcv_strip_log

-- So do three, the shape of a prover, verifier and extractor chain.
example (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (oc : α → β → OracleComp spec γ) (k : α → β → γ → δ) :
    ((simulateQ loggingOracle oa).run >>= fun p =>
      (simulateQ loggingOracle (ob p.1)).run >>= fun q =>
        (simulateQ loggingOracle (oc p.1 q.1)).run >>= fun r => pure (k p.1 q.1 r.1)) =
      oa >>= fun a => ob a >>= fun b => oc a b >>= fun c => pure (k a b c) := by
  vcv_strip_log

-- A run whose log is read must stay: the simproc makes no progress.
example (oa : OracleComp spec α) (read : QueryLog spec → OracleComp spec β)
    (rhs : OracleComp spec β)
    (h : ((simulateQ loggingOracle oa).run >>= fun x => read x.2) = rhs) :
    ((simulateQ loggingOracle oa).run >>= fun x => read x.2) = rhs := by
  fail_if_success vcv_strip_log
  exact h

-- Reading the value as well as the log does not help.
example (oa : OracleComp spec α) (read : α → QueryLog spec → OracleComp spec β)
    (rhs : OracleComp spec β)
    (h : ((simulateQ loggingOracle oa).run >>= fun x => read x.1 x.2) = rhs) :
    ((simulateQ loggingOracle oa).run >>= fun x => read x.1 x.2) = rhs := by
  fail_if_success vcv_strip_log
  exact h

-- Under a kept outer log, an unused inner log still strips, and the outer run stays in place.
example (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (read : QueryLog spec → β → OracleComp spec γ) (rhs : OracleComp spec γ)
    (h : ((simulateQ loggingOracle oa).run >>= fun x => ob x.1 >>= read x.2) = rhs) :
    ((simulateQ loggingOracle oa).run >>= fun x =>
      (simulateQ loggingOracle (ob x.1)).run >>= fun y => read x.2 y.1) = rhs := by
  vcv_strip_log
  guard_target = ((simulateQ loggingOracle oa).run >>= fun x => ob x.1 >>= read x.2) = rhs
  exact h

-- A logged run under a map is not literally the left side of the strip lemma, whose proof would
-- not typecheck there.
example (oa : OracleComp spec α) (ob : α → OracleComp spec β) (rhs : OracleComp spec β)
    (f : α × QueryLog spec → α × QueryLog spec)
    (h : (f <$> (simulateQ loggingOracle oa).run >>= fun x => ob x.1) = rhs) :
    (f <$> (simulateQ loggingOracle oa).run >>= fun x => ob x.1) = rhs := by
  fail_if_success vcv_strip_log
  exact h

-- Nor is a logged run interpreted further by a stateful handler.
example {σ : Type} (impl : QueryImpl spec (StateT σ ProbComp)) (oa : OracleComp spec α)
    (s : σ) (ob : (α × QueryLog spec) → ProbComp β) (rhs : ProbComp β)
    (h : ((simulateQ impl (simulateQ loggingOracle oa).run).run s >>= fun x => ob x.1) = rhs) :
    ((simulateQ impl (simulateQ loggingOracle oa).run).run s >>= fun x => ob x.1) = rhs := by
  fail_if_success vcv_strip_log
  exact h

end VCVNormTest
