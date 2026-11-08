/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module
public import VCVio.OracleComp.QueryTracking.QueryLog

/-!
# Query-log simplification checks

One-call examples for the simplification rules that look up entries and project routed logs.
-/

open OracleSpec

public section

namespace VCVioTest.QueryLog

example {ι : Type} {spec : OracleSpec ι} [DecidableEq ι] (t : spec.Domain) :
    QueryLog.lookup? ([] : QueryLog spec) t = none := by
  simp

example {ι κ ν : Type} {a : OracleSpec ι} {b : OracleSpec κ} {c : OracleSpec ν}
    (log : QueryLog ((a + b) + c)) :
    log.swapRight.eraseMiddle = log.fst := by
  simp

example {ι κ ν : Type} {a : OracleSpec ι} {b : OracleSpec κ} {c : OracleSpec ν}
    (log : QueryLog ((a + c) + b)) :
    log.eraseMiddle.snd = log.snd := by
  simp

example {ι κ ν : Type} {a : OracleSpec ι} {b : OracleSpec κ} {c : OracleSpec ν}
    (log : QueryLog ((a + c) + b)) :
    log.eraseMiddle.fst = log.fst.fst := by
  simp

end VCVioTest.QueryLog
