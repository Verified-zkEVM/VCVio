/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Support
public import VCVio.OracleComp.EvalDist

/-!
# Exact return predicates for oracle computations

The polynomial free monad's exact `MonadAttach` return predicate agrees with the framework's
syntactic support fold. This bridge allows generic progress and invariant theorems to use the
same oracle-response paths as probability-facing support arguments.
-/

public section

universe u v

namespace OracleComp

variable {ι : Type u} {α : Type v} {spec : OracleSpec.{u, v} ι}

/-- Generic exact return reachability agrees with the oracle support interpretation. -/
theorem canReturn_iff_mem_support (program : OracleComp spec α) (value : α) :
    MonadAttach.CanReturn program value ↔ value ∈ support program := by rfl

end OracleComp
