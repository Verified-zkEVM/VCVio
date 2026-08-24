/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.Asymptotics.OracleClosure

/-!
# Oracle-handler complexity API checks

Compile-time checks for the proof-bearing handler boundary and its whole-tree result-conformance
predicate.
-/

public section

open PFunctor
open OracleComp.Complexity

#check FreeM.LeavesSatisfyUnder
#check FreeM.leavesSatisfyUnder_bind_iff
#check handlerBoundary
#check packHandler
#check closeHandler
#check HandlerCertificate
#check HandlerCertificate.packedReturnsAllowed
#check HandlerCertificate.isOraclePPTBy

universe u

namespace OracleComp.Complexity

variable {p q : PFunctor.{u, u}} {α : Type u}

example (handler : ∀ position : p.A, FreeM q (p.B position))
    (position : p.A) :
    packHandler handler position =
      (fun answer ↦ ⟨position, answer⟩) <$> handler position :=
  rfl

example (handler : ∀ position : p.A, FreeM q (p.B position))
    (result : α) :
    closeHandler handler (pure result : FreeM p α) = pure result :=
  rfl

end OracleComp.Complexity
