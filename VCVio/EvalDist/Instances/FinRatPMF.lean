/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import ToMathlib.ProbabilityTheory.FinRatPMF
public import VCVio.EvalDist.Defs.Basic
public import VCVio.EvalDist.Defs.Measure.FinRatPMF

/-!
# Measure Semantics for `FinRatPMF.Raw`

The executable rational distribution has native measure semantics and discrete interoperability.
Its namespaced `Raw.support` records positive mass; raw arrays may also retain zero-weight
entries, so generic `MonadAttach.support` is not defined for `Raw`.
-/

@[expose] public section

universe u

namespace FinRatPMF
namespace Raw

noncomputable instance : MonadLift Raw PMF where
  monadLift := Raw.toPMFHom.toFun _

noncomputable instance : LawfulMonadLift Raw PMF where
  monadLift_pure := Raw.toPMFHom.toFun_pure'
  monadLift_bind := Raw.toPMFHom.toFun_bind'

end Raw
end FinRatPMF
