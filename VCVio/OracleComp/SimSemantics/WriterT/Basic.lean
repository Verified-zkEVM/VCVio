/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.SimSemantics.WriterT.Core
public import VCVio.OracleComp.ReachableWhen
public import VCVio.OracleComp.Support
public import PolyFun.PFunctor.Free.WP
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import ToMathlib.Data.Set.Functor

/-!
# Probability compatibility for writer-instrumented handlers

Scalar failure and losslessness identities for writer-instrumented oracle simulations.
-/

@[expose] public section

open OracleSpec

universe u

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α : Type u} {ω : Type u} [Monoid ω]

end OracleComp
