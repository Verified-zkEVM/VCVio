/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.MapLens

/-!
# The input-routing lens of a random oracle

`OracleComp.RandomOracleRouting.lens encode` sends each query `a` of `A →ₒ R` to the query
`encode a` of `B →ₒ R` and returns its response unchanged; `RandomOracleRouting.route encode`
transports a client along it. These are universe polymorphic and need only the lens API. The
measure laws of routing into a finite random oracle are in
`VCVio.OracleComp.QueryTracking.RandomOracle.Routing`.
-/

public section

open OracleSpec

namespace OracleComp.RandomOracleRouting

universe u

variable {A B R X : Type u}

/-- Route inputs through an encoding while retaining each response unchanged. -/
@[expose]
def lens (encode : A → B) :
    PFunctor.Lens (A →ₒ R).toPFunctor (B →ₒ R).toPFunctor where
  toFunA := encode
  toFunB _ := id

/-- Apply an input encoding at every query of an adaptive client. -/
@[expose]
def route (encode : A → B) (program : OracleComp (A →ₒ R) X) :
    OracleComp (B →ₒ R) X := program.mapLens (lens encode)

end OracleComp.RandomOracleRouting
