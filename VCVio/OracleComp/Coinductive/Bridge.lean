/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.OracleComp
public import PolyFun.ITree.Free

/-! # Bridge between `OracleComp` and `ITree`

`OracleComp spec α` is the *inductive* free monad on `spec.toPFunctor`;
`ITree spec.toPFunctor α` is the *coinductive* (M-type) free monad on the
same polynomial functor. Every finite, terminating `OracleComp` program has
a canonical embedding into the (potentially-infinite) ITree world.

This module provides that embedding, `OracleComp.toITree`, together with the
structural equations (`toITree_pure`, `toITree_queryBind`) that compute it;
`toITree_pure` is also registered as a simp lemma.

The reverse map "ITree-to-OracleComp" exists *only* on terminating ITrees
and requires productivity / well-foundedness arguments that are not yet
in scope; hence we provide only the forward direction here.

## Universe restriction

To keep the polynomial functor uniform-universe, we specialise to
`OracleSpec.{u, u} ι`. The general `OracleSpec.{u, v}` case would force
`Poly F α` to live in `Type (max u v + 1)`, which is at odds with our
single-universe ITree definition.
-/

@[expose] public section

universe u

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α β : Type u}

/-- The canonical polynomial free-program embedding into interaction trees. -/
def toITree (oa : OracleComp spec α) : ITree spec.toPFunctor α :=
  PFunctor.FreeM.toITree oa

@[simp] theorem toITree_pure (x : α) :
    toITree (pure x : OracleComp spec α) = ITree.pure x :=
  PFunctor.FreeM.toITree_pure x

theorem toITree_queryBind (t : spec.Domain) (k : spec.Range t → OracleComp spec α) :
    toITree (queryBind t k) = ITree.query (F := spec.toPFunctor) t (fun u => toITree (k u)) :=
  PFunctor.FreeM.toITree_liftBind (E := spec.toPFunctor) t k

/-- The oracle-computation bridge is the canonical free-program bridge. -/
theorem toITree_eq_freeM (oa : OracleComp spec α) :
    toITree oa = PFunctor.FreeM.toITree oa := rfl

end OracleComp
