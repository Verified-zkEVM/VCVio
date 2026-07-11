/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.Machine

/-!
# Sequential Composition of Oracle Machines Implements Bind

The semantic half of `IsPolyTime.bind`: machines implementing `oa` and `ob` compose by
PolyFun's `PointedMachine.seqComp` to a machine implementing `fun x => oa x >>= ob` at
the summed round budget (`Implements.seqComp`).

The proof consumes PolyFun's fuel-exact sequential-composition law
(`PointedMachine.runWith_seqComp_init`), whose per-phase resolution certificates come
from the implements equations themselves: instantiating the monad-parametric
`Implements` at the *syntactic* monad `m := OracleComp spec` with the identity query
implementation turns the run into the unrolling itself (`Implements.toComp_eq`), whose
`some <$> _` shape is exactly the no-`none`-leaves certificate
(`PointedMachine.resolvesIn_of_toComp_eq_map_some`). This extraction is the first
concrete dividend of stating `Implements` over every lawful monad rather than over
`SPMF` alone.
-/

universe u

open OracleSpec PFunctor

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α mid β : Type u}

namespace OracleMachine

/-- **Syntactic canary extraction**: an implements equation, instantiated at the
identity query implementation in `m := OracleComp spec`, says the machine's unrolling
*is* the program (up to the `some` resolution layer). -/
theorem Implements.toComp_eq {M : OracleMachine spec α β} {oa : α → OracleComp spec β}
    {k : ℕ} (h : M ⊨[k] oa) (x : α) :
    M.toComp k (M.init x) = some <$> oa x := by
  have key := h (QueryImpl.id' spec) x
  rwa [show M.runK (QueryImpl.id' spec) k (M.init x)
      = simulateQ (QueryImpl.id' spec) (M.toComp k (M.init x)) from rfl,
    simulateQ_id', simulateQ_id'] at key

/-- An implementing machine carries the syntactic resolution certificate: every answer
path of the `k`-query unrolling reads out. -/
theorem Implements.resolvesIn {M : OracleMachine spec α β} {oa : α → OracleComp spec β}
    {k : ℕ} (h : M ⊨[k] oa) (x : α) :
    PointedMachine.ResolvesIn M k (M.init x) :=
  PointedMachine.resolvesIn_of_toComp_eq_map_some (h.toComp_eq x)

/-- **Sequential composition implements bind**: machines implementing the two stages
compose by `PointedMachine.seqComp` to a machine implementing the bound program at the
summed round budget — in every lawful monad at once, by the fuel-exact composition law
with the resolution certificates extracted from the implements equations. This is the
semantic half of `IsPolyTime.bind`; the Turing-machine halves (state encoding and step
witnesses for the `⊕`-state machine) are supplied separately. -/
theorem Implements.seqComp {M₁ : OracleMachine spec α mid} {M₂ : OracleMachine spec mid β}
    {oa : α → OracleComp spec mid} {ob : mid → OracleComp spec β} {k₁ k₂ : ℕ}
    (h₁ : M₁ ⊨[k₁] oa) (h₂ : M₂ ⊨[k₂] ob) :
    M₁ ⨟ M₂ ⊨[k₁ + k₂] fun x => oa x >>= ob := by
  intro m _ _ H x
  rw [show OracleMachine.runK (M₁ ⨟ M₂) H (k₁ + k₂) ((M₁ ⨟ M₂).init x)
      = (M₁ ⨟ M₂).runWith H (k₁ + k₂) ((M₁ ⨟ M₂).init x) from rfl,
    PointedMachine.runWith_seqComp_init M₁ M₂ H k₂ x (h₁.resolvesIn x)
      (fun y => h₂.resolvesIn y),
    show M₁.runWith H k₁ (M₁.init x) = M₁.runK H k₁ (M₁.init x) from rfl,
    h₁ H x, simulateQ_bind, map_eq_bind_pure_comp, bind_assoc, map_bind]
  refine bind_congr fun a => ?_
  rw [Function.comp_apply, pure_bind]
  exact h₂ H a

end OracleMachine
