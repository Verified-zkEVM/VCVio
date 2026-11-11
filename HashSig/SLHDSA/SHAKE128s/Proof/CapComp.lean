/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.SignedWatch

/-!
# Capping a computation at a weighted query budget

The total budget `HasTotalBudget` is a probability-one statement about the real game. A charge
taken in a *blind* game needs the adversary's query count bounded there too, and after the blind
game's bad event its answers can be inconsistent with anything the real game produces — an
adversary that notices may then query without limit. So the adversary is capped.

`capComp weight fallback limit oa` runs `oa` until the next query would take its weighted count
past `limit`, and then returns `fallback`. Two facts make it usable:

* **On every handler, the capped run's weighted cost is at most `limit`** (`cost_capComp_le`) —
  provided the handler's state reports the cost, step by step.
* **Where the uncapped run never exceeds `limit`, capping changes nothing** (`evalDist_capComp`).

The second is applied at the real game, where the budget says the cap never fires; the first at
the blind game, where nothing else bounds the count.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s.CapComp

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- **Truncate a computation once its weighted queries would exceed the limit.** -/
@[expose] noncomputable def capComp (weight : ι → Nat) (fallback : α) :
    Nat → OracleComp spec α → OracleComp spec α :=
  fun limit oa => OracleComp.construct (C := fun _ => Nat → OracleComp spec α)
    (fun value _ => pure value)
    (fun t _ rest remaining =>
      if weight t ≤ remaining then
        liftM (spec.query t) >>= fun answer => rest answer (remaining - weight t)
      else pure fallback) oa limit

variable {S : Type}

/-- A handler whose state reports the weighted cost, query by query. -/
@[expose] def ReportsCost (impl : QueryImpl spec (StateT S ProbComp)) (weight : ι → Nat)
    (cost : S → Nat) : Prop :=
  ∀ (t : ι) (state : S), ∀ z ∈ support ((impl t).run state), cost z.2 = cost state + weight t

/-- The cost only grows along a run. -/
theorem cost_run_ge (impl : QueryImpl spec (StateT S ProbComp)) (weight : ι → Nat)
    (cost : S → Nat) (hcost : ReportsCost impl weight cost) :
    ∀ (oa : OracleComp spec α) (state : S),
      ∀ z ∈ support ((simulateQ impl oa).run state), cost state ≤ cost z.2 := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure value =>
    intro state z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | query_bind t next ih =>
    intro state z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    have := ih step.1 step.2 z hrest
    have hstepCost := hcost t state step hstep
    omega

/-- A bind is determined by its continuation on the support. -/
theorem evalDist_bind_congr_support {β γ : Type} (oa : ProbComp β) (f g : β → ProbComp γ)
    (h : ∀ a ∈ support oa, f a =ᵈ g a) : oa >>= f =ᵈ oa >>= g :=
  OracleComp.EvalDistEq.bind_congr_of_support oa h

end SLHDSA.SHAKE128s.CapComp
