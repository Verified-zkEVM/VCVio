/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import PolyFun.PFunctor.Dynamical.PointedMachine
import VCVio.OracleComp.Coinductive.DynSystem
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Oracle Machines: Strategies with Initialization and Readout

An `OracleMachine spec α β` is PolyFun's `PFunctor.PointedMachine` at the spec's polynomial:
an `OracleStrategy` together with an initial-state map `init : α → State` and a Moore-style
partial readout `output : State → Option β`. `output s = some b` means the machine has
halted with result `b`, while `none` means it queries on. This is the machine-shaped
presentation of an adversary `α → OracleComp spec β`; since the machine is given by a state
type and pure step functions, it is the shape on which computational-cost notions (such as
Turing-machine polynomial time, in `VCVio.OracleComp.Coinductive.PolyTime`) can be imposed.

The run/unrolling theory is inherited from PolyFun rather than duplicated:

* `OracleMachine.toComp` is `PFunctor.PointedMachine.toComp` — the fuelled unrolling into
  `OracleComp spec (Option β)` (which *is* `FreeM spec.toPFunctor (Option β)`). Fuel counts
  queries exactly: the readout is free, so the `k`-step unrolling makes at most `k` queries
  and resolves precisely when the machine is steady within `k` queries.
* `OracleMachine.runK`: the monad-parametric fuelled run — `PointedMachine.runWith` fed a
  `QueryImpl spec m` (which *is* a `PFunctor.Handler m spec.toPFunctor`). The probabilistic
  run of an adversary is the `m := SPMF` instance; the early-stopping behaviour (halted
  states are absorbing) is what keeps sub-probability mass against lossy handlers.
* `OracleMachine.runD`: the deterministic run, the `m := Id` instance of `runK`.
* `simulateQ H (M.toComp k s) = M.runK H k s` is *definitional* (`simulateQ` is
  `FreeM.mapM`, and `runWith` is `FreeM.mapM ∘ toComp`).

Key definitions:

* `OracleMachine.Implements M oa k` (scoped notation `M ⊨[k] oa`): the run of `M` at fuel
  `k` agrees with `simulateQ` of
  `oa` against every query implementation in every lawful monad. The single-monad SPMF
  form (agreement against every `ProbHandler`) already pins down distribution semantics,
  but the monad-parametric form is what stateful challengers consume (`m := StateT σ SPMF`
  runs a machine against an oracle with hidden state) and it makes the deterministic form
  `ImplementsDet` the trivial `m := Id` instance rather than a Dirac-bridge argument.
* `OracleMachine.IsSimulation`: a step-synchronized simulation relation between machine
  states and program residues; `implements_of_isSimulation` is the practical method for
  establishing `Implements`, with the fuel supplied by a total query bound. One fuel
  induction gives agreement in *every* lawful monad at once.
-/

universe u v w

open OracleSpec PFunctor

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α β : Type u}

/-! ## Oracle machines -/

/-- An oracle machine: PolyFun's `PointedMachine` over the spec's polynomial. An adaptive
querying strategy (`OracleStrategy`, the `toDynSystem` parent) together with an
initialization of its state from an input and a Moore-style partial readout of its result.
`output s = some b` means the machine has halted with result `b`; `output s = none` means
it queries on. Since a machine is a state type with pure Lean step functions, it is the
presentation of an adversary on which per-step computational cost can be imposed. -/
abbrev OracleMachine (spec : OracleSpec.{u, u} ι) (α β : Type u) :=
  PFunctor.PointedMachine.{u, u, u, u, u} spec.toPFunctor α β

/-- A query implementation *is* a PolyFun handler for the spec's polynomial — the
identification `runK = PointedMachine.runWith` rests on. Recorded as a regression
guard: it must remain definitional. -/
example {m : Type u → Type u} : QueryImpl spec m = PFunctor.Handler m spec.toPFunctor := rfl

namespace OracleMachine

variable (M : OracleMachine spec α β)

/-! ## Stability and steadiness -/

/-- Output stability: once the readout is `some b`, every further update preserves it. -/
def StableOutput : Prop :=
  ∀ ⦃s : M.State⦄ ⦃b : β⦄, M.output s = some b →
    ∀ r : spec.Range (M.expose s), M.output (M.update s r) = some b

/-- A stable readout persists along every handler-answered run. -/
theorem StableOutput.output_stateAfter {M : OracleMachine spec α β} (hst : M.StableOutput)
    (h : OracleHandler spec) {s : M.State} {b : β} (hb : M.output s = some b) (k : ℕ) :
    M.output (OracleStrategy.stateAfter h M.toDynSystem s k) = some b := by
  induction k generalizing s with
  | zero => exact hb
  | succ k ih => exact OracleStrategy.stateAfter_succ h M.toDynSystem s k ▸ ih (hst hb _)

/-- Steadiness against a handler: after `k` answered steps from `s`, the readout has
resolved. -/
def SteadyBy (h : OracleHandler spec) (s : M.State) (k : ℕ) : Prop :=
  (M.output (OracleStrategy.stateAfter h M.toDynSystem s k)).isSome

/-! ## Fuelled monad-parametric runs

`runK` is `PointedMachine.runWith`: a `QueryImpl spec m` is definitionally a
`PFunctor.Handler m spec.toPFunctor`, so the machine run against a randomized oracle
(`m := SPMF`), a stateful oracle (`m := StateT σ SPMF`), or a deterministic handler
(`m := Id`, packaged as `runD`) are all instances of one PolyFun run. -/

section runK

variable {m : Type u → Type u} [Monad m]

/-- The fuelled run of a machine against a query implementation in an arbitrary monad,
stopping early at the first `some` readout. At `m := SPMF` this is the sub-distribution
over readouts after at most `k` adaptive queries, with halted states absorbing; early
stopping is essential there, since continuing to sample after halting would multiply by
the remaining handler mass against lossy handlers. -/
def runK (H : QueryImpl spec m) : ℕ → M.State → m (Option β) :=
  M.runWith H

@[simp] theorem runK_zero (H : QueryImpl spec m) (s : M.State) :
    M.runK H 0 s = pure (M.output s) := rfl

theorem runK_succ_of_output_eq_none (H : QueryImpl spec m) {s : M.State}
    (hb : M.output s = none) (k : ℕ) :
    M.runK H (k + 1) s = H (M.expose s) >>= fun r => M.runK H k (M.update s r) := by
  rw [runK, PointedMachine.runWith_succ, hb]
  rfl

/-- A halted machine's run is `pure` on its readout, at any fuel. -/
theorem runK_of_output_eq_some (H : QueryImpl spec m) {s : M.State} {b : β}
    (hb : M.output s = some b) (k : ℕ) : M.runK H k s = pure (some b) :=
  PointedMachine.runWith_of_output_eq_some M H k hb

theorem runK_succ_of_output_eq_some (H : QueryImpl spec m) {s : M.State} {b : β}
    (hb : M.output s = some b) (k : ℕ) : M.runK H (k + 1) s = pure (some b) :=
  M.runK_of_output_eq_some H hb (k + 1)

/-- The probabilistic run unfolds through `kleisliStep`: sample an answer, advance, and
recurse. The generic unfolding is `runK_succ_of_output_eq_none`. -/
theorem runK_succ_of_output_eq_none' (H : ProbHandler spec) {s : M.State}
    (hb : M.output s = none) (k : ℕ) :
    M.runK H (k + 1) s = OracleStrategy.kleisliStep H M.toDynSystem s >>= M.runK H k := by
  rw [M.runK_succ_of_output_eq_none H hb, OracleStrategy.kleisliStep, bind_map_left]
  rfl

end runK

/-! ## The deterministic run -/

/-- The fuelled deterministic run of a machine against a handler: the `m := Id` instance
of `runK`, stopping early at the first `some` readout. For stable machines the plain
readout after `k` steps agrees (`runD_eq_output_stateAfter`). -/
def runD (h : OracleHandler spec) (k : ℕ) (s : M.State) : Option β :=
  M.runK (m := Id) h.toQueryImpl k s

@[simp] theorem runD_zero (h : OracleHandler spec) (s : M.State) :
    M.runD h 0 s = M.output s := rfl

theorem runD_succ_of_output_eq_some (h : OracleHandler spec) {s : M.State} {b : β}
    (hb : M.output s = some b) (k : ℕ) : M.runD h (k + 1) s = some b :=
  M.runK_succ_of_output_eq_some h.toQueryImpl hb k

theorem runD_succ_of_output_eq_none (h : OracleHandler spec) {s : M.State}
    (hb : M.output s = none) (k : ℕ) :
    M.runD h (k + 1) s = M.runD h k (OracleStrategy.advanceOnce h M.toDynSystem s) :=
  M.runK_succ_of_output_eq_none (m := Id) h.toQueryImpl hb k

/-- A halted machine's run is its readout, at any fuel. -/
theorem runD_of_output_eq_some (h : OracleHandler spec) {s : M.State} {b : β}
    (hb : M.output s = some b) (k : ℕ) : M.runD h k s = some b :=
  M.runK_of_output_eq_some h.toQueryImpl hb k

/-- For a stable machine, the early-stopping run is the plain readout after `k` steps. -/
theorem runD_eq_output_stateAfter {M : OracleMachine spec α β} (hst : M.StableOutput)
    (h : OracleHandler spec) (k : ℕ) (s : M.State) :
    M.runD h k s = M.output (OracleStrategy.stateAfter h M.toDynSystem s k) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    cases hb : M.output s with
    | none =>
      rw [M.runD_succ_of_output_eq_none h hb, ih, OracleStrategy.stateAfter_succ]
    | some b =>
      rw [M.runD_succ_of_output_eq_some h hb, (hst.output_stateAfter h hb (k + 1)).symm]

/-- For a stable machine, steadiness is exactly the early-stopping run resolving. -/
theorem steadyBy_iff_isSome_runD {M : OracleMachine spec α β} (hst : M.StableOutput)
    (h : OracleHandler spec) (s : M.State) (k : ℕ) :
    M.SteadyBy h s k ↔ (M.runD h k s).isSome := by
  rw [SteadyBy, runD_eq_output_stateAfter hst]

/-- **Dirac bridge**: the probabilistic run against a deterministic handler is the Dirac
mass on the deterministic run. -/
@[simp] theorem runK_ofHandler (h : OracleHandler spec) (k : ℕ) (s : M.State) :
    M.runK (ProbHandler.ofHandler h) k s = pure (M.runD h k s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    cases hb : M.output s with
    | some b =>
      rw [M.runK_succ_of_output_eq_some _ hb, M.runD_succ_of_output_eq_some h hb]
    | none =>
      rw [M.runK_succ_of_output_eq_none' _ hb, OracleStrategy.kleisliStep_ofHandler,
        pure_bind, ih, M.runD_succ_of_output_eq_none h hb]

end OracleMachine

namespace OracleComp

/-! ## Simulation by a deterministic handler is deterministic -/

/-- `simulateQ` on the `queryBind` constructor: answer the head query with the
implementation, then simulate the continuation. -/
theorem simulateQ_queryBind {r : Type u → Type w} [Monad r] [LawfulMonad r]
    (impl : QueryImpl spec r) (t : spec.Domain) (k : spec.Range t → OracleComp spec β) :
    simulateQ impl (queryBind t k) = impl t >>= fun u => simulateQ impl (k u) := by
  rw [show queryBind t k = liftM (spec.query t) >>= k from rfl, simulateQ_bind,
    simulateQ_spec_query]

/-- `simulateQ` under the Dirac lift of a deterministic handler is the Dirac mass on the
deterministic evaluation `evalWithAnswerFn`. -/
theorem simulateQ_ofHandler (h : OracleHandler spec) (ob : OracleComp spec β) :
    simulateQ (ProbHandler.ofHandler h) ob =
      (pure (evalWithAnswerFn (QueryImpl.ofFn h) ob) : SPMF β) := by
  induction ob with
  | pure x => rfl
  | queryBind t k ih =>
    rw [simulateQ_queryBind]
    simp only [ProbHandler.ofHandler, pure_bind]
    rw [ih (h t), evalWithAnswerFn_queryBind, QueryImpl.ofFn_apply]

end OracleComp

namespace OracleMachine

/-! ## The implements relation -/

variable (M : OracleMachine spec α β)

/-- A machine implements a program at fuel `k`: **PolyFun's native
`PointedMachine.Implements`**, the free-handler equation `M.toComp k (M.init x) = some <$> oa x`
(`OracleComp spec` is `FreeM spec.toPFunctor`). Stated at the free/initial handler, it pins
the machine's observable behaviour once and universally; the run against *any* lawful-monad
handler is the derived reading `Implements.runK_eq` (the `m := SPMF` instance pins the full
distribution; `m := Id` gives the deterministic form). -/
def Implements (oa : α → OracleComp spec β) (k : ℕ) : Prop :=
  PFunctor.PointedMachine.Implements M oa k

@[inherit_doc Implements]
scoped notation:50 M " ⊨[" k "] " oa => OracleMachine.Implements M oa k

/-- **The handler reading of `Implements`.** Running an implementing machine through any
lawful-monad handler `H` agrees with `simulateQ H` of the program — a one-line corollary of
`PointedMachine.Implements.runWith_eq` via `FreeM.mapM` naturality, using `runK = runWith`
and `simulateQ = FreeM.mapMHom` definitionally. This is the monad-parametric form the
stateful game transfer consumes (`m := StateT σ SPMF`), the distribution semantics
(`m := SPMF`), and the deterministic form (`m := Id`), all at once. -/
theorem Implements.runK_eq {M : OracleMachine spec α β} {oa : α → OracleComp spec β} {k : ℕ}
    (h : M ⊨[k] oa) ⦃m : Type u → Type u⦄ [Monad m] [LawfulMonad m]
    (H : QueryImpl spec m) (x : α) :
    M.runK H k (M.init x) = some <$> simulateQ H (oa x) :=
  PFunctor.PointedMachine.Implements.runWith_eq M H h x

/-- Converse of `Implements.runK_eq`: agreement of the fuelled run with `simulateQ` against
every lawful-monad handler already gives `Implements` — it suffices to check the free/initial
handler (`m := OracleComp spec`, `QueryImpl.id'`), where `runK` is `toComp` and `simulateQ` is
the identity. Lets run-level arguments (e.g. `runK_setInit`) discharge `Implements`. -/
theorem Implements.of_runK_eq {M : OracleMachine spec α β} {oa : α → OracleComp spec β} {k : ℕ}
    (h : ∀ ⦃m : Type u → Type u⦄ [Monad m] [LawfulMonad m] (H : QueryImpl spec m) (x : α),
      M.runK H k (M.init x) = some <$> simulateQ H (oa x)) : M ⊨[k] oa := by
  intro x
  have key := h (m := OracleComp spec) (QueryImpl.id' spec) x
  rwa [show M.runK (QueryImpl.id' spec) k (M.init x) = M.toComp k (M.init x) from
    simulateQ_id' _, simulateQ_id'] at key

/-- The deterministic form of the implements relation: the early-stopping run against
every deterministic handler computes `evalWithAnswerFn`. Weaker than `Implements`; see
`Implements.implementsDet`. -/
def ImplementsDet (oa : α → OracleComp spec β) (k : ℕ) : Prop :=
  ∀ (h : OracleHandler spec) (x : α),
    M.runD h k (M.init x) = some (evalWithAnswerFn (QueryImpl.ofFn h) (oa x))

/-- Monad-parametric agreement specializes to deterministic agreement at `m := Id`. -/
theorem Implements.implementsDet {M : OracleMachine spec α β}
    {oa : α → OracleComp spec β} {k : ℕ} (h : M ⊨[k] oa) :
    M.ImplementsDet oa k := by
  intro hd x
  have key := h.runK_eq (m := Id) hd.toQueryImpl x
  rw [runD, key]
  rfl

/-- For a stable machine, implementing a program at fuel `k` forces deterministic
steadiness at `k`: the `steady` field of a `PolyTimeAdversary` is *derivable* for any
implementing bundle — it keeps standalone bundles self-certifying but adds no strength
beyond the implements equation. -/
theorem Implements.steadyBy {M : OracleMachine spec α β} {oa : α → OracleComp spec β}
    {k : ℕ} (hst : M.StableOutput) (h : M ⊨[k] oa) (hd : OracleHandler spec)
    (x : α) : M.SteadyBy hd (M.init x) k := by
  rw [steadyBy_iff_isSome_runD hst, h.implementsDet hd x]
  rfl

/-- An implementing machine resolves along every randomized run: the early-stopping
probabilistic run puts no mass on an unresolved readout. Probabilistic steadiness is
thus a consequence of `Implements`, not an extra assumption. -/
theorem Implements.runK_none_eq_zero {M : OracleMachine spec α β}
    {oa : α → OracleComp spec β} {k : ℕ} (h : M ⊨[k] oa)
    (H : ProbHandler spec) (x : α) : M.runK H k (M.init x) none = 0 := by
  rw [h.runK_eq H x, map_eq_bind_pure_comp, SPMF.bind_apply_eq_tsum]
  refine ENNReal.tsum_eq_zero.mpr fun b => ?_
  rw [Function.comp_apply, (SPMF.pure_apply_eq_zero_iff _ _).mpr (by simp)]
  exact mul_zero _

/-! ## Simulation relations: the practical proof method for `Implements` -/

/-- A step-synchronized simulation between machine states and program residues: related
`pure` programs read out, related query programs are unresolved and ask the same query,
and updating along any answer stays related to the continuation. This is the practical
interface for proving `Implements` (`implements_of_isSimulation`).

Step synchronization (each machine round consumes exactly one program query, enforced
by `expose_eq`) restricts this *proof method*, not the `Implements` relation itself: a
machine taking internal bookkeeping rounds can still implement a program, but must be
handled either by restructuring its state so each round consumes a query, or by a
future stuttering variant (a relation with a per-query stutter budget, `expose_eq` and
`update_rel` required only at query-consuming steps, and fuel scaled accordingly in
`implements_of_isSimulation`). Every current machine construction is step-synchronized
by design, so the stuttering variant is deferred until a consumer needs it. -/
structure IsSimulation (R : M.State → OracleComp spec β → Prop) : Prop where
  /-- A state related to a halted program reads out its value. -/
  output_pure : ∀ ⦃s : M.State⦄ ⦃b : β⦄, R s (pure b) → M.output s = some b
  /-- A state related to a querying program is unresolved. -/
  output_queryBind : ∀ ⦃s : M.State⦄ ⦃t : spec.Domain⦄
    ⦃k : spec.Range t → OracleComp spec β⦄, R s (OracleComp.queryBind t k) →
      M.output s = none
  /-- A state related to a querying program exposes that query. -/
  expose_eq : ∀ ⦃s : M.State⦄ ⦃t : spec.Domain⦄
    ⦃k : spec.Range t → OracleComp spec β⦄, R s (OracleComp.queryBind t k) →
      M.expose s = t
  /-- Updating along any answer tracks the program continuation. -/
  update_rel : ∀ ⦃s : M.State⦄ ⦃t : spec.Domain⦄
    ⦃k : spec.Range t → OracleComp spec β⦄ (hR : R s (OracleComp.queryBind t k))
    (r : spec.Range (M.expose s)), R (M.update s r) (k (expose_eq hR ▸ r))

/-- Auxiliary induction for `implements_of_isSimulation`: at any fuel at least a total
query bound of the residual program, the run from any related state computes
`simulateQ` — in every lawful monad at once. Early stopping makes the `pure` case
fuel-independent. -/
theorem IsSimulation.runK_eq {M : OracleMachine spec α β}
    {R : M.State → OracleComp spec β → Prop} (hsim : M.IsSimulation R)
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    (H : QueryImpl spec m) (ob : OracleComp spec β) :
    ∀ (s : M.State) (n j : ℕ), R s ob → OracleComp.IsTotalQueryBound ob j → j ≤ n →
      M.runK H n s = some <$> simulateQ H ob := by
  induction ob with
  | pure b =>
    intro s n j hR _ _
    rw [M.runK_of_output_eq_some H (hsim.output_pure hR)]
    change (pure (some b) : m (Option β)) = some <$> simulateQ H (pure b)
    rw [simulateQ_pure, map_pure]
  | queryBind t k ih =>
    intro s n j hR hqb hjn
    obtain ⟨hj, hk⟩ := OracleComp.isTotalQueryBound_query_bind_iff.mp hqb
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have he := hsim.expose_eq hR
    subst he
    rw [M.runK_succ_of_output_eq_none H (hsim.output_queryBind hR),
      OracleComp.simulateQ_queryBind, map_bind]
    refine bind_congr fun r => ?_
    exact ih r (M.update s r) n (j - 1) (hsim.update_rel hR r) (hk r) (by omega)

/-- **Main proof method.** A machine implements a program at any fuel that totally
bounds the program's queries, given a simulation relation matching the initial states.
The bound supplies the fuel; the simulation supplies the step-by-step agreement, in
every lawful monad at once. -/
theorem implements_of_isSimulation {M : OracleMachine spec α β}
    {oa : α → OracleComp spec β} {k : ℕ} {R : M.State → OracleComp spec β → Prop}
    (hsim : M.IsSimulation R) (hinit : ∀ x, R (M.init x) (oa x))
    (hqb : ∀ x, OracleComp.IsTotalQueryBound (oa x) k) : M ⊨[k] oa := by
  intro x
  have key := hsim.runK_eq (QueryImpl.id' spec) (oa x) (M.init x) k k (hinit x) (hqb x) le_rfl
  rwa [show M.runK (QueryImpl.id' spec) k (M.init x) = M.toComp k (M.init x) from
    simulateQ_id' _, simulateQ_id'] at key

end OracleMachine

/-! ## Bridging between programs and machines

Query bounds on the inductive side and steadiness on the coinductive side are two
presentations of the same finiteness. A program family with a total query bound `k` is
a machine — its own residual program is the state — that is steady within `k` rounds
against every handler and implements the family (`OracleComp.toMachine`). Conversely a
machine unrolled for `k` rounds is a program with total query bound `k` — the PolyFun
unrolling `PointedMachine.toComp`, whose `simulateQ` semantics is *definitionally* the
machine's run (`simulateQ_toComp`). -/

namespace OracleComp

section ToMachine

/-- The readout of a program: its value at `pure`, nothing at a query. -/
def pureOutput (ob : OracleComp spec β) : Option β :=
  ob.casesOn some fun _ _ => none

@[simp] theorem pureOutput_pure (x : β) :
    pureOutput (pure x : OracleComp spec β) = some x := rfl

@[simp] theorem pureOutput_queryBind (t : spec.Domain)
    (k : spec.Range t → OracleComp spec β) : pureOutput (queryBind t k) = none := rfl

variable [Inhabited ι]

/-- The head query of a program; a default query at `pure`. -/
def headQuery (ob : OracleComp spec β) : ι :=
  ob.casesOn (fun _ => default) fun t _ => t

@[simp] theorem headQuery_pure (x : β) :
    headQuery (pure x : OracleComp spec β) = default := rfl

@[simp] theorem headQuery_queryBind (t : spec.Domain)
    (k : spec.Range t → OracleComp spec β) : headQuery (queryBind t k) = t := rfl

/-- Feed one answer to the head query of a program; a `pure` stays put. -/
def headUpdate : (ob : OracleComp spec β) → spec.Range (headQuery ob) → OracleComp spec β :=
  fun ob => ob.casesOn (motive := fun ob => spec.Range (headQuery ob) → OracleComp spec β)
    (fun x _ => pure x) fun _ k r => k r

@[simp] theorem headUpdate_pure (x : β)
    (r : spec.Range (headQuery (pure x : OracleComp spec β))) :
    headUpdate (pure x) r = pure x := rfl

@[simp] theorem headUpdate_queryBind (t : spec.Domain)
    (k : spec.Range t → OracleComp spec β) (r : spec.Range t) :
    headUpdate (queryBind t k) r = k r := rfl

/-- The readout survives one head update: it is only ever `some` at a `pure`, which
head updates fix. -/
theorem pureOutput_headUpdate_of_eq_some {ob : OracleComp spec β} {b : β}
    (hb : pureOutput ob = some b) (r : spec.Range (headQuery ob)) :
    pureOutput (headUpdate ob r) = some b := by
  cases ob with
  | pure x => exact hb
  | queryBind t k => simp at hb

/-- A program family as an oracle machine: the state is the residual program, one round
answers the head query. Steadiness of this machine is exactly a total query bound on
the family (`toMachine_steadyBy`), and it implements the family at any such bound
(`toMachine_implements`). -/
def toMachine (oa : α → OracleComp spec β) : OracleMachine spec α β where
  State := OracleComp spec β
  expose := headQuery
  update := headUpdate
  init := oa
  output := pureOutput

/-- One closed-loop step of the program-as-machine is `advance`. -/
theorem toMachine_advanceOnce (h : OracleHandler spec) (oa : α → OracleComp spec β) :
    OracleStrategy.advanceOnce h (toMachine oa).toDynSystem = advance h := by
  refine funext fun ob : OracleComp spec β => ?_
  cases ob with
  | pure x => rfl
  | queryBind t k => rfl

theorem toMachine_stableOutput (oa : α → OracleComp spec β) :
    OracleMachine.StableOutput (toMachine oa) :=
  fun _ _ hb r => pureOutput_headUpdate_of_eq_some hb r

/-- The program-as-machine is in step-synchronized simulation with the programs
themselves, via equality of states and residual programs. -/
theorem toMachine_isSimulation (oa : α → OracleComp spec β) :
    OracleMachine.IsSimulation (toMachine oa) Eq where
  output_pure := by rintro s b rfl; rfl
  output_queryBind := by rintro s t k rfl; rfl
  expose_eq := by rintro s t k rfl; rfl
  update_rel := by rintro s t k rfl r; rfl

open scoped OracleMachine in
/-- **Program-to-machine bridge (semantics).** A query-bounded program family is
implemented by its program-as-machine at the bound. -/
theorem toMachine_implements {oa : α → OracleComp spec β} {k : ℕ}
    (hqb : ∀ x, IsTotalQueryBound (oa x) k) : toMachine oa ⊨[k] oa :=
  OracleMachine.implements_of_isSimulation (toMachine_isSimulation oa) (fun _ => rfl) hqb

omit [Inhabited ι] in
/-- Iterating `advance` at or beyond `stepsToHalt` lands at the simulated value: `pure`
states are fixed points, so the run stabilizes. -/
theorem iterate_advance_eq_of_le (h : OracleHandler spec) {ob : OracleComp spec β}
    {n : ℕ} (hn : stepsToHalt h ob ≤ n) :
    (advance h)^[n] ob = pure (evalWithAnswerFn (QueryImpl.ofFn h) ob) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm, Function.iterate_add_apply, iterate_advance_eq_simulate,
    Function.iterate_fixed (advance_pure h _)]

/-- **Program-to-machine bridge (steadiness).** A total query bound on the program
makes the program-as-machine steady within that bound, against every handler. -/
theorem toMachine_steadyBy {oa : α → OracleComp spec β} (h : OracleHandler spec)
    (x : α) {k : ℕ} (hqb : IsTotalQueryBound (oa x) k) :
    OracleMachine.SteadyBy (toMachine oa) h ((toMachine oa).init x) k := by
  have key : OracleStrategy.stateAfter h (toMachine oa).toDynSystem (oa x) k =
      pure (evalWithAnswerFn (QueryImpl.ofFn h) (oa x)) := by
    change (OracleStrategy.advanceOnce h (toMachine oa).toDynSystem)^[k] (oa x) = _
    rw [toMachine_advanceOnce]
    exact iterate_advance_eq_of_le h (stepsToHalt_le_of_isTotalQueryBound h hqb)
  change (pureOutput (OracleStrategy.stateAfter h (toMachine oa).toDynSystem (oa x) k)).isSome
  exact key ▸ rfl

end ToMachine

end OracleComp

namespace OracleMachine

/-! ## The unrolling bridge, inherited from PolyFun

`M.toComp` is `PFunctor.PointedMachine.toComp`, which lands in
`FreeM spec.toPFunctor (Option β) = OracleComp spec (Option β)` on the nose. The `Option`
accounts for fuel exhaustion; under steadiness at `k` the result is always `some`. -/

section ToComp

variable (M : OracleMachine spec α β)

theorem toComp_succ_of_output_eq_some {s : M.State} {b : β} (hb : M.output s = some b)
    (k : ℕ) : M.toComp (k + 1) s = pure (some b) := by
  rw [PointedMachine.toComp_succ, hb]
  rfl

theorem toComp_succ_of_output_eq_none {s : M.State} (hb : M.output s = none) (k : ℕ) :
    M.toComp (k + 1) s =
      OracleComp.queryBind (M.expose s) fun r => M.toComp k (M.update s r) := by
  rw [PointedMachine.toComp_succ, hb]
  rfl

/-- A halted machine unrolls to its readout, at any fuel. -/
theorem toComp_of_output_eq_some {s : M.State} {b : β} (hb : M.output s = some b)
    (k : ℕ) : M.toComp k s = pure (some b) :=
  PointedMachine.toComp_of_output_eq_some M k hb

/-- **Machine-to-program bridge (query bounds).** The `k`-round unrolling makes at most
`k` queries: steadiness fuel is a total query bound. -/
theorem isTotalQueryBound_toComp (k : ℕ) (s : M.State) :
    OracleComp.IsTotalQueryBound (M.toComp k s) k := by
  induction k generalizing s with
  | zero => cases hb : M.output s <;> · rw [show M.toComp 0 s = pure (M.output s) from rfl]; trivial
  | succ k ih =>
    cases hb : M.output s with
    | some b => rw [M.toComp_succ_of_output_eq_some hb]; trivial
    | none =>
      rw [M.toComp_succ_of_output_eq_none hb]
      exact OracleComp.isTotalQueryBound_query_bind_iff.mpr
        ⟨Nat.succ_pos k, fun u => ih (M.update s u)⟩

/-- **Machine-to-program bridge (semantics).** Simulating the unrolled program is the
machine's run — *definitionally*: `simulateQ` is `FreeM.mapM` and `runK` is
`PointedMachine.runWith = FreeM.mapM ∘ toComp`. -/
theorem simulateQ_toComp {m : Type u → Type u} [Monad m] (H : QueryImpl spec m)
    (k : ℕ) (s : M.State) : simulateQ H (M.toComp k s) = M.runK H k s := rfl

/-- Deterministic form of `simulateQ_toComp`. -/
theorem evalWithAnswerFn_toComp (h : OracleHandler spec) (k : ℕ) (s : M.State) :
    evalWithAnswerFn (QueryImpl.ofFn h) (M.toComp k s) = M.runD h k s := by
  have key := M.simulateQ_toComp (ProbHandler.ofHandler h) k s
  rw [M.runK_ofHandler, OracleComp.simulateQ_ofHandler] at key
  refine Set.singleton_injective (α := Option β) ?_
  rw [← SPMF.support_pure, ← SPMF.support_pure, key]

end ToComp

end OracleMachine
