/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.DynSystem
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Oracle Machines: Strategies with Initialization and Readout

An `OracleMachine spec α β` is an `OracleStrategy` together with an initial-state map
`init : α → State` and a Moore-style partial readout `output : State → Option β`:
`output s = some b` means the machine has halted with result `b`, while `none` means it
queries on. This is the machine-shaped presentation of an adversary
`α → OracleComp spec β`; since the machine is given by a state type and pure step
functions, it is the shape on which computational-cost notions (such as Turing-machine
polynomial time, in `VCVio.OracleComp.Coinductive.PolyTime`) can be imposed.

Key definitions:

* `OracleMachine.runD` / `OracleMachine.runK`: fuelled deterministic / probabilistic
  runs that stop early at the first `some` readout. Early stopping is essential on the
  probabilistic side: continuing to sample after halting would multiply by the remaining
  handler mass, losing sub-probability mass against lossy handlers.
* `OracleMachine.Implements M oa k`: the run of `M` at fuel `k` agrees with `simulateQ`
  of `oa` against every randomized oracle (`ProbHandler`). Quantifying over
  deterministic handlers only would not pin down semantics — a handler answers repeated
  queries to the same index identically, so e.g. two coin flips and one duplicated coin
  flip agree against every `OracleHandler` while their distributions differ. The
  deterministic form `ImplementsDet` follows via the Dirac bridge
  (`Implements.implementsDet`).
* `OracleMachine.IsSimulation`: a step-synchronized simulation relation between machine
  states and program residues; `implements_of_isSimulation` is the practical method for
  establishing `Implements`, with the fuel supplied by a total query bound.
* `OracleStrategy.ReachableIn`: states reachable under *some* answer sequence — strictly
  stronger quantification than reachability along handler runs, which repeat answers
  (`reachableIn_stateAfter`).
-/

universe u v w

open OracleSpec

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α β : Type u}

namespace OracleStrategy

/-! ## Reachability under arbitrary answer sequences -/

/-- `ReachableIn A n s s'`: the state `s'` is reachable from `s` in exactly `n` steps of
the strategy `A` under *some* (possibly time-varying) sequence of oracle answers. This
quantification is strictly stronger than reachability along every handler run
(`reachableIn_stateAfter`): a deterministic handler answers repeated queries to the same
index identically, while `ReachableIn` ranges over all answer paths. -/
inductive ReachableIn (A : OracleStrategy spec) : ℕ → A.State → A.State → Prop
  | refl (s : A.State) : ReachableIn A 0 s s
  | step {n : ℕ} {s s' : A.State} (r : spec.Range (A.expose s)) :
      ReachableIn A n (A.update s r) s' → ReachableIn A (n + 1) s s'

/-- Every state along a handler-answered run is reachable under some answer sequence. -/
theorem reachableIn_stateAfter (h : OracleHandler spec) (A : OracleStrategy spec)
    (s : A.State) (n : ℕ) : A.ReachableIn n s (stateAfter h A s n) := by
  induction n generalizing s with
  | zero => exact .refl s
  | succ n ih => exact stateAfter_succ h A s n ▸ .step _ (ih (advanceOnce h A s))

end OracleStrategy

/-! ## Oracle machines -/

/-- An oracle machine: an adaptive querying strategy (`OracleStrategy`, extended as the
`toStrategy` parent) together with an initialization of its state from an input and a
Moore-style partial readout of its result. `output s = some b` means the machine has
halted with result `b`; `output s = none` means it queries on. Since a machine is a
state type with pure Lean step functions, it is the presentation of an adversary on
which per-step computational cost can be imposed. -/
structure OracleMachine {ι : Type u} (spec : OracleSpec.{u, u} ι) (α β : Type u)
    extends toStrategy : OracleStrategy.{u, u, u} spec where
  /-- The machine's initial state on a given input. -/
  init : α → toStrategy.State
  /-- The partial readout: `some b` once the machine has halted with result `b`. -/
  output : toStrategy.State → Option β

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
    M.output (OracleStrategy.stateAfter h M.toStrategy s k) = some b := by
  induction k generalizing s with
  | zero => exact hb
  | succ k ih => exact OracleStrategy.stateAfter_succ h M.toStrategy s k ▸ ih (hst hb _)

/-- Steadiness against a handler: after `k` answered steps from `s`, the readout has
resolved. -/
def SteadyBy (h : OracleHandler spec) (s : M.State) (k : ℕ) : Prop :=
  (M.output (OracleStrategy.stateAfter h M.toStrategy s k)).isSome

/-! ## Early-stopping runs -/

/-- The fuelled deterministic run of a machine against a handler, stopping early at the
first `some` readout. Early stopping matches the probabilistic run `runK`, where it is
essential; for stable machines the plain readout after `k` steps agrees
(`runD_eq_output_stateAfter`). -/
def runD (h : OracleHandler spec) : ℕ → M.State → Option β
  | 0, s => M.output s
  | k + 1, s => match M.output s with
    | some b => some b
    | none => runD h k (OracleStrategy.advanceOnce h M.toStrategy s)

@[simp] theorem runD_zero (h : OracleHandler spec) (s : M.State) :
    M.runD h 0 s = M.output s := rfl

theorem runD_succ_of_output_eq_some (h : OracleHandler spec) {s : M.State} {b : β}
    (hb : M.output s = some b) (k : ℕ) : M.runD h (k + 1) s = some b := by
  simp [runD, hb]

theorem runD_succ_of_output_eq_none (h : OracleHandler spec) {s : M.State}
    (hb : M.output s = none) (k : ℕ) :
    M.runD h (k + 1) s = M.runD h k (OracleStrategy.advanceOnce h M.toStrategy s) := by
  simp [runD, hb]

/-- A halted machine's run is its readout, at any fuel. -/
theorem runD_of_output_eq_some (h : OracleHandler spec) {s : M.State} {b : β}
    (hb : M.output s = some b) (k : ℕ) : M.runD h k s = some b := by
  cases k with
  | zero => exact hb
  | succ k => exact M.runD_succ_of_output_eq_some h hb k

/-- For a stable machine, the early-stopping run is the plain readout after `k` steps. -/
theorem runD_eq_output_stateAfter {M : OracleMachine spec α β} (hst : M.StableOutput)
    (h : OracleHandler spec) (k : ℕ) (s : M.State) :
    M.runD h k s = M.output (OracleStrategy.stateAfter h M.toStrategy s k) := by
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

/-- The fuelled probabilistic run of a machine against a randomized oracle: check the
readout, and only sample the next answer while it is unresolved. The result is the
sub-distribution over readouts after at most `k` adaptive queries; halted states are
absorbing. -/
noncomputable def runK (H : ProbHandler spec) : ℕ → M.State → SPMF (Option β)
  | 0, s => pure (M.output s)
  | k + 1, s => match M.output s with
    | some b => pure (some b)
    | none => OracleStrategy.kleisliStep H M.toStrategy s >>= runK H k

@[simp] theorem runK_zero (H : ProbHandler spec) (s : M.State) :
    M.runK H 0 s = pure (M.output s) := rfl

theorem runK_succ_of_output_eq_some (H : ProbHandler spec) {s : M.State} {b : β}
    (hb : M.output s = some b) (k : ℕ) : M.runK H (k + 1) s = pure (some b) := by
  simp [runK, hb]

theorem runK_succ_of_output_eq_none (H : ProbHandler spec) {s : M.State}
    (hb : M.output s = none) (k : ℕ) :
    M.runK H (k + 1) s = OracleStrategy.kleisliStep H M.toStrategy s >>= M.runK H k := by
  simp [runK, hb]

/-- A halted machine's probabilistic run is the Dirac mass on its readout, at any
fuel. -/
theorem runK_of_output_eq_some (H : ProbHandler spec) {s : M.State} {b : β}
    (hb : M.output s = some b) (k : ℕ) : M.runK H k s = pure (some b) := by
  cases k with
  | zero => rw [runK_zero, hb]
  | succ k => exact M.runK_succ_of_output_eq_some H hb k

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
      rw [M.runK_succ_of_output_eq_none _ hb, OracleStrategy.kleisliStep_ofHandler,
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

/-- A machine implements a program at fuel `k` when its probabilistic run agrees with
`simulateQ` of the program against every randomized oracle. Randomized oracles sample
each query independently, so this pins down the program's full distribution semantics
(deterministic handlers alone would not — they answer repeated queries identically). -/
def Implements (oa : α → OracleComp spec β) (k : ℕ) : Prop :=
  ∀ (H : ProbHandler spec) (x : α),
    M.runK H k (M.init x) = some <$> simulateQ H (oa x)

/-- The deterministic form of the implements relation: the early-stopping run against
every deterministic handler computes `evalWithAnswerFn`. Weaker than `Implements`; see
`Implements.implementsDet`. -/
def ImplementsDet (oa : α → OracleComp spec β) (k : ℕ) : Prop :=
  ∀ (h : OracleHandler spec) (x : α),
    M.runD h k (M.init x) = some (evalWithAnswerFn (QueryImpl.ofFn h) (oa x))

/-- Probabilistic agreement specializes to deterministic agreement along the Dirac
bridge. -/
theorem Implements.implementsDet {M : OracleMachine spec α β}
    {oa : α → OracleComp spec β} {k : ℕ} (h : M.Implements oa k) :
    M.ImplementsDet oa k := by
  intro hd x
  have key := h (ProbHandler.ofHandler hd) x
  rw [runK_ofHandler, OracleComp.simulateQ_ofHandler, map_pure] at key
  exact SPMF.pure_injective key

/-- For a stable machine, implementing a program at fuel `k` forces deterministic
steadiness at `k`: the `steady` field of a `PolyTimeAdversary` is *derivable* for any
implementing bundle — it keeps standalone bundles self-certifying but adds no strength
beyond the implements equation. -/
theorem Implements.steadyBy {M : OracleMachine spec α β} {oa : α → OracleComp spec β}
    {k : ℕ} (hst : M.StableOutput) (h : M.Implements oa k) (hd : OracleHandler spec)
    (x : α) : M.SteadyBy hd (M.init x) k := by
  rw [steadyBy_iff_isSome_runD hst, h.implementsDet hd x]
  rfl

/-- An implementing machine resolves along every randomized run: the early-stopping
probabilistic run puts no mass on an unresolved readout. Probabilistic steadiness is
thus a consequence of `Implements`, not an extra assumption — the deterministic
quantification of the `steady` field loses nothing. -/
theorem Implements.runK_none_eq_zero {M : OracleMachine spec α β}
    {oa : α → OracleComp spec β} {k : ℕ} (h : M.Implements oa k)
    (H : ProbHandler spec) (x : α) : M.runK H k (M.init x) none = 0 := by
  rw [h H x, map_eq_bind_pure_comp, SPMF.bind_apply_eq_tsum]
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
`simulateQ`. Early stopping makes the `pure` case fuel-independent. -/
theorem IsSimulation.runK_eq {M : OracleMachine spec α β}
    {R : M.State → OracleComp spec β → Prop} (hsim : M.IsSimulation R)
    (H : ProbHandler spec) (ob : OracleComp spec β) :
    ∀ (s : M.State) (m j : ℕ), R s ob → OracleComp.IsTotalQueryBound ob j → j ≤ m →
      M.runK H m s = some <$> simulateQ H ob := by
  induction ob with
  | pure b =>
    intro s m j hR _ _
    rw [M.runK_of_output_eq_some H (hsim.output_pure hR)]
    change (pure (some b) : SPMF (Option β)) = some <$> simulateQ H (pure b)
    rw [simulateQ_pure, map_pure]
  | queryBind t k ih =>
    intro s m j hR hqb hjm
    obtain ⟨hj, hk⟩ := OracleComp.isTotalQueryBound_query_bind_iff.mp hqb
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have he := hsim.expose_eq hR
    subst he
    rw [M.runK_succ_of_output_eq_none H (hsim.output_queryBind hR),
      OracleComp.simulateQ_queryBind, OracleStrategy.kleisliStep, map_bind,
      bind_map_left]
    refine bind_congr fun r => ?_
    exact ih r (M.update s r) m (j - 1) (hsim.update_rel hR r) (hk r) (by omega)

/-- **Main proof method.** A machine implements a program at any fuel that totally
bounds the program's queries, given a simulation relation matching the initial states.
The bound supplies the fuel; the simulation supplies the step-by-step agreement. -/
theorem implements_of_isSimulation {M : OracleMachine spec α β}
    {oa : α → OracleComp spec β} {k : ℕ} {R : M.State → OracleComp spec β → Prop}
    (hsim : M.IsSimulation R) (hinit : ∀ x, R (M.init x) (oa x))
    (hqb : ∀ x, OracleComp.IsTotalQueryBound (oa x) k) : M.Implements oa k :=
  fun H x => hsim.runK_eq H (oa x) (M.init x) k k (hinit x) (hqb x) le_rfl

end OracleMachine

/-! ## Bridging between programs and machines

Query bounds on the inductive side and steadiness on the coinductive side are two
presentations of the same finiteness. A program family with a total query bound `k` is
a machine — its own residual program is the state — that is steady within `k` rounds
against every handler and implements the family (`OracleComp.toMachine`). Conversely a
machine unrolled for `k` rounds is a program with total query bound `k` whose
`simulateQ` semantics is exactly the machine's run (`OracleMachine.toComp`). -/

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
    OracleStrategy.advanceOnce h (toMachine oa).toStrategy = advance h := by
  refine funext fun ob : OracleComp spec β => ?_
  cases ob with
  | pure x => rfl
  | queryBind t k => rfl

theorem toMachine_stableOutput (oa : α → OracleComp spec β) :
    (toMachine oa).StableOutput :=
  fun _ _ hb r => pureOutput_headUpdate_of_eq_some hb r

/-- The program-as-machine is in step-synchronized simulation with the programs
themselves, via equality of states and residual programs. -/
theorem toMachine_isSimulation (oa : α → OracleComp spec β) :
    (toMachine oa).IsSimulation Eq where
  output_pure := by rintro s b rfl; rfl
  output_queryBind := by rintro s t k rfl; rfl
  expose_eq := by rintro s t k rfl; rfl
  update_rel := by rintro s t k rfl r; rfl

/-- **Program-to-machine bridge (semantics).** A query-bounded program family is
implemented by its program-as-machine at the bound. -/
theorem toMachine_implements {oa : α → OracleComp spec β} {k : ℕ}
    (hqb : ∀ x, IsTotalQueryBound (oa x) k) : (toMachine oa).Implements oa k :=
  OracleMachine.implements_of_isSimulation (toMachine_isSimulation oa) (fun _ => rfl) hqb

omit [Inhabited ι] in
/-- Iterating `advance` at or beyond `stepsToHalt` lands at the simulated value: `pure`
states are fixed points, so the run stabilizes. -/
theorem iterate_advance_eq_of_le (h : OracleHandler spec) {ob : OracleComp spec β}
    {m : ℕ} (hm : stepsToHalt h ob ≤ m) :
    (advance h)^[m] ob = pure (evalWithAnswerFn (QueryImpl.ofFn h) ob) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm, Function.iterate_add_apply, iterate_advance_eq_simulate,
    Function.iterate_fixed (advance_pure h _)]

/-- **Program-to-machine bridge (steadiness).** A total query bound on the program
makes the program-as-machine steady within that bound, against every handler. -/
theorem toMachine_steadyBy {oa : α → OracleComp spec β} (h : OracleHandler spec)
    (x : α) {k : ℕ} (hqb : IsTotalQueryBound (oa x) k) :
    (toMachine oa).SteadyBy h ((toMachine oa).init x) k := by
  have key : OracleStrategy.stateAfter h (toMachine oa).toStrategy (oa x) k =
      pure (evalWithAnswerFn (QueryImpl.ofFn h) (oa x)) := by
    change (OracleStrategy.advanceOnce h (toMachine oa).toStrategy)^[k] (oa x) = _
    rw [toMachine_advanceOnce]
    exact iterate_advance_eq_of_le h (stepsToHalt_le_of_isTotalQueryBound h hqb)
  change (pureOutput (OracleStrategy.stateAfter h (toMachine oa).toStrategy (oa x) k)).isSome
  rw [key]
  rfl

end ToMachine

end OracleComp

namespace OracleMachine

section ToComp

variable (M : OracleMachine spec α β)

/-- Unroll a machine for `k` rounds into a program: read out if resolved, otherwise ask
the exposed query and continue on the updated state. The `Option` accounts for fuel
exhaustion; under steadiness at `k` the result is always `some`. -/
def toComp : ℕ → M.State → OracleComp spec (Option β)
  | 0, s => pure (M.output s)
  | k + 1, s => match M.output s with
    | some b => pure (some b)
    | none => OracleComp.queryBind (M.expose s) fun r => toComp k (M.update s r)

@[simp] theorem toComp_zero (s : M.State) : M.toComp 0 s = pure (M.output s) := rfl

theorem toComp_succ_of_output_eq_some {s : M.State} {b : β} (hb : M.output s = some b)
    (k : ℕ) : M.toComp (k + 1) s = pure (some b) := by
  simp [toComp, hb]

theorem toComp_succ_of_output_eq_none {s : M.State} (hb : M.output s = none) (k : ℕ) :
    M.toComp (k + 1) s =
      OracleComp.queryBind (M.expose s) fun r => M.toComp k (M.update s r) := by
  simp only [toComp, hb]
  rfl

/-- **Machine-to-program bridge (query bounds).** The `k`-round unrolling makes at most
`k` queries: steadiness fuel is a total query bound. -/
theorem isTotalQueryBound_toComp (k : ℕ) (s : M.State) :
    OracleComp.IsTotalQueryBound (M.toComp k s) k := by
  induction k generalizing s with
  | zero => trivial
  | succ k ih =>
    cases hb : M.output s with
    | some b => rw [M.toComp_succ_of_output_eq_some hb]; trivial
    | none =>
      rw [M.toComp_succ_of_output_eq_none hb]
      exact OracleComp.isTotalQueryBound_query_bind_iff.mpr
        ⟨Nat.succ_pos k, fun u => ih (M.update s u)⟩

/-- **Machine-to-program bridge (semantics).** Simulating the unrolled program is
exactly the machine's probabilistic run. -/
theorem simulateQ_toComp (H : ProbHandler spec) (k : ℕ) (s : M.State) :
    simulateQ H (M.toComp k s) = M.runK H k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    cases hb : M.output s with
    | some b =>
      rw [M.toComp_succ_of_output_eq_some hb, M.runK_succ_of_output_eq_some H hb]
      rfl
    | none =>
      rw [M.toComp_succ_of_output_eq_none hb, M.runK_succ_of_output_eq_none H hb]
      refine Eq.trans (OracleComp.simulateQ_queryBind H (M.expose s)
        (fun r => M.toComp k (M.update s r))) ?_
      rw [OracleStrategy.kleisliStep, bind_map_left]
      exact bind_congr fun r => ih (M.update s r)

/-- Deterministic form of `simulateQ_toComp`, via the Dirac bridge. -/
theorem evalWithAnswerFn_toComp (h : OracleHandler spec) (k : ℕ) (s : M.State) :
    evalWithAnswerFn (QueryImpl.ofFn h) (M.toComp k s) = M.runD h k s := by
  have key := M.simulateQ_toComp (ProbHandler.ofHandler h) k s
  rw [M.runK_ofHandler, OracleComp.simulateQ_ofHandler] at key
  exact SPMF.pure_injective key

end ToComp

end OracleMachine
