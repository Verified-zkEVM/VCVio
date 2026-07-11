/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.Machine
import ToMathlib.ProbabilityTheory.SPMFOrder
import VCVio.EvalDist.TVDist

/-!
# Limit Semantics for Oracle Machine Runs

The fuelled probabilistic run `OracleMachine.runK` observes a machine for at most `k`
adaptive queries. This file gives machines a fuel-free semantics: the *limit* of the
truncated runs along the fuel order.

* `OracleMachine.runKT`: the truncated run, with fuel exhaustion squashed into missing
  mass (`SPMF.joinOption` of `runK`). This is the presentation under which runs are
  monotone in fuel (`runKT_le_succ`) — `runK` itself is not monotone, because
  fuel-exhaustion mass sits on the *value* `none` and migrates onto resolved values as
  fuel grows.
* `OracleMachine.runLimit`: the least upper bound of the truncated runs, a genuine
  subprobability distribution by the ωCPO structure of
  `ToMathlib.ProbabilityTheory.SPMFOrder`. It satisfies the fixpoint equation
  `runLimit_fix`: read out if halted, otherwise take one sampled step and continue —
  the "run forever" semantics, with divergence recorded as missing mass.
* `OracleMachine.runK_eq_of_apply_none_eq_zero`: **fuel irrelevance** — once the
  fuelled run has no unresolved mass, adding fuel does not change it. (This is also
  the run-extension lemma that sequential machine composition and the
  run-factorization certificate consume; it lives here as its single home.)
* `OracleMachine.ASTerminates`: the limit run carries full mass — almost-sure
  resolution of the readout, against a lossless handler. The truncated missing masses
  converge to the limit's (`gap_runLimit`, `tendsto_gap_runKT`).
* `OracleMachine.ImplementsAE`: limit agreement with `simulateQ` against every
  randomized oracle. Fuelled `Implements` implies it (`Implements.implementsAE`); the
  converse needs probabilistic steadiness at some fuel, honestly stated as a
  hypothesis (`ImplementsAE.implements`).
* `OracleMachine.ImplementsWithin`: approximate implementation — the truncated run at
  fuel `k` is within `ε` of the program's semantics in extended total-variation
  distance. Since truncations sit *below* the limit pointwise, the distance is exactly
  a difference of missing masses (`SPMF.etvDist_eq_gap_sub_of_le`), so quantitative
  termination tails (e.g. the geometric tail of rejection sampling) bound it directly
  (`ImplementsAE.implementsWithin_of_gap_le`).

## Relation to the cofree construction (Spivak–Niu)

For polynomial-functor dynamical systems, Spivak–Niu §7.1.5 packages the length-`n`
behaviors of a system as the runs `Run_n`, and §8.1 assembles all finite runs into the
cofree comonoid `𝔱_p = lim (y ← p ← p^{◁2} ← ⋯)` — the limit of the finite-run
truncations. `runK H k` is the probabilistic shadow of the `k`-truncation against the
environment `H`, and `runLimit` is the shadow of the limit: the chain
`k ↦ runKT H k s` plays the role of the diagram and its `ωSup` the role of its limit.
The coalgebraic "run forever" object thus acquires an exact probability semantics
precisely when the truncations' missing mass converges to zero (`ASTerminates`); in
general the limit exists as a subprobability distribution.

Note this limit layer is a *semantic enrichment*, not a change to the resource-bounded
adversary class: `OracleComp.IsPolyTime` still demands a fuelled `Implements` witness,
so a machine that terminates almost surely but slowly is expressible here yet still
not polynomial-time. See `docs/agents/polytime-model.md`.
-/

universe u

open ENNReal OracleSpec OmegaCompletePartialOrder

namespace OracleMachine

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α β : Type u}
  (M : OracleMachine spec α β)

/-! ## The truncated run -/

/-- The fuelled probabilistic run with fuel exhaustion squashed into missing mass: an
unresolved readout after `k` sampled steps becomes `failure` rather than the value
`none`. Agrees with `SPMF.joinOption` of `runK` (`runKT_eq_joinOption_runK`), and is
monotone in the fuel (`runKT_le_succ`) — the presentation whose limit is
`runLimit`. -/
noncomputable def runKT (H : ProbHandler spec) : ℕ → M.State → SPMF β
  | 0, s => (M.output s).elim failure pure
  | k + 1, s => match M.output s with
    | some b => pure b
    | none => OracleStrategy.kleisliStep H M.toDynSystem s >>= runKT H k

@[simp] theorem runKT_zero (H : ProbHandler spec) (s : M.State) :
    M.runKT H 0 s = (M.output s).elim failure pure := rfl

theorem runKT_succ_of_output_eq_some (H : ProbHandler spec) {s : M.State} {b : β}
    (hb : M.output s = some b) (k : ℕ) : M.runKT H (k + 1) s = pure b := by
  simp [runKT, hb]

theorem runKT_succ_of_output_eq_none (H : ProbHandler spec) {s : M.State}
    (hb : M.output s = none) (k : ℕ) :
    M.runKT H (k + 1) s =
      OracleStrategy.kleisliStep H M.toDynSystem s >>= M.runKT H k := by
  simp [runKT, hb]

/-- A halted machine's truncated run is the Dirac mass on its readout, at any fuel. -/
theorem runKT_of_output_eq_some (H : ProbHandler spec) {s : M.State} {b : β}
    (hb : M.output s = some b) (k : ℕ) : M.runKT H k s = pure b := by
  cases k with
  | zero => rw [runKT_zero, hb]; rfl
  | succ k => exact M.runKT_succ_of_output_eq_some H hb k

/-- The truncated run is the fuelled run with fuel exhaustion merged into the failure
mass. -/
theorem runKT_eq_joinOption_runK (H : ProbHandler spec) (k : ℕ) (s : M.State) :
    M.runKT H k s = (M.runK H k s).joinOption := by
  induction k generalizing s with
  | zero => rw [runKT_zero, runK_zero, SPMF.joinOption_pure]
  | succ k ih =>
    cases hb : M.output s with
    | some b =>
      rw [M.runKT_succ_of_output_eq_some H hb, M.runK_succ_of_output_eq_some H hb,
        SPMF.joinOption_pure]
      rfl
    | none =>
      rw [M.runKT_succ_of_output_eq_none H hb, M.runK_succ_of_output_eq_none' H hb,
        SPMF.joinOption_bind]
      exact congrArg (fun f => OracleStrategy.kleisliStep H M.toDynSystem s >>= f)
        (funext fun s' => ih s')

/-- **Dirac bridge** for the truncated run: against a deterministic handler it is the
Dirac mass on the deterministic run's readout, with fuel exhaustion as failure. -/
@[simp] theorem runKT_ofHandler (h : OracleHandler spec) (k : ℕ) (s : M.State) :
    M.runKT (ProbHandler.ofHandler h) k s = (M.runD h k s).elim failure pure := by
  rw [runKT_eq_joinOption_runK, runK_ofHandler, SPMF.joinOption_pure]

/-! ## Fuel monotonicity and the limit run -/

/-- Truncated runs grow with fuel: mass only moves from missing to resolved. -/
theorem runKT_le_succ (H : ProbHandler spec) (k : ℕ) (s : M.State) :
    M.runKT H k s ≤ M.runKT H (k + 1) s := by
  induction k generalizing s with
  | zero =>
    cases hb : M.output s with
    | some b =>
      rw [runKT_zero, hb, M.runKT_succ_of_output_eq_some H hb]
      exact le_rfl
    | none =>
      rw [runKT_zero, hb]
      exact bot_le
  | succ k ih =>
    cases hb : M.output s with
    | some b =>
      rw [M.runKT_succ_of_output_eq_some H hb, M.runKT_succ_of_output_eq_some H hb]
    | none =>
      rw [M.runKT_succ_of_output_eq_none H hb, M.runKT_succ_of_output_eq_none H hb]
      exact SPMF.bind_le_bind le_rfl fun s' => ih s'

theorem runKT_monotone (H : ProbHandler spec) (s : M.State) :
    Monotone fun k => M.runKT H k s :=
  monotone_nat_of_le_succ fun k => M.runKT_le_succ H k s

/-- The fuel-indexed chain of truncated runs. -/
noncomputable def runChain (H : ProbHandler spec) (s : M.State) : Chain (SPMF β) :=
  ⟨fun k => M.runKT H k s, M.runKT_monotone H s⟩

@[simp] lemma runChain_apply (H : ProbHandler spec) (s : M.State) (k : ℕ) :
    M.runChain H s k = M.runKT H k s := rfl

/-- The limit run: the least upper bound of the truncated runs over all fuels. This is
the fuel-free "run forever" semantics of a machine against a randomized oracle, with
divergence (and handler loss) recorded as missing mass. -/
noncomputable def runLimit (H : ProbHandler spec) (s : M.State) : SPMF β :=
  ωSup (M.runChain H s)

lemma runLimit_apply (H : ProbHandler spec) (s : M.State) (b : β) :
    M.runLimit H s b = ⨆ k, M.runKT H k s b := rfl

theorem runKT_le_runLimit (H : ProbHandler spec) (k : ℕ) (s : M.State) :
    M.runKT H k s ≤ M.runLimit H s :=
  le_ωSup (M.runChain H s) k

/-! ## The fixpoint equation -/

/-- A halted machine's limit run is the Dirac mass on its readout. -/
theorem runLimit_of_output_eq_some (H : ProbHandler spec) {s : M.State} {b : β}
    (hb : M.output s = some b) : M.runLimit H s = pure b := by
  have h0 : M.runChain H s 0 = pure b := M.runKT_of_output_eq_some H hb 0
  refine (SPMF.ωSup_eq_of_eventually_const (c := M.runChain H s) (k := 0)
    fun m _ => ?_).trans h0
  show M.runKT H m s = M.runKT H 0 s
  rw [M.runKT_of_output_eq_some H hb m, M.runKT_of_output_eq_some H hb 0]

/-- An unresolved machine's limit run takes one sampled step and continues: the limit
absorbs the fuel recursion. -/
theorem runLimit_of_output_eq_none (H : ProbHandler spec) {s : M.State}
    (hb : M.output s = none) :
    M.runLimit H s = OracleStrategy.kleisliStep H M.toDynSystem s >>= M.runLimit H := by
  let C : Chain (SPMF β) :=
    ⟨fun k => OracleStrategy.kleisliStep H M.toDynSystem s >>= fun s' => M.runKT H k s',
      fun _ _ h => SPMF.bind_le_bind le_rfl fun s' => M.runKT_monotone H s' h⟩
  have hbind : OracleStrategy.kleisliStep H M.toDynSystem s >>= M.runLimit H = ωSup C :=
    SPMF.bind_ωSup _ fun s' => M.runChain H s'
  rw [hbind]
  refine le_antisymm (ωSup_le _ _ fun k => ?_) (ωSup_le _ _ fun k => ?_)
  · cases k with
    | zero =>
      have h0 : M.runKT H 0 s = failure := by rw [runKT_zero, hb]; rfl
      exact le_of_eq_of_le h0 bot_le
    | succ k =>
      exact le_of_eq_of_le (M.runKT_succ_of_output_eq_none H hb k) (le_ωSup C k)
  · exact le_of_eq_of_le (M.runKT_succ_of_output_eq_none H hb k).symm
      (M.runKT_le_runLimit H (k + 1) s)

/-- **The fixpoint equation**: the limit run reads out a halted state and otherwise
takes one sampled step and continues. This is the equation a direct coinductive or
least-fixpoint definition would impose; here it is a theorem about the chain
supremum. -/
theorem runLimit_fix (H : ProbHandler spec) (s : M.State) :
    M.runLimit H s = match M.output s with
      | some b => pure b
      | none => OracleStrategy.kleisliStep H M.toDynSystem s >>= M.runLimit H := by
  cases hb : M.output s with
  | some b => exact M.runLimit_of_output_eq_some H hb
  | none => exact M.runLimit_of_output_eq_none H hb

/-! ## Fuel irrelevance -/

/-- One more fuel step is irrelevant once the fuelled run has no unresolved mass. -/
theorem runK_succ_eq_of_apply_none_eq_zero (H : ProbHandler spec) :
    ∀ {k : ℕ} {s : M.State}, M.runK H k s none = 0 →
      M.runK H (k + 1) s = M.runK H k s := by
  intro k
  induction k with
  | zero =>
    intro s h
    rw [runK_zero] at h
    cases hb : M.output s with
    | some b => rw [M.runK_succ_of_output_eq_some H hb 0, runK_zero, hb]
    | none =>
      rw [hb] at h
      exact absurd rfl ((SPMF.pure_apply_eq_zero_iff _ _).mp h)
  | succ k ih =>
    intro s h
    cases hb : M.output s with
    | some b =>
      rw [M.runK_succ_of_output_eq_some H hb (k + 1),
        M.runK_succ_of_output_eq_some H hb k]
    | none =>
      rw [M.runK_succ_of_output_eq_none H hb k, SPMF.bind_apply_eq_tsum] at h
      rw [M.runK_succ_of_output_eq_none H hb (k + 1),
        M.runK_succ_of_output_eq_none H hb k]
      refine SPMF.bind_congr fun s' hs' => ih ?_
      rcases mul_eq_zero.mp (ENNReal.tsum_eq_zero.mp h s') with h1 | h2
      · exact absurd h1 hs'
      · exact h2

/-- **Fuel irrelevance**: once the fuelled run has no unresolved mass, adding fuel does
not change it. This is the run-extension lemma consumed by sequential machine
composition (the two-phase `bind` construction) and by the run-factorization
certificate work — cross-reference it rather than re-proving it there. -/
theorem runK_eq_of_apply_none_eq_zero (H : ProbHandler spec) {k : ℕ} {s : M.State}
    (h : M.runK H k s none = 0) {m : ℕ} (hm : k ≤ m) : M.runK H m s = M.runK H k s := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← Nat.add_assoc, M.runK_succ_eq_of_apply_none_eq_zero H (by rw [ih]; exact h), ih]

/-- **Steady agreement**: once the fuelled run has no unresolved mass, the limit run is
the truncated run — the chain is constant from that fuel on. -/
theorem runLimit_eq_runKT_of_apply_none_eq_zero (H : ProbHandler spec) {k : ℕ}
    {s : M.State} (h : M.runK H k s none = 0) : M.runLimit H s = M.runKT H k s := by
  refine SPMF.ωSup_eq_of_eventually_const (c := M.runChain H s) (k := k) fun m hm => ?_
  show M.runKT H m s = M.runKT H k s
  rw [runKT_eq_joinOption_runK, runKT_eq_joinOption_runK,
    M.runK_eq_of_apply_none_eq_zero H h hm]

/-! ## Almost-sure termination -/

/-- The missing mass of the truncated run shrinks as fuel grows. -/
theorem gap_runKT_antitone (H : ProbHandler spec) (s : M.State) :
    Antitone fun k => (M.runKT H k s).gap :=
  fun _ _ h => SPMF.gap_antitone (M.runKT_monotone H s h)

/-- The limit run's missing mass is the infimum of the truncated runs'. -/
theorem gap_runLimit (H : ProbHandler spec) (s : M.State) :
    (M.runLimit H s).gap = ⨅ k, (M.runKT H k s).gap :=
  SPMF.gap_ωSup (M.runChain H s)

/-- The truncated runs' missing masses converge to the limit run's. -/
theorem tendsto_gap_runKT (H : ProbHandler spec) (s : M.State) :
    Filter.Tendsto (fun k => (M.runKT H k s).gap) Filter.atTop
      (nhds (M.runLimit H s).gap) := by
  rw [M.gap_runLimit H s]
  exact tendsto_atTop_iInf (M.gap_runKT_antitone H s)

/-- Almost-sure termination of a machine from a state against a handler: the limit run
carries full mass. Since the handler's own losses also land in the missing mass, this
additionally requires the handler to lose nothing along the run; against a lossless
handler it is exactly almost-sure resolution of the readout. -/
def ASTerminates (H : ProbHandler spec) (s : M.State) : Prop :=
  (M.runLimit H s).gap = 0

theorem asTerminates_iff_iInf_gap (H : ProbHandler spec) (s : M.State) :
    M.ASTerminates H s ↔ (⨅ k, (M.runKT H k s).gap) = 0 := by
  rw [ASTerminates, gap_runLimit]

/-! ## Limit and approximate implements relations -/

/-- A machine implements a program *in the limit*: the limit run agrees with
`simulateQ` against every randomized oracle. No `some <$>` lift appears (compare
`Implements`): the squash into missing mass already absorbed the resolution layer. -/
def ImplementsAE (oa : α → OracleComp spec β) : Prop :=
  ∀ (H : ProbHandler spec) (x : α), M.runLimit H (M.init x) = simulateQ H (oa x)

/-- Fuelled implementation implies limit implementation: an implementing run has no
unresolved mass, so the chain is already constant at its fuel. -/
theorem Implements.implementsAE {M : OracleMachine spec α β}
    {oa : α → OracleComp spec β} {k : ℕ} (h : M.Implements oa k) :
    M.ImplementsAE oa := fun H x => by
  rw [M.runLimit_eq_runKT_of_apply_none_eq_zero H (h.runK_none_eq_zero H x),
    runKT_eq_joinOption_runK, h H x, SPMF.joinOption_map_some]

/-- Limit implementation plus probabilistic steadiness at fuel `k` (no unresolved mass
against any handler) recovers the fuelled run equation against every randomized oracle —
the `m := SPMF` face of `Implements`. The steadiness hypothesis is essential:
`ImplementsAE` alone says nothing about *when* the machine resolves. Note the full
monad-parametric `Implements` is *not* recoverable from limit data: `ImplementsAE` is
an SPMF-level hypothesis, and nothing in it constrains the run in other monads
(recovering it would need the machine-vs-program correspondence at the level of
transition structure, not distribution semantics). -/
theorem ImplementsAE.runK_eq {M : OracleMachine spec α β}
    {oa : α → OracleComp spec β} (h : M.ImplementsAE oa) {k : ℕ}
    (hk : ∀ (H : ProbHandler spec) (x : α), M.runK H k (M.init x) none = 0)
    (H : ProbHandler spec) (x : α) :
    M.runK H k (M.init x) = some <$> simulateQ H (oa x) := by
  rw [SPMF.eq_map_some_of_apply_none_eq_zero (hk H x)]
  refine congrArg (fun p => some <$> p) ?_
  rw [← runKT_eq_joinOption_runK, ← M.runLimit_eq_runKT_of_apply_none_eq_zero H (hk H x)]
  exact h H x

/-- Approximate implementation: at fuel `k` the truncated run is within `ε` of the
program's semantics in extended total-variation distance, against every randomized
oracle. This is the resource-honest relation for machines that only terminate almost
surely: a strict fuel budget plus an explicit statistical-distance budget. -/
def ImplementsWithin (oa : α → OracleComp spec β) (k : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ (H : ProbHandler spec) (x : α),
    (M.runKT H k (M.init x)).etvDist (simulateQ H (oa x)) ≤ ε

theorem ImplementsWithin.mono {M : OracleMachine spec α β}
    {oa : α → OracleComp spec β} {k : ℕ} {ε ε' : ℝ≥0∞}
    (h : M.ImplementsWithin oa k ε) (hε : ε ≤ ε') : M.ImplementsWithin oa k ε' :=
  fun H x => (h H x).trans hε

/-- Exact fuelled implementation is approximate implementation with budget zero. -/
theorem Implements.implementsWithin {M : OracleMachine spec α β}
    {oa : α → OracleComp spec β} {k : ℕ} (h : M.Implements oa k) :
    M.ImplementsWithin oa k 0 := fun H x => by
  rw [runKT_eq_joinOption_runK, h H x, SPMF.joinOption_map_some]
  exact le_of_eq (SPMF.etvDist_self _)

/-- For a limit-implementing machine, the truncated run sits below the program's
semantics pointwise, so its distance is exactly the difference of missing masses;
bounding that difference bounds the distance. -/
theorem ImplementsAE.implementsWithin {M : OracleMachine spec α β}
    {oa : α → OracleComp spec β} (h : M.ImplementsAE oa) {k : ℕ} {ε : ℝ≥0∞}
    (hgap : ∀ (H : ProbHandler spec) (x : α),
      (M.runKT H k (M.init x)).gap - (simulateQ H (oa x)).gap ≤ ε) :
    M.ImplementsWithin oa k ε := fun H x => by
  have hle : M.runKT H k (M.init x) ≤ simulateQ H (oa x) :=
    h H x ▸ M.runKT_le_runLimit H k (M.init x)
  rw [SPMF.etvDist_eq_gap_sub_of_le hle]
  exact hgap H x

/-- The form quantitative termination tails produce: for a limit-implementing machine,
a bound on the truncated run's missing mass alone bounds the distance to the program's
semantics (e.g. the geometric tail `2⁻⁽ᵏ⁺¹⁾` of truncated rejection sampling). -/
theorem ImplementsAE.implementsWithin_of_gap_le {M : OracleMachine spec α β}
    {oa : α → OracleComp spec β} (h : M.ImplementsAE oa) {k : ℕ} {ε : ℝ≥0∞}
    (hgap : ∀ (H : ProbHandler spec) (x : α), (M.runKT H k (M.init x)).gap ≤ ε) :
    M.ImplementsWithin oa k ε :=
  h.implementsWithin fun H x => le_trans tsub_le_self (hgap H x)

end OracleMachine
