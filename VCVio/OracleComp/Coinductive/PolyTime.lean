/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.Machine
import ToMathlib.Computability.CslibPolyTime

/-!
# Turing-Machine-Grounded Polynomial-Time Adversaries

A `PolyTimeAdversary spec α β` is a family of oracle machines (`OracleMachine`),
indexed by a security parameter, whose step functions are each Turing-machine
computable in polynomial time (via `Computability.EncPolyTime`, grounded in Cslib's
single-tape machines) and whose readout resolves within polynomially many oracle
rounds. Defining polynomial time on machines rather than on `OracleComp` programs
directly is what makes a Turing-machine grounding possible: a machine is a state type
with four plain Lean functions (`init`, `expose`, `update`, `output`), each of which
can be computed by a concrete machine on encoded states, whereas the continuations of
a program tree have no bounded syntactic presentation.

`OracleComp.IsPolyTime oa` then holds when *some* polynomial-time adversary implements
the program family `oa`, in the sense of `OracleMachine.Implements`; it is the intended
instantiation of the `isPPT` predicate of `SecurityGame.secureAgainst`.

Design notes, deliberate and worth restating:

* **Non-uniform**: there is one machine per security parameter `n` (with uniform
  polynomial bounds across the family), the standard non-uniform adversary model.
  A uniform variant — a single machine reading `n` as part of its input — is a
  possible future refinement.
* **Bounds are functions of `n` alone**, matching `PolyQueries`: adversaries whose
  resource use must grow with an unbounded input cannot be certified; an
  input-size-aware variant (bounds in `n + |input|`) is a possible refinement.
* **The encoded-state-size invariant `encState_length_le` is an explicit field, not
  derivable**: a machine can double its state on every step while remaining per-step
  polynomial-time in its current state length, so per-step time witnesses plus a
  polynomial round count alone would admit exponentially growing states (and hence
  super-polynomial total time). The invariant is exactly what makes the total-time
  bound `detTotalTime_le` sound.
* The total query bound demanded by `OracleComp.IsPolyTime` is in principle
  extractable from the `Implements` equation (by driving the program along handlers
  concentrated on deep paths), but that extraction is genuinely involved; it is kept
  as an explicit conjunct, which also feeds the `PolyQueries` bridge directly.
-/

universe u v w

open OracleSpec Computability

variable {ι : Type} [DecidableEq ι]

/-! ## Encoding the oracle interface -/

/-- Turing-machine-facing encodability of an oracle interface: finite-alphabet
encodings of the query indices and of the typed query/answer pairs. The answer
component encodes the dependent pair `⟨t, r⟩` so that a machine can consume answers of
varying type through one alphabet; build it from per-index range encodings over a
shared alphabet with `InterfaceEncoding.ofRangeEncodings`. -/
structure OracleSpec.InterfaceEncoding (spec : OracleSpec.{0, 0} ι) where
  /-- An encoding of the query index type. -/
  encQuery : FinEncoding ι
  /-- An encoding of typed query/answer pairs. -/
  encAns : FinEncoding ((t : ι) × spec.Range t)

/-- Build an `InterfaceEncoding` from an index encoding and per-index range encodings
over a shared alphabet, via `Computability.finEncodingSigma`. -/
def OracleSpec.InterfaceEncoding.ofRangeEncodings {spec : OracleSpec.{0, 0} ι}
    (ei : FinEncoding ι) {Γ : Type} [Fintype Γ]
    (enc : (t : ι) → spec.Range t → List Γ)
    (dec : (t : ι) → List Γ → Option (spec.Range t))
    (henc : ∀ t x, dec t (enc t x) = some x) : spec.InterfaceEncoding :=
  ⟨ei, finEncodingSigma ei enc dec henc⟩

/-- The canonical `InterfaceEncoding` of an oracle interface with enumerable finite
index and answer types, via `Computability.finEncodingOfFinEnum`. Covers the common
concrete specs (e.g. `coinSpec`) with no encoding work. -/
def OracleSpec.InterfaceEncoding.ofFinEnum (spec : OracleSpec.{0, 0} ι) [FinEnum ι]
    [∀ t, FinEnum (spec.Range t)] : spec.InterfaceEncoding :=
  ⟨finEncodingOfFinEnum ι, finEncodingOfFinEnum ((t : ι) × spec.Range t)⟩

/-! ## Flattening the dependent update -/

namespace OracleMachine

variable {spec : OracleSpec.{0, 0} ι} {α β : Type}

/-- The machine's dependent update flattened to a total function on tagged
query/answer pairs, as a Turing machine must consume it: answers tagged with the
currently exposed query update the state, mismatched tags act as the identity. -/
def updateFlat (M : OracleMachine spec α β) :
    M.State × ((t : ι) × spec.Range t) → M.State := fun p =>
  letI : DecidableEq spec.toPFunctor.A := ‹DecidableEq ι›
  if h : M.expose p.1 = p.2.1 then M.update p.1 (h ▸ p.2.2) else p.1

@[simp] theorem updateFlat_expose (M : OracleMachine spec α β) (s : M.State)
    (r : spec.Range (M.expose s)) : M.updateFlat (s, ⟨M.expose s, r⟩) = M.update s r := by
  simp [updateFlat]

end OracleMachine

/-! ## Polynomial-time adversaries -/

/-- A Turing-machine-grounded polynomial-time adversary: a family of oracle machines
indexed by the security parameter, together with

* a polynomial round bound `steps` within which the readout resolves against every
  handler (`steady`), stably (`stable`);
* `Bool`-string encodings of states, inputs, outputs, and the oracle interface;
* a polynomial invariant `sizeBound` on encoded state length along every run (an
  explicit field — per-step polynomial time alone admits exponential state growth);
* per-step machine witnesses (`initTM`, `exposeTM`, `updateTM`, `outputTM`) that each
  step function is polynomial-time computable on encodings, with a single polynomial
  `stepTime` bounding all of their running times uniformly in `n`.

The witnesses are data (they carry concrete machines); the Prop-level predicate on
program families is `OracleComp.IsPolyTime`. No composition of machines is involved:
polynomial time is the conjunction of per-step witnesses, the round bound, and the
state-size invariant, exactly the clocked-machine reading of "PPT". -/
structure PolyTimeAdversary (spec : ℕ → OracleSpec.{0, 0} ι) (α β : ℕ → Type) where
  /-- The machine at each security parameter. -/
  M : (n : ℕ) → OracleMachine (spec n) (α n) (β n)
  /-- Polynomial bound on the number of oracle rounds. -/
  steps : Polynomial ℕ
  /-- The readout is stable: once resolved it never changes. -/
  stable : ∀ n, (M n).StableOutput
  /-- The readout resolves within `steps.eval n` rounds against every handler. -/
  steady : ∀ (n : ℕ) (h : OracleHandler (spec n)) (x : α n),
    (M n).SteadyBy h ((M n).init x) (steps.eval n)
  /-- An encoding of the machine's states. -/
  encState : (n : ℕ) → FinEncoding (M n).State
  /-- An encoding of the inputs. -/
  encIn : (n : ℕ) → FinEncoding (α n)
  /-- An encoding of the outputs. -/
  encOut : (n : ℕ) → FinEncoding (β n)
  /-- An encoding of the oracle interface. -/
  encIface : (n : ℕ) → (spec n).InterfaceEncoding
  /-- Polynomial bound on the encoded state length along every run. -/
  sizeBound : Polynomial ℕ
  /-- The encoded state length stays below `sizeBound` along every handler run. -/
  encState_length_le : ∀ (n : ℕ) (h : OracleHandler (spec n)) (x : α n) (j : ℕ),
    j ≤ steps.eval n →
    ((encState n).boolify
      (OracleStrategy.stateAfter h (M n).toStrategy ((M n).init x) j)).length ≤
      sizeBound.eval n
  /-- The initialization map is polynomial-time computable. -/
  initTM : (n : ℕ) → EncPolyTime ((encIn n).boolify) ((encState n).boolify) (M n).init
  /-- The query-selection map is polynomial-time computable. -/
  exposeTM : (n : ℕ) →
    EncPolyTime ((encState n).boolify) ((encIface n).encQuery.boolify) (M n).expose
  /-- The (flattened) state-update map is polynomial-time computable. -/
  updateTM : (n : ℕ) →
    EncPolyTime ((finEncodingPair (encState n) (encIface n).encAns).boolify)
      ((encState n).boolify) (M n).updateFlat
  /-- The readout map is polynomial-time computable. -/
  outputTM : (n : ℕ) →
    EncPolyTime ((encState n).boolify) ((finEncodingOption (encOut n)).boolify)
      (M n).output
  /-- A single polynomial bounding every per-step running time, uniformly in `n`
  (without this, per-`n` polynomial bounds could grow arbitrarily with `n`). -/
  stepTime : Polynomial ℕ
  /-- `initTM` runs within the uniform per-step bound. -/
  initTM_time_le : ∀ n k, ((initTM n).time).eval k ≤ stepTime.eval (n + k)
  /-- `exposeTM` runs within the uniform per-step bound. -/
  exposeTM_time_le : ∀ n k, ((exposeTM n).time).eval k ≤ stepTime.eval (n + k)
  /-- `updateTM` runs within the uniform per-step bound. -/
  updateTM_time_le : ∀ n k, ((updateTM n).time).eval k ≤ stepTime.eval (n + k)
  /-- `outputTM` runs within the uniform per-step bound. -/
  outputTM_time_le : ∀ n k, ((outputTM n).time).eval k ≤ stepTime.eval (n + k)

namespace PolyTimeAdversary

variable {spec : ℕ → OracleSpec.{0, 0} ι} {α β : ℕ → Type}

/-! ## Run semantics and the implements relation -/

/-- The adversary's run at security parameter `n`: the early-stopping probabilistic
run of the machine at its round bound. -/
noncomputable def exec (D : PolyTimeAdversary spec α β) (n : ℕ)
    (H : ProbHandler (spec n)) (x : α n) : SPMF (Option (β n)) :=
  (D.M n).runK H (D.steps.eval n) ((D.M n).init x)

/-- The adversary implements a program family when each machine implements the
program at the round bound (`OracleMachine.Implements`). -/
def Implements (D : PolyTimeAdversary spec α β)
    (oa : (n : ℕ) → α n → OracleComp (spec n) (β n)) : Prop :=
  ∀ n, (D.M n).Implements (oa n) (D.steps.eval n)

/-- **Master transfer equation**: the run of an implementing adversary computes the
program's `simulateQ` semantics. Game-level advantage transfers are instances. -/
theorem exec_eq_of_implements {D : PolyTimeAdversary spec α β}
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)} (h : D.Implements oa)
    (n : ℕ) (H : ProbHandler (spec n)) (x : α n) :
    D.exec n H x = some <$> simulateQ H (oa n x) :=
  h n H x

end PolyTimeAdversary

/-! ## The polynomial-time predicate on program families -/

/-- A program family is polynomial time when some `PolyTimeAdversary` implements it
within its round bound. This is the intended `isPPT` instantiation for
`SecurityGame.secureAgainst`. The total query bound conjunct feeds the `PolyQueries`
bridge; it is morally a consequence of the implements equation, but the extraction is
kept as an explicit hypothesis (see the module docstring). -/
def OracleComp.IsPolyTime {spec : ℕ → OracleSpec.{0, 0} ι} {α β : ℕ → Type}
    (oa : (n : ℕ) → α n → OracleComp (spec n) (β n)) : Prop :=
  ∃ D : PolyTimeAdversary spec α β, D.Implements oa ∧
    ∀ n x, OracleComp.IsTotalQueryBound (oa n x) (D.steps.eval n)

namespace PolyTimeAdversary

variable {spec : ℕ → OracleSpec.{0, 0} ι} {α β : ℕ → Type}

/-- **Bridge to query bounds**: a polynomial-time adversary's round bound gives a
(per-index constant) `PolyQueries` certificate for any program family it query-bounds. -/
def toPolyQueries (D : PolyTimeAdversary spec α β)
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)}
    (hqb : ∀ n x, OracleComp.IsTotalQueryBound (oa n x) (D.steps.eval n)) :
    OracleComp.PolyQueries oa where
  qb _ := D.steps
  qb_isQueryBound n x := (hqb n x).isPerIndexQueryBound

end PolyTimeAdversary

/-- Polynomial-time program families make polynomially many queries. -/
theorem OracleComp.IsPolyTime.polyQueries {spec : ℕ → OracleSpec.{0, 0} ι}
    {α β : ℕ → Type} {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)}
    (h : OracleComp.IsPolyTime oa) : Nonempty (OracleComp.PolyQueries oa) := by
  obtain ⟨D, -, hqb⟩ := h
  exact ⟨D.toPolyQueries hqb⟩

/-! ## Total running time

The total Turing-machine time of a run is polynomial in the security parameter: the
round count is bounded by `steps`, each per-step time by `stepTime` at inputs whose
length the `sizeBound` invariant (for states) and explicit hypotheses (for inputs and
answers, which are handler-controlled and hence not machine data) keep polynomial.
This is pure polynomial arithmetic over the per-step witnesses — no machine is
constructed. An end-to-end single-machine witness for the whole run is a separate,
genuinely harder goal (it needs machine iteration on top of Cslib's composition). -/

namespace PolyTimeAdversary

variable {spec : ℕ → OracleSpec.{0, 0} ι} {α β : ℕ → Type}

/-- The state at round `j` of the deterministic run against handler `h` on input `x`. -/
def stateAt (D : PolyTimeAdversary spec α β) (n : ℕ) (h : OracleHandler (spec n))
    (x : α n) (j : ℕ) : (D.M n).State :=
  OracleStrategy.stateAfter h (D.M n).toStrategy ((D.M n).init x) j

/-- The tagged query/answer pair received at round `j` of the deterministic run. -/
def answerAt (D : PolyTimeAdversary spec α β) (n : ℕ) (h : OracleHandler (spec n))
    (x : α n) (j : ℕ) : (t : ι) × (spec n).Range t :=
  ⟨(D.M n).expose (D.stateAt n h x j), h ((D.M n).expose (D.stateAt n h x j))⟩

/-- The total Turing-machine time of the deterministic run against handler `h` on
input `x`: the initialization cost plus, per round, the expose, update, and readout
costs, each evaluated at the encoded lengths actually occurring along the run. -/
noncomputable def detTotalTime (D : PolyTimeAdversary spec α β) (n : ℕ)
    (h : OracleHandler (spec n)) (x : α n) : ℕ :=
  (D.initTM n).time.eval ((D.encIn n).boolify x).length +
    ∑ j ∈ Finset.range (D.steps.eval n),
      ((D.exposeTM n).time.eval
          ((D.encState n).boolify (D.stateAt n h x j)).length +
        (D.updateTM n).time.eval
          ((finEncodingPair (D.encState n) (D.encIface n).encAns).boolify
            (D.stateAt n h x j, D.answerAt n h x j)).length +
        (D.outputTM n).time.eval
          ((D.encState n).boolify (D.stateAt n h x j)).length)

/-- **Tier-1 total-time bound.** Against handlers whose answers are boundedly encoded
(`hpair`) and on boundedly encoded inputs (`hin`), the total machine time of a run is
bounded by an explicit polynomial expression in `n`. -/
theorem detTotalTime_le (D : PolyTimeAdversary spec α β) (iB pB : Polynomial ℕ)
    (hin : ∀ (n : ℕ) (x : α n), ((D.encIn n).boolify x).length ≤ iB.eval n)
    (hpair : ∀ (n : ℕ) (h : OracleHandler (spec n)) (x : α n) (j : ℕ),
      j < D.steps.eval n →
      ((finEncodingPair (D.encState n) (D.encIface n).encAns).boolify
        (D.stateAt n h x j, D.answerAt n h x j)).length ≤
        pB.eval n)
    (n : ℕ) (h : OracleHandler (spec n)) (x : α n) :
    D.detTotalTime n h x ≤
      D.stepTime.eval (n + iB.eval n) +
        D.steps.eval n *
          (2 * D.stepTime.eval (n + D.sizeBound.eval n) +
            D.stepTime.eval (n + pB.eval n)) := by
  refine Nat.add_le_add ?_ ?_
  · exact ((D.initTM_time_le n _).trans
      (Polynomial.eval_le_eval (Nat.add_le_add_left (hin n x) n)))
  · refine le_trans (Finset.sum_le_card_nsmul _ _
      (2 * D.stepTime.eval (n + D.sizeBound.eval n) + D.stepTime.eval (n + pB.eval n))
      fun j hj => ?_) ?_
    · rw [Finset.mem_range] at hj
      have hstate : ((D.encState n).boolify (D.stateAt n h x j)).length ≤
          D.sizeBound.eval n :=
        D.encState_length_le n h x j hj.le
      have hexpose := (D.exposeTM_time_le n _).trans
        (Polynomial.eval_le_eval (Nat.add_le_add_left hstate n))
      have houtput := (D.outputTM_time_le n _).trans
        (Polynomial.eval_le_eval (Nat.add_le_add_left hstate n))
      have hupdate := (D.updateTM_time_le n _).trans
        (Polynomial.eval_le_eval (Nat.add_le_add_left (hpair n h x j hj) n))
      omega
    · rw [Finset.card_range, smul_eq_mul]

/-- Packaged form of `detTotalTime_le`: the total run time is bounded by a single
polynomial in the security parameter. -/
theorem exists_polynomial_detTotalTime_le (D : PolyTimeAdversary spec α β)
    (iB pB : Polynomial ℕ)
    (hin : ∀ (n : ℕ) (x : α n), ((D.encIn n).boolify x).length ≤ iB.eval n)
    (hpair : ∀ (n : ℕ) (h : OracleHandler (spec n)) (x : α n) (j : ℕ),
      j < D.steps.eval n →
      ((finEncodingPair (D.encState n) (D.encIface n).encAns).boolify
        (D.stateAt n h x j, D.answerAt n h x j)).length ≤
        pB.eval n) :
    ∃ p : Polynomial ℕ, ∀ (n : ℕ) (h : OracleHandler (spec n)) (x : α n),
      D.detTotalTime n h x ≤ p.eval n := by
  refine ⟨D.stepTime.comp (.X + iB) +
    D.steps * (2 * D.stepTime.comp (.X + D.sizeBound) + D.stepTime.comp (.X + pB)),
    fun n h x => (D.detTotalTime_le iB pB hin hpair n h x).trans_eq ?_⟩
  simp [Polynomial.eval_comp]

end PolyTimeAdversary

/-! ## Query-free adversaries are polynomial time -/

section PureFn

variable [Inhabited ι]

/-- The trivial machine of a query-free function: the state is the input, updates are
ignored, and the readout is immediate. -/
def OracleMachine.ofPureFn {spec : OracleSpec.{0, 0} ι} {α β : Type} (f : α → β) :
    OracleMachine spec α β where
  State := α
  expose _ := (default : ι)
  update s _ := s
  init := id
  output x := some (f x)

/-- The flattened update of the trivial machine is the first projection. -/
theorem OracleMachine.updateFlat_ofPureFn {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (f : α → β) : (OracleMachine.ofPureFn (spec := spec) f).updateFlat = Prod.fst := by
  funext p
  simp [OracleMachine.updateFlat, OracleMachine.ofPureFn]

/-- **Sanity: query-free adversaries are polynomial time**, given machine witnesses
for their (trivial) step functions: the identity witness serves initialization, and
the caller supplies witnesses for the constant query selection, first-projection
update, and the output map itself. Once concrete base machines for constants and
projections exist, all hypotheses discharge generically; until then this is the honest
hypothesis form. -/
theorem OracleComp.isPolyTime_pure_of_witnesses
    {spec : ℕ → OracleSpec.{0, 0} ι} {α β : ℕ → Type} (f : (n : ℕ) → α n → β n)
    (encIn : (n : ℕ) → FinEncoding (α n)) (encOut : (n : ℕ) → FinEncoding (β n))
    (encIface : (n : ℕ) → (spec n).InterfaceEncoding)
    (sizeBound : Polynomial ℕ)
    (hsize : ∀ n x, ((encIn n).boolify x).length ≤ sizeBound.eval n)
    (stepTime : Polynomial ℕ) (hone : ∀ m, 1 ≤ stepTime.eval m)
    (exposeTM : (n : ℕ) → EncPolyTime ((encIn n).boolify)
      ((encIface n).encQuery.boolify) (fun _ => (default : ι)))
    (hexpose : ∀ n k, ((exposeTM n).time).eval k ≤ stepTime.eval (n + k))
    (updateTM : (n : ℕ) → EncPolyTime
      ((finEncodingPair (encIn n) (encIface n).encAns).boolify) ((encIn n).boolify)
      Prod.fst)
    (hupdate : ∀ n k, ((updateTM n).time).eval k ≤ stepTime.eval (n + k))
    (outputTM : (n : ℕ) → EncPolyTime ((encIn n).boolify)
      ((finEncodingOption (encOut n)).boolify) (fun x => some (f n x)))
    (houtput : ∀ n k, ((outputTM n).time).eval k ≤ stepTime.eval (n + k)) :
    OracleComp.IsPolyTime (fun n x => (pure (f n x) : OracleComp (spec n) (β n))) := by
  refine ⟨{
    M := fun n => .ofPureFn (f n)
    steps := 0
    stable := fun n _ _ hb _ => hb
    steady := fun n h x => rfl
    encState := encIn
    encIn := encIn
    encOut := encOut
    encIface := encIface
    sizeBound := sizeBound
    encState_length_le := fun n h x j hj => by
      rw [Polynomial.eval_zero, Nat.le_zero] at hj
      subst hj
      exact hsize n x
    initTM := fun n => .id ((encIn n).boolify)
    exposeTM := exposeTM
    updateTM := fun n => (updateTM n).copy _
      fun p => congrFun (OracleMachine.updateFlat_ofPureFn (f n)).symm p
    outputTM := outputTM
    stepTime := stepTime
    initTM_time_le := fun n k => by
      simpa [EncPolyTime.time, EncPolyTime.id,
        Turing.SingleTapeTM.PolyTimeComputable.id] using hone (n + k)
    exposeTM_time_le := hexpose
    updateTM_time_le := fun n k => hupdate n k
    outputTM_time_le := houtput }, fun n H x => ?_, fun n x => trivial⟩
  rw [Polynomial.eval_zero, OracleMachine.runK_zero]
  change (pure (some (f n x)) : SPMF (Option (β n))) = some <$> simulateQ H (pure (f n x))
  rw [simulateQ_pure, map_pure]

end PureFn
