/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.Machine
import ToMathlib.Computability.BitEncoding

/-!
# Turing-Machine-Grounded Polynomial-Time Adversaries

A `MachineAdversary bd` is a family of oracle machines (`OracleMachine`), indexed by a
security parameter, whose step functions are each Turing-machine computable in
polynomial time (via `Computability.EncPolyTimeFam`, grounded in Cslib's single-tape
machines) relative to **pinned canonical boundary encodings** `bd : BoundaryData`.
Defining polynomial time on machines rather than on `OracleComp` programs directly is
what makes a Turing-machine grounding possible: a machine is a state type with four
plain Lean functions (`init`, `expose`, `update`, `output`), each of which can be
computed by a concrete machine on encoded states, whereas the continuations of a
program tree have no bounded syntactic presentation.

`OracleComp.IsPolyTime bd oa` holds when some adversary carries a `PolyTimeWitness`
for the program family `oa`: it implements `oa` (`OracleMachine.Implements`) within its
round budget, and `oa` is syntactically query-bounded by that budget. It is the
intended instantiation of the `isPPT` predicate of `SecurityGame.secureAgainst`.

## Model

The adversary model is **non-uniform P/poly relative to a fixed canonical
representation**. The pieces, and why each exists:

* **Canonical boundaries** (`BoundaryData`: input, output, and oracle-interface
  encodings, all fixed-width `Computability.BitEncFam`). Without pinning these,
  "polynomial time relative to *some* encoding" is vacuous: the encoding
  `enc x := std x ++ block (f x)` caches any `f` inside the representation, and every
  machine witness degenerates to a small projection — the class would contain every
  function, making hardness assumptions such as `PRGScheme.PRGSecure` unsatisfiable.
  The oracle-answer encoding is an equally real caching channel and is pinned for the
  same reason. Statement-site discipline: `bd` is always an explicit pinned parameter
  of a security definition, never existentially quantified and never adversary-chosen
  (the sole documented exemption is a multi-phase adversary's *own* cross-phase state,
  which its phases share — every bit cached there was produced by a witnessed machine
  from canonical inputs and answers). The registry of canonical constructors
  (`BitEncFam.const/bitVec/pair/option`) is deliberately tiny and structural; theorems
  mean "secure against P/poly relative to the standard representation".
* **The `1^n` convention, formalized.** Katz–Lindell define PPT as polynomial in the
  *input length* and reconcile it with "polynomial in `n`" by handing algorithms the
  security parameter in unary. Here the boundary widths are polynomially bounded by
  definition (`BitEncFam.widBound`), so the two readings agree — the width bound *is*
  the `1^n` convention.
* **Machine-internal freedom.** The state representation (`StrEncFam`, variable-width,
  polynomially length-bounded, existential in the bundle) is the machine's choice of
  data structure. This is harmless by construction: every bit entering a state
  encoding is written by a witnessed step machine from a canonical input or a
  canonical oracle answer, so a crafted state encoding can only cache what the
  machines already computed within their budgets.
* **Resources.** Rounds (`steps`), state length (`StrEncFam.bound`), per-step time
  (`EncPolyTimeFam.time`), and description size (`EncPolyTimeFam.size` — the advice
  bound; time bounds alone admit lookup tables with one state per input, i.e.
  unbounded advice). All four are single polynomials uniform across the family:
  non-uniform machines, P/poly-style, with uniformly polynomial bounds. A uniform
  variant (one machine reading `n`) is deliberately out of scope rather than stubbed.
* Bounds are functions of `n` alone, matching `PolyQueries`; boundary widths being
  `poly(n)` is what makes this equivalent to input-length-based bounds on game inputs.

## Universes

The coalgebra layer (`VCVio.OracleComp.Coinductive.DynSystem`,
`VCVio.OracleComp.Coinductive.Machine`) is universe-polymorphic at `OracleSpec.{u, u}`
(single-universe, forced by `SPMF : Type u → Type u`). This file and everything above
it (closure properties, concrete constructions, asymptotic security) is pinned to
`OracleSpec.{0, 0}` and `Type`: Cslib's single-tape machines, the bit-string
encodings, `Polynomial ℕ`, and the program logic's `wp` all live at `Type 0`.
-/

open OracleSpec Computability

variable {ι : ℕ → Type}

/-! ## Canonical interface encodings -/

/-- Turing-machine-facing canonical encodability of an oracle interface: fixed-width
encodings of the query indices and of the typed query/answer pairs. The answer
component encodes the dependent pair `⟨t, r⟩` so that a machine can consume answers of
varying type through one representation. Pinned per spec family: adversary-chosen
answer encodings would be a caching channel (see the module docstring). -/
structure OracleSpec.InterfaceBitEnc (spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)) where
  /-- Canonical fixed-width encoding of the query index type. -/
  encQuery : BitEncFam ι
  /-- Canonical fixed-width encoding of typed query/answer pairs. -/
  encAns : BitEncFam (fun n => (t : ι n) × (spec n).Range t)

/-- The canonical coin-oracle interface: queries have width `0` (the index type is
`Unit`), answers width `1` (the coin bit). -/
noncomputable def OracleSpec.InterfaceBitEnc.coin :
    InterfaceBitEnc (fun _ => coinSpec) where
  encQuery := .const Unit
  encAns :=
    { wid := fun _ => 1
      widBound := .C 1
      wid_le := fun _ => by simp
      enc := fun _ a => [a.2]
      len_eq := fun _ _ => rfl
      enc_injective := fun n a₁ a₂ h => by
        rcases a₁ with ⟨⟨⟩, b₁⟩
        rcases a₂ with ⟨⟨⟩, b₂⟩
        simpa using h }

/-- The pinned boundary data of a polynomial-time program family: canonical fixed-width
encodings of its inputs and outputs, and the canonical interface encoding of its oracle.
Always an explicit parameter of security statements — never existential (see the module
docstring). -/
structure BoundaryData (spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)) (α β : ℕ → Type) where
  /-- Canonical input encoding. -/
  eIn : BitEncFam α
  /-- Canonical output encoding. -/
  eOut : BitEncFam β
  /-- Canonical oracle-interface encoding. -/
  eIface : OracleSpec.InterfaceBitEnc spec

namespace BoundaryData

variable {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)} {α β γ : ℕ → Type}

/-- Replace the input boundary. -/
def withIn (bd : BoundaryData spec α β) (eIn' : BitEncFam γ) : BoundaryData spec γ β :=
  ⟨eIn', bd.eOut, bd.eIface⟩

/-- Replace the output boundary. -/
def withOut (bd : BoundaryData spec α β) (eOut' : BitEncFam γ) : BoundaryData spec α γ :=
  ⟨bd.eIn, eOut', bd.eIface⟩

/-- Replace the interface boundary. -/
def withIface (bd : BoundaryData spec α β) (eIface' : OracleSpec.InterfaceBitEnc spec) :
    BoundaryData spec α β :=
  ⟨bd.eIn, bd.eOut, eIface'⟩

@[simp] theorem withIn_eIn (bd : BoundaryData spec α β) (e : BitEncFam γ) :
    (bd.withIn e).eIn = e := rfl

@[simp] theorem withIn_eOut (bd : BoundaryData spec α β) (e : BitEncFam γ) :
    (bd.withIn e).eOut = bd.eOut := rfl

@[simp] theorem withOut_eOut (bd : BoundaryData spec α β) (e : BitEncFam γ) :
    (bd.withOut e).eOut = e := rfl

@[simp] theorem withOut_eIn (bd : BoundaryData spec α β) (e : BitEncFam γ) :
    (bd.withOut e).eIn = bd.eIn := rfl

@[simp] theorem withIn_eIface (bd : BoundaryData spec α β) (e : BitEncFam γ) :
    (bd.withIn e).eIface = bd.eIface := rfl

@[simp] theorem withOut_eIface (bd : BoundaryData spec α β) (e : BitEncFam γ) :
    (bd.withOut e).eIface = bd.eIface := rfl

@[simp] theorem withIface_eIface (bd : BoundaryData spec α β)
    (e : OracleSpec.InterfaceBitEnc spec) : (bd.withIface e).eIface = e := rfl

@[simp] theorem withIface_eIn (bd : BoundaryData spec α β)
    (e : OracleSpec.InterfaceBitEnc spec) : (bd.withIface e).eIn = bd.eIn := rfl

@[simp] theorem withIface_eOut (bd : BoundaryData spec α β)
    (e : OracleSpec.InterfaceBitEnc spec) : (bd.withIface e).eOut = bd.eOut := rfl

end BoundaryData

/-- Boundary data over the coin oracle: the common case for textbook adversaries (the
coin oracle is the random bit tape). -/
noncomputable def BoundaryData.coin {α β : ℕ → Type} (eIn : BitEncFam α)
    (eOut : BitEncFam β) : BoundaryData (fun _ => coinSpec) α β :=
  ⟨eIn, eOut, .coin⟩

/-! ## Flattening the dependent update -/

section UpdateFlat

variable {ι : Type} [DecidableEq ι]

namespace OracleMachine

variable {spec : OracleSpec.{0, 0} ι} {α β : Type}

/-- The machine's dependent update flattened to a total function on tagged
query/answer pairs, as a Turing machine must consume it: answers tagged with the
currently exposed query update the state, mismatched tags act as the identity.
Acting as the identity on mismatched tags is a canonical completion, not a modeling
commitment: the run semantics only ever applies the update at the exposed query
(`updateFlat_expose`), but the machine witness needs a total function on the flat
pair type, and any other completion would certify the same machines. -/
def updateFlat (M : OracleMachine spec α β) :
    M.State × ((t : ι) × spec.Range t) → M.State := fun p =>
  letI : DecidableEq spec.toPFunctor.A := ‹DecidableEq ι›
  if h : M.expose p.1 = p.2.1 then M.update p.1 (h ▸ p.2.2) else p.1

@[simp] theorem updateFlat_expose (M : OracleMachine spec α β) (s : M.State)
    (r : spec.Range (M.expose s)) : M.updateFlat (s, ⟨M.expose s, r⟩) = M.update s r := by
  simp [updateFlat]

end OracleMachine

end UpdateFlat

/-! ## Machine adversaries -/

variable [∀ n, DecidableEq (ι n)]

/-- A Turing-machine-grounded polynomial-time adversary at pinned boundaries `bd`:
a family of oracle machines indexed by the security parameter, together with

* a polynomial round budget `steps` and a stable readout (`stable`);
* an injective, polynomially length-bounded string representation of the machine
  states (`state : Computability.StrEncFam` — machine-internal, hence variable-width
  and freely chosen);
* uniform polynomial-time machine families (`Computability.EncPolyTimeFam`, each
  bundling per-parameter Cslib machine witnesses with one time and one description
  polynomial) for the four step functions, against the canonical boundary encodings.

There is no `steady` field: readout resolution within the round budget is *derivable*
for any adversary that implements a program family (`PolyTimeWitness.steadyBy`), and
probabilistic resolution likewise (`OracleMachine.Implements.runK_none_eq_zero`).
The witnesses are data (they carry concrete machines); the Prop-level predicate on
program families is `OracleComp.IsPolyTime`. -/
structure MachineAdversary {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)} {α β : ℕ → Type}
    (bd : BoundaryData spec α β) where
  /-- The machine at each security parameter. -/
  M : (n : ℕ) → OracleMachine (spec n) (α n) (β n)
  /-- Polynomial bound on the number of oracle rounds. -/
  steps : Polynomial ℕ
  /-- The readout is stable: once resolved it never changes. -/
  stable : ∀ n, (M n).StableOutput
  /-- The machine-internal state representation: injective raw bit strings with a
  polynomial length bound (over all states). -/
  state : StrEncFam (fun n => (M n).State)
  /-- The initialization map is uniformly polynomial-time computable. -/
  initF : EncPolyTimeFam bd.eIn.enc state.enc (fun n => (M n).init)
  /-- The query-selection map is uniformly polynomial-time computable. -/
  exposeF : EncPolyTimeFam state.enc bd.eIface.encQuery.enc (fun n => (M n).expose)
  /-- The (flattened) state-update map is uniformly polynomial-time computable, on the
  append encoding of state/answer pairs. -/
  updateF : EncPolyTimeFam (state.pairVar bd.eIface.encAns).enc state.enc
    (fun n => (M n).updateFlat)
  /-- The readout map is uniformly polynomial-time computable, into the canonical
  optional output encoding. -/
  outputF : EncPolyTimeFam state.enc (bd.eOut.option).enc (fun n => (M n).output)

namespace MachineAdversary

variable {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)} {α β : ℕ → Type}
  {bd : BoundaryData spec α β}

/-- A single polynomial dominating every per-step running time. -/
noncomputable def stepTime (D : MachineAdversary bd) : Polynomial ℕ :=
  D.initF.time + D.exposeF.time + D.updateF.time + D.outputF.time

/-- A single polynomial dominating every witness description size — the total advice. -/
noncomputable def descBound (D : MachineAdversary bd) : Polynomial ℕ :=
  D.initF.size + D.exposeF.size + D.updateF.size + D.outputF.size

/-! ## Run semantics and the implements relation -/

/-- The adversary's run at security parameter `n`: the early-stopping run of the
machine at its round budget, against a query implementation in any monad. The
probabilistic run is the `m := SPMF` instance (`H : ProbHandler (spec n)`); a run
against a stateful challenger oracle is the `m := StateT σ SPMF` instance. -/
noncomputable def exec (D : MachineAdversary bd) (n : ℕ) {m : Type → Type} [Monad m]
    (H : QueryImpl (spec n) m) (x : α n) : m (Option (β n)) :=
  (D.M n).runK H (D.steps.eval n) ((D.M n).init x)

/-- The adversary implements a program family when each machine implements the
program at the round budget (`OracleMachine.Implements`). -/
def Implements (D : MachineAdversary bd)
    (oa : (n : ℕ) → α n → OracleComp (spec n) (β n)) : Prop :=
  ∀ n, (D.M n).Implements (oa n) (D.steps.eval n)

@[inherit_doc Implements]
scoped notation:50 D " ⊨ " oa => MachineAdversary.Implements D oa

/-- **Master transfer equation**: the run of an implementing adversary computes the
program's `simulateQ` semantics, in every lawful monad. Game-level advantage transfers
— including against stateful challenger oracles at `m := StateT σ SPMF` — are
instances. -/
theorem exec_eq_of_implements {D : MachineAdversary bd}
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)} (h : D ⊨ oa)
    (n : ℕ) {m : Type → Type} [Monad m] [LawfulMonad m]
    (H : QueryImpl (spec n) m) (x : α n) :
    D.exec n H x = some <$> simulateQ H (oa n x) :=
  h n H x

/-- An implementing adversary's run resolves along every randomized handler: no mass on
an unresolved readout. Probabilistic steadiness is a consequence of the implements
equation (`OracleMachine.Implements.runK_none_eq_zero`), not an extra field. -/
theorem exec_none_eq_zero {D : MachineAdversary bd}
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)} (h : D ⊨ oa)
    (n : ℕ) (H : ProbHandler (spec n)) (x : α n) :
    D.exec n H x none = 0 :=
  (h n).runK_none_eq_zero H x

end MachineAdversary

open scoped MachineAdversary

/-! ## The polynomial-time certificate and predicate -/

/-- A certificate that the program family `oa` is polynomial time at boundaries `bd`:
an adversary together with proofs that it implements `oa` within its round budget and
that `oa` itself respects that budget syntactically. Proof-relevant data, mirroring
`OracleComp.PolyQueries`; the Prop-level predicate is `OracleComp.IsPolyTime`.

The `queryBound` field is definitional, not a wart: "makes polynomially many queries"
is part of what polynomial time means, it feeds the `PolyQueries` bridge directly, and
every route to `implements` produces it as an input or byproduct. It is *conjectured*
to follow from `implements` alone, but the extraction is genuinely hard:

* A counting handler cannot do it. `Implements` quantifies over
  `ProbHandler spec = QueryImpl spec SPMF`, and `SPMF` has no writer component, so no
  handler admissible in the quantification observes query counts.
* The plausible route drives the program along *scaled* handlers `H_ε` (each answer
  distribution scaled to total mass `ε ∈ (0, 1]`): the output mass of the fuelled run
  is a polynomial of degree at most the budget in `ε`, while a program family
  violating the bound contributes a positive higher-degree monomial to the mass of
  `some <$> simulateQ H_ε`, and agreement on `(0, 1]` forces equal coefficients. The
  coefficient-extraction step over `ℝ≥0∞` is the hard part; it is recorded here as a
  conjecture rather than smuggled as an axiom. -/
structure PolyTimeWitness {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)} {α β : ℕ → Type}
    (bd : BoundaryData spec α β)
    (oa : (n : ℕ) → α n → OracleComp (spec n) (β n)) where
  /-- The machine adversary. -/
  A : MachineAdversary bd
  /-- The adversary implements the program family within its round budget. -/
  implements : A ⊨ oa
  /-- The program family syntactically respects the round budget. -/
  queryBound : ∀ n x, OracleComp.IsTotalQueryBound (oa n x) (A.steps.eval n)

/-- A program family is polynomial time at pinned boundaries `bd` when it carries a
`PolyTimeWitness`. This is the intended `isPPT` instantiation for
`SecurityGame.secureAgainst`; `bd` must be a fixed parameter of the enclosing security
statement (see the module docstring's statement-site discipline). -/
def OracleComp.IsPolyTime {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)} {α β : ℕ → Type}
    (bd : BoundaryData spec α β)
    (oa : (n : ℕ) → α n → OracleComp (spec n) (β n)) : Prop :=
  Nonempty (PolyTimeWitness bd oa)

namespace PolyTimeWitness

variable {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)} {α β : ℕ → Type}
  {bd : BoundaryData spec α β} {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)}

/-- Deterministic steadiness is derivable for any certified adversary: the old `steady`
field, now a theorem (via `OracleMachine.Implements.steadyBy`). -/
theorem steadyBy (w : PolyTimeWitness bd oa) (n : ℕ) (h : OracleHandler (spec n))
    (x : α n) : (w.A.M n).SteadyBy h ((w.A.M n).init x) (w.A.steps.eval n) :=
  (w.implements n).steadyBy (w.A.stable n) h x

/-- **Bridge to query bounds**: a certified family makes polynomially many queries,
with a per-index constant `PolyQueries` certificate. -/
def toPolyQueries (w : PolyTimeWitness bd oa) : OracleComp.PolyQueries oa where
  qb := w.A.steps
  qb_isQueryBound n x := (w.queryBound n x).isPerIndexQueryBound

end PolyTimeWitness

/-- Polynomial-time program families make polynomially many queries. -/
theorem OracleComp.IsPolyTime.polyQueries {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)}
    {α β : ℕ → Type} {bd : BoundaryData spec α β}
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)}
    (h : OracleComp.IsPolyTime bd oa) : Nonempty (OracleComp.PolyQueries oa) :=
  h.elim fun w => ⟨w.toPolyQueries⟩

/-! ## Total running time

The total Turing-machine time of a run is polynomial in the security parameter,
hypothesis-free: the round count is bounded by `steps`, each per-step time by its
family's polynomial at inputs whose lengths the state bound (for states) and the
canonical fixed widths (for inputs and answers) control. This is pure polynomial
arithmetic over the per-step witnesses — no machine is constructed. An end-to-end
single-machine witness for the whole run is a separate, genuinely harder goal (it
needs machine iteration on top of Cslib's composition). -/

namespace MachineAdversary

variable {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)} {α β : ℕ → Type}
  {bd : BoundaryData spec α β}

/-- The state at round `j` of the deterministic run against handler `h` on input `x`. -/
def stateAt (D : MachineAdversary bd) (n : ℕ) (h : OracleHandler (spec n))
    (x : α n) (j : ℕ) : (D.M n).State :=
  OracleStrategy.stateAfter h (D.M n).toDynSystem ((D.M n).init x) j

/-- The tagged query/answer pair received at round `j` of the deterministic run. -/
def answerAt (D : MachineAdversary bd) (n : ℕ) (h : OracleHandler (spec n))
    (x : α n) (j : ℕ) : (t : ι n) × (spec n).Range t :=
  ⟨(D.M n).expose (D.stateAt n h x j), h ((D.M n).expose (D.stateAt n h x j))⟩

/-- The total Turing-machine time of the deterministic run against handler `h` on
input `x`: the initialization cost plus, per round, the expose, update, and readout
costs, each evaluated at the encoded lengths actually occurring along the run. -/
noncomputable def detTotalTime (D : MachineAdversary bd) (n : ℕ)
    (h : OracleHandler (spec n)) (x : α n) : ℕ :=
  ((D.initF.wit n).time).eval (bd.eIn.enc n x).length +
    ∑ j ∈ Finset.range (D.steps.eval n),
      (((D.exposeF.wit n).time).eval (D.state.enc n (D.stateAt n h x j)).length +
        ((D.updateF.wit n).time).eval
          ((D.state.pairVar bd.eIface.encAns).enc n
            (D.stateAt n h x j, D.answerAt n h x j)).length +
        ((D.outputF.wit n).time).eval (D.state.enc n (D.stateAt n h x j)).length)

/-- **Total-time bound, hypothesis-free**: the total machine time of any run is bounded
by an explicit polynomial expression in `n` — the canonical fixed input width bounds
the initialization input, the state bound covers every occurring state, and the
canonical answer width caps the update inputs. -/
theorem detTotalTime_le (D : MachineAdversary bd)
    (n : ℕ) (h : OracleHandler (spec n)) (x : α n) :
    D.detTotalTime n h x ≤
      D.initF.time.eval (n + bd.eIn.widBound.eval n) +
        D.steps.eval n *
          (D.exposeF.time.eval (n + D.state.bound.eval n) +
            D.updateF.time.eval
              (n + (D.state.bound.eval n + bd.eIface.encAns.widBound.eval n)) +
            D.outputF.time.eval (n + D.state.bound.eval n)) := by
  refine Nat.add_le_add ?_ ?_
  · refine (D.initF.time_le n _).trans (Polynomial.eval_le_eval ?_)
    have h1 : (bd.eIn.enc n x).length ≤ bd.eIn.widBound.eval n :=
      (bd.eIn.len_eq n x).le.trans (bd.eIn.wid_le n)
    omega
  · refine le_trans (Finset.sum_le_card_nsmul _ _
      (D.exposeF.time.eval (n + D.state.bound.eval n) +
        D.updateF.time.eval
          (n + (D.state.bound.eval n + bd.eIface.encAns.widBound.eval n)) +
        D.outputF.time.eval (n + D.state.bound.eval n))
      fun j _ => ?_) (by rw [Finset.card_range, smul_eq_mul])
    have hstate : (D.state.enc n (D.stateAt n h x j)).length ≤ D.state.bound.eval n :=
      D.state.len_le n _
    have hpair : ((D.state.pairVar bd.eIface.encAns).enc n
        (D.stateAt n h x j, D.answerAt n h x j)).length ≤
          D.state.bound.eval n + bd.eIface.encAns.widBound.eval n := by
      rw [StrEncFam.pairVar_enc, List.length_append, bd.eIface.encAns.len_eq]
      have h1 := D.state.len_le n (D.stateAt n h x j, D.answerAt n h x j).1
      have h2 := bd.eIface.encAns.wid_le n
      omega
    have hexpose := (D.exposeF.time_le n _).trans
      (Polynomial.eval_le_eval (Nat.add_le_add_left hstate n))
    have hupdate := (D.updateF.time_le n _).trans
      (Polynomial.eval_le_eval (Nat.add_le_add_left hpair n))
    have houtput := (D.outputF.time_le n _).trans
      (Polynomial.eval_le_eval (Nat.add_le_add_left hstate n))
    omega

/-- Packaged form of `detTotalTime_le`: the total run time of any adversary is bounded
by a single polynomial in the security parameter, with no side conditions. -/
theorem exists_polynomial_detTotalTime_le (D : MachineAdversary bd) :
    ∃ p : Polynomial ℕ, ∀ (n : ℕ) (h : OracleHandler (spec n)) (x : α n),
      D.detTotalTime n h x ≤ p.eval n := by
  refine ⟨D.initF.time.comp (.X + bd.eIn.widBound) +
    D.steps * (D.exposeF.time.comp (.X + D.state.bound) +
      D.updateF.time.comp (.X + (D.state.bound + bd.eIface.encAns.widBound)) +
      D.outputF.time.comp (.X + D.state.bound)),
    fun n h x => (D.detTotalTime_le n h x).trans_eq ?_⟩
  simp [Polynomial.eval_comp]

end MachineAdversary

/-! ## Query-free adversaries are polynomial time -/

section PureFn

section SingleSpec

variable {ι : Type} [DecidableEq ι] [Inhabited ι]

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

end SingleSpec

variable [∀ n, Inhabited (ι n)]

/-- **Query-free adversaries are polynomial time**, given uniform machine families for
their (trivial) step functions: the identity family serves initialization and the
state representation is the canonical input boundary itself, so the caller supplies
families for the constant query selection, the first-projection update, and the output
map. Once base machines for constants and projections exist, all three discharge
generically; until then this is the honest hypothesis form — and the output family is a
genuine assumption ("`f` is P/poly-computable"), not a formality. -/
theorem OracleComp.isPolyTime_pure_of_witnesses
    {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)} {α β : ℕ → Type} (bd : BoundaryData spec α β)
    (f : (n : ℕ) → α n → β n)
    (exposeF : EncPolyTimeFam bd.eIn.enc bd.eIface.encQuery.enc
      (fun n _ => (default : ι n)))
    (updateF : EncPolyTimeFam (bd.eIn.toStrEncFam.pairVar bd.eIface.encAns).enc
      bd.eIn.enc (fun _ => Prod.fst))
    (outputF : EncPolyTimeFam bd.eIn.enc (bd.eOut.option).enc
      (fun n x => some (f n x))) :
    OracleComp.IsPolyTime bd (fun n x => (pure (f n x) : OracleComp (spec n) (β n))) := by
  refine ⟨{
    A := {
      M := fun n => .ofPureFn (f n)
      steps := 0
      stable := fun n _ _ hb _ => hb
      state := bd.eIn.toStrEncFam
      initF := .id bd.eIn.enc
      exposeF := exposeF
      updateF := updateF.copy _
        (fun n p => congrFun (OracleMachine.updateFlat_ofPureFn (f n)).symm p)
      outputF := outputF }
    implements := fun n => ?_
    queryBound := fun n x => trivial }⟩
  intro m _ _ H x
  rw [Polynomial.eval_zero, OracleMachine.runK_zero]
  change (pure (some (f n x)) : m (Option (β n))) = some <$> simulateQ H (pure (f n x))
  rw [simulateQ_pure, map_pure]

end PureFn
