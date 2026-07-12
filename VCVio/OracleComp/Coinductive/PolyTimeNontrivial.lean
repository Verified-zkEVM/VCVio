/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.PolyTimeClosure
import ToMathlib.Computability.MachineCounting

/-!
# Non-Triviality Certificates for the Polynomial-Time Adversary Model

Acceptance targets for the canonical-boundary machine model: theorems asserting that
the polynomial-time class does **not** contain every function. Their provability is the
model's soundness certificate, and their history is the model's design rationale:

* With the pre-canonicalization model (existential boundary encodings), both statements
  below were **false**: the encoding `enc x := std x ++ block (f x)` caches any `f`
  inside the input representation, whereupon a bundle with `steps = 0`, `initTM` the
  identity machine, `exposeTM` a constant machine, and two small streaming machines
  (a projection and a block extraction) certifies `f` — no machine ever computes `f`.
* With pinned canonical boundaries (`BoundaryData`), the caching channel is closed, and
  the counting/diagonalization argument goes through: an implementing bundle's
  input→output behavior at parameter `n` factors through its four witness string
  functions (machines of at most `descBound`-many states over the fixed `Bool`
  alphabet, composed at most `steps`-many times), of which there are at most
  `2^{O(d log d)}` at size `d`, while there are `2^{2^n}` functions `BitVec n → Bool`;
  a function chosen (classically) to differ from every `2^{n/4}`-sized composite
  behavior defeats every polynomial bundle at large `n`.

The proofs are staged (see `docs/agents/polytime-model.md`): the run-factorization
lemma (the "compiled run": the deterministic run against a fixed handler is an iterate
of the witness string functions), machine counting and normalization to `Fin d` state
spaces, elementary `p.eval n ≤ 2^(n/4)` growth bounds, and the diagonal construction.
The `sorry`s below are those staged proofs' end products, recorded as the model's
falsifiable acceptance criteria rather than smuggled as axioms — nothing downstream
may depend on them.
-/

open OracleSpec Computability

namespace OracleComp

/-! ## The realizable-predicate bridge

An implementing adversary's computed predicate `f n` at parameter `n` lands in
`Computability.RealizableLE n (d n)` for a polynomial description bound `d`, so a
predicate chosen to escape every polynomial realizable set (the diagonal of
`MachineCounting`) is implemented by no polynomial adversary. The `steps = 0` case is a
real proof (`realizable_of_implements_steps_eq_zero`): the initial-state readout factors
through only the initialization and output witnesses. The general case needs the compiled
run's factorization through the witness string functions, isolated as
`exists_poly_realizable_of_implements`. -/

/-- **[B-factor — isolated crux, `sorry`]** For an adversary implementing `pure ∘ f` at the
coin boundary, the input→output behavior `x ↦ (M n).output (run …)` at parameter `n` is
realized by an `EncPolyTime` initialization/output pair whose description sizes are bounded
by a single polynomial `q` in the adversary's `descBound` and `steps`. The compiled run is
an iterate (at most `steps.eval n` times) of the four witness string functions against the
canonical answer encoding, so its input→output map has a machine of `q.eval n`-bounded
description; discharging it needs the run-factorization of the fuelled machine run through
its per-step witnesses. This is the general-`steps` input to the diagonal contradiction;
the `steps = 0` special case is proved directly by
`realizable_of_implements_steps_eq_zero`. -/
theorem exists_poly_realizable_of_implements
    (A : MachineAdversary (BoundaryData.coin BitEncFam.bitVecX BitEncFam.bool))
    (f : (n : ℕ) → BitVec n → Bool)
    (himpl : A.Implements (fun n x => (pure (f n x) : OracleComp coinSpec Bool))) :
    ∃ q : Polynomial ℕ, ∀ n, f n ∈ RealizableLE n (q.eval n) := by
  sorry

/-- **Milestone A, realizability step (real).** A round-free adversary implementing
`pure ∘ f` realizes `f n` within its description bound: at `steps = 0` the run is the plain
readout of the initial state (`runK_zero`), so `(M n).output ((M n).init x) = some (f n x)`,
and the initialization and output witness families supply the required `EncPolyTime` pair
with sizes bounded by `descBound`. -/
private theorem realizable_of_implements_steps_eq_zero
    (A : MachineAdversary (BoundaryData.coin BitEncFam.bitVecX BitEncFam.bool))
    (f : (n : ℕ) → BitVec n → Bool)
    (himpl : A.Implements (fun n x => (pure (f n x) : OracleComp coinSpec Bool)))
    (hsteps : A.steps = 0) (n : ℕ) :
    f n ∈ RealizableLE n (A.descBound.eval n) := by
  have hout : ∀ x, (A.M n).output ((A.M n).init x) = some (f n x) := by
    intro x
    have h := himpl n
    rw [hsteps] at h
    simp only [Polynomial.eval_zero] at h
    have key := h.runK_eq (m := Id) (OracleHandler.ofFn (fun _ => true)).toQueryImpl x
    rw [OracleMachine.runK_zero] at key
    simp only [simulateQ_pure] at key
    exact key
  refine ⟨(A.M n).State, A.state.enc n, (A.M n).init, (A.M n).output,
    A.initF.wit n, A.outputF.wit n, ?_, ?_, hout⟩
  · exact (A.initF.size_le n).trans (by
      simp only [MachineAdversary.descBound, Polynomial.eval_add]; omega)
  · exact (A.outputF.size_le n).trans (by
      simp only [MachineAdversary.descBound, Polynomial.eval_add]; omega)

/-- **The diagonal predicate (real).** A predicate family `f` together with the covering
`Finset` family `S` of the threshold realizable sets, such that `f` escapes `S` cofinitely.
Assembled from the machine count (`exists_realizableLE_covering`), the count-versus-function
bound (`eventually_count_lt`), and the diagonal argument (`exists_diagonal`). -/
private theorem exists_diagonal_realizable :
    ∃ (f : (n : ℕ) → BitVec n → Bool) (S : (n : ℕ) → Finset (BitVec n → Bool)),
      (∀ n, RealizableLE n (2 ^ (n / 4)) ⊆ ↑(S n)) ∧
        (∀ᶠ n in Filter.atTop, f n ∉ S n) := by
  classical
  set S : (n : ℕ) → Finset (BitVec n → Bool) :=
    fun n => (exists_realizableLE_covering n (2 ^ (n / 4))).choose with hS
  have hcov : ∀ n, RealizableLE n (2 ^ (n / 4)) ⊆ ↑(S n) := fun n =>
    (exists_realizableLE_covering n (2 ^ (n / 4))).choose_spec.1
  have hcard : ∀ n, (S n).card ≤ Turing.SingleTapeTM.B (2 ^ (n / 4)) ^ 2 := fun n =>
    (exists_realizableLE_covering n (2 ^ (n / 4))).choose_spec.2
  have hSlt : ∀ᶠ n in Filter.atTop, (S n).card < 2 ^ (2 ^ n) :=
    eventually_count_lt.mono fun n h => lt_of_le_of_lt (hcard n) h
  obtain ⟨f, hf⟩ := exists_diagonal S hSlt
  exact ⟨f, S, hcov, hf⟩

/-- **The counting contradiction (real).** A diagonal predicate `f` escaping the threshold
realizable sets cofinitely is realized at no polynomial description bound: if `f n` were
realizable within `q.eval n` for every `n`, then cofinitely `q.eval n ≤ 2 ^ (n / 4)`
(`eventually_poly_le`), so `f n` would lie in the covered threshold set — contradicting that
it escapes it. -/
private theorem not_realizable_of_diagonal
    {f : (n : ℕ) → BitVec n → Bool} {S : (n : ℕ) → Finset (BitVec n → Bool)}
    (hcov : ∀ n, RealizableLE n (2 ^ (n / 4)) ⊆ ↑(S n))
    (hnot : ∀ᶠ n in Filter.atTop, f n ∉ S n) (q : Polynomial ℕ)
    (hreal : ∀ n, f n ∈ RealizableLE n (q.eval n)) : False := by
  have hmem : ∀ᶠ n in Filter.atTop, f n ∈ S n :=
    (eventually_poly_le q).mono fun n h =>
      Finset.mem_coe.mp (hcov n (realizableLE_mono h (hreal n)))
  obtain ⟨n, hin, hnotn⟩ := (hmem.and hnot).exists
  exact hnotn hin

/-! ## The certificates -/

/-- **Milestone A (sentinel)**: no family of *round-free* machine adversaries computes
every bitvector predicate. The `steps = 0` case needs no run analysis — the readout of
the initial state factors through just two witness machines — so it isolates the
counting core of the full certificate. False before boundary canonicalization (the
encoding-caching bundle above had `steps = 0`); its provability certifies the pinned
model. -/
theorem exists_not_implements_pure_of_steps_eq_zero :
    ∃ f : (n : ℕ) → BitVec n → Bool,
      ∀ A : MachineAdversary
          (BoundaryData.coin BitEncFam.bitVecX BitEncFam.bool),
        A.steps = 0 →
          ¬ A.Implements (fun n x => (pure (f n x) : OracleComp coinSpec Bool)) := by
  obtain ⟨f, S, hcov, hnot⟩ := exists_diagonal_realizable
  exact ⟨f, fun A hsteps himpl => not_realizable_of_diagonal hcov hnot A.descBound
    (realizable_of_implements_steps_eq_zero A f himpl hsteps)⟩

/-- **Milestone B (the acceptance target)**: the polynomial-time class at canonical
boundaries does not contain every bitvector predicate. This is the model's
non-triviality certificate — the statement whose provability separates a sound
definition of P/poly from the encoding-caching collapse, by counting: polynomially
many description bits per parameter cannot name doubly-exponentially many functions. -/
theorem exists_not_isPolyTime_pure :
    ∃ f : (n : ℕ) → BitVec n → Bool,
      ¬ OracleComp.IsPolyTime (BoundaryData.coin BitEncFam.bitVecX BitEncFam.bool)
          (fun n x => (pure (f n x) : OracleComp coinSpec Bool)) := by
  obtain ⟨f, S, hcov, hnot⟩ := exists_diagonal_realizable
  refine ⟨f, fun h => ?_⟩
  obtain ⟨w⟩ := h
  obtain ⟨q, hreal⟩ := exists_poly_realizable_of_implements w.A f w.implements
  exact not_realizable_of_diagonal hcov hnot q hreal

end OracleComp
