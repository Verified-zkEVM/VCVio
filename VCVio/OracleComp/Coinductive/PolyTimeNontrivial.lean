/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.PolyTimeClosure

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
  sorry

/-- **Milestone B (the acceptance target)**: the polynomial-time class at canonical
boundaries does not contain every bitvector predicate. This is the model's
non-triviality certificate — the statement whose provability separates a sound
definition of P/poly from the encoding-caching collapse, by counting: polynomially
many description bits per parameter cannot name doubly-exponentially many functions. -/
theorem exists_not_isPolyTime_pure :
    ∃ f : (n : ℕ) → BitVec n → Bool,
      ¬ OracleComp.IsPolyTime (BoundaryData.coin BitEncFam.bitVecX BitEncFam.bool)
          (fun n x => (pure (f n x) : OracleComp coinSpec Bool)) := by
  sorry

end OracleComp
