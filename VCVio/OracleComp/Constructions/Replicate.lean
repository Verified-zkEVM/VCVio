/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Constructions.Replicate.Basic
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.EvalDist
public import VCVio.EvalDist.List
public import VCVio.OracleComp.Constructions.SampleableType
public import Init.Data.Vector.Lemmas

/-!
# Running a Computation Multiple Times

This file defines a function `replicate oa n` that runs the computation `oa` a total of `n` times,
returning the result as a list of length `n`.

Note that while the executions are independent, they may no longer be after calling `simulate`.
-/

@[expose] public section

open OracleSpec

universe u v w

namespace OracleComp

variable {ι} {spec : OracleSpec ι} {α β : Type v}
  (oa : OracleComp spec α) (n : ℕ)

/-- Possible outputs of `replicate n oa` are lists of length `n` where
each element in the list is a possible output of `oa`. -/
@[simp]
lemma support_replicate :
    support (oa.replicate n) = {xs | xs.length = n ∧ ∀ x ∈ xs, x ∈ support oa} := by
  induction n with
  | zero => ext xs; aesop
  | succ n ih =>
    rw [replicate_succ]
    ext xs
    cases xs with
    | nil => simp
    | cons x xs => rw [cons_mem_support_seq_map_cons_iff, ih]; aesop

section probability

variable [IsUniformSpec spec]

lemma probFailure_replicate :
    Pr[⊥ | oa.replicate n] = 1 - (1 - Pr[⊥ | oa]) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp

/-- The probability of getting a list from `replicate` is the product of the chances of
getting each of the individual elements. -/
@[simp]
lemma probOutput_replicate (xs : List α) :
    Pr[= xs | oa.replicate n] = if xs.length = n then (xs.map (Pr[= · | oa])).prod else 0 := by
  have : DecidableEq α := Classical.decEq α
  induction n generalizing xs with
  | zero => cases xs <;> simp [probOutput_eq_zero_of_not_mem_support]
  | succ n ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      rw [replicate_succ, probOutput_cons_seq_map_cons_eq_mul oa (replicate n oa) y ys, ih]
      simp

lemma probEvent_replicate_of_probEvent_cons
    (p : List α → Prop) (hp : p []) (q : α → Prop) (hq : ∀ x xs, p (x :: xs) ↔ q x ∧ p xs) :
    Pr[ p | oa.replicate n] = Pr[ q | oa] ^ n := by
  induction n with
  | zero => simp [hp]
  | succ n ih =>
    rw [replicate_succ,
      probEvent_seq_map_eq_mul oa (replicate n oa) List.cons p q p
        (fun x _ xs _ => hq x xs),
      ih, pow_succ, mul_comm]

@[simp]
lemma mem_finSupport_replicate [DecidableEq α]
    (xs : List α) : xs ∈ finSupport (oa.replicate n) ↔
      xs.length = n ∧ ∀ x ∈ xs, x ∈ finSupport oa := by
  simp [mem_finSupport_iff_mem_support]

lemma probOutput_replicate_uniformSample {α : Type} [Fintype α] [SampleableType α]
    {n : ℕ} {xs : List α} (hlen : xs.length = n) :
    Pr[= xs | replicate n ($ᵗ α)] = (↑(Fintype.card α ^ n) : ENNReal)⁻¹ := by
  simp only [probOutput_replicate, hlen, ite_true, probOutput_uniformSample]
  rw [List.prod_map_const, hlen]
  simpa [Nat.cast_pow] using
    (ENNReal.inv_pow (a := (Fintype.card α : ENNReal)) (n := n)).symm

end probability

/-! ## SimulateQ distributivity -/

section SimulateQ

variable {ι'} {spec' : OracleSpec ι'} {r : Type v → Type*}
  [Monad r] [LawfulMonad r] (impl : QueryImpl spec r)

/-- `simulateQ` distributes over `replicate`: simulating a replicated computation
equals running the simulated body `n` times via monadic recursion. -/
lemma simulateQ_replicate :
    simulateQ impl (replicate n oa) =
      (List.replicate n ()).mapM (fun _ => simulateQ impl oa) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [replicate_succ_bind, simulateQ_bind, simulateQ_pure,
      List.replicate, List.mapM_cons, ih]

end SimulateQ

section VectorMapM

/-- Index-extraction for `(Vector.ofFn id).mapM` over an `OracleComp`: any element in the
support of the monadic `mapM` has each component lying in the support of the corresponding
inner computation. -/
lemma support_ofFn_mapM_index
    {ι α : Type} {spec : OracleSpec ι} {L : ℕ}
    (f : Fin L → OracleComp spec α)
    {v : Vector α L}
    (hv : v ∈ support ((Vector.ofFn (id : Fin L → Fin L)).mapM f))
    (i : Fin L) : v[i] ∈ support (f i) := by
  simpa using
    Vector.support_mapM_index (Vector.ofFn (id : Fin L → Fin L)) f hv i

end VectorMapM

end OracleComp
