/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Constructions.Replicate.Basic
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.Constructions.UniformFinMeasure
public import VCVio.OracleComp.EvalDist
public import VCVio.EvalDist.List
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import Init.Data.Vector.Lemmas

/-!
# Running a Computation Multiple Times

This file defines a function `replicate oa n` that runs the computation `oa` a total of `n` times,
returning the result as a list of length `n`.

The executions are independent, though simulating them with a stateful handler through
`simulateQ` can correlate them.
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

@[simp]
lemma mem_finSupport_replicate [∀ t, Fintype (spec.Range t)] [DecidableEq α]
    (xs : List α) : xs ∈ finSupport (oa.replicate n) ↔
      xs.length = n ∧ ∀ x ∈ xs, x ∈ finSupport oa := by
  simp [mem_finSupport_iff_mem_support]

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
