/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.WeightedQuery
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.FiniteLabels
public import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! # Lazy extraction for weighted signing interfaces

Base hashes and signed messages have independent types. Signing combines a finite list of
base values through the same private oracle used by direct hash queries. Each public reply
appends one representation to the chronological received-input basis; the internal base
lookups of a signing query append no adversary-visible inputs.

This adapts the weighted-reduction construction underlying Gurkan's OOPS proof to a
shared base oracle and representations recorded when replies arrive.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.LinearFunctional

/-- Uniform randomness, base hashing, and signing of possibly different message labels. -/
abbrev weightedInterfaceSpec (I M G : Type) := (unifSpec + (I →ₒ G)) + (M →ₒ G)

/-- Answer public queries through one private base oracle and record each received point's
representation. Weighted signing queries add one input, regardless of their number of bases. -/
@[expose] def weightedOracle {F I M R G V : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (hash sign : R → G) (hashRep signRep : R → V) :
    QueryImpl (weightedInterfaceSpec I M G)
      (StateT (List V) (OracleComp (unifSpec + (I →ₒ R)))) := by
  intro q basis
  rcases q with ((n | i) | m)
  · exact (fun r => (r, basis)) <$> (unifSpec + (I →ₒ R)).query (.inl n)
  · exact (fun r => (hash r, basis ++ [hashRep r])) <$>
      (unifSpec + (I →ₒ R)).query (.inr i)
  · exact (fun r => (sign r, basis ++ [signRep r])) <$>
      (liftM (weightedQuery (G := R) (terms m)) : OracleComp (unifSpec + (I →ₒ R)) R)

/-- Run the public interaction and query the final weighted target using the same private
oracle. The final target is excluded from the adversary's received-input basis. -/
@[expose] def weightedExtractionProgram {F I M R G V α : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (target : α → M)
    (hash sign : R → G) (hashRep signRep : R → V) (initial : List V)
    (oa : OracleComp (weightedInterfaceSpec I M G) α) :
    OracleComp (unifSpec + (I →ₒ R)) (α × List V × R) := do
  let (out, basis) ← (simulateQ (weightedOracle terms hash sign hashRep signRep) oa).run initial
  let targetValue ← liftM (weightedQuery (G := R) (terms (target out)))
  return (out, basis, targetValue)

/-- The fixed-table counterpart of weighted execution, retaining the same representation basis. -/
@[expose] def weightedTableOracle {F I M R G V : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (table : I → R)
    (hash sign : R → G) (hashRep signRep : R → V) :
    QueryImpl (weightedInterfaceSpec I M G) (StateT (List V) ProbComp) := by
  intro q basis
  rcases q with ((n | i) | m)
  · exact (fun r => (r, basis)) <$> (unifSpec.query n : ProbComp _)
  · exact pure (hash (table i), basis ++ [hashRep (table i)])
  · let r := ((terms m).map fun p => p.2 • table p.1).sum
    exact pure (sign r, basis ++ [signRep r])

/-- Interpreting all private base lookups by one table preserves chronological execution. -/
theorem weightedOracle_table {F I M R G V α : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (table : I → R)
    (hash sign : R → G) (hashRep signRep : R → V)
    (oa : OracleComp (weightedInterfaceSpec I M G) α) (initial : List V) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn table))
      ((simulateQ (weightedOracle terms hash sign hashRep signRep) oa).run initial) =
      (simulateQ (weightedTableOracle terms table hash sign hashRep signRep) oa).run initial := by
  apply simulateQ_StateT_compose
  intro q basis
  rcases q with ((n | i) | m)
  · simp [weightedOracle, weightedTableOracle, StateT.run, unifFwdAnswerImpl]
  · change simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn table))
      ((fun r => (hash r, basis ++ [hashRep r])) <$>
        (liftM ((unifSpec + (I →ₒ R)).query (.inr i)))) = _
    rw [simulateQ_map, simulateQ_spec_query]
    rfl
  · simp only [weightedOracle, weightedTableOracle, StateT.run, simulateQ_map,
      simulateQ_unifFwd_weightedQuery, map_pure]

/-- A fixed table interprets both the interaction and its final polynomial target. -/
theorem weightedExtractionProgram_table {F I M R G V α : Type}
    [AddMonoid R] [SMul F R] (terms : M → List (I × F)) (table : I → R)
    (target : α → M) (hash sign : R → G) (hashRep signRep : R → V)
    (initial : List V) (oa : OracleComp (weightedInterfaceSpec I M G) α) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn table))
      (weightedExtractionProgram terms target hash sign hashRep signRep initial oa) =
      (fun z => (z.1, z.2, ((terms (target z.1)).map fun p => p.2 • table p.1).sum)) <$>
        (simulateQ (weightedTableOracle terms table hash sign hashRep signRep) oa).run initial := by
  simp only [weightedExtractionProgram, simulateQ_bind, weightedOracle_table,
    simulateQ_map, simulateQ_unifFwd_weightedQuery, map_pure, bind_pure_comp]

/-- A finite proof cover gives a uniform-table interpretation of weighted lazy extraction.
The base label type itself may be infinite; only the covered labels are sampled in the proof. -/
theorem weightedExtractionProgram_evalDistEq_finite_table {F I M R G V α : Type}
    [AddMonoid R] [SMul F R] [DecidableEq I] [SampleableType R]
    (terms : M → List (I × F)) (target : α → M)
    (hash sign : R → G) (hashRep signRep : R → V)
    (initial : List V) (oa : OracleComp (weightedInterfaceSpec I M G) α)
    (S : Finset I) (fallback : R)
    (h : QueriesCovered S
      (weightedExtractionProgram terms target hash sign hashRep signRep initial oa)) :
    (simulateQ (I →ₒ R).romImpl
      (weightedExtractionProgram terms target hash sign hashRep signRep initial oa)).run' ∅ =ᵈ
      (do
        let table ← $ᵗ (S → R)
        let H := extendTable S fallback table
        (fun z : α × List V =>
          (z.1, z.2, ((terms (target z.1)).map fun p : I × F => p.2 • H p.1).sum)) <$>
          (simulateQ (weightedTableOracle terms H hash sign hashRep signRep) oa).run initial) := by
  refine (simulateQ_romImpl_evalDistEq_finite_table S _ h fallback).trans ?_
  apply _root_.EvalDistEq.bind_right
  intro table
  rw [weightedExtractionProgram_table]

end GroupModel.LinearFunctional
