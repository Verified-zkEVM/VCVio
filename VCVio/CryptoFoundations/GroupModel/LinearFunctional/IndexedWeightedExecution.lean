/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.WeightedQuery
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.FiniteLabels
public import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! # Message-dependent weighted extraction

Signing and representation callbacks receive the signed message as well as the combined base.
This supports several secret-key coefficients acting on the same cached base, while preserving
one chronological received input per signing request. The private base oracle and finite-table
transport are shared with ordinary weighted extraction. The computational definitions are
reducible so that the message-independent wrappers preserve their unfolding behavior.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.LinearFunctional

/-- Uniform randomness, base hashing, and signing of possibly different message labels. -/
abbrev weightedInterfaceSpec (I M G : Type) := (unifSpec + (I →ₒ G)) + (M →ₒ G)

/-- Answer public queries through one private base oracle and record each received point's
representation. Weighted signing queries add one input, regardless of their number of bases. -/
@[expose, reducible] def indexedWeightedOracle {F I M R G V : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (hash : R → G) (sign : M → R → G)
    (hashRep : R → V) (signRep : M → R → V) :
    QueryImpl (weightedInterfaceSpec I M G)
      (StateT (List V) (OracleComp (unifSpec + (I →ₒ R)))) := by
  intro q basis
  rcases q with ((n | i) | m)
  · exact (fun r => (r, basis)) <$> (unifSpec + (I →ₒ R)).query (.inl n)
  · exact (fun r => (hash r, basis ++ [hashRep r])) <$>
      (unifSpec + (I →ₒ R)).query (.inr i)
  · exact (fun r => (sign m r, basis ++ [signRep m r])) <$>
      (liftM (weightedQuery (G := R) (terms m)) : OracleComp (unifSpec + (I →ₒ R)) R)

/-- Run the public interaction and query the final weighted target using the same private
oracle. The final target is excluded from the adversary's received-input basis. -/
@[expose, reducible] def indexedWeightedExtractionProgram {F I M R G V α : Type}
    [AddMonoid R] [SMul F R] (terms : M → List (I × F)) (target : α → M)
    (hash : R → G) (sign : M → R → G)
    (hashRep : R → V) (signRep : M → R → V) (initial : List V)
    (oa : OracleComp (weightedInterfaceSpec I M G) α) :
    OracleComp (unifSpec + (I →ₒ R)) (α × List V × R) := do
  let (out, basis) ← (simulateQ (indexedWeightedOracle terms hash sign hashRep signRep)
        oa).run initial
  let targetValue ← liftM (weightedQuery (G := R) (terms (target out)))
  return (out, basis, targetValue)

/-- The fixed-table counterpart of weighted execution, retaining the same representation basis. -/
@[expose, reducible] def indexedWeightedTableOracle {F I M R G V : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (table : I → R)
    (hash : R → G) (sign : M → R → G)
    (hashRep : R → V) (signRep : M → R → V) :
    QueryImpl (weightedInterfaceSpec I M G) (StateT (List V) ProbComp) := by
  intro q basis
  rcases q with ((n | i) | m)
  · exact (fun r => (r, basis)) <$> (unifSpec.query n : ProbComp _)
  · exact pure (hash (table i), basis ++ [hashRep (table i)])
  · let r := ((terms m).map fun p => p.2 • table p.1).sum
    exact pure (sign m r, basis ++ [signRep m r])

/-- Interpreting all private base lookups by one table preserves chronological execution. -/
theorem indexedWeightedOracle_table {F I M R G V α : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (table : I → R)
    (hash : R → G) (sign : M → R → G)
    (hashRep : R → V) (signRep : M → R → V)
    (oa : OracleComp (weightedInterfaceSpec I M G) α) (initial : List V) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn table))
      ((simulateQ (indexedWeightedOracle terms hash sign hashRep signRep) oa).run initial) =
      (simulateQ (indexedWeightedTableOracle terms table hash sign hashRep signRep)
        oa).run initial := by
  apply simulateQ_StateT_compose
  intro q basis
  rcases q with ((n | i) | m)
  · simp [indexedWeightedOracle, indexedWeightedTableOracle, StateT.run, unifFwdAnswerImpl]
  · change simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn table))
      ((fun r => (hash r, basis ++ [hashRep r])) <$>
        (liftM ((unifSpec + (I →ₒ R)).query (.inr i)))) = _
    rw [simulateQ_map, simulateQ_spec_query]
    rfl
  · simp only [indexedWeightedOracle, indexedWeightedTableOracle, StateT.run, simulateQ_map,
      simulateQ_unifFwd_weightedQuery, map_pure]

/-- A fixed table interprets both the interaction and its final polynomial target. -/
theorem indexedWeightedExtractionProgram_table {F I M R G V α : Type}
    [AddMonoid R] [SMul F R] (terms : M → List (I × F)) (table : I → R)
    (target : α → M) (hash : R → G) (sign : M → R → G)
    (hashRep : R → V) (signRep : M → R → V)
    (initial : List V) (oa : OracleComp (weightedInterfaceSpec I M G) α) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn table))
      (indexedWeightedExtractionProgram terms target hash sign hashRep signRep initial oa) =
      (fun z => (z.1, z.2, ((terms (target z.1)).map fun p => p.2 • table p.1).sum)) <$>
        (simulateQ (indexedWeightedTableOracle terms table hash sign hashRep signRep)
        oa).run initial := by
  simp only [indexedWeightedExtractionProgram, simulateQ_bind, indexedWeightedOracle_table,
    simulateQ_map, simulateQ_unifFwd_weightedQuery, map_pure, bind_pure_comp]

/-- A finite proof cover gives a uniform-table interpretation of weighted lazy extraction.
The base label type itself may be infinite; only the covered labels are sampled in the proof. -/
theorem indexedWeightedExtractionProgram_evalDistEq_finite_table {F I M R G V α : Type}
    [AddMonoid R] [SMul F R] [DecidableEq I] [SampleableType R]
    (terms : M → List (I × F)) (target : α → M)
    (hash : R → G) (sign : M → R → G)
    (hashRep : R → V) (signRep : M → R → V)
    (initial : List V) (oa : OracleComp (weightedInterfaceSpec I M G) α)
    (S : Finset I) (fallback : R)
    (h : QueriesCovered S
      (indexedWeightedExtractionProgram terms target hash sign hashRep signRep initial oa)) :
    (simulateQ (I →ₒ R).romImpl
      (indexedWeightedExtractionProgram terms target hash sign hashRep signRep initial oa)).run' ∅
        =ᵈ
      (do
        let table ← $ᵗ (S → R)
        let H := extendTable S fallback table
        (fun z : α × List V =>
          (z.1, z.2, ((terms (target z.1)).map fun p : I × F => p.2 • H p.1).sum)) <$>
          (simulateQ (indexedWeightedTableOracle terms H hash sign hashRep signRep)
        oa).run initial) := by
  refine (simulateQ_romImpl_evalDistEq_finite_table S _ h fallback).trans ?_
  apply _root_.EvalDistEq.bind_right
  intro table
  rw [indexedWeightedExtractionProgram_table]

end GroupModel.LinearFunctional
