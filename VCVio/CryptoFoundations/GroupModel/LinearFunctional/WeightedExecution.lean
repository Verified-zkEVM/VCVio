/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.IndexedWeightedExecution

/-! # Lazy extraction for weighted signing interfaces

Base hashes and signed messages have independent types. Signing combines a finite list of
base values through the same private oracle used by direct hash queries. Each public reply
appends one representation to the chronological received-input basis; the internal base
lookups of a signing query append no adversary-visible inputs.

This adapts the weighted-reduction construction underlying Gurkan's OOPS proof to a
shared base oracle and representations recorded when replies arrive. The definitions specialize
the message-dependent execution core with callbacks that ignore the message.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.LinearFunctional

/-- Answer public queries through one private base oracle and record each received point's
representation. Weighted signing queries add one input, regardless of their number of bases. -/
@[expose] def weightedOracle {F I M R G V : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (hash sign : R → G) (hashRep signRep : R → V) :
    QueryImpl (weightedInterfaceSpec I M G)
      (StateT (List V) (OracleComp (unifSpec + (I →ₒ R)))) :=
  indexedWeightedOracle terms hash (fun _ => sign) hashRep (fun _ => signRep)

/-- Run the public interaction and query the final weighted target using the same private
oracle. The final target is excluded from the adversary's received-input basis. -/
@[expose] def weightedExtractionProgram {F I M R G V α : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (target : α → M)
    (hash sign : R → G) (hashRep signRep : R → V) (initial : List V)
    (oa : OracleComp (weightedInterfaceSpec I M G) α) :
    OracleComp (unifSpec + (I →ₒ R)) (α × List V × R) :=
  indexedWeightedExtractionProgram terms target hash (fun _ => sign)
    hashRep (fun _ => signRep) initial oa

/-- The fixed-table counterpart of weighted execution, retaining the same representation basis. -/
@[expose] def weightedTableOracle {F I M R G V : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (table : I → R)
    (hash sign : R → G) (hashRep signRep : R → V) :
    QueryImpl (weightedInterfaceSpec I M G) (StateT (List V) ProbComp) :=
  indexedWeightedTableOracle terms table hash (fun _ => sign) hashRep (fun _ => signRep)

/-- Interpreting all private base lookups by one table preserves chronological execution. -/
theorem weightedOracle_table {F I M R G V α : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (table : I → R)
    (hash sign : R → G) (hashRep signRep : R → V)
    (oa : OracleComp (weightedInterfaceSpec I M G) α) (initial : List V) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn table))
      ((simulateQ (weightedOracle terms hash sign hashRep signRep) oa).run initial) =
      (simulateQ (weightedTableOracle terms table hash sign hashRep signRep) oa).run initial :=
  indexedWeightedOracle_table terms table hash (fun _ => sign) hashRep (fun _ => signRep) oa initial

/-- A fixed table interprets both the interaction and its final polynomial target. -/
theorem weightedExtractionProgram_table {F I M R G V α : Type}
    [AddMonoid R] [SMul F R] (terms : M → List (I × F)) (table : I → R)
    (target : α → M) (hash sign : R → G) (hashRep signRep : R → V)
    (initial : List V) (oa : OracleComp (weightedInterfaceSpec I M G) α) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn table))
      (weightedExtractionProgram terms target hash sign hashRep signRep initial oa) =
      (fun z => (z.1, z.2, ((terms (target z.1)).map fun p => p.2 • table p.1).sum)) <$>
        (simulateQ (weightedTableOracle terms table hash sign hashRep signRep) oa).run initial :=
  indexedWeightedExtractionProgram_table terms table target hash (fun _ => sign)
    hashRep (fun _ => signRep) initial oa

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
          (simulateQ (weightedTableOracle terms H hash sign hashRep signRep) oa).run initial) :=
  indexedWeightedExtractionProgram_evalDistEq_finite_table terms target hash (fun _ => sign)
    hashRep (fun _ => signRep) initial oa S fallback h

end GroupModel.LinearFunctional
