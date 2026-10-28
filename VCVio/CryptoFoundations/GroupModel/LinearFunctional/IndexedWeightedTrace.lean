/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.IndexedWeightedExecution
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.WeightedTrace
public import VCVio.OracleComp.Constructions.SampleableType.Measure
import all VCVio.CryptoFoundations.GroupModel.LinearFunctional.FiniteLabels
import VCVio.OracleComp.QueryTracking.RandomOracle.FiniteSupport

/-! # Covers and traces for message-dependent weighted extraction

Finite public covers control all private base queries. The recorded representations agree
with the chronological public trace, even when signing callbacks depend on the message.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.LinearFunctional

private theorem indexedWeighted_bind_covered {F I M R G V α β : Type}
    [AddMonoid R] [SMul F R] (S : Finset I) (terms : M → List (I × F))
    (target : α → M) (hash : R → G) (sign : M → R → G)
    (hashRep : R → V) (signRep : M → R → V)
    (oa : OracleComp (weightedInterfaceSpec I M G) α)
    (h : WeightedInterfaceCovered S terms target oa) (basis : List V)
    (k : α × List V → OracleComp (unifSpec + (I →ₒ R)) β)
    (hk : ∀ out basis, (∀ p ∈ terms (target out), p.1 ∈ S) →
      QueriesCovered S (k (out, basis))) :
    QueriesCovered S
      ((simulateQ (indexedWeightedOracle terms hash sign hashRep signRep) oa).run basis >>= k) := by
  induction oa using OracleComp.inductionOn generalizing basis with
  | pure out =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hk out basis (by simpa [WeightedInterfaceCovered] using h)
  | query_bind q next ih =>
    obtain ⟨hq, hn⟩ := (allPathsSatisfy_query_bind q next).mp h
    rcases q with ((n | i) | m) <;>
      simp only [QueriesCovered, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        bind_assoc]
    all_goals simp only [indexedWeightedOracle, StateT.run, bind_map_left]
    · exact (allQueriesSatisfy_query_bind_iff _ _ _).2
        ⟨trivial, fun r => ih r (hn r (Set.mem_univ _)) basis⟩
    · exact (allQueriesSatisfy_query_bind_iff _ _ _).2
        ⟨hq, fun r => ih (hash r) (hn _ (Set.mem_univ _)) _⟩
    · apply allQueriesSatisfy_bind (weightedQuery_covered S (terms m) hq)
      intro r
      exact ih (sign m r) (hn _ (Set.mem_univ _)) _

/-- The public cover contains every private lookup of weighted extraction, including the
final verification target and the internal bases of each signing request. -/
theorem indexedWeightedExtractionProgram_covered {F I M R G V α : Type}
    [AddMonoid R] [SMul F R] (S : Finset I) (terms : M → List (I × F))
    (target : α → M) (hash : R → G) (sign : M → R → G)
    (hashRep : R → V) (signRep : M → R → V)
    (initial : List V) (oa : OracleComp (weightedInterfaceSpec I M G) α)
    (h : WeightedInterfaceCovered S terms target oa) :
    QueriesCovered S
      (indexedWeightedExtractionProgram terms target hash sign hashRep signRep initial oa) := by
  unfold indexedWeightedExtractionProgram
  apply indexedWeighted_bind_covered S terms target hash sign hashRep signRep oa h initial
  intro out basis hout
  apply allQueriesSatisfy_bind (weightedQuery_covered S (terms (target out)) hout)
  intro targetValue
  exact allQueriesSatisfy_pure _ _


/-- The representations recorded at reply arrival agree with the corresponding chronological
labels, preserving the initial basis and every repeated query occurrence. -/
theorem indexedWeightedTableOracle_run_eq {F I M R G V α : Type}
    [AddMonoid R] [SMul F R] (terms : M → List (I × F)) (table : I → R)
    (hash : R → G) (sign : M → R → G)
    (hashRep : R → V) (signRep : M → R → V) (initial : List V)
    (oa : OracleComp (weightedInterfaceSpec I M G) α) :
    (simulateQ (indexedWeightedTableOracle terms table hash sign hashRep signRep) oa).run initial =
      (fun z => (z.1, initial ++ z.2.map (Sum.elim (fun i => hashRep (table i))
        (fun m => signRep m (((terms m).map fun p => p.2 • table p.1).sum))))) <$>
      weightedFixedRun (fun i => hash (table i))
        (fun m => sign m (((terms m).map fun p => p.2 • table p.1).sum)) oa := by
  let value := fun m => ((terms m).map fun p => p.2 • table p.1).sum
  let decode := fun tr : List (I ⊕ M) =>
    initial ++ tr.map (Sum.elim (fun i => hashRep (table i)) (fun m => signRep m (value m)))
  have hstep : ∀ q tr, Prod.map id decode <$>
      ((weightedFixedOracle (fun i => hash (table i)) (fun m => sign m (value m))) q).run tr =
      (indexedWeightedTableOracle terms table hash sign hashRep signRep q).run (decode tr) := by
    intro q tr
    rcases q with ((n | i) | m) <;>
      simp [weightedFixedOracle, indexedWeightedTableOracle, StateT.run, decode,
        value, List.append_assoc]
  have h := map_run_simulateQ_eq_of_query_map_eq _ _ decode hstep oa []
  simpa only [weightedFixedRun, decode, List.map_nil, List.append_nil, Prod.map_def,
    id_eq, value] using h.symm


/-- Independent uniform tables pair to a uniform table of pairs. -/
theorem uniformSample_pair_tables {F I : Type} [SampleableType F] [Fintype I] [DecidableEq I] :
    (do let a ← $ᵗ (I → F); let b ← $ᵗ (I → F); return fun i => (a i, b i)) =ᵈ
      ($ᵗ (I → F × F) : ProbComp _) := by
  apply SampleableType.evalDistEq_uniformSample_pair_of_bijective
  constructor
  · intro ⟨a, b⟩ ⟨c, d⟩ h
    exact Prod.ext (funext fun i => congrArg Prod.fst (congrFun h i))
      (funext fun i => congrArg Prod.snd (congrFun h i))
  · intro ρ
    exact ⟨(fun i => (ρ i).1, fun i => (ρ i).2), rfl⟩

/-- Extending a finite table commutes with mapping both its entries and its fallback. -/
theorem extendTable_map {I R U : Type} [DecidableEq I]
    (S : Finset I) (fallback : R) (table : S → R) (f : R → U) (i : I) :
    extendTable S (f fallback) (fun j => f (table j)) i = f (extendTable S fallback table i) := by
  simp only [GroupModel.LinearFunctional.extendTable]
  split <;> rfl

end GroupModel.LinearFunctional
