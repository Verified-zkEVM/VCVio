/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.WeightedExecution
import all VCVio.CryptoFoundations.GroupModel.LinearFunctional.FiniteLabels
import VCVio.OracleComp.QueryTracking.RandomOracle.FiniteSupport

/-! # Finite covers for weighted interactions

A signing request can read several private bases while returning one public group element.
The cover includes those bases and the final verification bases, for all adaptive paths.
Neither the public message type nor the private base label type needs to be finite.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.LinearFunctional

/-- All bases used by public hash queries, weighted signing queries, and the final target
belong to the finite proof cover. -/
@[expose] def WeightedInterfaceCovered {F I M G α : Type}
    (S : Finset I) (terms : M → List (I × F)) (target : α → M)
    (oa : OracleComp (weightedInterfaceSpec I M G) α) : Prop :=
  allPathsSatisfy (fun q => match q with
    | .inl (.inl _) => True
    | .inl (.inr i) => i ∈ S
    | .inr m => ∀ p ∈ terms m, p.1 ∈ S)
    (fun out => ∀ p ∈ terms (target out), p.1 ∈ S) (fun _ => Set.univ) oa

/-- Enlarging a proof cover preserves its public interaction invariant. -/
theorem WeightedInterfaceCovered.mono {F I M G α : Type}
    {S U : Finset I} {terms : M → List (I × F)} {target : α → M}
    {oa : OracleComp (weightedInterfaceSpec I M G) α}
    (h : WeightedInterfaceCovered S terms target oa) (hSU : S ⊆ U) :
    WeightedInterfaceCovered U terms target oa := by
  apply allPaths_mono oa _ _ h
  · intro q hq
    rcases q with ((n | i) | m)
    · trivial
    · exact hSU hq
    · exact fun p hp => hSU (hq p hp)
  · exact fun out hout p hp => hSU (hout p hp)

/-- Every finite-answer private-oracle computation has a finite query cover. -/
theorem exists_queriesCovered {I R α : Type} [Finite R]
    (oa : OracleComp (unifSpec + (I →ₒ R)) α) : ∃ S : Finset I, QueriesCovered S oa := by
  classical
  refine ⟨possibleRandomOracleKeys oa, ?_⟩
  apply (allQueriesSatisfy_possibleRandomOracleKeys oa).mono
  intro q hq
  cases q <;> exact hq

/-- Finite public answers give a common finite base cover for a finite family of interactions. -/
theorem exists_weightedInterfaceCovered {F I M G α K : Type} [Finite G] [Finite K]
    (terms : M → List (I × F)) (target : α → M)
    (oa : K → OracleComp (weightedInterfaceSpec I M G) α) :
    ∃ S : Finset I, ∀ k, WeightedInterfaceCovered S terms target (oa k) := by
  classical
  let labels : (weightedInterfaceSpec I M G).Domain → Finset I := fun q => match q with
    | .inl (.inl _) => ∅
    | .inl (.inr i) => {i}
    | .inr m => ((terms m).map Prod.fst).toFinset
  have : ∀ q, Finite ((weightedInterfaceSpec I M G).Range q) := by
    intro q
    rcases q with ((n | i) | m) <;> dsimp [weightedInterfaceSpec] <;> infer_instance
  obtain ⟨S, hS⟩ := exists_finite_label_cover labels
    (fun out => ((terms (target out)).map Prod.fst).toFinset) oa
  refine ⟨S, fun k => allPaths_mono (oa k) ?_ ?_ (hS k)⟩
  · intro q hq
    rcases q with ((n | i) | m)
    · trivial
    · exact hq (Finset.mem_singleton_self i)
    · intro p hp
      exact hq (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩))
  · intro out hout p hp
    exact hout (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩))

/-- A weighted lookup accesses only the labels occurring in its list of terms. -/
theorem weightedQuery_covered {F I R : Type} [AddMonoid R] [SMul F R]
    (S : Finset I) (ts : List (I × F)) (h : ∀ p ∈ ts, p.1 ∈ S) :
    QueriesCovered S (liftM (weightedQuery (G := R) ts) :
      OracleComp (unifSpec + (I →ₒ R)) R) := by
  induction ts with
  | nil => exact allQueriesSatisfy_pure _ _
  | cons p rest ih =>
    simp only [weightedQuery, liftM_bind, liftM_pure]
    refine (allQueriesSatisfy_query_bind_iff _ _ _).2 ⟨h p (by simp), ?_⟩
    intro r
    apply allQueriesSatisfy_bind (ih (fun p hp => h p (by simp [hp])))
    intro tail
    exact allQueriesSatisfy_pure _ _

private theorem weighted_bind_covered {F I M R G V α β : Type}
    [AddMonoid R] [SMul F R] (S : Finset I) (terms : M → List (I × F))
    (target : α → M) (hash sign : R → G) (hashRep signRep : R → V)
    (oa : OracleComp (weightedInterfaceSpec I M G) α)
    (h : WeightedInterfaceCovered S terms target oa) (basis : List V)
    (k : α × List V → OracleComp (unifSpec + (I →ₒ R)) β)
    (hk : ∀ out basis, (∀ p ∈ terms (target out), p.1 ∈ S) →
      QueriesCovered S (k (out, basis))) :
    QueriesCovered S
      ((simulateQ (weightedOracle terms hash sign hashRep signRep) oa).run basis >>= k) := by
  induction oa using OracleComp.inductionOn generalizing basis with
  | pure out =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hk out basis (by simpa [WeightedInterfaceCovered] using h)
  | query_bind q next ih =>
    obtain ⟨hq, hn⟩ := (allPathsSatisfy_query_bind q next).mp h
    rcases q with ((n | i) | m) <;>
      simp only [QueriesCovered, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        bind_assoc]
    all_goals simp only [weightedOracle, StateT.run, bind_map_left]
    · exact (allQueriesSatisfy_query_bind_iff _ _ _).2
        ⟨trivial, fun r => ih r (hn r (Set.mem_univ _)) basis⟩
    · exact (allQueriesSatisfy_query_bind_iff _ _ _).2
        ⟨hq, fun r => ih (hash r) (hn _ (Set.mem_univ _)) _⟩
    · apply allQueriesSatisfy_bind (weightedQuery_covered S (terms m) hq)
      intro r
      exact ih (sign r) (hn _ (Set.mem_univ _)) _

/-- The public cover contains every private lookup of weighted extraction, including the
final verification target and the internal bases of each signing request. -/
theorem weightedExtractionProgram_covered {F I M R G V α : Type}
    [AddMonoid R] [SMul F R] (S : Finset I) (terms : M → List (I × F))
    (target : α → M) (hash sign : R → G) (hashRep signRep : R → V)
    (initial : List V) (oa : OracleComp (weightedInterfaceSpec I M G) α)
    (h : WeightedInterfaceCovered S terms target oa) :
    QueriesCovered S
      (weightedExtractionProgram terms target hash sign hashRep signRep initial oa) := by
  unfold weightedExtractionProgram
  apply weighted_bind_covered S terms target hash sign hashRep signRep oa h initial
  intro out basis hout
  apply allQueriesSatisfy_bind (weightedQuery_covered S (terms (target out)) hout)
  intro targetValue
  exact allQueriesSatisfy_pure _ _

end GroupModel.LinearFunctional
