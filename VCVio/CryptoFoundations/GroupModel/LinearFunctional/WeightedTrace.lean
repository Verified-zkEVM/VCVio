/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.WeightedCover
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-! # Chronological traces for weighted interactions

Hash labels and signing messages occupy distinct summands. Each public group reply adds
one occurrence, even when a signing request internally reads several base values.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.LinearFunctional

/-- A fixed public oracle with one chronological entry per group reply. -/
@[expose] def weightedFixedOracle {I M G : Type} (hash : I → G) (sign : M → G) :
    QueryImpl (weightedInterfaceSpec I M G) (StateT (List (I ⊕ M)) ProbComp) := by
  intro q tr
  rcases q with ((n | i) | m)
  · exact (fun r => (r, tr)) <$> (unifSpec.query n : ProbComp _)
  · exact pure (hash i, tr ++ [.inl i])
  · exact pure (sign m, tr ++ [.inr m])

/-- The chronological execution against fixed hash and signing functions. -/
@[expose] def weightedFixedRun {I M G α : Type} (hash : I → G) (sign : M → G)
    (oa : OracleComp (weightedInterfaceSpec I M G) α) : ProbComp (α × List (I ⊕ M)) :=
  (simulateQ (weightedFixedOracle hash sign) oa).run []

/-- Chronological signing messages, including repeated requests. -/
@[expose] def weightedSignedMessages {I M : Type} (tr : List (I ⊕ M)) : List M :=
  tr.filterMap (Sum.elim (fun _ => none) some)

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

/-- The representations recorded at reply arrival agree with the corresponding chronological
labels, preserving the initial basis and every repeated query occurrence. -/
theorem weightedTableOracle_run_eq {F I M R G V α : Type}
    [AddMonoid R] [SMul F R] (terms : M → List (I × F)) (table : I → R)
    (hash sign : R → G) (hashRep signRep : R → V) (initial : List V)
    (oa : OracleComp (weightedInterfaceSpec I M G) α) :
    (simulateQ (weightedTableOracle terms table hash sign hashRep signRep) oa).run initial =
      (fun z => (z.1, initial ++ z.2.map (Sum.elim (fun i => hashRep (table i))
        (fun m => signRep (((terms m).map fun p => p.2 • table p.1).sum))))) <$>
      weightedFixedRun (fun i => hash (table i))
        (fun m => sign (((terms m).map fun p => p.2 • table p.1).sum)) oa :=
  indexedWeightedTableOracle_run_eq terms table hash (fun _ => sign)
    hashRep (fun _ => signRep) initial oa

/-- Every supported fixed execution returns a covered target and records covered requests. -/
theorem weightedFixedRun_mem_cover {F I M G α : Type}
    (S : Finset I) (terms : M → List (I × F)) (target : α → M)
    (hash : I → G) (sign : M → G) (oa : OracleComp (weightedInterfaceSpec I M G) α)
    (h : WeightedInterfaceCovered S terms target oa) (z : α × List (I ⊕ M))
    (hz : z ∈ support (weightedFixedRun hash sign oa)) :
    (∀ p ∈ terms (target z.1), p.1 ∈ S) ∧
      ∀ q ∈ z.2, Sum.elim (fun i => i ∈ S) (fun m => ∀ p ∈ terms m, p.1 ∈ S) q := by
  let covered := Sum.elim (fun i => i ∈ S) (fun m => ∀ p ∈ terms m, p.1 ∈ S)
  suffices ∀ tr, (∀ q ∈ tr, covered q) →
      z ∈ support ((simulateQ (weightedFixedOracle hash sign) oa).run tr) →
      (∀ p ∈ terms (target z.1), p.1 ∈ S) ∧ ∀ q ∈ z.2, covered q from
    this [] (by simp) hz
  clear hz
  intro tr htr hz
  induction oa using OracleComp.inductionOn generalizing tr with
  | pure out =>
    have he : z = (out, tr) := by simpa using hz
    subst z
    exact ⟨by simpa [WeightedInterfaceCovered] using h, htr⟩
  | query_bind q next ih =>
    obtain ⟨hq, hn⟩ := (allPathsSatisfy_query_bind q next).mp h
    rcases q with ((n | i) | m) <;>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    · simp only [weightedFixedOracle, StateT.run, bind_map_left] at hz
      obtain ⟨r, _, hr⟩ := mem_support_bind_peel _ _ hz
      exact ih r (hn r (Set.mem_univ _)) tr htr hr
    · simp only [weightedFixedOracle, StateT.run, pure_bind] at hz
      apply ih (hash i) (hn _ (Set.mem_univ _)) _ _ hz
      intro q hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact htr q hmem
      · rcases List.mem_singleton.mp hmem with rfl
        exact hq
    · simp only [weightedFixedOracle, StateT.run, pure_bind] at hz
      apply ih (sign m) (hn _ (Set.mem_univ _)) _ _ hz
      intro q hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact htr q hmem
      · rcases List.mem_singleton.mp hmem with rfl
        exact hq

end GroupModel.LinearFunctional
