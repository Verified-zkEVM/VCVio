/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.LazyTable
import VCVio.OracleComp.QueryTracking.RandomOracle.FiniteSupport
public import VCVio.OracleComp.Traversal

/-! # Finite proof covers for arbitrary labels

This follows Gurkan's linear-functional proof of BLS security in the algebraic group model
of Fuchsbauer, Kiltz and Loss (CRYPTO 2018). Finite answers give a finite cover of all adaptive
paths, including output labels. The cover is a proof artifact and is never enumerated by a
reduction. No query budget or finite message space is assumed.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.LinearFunctional

private theorem allPaths_mono {I α : Type} {spec : OracleSpec I}
    {P P' : I → Prop} {Q Q' : α → Prop} (oa : OracleComp spec α)
    (hp : ∀ q, P q → P' q) (hq : ∀ a, Q a → Q' a)
    (h : allPathsSatisfy P Q (fun _ => Set.univ) oa) :
    allPathsSatisfy P' Q' (fun _ => Set.univ) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      simp only [allPathsSatisfy_pure] at h ⊢
      exact hq a h
  | query_bind q next ih =>
      obtain ⟨hroot, htail⟩ := (allPathsSatisfy_query_bind q next).mp h
      exact (allPathsSatisfy_query_bind q next).mpr
        ⟨hp q hroot, fun r hr => ih r (htail r hr)⟩

private theorem exists_cover {I α M : Type} {spec : OracleSpec I}
    [∀ q, Finite (spec.Range q)] (queries : I → Finset M) (outputs : α → Finset M)
    (oa : OracleComp spec α) :
    ∃ S : Finset M, allPathsSatisfy (fun q => queries q ⊆ S)
      (fun a => outputs a ⊆ S) (fun _ => Set.univ) oa := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a => exact ⟨outputs a, by simp⟩
  | query_bind q next ih =>
      let : Fintype (spec.Range q) := Fintype.ofFinite _
      choose covers hcovers using ih
      refine ⟨queries q ∪ Finset.univ.biUnion covers, ?_⟩
      apply (allPathsSatisfy_query_bind q next).mpr
      refine ⟨Finset.subset_union_left, fun r _ => ?_⟩
      have hsub : covers r ⊆ queries q ∪ Finset.univ.biUnion covers := by
        intro m hm
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, hm⟩)
      exact allPaths_mono (next r) (fun _ h => h.trans hsub)
        (fun _ h => h.trans hsub) (hcovers r)

/-- A finite family of finite-answer programs has a common finite label cover containing every
query and output label on every adaptive path. The label type itself may be infinite. -/
theorem exists_finite_label_cover {I α M K : Type} {spec : OracleSpec I}
    [Finite K] [∀ q, Finite (spec.Range q)]
    (queries : I → Finset M) (outputs : α → Finset M) (oa : K → OracleComp spec α) :
    ∃ S : Finset M, ∀ k, allPathsSatisfy (fun q => queries q ⊆ S)
      (fun a => outputs a ⊆ S) (fun _ => Set.univ) (oa k) := by
  classical
  let : Fintype K := Fintype.ofFinite _
  choose covers hcovers using fun k => exists_cover queries outputs (oa k)
  refine ⟨Finset.univ.biUnion covers, fun k => ?_⟩
  have hsub : covers k ⊆ Finset.univ.biUnion covers := by
    intro m hm
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hm⟩
  exact allPaths_mono (oa k) (fun _ h => h.trans hsub)
    (fun _ h => h.trans hsub) (hcovers k)

/-- Private lookups stay inside a finite cover; ordinary randomness is unrestricted. -/
@[expose] def QueriesCovered {M R α : Type} (S : Finset M)
    (oa : OracleComp (unifSpec + (M →ₒ R)) α) : Prop :=
  AllQueriesSatisfy oa (fun q => match q with | .inl _ => True | .inr m => m ∈ S)

private theorem queriesCovered_elim {M R α : Type} {S : Finset M}
    {oa : OracleComp (unifSpec + (M →ₒ R)) α} (h : QueriesCovered S oa) :
    AllQueriesSatisfy oa (Sum.elim (fun _ => True) (· ∈ S)) := by
  apply h.mono
  intro q hq
  cases q <;> exact hq

private theorem restrict_rom {M R α : Type} [DecidableEq M] [SampleableType R]
    (S : Finset M) (oa : OracleComp (unifSpec + (M →ₒ R)) α) (h : QueriesCovered S oa)
    (c : (M →ₒ R).QueryCache) :
    (simulateQ (S →ₒ R).romImpl
      (restrictRandomOracleQueries S oa (queriesCovered_elim h))).run' (restrictCache S c) =
      (simulateQ (M →ₒ R).romImpl oa).run' c := by
  have he := congrArg (fun p => (fun z => z.1.1) <$> p)
    (randomOracleLoggedRun_restrictCache S oa (queriesCovered_elim h) c)
  simp only [StateT.run'_eq, ← randomOracleLoggedRun_project, Functor.map_map]
  simpa only [Functor.map_map, extendLoggedResult] using he

private theorem restrict_table {M R α : Type} (S : Finset M)
    (oa : OracleComp (unifSpec + (M →ₒ R)) α) (h : QueriesCovered S oa) (table : M → R) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (fun m : S => table m)))
      (restrictRandomOracleQueries S oa (queriesCovered_elim h)) =
      simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn table)) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [restrictRandomOracleQueries_pure, simulateQ_pure]
  | query_bind q next ih =>
      cases q with
      | inl n =>
          rw [restrictRandomOracleQueries_uniformQuery_bind]
          simp only [simulateQ_bind, simulateQ_spec_query]
          change ((unifSpec.query n : ProbComp _) >>= _) = ((unifSpec.query n : ProbComp _) >>= _)
          exact bind_congr fun r => ih r (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 r)
      | inr m =>
          rw [restrictRandomOracleQueries_hashQuery_bind]
          simp only [simulateQ_bind, simulateQ_spec_query]
          change (pure (table m) >>= _) = (pure (table m) >>= _)
          simpa only [pure_bind] using
            ih (table m) (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 (table m))

/-- Extend a proof table by a fixed fallback outside its finite domain. -/
@[expose] def extendTable {M R : Type} [DecidableEq M] (S : Finset M) (fallback : R)
    (table : S → R) (m : M) : R := if h : m ∈ S then table ⟨m, h⟩ else fallback

/-- Every finitely covered lazy program has a finite-table interpretation, even for an infinite
label type. The fallback is unobservable because all lookups belong to the cover. -/
theorem simulateQ_romImpl_evalDistEq_finite_table {M R α : Type}
    [DecidableEq M] [SampleableType R] (S : Finset M)
    (oa : OracleComp (unifSpec + (M →ₒ R)) α) (h : QueriesCovered S oa) (fallback : R) :
    (simulateQ (M →ₒ R).romImpl oa).run' ∅ =ᵈ
      (do let table ← $ᵗ (S → R)
          simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (extendTable S fallback table))) oa) := by
  rw [← restrict_rom S oa h ∅, restrictCache_empty]
  refine (simulateQ_romImpl_evalDistEq_table
    (restrictRandomOracleQueries S oa (queriesCovered_elim h)) ∅).trans ?_
  apply _root_.EvalDistEq.bind_right
  intro table
  rw [completeTable_empty]
  have he : (fun m : S => extendTable S fallback table m) = table := by
    funext m
    simp [extendTable]
  have h := restrict_table S oa h (extendTable S fallback table)
  rw [he] at h
  rw [h]

end GroupModel.LinearFunctional
