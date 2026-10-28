/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.WeightedExecution
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.FiniteLabels
import all VCVio.CryptoFoundations.GroupModel.LinearFunctional.FiniteLabels

/-! # Finite proof covers for weighted oracle execution

Finite-answer programs use finitely many base labels across all adaptive paths. A cover
includes each weighted signing list and the final target's list. Replay adds no labels, so
the existing finite-table random-oracle theorem applies to the whole extraction program.
The finite cover is used only in proofs and never enumerated by the executable reduction.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.LinearFunctional.Weighted

/-- A base query is covered when its label is; a signing query requires all its weighted bases. -/
@[expose] def ReplyCovered {F I M : Type} (terms : M → List (I × F)) (S : Finset I) :
    I ⊕ M → Prop
  | .inl i => i ∈ S
  | .inr m => ∀ t ∈ terms m, t.1 ∈ S

/-- Every possible public reply and final target uses bases from a single finite cover. -/
@[expose] def Covered {F I M G α : Type} (terms : M → List (I × F)) (S : Finset I)
    (target : α → M) (oa : OracleComp (interfaceSpec I M G) α) : Prop :=
  allPathsSatisfy (fun q => match q with
    | .inl (.inl _) => True
    | .inl (.inr i) => i ∈ S
    | .inr m => ReplyCovered terms S (.inr m))
    (fun out => ReplyCovered terms S (.inr (target out))) (fun _ => Set.univ) oa

/-- A finite family of finite-answer public programs admits one common weighted-base cover. -/
theorem exists_cover {F I M G α K : Type} [Finite G] [Finite K]
    (terms : M → List (I × F)) (target : α → M)
    (oa : K → OracleComp (interfaceSpec I M G) α) :
    ∃ S : Finset I, ∀ k, Covered terms S target (oa k) := by
  classical
  let labels : (interfaceSpec I M G).Domain → Finset I := fun q => match q with
    | .inl (.inl _) => ∅
    | .inl (.inr i) => {i}
    | .inr m => ((terms m).map Prod.fst).toFinset
  have : ∀ q, Finite ((interfaceSpec I M G).Range q) := by
    intro q
    rcases q with ((n | i) | m) <;> dsimp [interfaceSpec] <;> infer_instance
  obtain ⟨S, h⟩ := exists_finite_label_cover labels
    (fun out => ((terms (target out)).map Prod.fst).toFinset) oa
  refine ⟨S, fun k => ?_⟩
  apply allPaths_mono (oa k) _ _ (h k)
  · intro q hq
    rcases q with ((n | i) | m)
    · trivial
    · exact hq (Finset.mem_singleton_self i)
    · intro t ht
      exact hq (by simp [labels, List.mem_map.mpr ⟨t, ht, rfl⟩])
  · intro out ho t ht
    exact ho (by simp [List.mem_map.mpr ⟨t, ht, rfl⟩])

/-- Every lookup in a weighted query belongs to the cover of its list. -/
theorem weightedQuery_covered {F I R : Type} [AddMonoid R] [SMul F R]
    (S : Finset I) (ts : List (I × F)) (h : ∀ t ∈ ts, t.1 ∈ S) :
    QueriesCovered S (weightedQuery (V := R) ts) := by
  induction ts with
  | nil => exact allQueriesSatisfy_pure _ _
  | cons t ts ih =>
      rcases t with ⟨i, a⟩
      rw [weightedQuery_cons]
      apply (allQueriesSatisfy_query_bind_iff _ _ _).2
      refine ⟨h (i, a) (by simp), fun _ => ?_⟩
      exact allQueriesSatisfy_bind (ih (fun t ht => h t (by simp [ht])))
        (fun _ => allQueriesSatisfy_pure _ _)

private theorem oracle_bind_covered {F I M R G α β : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (S : Finset I) (target : α → M) (hash sign : R → G)
    (oa : OracleComp (interfaceSpec I M G) α) (h : Covered terms S target oa)
    (tr : Transcript I M) (htr : ∀ q ∈ tr, ReplyCovered terms S q)
    (k : α × Transcript I M → OracleComp (unifSpec + (I →ₒ R)) β)
    (hk : ∀ out tr, ReplyCovered terms S (.inr (target out)) →
      (∀ q ∈ tr, ReplyCovered terms S q) → QueriesCovered S (k (out, tr))) :
    QueriesCovered S ((simulateQ (oracle terms hash sign) oa).run tr >>= k) := by
  induction oa using OracleComp.inductionOn generalizing tr with
  | pure out =>
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact hk out tr (by simpa [Covered] using h) htr
  | query_bind q next ih =>
      obtain ⟨hq, hn⟩ := (allPathsSatisfy_query_bind q next).mp h
      rcases q with ((n | i) | m) <;>
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
      · change QueriesCovered S
          (((fun r => (r, tr)) <$> (unifSpec.query n : OracleComp (unifSpec + (I →ₒ R)) _))
            >>= fun z => (simulateQ (oracle terms hash sign) (next z.1)).run z.2 >>= k)
        simp only [bind_map_left]
        exact (allQueriesSatisfy_query_bind_iff _ _ _).2
          ⟨trivial, fun r => ih r (hn r (Set.mem_univ _)) tr htr⟩
      · change QueriesCovered S
          (((fun r => (hash r, tr ++ [.inl i])) <$>
            ((I →ₒ R).query i : OracleComp (unifSpec + (I →ₒ R)) _)) >>= fun z =>
              (simulateQ (oracle terms hash sign) (next z.1)).run z.2 >>= k)
        simp only [bind_map_left]
        refine (allQueriesSatisfy_query_bind_iff _ _ _).2
          ⟨hq, fun r => ih (hash r) (hn _ (Set.mem_univ _)) _ ?_⟩
        intro q hq'
        rcases List.mem_append.mp hq' with hmem | hmem
        · exact htr q hmem
        · simpa using (List.mem_singleton.mp hmem) ▸ hq
      · change QueriesCovered S
          (((fun r => (sign r, tr ++ [.inr m])) <$> weightedQuery (terms m)) >>= fun z =>
            (simulateQ (oracle terms hash sign) (next z.1)).run z.2 >>= k)
        simp only [bind_map_left]
        apply allQueriesSatisfy_bind (weightedQuery_covered S (terms m) hq)
        intro r
        apply ih (sign r) (hn _ (Set.mem_univ _))
        intro q hq'
        rcases List.mem_append.mp hq' with hmem | hmem
        · exact htr q hmem
        · simpa using (List.mem_singleton.mp hmem) ▸ hq

private theorem readTranscript_covered {F I M R V : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (S : Finset I) (hash sign : R → V)
    (tr : Transcript I M) (htr : ∀ q ∈ tr, ReplyCovered terms S q) :
    QueriesCovered S (readTranscript terms hash sign tr) := by
  induction tr with
  | nil => exact allQueriesSatisfy_pure _ _
  | cons q rest ih =>
      cases q with
      | inl i =>
          simp only [readTranscript]
          refine (allQueriesSatisfy_query_bind_iff _ _ _).2
            ⟨htr (.inl i) (by simp), fun _ => ?_⟩
          exact allQueriesSatisfy_bind (ih (fun q h => htr q (by simp [h])))
            (fun _ => allQueriesSatisfy_pure _ _)
      | inr m =>
          simp only [readTranscript]
          apply allQueriesSatisfy_bind
            (weightedQuery_covered S (terms m) (htr (.inr m) (by simp)))
          intro r
          exact allQueriesSatisfy_bind (ih (fun q h => htr q (by simp [h])))
            (fun _ => allQueriesSatisfy_pure _ _)

/-- The public weighted-base cover includes replay and final-target lookups. -/
theorem extractionProgram_covered {F I M R G V α : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (S : Finset I) (target : α → M)
    (hash sign : R → G) (hashRep signRep : R → V) (initial : List V)
    (oa : OracleComp (interfaceSpec I M G) α) (h : Covered terms S target oa) :
    QueriesCovered S (extractionProgram terms target hash sign hashRep signRep initial oa) := by
  unfold extractionProgram
  apply oracle_bind_covered terms S target hash sign oa h [] (by simp)
  intro out tr hout htr
  apply allQueriesSatisfy_bind (readTranscript_covered terms S hashRep signRep tr htr)
  intro basis
  exact allQueriesSatisfy_bind (weightedQuery_covered S (terms (target out)) hout)
    (fun _ => allQueriesSatisfy_pure _ _)

/-- The entire lazy weighted extractor has the law of one finite table, jointly with its
output, chronological coefficient basis, and final target. -/
theorem extractionProgram_evalDistEq_finite_table {F I M R G V α : Type}
    [AddMonoid R] [SMul F R] [DecidableEq I] [SampleableType R]
    (terms : M → List (I × F)) (S : Finset I) (target : α → M)
    (hash sign : R → G) (hashRep signRep : R → V) (initial : List V)
    (oa : OracleComp (interfaceSpec I M G) α) (h : Covered terms S target oa) (fallback : R) :
    (simulateQ (I →ₒ R).romImpl
      (extractionProgram terms target hash sign hashRep signRep initial oa)).run' ∅ =ᵈ
      (do let table ← $ᵗ (S → R)
          let ρ := extendTable S fallback table
          let z ← fixedRun (hash ∘ ρ) (fun m => sign (value ρ (terms m))) oa
          return (z.1, initial ++ z.2.map
            (Sum.elim (hashRep ∘ ρ) (fun m => signRep (value ρ (terms m)))),
            value ρ (terms (target z.1)))) := by
  have he := simulateQ_romImpl_evalDistEq_finite_table S _
    (extractionProgram_covered terms S target hash sign hashRep signRep initial oa h) fallback
  simpa only [extractionProgram_table, bind_pure_comp] using he

end GroupModel.LinearFunctional.Weighted
