/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.FiniteLabels
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.LazyExecution
import all VCVio.CryptoFoundations.GroupModel.LinearFunctional.FiniteLabels

/-! # Covers preserved by chronological extraction

This follows Gurkan's linear-functional proof of BLS security in the algebraic group model
of Fuchsbauer, Kiltz and Loss (CRYPTO 2018). A cover of public interaction labels also covers
the private transcript replay and final target lookup. Thus one finite table suffices for all
parts of the reduction, without changing its executable cache.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.LinearFunctional

/-- Every public request label and the final target belong to the indicated proof cover. -/
@[expose] def InterfaceCovered {M G α : Type} (S : Finset M) (target : α → M)
    (oa : OracleComp (interfaceSpec M G) α) : Prop :=
  allPathsSatisfy (fun q => match q with
    | .inl (.inl _) => True | .inl (.inr m) | .inr m => m ∈ S)
    (fun out => target out ∈ S) (fun _ => Set.univ) oa

/-- A finite family of public inputs admits a common finite cover for all replies and targets. -/
theorem exists_interface_cover {M G α K : Type} [Finite G] [Finite K]
    (target : α → M) (oa : K → OracleComp (interfaceSpec M G) α) :
    ∃ S : Finset M, ∀ k, InterfaceCovered S target (oa k) := by
  classical
  let labels : (interfaceSpec M G).Domain → Finset M := fun q => match q with
    | .inl (.inl _) => ∅ | .inl (.inr m) | .inr m => {m}
  have : ∀ q, Finite ((interfaceSpec M G).Range q) := by
    intro q
    rcases q with ((n | m) | m) <;> dsimp [interfaceSpec] <;> infer_instance
  obtain ⟨S, h⟩ := exists_finite_label_cover labels (fun out => {target out}) oa
  refine ⟨S, fun k => ?_⟩
  apply allPaths_mono (oa k) _ _ (h k)
  · intro q hq
    rcases q with ((n | m) | m)
    · trivial
    · exact hq (Finset.mem_singleton_self m)
    · exact hq (Finset.mem_singleton_self m)
  · intro out ho
    exact ho (Finset.mem_singleton_self _)

private theorem transcript_bind_covered {M R G α β : Type} (S : Finset M) (target : α → M)
    (hash sign : R → G) (oa : OracleComp (interfaceSpec M G) α)
    (h : InterfaceCovered S target oa) (tr : Transcript M)
    (htr : ∀ q ∈ tr, q.2 ∈ S)
    (k : α × Transcript M → OracleComp (unifSpec + (M →ₒ R)) β)
    (hk : ∀ out tr, target out ∈ S → (∀ q ∈ tr, q.2 ∈ S) → QueriesCovered S (k (out, tr))) :
    QueriesCovered S ((simulateQ (transcriptOracle hash sign) oa).run tr >>= k) := by
  induction oa using OracleComp.inductionOn generalizing tr with
  | pure out =>
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact hk out tr (by simpa [InterfaceCovered] using h) htr
  | query_bind q next ih =>
      obtain ⟨hq, hn⟩ := (allPathsSatisfy_query_bind q next).mp h
      rcases q with ((n | m) | m) <;>
        simp only [QueriesCovered, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
          bind_assoc]
      · rw [transcriptOracle_random]
        simp only [OracleComp.liftM_map, bind_map_left]
        exact (allQueriesSatisfy_query_bind_iff _ _ _).2
          ⟨trivial, fun r => ih r (hn r (Set.mem_univ _)) tr htr⟩
      · rw [transcriptOracle_hash]
        simp only [OracleComp.liftM_map, bind_map_left]
        refine (allQueriesSatisfy_query_bind_iff _ _ _).2
          ⟨hq, fun r => ih (hash r) (hn _ (Set.mem_univ _)) _ ?_⟩
        intro q hq'
        rcases List.mem_append.mp hq' with hmem | hmem
        · exact htr q hmem
        · simpa using (List.mem_singleton.mp hmem) ▸ hq
      · rw [transcriptOracle_sign]
        simp only [OracleComp.liftM_map, bind_map_left]
        refine (allQueriesSatisfy_query_bind_iff _ _ _).2
          ⟨hq, fun r => ih (sign r) (hn _ (Set.mem_univ _)) _ ?_⟩
        intro q hq'
        rcases List.mem_append.mp hq' with hmem | hmem
        · exact htr q hmem
        · simpa using (List.mem_singleton.mp hmem) ▸ hq

private theorem readTranscript_covered {M R V : Type} (S : Finset M)
    (hash sign : R → V) (tr : Transcript M) (htr : ∀ q ∈ tr, q.2 ∈ S) :
    QueriesCovered S (readTranscript hash sign tr) := by
  induction tr with
  | nil => exact allQueriesSatisfy_pure _ _
  | cons q rest ih =>
      rcases q with ⟨kind, m⟩
      simp only [readTranscript, QueriesCovered, allQueriesSatisfy_query_bind_iff]
      refine ⟨htr (kind, m) (by simp), fun _ => ?_⟩
      exact allQueriesSatisfy_bind (ih (fun q h => htr q (by simp [h])))
        (fun _ => allQueriesSatisfy_pure _ _)

/-- The source cover also contains every replay lookup and the final extraction target. -/
theorem extractionProgram_covered {M R G V α : Type} (S : Finset M) (target : α → M)
    (hash sign : R → G) (hashRep signRep : R → V) (initial : List V)
    (oa : OracleComp (interfaceSpec M G) α) (h : InterfaceCovered S target oa) :
    QueriesCovered S (extractionProgram target hash sign hashRep signRep initial oa) := by
  unfold extractionProgram
  apply transcript_bind_covered S target hash sign oa h [] (by simp)
  intro out tr hout htr
  apply allQueriesSatisfy_bind (readTranscript_covered S hashRep signRep tr htr)
  intro basis
  exact (allQueriesSatisfy_query_bind_iff _ _ _).2
    ⟨hout, fun _ => allQueriesSatisfy_pure _ _⟩

/-- The finite cover also contains the verification lookup after chronological execution. -/
theorem targetProgram_covered {M R G α : Type} (S : Finset M) (target : α → M)
    (hash sign : R → G) (oa : OracleComp (interfaceSpec M G) α)
    (h : InterfaceCovered S target oa) :
    QueriesCovered S (targetProgram target hash sign oa) := by
  unfold targetProgram
  apply transcript_bind_covered S target hash sign oa h [] (by simp)
  intro out tr hout _
  exact (allQueriesSatisfy_query_bind_iff _ _ _).2
    ⟨hout, fun _ => allQueriesSatisfy_pure _ _⟩

private theorem fixedOracle_run_random {M G : Type} (hash sign : M → G)
    (n : ℕ) (tr : Transcript M) :
    (fixedOracle hash sign (.inl (.inl n))).run tr =
      (fun r => (r, tr)) <$> (unifSpec.query n : ProbComp _) := rfl

private theorem fixedOracle_run_hash {M G : Type} (hash sign : M → G)
    (m : M) (tr : Transcript M) :
    (fixedOracle hash sign (.inl (.inr m))).run tr =
      pure (hash m, tr ++ [(false, m)]) := rfl

private theorem fixedOracle_run_sign {M G : Type} (hash sign : M → G)
    (m : M) (tr : Transcript M) :
    (fixedOracle hash sign (.inr m)).run tr =
      pure (sign m, tr ++ [(true, m)]) := rfl

/-- Every fixed-table execution retains only covered labels and returns a covered target. -/
theorem fixedRun_mem_cover {M G α : Type} (S : Finset M) (target : α → M)
    (hash sign : M → G) (oa : OracleComp (interfaceSpec M G) α)
    (h : InterfaceCovered S target oa) (z : α × Transcript M)
    (hz : z ∈ support (fixedRun hash sign oa)) :
    target z.1 ∈ S ∧ ∀ q ∈ z.2, q.2 ∈ S := by
  suffices ∀ tr, (∀ q ∈ tr, q.2 ∈ S) →
      z ∈ support ((simulateQ (fixedOracle hash sign) oa).run tr) →
      target z.1 ∈ S ∧ ∀ q ∈ z.2, q.2 ∈ S from this [] (by simp) hz
  clear hz
  intro tr htr hz
  induction oa using OracleComp.inductionOn generalizing tr with
  | pure out =>
      have he : z = (out, tr) := by simpa using hz
      subst z
      exact ⟨by simpa [InterfaceCovered] using h, htr⟩
  | query_bind q next ih =>
      obtain ⟨hq, hn⟩ := (allPathsSatisfy_query_bind q next).mp h
      rcases q with ((n | m) | m) <;>
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
          fixedOracle_run_random, fixedOracle_run_hash, fixedOracle_run_sign,
          bind_map_left, pure_bind] at hz
      · obtain ⟨r, _, hr⟩ := mem_support_bind_peel _ _ hz
        exact ih r (hn r (Set.mem_univ _)) tr htr hr
      · apply ih (hash m) (hn _ (Set.mem_univ _)) _ _ hz
        intro q hq'
        rcases List.mem_append.mp hq' with hmem | hmem
        · exact htr q hmem
        · simpa using (List.mem_singleton.mp hmem) ▸ hq
      · apply ih (sign m) (hn _ (Set.mem_univ _)) _ _ hz
        intro q hq'
        rcases List.mem_append.mp hq' with hmem | hmem
        · exact htr q hmem
        · simpa using (List.mem_singleton.mp hmem) ▸ hq

end GroupModel.LinearFunctional
