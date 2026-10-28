/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.Proximity.Weighted

/-! # Finite-cover bridges for chronological Proximity execution

The shared weighted-interface cover bounds the private lookups of the label-recording
handler and its final verification target. The shared extractor's finite-table law also
retains the chronological representations through `weightedTableOracle_run_eq`.
The finite cover is used only in proofs and never enumerated by the executable reduction.
-/

public section

open OracleComp OracleSpec GroupModel.LinearFunctional

namespace Proximity.Weighted

private theorem oracle_bind_covered {F I M R G α β : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (S : Finset I) (target : α → M) (hash sign : R → G)
    (oa : OracleComp (interfaceSpec I M G) α) (h : WeightedInterfaceCovered S terms target oa)
    (tr : Transcript I M)
    (k : α × Transcript I M → OracleComp (unifSpec + (I →ₒ R)) β)
    (hk : ∀ out tr, (∀ p ∈ terms (target out), p.1 ∈ S) →
      QueriesCovered S (k (out, tr))) :
    QueriesCovered S ((simulateQ (oracle terms hash sign) oa).run tr >>= k) := by
  induction oa using OracleComp.inductionOn generalizing tr with
  | pure out =>
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact hk out tr (by simpa [WeightedInterfaceCovered] using h)
  | query_bind q next ih =>
      obtain ⟨hq, hn⟩ := (allPathsSatisfy_query_bind q next).mp h
      rcases q with ((n | i) | m) <;>
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
      · change QueriesCovered S
          (((fun r => (r, tr)) <$> (unifSpec.query n : OracleComp (unifSpec + (I →ₒ R)) _))
            >>= fun z => (simulateQ (oracle terms hash sign) (next z.1)).run z.2 >>= k)
        simp only [bind_map_left]
        exact (allQueriesSatisfy_query_bind_iff _ _ _).2
          ⟨trivial, fun r => ih r (hn r (Set.mem_univ _)) tr⟩
      · change QueriesCovered S
          (((fun r => (hash r, tr ++ [.inl i])) <$>
            ((I →ₒ R).query i : OracleComp (unifSpec + (I →ₒ R)) _)) >>= fun z =>
              (simulateQ (oracle terms hash sign) (next z.1)).run z.2 >>= k)
        simp only [bind_map_left]
        exact (allQueriesSatisfy_query_bind_iff _ _ _).2
          ⟨hq, fun r => ih (hash r) (hn _ (Set.mem_univ _)) _⟩
      · change QueriesCovered S
          (((fun r => (sign r, tr ++ [.inr m])) <$>
            (liftM (weightedQuery (terms m)) : OracleComp (unifSpec + (I →ₒ R)) R)) >>= fun z =>
            (simulateQ (oracle terms hash sign) (next z.1)).run z.2 >>= k)
        simp only [bind_map_left]
        apply allQueriesSatisfy_bind (weightedQuery_covered S (terms m) hq)
        intro r
        exact ih (sign r) (hn _ (Set.mem_univ _)) _

/-- Chronological execution uses only the public program's covered bases. -/
theorem oracle_covered {F I M R G α : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (S : Finset I) (target : α → M) (hash sign : R → G)
    (oa : OracleComp (interfaceSpec I M G) α) (h : WeightedInterfaceCovered S terms target oa) :
    QueriesCovered S ((simulateQ (oracle terms hash sign) oa).run []) := by
  simpa only [bind_pure] using oracle_bind_covered terms S target hash sign oa h []
    pure (fun _ _ _ => allQueriesSatisfy_pure _ _)

/-- The verification target and every chronological query use covered bases. -/
theorem targetProgram_covered {F I M R G α : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (S : Finset I) (target : α → M) (hash sign : R → G)
    (oa : OracleComp (interfaceSpec I M G) α) (h : WeightedInterfaceCovered S terms target oa) :
    QueriesCovered S (targetProgram terms target hash sign oa) := by
  unfold targetProgram
  apply oracle_bind_covered terms S target hash sign oa h []
  intro out tr hout
  exact allQueriesSatisfy_bind (weightedQuery_covered S (terms (target out)) hout)
    (fun _ => allQueriesSatisfy_pure _ _)

/-- The shared lazy weighted extractor has the law of one finite table, jointly with its
output, chronological coefficient basis, and final target. -/
theorem extractionProgram_evalDistEq_finite_table {F I M R G V α : Type}
    [AddMonoid R] [SMul F R] [DecidableEq I] [SampleableType R]
    (terms : M → List (I × F)) (S : Finset I) (target : α → M)
    (hash sign : R → G) (hashRep signRep : R → V) (initial : List V)
    (oa : OracleComp (interfaceSpec I M G) α)
    (h : WeightedInterfaceCovered S terms target oa) (fallback : R) :
    (simulateQ (I →ₒ R).romImpl
      (weightedExtractionProgram terms target hash sign hashRep signRep initial oa)).run' ∅ =ᵈ
      (do let table ← $ᵗ (S → R)
          let ρ := extendTable S fallback table
          let z ← weightedFixedRun (hash ∘ ρ) (fun m => sign (value ρ (terms m))) oa
          return (z.1, initial ++ z.2.map
            (Sum.elim (hashRep ∘ ρ) (fun m => signRep (value ρ (terms m)))),
            value ρ (terms (target z.1)))) := by
  have he := weightedExtractionProgram_evalDistEq_finite_table terms target
    hash sign hashRep signRep initial oa S fallback
    (weightedExtractionProgram_covered S terms target hash sign hashRep signRep initial oa h)
  simpa only [weightedTableOracle_run_eq, Functor.map_map, bind_pure_comp, value,
    Function.comp_def] using he

end Proximity.Weighted
