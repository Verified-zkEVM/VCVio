/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Invariants

/-! # Final verification lookup and BLS query accounting

The final verification hash is included in the adaptive program, sharing the same indexed
cache as the adversary's direct hashes and signing queries. This accounts for the extra slot
in the Boneh–Lynn–Shacham index-guessing bound.
-/

public section

open OracleComp OracleSpec

namespace BLS

/-- Run a forgery-producing program and perform its final verification hash lookup. -/
@[expose] def withFinalHash {M G : Type}
    (oa : OracleComp ((unifSpec + (M →ₒ G)) + (M →ₒ G)) (M × G)) :
    OracleComp ((unifSpec + (M →ₒ G)) + (M →ₒ G)) ((M × G) × G) := do
  let out ← oa
  let h ← ((unifSpec + (M →ₒ G)) + (M →ₒ G)).query (.inl (.inr out.1))
  return (out, h)

/-- Final verification adds one direct hash query. -/
theorem withFinalHash_hash_bound {M G : Type}
    (oa : OracleComp ((unifSpec + (M →ₒ G)) + (M →ₒ G)) (M × G))
    (qH : ℕ) (hH : oa.IsQueryBoundP (· matches .inl (.inr _)) qH) :
    (withFinalHash oa).IsQueryBoundP (· matches .inl (.inr _)) (qH + 1) := by
  apply isQueryBoundP_bind hH
  intro out _
  simp only [isQueryBoundP_query_bind_iff, isQueryBoundP_pure]
  simp

/-- Final verification adds no signing query. -/
theorem withFinalHash_sign_bound {M G : Type}
    (oa : OracleComp ((unifSpec + (M →ₒ G)) + (M →ₒ G)) (M × G))
    (qS : ℕ) (hS : oa.IsQueryBoundP (· matches .inr _) qS) :
    (withFinalHash oa).IsQueryBoundP (· matches .inr _) qS := by
  have h : (withFinalHash oa).IsQueryBoundP (· matches .inr _) (qS + 0) := by
    apply isQueryBoundP_bind hS
    intro out _
    simp only [isQueryBoundP_query_bind_iff, isQueryBoundP_pure]
    simp
  exact h.mono (Nat.add_zero qS).le

/-- Every final hash answer is represented by a cached entry in the resulting state. -/
theorem withFinalHash_support_entry {V M G : Type} [DecidableEq M]
    (draw : ℕ → ProbComp V) (hash sign : V → G) (j : Option ℕ)
    (oa : OracleComp ((unifSpec + (M →ₒ G)) + (M →ₒ G)) (M × G))
    (s : OracleState V M) (hs : IndexInv j s)
    (z : ((M × G) × G) × OracleState V M)
    (hz : z ∈ support ((simulateQ (indexedOracle draw hash sign j) (withFinalHash oa)).run s)) :
    ∃ v i, z.2.cache z.1.1.1 = some (v, i) ∧ z.1.2 = hash v := by
  simp only [withFinalHash, simulateQ_bind, StateT.run_bind] at hz
  obtain ⟨⟨out, st⟩, ho, hz⟩ := mem_support_bind_peel _ _ hz
  have hi := simulateQ_run_preservesInv _ _ (indexedOracle_preserves_indexInv draw hash sign j)
    oa s hs (out, st) ho
  simp only [simulateQ_spec_query, simulateQ_pure, StateT.run_pure, bind_pure_comp] at hz
  obtain ⟨w, hw, he⟩ := mem_support_map_peel _ _ hz
  subst z
  change w ∈ support ((indexedOracle draw hash sign j (.inl (.inr out.1))).run st) at hw
  rw [indexedOracle_run_hash] at hw
  obtain ⟨u, hu, he⟩ := mem_support_map_peel _ _ hw
  subst w
  exact ⟨u.1.1, u.1.2, (indexedEntry_support_inv draw j out.1 st hi u hu).2, rfl⟩

/-- The forgery's insertion index lies within the guessed range once the final verification
hash is included. -/
theorem withFinalHash_support_index_lt {V M G : Type} [DecidableEq M]
    (draw : ℕ → ProbComp V) (hash sign : V → G) (j : Option ℕ)
    (oa : OracleComp ((unifSpec + (M →ₒ G)) + (M →ₒ G)) (M × G))
    (qH qS : ℕ) (hH : oa.IsQueryBoundP (· matches .inl (.inr _)) qH)
    (hS : oa.IsQueryBoundP (· matches .inr _) qS)
    (z : ((M × G) × G) × OracleState V M)
    (hz : z ∈ support ((simulateQ (indexedOracle draw hash sign j) (withFinalHash oa)).run
      OracleState.empty)) :
    ∃ v i, z.2.cache z.1.1.1 = some (v, i) ∧ z.1.2 = hash v ∧ i < qH + qS + 1 := by
  obtain ⟨v, i, hc, hv⟩ := withFinalHash_support_entry draw hash sign j oa _ (indexInv_empty j) z hz
  have hi := simulateQ_run_preservesInv _ _ (indexedOracle_preserves_indexInv draw hash sign j)
    (withFinalHash oa) _ (indexInv_empty j) z hz
  have hb := simulateQ_indexedOracle_count_le draw hash sign j (withFinalHash oa)
    OracleState.empty (qH + 1) qS (withFinalHash_hash_bound oa qH hH)
    (withFinalHash_sign_bound oa qS hS) z hz
  have he := hi.bounded z.1.1.1 v i hc
  refine ⟨v, i, hc, hv, ?_⟩
  simp only [OracleState.empty] at hb
  omega

end BLS
