/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Aggregate.Reduction
public import VCVio.Schemes.BLS.Execution

/-! # Aggregate verification lookups and query accounting

Final aggregate verification hashes every listed message in the shared indexed cache.
These lookups account for the forgery-length term in the BGLS guessing range.
-/

public section

open OracleComp OracleSpec

namespace BLS.Aggregate

variable {F G₁ G₂ Gₜ M : Type}

/-- Run the adversary and retain the sum of pairings from all final verification hashes. -/
@[expose] def withFinalPairings [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ)
    (oa : OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)) (List (G₂ × M) × G₁)) :
    OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)) ((List (G₂ × M) × G₁) × Gₜ) := do
  let out ← oa
  let rhs ← simulateQ
    (fun msg => (liftM
      (((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)).query (.inl (.inr msg))) :
        OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)) G₁))
    (pairingSum e out.1)
  return (out, rhs)

private theorem pairingSum_discard [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (ps : List (G₂ × M)) :
    (do let _ ← simulateQ
          (fun msg => (liftM
      (((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)).query (.inl (.inr msg))) :
        OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)) G₁))
          (pairingSum e ps)
        pure ()) =
    (do let _ ← ps.mapM fun p =>
          (liftM (((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)).query (.inl (.inr p.2))) :
            OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)) G₁)
        pure ()) := by
  induction ps with
  | nil => simp [pairingSum]
  | cons p ps ih =>
    simp only [pairingSum, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
      List.mapM_cons, bind_assoc, pure_bind]
    congr 1
    funext h
    exact ih

/-- Discarding the pairing sum leaves exactly the reduction's final hash queries. -/
theorem withFinalPairings_map_fst [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ)
    (oa : OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)) (List (G₂ × M) × G₁)) :
    Prod.fst <$> withFinalPairings e oa = withFinalHashes oa := by
  simp only [withFinalPairings, withFinalHashes, map_bind, map_pure]
  congr 1
  funext out
  have h := congrArg (fun mx => mx >>= fun _ => pure out) (pairingSum_discard e out.1)
  simpa only [bind_assoc, pure_bind] using h

private theorem pairingSum_hash_bound [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (ps : List (G₂ × M)) :
    (simulateQ
      (fun msg => (liftM
      (((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)).query (.inl (.inr msg))) :
        OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)) G₁))
      (pairingSum e ps)).IsQueryBoundP (· matches .inl (.inr _)) ps.length := by
  induction ps with
  | nil => simp [pairingSum]
  | cons p ps ih =>
    simp only [pairingSum, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
      isQueryBoundP_query_bind_iff, List.length_cons]
    constructor
    · simp
    · intro h
      simpa [bind_pure_comp, isQueryBoundP_map_iff] using ih

private theorem pairingSum_sign_bound [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (ps : List (G₂ × M)) :
    (simulateQ
      (fun msg => (liftM
      (((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)).query (.inl (.inr msg))) :
        OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)) G₁))
      (pairingSum e ps)).IsQueryBoundP (· matches .inr _) 0 := by
  induction ps with
  | nil => simp [pairingSum]
  | cons p ps ih =>
    simp only [pairingSum, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
      isQueryBoundP_query_bind_iff]
    constructor
    · simp
    · intro h
      simpa [bind_pure_comp, isQueryBoundP_map_iff] using ih

/-- Final verification adds at most the forgery-length budget to the direct hash budget. -/
theorem withFinalPairings_hash_bound [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ)
    (oa : OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)) (List (G₂ × M) × G₁))
    (qH N : ℕ) (hH : oa.IsQueryBoundP (· matches .inl (.inr _)) qH)
    (hN : ∀ out ∈ support oa, out.1.length ≤ N) :
    (withFinalPairings e oa).IsQueryBoundP (· matches .inl (.inr _)) (qH + N) := by
  apply isQueryBoundP_bind hH
  intro out hout
  rw [bind_pure_comp, isQueryBoundP_map_iff]
  convert (pairingSum_hash_bound e out.1).mono (hN out hout) using 1
  funext t
  rcases t with (t | msg) | msg <;> rfl

/-- Final aggregate verification makes no signing queries. -/
theorem withFinalPairings_sign_bound [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ)
    (oa : OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)) (List (G₂ × M) × G₁))
    (qS : ℕ) (hS : oa.IsQueryBoundP (· matches .inr _) qS) :
    (withFinalPairings e oa).IsQueryBoundP (· matches .inr _) qS := by
  have hb : (withFinalPairings e oa).IsQueryBoundP (· matches .inr _) (qS + 0) := by
    apply isQueryBoundP_bind hS
    intro out _
    rw [bind_pure_comp, isQueryBoundP_map_iff]
    convert pairingSum_sign_bound e out.1 using 1
    funext t
    rcases t with (t | msg) | msg <;> rfl
  exact hb.mono (Nat.add_zero qS).le

/-- Interpret a cached entry as a hash answer, with zero for messages not yet cached. -/
@[expose] def cachedHash {V : Type} [Zero G₁]
    (hash : V → G₁) (st : OracleState V M) (msg : M) : G₁ :=
  ((st.cache msg).map fun vi => hash vi.1).getD 0

private theorem indexedEntry_preserves_cache {V : Type} [DecidableEq M]
    (draw : ℕ → ProbComp V) (j : Option ℕ) (msg : M) (s : OracleState V M)
    (z : (V × ℕ) × OracleState V M)
    (hz : z ∈ support ((indexedEntry draw j msg).run s)) :
    ∀ n v i, s.cache n = some (v, i) → z.2.cache n = some (v, i) := by
  cases hc : s.cache msg with
  | some vi =>
    simp only [indexedEntry, StateT.run, hc, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact fun _ _ _ h => h
  | none =>
    simp only [indexedEntry, StateT.run, hc, support_map, Set.mem_image] at hz
    obtain ⟨w, _, rfl⟩ := hz
    intro n v i hn
    have hne : n ≠ msg := by rintro rfl; simp [hc] at hn
    simpa [OracleState.insert, hne] using hn

private theorem pairingSum_support {V : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq M]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ)
    (draw : ℕ → ProbComp V) (hash sign : V → G₁) (j : Option ℕ)
    (ps : List (G₂ × M)) (s : OracleState V M) (hs : IndexInv j s)
    (z : Gₜ × OracleState V M)
    (hz : z ∈ support ((simulateQ
      (fun msg => indexedOracle draw hash sign j (.inl (.inr msg)))
      (pairingSum e ps)).run s)) :
    IndexInv j z.2 ∧
      (∀ n v i, s.cache n = some (v, i) → z.2.cache n = some (v, i)) ∧
      (∀ p ∈ ps, ∃ v i, z.2.cache p.2 = some (v, i)) ∧
      z.1 = (ps.map fun p => e (cachedHash hash z.2 p.2) p.1).sum := by
  induction ps generalizing s z with
  | nil =>
    simp only [pairingSum, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst z
    exact ⟨hs, fun _ _ _ h => h, by simp, by simp⟩
  | cons p ps ih =>
    simp only [pairingSum, simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    obtain ⟨⟨h, st⟩, hh, hz⟩ := mem_support_bind_peel _ _ hz
    rw [indexedOracle_run_hash] at hh
    obtain ⟨u, hu, heu⟩ := mem_support_map_peel _ _ hh
    cases heu
    obtain ⟨hi, hc⟩ := indexedEntry_support_inv draw j p.2 s hs u hu
    simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp] at hz
    obtain ⟨w, hw, hew⟩ := mem_support_map_peel _ _ hz
    subst z
    obtain ⟨hi', hp, hall, he⟩ := ih u.2 hi w hw
    have hc' := hp p.2 u.1.1 u.1.2 hc
    refine ⟨hi', ?_, ?_, ?_⟩
    · intro n v i hn
      exact hp n v i (indexedEntry_preserves_cache draw j p.2 s u hu n v i hn)
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨u.1.1, u.1.2, hc'⟩
      · exact hall q hq
    · simpa [cachedHash, hc'] using congrArg (e (hash u.1.1) p.1 + ·) he

/-- Every final message is cached, and the retained pairing sum uses precisely those final
cached answers. The shared BLS insertion and abort invariants hold in the resulting state. -/
theorem withFinalPairings_support {V : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq M]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ)
    (draw : ℕ → ProbComp V) (hash sign : V → G₁) (j : Option ℕ)
    (oa : OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)) (List (G₂ × M) × G₁))
    (s : OracleState V M) (hs : IndexInv j s)
    (z : ((List (G₂ × M) × G₁) × Gₜ) × OracleState V M)
    (hz : z ∈ support ((simulateQ (indexedOracle draw hash sign j)
      (withFinalPairings e oa)).run s)) :
    IndexInv j z.2 ∧ (∀ p ∈ z.1.1.1, ∃ v i, z.2.cache p.2 = some (v, i)) ∧
      z.1.2 = (z.1.1.1.map fun p => e (cachedHash hash z.2 p.2) p.1).sum := by
  simp only [withFinalPairings, simulateQ_bind, StateT.run_bind] at hz
  obtain ⟨⟨out, st⟩, ho, hz⟩ := mem_support_bind_peel _ _ hz
  have hi := simulateQ_run_preservesInv _ _ (indexedOracle_preserves_indexInv draw hash sign j)
    oa s hs (out, st) ho
  simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp] at hz
  obtain ⟨w, hw, he⟩ := mem_support_map_peel _ _ hz
  subst z
  have heq : simulateQ (indexedOracle draw hash sign j)
      (simulateQ (fun msg => (liftM
        (((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)).query (.inl (.inr msg))) :
          OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)) G₁)) (pairingSum e out.1)) =
      simulateQ (fun msg => indexedOracle draw hash sign j (.inl (.inr msg)))
        (pairingSum e out.1) := by
    apply QueryImpl.simulateQ_simulateQ_eq_of_apply
    intro msg
    simp
  rw [heq] at hw
  obtain ⟨hi', _, hall, hr⟩ := pairingSum_support e draw hash sign j out.1 st hi w hw
  exact ⟨hi', hall, hr⟩

/-- Every final message's insertion index lies in the finite guessing range, accounting for
direct hash queries, signing queries, and the maximum forgery length. -/
theorem withFinalPairings_support_index_lt {V : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq M]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ)
    (draw : ℕ → ProbComp V) (hash sign : V → G₁) (j : Option ℕ)
    (oa : OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)) (List (G₂ × M) × G₁))
    (qH qS N : ℕ) (hH : oa.IsQueryBoundP (· matches .inl (.inr _)) qH)
    (hS : oa.IsQueryBoundP (· matches .inr _) qS)
    (hN : ∀ out ∈ support oa, out.1.length ≤ N)
    (z : ((List (G₂ × M) × G₁) × Gₜ) × OracleState V M)
    (hz : z ∈ support ((simulateQ (indexedOracle draw hash sign j)
      (withFinalPairings e oa)).run OracleState.empty)) :
    ∀ p ∈ z.1.1.1, ∃ v i, z.2.cache p.2 = some (v, i) ∧
      i < max 1 (qH + qS + N) := by
  obtain ⟨hi, hall, _⟩ := withFinalPairings_support e draw hash sign j oa _ (indexInv_empty j) z hz
  have hb := simulateQ_indexedOracle_count_le draw hash sign j (withFinalPairings e oa)
    OracleState.empty (qH + N) qS (withFinalPairings_hash_bound e oa qH N hH hN)
    (withFinalPairings_sign_bound e oa qS hS) z hz
  intro p hp
  obtain ⟨v, i, hc⟩ := hall p hp
  have he := hi.bounded p.2 v i hc
  refine ⟨v, i, hc, ?_⟩
  simp only [OracleState.empty] at hb
  omega

end BLS.Aggregate
