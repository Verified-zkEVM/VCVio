/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Oracle

/-! # Invariants of the BLS indexed cache

Insertion indices are bounded by the counter and identify messages uniquely. The bad flag
records a signing request at the selected index. These facts connect freshness in the
Boneh–Lynn–Shacham game to the reduction's abort condition.
-/

public section

open OracleComp OracleSpec

namespace BLS

/-- Cache indices identify distinct messages, precede the insertion counter, and witness every
raised abort flag through a signing request at the selected index. -/
structure IndexInv {V M : Type} (j : Option ℕ) (s : OracleState V M) : Prop where
  /-- Every cached index is below the insertion counter. -/
  bounded : ∀ msg v i, s.cache msg = some (v, i) → i < s.count
  /-- Two entries with the same index belong to the same message. -/
  unique : ∀ m n v w i, s.cache m = some (v, i) → s.cache n = some (w, i) → m = n
  /-- A raised flag has a signing request at the selected index as witness. -/
  flagged : s.bad = true → ∃ msg ∈ s.signed, ∃ v i,
    j = some i ∧ s.cache msg = some (v, i)

/-- The empty indexed oracle satisfies its cache and abort invariants. -/
theorem indexInv_empty {V M : Type} (j : Option ℕ) :
    IndexInv j (OracleState.empty : OracleState V M) := by
  constructor <;> simp [OracleState.empty]

private theorem indexInv_insert {V M : Type} [DecidableEq M] {j : Option ℕ}
    {s : OracleState V M} (hs : IndexInv j s) (msg : M) (v : V)
    (hc : s.cache msg = none) : IndexInv j (s.insert j msg v) := by
  constructor
  · intro n w i hn
    by_cases h : n = msg
    · subst n
      simp only [OracleState.insert, QueryCache.cacheQuery_self, Option.some.injEq,
        Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact Nat.lt_succ_self _
    · simp only [OracleState.insert, QueryCache.cacheQuery_of_ne _ _ h] at hn
      exact (hs.bounded n w i hn).trans_le (Nat.le_succ _)
  · intro m n a b i hm hn
    by_cases hm' : m = msg <;> by_cases hn' : n = msg
    · exact hm'.trans hn'.symm
    · subst m
      simp only [OracleState.insert, QueryCache.cacheQuery_self, Option.some.injEq,
        Prod.mk.injEq] at hm
      simp only [OracleState.insert, QueryCache.cacheQuery_of_ne _ _ hn'] at hn
      have := hs.bounded n b i hn
      omega
    · subst n
      simp only [OracleState.insert, QueryCache.cacheQuery_self, Option.some.injEq,
        Prod.mk.injEq] at hn
      simp only [OracleState.insert, QueryCache.cacheQuery_of_ne _ _ hm'] at hm
      have := hs.bounded m a i hm
      omega
    · simp only [OracleState.insert, QueryCache.cacheQuery_of_ne _ _ hm'] at hm
      simp only [OracleState.insert, QueryCache.cacheQuery_of_ne _ _ hn'] at hn
      exact hs.unique m n a b i hm hn
  · intro hb
    obtain ⟨n, hn, w, i, hi, he⟩ := hs.flagged hb
    have hne : n ≠ msg := by rintro rfl; simp [hc] at he
    exact ⟨n, hn, w, i, hi, by simpa [OracleState.insert, hne] using he⟩

private theorem indexInv_recordSign {V M : Type} {j : Option ℕ}
    {s : OracleState V M} (hs : IndexInv j s) (msg : M) (v : V) (i : ℕ)
    (hc : s.cache msg = some (v, i)) : IndexInv j (s.recordSign j msg i) := by
  refine ⟨hs.bounded, hs.unique, ?_⟩
  intro hb
  simp only [OracleState.recordSign, Bool.or_eq_true, decide_eq_true_eq] at hb
  rcases hb with hb | hj
  · obtain ⟨n, hn, w, k, hk, he⟩ := hs.flagged hb
    exact ⟨n, List.mem_append_left _ hn, w, k, hk, he⟩
  · exact ⟨msg, List.mem_append_right _ (by simp), v, i, hj, hc⟩

/-- Reading an indexed entry preserves the invariant and leaves that entry in the cache. -/
theorem indexedEntry_support_inv {V M : Type} [DecidableEq M]
    (draw : ℕ → ProbComp V) (j : Option ℕ) (msg : M) (s : OracleState V M)
    (hs : IndexInv j s) (z : (V × ℕ) × OracleState V M)
    (hz : z ∈ support ((indexedEntry draw j msg).run s)) :
    IndexInv j z.2 ∧ z.2.cache msg = some z.1 := by
  cases hc : s.cache msg with
  | some v =>
    simp only [indexedEntry, StateT.run, hc, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨hs, hc⟩
  | none =>
    simp only [indexedEntry, StateT.run, hc, support_map, Set.mem_image] at hz
    obtain ⟨v, _, rfl⟩ := hz
    exact ⟨indexInv_insert hs msg v hc, by simp [OracleState.insert]⟩

/-- Every combined hash/signing step preserves the cache and abort invariants. -/
theorem indexedOracle_preserves_indexInv {V M G : Type} [DecidableEq M]
    (draw : ℕ → ProbComp V) (hash sign : V → G) (j : Option ℕ) :
    QueryImpl.PreservesInv (indexedOracle (M := M) draw hash sign j) (IndexInv j) := by
  intro t s hs z hz
  rcases t with (t | msg) | msg
  · change z ∈ support ((fun v => (v, s)) <$> (unifSpec.query t : ProbComp _)) at hz
    obtain ⟨_, _, rfl⟩ := mem_support_map_peel _ _ hz
    exact hs
  · rw [indexedOracle_run_hash, support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (indexedEntry_support_inv draw j msg s hs w hw).1
  · rw [indexedOracle_run_sign, support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨hi, hc⟩ := indexedEntry_support_inv draw j msg s hs w hw
    exact indexInv_recordSign hi msg w.1.1 w.1.2 hc

/-- A fresh message at the guessed index implies that no abort has occurred. -/
theorem IndexInv.not_bad_of_fresh {V M : Type} {j : ℕ} {s : OracleState V M}
    (hs : IndexInv (some j) s) {msg : M} {v : V}
    (hc : s.cache msg = some (v, j)) (hf : msg ∉ s.signed) : s.bad = false := by
  cases hb : s.bad with
  | false => rfl
  | true =>
    obtain ⟨n, hn, w, i, hi, he⟩ := hs.flagged hb
    cases Option.some.inj hi
    exact False.elim (hf ((hs.unique n msg w v j he hc) ▸ hn))

/-- The selected scalar has not yet been drawn exactly while the counter has not passed
its index; entries at that index agree with the recorded scalar. -/
structure SelectionInv {V M : Type} (j : ℕ) (s : OracleState V M) : Prop where
  /-- The selected value is absent before the selected insertion. -/
  pending : s.selected = none ↔ s.count ≤ j
  /-- Cached values at the selected index agree with the recorded value. -/
  selected : ∀ msg v, s.cache msg = some (v, j) → s.selected = some v

/-- The selected slot is pending in the empty state. -/
theorem selectionInv_empty {V M : Type} (j : ℕ) :
    SelectionInv j (OracleState.empty : OracleState V M) := by
  constructor <;> simp [OracleState.empty]

private theorem selectionInv_insert {V M : Type} [DecidableEq M] {j : ℕ}
    {s : OracleState V M} (hs : SelectionInv j s) (msg : M) (v : V) :
    SelectionInv j (s.insert (some j) msg v) := by
  constructor
  · by_cases hj : j = s.count
    · simp [OracleState.insert, hj]
    · simpa [OracleState.insert, hj, hs.pending] using
        (show s.count ≤ j ↔ s.count + 1 ≤ j by omega)
  · intro n w hn
    by_cases h : n = msg
    · subst n
      simp only [OracleState.insert, QueryCache.cacheQuery_self, Option.some.injEq,
        Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      simp [OracleState.insert]
    · simp only [OracleState.insert, QueryCache.cacheQuery_of_ne _ _ h] at hn
      have he := hs.selected n w hn
      have hj : j ≠ s.count := by
        intro hj
        have := hs.pending.mpr (by omega)
        simp [he] at this
      simp [OracleState.insert, hj, he]

/-- Every combined hash/signing step preserves the selected-value invariant. -/
theorem indexedOracle_preserves_selectionInv {V M G : Type} [DecidableEq M]
    (draw : ℕ → ProbComp V) (hash sign : V → G) (j : ℕ) :
    QueryImpl.PreservesInv (indexedOracle (M := M) draw hash sign (some j)) (SelectionInv j) := by
  have hentry (msg : M) (s : OracleState V M) (hs : SelectionInv j s)
      (z : (V × ℕ) × OracleState V M)
      (hz : z ∈ support ((indexedEntry draw (some j) msg).run s)) : SelectionInv j z.2 := by
    cases hc : s.cache msg with
    | some v =>
      simp only [indexedEntry, StateT.run, hc, support_pure, Set.mem_singleton_iff] at hz
      subst z
      exact hs
    | none =>
      simp only [indexedEntry, StateT.run, hc, support_map, Set.mem_image] at hz
      obtain ⟨v, _, rfl⟩ := hz
      exact selectionInv_insert hs msg v
  intro t s hs z hz
  rcases t with (t | msg) | msg
  · change z ∈ support ((fun v => (v, s)) <$> (unifSpec.query t : ProbComp _)) at hz
    obtain ⟨_, _, rfl⟩ := mem_support_map_peel _ _ hz
    exact hs
  · rw [indexedOracle_run_hash, support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact hentry msg s hs w hw
  · rw [indexedOracle_run_sign, support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨hp, he⟩ := hentry msg s hs w hw
    exact ⟨hp, he⟩

/-- A hash lookup inserts at most one new message. -/
private theorem indexedEntry_count_le {V M : Type} [DecidableEq M]
    (draw : ℕ → ProbComp V) (j : Option ℕ) (msg : M) (s : OracleState V M)
    (z : (V × ℕ) × OracleState V M)
    (hz : z ∈ support ((indexedEntry draw j msg).run s)) : z.2.count ≤ s.count + 1 := by
  cases hc : s.cache msg with
  | some v =>
    simp only [indexedEntry, StateT.run, hc, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact Nat.le_succ _
  | none =>
    simp only [indexedEntry, StateT.run, hc, support_map, Set.mem_image] at hz
    obtain ⟨v, _, rfl⟩ := hz
    exact le_rfl

/-- The number of distinct inserted messages is bounded by the sum of the direct-hash and
signing-query budgets, independently of the response distribution. -/
theorem simulateQ_indexedOracle_count_le {V M G α : Type} [DecidableEq M]
    (draw : ℕ → ProbComp V) (hash sign : V → G) (j : Option ℕ)
    (oa : OracleComp ((unifSpec + (M →ₒ G)) + (M →ₒ G)) α)
    (s : OracleState V M) (qH qS : ℕ)
    (hH : oa.IsQueryBoundP (· matches .inl (.inr _)) qH)
    (hS : oa.IsQueryBoundP (· matches .inr _) qS)
    (z : α × OracleState V M)
    (hz : z ∈ support ((simulateQ (indexedOracle draw hash sign j) oa).run s)) :
    z.2.count ≤ s.count + qH + qS := by
  induction oa using OracleComp.inductionOn generalizing s qH qS z with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    change s.count ≤ s.count + qH + qS
    omega
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hH hS
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    obtain ⟨⟨a, st⟩, ha, hz⟩ := mem_support_bind_peel _ _ hz
    rcases t with (t | msg) | msg
    · change (a, st) ∈ support
        ((fun v => (v, s)) <$> (unifSpec.query t : ProbComp _)) at ha
      obtain ⟨v, _, he⟩ := mem_support_map_peel _ _ ha
      have he' : st = s := congrArg Prod.snd he
      subst st
      exact ih a s qH qS (by simpa using hH.2 a) (by simpa using hS.2 a) z hz
    · rw [indexedOracle_run_hash] at ha
      obtain ⟨w, hw, he⟩ := mem_support_map_peel _ _ ha
      have hc := indexedEntry_count_le draw j msg s w hw
      have he' : st.count = w.2.count := congrArg (fun z => z.2.count) he
      have hb := ih a st (qH - 1) qS (by simpa using hH.2 a)
        (by simpa using hS.2 a) z hz
      have hpos : 0 < qH := by simpa using hH.1
      omega
    · rw [indexedOracle_run_sign] at ha
      obtain ⟨w, hw, he⟩ := mem_support_map_peel _ _ ha
      have hc := indexedEntry_count_le draw j msg s w hw
      have he' : st.count = w.2.count := congrArg (fun z => z.2.count) he
      have hb := ih a st qH (qS - 1) (by simpa using hH.2 a)
        (by simpa using hS.2 a) z hz
      have hpos : 0 < qS := by simpa using hS.1
      omega

end BLS
