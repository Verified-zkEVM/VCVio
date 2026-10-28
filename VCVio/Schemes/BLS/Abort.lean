/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Programming

/-! # The BLS signing-abort comparison

Honest signing and scalar-derived signing agree until the challenge-tagged message is
signed. The persistent abort flag permits a whole-execution comparison using the existing
stateful domination theorem, as in the Boneh–Lynn–Shacham index-guessing reduction.
-/

public section

open OracleComp OracleSpec

namespace BLS

/-- Every challenge tag in the cache belongs to the guessed insertion index. -/
private def ChallengeInv {V M : Type} (j : ℕ) (s : OracleState (Option V) M) : Prop :=
  ∀ msg i, s.cache msg = some (none, i) → i = j

/-- The empty scalar-tag cache satisfies challenge-index consistency. -/
private theorem challengeInv_empty {V M : Type} (j : ℕ) :
    ChallengeInv j (OracleState.empty : OracleState (Option V) M) := by
  simp [ChallengeInv, OracleState.empty]

private theorem tagDraw_none {V : Type} [SampleableType V] (j n : ℕ)
    (h : none ∈ support (tagDraw (V := V) j n)) : n = j := by
  by_contra hn
  simp [tagDraw, hn] at h

private theorem challengeInv_insert {V M : Type} [DecidableEq M]
    {j : ℕ} {s : OracleState (Option V) M} (hs : ChallengeInv j s)
    (msg : M) (v : Option V) (hv : v = none → s.count = j) :
    ChallengeInv j (s.insert (some j) msg v) := by
  intro n i hn
  by_cases h : n = msg
  · subst n
    simp only [OracleState.insert, QueryCache.cacheQuery_self, Option.some.injEq,
      Prod.mk.injEq] at hn
    exact hn.2.symm.trans (hv hn.1)
  · simp only [OracleState.insert, QueryCache.cacheQuery_of_ne _ _ h] at hn
    exact hs n i hn

/-- A tag lookup preserves challenge-index consistency and identifies every returned
challenge tag with the guessed slot. -/
private theorem indexedEntry_support_challengeInv {V M : Type}
    [SampleableType V] [DecidableEq M] (j : ℕ) (msg : M)
    (s : OracleState (Option V) M) (hs : ChallengeInv j s)
    (z : (Option V × ℕ) × OracleState (Option V) M)
    (hz : z ∈ support ((indexedEntry (tagDraw j) (some j) msg).run s)) :
    ChallengeInv j z.2 ∧ (z.1.1 = none → z.1.2 = j) := by
  cases hc : s.cache msg with
  | some vi =>
    obtain ⟨v, i⟩ := vi
    simp only [indexedEntry, StateT.run, hc, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨hs, fun hv => hs msg i (hv ▸ hc)⟩
  | none =>
    simp only [indexedEntry, StateT.run, hc, support_map, Set.mem_image] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    have ht : v = none → s.count = j := fun h => tagDraw_none j s.count (h ▸ hv)
    exact ⟨challengeInv_insert hs msg v ht, ht⟩

/-- Challenge-index consistency is preserved by every hash and signing query. -/
theorem indexedOracle_preserves_challengeInv {V M G : Type}
    [SampleableType V] [DecidableEq M] (hash sign : Option V → G) (j : ℕ) :
    QueryImpl.PreservesInv (indexedOracle (M := M) (tagDraw j) hash sign (some j))
      (fun s => ∀ msg i, s.cache msg = some (none, i) → i = j) := by
  intro t s hs z hz
  rcases t with (t | msg) | msg
  · change z ∈ support ((fun v => (v, s)) <$> (unifSpec.query t : ProbComp _)) at hz
    obtain ⟨_, _, rfl⟩ := mem_support_map_peel _ _ hz
    exact hs
  · rw [indexedOracle_run_hash, support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (indexedEntry_support_challengeInv j msg s hs w hw).1
  · rw [indexedOracle_run_sign, support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (indexedEntry_support_challengeInv j msg s hs w hw).1

private theorem indexedEntry_bad_eq {V M : Type} [DecidableEq M]
    (draw : ℕ → ProbComp V) (j : Option ℕ) (msg : M) (s : OracleState V M)
    (z : (V × ℕ) × OracleState V M)
    (hz : z ∈ support ((indexedEntry draw j msg).run s)) : z.2.bad = s.bad := by
  cases hc : s.cache msg with
  | some vi =>
    simp only [indexedEntry, StateT.run, hc, support_pure, Set.mem_singleton_iff] at hz
    subst z
    rfl
  | none =>
    simp only [indexedEntry, StateT.run, hc, support_map, Set.mem_image] at hz
    obtain ⟨v, _, rfl⟩ := hz
    rfl

/-- Once raised, the abort flag remains raised throughout every subsequent oracle step. -/
private theorem indexedOracle_preserves_bad {V M G : Type} [DecidableEq M]
    (draw : ℕ → ProbComp V) (hash sign : V → G) (j : Option ℕ) :
    QueryImpl.PreservesInv (indexedOracle (M := M) draw hash sign j) (fun s => s.bad = true) := by
  intro t s hs z hz
  rcases t with (t | msg) | msg
  · change z ∈ support ((fun v => (v, s)) <$> (unifSpec.query t : ProbComp _)) at hz
    obtain ⟨_, _, rfl⟩ := mem_support_map_peel _ _ hz
    exact hs
  · rw [indexedOracle_run_hash, support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (indexedEntry_bad_eq draw j msg s w hw).trans hs
  · rw [indexedOracle_run_sign, support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hb := (indexedEntry_bad_eq draw j msg s w hw).trans hs
    simp [OracleState.recordSign, hb]

/-- Signing responses may be changed on challenge tags without decreasing any event restricted
to non-aborted runs. Scalar-tagged signing responses must agree. -/
private theorem indexedOracle_dominatedUntilBad {V M G : Type}
    [SampleableType V] [DecidableEq M] (hash sign sign' : Option V → G)
    (hsign : ∀ v, sign (some v) = sign' (some v)) (j : ℕ) :
    QueryImpl.DominatedUntilBad
      (indexedOracle (M := M) (tagDraw j) hash sign (some j))
      (indexedOracle (tagDraw j) hash sign' (some j)) id (ChallengeInv j)
      (fun s => s.bad = true) := by
  intro t s hs _ Q
  rcases t with (t | msg) | msg
  · change Pr{let z ← (fun v => (v, s)) <$> (unifSpec.query t : ProbComp _)}[
        Q (z.1, id z.2) ∧ ¬z.2.bad = true] ≤
      Pr{let z ← (fun v => (v, s)) <$> (unifSpec.query t : ProbComp _)}[Q z]
    exact prEvent_mono _ _ _ fun _ h => h.1
  · rw [indexedOracle_run_hash, indexedOracle_run_hash]
    exact prEvent_mono _ _ _ fun _ h => h.1
  · rw [indexedOracle_run_sign, indexedOracle_run_sign]
    simp only [prEvent_map]
    apply prEvent_mono_of_support
    intro z hz h
    have ht := (indexedEntry_support_challengeInv j msg s hs z hz).2
    cases hc : z.1.1 with
    | some v => simpa only [id_eq, hc, hsign v] using h.1
    | none =>
      have hj := ht hc
      have hb : (z.2.recordSign (some j) msg z.1.2).bad = true := by
        simp [OracleState.recordSign, hj]
      exact False.elim (h.2 hb)

/-- The adaptive honest signing execution, restricted to non-aborted runs, is dominated by
scalar-derived signing with the same challenge-programmed hash oracle. -/
theorem prEvent_indexedOracle_and_not_bad_le {V M G α : Type}
    [SampleableType V] [DecidableEq M] (hash sign sign' : Option V → G)
    (hsign : ∀ v, sign (some v) = sign' (some v)) (j : ℕ)
    (oa : OracleComp ((unifSpec + (M →ₒ G)) + (M →ₒ G)) α)
    (P : α × OracleState (Option V) M → Prop) :
    Pr{let z ← (simulateQ (indexedOracle (tagDraw j) hash sign (some j)) oa).run
        OracleState.empty}[P z ∧ ¬z.2.bad = true] ≤
    Pr{let z ← (simulateQ (indexedOracle (tagDraw j) hash sign' (some j)) oa).run
        OracleState.empty}[P z] := by
  have h := indexedOracle_dominatedUntilBad (M := M) hash sign sign' hsign j
  exact h.prEvent_simulateQ_run_map_and_not_bad_le
      (indexedOracle_preserves_challengeInv hash sign j)
      (indexedOracle_preserves_bad (tagDraw j) hash sign (some j)) oa OracleState.empty
      (challengeInv_empty j) P

end BLS
