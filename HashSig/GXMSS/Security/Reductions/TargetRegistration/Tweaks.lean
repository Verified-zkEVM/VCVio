/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.TargetRegistration.Chains

import HashSig.GXMSS.Security.Reductions.TargetRegistration.Basic

/-!
# Tree tweak freshness and target capacities
-/

public section

namespace GXMSS.Reductions

open OracleComp OracleSpec TweakableHash

variable {PP T X H M R : Type} {h w v : ℕ}

private def merkleTweaks (hash : HashInstance PP T X H h w v) :
    (z t : ℕ) → List T
  | 0, t =>
      if ht : t < 2 ^ h then [hash.treeTweak (0, ⟨t, ht⟩)] else []
  | z + 1, t =>
      let registered := merkleTweaks hash z (2 * t) ++ merkleTweaks hash z (2 * t + 1)
      if hz : z + 1 < h + 1 then
        if ht : t < 2 ^ h then
          registered ++ [hash.treeTweak (⟨z + 1, hz⟩, ⟨t, ht⟩)]
        else registered
      else registered

private theorem mem_merkleTweaks_bounds
    (hash : HashInstance PP T X H h w v) (z t : ℕ)
    (hz : z ≤ h) (ht : (t + 1) * 2 ^ z ≤ 2 ^ h) {q : T}
    (hq : q ∈ merkleTweaks hash z t) :
    ∃ (level : Fin (h + 1)) (index : Fin (2 ^ h)),
      q = hash.treeTweak (level, index) ∧ level.val ≤ z ∧
      t * 2 ^ z ≤ index.val * 2 ^ level.val ∧
      (index.val + 1) * 2 ^ level.val ≤ (t + 1) * 2 ^ z := by
  induction z generalizing t with
  | zero =>
      have hindex : t < 2 ^ h := by simpa using ht
      rw [merkleTweaks, dite_eq_left hindex] at hq
      simp only [List.mem_singleton] at hq
      subst q
      exact ⟨0, ⟨t, hindex⟩, rfl, by simp, by simp, by simp⟩
  | succ z ih =>
      have hpow : 2 ^ (z + 1) = 2 ^ z * 2 := Nat.pow_succ _ _
      have hp : 0 < 2 ^ z := by positivity
      have hleft : (2 * t + 1) * 2 ^ z ≤ 2 ^ h := by
        rw [hpow] at ht
        nlinarith
      have hright : (2 * t + 1 + 1) * 2 ^ z ≤ 2 ^ h := by
        rw [hpow] at ht
        nlinarith
      have hlevel : z + 1 < h + 1 := by omega
      have hindex : t < 2 ^ h := (PerfectMerkleTree.subtree_legal hz ht).2
      rw [merkleTweaks, dite_eq_left hlevel, dite_eq_left hindex] at hq
      simp only [List.mem_append, List.mem_singleton] at hq
      rcases hq with (hq | hq) | hq
      · obtain ⟨level, index, rfl, hlevelBound, hlower, hupper⟩ :=
          ih (2 * t) (by omega) hleft hq
        refine ⟨level, index, rfl, by omega, ?_, ?_⟩
        · rw [hpow]
          nlinarith
        · rw [hpow]
          nlinarith
      · obtain ⟨level, index, rfl, hlevelBound, hlower, hupper⟩ :=
          ih (2 * t + 1) (by omega) hright hq
        refine ⟨level, index, rfl, by omega, ?_, ?_⟩
        · rw [hpow]
          nlinarith
        · rw [hpow]
          nlinarith
      · subst q
        refine ⟨⟨z + 1, hlevel⟩, ⟨t, hindex⟩, rfl, by simp, ?_, ?_⟩
        · simp
        · simp

private theorem merkleTweaks_nodup
    (hash : HashInstance PP T X H h w v) (z t : ℕ)
    (hz : z ≤ h) (ht : (t + 1) * 2 ^ z ≤ 2 ^ h) :
    (merkleTweaks hash z t).Nodup := by
  induction z generalizing t with
  | zero =>
      have hindex : t < 2 ^ h := by simpa using ht
      simp [merkleTweaks, hindex]
  | succ z ih =>
      have hpow : 2 ^ (z + 1) = 2 ^ z * 2 := Nat.pow_succ _ _
      have hp : 0 < 2 ^ z := by positivity
      have hleft : (2 * t + 1) * 2 ^ z ≤ 2 ^ h := by
        rw [hpow] at ht
        nlinarith
      have hright : (2 * t + 1 + 1) * 2 ^ z ≤ 2 ^ h := by
        rw [hpow] at ht
        nlinarith
      have hlevel : z + 1 < h + 1 := by omega
      have hindex : t < 2 ^ h := (PerfectMerkleTree.subtree_legal hz ht).2
      rw [merkleTweaks, dite_eq_left hlevel, dite_eq_left hindex,
        List.nodup_append]
      refine ⟨?_, by simp, ?_⟩
      · rw [List.nodup_append]
        refine ⟨ih (2 * t) (by omega) hleft,
          ih (2 * t + 1) (by omega) hright, ?_⟩
        intro a ha b hb hab
        obtain ⟨levelA, indexA, haEq, _, _, haUpper⟩ :=
          mem_merkleTweaks_bounds hash z (2 * t) (by omega) hleft ha
        obtain ⟨levelB, indexB, hbEq, _, hbLower, _⟩ :=
          mem_merkleTweaks_bounds hash z (2 * t + 1) (by omega) hright hb
        rw [haEq, hbEq] at hab
        have haddress := hash.treeTweak.injective hab
        have hlevelEq : levelA = levelB := congrArg Prod.fst haddress
        have hindexEq : indexA = indexB := congrArg Prod.snd haddress
        subst levelB
        subst indexB
        have hpLevel : 0 < 2 ^ levelA.val := by positivity
        nlinarith
      · intro a ha b hb hab
        simp only [List.mem_singleton] at hb
        rw [hb] at hab
        simp only [List.mem_append] at ha
        rcases ha with ha | ha
        · obtain ⟨level, index, haEq, hlevelBound, _, _⟩ :=
            mem_merkleTweaks_bounds hash z (2 * t) (by omega) hleft ha
          rw [haEq] at hab
          have haddress := hash.treeTweak.injective hab
          have hlevelEq : level.val = z + 1 := congrArg (fun address => address.1.val) haddress
          omega
        · obtain ⟨level, index, haEq, hlevelBound, _, _⟩ :=
            mem_merkleTweaks_bounds hash z (2 * t + 1) (by omega) hright ha
          rw [haEq] at hab
          have haddress := hash.treeTweak.injective hab
          have hlevelEq : level.val = z + 1 := congrArg (fun address => address.1.val) haddress
          omega

private theorem tweakFresh_after_prefix
    (history before after : List (T × X)) (target : T × X)
    (hdisjoint : ∀ q ∈ history, ∀ r ∈ before ++ target :: after, q.1 ≠ r.1)
    (hnodup : ((before ++ target :: after).map Prod.fst).Nodup) :
    TweakFresh Prod.fst (history ++ before) [] target.1 := by
  rw [TweakFresh, not_tweakReserved_iff]
  constructor
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with hq | hq
    · exact hdisjoint q hq target (by simp)
    · have hall := List.nodup_append.mp (by simpa [List.map_append] using hnodup)
      obtain ⟨_, _, hseparate⟩ := hall
      exact hseparate q.1 (List.mem_map.mpr ⟨q, hq, rfl⟩) target.1 (by simp)
  · simp

/-- The Merkle problem's doubled budget covers all chain targets and all full-tree targets.
The positive-chain-count premise is exactly the existing Merkle reduction boundary. -/
theorem merkleProblem_capacity (hash : HashInstance PP T X H h w v) (hv : 0 < v) :
    (2 ^ h) * v * (2 ^ w - 1) + (2 ^ (h + 1) - 1) ≤
      (merkleTCRProblem hash).numTargets := by
  change (2 ^ h) * v * (2 ^ w - 1) + (2 ^ (h + 1) - 1) ≤
    2 * (2 ^ h) * v * 2 ^ w
  rw [pow_succ]
  have hh : 0 < 2 ^ h := by positivity
  have hw : 0 < 2 ^ w := by positivity
  have hsplit : 2 ^ w = (2 ^ w - 1) + 1 := by omega
  have hchain : (2 ^ h) * v * (2 ^ w - 1) ≤
      2 * (2 ^ h) * v * (2 ^ w - 1) := by
    ring_nf
    omega
  have htree : 2 * (2 ^ h) ≤ 2 * (2 ^ h) * v := by nlinarith
  calc
    (2 ^ h) * v * (2 ^ w - 1) + (2 ^ h * 2 - 1) ≤
        (2 ^ h) * v * (2 ^ w - 1) + 2 * (2 ^ h) := by omega
    _ ≤ 2 * (2 ^ h) * v * (2 ^ w - 1) + 2 * (2 ^ h) * v :=
      Nat.add_le_add hchain htree
    _ = 2 * (2 ^ h) * v * ((2 ^ w - 1) + 1) := by ring
    _ = 2 * (2 ^ h) * v * 2 ^ w := by rw [← hsplit]

/-- Membership simultaneously supplies the registered index's length bound, exact lookup, and
capacity bound. -/
theorem registeredIndex_spec [DecidableEq T] [DecidableEq X]
    (history : List (T × X)) (tweak : T) (input : X) (capacity : ℕ)
    (hmem : (tweak, input) ∈ history) (hlen : history.length ≤ capacity) :
    registeredIndex history tweak input < history.length ∧
      history[registeredIndex history tweak input]? = some (tweak, input) ∧
      registeredIndex history tweak input < capacity := by
  exact ⟨registeredIndex_lt_length_of_mem history tweak input hmem,
    registeredIndex_lookup_of_mem history tweak input hmem,
    registeredIndex_lt_capacity_of_mem history tweak input capacity hmem hlen⟩

end GXMSS.Reductions
