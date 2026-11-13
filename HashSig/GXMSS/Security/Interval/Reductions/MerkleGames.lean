/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Scheme
public import HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
public import HashSig.GXMSS.Security.Interval.Auxiliary.Interaction
public import HashSig.GXMSS.Security.Interval.Auxiliary.MerkleWitnesses
public import HashSig.GXMSS.Security.Reductions.TargetRegistration.Tweaks
import HashSig.GXMSS.Security.Reductions.TargetRegistration.Basic
import all HashSig.GXMSS.Security.Reductions.TargetRegistration.Chains
import all HashSig.GXMSS.Security.Reductions.TargetRegistration.Tweaks

/-!
# Pruned interval Merkle target registration
-/

public section

namespace GXMSS.Interval.Unforgeability

open OracleComp OracleSpec TweakableHash GXMSS.IntervalMerkle GXMSS.Reductions IncomparableEncoding

variable {PP T X H M R : Type} {h w v : ℕ}

private def merkleCandidateWins [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (history : List (T × X)) (candidate : ℕ × X) : Bool :=
  match history[candidate.1]? with
  | none => false
  | some (t, first) =>
    decide (candidate.2 ≠ first ∧
      (HashInstance.thf hash).eval pp t candidate.2 =
        (HashInstance.thf hash).eval pp t first)

/-- Pure left/right/parent schedule with the exact hash inputs of the mixed tree. -/
private def prunedTargetRun (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H) (fallback : H) :
    (z t : ℕ) → H × List (T × X)
  | 0, t =>
      if hf : Subtree.IsInactiveFrontier I 0 t then
        (frontierValue I fillers 0 t hf, [])
      else if ht : t < 2 ^ h then
        let ep : Epoch h := ⟨t, ht⟩
        let target := (P.treeTweak (0, ep), P.vectorInput (endpoints ep))
        let thf := P.thf
        (thf.eval pp target.1 target.2, [target])
      else (fallback, [])
  | z + 1, t =>
      if hf : Subtree.IsInactiveFrontier I (z + 1) t then
        (frontierValue I fillers (z + 1) t hf, [])
      else
        let leftRun := prunedTargetRun P I pp endpoints fillers fallback z (2 * t)
        let rightRun := prunedTargetRun P I pp endpoints fillers fallback z (2 * t + 1)
        let registered := leftRun.2 ++ rightRun.2
        if hz : z + 1 < h + 1 then
          if ht : t < 2 ^ h then
            let target := (P.treeTweak (⟨z + 1, hz⟩, ⟨t, ht⟩),
              P.pairInput (leftRun.1, rightRun.1))
            let thf := P.thf
            (thf.eval pp target.1 target.2, registered ++ [target])
          else (fallback, registered)
        else (fallback, registered)

/-- The original challenge program, terminating at every inactive frontier. -/
private def tcrPrunedRoot (P : HashInstance PP T X H h w v) (targets : ℕ) (I : Interval h)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H) (fallback : H) :
    (z t : ℕ) → TCRSetupM P targets H
  | 0, t =>
      if hf : Subtree.IsInactiveFrontier I 0 t then
        pure (frontierValue I fillers 0 t hf)
      else if ht : t < 2 ^ h then
        tcrEval P targets (P.treeTweak (0, ⟨t, ht⟩))
          (P.vectorInput (endpoints ⟨t, ht⟩)) fallback
      else pure fallback
  | z + 1, t =>
      if hf : Subtree.IsInactiveFrontier I (z + 1) t then
        pure (frontierValue I fillers (z + 1) t hf)
      else do
        let left ← tcrPrunedRoot P targets I endpoints fillers fallback z (2 * t)
        let right ← tcrPrunedRoot P targets I endpoints fillers fallback z (2 * t + 1)
        if hz : z + 1 < h + 1 then
          if ht : t < 2 ^ h then
            tcrEval P targets (P.treeTweak (⟨z + 1, hz⟩, ⟨t, ht⟩))
              (P.pairInput (left, right)) fallback
          else pure fallback
        else pure fallback

/-- Frontier nodes contribute zero targets; every other legal node contributes one. -/
private def prunedCount (I : Interval h) : (z t : ℕ) → ℕ
  | 0, t => if Subtree.IsInactiveFrontier I 0 t then 0 else 1
  | z + 1, t => if Subtree.IsInactiveFrontier I (z + 1) t then 0 else
      prunedCount I z (2 * t) + prunedCount I z (2 * t + 1) + 1

private theorem prunedCount_le (I : Interval h) (z t : ℕ) :
    prunedCount I z t ≤ 2 ^ (z + 1) - 1 := by
  induction z generalizing t with
  | zero => simp only [prunedCount]; split <;> norm_num
  | succ z ih =>
      have hl := ih (2 * t)
      have hr := ih (2 * t + 1)
      have hp : 0 < 2 ^ (z + 1) := by positivity
      simp only [prunedCount]
      split
      · omega
      · rw [pow_succ]
        omega

private theorem prunedTargetRun_tweaks_sublist
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H) (fallback : H) (z t : ℕ) :
    List.Sublist (List.map Prod.fst
      (prunedTargetRun P I pp endpoints fillers fallback z t).2) (merkleTweaks P z t) := by
  induction z generalizing t with
  | zero =>
      simp only [prunedTargetRun, merkleTweaks]
      split
      · simp
      · split <;> simp
  | succ z ih =>
      have hl := ih (2 * t)
      have hr := ih (2 * t + 1)
      simp only [prunedTargetRun]
      split
      · simp
      · simp only [merkleTweaks]
        split
        · split
          · simpa only [List.map_append, List.map_singleton] using
              (List.Sublist.append (List.Sublist.append hl hr) (List.Sublist.refl [_]))
          · simpa only [List.map_append] using List.Sublist.append hl hr
        · simpa only [List.map_append] using List.Sublist.append hl hr

private theorem prunedTargetRun_legal
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H) (fallback : H)
    (z t : ℕ) (hz : z ≤ h) (ht : (t + 1) * 2 ^ z ≤ 2 ^ h) :
    let (value, registered) := prunedTargetRun P I pp endpoints fillers fallback z t
    value = prunedRoot P I pp endpoints fillers z t ∧ registered.length = prunedCount I z t := by
  induction z generalizing t with
  | zero =>
      have ht' : t < 2 ^ h := by simpa using ht
      by_cases hf : Subtree.IsInactiveFrontier I 0 t
      · simp [prunedTargetRun, prunedRoot, prunedCount, hf]
      · simp [prunedTargetRun, prunedRoot, prunedCount, leaf, hf, ht', HashInstance.leafHash]
  | succ z ih =>
      have hpow : 2 ^ (z + 1) = 2 ^ z * 2 := Nat.pow_succ _ _
      have hp : 0 < 2 ^ z := by positivity
      have hleft : (2 * t + 1) * 2 ^ z ≤ 2 ^ h := by rw [hpow] at ht; nlinarith
      have hright : (2 * t + 1 + 1) * 2 ^ z ≤ 2 ^ h := by rw [hpow] at ht; nlinarith
      have hlevel : z + 1 < h + 1 := by omega
      have hindex : t < 2 ^ h := (PerfectMerkleTree.subtree_legal hz ht).2
      have hl := ih (2 * t) (by omega) hleft
      have hr := ih (2 * t + 1) (by omega) hright
      dsimp only at hl hr
      by_cases hf : Subtree.IsInactiveFrontier I (z + 1) t
      · simp [prunedTargetRun, prunedRoot, prunedCount, hf]
      · simp [prunedTargetRun, prunedRoot, prunedCount, hf, hlevel, hindex,
          node, HashInstance.nodeHash, hl, hr, Nat.add_assoc]

/-- Freshness is inherited from the original addressed complete traversal. -/
private theorem prunedTargets_nodup
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H) (fallback : H) :
    (List.map Prod.fst (prunedTargetRun P I pp endpoints fillers fallback h 0).2).Nodup :=
  (merkleTweaks_nodup P h 0 le_rfl (by simp)).sublist
    (prunedTargetRun_tweaks_sublist P I pp endpoints fillers fallback h 0)

private theorem endpointTargets_prunedTargets_disjoint
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (starts endpoints : Epoch h → Fin v → H) (fillers : Fillers I H) (fallback : H) :
    ∀ q ∈ endpointTargets P pp starts,
      ∀ r ∈ (prunedTargetRun P I pp endpoints fillers fallback h 0).2, q.1 ≠ r.1 := by
  intro q hq r hr
  simp only [endpointTargets, List.mem_flatten, List.mem_ofFn] at hq
  obtain ⟨epochTargets, ⟨ep, hepochTargets⟩, hq⟩ := hq
  rw [← hepochTargets] at hq
  simp only [List.mem_flatten, List.mem_ofFn] at hq
  obtain ⟨chain, ⟨i, hchain⟩, hq⟩ := hq
  rw [← hchain] at hq
  simp only [chainTargets, List.mem_ofFn] at hq
  obtain ⟨j, rfl⟩ := hq
  have hrTweak : r.1 ∈ merkleTweaks P h 0 :=
    (prunedTargetRun_tweaks_sublist P I pp endpoints fillers fallback h 0).subset
      (List.mem_map.mpr ⟨r, hr, rfl⟩)
  obtain ⟨level, index, hrEq, _, _, _⟩ :=
    mem_merkleTweaks_bounds P h 0 le_rfl (by simp) hrTweak
  rw [hrEq]
  exact P.chain_ne_tree _ _

private theorem tcrPrunedRootAt_run [DecidableEq T]
    (P : HashInstance PP T X H h w v) (targets : ℕ) (I : Interval h) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H) (fallback : H)
    (history before after : List (T × X)) (z t : ℕ)
    (hz : z ≤ h) (ht : (t + 1) * 2 ^ z ≤ 2 ^ h)
    (hcap : history.length + (before ++
      (prunedTargetRun P I pp endpoints fillers fallback z t).2 ++ after).length ≤ targets)
    (hdisjoint : ∀ q ∈ history,
      ∀ r ∈ before ++ (prunedTargetRun P I pp endpoints fillers fallback z t).2 ++ after,
        q.1 ≠ r.1)
    (hnodup : ((before ++ (prunedTargetRun P I pp endpoints fillers fallback z t).2 ++ after).map
      Prod.fst).Nodup) :
    let run := prunedTargetRun P I pp endpoints fillers fallback z t
    ((simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone P.thf targets) pp)
      ((tcrPrunedRoot P targets I endpoints fillers fallback z t).run
        (history ++ before))).run (history ++ before, [])) =
      pure (((run.1, history ++ before ++ run.2), history ++ before ++ run.2, [])) := by
  dsimp only
  induction z generalizing t before after with
  | zero =>
      by_cases hf : Subtree.IsInactiveFrontier I 0 t
      · simp [tcrPrunedRoot, prunedTargetRun, hf]
      · have ht' : t < 2 ^ h := by simpa using ht
        let target := (P.treeTweak (0, ⟨t, ht'⟩), P.vectorInput (endpoints ⟨t, ht'⟩))
        have hrun : (prunedTargetRun P I pp endpoints fillers fallback 0 t).2 = [target] := by
          simp [prunedTargetRun, hf, ht', target]
        have hbelow : (history ++ before).length < targets := by
          rw [hrun] at hcap
          simp only [List.length_append, List.length_cons, List.length_nil] at hcap ⊢
          omega
        have hfresh : TweakFresh Prod.fst (history ++ before) [] target.1 := by
          apply tweakFresh_after_prefix history before after target
          · simpa [hrun, List.append_assoc] using hdisjoint
          · simpa [hrun, List.append_assoc] using hnodup
        simp only [tcrPrunedRoot, dite_eq_right hf, dite_eq_left ht']
        rw [tcrEval_run_of_fresh P targets pp target.1 target.2 fallback
          (history ++ before) hbelow hfresh]
        simp [target, prunedTargetRun, hf, ht', List.append_assoc]
  | succ z ih =>
      by_cases hf : Subtree.IsInactiveFrontier I (z + 1) t
      · simp [tcrPrunedRoot, prunedTargetRun, hf]
      · have hpow : 2 ^ (z + 1) = 2 ^ z * 2 := Nat.pow_succ _ _
        have hp : 0 < 2 ^ z := by positivity
        have hleft : (2 * t + 1) * 2 ^ z ≤ 2 ^ h := by rw [hpow] at ht; nlinarith
        have hright : (2 * t + 1 + 1) * 2 ^ z ≤ 2 ^ h := by rw [hpow] at ht; nlinarith
        have hlevel : z + 1 < h + 1 := by omega
        have hindex : t < 2 ^ h := (PerfectMerkleTree.subtree_legal hz ht).2
        let leftRun := prunedTargetRun P I pp endpoints fillers fallback z (2 * t)
        let rightRun := prunedTargetRun P I pp endpoints fillers fallback z (2 * t + 1)
        let target := (P.treeTweak (⟨z + 1, hlevel⟩, ⟨t, hindex⟩),
          P.pairInput (leftRun.1, rightRun.1))
        have hrun : (prunedTargetRun P I pp endpoints fillers fallback (z + 1) t).2 =
            leftRun.2 ++ rightRun.2 ++ [target] := by
          simp [prunedTargetRun, hf, hlevel, hindex, leftRun, rightRun, target]
        have hleftRun := ih (t := 2 * t) (before := before)
          (after := rightRun.2 ++ target :: after) (hz := by omega) (ht := hleft)
        have hleftExec := hleftRun
          (by simpa [hrun, List.append_assoc] using hcap)
          (by simpa [hrun, List.append_assoc] using hdisjoint)
          (by simpa [hrun, List.append_assoc] using hnodup)
        have hrightRun := ih (t := 2 * t + 1) (before := before ++ leftRun.2)
          (after := target :: after) (hz := by omega) (ht := hright)
        have hrightExec := hrightRun
          (by simpa [hrun, List.append_assoc] using hcap)
          (by simpa [hrun, List.append_assoc] using hdisjoint)
          (by simpa [hrun, List.append_assoc] using hnodup)
        have hbelow : (history ++ before ++ leftRun.2 ++ rightRun.2).length < targets := by
          rw [hrun] at hcap
          simp only [List.length_append, List.length_cons, List.length_nil] at hcap ⊢
          omega
        have hfresh : TweakFresh Prod.fst
            (history ++ before ++ leftRun.2 ++ rightRun.2) [] target.1 := by
          simpa only [List.append_assoc] using
            (tweakFresh_after_prefix history (before ++ leftRun.2 ++ rightRun.2) after target
              (by simpa [hrun, List.append_assoc] using hdisjoint)
              (by simpa [hrun, List.append_assoc] using hnodup))
        simp only [tcrPrunedRoot, dite_eq_right hf, StateT.run_bind, simulateQ_bind]
        rw [hleftExec]
        simp only [pure_bind]
        rw [List.append_assoc history before leftRun.2]
        rw [hrightExec]
        simp only [pure_bind]
        rw [dite_eq_left hlevel, dite_eq_left hindex]
        rw [← List.append_assoc history before leftRun.2]
        rw [tcrEval_run_of_fresh P targets pp target.1 target.2 fallback
          (history ++ before ++ leftRun.2 ++ rightRun.2) hbelow hfresh]
        simp [leftRun, rightRun, target, prunedTargetRun, hf, hlevel, hindex, List.append_assoc]

private theorem prunedTargetRun_fallback_irrelevant
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H) (fallback₁ fallback₂ : H)
    (z t : ℕ) (hz : z ≤ h) (ht : (t + 1) * 2 ^ z ≤ 2 ^ h) :
    prunedTargetRun P I pp endpoints fillers fallback₁ z t =
      prunedTargetRun P I pp endpoints fillers fallback₂ z t := by
  induction z generalizing t with
  | zero =>
      have ht' : t < 2 ^ h := by simpa using ht
      by_cases hf : Subtree.IsInactiveFrontier I 0 t
      · simp [prunedTargetRun, hf]
      · simp [prunedTargetRun, hf, ht']
  | succ z ih =>
      have hpow : 2 ^ (z + 1) = 2 ^ z * 2 := Nat.pow_succ _ _
      have hp : 0 < 2 ^ z := by positivity
      have hleft : (2 * t + 1) * 2 ^ z ≤ 2 ^ h := by rw [hpow] at ht; nlinarith
      have hright : (2 * t + 1 + 1) * 2 ^ z ≤ 2 ^ h := by rw [hpow] at ht; nlinarith
      have hlevel : z + 1 < h + 1 := by omega
      have hindex : t < 2 ^ h := (PerfectMerkleTree.subtree_legal hz ht).2
      simp only [prunedTargetRun]
      split
      · rfl
      · simp only [ih (2 * t) (by omega) hleft, ih (2 * t + 1) (by omega) hright]

/-- The deterministic pruned schedule depends on endpoints and the retained fillers only. -/
private def prunedTargets (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H) : List (T × X) :=
  (prunedTargetRun P I pp endpoints fillers (P.leafHash pp 0 (endpoints 0)) h 0).2

private theorem prunedTargetRun_full
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H) (fallback : H) :
    prunedTargetRun P I pp endpoints fillers fallback h 0 =
      (GXMSS.IntervalMerkle.root P I pp endpoints fillers, prunedTargets P I pp endpoints fillers)
          := by
  apply Prod.ext
  · have hv := (prunedTargetRun_legal P I pp endpoints fillers fallback h 0
        le_rfl (by simp)).1
    exact hv.trans (prunedRoot_eq_subtreeRoot P I pp endpoints fillers h 0)
  · change (prunedTargetRun P I pp endpoints fillers fallback h 0).2 =
      prunedTargets P I pp endpoints fillers
    simpa only [prunedTargets] using congrArg Prod.snd
      (prunedTargetRun_fallback_irrelevant P I pp endpoints fillers
        fallback (P.leafHash pp 0 (endpoints 0)) h 0 le_rfl (by simp))

private theorem prunedTargets_length
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H) :
    (prunedTargets P I pp endpoints fillers).length = prunedCount I h 0 := by
  exact (prunedTargetRun_legal P I pp endpoints fillers
    (P.leafHash pp 0 (endpoints 0)) h 0 le_rfl (by simp)).2

/-- The actual interpreted traversal preserves both accepted histories separately. -/
private theorem tcrPrunedRoot_run [DecidableEq T]
    (P : HashInstance PP T X H h w v) (targets : ℕ) (I : Interval h) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H) (fallback : H)
    (history : List (T × X))
    (hcap : history.length + (prunedTargets P I pp endpoints fillers).length ≤ targets)
    (hdisjoint : ∀ q ∈ history, ∀ r ∈ prunedTargets P I pp endpoints fillers,
      q.1 ≠ r.1) :
    ((simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone P.thf targets) pp)
      ((tcrPrunedRoot P targets I endpoints fillers fallback h 0).run history)).run
        (history, [])) =
      pure (((GXMSS.IntervalMerkle.root P I pp endpoints fillers,
        history ++ prunedTargets P I pp endpoints fillers),
        history ++ prunedTargets P I pp endpoints fillers, [])) := by
  have hfull := prunedTargetRun_full P I pp endpoints fillers fallback
  have hnodup := prunedTargets_nodup P I pp endpoints fillers fallback
  rw [hfull] at hnodup
  have hexec := tcrPrunedRootAt_run P targets I pp endpoints fillers fallback history [] [] h 0
    le_rfl (by simp)
    (by simpa [hfull] using hcap)
    (by simpa [hfull] using hdisjoint)
    (by simpa [hfull] using hnodup)
  simpa [hfull] using hexec

private def tcrIntervalCore (P : HashInstance PP T X H h w v) (targets : ℕ) (I : Interval h)
    (starts : Epoch h → Fin v → H) (fillers : Fillers I H) (fallback : H) :
    TCRSetupM P targets ((Epoch h → Fin v → H) × H) := do
  let endpoints ← tcrEndpoints P targets starts fallback
  let root ← tcrPrunedRoot P targets I endpoints fillers fallback h 0
  return (endpoints, root)

/-- Fixed samples give the ordinary endpoints, mixed root, identical C++Q histories,
and an empty collection history in the actual original challenge oracle. -/
private theorem tcrIntervalCore_run [DecidableEq T]
    (P : HashInstance PP T X H h w v) (targets : ℕ) (I : Interval h) (pp : PP)
    (starts : Epoch h → Fin v → H) (fillers : Fillers I H) (fallback : H)
    (hcap : (2 ^ h) * v * (2 ^ w - 1) + prunedCount I h 0 ≤ targets) :
    let endpoints := GXMSS.endpoints P pp starts
    let registered := endpointTargets P pp starts ++ prunedTargets P I pp endpoints fillers
    ((simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone P.thf targets) pp)
      ((tcrIntervalCore P targets I starts fillers fallback).run [])).run ([], [])) =
      pure ((((endpoints, GXMSS.IntervalMerkle.root P I pp endpoints fillers), registered),
        registered, [])) := by
  dsimp only
  have hchain : (2 ^ h) * v * (2 ^ w - 1) ≤ targets := by omega
  have hlengths : (endpointTargets P pp starts).length +
      (prunedTargets P I pp (GXMSS.endpoints P pp starts) fillers).length ≤ targets := by
    simpa only [endpointTargets_length, prunedTargets_length] using hcap
  have hdisjoint := endpointTargets_prunedTargets_disjoint P I pp starts
    (GXMSS.endpoints P pp starts) fillers (P.leafHash pp 0 (GXMSS.endpoints P pp starts 0))
  change ∀ q ∈ endpointTargets P pp starts,
    ∀ r ∈ prunedTargets P I pp (GXMSS.endpoints P pp starts) fillers, q.1 ≠ r.1 at hdisjoint
  simp only [tcrIntervalCore, StateT.run_bind, simulateQ_bind]
  rw [tcrEndpoints_run_empty P targets pp starts fallback hchain]
  simp only [pure_bind]
  rw [tcrPrunedRoot_run P targets I pp (GXMSS.endpoints P pp starts) fillers fallback
    (endpointTargets P pp starts) hlengths hdisjoint]
  simp

private theorem prunedProblem_capacity (P : HashInstance PP T X H h w v) (I : Interval h)
    (hv : 0 < v) :
    (2 ^ h) * v * (2 ^ w - 1) + prunedCount I h 0 ≤ (merkleTCRProblem P).numTargets :=
  (Nat.add_le_add_left (prunedCount_le I h 0) _).trans (merkleProblem_capacity P hv)

private structure IntervalTCRState (PP T X H : Type) (h v : ℕ) (I : Interval h) where
  complete : TCRKeyState PP T X H h v
  fillers : Fillers I H

private noncomputable def tcrIntervalSetup [SampleableType H]
    (P : HashInstance PP T X H h w v) (targets : ℕ) (I : Interval h) :
    OracleComp (unifSpec + (SM_DT_TCR_challengeSpec T X H +
      collectionSpec (SM_DT_TCR_Problem.standalone P.thf targets).thColl))
      (IntervalTCRState PP T X H h v I) := do
  let fallback ← OracleComp.liftComp ($ᵗ H) _
  let starts ← OracleComp.liftComp (GXMSS.sampleStarts H h v) _
  let fillers ← OracleComp.liftComp (sampleFillers I H) _
  let ((endpoints, root), registered) ←
    (tcrIntervalCore P targets I starts fillers fallback).run []
  return ⟨⟨starts, endpoints, root, registered, fallback⟩, fillers⟩

private theorem tcrIntervalSetup_run [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v) (targets : ℕ) (I : Interval h) (pp : PP)
    (hcap : (2 ^ h) * v * (2 ^ w - 1) + prunedCount I h 0 ≤ targets) :
    (simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone P.thf targets) pp)
      (tcrIntervalSetup P targets I)).run ([], []) = (do
        let fallback ← ($ᵗ H : ProbComp H)
        let starts ← GXMSS.sampleStarts H h v
        let fillers ← sampleFillers I H
        let endpoints := GXMSS.endpoints P pp starts
        let registered := endpointTargets P pp starts ++ prunedTargets P I pp endpoints fillers
        pure ((⟨⟨starts, endpoints, GXMSS.IntervalMerkle.root P I pp endpoints fillers,
          registered, fallback⟩, fillers⟩ : IntervalTCRState PP T X H h v I), registered, [])) := by
  have hunif {Y : Type} (oa : ProbComp Y) (state : SM_DT_TCR_State T X) :
      (simulateQ
        (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone P.thf targets) pp)
        (OracleComp.liftComp oa _)).run state = (fun value => (value, state)) <$> oa := by
    rw [SM_DT_TCR_oracles, QueryImpl.simulateQ_add_liftComp_left, simulateQ_liftTarget,
      simulateQ_ofLift_eq_self]
    simp
  simp only [tcrIntervalSetup, simulateQ_bind, StateT.run_bind]
  rw [hunif, bind_map_left]
  apply bind_congr
  intro fallback
  rw [hunif, bind_map_left]
  apply bind_congr
  intro starts
  rw [hunif, bind_map_left]
  apply bind_congr
  intro fillers
  rw [tcrIntervalCore_run P targets I pp starts fillers fallback hcap]
  simp

/-- Deterministic extraction from the entire returned adaptive interval view. -/
private def intervalMerkleCandidate [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w))
    (I : Interval h) (state : IntervalTCRState PP T X H h v I) (pp : PP)
    (out : SyncSignatureUnforgeability.ExperimentResult (GXMSS.PublicKey PP H)
      (Epoch h) M (GXMSS.Signature R H h v)) : ℕ × X :=
  let complete := state.complete
  let observed := out.2
  let forgery := observed.1
  let e := forgery.1
  let payload := forgery.2
  let msg := payload.1
  let sig := payload.2
  let fallback := (0, P.vectorInput (complete.endpoints 0))
  match enc.value pp msg sig.randomizer e with
  | none => fallback
  | some word =>
    let recovered := fun i => P.chain pp e i (word i)
      (2 ^ w - 1 - (word i).val) (sig.ots i)
    if Epoch.IsActive I e then
      match P.findMerkleCollision pp e (complete.endpoints e) recovered
          (GXMSS.IntervalMerkle.authPath P I pp complete.endpoints state.fillers e) sig.path with
      | none => fallback
      | some collision =>
          (registeredIndex complete.targets collision.tweak collision.first,
            collision.second)
    else
      match GXMSS.Interval.MerkleWitnesses.findAboveFrontier P I pp complete.endpoints
          state.fillers e recovered sig.path with
      | none => fallback
      | some (q, first, second) =>
          let level := frontierLevel I e + q
          let index := e.val / 2 ^ level
          if hl : level < h + 1 then
            if hi : index < 2 ^ h then
              let tweak := P.treeTweak (⟨level, hl⟩, ⟨index, hi⟩)
              (registeredIndex complete.targets tweak (P.pairInput first),
                P.pairInput second)
            else fallback
          else fallback

/-- The original Merkle TCR adversary with interval paths and pruned target registration. -/
noncomputable def merkleTargetCollisionAdversary [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (I : Interval h) (_hv : 0 < v)
    (A : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Epoch h) M (GXMSS.Signature R H h v)) : SM_DT_TCR_Adversary (merkleTCRProblem P) where
  State := IntervalTCRState PP T X H h v I
  choose := tcrIntervalSetup P _ I
  forge state pp := do
    let complete := state.complete
    let pk : GXMSS.PublicKey PP H := ⟨complete.root, pp⟩
    let sk : GXMSS.Interval.SecretKey PP H h v I :=
      ⟨⟨pp, complete.starts, complete.endpoints⟩, state.fillers⟩
    let out ← GXMSS.Interval.viewWithKeys P enc K I A pk sk
    return intervalMerkleCandidate P enc I state pp out

end GXMSS.Interval.Unforgeability
