/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.CollisionReductions
import all HashSig.GXMSS.Security.Reductions.CollisionReductions
import all HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
import all HashSig.GXMSS.Merkle

/-!
# Honest SM-DT-TCR setup simulation

This module proves the deterministic registration and capacity facts used by the Merkle and chain
target-collision reductions.  It does not compare winning probabilities or prove a game hop.
-/

public section

namespace GXMSS.Reductions

open OracleComp OracleSpec TweakableHash

variable {PP T X H : Type} {h w v : ℕ}

/-- One fresh, below-cap honest query returns the ordinary hash value and appends the same target
to both the local registration history and the authoritative challenge history. -/
theorem tcrEval_run_of_fresh [DecidableEq T]
    (hash : HashInstance PP T X H h w v) (targets : ℕ) (pp : PP)
    (tweak : T) (input : X) (fallback : H) (history : List (T × X))
    (hlen : history.length < targets)
    (hfresh : TweakFresh Prod.fst history [] tweak) :
    ((simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
      ((tcrEval hash targets tweak input fallback).run history)).run (history, [])) =
      pure (((hash.thf.eval pp tweak input, history ++ [(tweak, input)]),
        history ++ [(tweak, input)], [])) := by
  let prob := SM_DT_TCR_Problem.standalone hash.thf targets
  have hchallenge := SM_DT_TCR_challengeOracle_run_of_fresh
    (prob := prob) (pk := pp) (t := tweak) (m := input)
    (qsChal := history) (twsColl := []) hlen hfresh
  have horacle :
      (SM_DT_TCR_oracles prob pp (.inr (.inl (tweak, input)))).run (history, []) =
        pure (some (hash.thf.eval pp tweak input), history ++ [(tweak, input)], []) := by
    change _ = pure (some (prob.th.eval pp tweak input), history ++ [(tweak, input)], [])
    simpa [SM_DT_TCR_oracles] using hchallenge
  simp [tcrEval, simulateQ_query, prob, horacle]

/-- The ordered targets of a chain prefix. Entry `j` is the input to paper step `j + 1`. -/
def chainTargets (hash : HashInstance PP T X H h w v) (pp : PP)
    (ep : Epoch h) (i : Fin v) (start : H) (s : ℕ) (hs : s ≤ 2 ^ w - 1) :
    List (T × X) :=
  List.ofFn fun j : Fin s =>
    (hash.chainTweak (ep, i, ⟨j.val, by omega⟩),
      hash.digestInput (hash.chain pp ep i 0 j.val start))

@[simp] theorem chainTargets_length (hash : HashInstance PP T X H h w v) (pp : PP)
    (ep : Epoch h) (i : Fin v) (start : H) (s : ℕ) (hs : s ≤ 2 ^ w - 1) :
    (chainTargets hash pp ep i start s hs).length = s := by
  simp [chainTargets]

theorem chainTargets_succ (hash : HashInstance PP T X H h w v) (pp : PP)
    (ep : Epoch h) (i : Fin v) (start : H) (s : ℕ)
    (hs : s + 1 ≤ 2 ^ w - 1) (hs' : s ≤ 2 ^ w - 1) :
    chainTargets hash pp ep i start (s + 1) hs =
      chainTargets hash pp ep i start s hs' ++
        [(hash.chainTweak (ep, i, ⟨s, by omega⟩),
          hash.digestInput (hash.chain pp ep i 0 s start))] := by
  unfold chainTargets
  rw [List.ofFn_succ_last]
  rfl

private theorem chainTarget_tweak_ne (hash : HashInstance PP T X H h w v)
    (ep : Epoch h) (i : Fin v) {j k : ℕ}
    (hj : j < 2 ^ w - 1) (hk : k < 2 ^ w - 1) (hne : j ≠ k) :
    hash.chainTweak (ep, i, ⟨j, hj⟩) ≠ hash.chainTweak (ep, i, ⟨k, hk⟩) := by
  intro heq
  have harg := hash.chainTweak.injective heq
  exact hne (congrArg (fun x =>
    let coordinate := x.2
    coordinate.2.val) harg)

private theorem chainTargets_fresh_next
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (ep : Epoch h) (i : Fin v) (start : H) (history : List (T × X))
    (s : ℕ) (hs : s + 1 ≤ 2 ^ w - 1)
    (hfresh : ∀ j : Fin (s + 1), ∀ q ∈ history,
      q.1 ≠ hash.chainTweak (ep, i, ⟨j.val, by omega⟩)) :
    TweakFresh Prod.fst (history ++ chainTargets hash pp ep i start s (by omega)) []
      (hash.chainTweak (ep, i, ⟨s, by omega⟩)) := by
  rw [TweakFresh, not_tweakReserved_iff]
  constructor
  · intro q hq
    simp only [List.mem_append, chainTargets, List.mem_ofFn] at hq
    rcases hq with hq | ⟨j, hjq⟩
    · exact hfresh (Fin.last s) q hq
    · rw [← hjq]
      exact chainTarget_tweak_ne hash ep i (by omega) (by omega) (by omega)
  · simp

/-- Honest chain simulation returns the ordinary chain and appends exactly its positive-step
targets, while the local and authoritative histories remain equal. -/
theorem tcrFullChain_run [DecidableEq T]
    (hash : HashInstance PP T X H h w v) (targets : ℕ) (pp : PP)
    (ep : Epoch h) (i : Fin v) (start fallback : H) (history : List (T × X))
    (s : ℕ) (hs : s ≤ 2 ^ w - 1)
    (hcap : history.length + s ≤ targets)
    (hfresh : ∀ j : Fin s, ∀ q ∈ history,
      q.1 ≠ hash.chainTweak (ep, i, ⟨j.val, by omega⟩)) :
    ((simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
      ((tcrFullChain hash targets ep i start fallback s hs).run history)).run (history, [])) =
      pure (((hash.chain pp ep i 0 s start,
        history ++ chainTargets hash pp ep i start s hs),
        history ++ chainTargets hash pp ep i start s hs, [])) := by
  induction s with
  | zero => simp [tcrFullChain, chainTargets]
  | succ s ih =>
      have hs' : s ≤ 2 ^ w - 1 := by omega
      have hcap' : history.length + s ≤ targets := by omega
      have hfresh' : ∀ j : Fin s, ∀ q ∈ history,
          q.1 ≠ hash.chainTweak (ep, i, ⟨j.val, by omega⟩) := by
        intro j
        exact hfresh j.castSucc
      have hnext := chainTargets_fresh_next hash pp ep i start history s hs hfresh
      have hbelow : (history ++ chainTargets hash pp ep i start s hs').length < targets := by
        simp only [List.length_append, chainTargets_length]
        omega
      rw [tcrFullChain]
      simp only [StateT.run_bind, simulateQ_bind]
      rw [ih hs' hcap' hfresh']
      simp only [pure_bind]
      rw [tcrEval_run_of_fresh hash targets pp _ _ fallback _ hbelow hnext]
      simp only [hash.chain_succ pp ep i 0 s start (by omega), List.append_assoc]
      rw [chainTargets_succ hash pp ep i start s hs hs']
      simp

/-- Empty-history specialization: the fallback branch is unreachable throughout an honest
bounded chain prefix. -/
theorem tcrFullChain_run_empty [DecidableEq T]
    (hash : HashInstance PP T X H h w v) (targets : ℕ) (pp : PP)
    (ep : Epoch h) (i : Fin v) (start fallback : H)
    (s : ℕ) (hs : s ≤ 2 ^ w - 1) (hcap : s ≤ targets) :
    ((simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
      ((tcrFullChain hash targets ep i start fallback s hs).run [])).run ([], [])) =
      pure (((hash.chain pp ep i 0 s start, chainTargets hash pp ep i start s hs),
        chainTargets hash pp ep i start s hs, [])) := by
  simpa using tcrFullChain_run hash targets pp ep i start fallback [] s hs (by simpa using hcap)
    (by simp)

/-- Any two fallback values give the same native computation on an honest chain prefix.  This is
an equality before observation, so it preserves returned failure and missing mass. -/
theorem tcrFullChain_fallback_irrelevant [DecidableEq T]
    (hash : HashInstance PP T X H h w v) (targets : ℕ) (pp : PP)
    (ep : Epoch h) (i : Fin v) (start fallback₁ fallback₂ : H)
    (s : ℕ) (hs : s ≤ 2 ^ w - 1) (hcap : s ≤ targets) :
    (simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
      ((tcrFullChain hash targets ep i start fallback₁ s hs).run [])).run ([], []) =
    (simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
      ((tcrFullChain hash targets ep i start fallback₂ s hs).run [])).run ([], []) := by
  rw [tcrFullChain_run_empty hash targets pp ep i start fallback₁ s hs hcap,
    tcrFullChain_run_empty hash targets pp ep i start fallback₂ s hs hcap]

/-- The depth-first family of all positive-step chain targets, ordered first by epoch and then by
chain label. This is the registration prefix produced by honest endpoint setup. -/
def endpointTargets (hash : HashInstance PP T X H h w v) (pp : PP)
    (starts : Epoch h → Fin v → H) : List (T × X) :=
  (List.ofFn fun ep : Epoch h =>
    (List.ofFn fun i : Fin v =>
      chainTargets hash pp ep i (starts ep i) (2 ^ w - 1) (by omega)).flatten).flatten

@[simp] theorem endpointTargets_length (hash : HashInstance PP T X H h w v) (pp : PP)
    (starts : Epoch h → Fin v → H) :
    (endpointTargets hash pp starts).length = (2 ^ h) * v * (2 ^ w - 1) := by
  simp [endpointTargets, List.length_flatten, List.sum_ofFn, Nat.mul_assoc]

/-- Every positive paper step of every honest chain occurs in the all-epoch endpoint traversal. -/
theorem chainTarget_mem_endpointTargets (hash : HashInstance PP T X H h w v) (pp : PP)
    (starts : Epoch h → Fin v → H) (ep : Epoch h) (i : Fin v)
    (j : Fin (2 ^ w - 1)) :
    (hash.chainTweak (ep, i, ⟨j.val, by omega⟩),
      hash.digestInput (hash.chain pp ep i 0 j.val (starts ep i))) ∈
      endpointTargets hash pp starts := by
  simp only [endpointTargets, List.mem_flatten, List.mem_ofFn]
  refine ⟨(List.ofFn fun i : Fin v =>
    chainTargets hash pp ep i (starts ep i) (2 ^ w - 1) (by omega)).flatten, ?_, ?_⟩
  · exact ⟨ep, rfl⟩
  · simp only [List.mem_flatten, List.mem_ofFn]
    refine ⟨chainTargets hash pp ep i (starts ep i) (2 ^ w - 1) (by omega), ⟨i, rfl⟩, ?_⟩
    simp [chainTargets]

private theorem tcrChainFamily_run [DecidableEq T]
    (hash : HashInstance PP T X H h w v) (targets : ℕ) (pp : PP)
    (ep : Epoch h) (starts : Fin v → H) (fallback : H)
    (n : ℕ) (labels : Fin n → Fin v) (hlabels : Function.Injective labels)
    (history : List (T × X))
    (hcap : history.length + n * (2 ^ w - 1) ≤ targets)
    (hfresh : ∀ a : Fin n, ∀ j : Fin (2 ^ w - 1), ∀ q ∈ history,
      q.1 ≠ hash.chainTweak (ep, labels a, ⟨j.val, by omega⟩)) :
    ((simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
      ((Fin.mOfFn n fun a => tcrFullChain hash targets ep (labels a) (starts (labels a))
        fallback (2 ^ w - 1) (by omega)).run history)).run (history, [])) =
      let values := fun a : Fin n =>
        hash.chain pp ep (labels a) 0 (2 ^ w - 1) (starts (labels a))
      let registered := (List.ofFn fun a =>
        chainTargets hash pp ep (labels a) (starts (labels a))
          (2 ^ w - 1) (by omega)).flatten
      pure ((values, history ++ registered), history ++ registered, []) := by
  induction n generalizing history with
  | zero =>
      simp only [Fin.mOfFn, StateT.run_pure, simulateQ_pure,
        List.ofFn_zero, List.flatten_nil, List.append_nil]
      congr
      funext a
      exact Fin.elim0 a
  | succ n ih =>
      let firstTargets := chainTargets hash pp ep (labels 0) (starts (labels 0))
        (2 ^ w - 1) (by omega)
      have hfirstCap : history.length + (2 ^ w - 1) ≤ targets := by
        simp only [Nat.succ_mul] at hcap
        omega
      have hfirstFresh : ∀ j : Fin (2 ^ w - 1), ∀ q ∈ history,
          q.1 ≠ hash.chainTweak (ep, labels 0, ⟨j.val, by omega⟩) := hfresh 0
      have htailLabels : Function.Injective (fun a : Fin n => labels a.succ) :=
        hlabels.comp (Fin.succ_injective n)
      have htailCap : (history ++ firstTargets).length + n * (2 ^ w - 1) ≤ targets := by
        simpa [firstTargets, Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hcap
      have htailFresh : ∀ a : Fin n, ∀ j : Fin (2 ^ w - 1),
          ∀ q ∈ history ++ firstTargets,
          q.1 ≠ hash.chainTweak (ep, labels a.succ, ⟨j.val, by omega⟩) := by
        intro a j q hq
        simp only [List.mem_append] at hq
        rcases hq with hq | hq
        · exact hfresh a.succ j q hq
        · simp only [firstTargets, chainTargets, List.mem_ofFn] at hq
          rcases hq with ⟨k, rfl⟩
          intro heq
          have hargs := hash.chainTweak.injective heq
          have hlabel : labels 0 = labels a.succ := congrArg (fun x =>
            let coordinate := x.2
            coordinate.1) hargs
          exact Fin.succ_ne_zero a (hlabels hlabel).symm
      rw [Fin.mOfFn]
      simp only [StateT.run_bind, simulateQ_bind]
      rw [tcrFullChain_run hash targets pp ep (labels 0) (starts (labels 0)) fallback history
        (2 ^ w - 1) (by omega) hfirstCap hfirstFresh]
      simp only [pure_bind]
      rw [ih (fun a => labels a.succ) htailLabels (history ++ firstTargets)
        htailCap htailFresh]
      simp only [List.append_assoc, StateT.run_pure, simulateQ_pure, bind_pure_comp,
        map_pure, List.ofFn_succ, List.flatten_cons, PFunctor.FreeM.pure_inj,
        Prod.mk.injEq, List.append_cancel_left_eq, List.append_cancel_right_eq,
        and_true, and_self_right]
      constructor
      · funext a
        exact Fin.cases rfl (fun _ => rfl) a
      · rfl

private theorem tcrEpochFamily_run [DecidableEq T]
    (hash : HashInstance PP T X H h w v) (targets : ℕ) (pp : PP)
    (starts : Epoch h → Fin v → H) (fallback : H)
    (n : ℕ) (epochs : Fin n → Epoch h) (hepochs : Function.Injective epochs)
    (history : List (T × X))
    (hcap : history.length + n * v * (2 ^ w - 1) ≤ targets)
    (hfresh : ∀ a : Fin n, ∀ i : Fin v, ∀ j : Fin (2 ^ w - 1), ∀ q ∈ history,
      q.1 ≠ hash.chainTweak (epochs a, i, ⟨j.val, by omega⟩)) :
    ((simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
      ((Fin.mOfFn n fun a => Fin.mOfFn v fun i =>
        tcrFullChain hash targets (epochs a) i (starts (epochs a) i)
          fallback (2 ^ w - 1) (by omega)).run history)).run (history, [])) =
      let values := fun a : Fin n => fun i : Fin v =>
        hash.chain pp (epochs a) i 0 (2 ^ w - 1) (starts (epochs a) i)
      let registered := (List.ofFn fun a =>
        (List.ofFn fun i => chainTargets hash pp (epochs a) i (starts (epochs a) i)
          (2 ^ w - 1) (by omega)).flatten).flatten
      pure ((values, history ++ registered), history ++ registered, []) := by
  induction n generalizing history with
  | zero =>
      simp only [Fin.mOfFn, StateT.run_pure, simulateQ_pure,
        List.ofFn_zero, List.flatten_nil, List.append_nil]
      congr
      funext a
      exact Fin.elim0 a
  | succ n ih =>
      let firstTargets := (List.ofFn fun i : Fin v =>
        chainTargets hash pp (epochs 0) i (starts (epochs 0) i)
          (2 ^ w - 1) (by omega)).flatten
      have hfirstCap : history.length + v * (2 ^ w - 1) ≤ targets := by
        simp only [Nat.succ_mul, Nat.add_mul] at hcap
        omega
      have hfirstFresh : ∀ i : Fin v, ∀ j : Fin (2 ^ w - 1), ∀ q ∈ history,
          q.1 ≠ hash.chainTweak (epochs 0, i, ⟨j.val, by omega⟩) := hfresh 0
      have htailEpochs : Function.Injective (fun a : Fin n => epochs a.succ) :=
        hepochs.comp (Fin.succ_injective n)
      have htailCap : (history ++ firstTargets).length + n * v * (2 ^ w - 1) ≤ targets := by
        simpa [firstTargets, List.length_flatten, List.sum_ofFn, Nat.succ_mul,
          Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcap
      have htailFresh : ∀ a : Fin n, ∀ i : Fin v, ∀ j : Fin (2 ^ w - 1),
          ∀ q ∈ history ++ firstTargets,
          q.1 ≠ hash.chainTweak (epochs a.succ, i, ⟨j.val, by omega⟩) := by
        intro a i j q hq
        simp only [List.mem_append] at hq
        rcases hq with hq | hq
        · exact hfresh a.succ i j q hq
        · simp only [firstTargets, List.mem_flatten, List.mem_ofFn] at hq
          rcases hq with ⟨chain, ⟨i₀, rfl⟩, hq⟩
          simp only [chainTargets, List.mem_ofFn] at hq
          rcases hq with ⟨k, rfl⟩
          intro heq
          have hargs := hash.chainTweak.injective heq
          have hep : epochs 0 = epochs a.succ := congrArg Prod.fst hargs
          exact Fin.succ_ne_zero a (hepochs hep).symm
      rw [Fin.mOfFn]
      simp only [StateT.run_bind, simulateQ_bind]
      rw [tcrChainFamily_run hash targets pp (epochs 0) (starts (epochs 0)) fallback v
        (fun i => i) Function.injective_id history hfirstCap hfirstFresh]
      simp only [pure_bind]
      rw [ih (fun a => epochs a.succ) htailEpochs (history ++ firstTargets)
        htailCap htailFresh]
      simp only [List.append_assoc, StateT.run_pure, simulateQ_pure, bind_pure_comp,
        map_pure, List.ofFn_succ, List.flatten_cons, PFunctor.FreeM.pure_inj,
        Prod.mk.injEq, List.append_cancel_left_eq, List.append_cancel_right_eq,
        and_true, and_self_right]
      constructor
      · funext a
        exact Fin.cases rfl (fun _ => rfl) a
      · rfl

/-- The pure endpoint family returned by an accepted honest setup is exactly the ordinary GXMSS
endpoint function. -/
theorem endpointFamily_eq (hash : HashInstance PP T X H h w v) (pp : PP)
    (starts : Epoch h → Fin v → H) :
    (fun ep i => hash.chain pp ep i 0 (2 ^ w - 1) (starts ep i)) =
      GXMSS.endpoints hash pp starts := by
  rfl

/-- Honest endpoint setup returns the ordinary all-epoch endpoint family and registers exactly the
positive chain targets in epoch-major order, with identical local and authoritative histories. -/
theorem tcrEndpoints_run_empty [DecidableEq T]
    (hash : HashInstance PP T X H h w v) (targets : ℕ) (pp : PP)
    (starts : Epoch h → Fin v → H) (fallback : H)
    (hcap : (2 ^ h) * v * (2 ^ w - 1) ≤ targets) :
    ((simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
      ((tcrEndpoints hash targets starts fallback).run [])).run ([], [])) =
      pure (((GXMSS.endpoints hash pp starts, endpointTargets hash pp starts),
        endpointTargets hash pp starts, [])) := by
  rw [← endpointFamily_eq hash pp starts]
  simpa [tcrEndpoints, endpointTargets] using
    (tcrEpochFamily_run hash targets pp starts fallback (2 ^ h) (fun ep => ep)
      Function.injective_id []
      (by simpa using hcap) (by simp))

/-- The chain reductions' honest setup samples the accepted starts, reconstructs the ordinary
endpoint family, and exposes exactly the positive-step registration history. -/
theorem tcrChainSetup_run [SampleableType H] [DecidableEq T]
    (hash : HashInstance PP T X H h w v) (targets : ℕ) (pp : PP)
    (hcap : (2 ^ h) * v * (2 ^ w - 1) ≤ targets) :
    (simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
      (tcrChainSetup hash targets)).run ([], []) = (do
        let fallback ← ($ᵗ H : ProbComp H)
        let starts ← GXMSS.sampleStarts H h v
        let endpoints := GXMSS.endpoints hash pp starts
        let registered := endpointTargets hash pp starts
        pure ((⟨starts, endpoints, fallback, registered, fallback⟩ :
          TCRKeyState PP T X H h v), registered, [])) := by
  have hunif {A : Type} (oa : ProbComp A) (state : SM_DT_TCR_State T X) :
      (simulateQ
        (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
        (OracleComp.liftComp oa _)).run state = (fun value => (value, state)) <$> oa := by
    rw [SM_DT_TCR_oracles, QueryImpl.simulateQ_add_liftComp_left, simulateQ_liftTarget,
      simulateQ_ofLift_eq_self]
    simp
  simp only [tcrChainSetup, simulateQ_bind, StateT.run_bind]
  rw [hunif, bind_map_left]
  apply bind_congr
  intro fallback
  rw [hunif, bind_map_left]
  apply bind_congr
  intro starts
  rw [tcrEndpoints_run_empty hash targets pp starts fallback hcap]
  simp

private def merkleTargetRun (hash : HashInstance PP T X H h w v) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fallback : H) :
    (z t : ℕ) → H × List (T × X)
  | 0, t =>
      if ht : t < 2 ^ h then
        let ep : Epoch h := ⟨t, ht⟩
        let target := (hash.treeTweak (0, ep), hash.vectorInput (endpoints ep))
        (hash.thf.eval pp target.1 target.2, [target])
      else (fallback, [])
  | z + 1, t =>
      let leftRun := merkleTargetRun hash pp endpoints fallback z (2 * t)
      let rightRun := merkleTargetRun hash pp endpoints fallback z (2 * t + 1)
      let registered := leftRun.2 ++ rightRun.2
      if hz : z + 1 < h + 1 then
        if ht : t < 2 ^ h then
          let target := (hash.treeTweak (⟨z + 1, hz⟩, ⟨t, ht⟩),
            hash.pairInput (leftRun.1, rightRun.1))
          (hash.thf.eval pp target.1 target.2, registered ++ [target])
        else (fallback, registered)
      else (fallback, registered)

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

private theorem merkleTargetRun_tweaks
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fallback : H) (z t : ℕ) :
    (merkleTargetRun hash pp endpoints fallback z t).2.map Prod.fst =
      merkleTweaks hash z t := by
  induction z generalizing t with
  | zero =>
      simp only [merkleTargetRun, merkleTweaks]
      split <;> simp
  | succ z ih =>
      simp only [merkleTargetRun, merkleTweaks]
      split
      · split <;> simp_all [List.map_append]
      · simp_all [List.map_append]

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
      have hindex : t < 2 ^ h := (Merkle.subtree_legal hz ht).2
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
      have hindex : t < 2 ^ h := (Merkle.subtree_legal hz ht).2
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

private theorem merkleTargetRun_legal
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fallback : H)
    (z t : ℕ) (hz : z ≤ h) (ht : (t + 1) * 2 ^ z ≤ 2 ^ h) :
    let run := merkleTargetRun hash pp endpoints fallback z t
    run.1 = PerfectMerkleTree.merkleRoot
        (hash.leafExtension pp endpoints) (hash.nodeExtension pp) z t ∧
      run.2.length = 2 ^ (z + 1) - 1 := by
  induction z generalizing t with
  | zero =>
      have ht' : t < 2 ^ h := by simpa using ht
      simp [merkleTargetRun, ht', HashInstance.leafExtension,
        HashInstance.leafHash, PerfectMerkleTree.merkleRoot]
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
      have hindex : t < 2 ^ h := (Merkle.subtree_legal hz ht).2
      have ihLeft := ih (2 * t) (by omega) hleft
      have ihRight := ih (2 * t + 1) (by omega) hright
      simp only at ihLeft ihRight
      simp only [merkleTargetRun, hlevel, hindex, dite_true,
        PerfectMerkleTree.merkleRoot_succ, HashInstance.nodeExtension,
        HashInstance.nodeHash, ihLeft.1, ihRight.1,
        List.length_append, List.length_singleton, ihLeft.2, ihRight.2]
      simp only [pow_succ]
      constructor
      · trivial
      · omega

private theorem merkleTargetRun_targets_fallback_irrelevant
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fallback₁ fallback₂ : H)
    (z t : ℕ) (hz : z ≤ h) (ht : (t + 1) * 2 ^ z ≤ 2 ^ h) :
    (merkleTargetRun hash pp endpoints fallback₁ z t).2 =
      (merkleTargetRun hash pp endpoints fallback₂ z t).2 := by
  induction z generalizing t with
  | zero =>
      have ht' : t < 2 ^ h := by simpa using ht
      simp [merkleTargetRun, ht']
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
      have hindex : t < 2 ^ h := (Merkle.subtree_legal hz ht).2
      have hleftTargets := ih (2 * t) (by omega) hleft
      have hrightTargets := ih (2 * t + 1) (by omega) hright
      have hleftRoot₁ :=
        (merkleTargetRun_legal hash pp endpoints fallback₁ z (2 * t) (by omega) hleft).1
      have hleftRoot₂ :=
        (merkleTargetRun_legal hash pp endpoints fallback₂ z (2 * t) (by omega) hleft).1
      have hrightRoot₁ :=
        (merkleTargetRun_legal hash pp endpoints fallback₁ z (2 * t + 1)
          (by omega) hright).1
      have hrightRoot₂ :=
        (merkleTargetRun_legal hash pp endpoints fallback₂ z (2 * t + 1)
          (by omega) hright).1
      simp [merkleTargetRun, hlevel, hindex, hleftTargets, hrightTargets,
        hleftRoot₁, hleftRoot₂, hrightRoot₁, hrightRoot₂]

/-- Honest full-tree targets in exact left-subtree, right-subtree, parent order. Leaf targets
contain endpoint vectors and internal targets contain the ordered child values computed by the
ordinary Merkle recursion. -/
def merkleTargets (hash : HashInstance PP T X H h w v) (pp : PP)
    (endpoints : Epoch h → Fin v → H) : List (T × X) :=
  let fallback := hash.leafHash pp 0 (endpoints 0)
  (merkleTargetRun hash pp endpoints fallback h 0).2

/-- The full-tree target schedule has one entry for every leaf and internal node. -/
@[simp] theorem merkleTargets_length (hash : HashInstance PP T X H h w v) (pp : PP)
    (endpoints : Epoch h → Fin v → H) :
    (merkleTargets hash pp endpoints).length = 2 ^ (h + 1) - 1 := by
  simpa [merkleTargets] using
    (merkleTargetRun_legal hash pp endpoints (hash.leafHash pp 0 (endpoints 0))
      h 0 le_rfl (by simp)).2

/-- Full-tree traversal never repeats a tweak. This is the freshness fact for the tree portion of
honest target registration; separation from the preceding chain prefix follows from
`HashInstance.chain_ne_tree`. -/
theorem merkleTargets_tweaks_nodup (hash : HashInstance PP T X H h w v) (pp : PP)
    (endpoints : Epoch h → Fin v → H) :
    ((merkleTargets hash pp endpoints).map Prod.fst).Nodup := by
  rw [merkleTargets, merkleTargetRun_tweaks]
  exact merkleTweaks_nodup hash h 0 le_rfl (by simp)

private theorem endpointTargets_merkleTargets_disjoint
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (starts endpoints : Epoch h → Fin v → H) :
    ∀ q ∈ endpointTargets hash pp starts, ∀ r ∈ merkleTargets hash pp endpoints,
      q.1 ≠ r.1 := by
  intro q hq r hr
  simp only [endpointTargets, List.mem_flatten, List.mem_ofFn] at hq
  obtain ⟨epochTargets, ⟨ep, hepochTargets⟩, hq⟩ := hq
  rw [← hepochTargets] at hq
  simp only [List.mem_flatten, List.mem_ofFn] at hq
  obtain ⟨chain, ⟨i, hchain⟩, hq⟩ := hq
  rw [← hchain] at hq
  simp only [chainTargets, List.mem_ofFn] at hq
  obtain ⟨j, rfl⟩ := hq
  have hrTweak : r.1 ∈ (merkleTargets hash pp endpoints).map Prod.fst :=
    List.mem_map.mpr ⟨r, hr, rfl⟩
  rw [merkleTargets, merkleTargetRun_tweaks] at hrTweak
  obtain ⟨level, index, hrEq, _, _, _⟩ :=
    mem_merkleTweaks_bounds hash h 0 le_rfl (by simp) hrTweak
  rw [hrEq]
  exact hash.chain_ne_tree _ _

private theorem merkleTargetRun_full (hash : HashInstance PP T X H h w v) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fallback : H) :
    let run := merkleTargetRun hash pp endpoints fallback h 0
    run.1 = hash.merkleRoot pp endpoints ∧ run.2 = merkleTargets hash pp endpoints := by
  have hlegal := merkleTargetRun_legal hash pp endpoints fallback h 0 le_rfl (by simp)
  refine ⟨?_, ?_⟩
  · simpa [HashInstance.merkleRoot] using hlegal.1
  · simpa [merkleTargets] using
      (merkleTargetRun_targets_fallback_irrelevant hash pp endpoints fallback
        (hash.leafHash pp 0 (endpoints 0)) h 0 le_rfl (by simp))

private theorem leafTarget_mem_merkleTargetRun
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fallback : H)
    (z t : ℕ) (hz : z ≤ h) (ht : (t + 1) * 2 ^ z ≤ 2 ^ h)
    (ep : Epoch h) (hlower : t * 2 ^ z ≤ ep.val)
    (hupper : ep.val + 1 ≤ (t + 1) * 2 ^ z) :
    (hash.treeTweak (0, ep), hash.vectorInput (endpoints ep)) ∈
      (merkleTargetRun hash pp endpoints fallback z t).2 := by
  induction z generalizing t with
  | zero =>
      have ht' : t < 2 ^ h := by simpa using ht
      have hep : ep = ⟨t, ht'⟩ := by
        apply Fin.ext
        simp only [pow_zero, Nat.mul_one] at hlower hupper
        exact Nat.le_antisymm (Nat.le_of_add_le_add_right hupper) hlower
      subst ep
      simp [merkleTargetRun, ht']
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
      have hindex : t < 2 ^ h := (Merkle.subtree_legal hz ht).2
      rw [merkleTargetRun, dite_eq_left hlevel, dite_eq_left hindex]
      simp only [List.mem_append, List.mem_singleton]
      by_cases hside : ep.val < (2 * t + 1) * 2 ^ z
      · exact Or.inl (Or.inl (ih (t := 2 * t) (hz := by omega) (ht := hleft)
          (by rw [hpow] at hlower; nlinarith) (by omega)))
      · exact Or.inl (Or.inr (ih (t := 2 * t + 1) (hz := by omega) (ht := hright)
          (by omega) (by rw [hpow] at hupper; nlinarith)))

private theorem nodeTarget_mem_merkleTargetRun
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fallback : H)
    (z t : ℕ) (hz : z ≤ h) (ht : (t + 1) * 2 ^ z ≤ 2 ^ h)
    (level : Fin (h + 1)) (index : Fin (2 ^ h))
    (hpos : 0 < level.val) (hlevelBound : level.val ≤ z)
    (hlower : t * 2 ^ z ≤ index.val * 2 ^ level.val)
    (hupper : (index.val + 1) * 2 ^ level.val ≤ (t + 1) * 2 ^ z) :
    (hash.treeTweak (level, index), hash.pairInput
      (PerfectMerkleTree.merkleRoot (hash.leafExtension pp endpoints)
        (hash.nodeExtension pp) (level.val - 1) (2 * index.val),
       PerfectMerkleTree.merkleRoot (hash.leafExtension pp endpoints)
        (hash.nodeExtension pp) (level.val - 1) (2 * index.val + 1))) ∈
      (merkleTargetRun hash pp endpoints fallback z t).2 := by
  induction z generalizing t with
  | zero => omega
  | succ z ih =>
      have hpow : 2 ^ (z + 1) = 2 ^ z * 2 := Nat.pow_succ _ _
      have hp : 0 < 2 ^ z := by positivity
      have hleft : (2 * t + 1) * 2 ^ z ≤ 2 ^ h := by
        rw [hpow] at ht
        nlinarith
      have hright : (2 * t + 1 + 1) * 2 ^ z ≤ 2 ^ h := by
        rw [hpow] at ht
        nlinarith
      have htreeLevel : z + 1 < h + 1 := by omega
      have htreeIndex : t < 2 ^ h := (Merkle.subtree_legal hz ht).2
      rw [merkleTargetRun, dite_eq_left htreeLevel, dite_eq_left htreeIndex]
      simp only [List.mem_append, List.mem_singleton]
      by_cases htop : level.val = z + 1
      · have hindexEq : index.val = t := by
          have hpLevel : 0 < 2 ^ level.val := by positivity
          rw [htop] at hlower hupper
          nlinarith
        have hlevelEq : level = ⟨z + 1, htreeLevel⟩ := by
          apply Fin.ext
          exact htop
        have hindexFinEq : index = ⟨t, htreeIndex⟩ := by
          apply Fin.ext
          exact hindexEq
        subst level
        subst index
        let leftRun := merkleTargetRun hash pp endpoints fallback z (2 * t)
        let rightRun := merkleTargetRun hash pp endpoints fallback z (2 * t + 1)
        have hleftRoot :=
          (merkleTargetRun_legal hash pp endpoints fallback z (2 * t) (by omega) hleft).1
        have hrightRoot :=
          (merkleTargetRun_legal hash pp endpoints fallback z (2 * t + 1)
            (by omega) hright).1
        exact Or.inr (by simp [hleftRoot, hrightRoot])
      · have hbelow : level.val ≤ z := by omega
        have hfactor : 2 ^ z = 2 ^ (z - level.val) * 2 ^ level.val := by
          rw [← Nat.pow_add, Nat.sub_add_cancel hbelow]
        by_cases hside : index.val < (2 * t + 1) * 2 ^ (z - level.val)
        · have hleftUpper : (index.val + 1) * 2 ^ level.val ≤
              (2 * t + 1) * 2 ^ z := by
            calc
              (index.val + 1) * 2 ^ level.val ≤
                  ((2 * t + 1) * 2 ^ (z - level.val)) * 2 ^ level.val :=
                Nat.mul_le_mul_right _ (by omega)
              _ = (2 * t + 1) * 2 ^ z := by rw [hfactor]; ring
          exact Or.inl (Or.inl (ih (t := 2 * t) (hz := by omega) (ht := hleft)
            hbelow (by rw [hpow] at hlower; nlinarith) hleftUpper))
        · have hrightLower : (2 * t + 1) * 2 ^ z ≤
              index.val * 2 ^ level.val := by
            calc
              (2 * t + 1) * 2 ^ z =
                  ((2 * t + 1) * 2 ^ (z - level.val)) * 2 ^ level.val := by
                rw [hfactor]
                ring
              _ ≤ index.val * 2 ^ level.val :=
                Nat.mul_le_mul_right _ (by omega)
          exact Or.inl (Or.inr (ih (t := 2 * t + 1) (hz := by omega) (ht := hright)
            hbelow hrightLower (by rw [hpow] at hupper; nlinarith)))

/-- Every exact hash target used by an honest Merkle opening occurs in the full-tree registration
schedule, including the raw endpoint vector and every ordered child pair on the path. -/
theorem merkleOpeningTarget_mem_merkleTargets
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (ep : Epoch h) (target : T × X)
    (hmem : target ∈
      hash.merkleOpeningQueries pp ep (endpoints ep) (hash.authPath pp endpoints ep)) :
    target ∈ merkleTargets hash pp endpoints := by
  rcases hash.mem_merkleOpeningQueries_honest_shape pp endpoints ep target hmem with
    hleaf | ⟨z, hnode⟩
  · rw [hleaf, merkleTargets]
    exact leafTarget_mem_merkleTargetRun hash pp endpoints
      (hash.leafHash pp 0 (endpoints 0)) h 0 le_rfl (by simp) ep (by simp) (by simp)
  · rw [hnode, merkleTargets]
    have hreachable := Merkle.parentAddress_reachable ep z
    let address := Merkle.parentAddress ep z
    change Merkle.ReachableNode h address.1.val address.2.val at hreachable
    obtain ⟨hlevelPos, hlevelBound, hindexBound⟩ := hreachable
    have hchildren : hash.honestMerkleChildren pp endpoints ep z =
        (PerfectMerkleTree.merkleRoot (hash.leafExtension pp endpoints)
          (hash.nodeExtension pp) (address.1.val - 1) (2 * address.2.val),
         PerfectMerkleTree.merkleRoot (hash.leafExtension pp endpoints)
          (hash.nodeExtension pp) (address.1.val - 1) (2 * address.2.val + 1)) := by
      simp [HashInstance.honestMerkleChildren, PerfectMerkleTree.honestChildren, address,
        Merkle.parentAddress]
    rw [hchildren]
    exact nodeTarget_mem_merkleTargetRun hash pp endpoints
      (hash.leafHash pp 0 (endpoints 0)) h 0 le_rfl (by simp) address.1 address.2
      hlevelPos hlevelBound (by simp) (by simpa using hindexBound)

private theorem tcrMerkleRootAt_run [DecidableEq T]
    (hash : HashInstance PP T X H h w v) (targets : ℕ) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fallback : H)
    (history before after : List (T × X)) (z t : ℕ)
    (hz : z ≤ h) (ht : (t + 1) * 2 ^ z ≤ 2 ^ h)
    (hcap : history.length + (before ++
      (merkleTargetRun hash pp endpoints fallback z t).2 ++ after).length ≤ targets)
    (hdisjoint : ∀ q ∈ history,
      ∀ r ∈ before ++ (merkleTargetRun hash pp endpoints fallback z t).2 ++ after,
        q.1 ≠ r.1)
    (hnodup : ((before ++ (merkleTargetRun hash pp endpoints fallback z t).2 ++ after).map
      Prod.fst).Nodup) :
    let leaf := fun t => if ht : t < 2 ^ h then
      let ep : Epoch h := ⟨t, ht⟩
      tcrEval hash targets (hash.treeTweak (0, ep))
        (hash.vectorInput (endpoints ep)) fallback
    else pure fallback
    let node := fun z t left right => if hz : z < h + 1 then
      if ht : t < 2 ^ h then
        tcrEval hash targets (hash.treeTweak (⟨z, hz⟩, ⟨t, ht⟩))
          (hash.pairInput (left, right)) fallback
      else pure fallback
    else pure fallback
    let run := merkleTargetRun hash pp endpoints fallback z t
    ((simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
      ((PerfectMerkleTree.merkleRootM leaf node z t).run (history ++ before))).run
        (history ++ before, [])) =
      pure (((run.1, history ++ before ++ run.2), history ++ before ++ run.2, [])) := by
  dsimp only
  induction z generalizing t before after with
  | zero =>
      have ht' : t < 2 ^ h := by simpa using ht
      let target := (hash.treeTweak (0, ⟨t, ht'⟩),
        hash.vectorInput (endpoints ⟨t, ht'⟩))
      have hrun : (merkleTargetRun hash pp endpoints fallback 0 t).2 = [target] := by
        simp [merkleTargetRun, ht', target]
      have hbelow : (history ++ before).length < targets := by
        rw [hrun] at hcap
        simp only [List.length_append, List.length_cons, List.length_nil] at hcap ⊢
        omega
      have hfresh : TweakFresh Prod.fst (history ++ before) [] target.1 := by
        apply tweakFresh_after_prefix history before after target
        · simpa [hrun, List.append_assoc] using hdisjoint
        · simpa [hrun, List.append_assoc] using hnodup
      simp only [PerfectMerkleTree.merkleRootM]
      rw [dite_eq_left ht']
      rw [tcrEval_run_of_fresh hash targets pp target.1 target.2 fallback
        (history ++ before) hbelow hfresh]
      simp [target, merkleTargetRun, ht', List.append_assoc]
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
      have hindex : t < 2 ^ h := (Merkle.subtree_legal hz ht).2
      let leftRun := merkleTargetRun hash pp endpoints fallback z (2 * t)
      let rightRun := merkleTargetRun hash pp endpoints fallback z (2 * t + 1)
      let target := (hash.treeTweak (⟨z + 1, hlevel⟩, ⟨t, hindex⟩),
        hash.pairInput (leftRun.1, rightRun.1))
      have hrun : (merkleTargetRun hash pp endpoints fallback (z + 1) t).2 =
          leftRun.2 ++ rightRun.2 ++ [target] := by
        simp [merkleTargetRun, hlevel, hindex, leftRun, rightRun, target]
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
      simp only [PerfectMerkleTree.merkleRootM, StateT.run_bind, simulateQ_bind]
      rw [hleftExec]
      simp only [pure_bind]
      rw [List.append_assoc history before leftRun.2]
      rw [hrightExec]
      simp only [pure_bind]
      rw [dite_eq_left hlevel, dite_eq_left hindex]
      rw [← List.append_assoc history before leftRun.2]
      rw [tcrEval_run_of_fresh hash targets pp target.1 target.2 fallback
        (history ++ before ++ leftRun.2 ++ rightRun.2) hbelow hfresh]
      simp [leftRun, rightRun, target, merkleTargetRun, hlevel, hindex, List.append_assoc]

/-- Honest Merkle setup returns the ordinary root and appends exactly the full-tree target schedule,
while the local registration history and authoritative challenge history remain equal. -/
theorem tcrMerkleRoot_run [DecidableEq T]
    (hash : HashInstance PP T X H h w v) (targets : ℕ) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fallback : H) (history : List (T × X))
    (hcap : history.length + (merkleTargets hash pp endpoints).length ≤ targets)
    (hdisjoint : ∀ q ∈ history, ∀ r ∈ merkleTargets hash pp endpoints,
      q.1 ≠ r.1) :
    ((simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
      ((tcrMerkleRoot hash targets endpoints fallback).run history)).run (history, [])) =
      pure (((hash.merkleRoot pp endpoints,
        history ++ merkleTargets hash pp endpoints),
        history ++ merkleTargets hash pp endpoints, [])) := by
  have hfull := merkleTargetRun_full hash pp endpoints fallback
  have hcap' : history.length +
      (merkleTargetRun hash pp endpoints fallback h 0).2.length ≤ targets := by
    rw [hfull.2]
    exact hcap
  have hdisjoint' : ∀ q ∈ history,
      ∀ r ∈ (merkleTargetRun hash pp endpoints fallback h 0).2, q.1 ≠ r.1 := by
    rw [hfull.2]
    exact hdisjoint
  have hnodup : ((merkleTargetRun hash pp endpoints fallback h 0).2.map Prod.fst).Nodup := by
    rw [hfull.2]
    exact merkleTargets_tweaks_nodup hash pp endpoints
  have hexec := tcrMerkleRootAt_run hash targets pp endpoints fallback history [] [] h 0
    le_rfl (by simp) (by simpa [List.append_assoc] using hcap')
    (by simpa [List.append_assoc] using hdisjoint')
    (by simpa [List.append_assoc] using hnodup)
  simpa [tcrMerkleRoot, hfull.1, hfull.2, List.append_assoc] using hexec

/-- Every query of every honest opening occurs in the exact authoritative history produced after
the chain prefix and full-tree traversal. -/
theorem merkleOpeningTarget_mem_registeredHistory
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (starts endpoints : Epoch h → Fin v → H) (ep : Epoch h) (target : T × X)
    (hmem : target ∈
      hash.merkleOpeningQueries pp ep (endpoints ep) (hash.authPath pp endpoints ep)) :
    target ∈ endpointTargets hash pp starts ++ merkleTargets hash pp endpoints :=
  List.mem_append_right _ (merkleOpeningTarget_mem_merkleTargets hash pp endpoints ep target hmem)

/-- Complete honest key setup returns the ordinary endpoints and root, and its local target list is
exactly the authoritative challenge history in chain-prefix then full-tree order. -/
theorem tcrKeySetup_run [SampleableType H] [DecidableEq T]
    (hash : HashInstance PP T X H h w v) (targets : ℕ) (pp : PP)
    (hcap : (2 ^ h) * v * (2 ^ w - 1) + (2 ^ (h + 1) - 1) ≤ targets) :
    (simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
      (tcrKeySetup hash targets)).run ([], []) = (do
        let fallback ← ($ᵗ H : ProbComp H)
        let starts ← GXMSS.sampleStarts H h v
        let endpoints := GXMSS.endpoints hash pp starts
        let registered := endpointTargets hash pp starts ++ merkleTargets hash pp endpoints
        pure ((⟨starts, endpoints, hash.merkleRoot pp endpoints, registered, fallback⟩ :
          TCRKeyState PP T X H h v), registered, [])) := by
  have hunif {A : Type} (oa : ProbComp A) (state : SM_DT_TCR_State T X) :
      (simulateQ
        (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
        (OracleComp.liftComp oa _)).run state = (fun value => (value, state)) <$> oa := by
    rw [SM_DT_TCR_oracles, QueryImpl.simulateQ_add_liftComp_left, simulateQ_liftTarget,
      simulateQ_ofLift_eq_self]
    simp
  simp only [tcrKeySetup, simulateQ_bind, StateT.run_bind]
  rw [hunif, bind_map_left]
  apply bind_congr
  intro fallback
  rw [hunif, bind_map_left]
  apply bind_congr
  intro starts
  let endpoints := GXMSS.endpoints hash pp starts
  have hlengths : (endpointTargets hash pp starts).length +
      (merkleTargets hash pp endpoints).length ≤ targets := by
    simpa only [endpointTargets_length, merkleTargets_length] using hcap
  have hchainCap : (2 ^ h) * v * (2 ^ w - 1) ≤ targets := by
    rw [← endpointTargets_length hash pp starts]
    omega
  rw [tcrEndpoints_run_empty hash targets pp starts fallback hchainCap]
  simp only [pure_bind]
  rw [tcrMerkleRoot_run hash targets pp endpoints fallback
    (endpointTargets hash pp starts) hlengths
    (endpointTargets_merkleTargets_disjoint hash pp starts endpoints)]
  simp [endpoints]

/-- All honest complete-opening queries, grouped by epoch. This list is used only as a coverage
view; it does not replace the full-tree traversal order retained by the setup. -/
def honestOpeningTargets (hash : HashInstance PP T X H h w v) (pp : PP)
    (endpoints : Epoch h → Fin v → H) : List (T × X) :=
  (List.ofFn fun ep : Epoch h =>
    hash.merkleOpeningQueries pp ep (endpoints ep) (hash.authPath pp endpoints ep)).flatten

/-- Every query of every honest opening occurs in the explicit all-opening coverage view. In
particular, the node inputs here retain the exact addressed ordered child values computed by the
honest opening, rather than merely a compatible address. -/
theorem mem_honestOpeningTargets (hash : HashInstance PP T X H h w v) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (ep : Epoch h) (target : T × X)
    (hmem : target ∈
      hash.merkleOpeningQueries pp ep (endpoints ep) (hash.authPath pp endpoints ep)) :
    target ∈ honestOpeningTargets hash pp endpoints := by
  simp only [honestOpeningTargets, List.mem_flatten, List.mem_ofFn]
  exact ⟨_, ⟨ep, rfl⟩, hmem⟩

/-- The setup fields visible to the later reductions. The independently sampled fallback is
intentionally absent from this observation. -/
structure TCRSetupObservation (H T X : Type) (h v : ℕ) where
  /-- The independently sampled starts for every epoch and chain. -/
  starts : Epoch h → Fin v → H
  /-- The full-chain endpoints authenticated by the Merkle tree. -/
  endpoints : Epoch h → Fin v → H
  /-- The public Merkle root. -/
  root : H
  /-- The ordered tweak/input pairs registered during setup. -/
  targets : List (T × X)

/-- Forget the internal fallback while retaining all ordinary key data and registered targets. -/
def TCRKeyState.observe (state : TCRKeyState PP T X H h v) :
    TCRSetupObservation H T X h v :=
  ⟨state.starts, state.endpoints, state.root, state.targets⟩

/-- Two setup states differing only in the internal fallback have exactly the same reduction
observation. -/
theorem TCRKeyState.observe_fallback_irrelevant
    (starts : Epoch h → Fin v → H) (endpoints : Epoch h → Fin v → H)
    (root : H) (targets : List (T × X)) (fallback₁ fallback₂ : H) :
    (TCRKeyState.mk (PP := PP) starts endpoints root targets fallback₁).observe =
      (TCRKeyState.mk (PP := PP) starts endpoints root targets fallback₂).observe := by
  rfl

/-- Faithful setup fields reconstruct precisely the ordinary GXMSS public and secret keys. -/
theorem TCRKeyState.keys_eq (hash : HashInstance PP T X H h w v) (pp : PP)
    (state : TCRKeyState PP T X H h v)
    (hendpoints : state.endpoints = GXMSS.endpoints hash pp state.starts)
    (hroot : state.root = hash.merkleRoot pp state.endpoints) :
    ((⟨state.root, pp⟩ : GXMSS.PublicKey PP H),
      (⟨pp, state.starts, state.endpoints⟩ : GXMSS.SecretKey PP H h v)) =
      GXMSS.keys hash pp state.starts := by
  rw [hendpoints] at hroot ⊢
  simp only [GXMSS.keys]
  rw [hroot]

/-- Mapping complete honest setup to public/secret key material yields exactly the ordinary GXMSS
keys while retaining the exact authoritative registration history. -/
theorem tcrKeySetup_keys_run [SampleableType H] [DecidableEq T]
    (hash : HashInstance PP T X H h w v) (targets : ℕ) (pp : PP)
    (hcap : (2 ^ h) * v * (2 ^ w - 1) + (2 ^ (h + 1) - 1) ≤ targets) :
    (fun (state, challengeHistory, collectionHistory) =>
      (((⟨state.root, pp⟩ : GXMSS.PublicKey PP H),
        (⟨pp, state.starts, state.endpoints⟩ : GXMSS.SecretKey PP H h v)),
        challengeHistory, collectionHistory)) <$>
      (simulateQ
        (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
        (tcrKeySetup hash targets)).run ([], []) = (do
          let _fallback ← ($ᵗ H : ProbComp H)
          let starts ← GXMSS.sampleStarts H h v
          let endpoints := GXMSS.endpoints hash pp starts
          let registered := endpointTargets hash pp starts ++ merkleTargets hash pp endpoints
          pure (GXMSS.keys hash pp starts, registered, [])) := by
  rw [tcrKeySetup_run hash targets pp hcap]
  simp [GXMSS.keys]

/-- The observable complete setup computation retains starts, endpoints, root, and exact targets,
but not the independently sampled internal fallback. -/
theorem tcrKeySetup_observe_run [SampleableType H] [DecidableEq T]
    (hash : HashInstance PP T X H h w v) (targets : ℕ) (pp : PP)
    (hcap : (2 ^ h) * v * (2 ^ w - 1) + (2 ^ (h + 1) - 1) ≤ targets) :
    (fun (state, challengeHistory, collectionHistory) =>
      (state.observe, challengeHistory, collectionHistory)) <$>
      (simulateQ
        (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
        (tcrKeySetup hash targets)).run ([], []) = (do
          let _fallback ← ($ᵗ H : ProbComp H)
          let starts ← GXMSS.sampleStarts H h v
          let endpoints := GXMSS.endpoints hash pp starts
          let registered := endpointTargets hash pp starts ++ merkleTargets hash pp endpoints
          pure ((⟨starts, endpoints, hash.merkleRoot pp endpoints, registered⟩ :
            TCRSetupObservation H T X h v), registered, [])) := by
  rw [tcrKeySetup_run hash targets pp hcap]
  simp [TCRKeyState.observe]

/-- Under native measure semantics, discarding the internal fallback removes its independent
uniform draw without conditioning or normalizing away missing mass. -/
theorem tcrKeySetup_observe_evalDist [SampleableType H] [DecidableEq T]
    (hash : HashInstance PP T X H h w v) (targets : ℕ) (pp : PP)
    (hcap : (2 ^ h) * v * (2 ^ w - 1) + (2 ^ (h + 1) - 1) ≤ targets)
    [MeasurableSpace (TCRSetupObservation H T X h v × List (T × X) × List T)] :
    evalDist (((fun (state, challengeHistory, collectionHistory) =>
      (state.observe, challengeHistory, collectionHistory)) <$>
      (simulateQ
        (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
        (tcrKeySetup hash targets)).run ([], []) :
      ProbComp (TCRSetupObservation H T X h v × List (T × X) × List T))) =
    evalDist ((do
      let starts ← GXMSS.sampleStarts H h v
      let endpoints := GXMSS.endpoints hash pp starts
      let registered := endpointTargets hash pp starts ++ merkleTargets hash pp endpoints
      pure ((⟨starts, endpoints, hash.merkleRoot pp endpoints, registered⟩ :
        TCRSetupObservation H T X h v), registered, []) :
      ProbComp (TCRSetupObservation H T X h v × List (T × X) × List T))) := by
  rw [tcrKeySetup_observe_run hash targets pp hcap]
  simpa only using (OracleComp.evalDist_bind_const ($ᵗ H : ProbComp H) (do
    let starts ← GXMSS.sampleStarts H h v
    let endpoints := GXMSS.endpoints hash pp starts
    let registered := endpointTargets hash pp starts ++ merkleTargets hash pp endpoints
    pure ((⟨starts, endpoints, hash.merkleRoot pp endpoints, registered⟩ :
      TCRSetupObservation H T X h v), registered, [])))

/-- The chain problem has room for all positive steps of all honest chains, including `w = 0`. -/
theorem chainProblem_capacity (hash : HashInstance PP T X H h w v) :
    (2 ^ h) * v * (2 ^ w - 1) ≤ (chainTCRProblem hash).numTargets := by
  change (2 ^ h) * v * (2 ^ w - 1) ≤ (2 ^ h) * v * 2 ^ w
  exact Nat.mul_le_mul_left ((2 ^ h) * v) (Nat.sub_le _ _)

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

/-- Every honest positive chain target has an exact authoritative index and lies below any bound
covering the complete endpoint registration history. -/
theorem chainTarget_registeredIndex_spec [DecidableEq T] [DecidableEq X]
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (starts : Epoch h → Fin v → H) (ep : Epoch h) (i : Fin v)
    (j : Fin (2 ^ w - 1)) (capacity : ℕ)
    (hcap : (endpointTargets hash pp starts).length ≤ capacity) :
    let target := (hash.chainTweak (ep, i, ⟨j.val, by omega⟩),
      hash.digestInput (hash.chain pp ep i 0 j.val (starts ep i)))
    registeredIndex (endpointTargets hash pp starts) target.1 target.2 <
        (endpointTargets hash pp starts).length ∧
      (endpointTargets hash pp starts)[registeredIndex (endpointTargets hash pp starts)
        target.1 target.2]? = some target ∧
      registeredIndex (endpointTargets hash pp starts) target.1 target.2 < capacity := by
  exact registeredIndex_spec _ _ _ _
    (chainTarget_mem_endpointTargets hash pp starts ep i j) hcap

/-- Every exact honest-opening target has the first registered index, exact lookup, and capacity
bound in the complete authoritative setup history. -/
theorem merkleOpeningTarget_registeredIndex_spec [DecidableEq T] [DecidableEq X]
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (starts endpoints : Epoch h → Fin v → H) (ep : Epoch h) (target : T × X)
    (hmem : target ∈
      hash.merkleOpeningQueries pp ep (endpoints ep) (hash.authPath pp endpoints ep))
    (capacity : ℕ)
    (hcap : (endpointTargets hash pp starts ++ merkleTargets hash pp endpoints).length ≤
      capacity) :
    let history := endpointTargets hash pp starts ++ merkleTargets hash pp endpoints
    registeredIndex history target.1 target.2 < history.length ∧
      history[registeredIndex history target.1 target.2]? = some target ∧
      registeredIndex history target.1 target.2 < capacity := by
  exact registeredIndex_spec _ _ _ _
    (merkleOpeningTarget_mem_registeredHistory hash pp starts endpoints ep target hmem) hcap

end GXMSS.Reductions
