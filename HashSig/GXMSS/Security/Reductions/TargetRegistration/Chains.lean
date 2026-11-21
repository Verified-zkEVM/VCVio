/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.TargetRegistration.Basic

import all HashSig.GXMSS.Security.Reductions.TargetRegistration.Basic

/-!
# Positive-step chain registration simulation
-/

public section

namespace GXMSS.Reductions

open OracleComp OracleSpec TweakableHash

variable {PP T X H M R : Type} {h w v : ℕ}

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

end GXMSS.Reductions
