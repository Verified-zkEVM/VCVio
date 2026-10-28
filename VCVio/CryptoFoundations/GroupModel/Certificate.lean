/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.GroupModel.Virtualize
public import VCVio.OracleComp.QueryTracking.QueryBound.Weighted

/-! # Group-operation certificates for reduction handlers

A certificate bounds each handler step from every state. Per-kind adversary budgets then
bound the reduction's group operations by setup and finalization costs plus the sum of
per-kind costs times query budgets. Setup may produce the initial handler state.

Equality tests are free for the adversary. A handler that spends a group operation on each
equality test therefore has no bound in the adversary's group operations alone: it needs a
separate equality-query budget. This is the counting part of the design note's T5 transfer.
-/

public section

open OracleComp OracleSpec

namespace GroupModel

variable {F S : Type} {σ : Sig S} {ι ι' : Type}
    {Γ : OracleSpec ι} {Γ' : OracleSpec ι'} {τ α β : Type}

/-- Each handler query costs at most its certificate charge, from every initial state. -/
@[expose] def CostCertificate
    (h : QueryImpl (spec F σ + Γ) (StateT τ (OracleComp (spec F σ + Γ'))))
    (c : (spec F σ + Γ).Domain → ℕ) : Prop :=
  ∀ t s, IsQueryBoundP ((h t).run s) (fun i => isGroupOp i = true) (c t)

/-- A certified handler turns an adversary's structural weighted budget into group work. -/
theorem CostCertificate.simulateQ_run
    {h : QueryImpl (spec F σ + Γ) (StateT τ (OracleComp (spec F σ + Γ')))}
    {c : (spec F σ + Γ).Domain → ℕ} (hc : CostCertificate h c)
    {A : OracleComp (spec F σ + Γ) α} {W : ℕ}
    (hA : IsQueryBound A W (fun t b => c t ≤ b) (fun t b => b - c t)) (s : τ) :
    IsQueryBoundP ((simulateQ h A).run s) (fun i => isGroupOp i = true) W :=
  hA.simulateQ_run_weighted hc s

/-- Setup and finalization add their combined allowance to the handler's per-kind budget. -/
theorem CostCertificate.transfer_per_kind
    {K : Type*} [Fintype K] [DecidableEq K]
    {h : QueryImpl (spec F σ + Γ) (StateT τ (OracleComp (spec F σ + Γ')))}
    (κ : (spec F σ + Γ).Domain → K) (c n : K → ℕ)
    (hc : CostCertificate h (fun t => c (κ t)))
    {A : OracleComp (spec F σ + Γ) α}
    (hA : ∀ k, IsQueryBoundP A (fun t => κ t = k) (n k))
    (setup : OracleComp (spec F σ + Γ') τ)
    (finish : α → τ → OracleComp (spec F σ + Γ') β)
    {cSetup cFinish c₀ : ℕ}
    (hsetup : IsQueryBoundP setup (fun i => isGroupOp i = true) cSetup)
    (hfinish : ∀ a s, IsQueryBoundP (finish a s) (fun i => isGroupOp i = true) cFinish)
    (h₀ : cSetup + cFinish ≤ c₀) :
    IsQueryBoundP (do
      let s ← setup
      let (a, st) ← (simulateQ h A).run s
      finish a st) (fun i => isGroupOp i = true) (c₀ + ∑ k, c k * n k) := by
  have hw := isQueryBound_weighted_of_per_kind κ c n hA
  have hb := isQueryBoundP_bind hsetup fun s _ =>
    isQueryBoundP_bind (hc.simulateQ_run hw s) fun z _ => hfinish z.1 z.2
  exact hb.mono (by omega)

/-- Virtualization charges one for each group operation and zero for equality and coins. -/
theorem costCertificate_virtualizeImpl [DecidableEq S] (z : S → Handle) :
    CostCertificate (virtualizeImpl (F := F) (σ := σ) z)
      (fun t => if isGroupOp t then 1 else 0) := by
  rintro (t | n) s
  · cases t <;> simp [virtualizeImpl, StateT.run, isGroupOp, Query.isOp]
  · simp [virtualizeImpl, StateT.run, isGroupOp]

end GroupModel
