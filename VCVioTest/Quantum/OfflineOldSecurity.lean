/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.OfflineOldSecurity

/-!
# The old offline theorem at the zero-budget boundary

The public security theorem gives zero actual challenger probability for arbitrary adaptive
zero-query adversaries and zero opening budget, even with infinite mass allowances.
-/

public section

open Quantum Quantum.EmulatedOracle Quantum.SaltedMerkle SaltedMerkle
open scoped ENNReal Kronecker
universe v w
variable {X Y Msg Salt : Type} [Fintype X] [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [AddCommGroup Y] [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
  [SampleableType Salt] (enc : Encoding X Y Msg Salt) {k : ℕ} (d : ℕ)
  {Z : Type} [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

/-- No total queries and no allowed openings give a zero actual offline mismatch event. -/
example (code : TpDCode k (DmOf (fun _ ↦ 2 ^ d) Msg (fun _ ↦ Td Y Salt d)) Z)
    (hk : 1 ≤ k) {A : QReg} {W : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v} (cohSpec (extIn k X Y Y Z)) W A)
    (claim : ∀ B, W B → OpeningClaim k Y Msg (fun _ ↦ 2 ^ d) (fun _ ↦ Pf Y Salt d))
    (ρ : SubState A) (hx : x.IsQueryBound fun _ ↦ 0) :
    ((compressedVCOracle k X Y).withExtract
      (multiExtract enc (fun _ ↦ d)) code).coherent.toRuntime.outcomeLawWith .instruments
        (experiment x fun B y ↦ offlineChallenger
          (fun _ : Fin k ↦ (scheme enc d).toVectorCommitment) code hk 0 (claim B y) B)
        ρ Sigma.snd {true} = 0 := by
  apply le_antisymm _ (by positivity)
  have h := merkle_offline_old enc d code hk 0 0 ⊤ ⊤ x claim ρ hx le_top le_top
  simpa only [Nat.zero_mul, oldOfflineBound_zero] using h
