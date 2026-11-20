/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.Preprocessing
public import VCVioTest.Quantum.PointerChainCoupling

/-!
# Exact pointer-chain security with live preprocessing

The retained-answer adversary queries one fixed raw address before publication and returns its
actual answer without online calls. Its phase budget instantiates the exact scheme's security
result. A malformed empty input never lies on an honestly programmed path, so its raw response
is preserved without charging a collision or incidence error.
-/

public section

open Quantum Quantum.TimeLockPuzzle PointerChainPuzzle PointerChainPuzzle.LeanSeal OracleComp
open scoped ENNReal

namespace VCVioTest.PointerChainPreprocessing

/-- One preprocessing point in one round, followed by no online oracle calls. -/
@[expose]
def retainedBudget : DelayBudget := ⟨1, 1, 0, 0, 0⟩

/-- The budget counts the actual preprocessing query while the online phase uses retained data. -/
theorem retained_budget (ρ : SubState Unit) :
    (PointerChainCoupling.adversary ρ).IsQueryBound retainedBudget := by
  have hc : IsOnlineQueryBound PointerChainCoupling.readStart (1, 1) :=
    isOnlineQueryBound_queryPoint PointerChainCoupling.address
  refine ⟨hc.isTotalQueryBound_toQuantumBatch, hc.isPointBound_toQuantumBatch, ?_⟩
  intro M state puzzle
  rcases state with ⟨h, word⟩
  subst M
  simp [retainedBudget]

/-- The full three-phase security theorem applies to oracle-dependent retained advice. The
fresh challenge is averaged after preprocessing; no claim of pointwise failure is needed. -/
example (ρ : SubState Unit) :
    qromDelayAdvantage
      (quantumWindowScheme (n := 1) (B := 83) (by decide : hashInputBound 1 ≤ 83) 0)
      (PointerChainCoupling.adversary ρ) ≤ min 1 (rankDelayBound 1 1 0 0 0 1 1) := by
  exact qromDelaySecure_quantumWindowScheme (b := 1) (n := 1) (m := 0) (B := 83)
    (by decide : 1 ≤ 32)
    (by decide : 1 < 2 ^ 32) (by decide : hashInputBound 1 ≤ 83)
    retainedBudget (by decide) (PointerChainCoupling.adversary ρ) (retained_budget ρ)

/-- The concrete 24-byte-link, sixteen-chain encoding fits an 86-byte raw window for every
step count. Both online budget constraints contribute to the public security certificate. -/
example (m : ℕ) (budget : DelayBudget) (hkey : budget.onlineRounds < keyRound 16 m) :
    QROMDelaySecure
      (quantumWindowScheme (b := 24) (n := 16) (B := 86) (by decide) m) budget
      (min 1 (rankDelayBound 24 16 m budget.onlineRounds
        (min budget.onlineWidth budget.onlinePoints)
        budget.preprocessingRounds budget.preprocessingPoints)) := by
  exact qromDelaySecure_quantumWindowScheme_min_width_points (by decide) (by norm_num)
    (by decide) budget hkey

/-- Zero online points force effective width zero even when both the round and hardware-width
ceilings are positive. The certificate keeps the same syntactic adversary budget. -/
example (m r k : ℕ) (hkey : r < keyRound 16 m) :
    QROMDelaySecure
      (quantumWindowScheme (b := 24) (n := 16) (B := 86) (by decide) m)
      ⟨0, 0, r, 0, k⟩ (min 1 (rankDelayBound 24 16 m r 0 0 0)) := by
  simpa using qromDelaySecure_quantumWindowScheme_min_width_points (b := 24) (n := 16)
    (m := m) (B := 86) (by decide) (by norm_num) (by decide) ⟨0, 0, r, 0, k⟩ hkey

/-- A raw input in the byte window that has no honest typed interpretation. -/
@[expose]
def emptyInput : ByteArray.Bounded 83 := ⟨ByteArray.empty, by decide⟩

private theorem emptyInput_ne_hashInputWindow (t : TypedPoint 1 1) :
    emptyInput ≠ hashInputWindow (by decide : hashInputBound 1 ≤ 83) t := by
  intro h
  have hs := congrArg (fun d : ByteArray.Bounded 83 ↦ d.toByteArray.size) h
  have hmin : 52 ≤ (hashInput t).size := by
    rw [size_hashInput]
    cases t <;> norm_num
  change 0 = (hashInput t).size at hs
  omega

/-- Even with arbitrary programmed words, a malformed raw cell retains its base response. -/
example (salt : Bytes 16) (x : Bytes 1)
    (H : ByteArray.Bounded 83 → Bytes 32) (W : PathValue 1 0 → Bytes 32) :
    programPath (by decide : 1 ≤ 32) (by decide : hashInputBound 1 ≤ 83)
      salt x Fin.elim0 H W emptyInput = H emptyInput := by
  apply programPath_apply_of_avoids
  intro v hv
  exact emptyInput_ne_hashInputWindow _ hv.symm

/-- Off-image preprocessing queries have zero path incidence, before or after conditioning
on any fixed salt and public link. -/
example (salt : Bytes 16) (x : Bytes 1) :
    Pr{let W ← $ᵗ (PathValue 1 0 → Bytes 32)}[
      ∃ v, emptyInput = rawPathInput (by decide : 1 ≤ 32)
        (by decide : hashInputBound 1 ≤ 83) salt x Fin.elim0 v W] = 0 := by
  exact prEvent_eq_zero_of_forall_not _ _ fun W ⟨v, hv⟩ ↦
    emptyInput_ne_hashInputWindow _ hv

end VCVioTest.PointerChainPreprocessing
