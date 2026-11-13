/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.MerkleCollision
public import HashSigTest.GXMSS.MerkleWitnesses
import all HashSig.GXMSS.Security.Interval.Reductions.MerkleGames
import HashSig.GXMSS.Security.Reductions.TargetRegistration.Basic
import HashSig.GXMSS.Security.Reductions.TargetRegistration.Chains

/-!
# Genuine interval target registration controls

A middle interval hashes seven surviving tree nodes. The natural-valued, noncommutative fixture
pins the exact postorder inputs, actual challenge histories and refusal at insufficient capacity.
Private imports supply only the actual setup kernels used by these implementation fixtures.
-/

public section
namespace GXMSS.MerkleRegistrationProbe
open GXMSS.IntervalMerkle GXMSS.Interval.Unforgeability GXMSS.Reductions
open GXMSS.MerkleWitnessProbe OracleComp OracleSpec TweakableHash

/-- Two active middle leaves and four inactive frontier nodes. -/
@[expose] def middle : Interval 3 := ⟨3, 4, by decide⟩

/-- Distinct raw endpoint labels, fixed before the public-seed stage. -/
@[expose] def ends (e : Fin 8) (_ : Fin 1) : ℕ := e.val + 1

/-- Each retained frontier carries its own tagged value. -/
@[expose] def fillers : Fillers middle ℕ := fun node =>
  500 + 1000 * node.val.1.val + 10 * node.val.2.val

/-- Seven independently calculated surviving raw hash inputs, in accepted issue order. -/
@[expose] def expectedTargets : List (Tweak × Input) :=
  [(.inr (0, 3), .inr (.inr (fun _ => 4))),
   (.inr (1, 1), .inr (.inl (520, 2))),
   (.inr (2, 0), .inr (.inl (1500, 371))),
   (.inr (0, 4), .inr (.inr (fun _ => 5))),
   (.inr (1, 2), .inr (.inl (2, 550))),
   (.inr (2, 1), .inr (.inl (2853, 1530))),
   (.inr (3, 0), .inr (.inl (2800, 9277)))]

/-- Pruning neither descends into retained frontiers nor changes surviving child order. -/
private theorem exact_postorder :
    prunedTargetRun (witnessInstance 3 1) middle () ends fillers 99 3 0 =
      (48080, expectedTargets) := by rfl

/-- The public construction has the independently calculated mixed root. -/
theorem exact_root : GXMSS.IntervalMerkle.root (witnessInstance 3 1) middle () ends fillers =
    48080 := by rfl

/-- Exact finite capacity for this pruned traversal. -/
private theorem exact_count : prunedCount middle 3 0 = 7 := by decide

/-- The original challenge handler registers all seven actual inputs in both histories. -/
private theorem genuine_registration :
    (simulateQ (SM_DT_TCR_oracles
      (SM_DT_TCR_Problem.standalone (witnessInstance 3 1).thf 7) ())
      ((tcrPrunedRoot (witnessInstance 3 1) 7 middle ends fillers 99 3 0).run [])).run
        ([], []) = pure ((48080, expectedTargets), expectedTargets, []) := by
  rw [tcrPrunedRoot_run (witnessInstance 3 1) 7 middle () ends fillers 99 []
    (by change 0 + 7 ≤ 7; decide) (by simp)]
  rfl

/-- Refused registration returns the retained fallback and records no invented target. -/
private theorem zero_capacity_refuses :
    (simulateQ (SM_DT_TCR_oracles
      (SM_DT_TCR_Problem.standalone (witnessInstance 3 1).thf 0) ())
      ((tcrPrunedRoot (witnessInstance 3 1) 0 middle ends fillers 99 3 0).run [])).run
        ([], []) = pure ((99, []), [], []) := by rfl

/-- One missing slot refuses the final root query while retaining its six accepted predecessors. -/
private theorem final_query_refused :
    (simulateQ (SM_DT_TCR_oracles
      (SM_DT_TCR_Problem.standalone (witnessInstance 3 1).thf 6) ())
      ((tcrPrunedRoot (witnessInstance 3 1) 6 middle ends fillers 99 3 0).run [])).run
        ([], []) = pure ((99, expectedTargets.take 6), expectedTargets.take 6, []) := by rfl

/-- Initial chain labels chosen so one positive paper step yields the fixed endpoint array. -/
@[expose] def starts (e : Fin 8) (_ : Fin 1) : ℕ := 2 * e.val

/-- All eight epochs contribute their positive chain step before the seven pruned tree targets. -/
@[expose] def expectedAll : List (Tweak × Input) :=
  [(.inl (0, 0, 0), .inl 0), (.inl (1, 0, 0), .inl 2),
   (.inl (2, 0, 0), .inl 4), (.inl (3, 0, 0), .inl 6),
   (.inl (4, 0, 0), .inl 8), (.inl (5, 0, 0), .inl 10),
   (.inl (6, 0, 0), .inl 12), (.inl (7, 0, 0), .inl 14)] ++ expectedTargets

/-- The actual one-step chain produces the independently labeled endpoint at every epoch. -/
private theorem endpoints_eq : GXMSS.endpoints (witnessInstance 3 1) () starts = ends := by
  funext e i
  change (witnessInstance 3 1).chain () e i 0 (0 + 1) (starts e i) = ends e i
  rw [HashInstance.chain_succ _ _ _ _ _ _ _ (by decide), HashInstance.chain_zero]
  change (2 * e.val) / 2 + 0 + 1 = e.val + 1
  omega

/-- Complete chain registration precedes the independently enumerated pruned tree schedule. -/
private theorem all_targets : endpointTargets (witnessInstance 3 1) () starts ++
    prunedTargets (witnessInstance 3 1) middle () ends fillers = expectedAll := by
  have hzero (ep : Fin 8) (i : Fin 1) (j : Fin 1) :
      (witnessInstance 3 1).chain () ep i 0 j.val (starts ep i) = starts ep i := by
    have hj : j.val = 0 := by omega
    rw [hj, HashInstance.chain_zero]
  simp only [endpointTargets, chainTargets, hzero, List.ofFn_succ, List.ofFn_zero]
  rfl

/-- Exact-capacity interpretation includes inactive-epoch chains and all surviving tree inputs. -/
private theorem full_registration :
    (simulateQ (SM_DT_TCR_oracles
      (SM_DT_TCR_Problem.standalone (witnessInstance 3 1).thf 15) ())
      ((tcrIntervalCore (witnessInstance 3 1) 15 middle starts fillers 99).run [])).run
        ([], []) = pure (((ends, 48080), expectedAll), expectedAll, []) := by
  rw [tcrIntervalCore_run (witnessInstance 3 1) 15 middle () starts fillers 99
    (by change 8 + 7 ≤ 15; decide)]
  rw [endpoints_eq]
  simp only [all_targets, exact_root]

/-- The public primitive retains its original capacity, separately from this exact tree count. -/
theorem primitive_capacity : (merkleTCRProblem (witnessInstance 3 1)).numTargets = 32 := rfl

end GXMSS.MerkleRegistrationProbe
