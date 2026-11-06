/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.Interval.FillerGames
import all HashSig.GXMSS.Security.Auxiliary.Interval.FillerTargets

/-!
# Interval filler game consumers and trust audit

Finite fixtures cover mixed target families, issue order, empty registration and both raw payloads.
The adaptive fixture exercises repeated requests after inactive failure and retry exhaustion through
exactly the shared original signing view. `DirectTrustAudit` covers every declaration in the filler
specification, interaction, opening and reduction modules.

Private imports supply the actual implementation kernels used by these controls. Ordinary public
endpoint applications live in `DirectEndpointApplications`.
-/

public section

open GXMSS GXMSS.IntervalMerkle GXMSS.Interval.Filler
open SyncSignatureUnforgeability GXMSS.Interval
open GXMSS.Interval.MerkleWitnesses OracleSpec OracleComp

private def middle : Interval 3 := ⟨3, 4, by decide⟩

example : targetCapacity .endpointVector middle = 2 := by decide
example : targetCapacity .childPair middle = 2 := by decide

private def vector2 : Target .endpointVector middle := ⟨⟨(0, 2), by decide⟩, by decide⟩

private def vector5 : Target .endpointVector middle := ⟨⟨(0, 5), by decide⟩, by decide⟩

private def pair0 : Target .childPair middle := ⟨⟨(1, 0), by decide⟩, by decide⟩

private def pair3 : Target .childPair middle := ⟨⟨(1, 3), by decide⟩, by decide⟩

private theorem vector_targets : targetList .endpointVector middle = [vector2, vector5] := by
  have hs : (Finset.univ : Finset (Target .endpointVector middle)) =
      [vector2, vector5].toFinset := by decide
  unfold targetList
  rw [hs]
  exact (List.toFinset_sort (· ≤ ·) (by decide : [vector2, vector5].Nodup)).mpr (by decide)

private theorem pair_targets : targetList .childPair middle = [pair0, pair3] := by
  have hs : (Finset.univ : Finset (Target .childPair middle)) = [pair0, pair3].toFinset := by decide
  unfold targetList
  rw [hs]
  exact (List.toFinset_sort (· ≤ ·) (by decide : [pair0, pair3].Nodup)).mpr (by decide)

example : (targetList .endpointVector middle).map address = [(0, 2), (0, 5)] := by
  rw [vector_targets]
  decide
example : (targetList .childPair middle).map address = [(1, 0), (1, 3)] := by
  rw [pair_targets]
  decide
example : targetIndex pair0 = 0 := by rw [targetIndex, pair_targets]; decide
example : targetIndex pair3 = 1 := by rw [targetIndex, pair_targets]; decide
example : targetIndex vector2 = 0 := by rw [targetIndex, vector_targets]; decide
example : targetIndex vector5 = 1 := by rw [targetIndex, vector_targets]; decide
example : targetList .childPair (Interval.full 0) = [] := by simp
example : targetList .endpointVector (Interval.full 0) = [] := by simp
example : targetCapacity .childPair (Interval.full 3) = 0 := by decide
example : targetCapacity .endpointVector (Interval.full 3) = 0 := by decide

private inductive TestInput where
  | digest : Bool → TestInput
  | pair : Bool × Bool → TestInput
  | vector : (Fin 1 → Bool) → TestInput

private inductive TestTweak where
  | chain : Fin 8 × Fin 1 × Fin 1 → TestTweak
  | tree : Fin 4 × Fin 8 → TestTweak
  deriving DecidableEq

private def testHash : HashInstance Unit TestTweak TestInput Bool 3 1 1 where
  thf := ⟨pure (), fun _ _ _ => false⟩
  digestInput := ⟨TestInput.digest, by intro a b hab; cases hab; rfl⟩
  pairInput := ⟨TestInput.pair, by intro a b hab; cases hab; rfl⟩
  vectorInput := ⟨TestInput.vector, by intro a b hab; cases hab; rfl⟩
  chainTweak := ⟨TestTweak.chain, by intro a b hab; cases hab; rfl⟩
  treeTweak := ⟨TestTweak.tree, by intro a b hab; cases hab; rfl⟩
  chain_ne_tree := by intro c t heq; cases heq

private def word : Encoding.Codeword 1 2 := fun _ => 0

private def testEncoding : Encoding.IncomparableEncoding Unit Bool Unit (Fin 8) 1 2 where
  code := {word}
  incomparable := by
    intro x hx y hy hne
    exact (hne ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm)).elim
  encode _ _ _ _ := some ⟨word, by simp⟩

private def starts : Fin 8 → Fin 1 → Bool := fun _ _ => false

private def fillers : Fillers middle Bool := fun _ => false

private def testSignature : GXMSS.Signature Unit Bool 3 1 := ⟨(), fun _ => false, fun _ => false⟩

example : openingFrontierPreimage testHash middle () fillers 0 (by decide)
    (fun _ => false) (fun _ => false) = some (.inr (false, false)) := by decide
example : openingFrontierPreimage testHash middle () fillers 5 (by decide)
    (fun _ => false) (fun _ => false) = some (.inl (fun _ => false)) := by decide
example : openingFrontierPreimage testHash middle () (fun _ => true) 0 (by decide)
    (fun _ => false) (fun _ => false) = none := by decide

private def requests (e : Fin 8) :
    Adversary unifSpec (GXMSS.PublicKey Unit Bool) (Fin 8) Bool
      (GXMSS.Signature Unit Bool 3 1) where
  forge _ := do
    let first ← liftM ((unifSpec + signingSpec (Fin 8) Bool
      (GXMSS.Signature Unit Bool 3 1)).query (.inr (2, false)))
    let repeated ← liftM ((unifSpec + signingSpec (Fin 8) Bool
      (GXMSS.Signature Unit Bool 3 1)).query (.inr (2, true)))
    let exhausted ← liftM ((unifSpec + signingSpec (Fin 8) Bool
      (GXMSS.Signature Unit Bool 3 1)).query (.inr (3, false)))
    let repeatedExhausted ← liftM ((unifSpec + signingSpec (Fin 8) Bool
      (GXMSS.Signature Unit Bool 3 1)).query (.inr (3, true)))
    pure (e, first.isNone && repeated.isNone && exhausted.isNone && repeatedExhausted.isNone,
      testSignature)

private def expectedHistory : History (Fin 8) Bool (GXMSS.Signature Unit Bool 3 1) :=
  Function.update (Function.update emptyHistory 2 (some (false, none))) 3 (some (false, none))

/-- The shared view records both first failures and rejects repeats without overwriting them. -/
private theorem adaptive_failure_view (e : Fin 8) :
    viewFromKeys testHash testEncoding 0 middle (requests e) () starts fillers =
      pure ((GXMSS.Interval.keys testHash middle () starts fillers).1,
        (e, true, testSignature), expectedHistory) := by
  rfl

private noncomputable instance signatureEquality :
    DecidableEq (GXMSS.Signature Unit Bool 3 1) := Classical.decEq _

private instance inputEquality (f : Family) : DecidableEq (Input f Bool 1) := by
  cases f <;> unfold Input <;> infer_instance

private def expectedView (e : Fin 8) :
    ExperimentResult (GXMSS.PublicKey Unit Bool) (Fin 8) Bool (GXMSS.Signature Unit Bool 3 1) :=
  ((GXMSS.Interval.keys testHash middle () starts fillers).1, (e, true, testSignature),
    expectedHistory)

example : extractFillerOpening testHash testEncoding 0 middle .childPair () fillers
    (expectedView 0) = some
      ((⟨⟨(1, 0), by decide⟩, by decide⟩ : Target .childPair middle), (false, false)) := by rfl
example : extractFillerOpening testHash testEncoding 0 middle .endpointVector () fillers
    (expectedView 5) = some
      ((⟨⟨(0, 5), by decide⟩, by decide⟩ : Target .endpointVector middle),
        (fun _ => false)) := by
  apply congrArg some
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · funext i
    fin_cases i
    exact (HashInstance.chain_succ testHash () 5 0 0 0 false (by decide)).trans rfl

example : openingEvent testHash testEncoding 0 middle .childPair () fillers (expectedView 0) =
    true := by decide
example : openingEvent testHash testEncoding 0 middle .endpointVector () fillers (expectedView 5) =
    true := by decide
example : openingEvent testHash testEncoding 0 middle .endpointVector () fillers (expectedView 0) =
    false := by decide

/-- Failed and repeated requests remain in the actual view before a child-pair filler opening. -/
private theorem adaptive_pair_opening :
    openingEvent testHash testEncoding 0 middle .childPair () fillers <$>
      viewFromKeys testHash testEncoding 0 middle (requests 0) () starts fillers = pure true := by
  rw [adaptive_failure_view]
  change (pure (openingEvent testHash testEncoding 0 middle _ () fillers (expectedView _)) :
    ProbComp Bool) = pure true
  rfl

/-- The same adaptive view exposes a leaf-frontier vector at the adjacent inactive epoch. -/
private theorem adaptive_vector_opening :
    openingEvent testHash testEncoding 0 middle .endpointVector () fillers <$>
      viewFromKeys testHash testEncoding 0 middle (requests 5) () starts fillers = pure true := by
  rw [adaptive_failure_view]
  change (pure (openingEvent testHash testEncoding 0 middle _ () fillers (expectedView _)) :
    ProbComp Bool) = pure true
  rfl

example (f : Family) : TweakableHash.SM_DT_UD_Advantage
    (udAdversary testHash testEncoding 0 (Interval.full 3) (requests 0) f) = 0 :=
  udAdvantage_full testHash testEncoding 0 (requests 0) f
example (f : Family) : TweakableHash.SM_DT_PRE_Advantage
    (preAdversary testHash testEncoding 0 (Interval.full 3) (requests 0) f) = 0 :=
  preAdvantage_full testHash testEncoding 0 (requests 0) f


/-- The ordinary public target API specializes to empty families at height zero. -/
theorem full_zero_target_capacity (f : Family) : targetCapacity f (Interval.full 0) = 0 :=
  targetCapacity_full f 0
