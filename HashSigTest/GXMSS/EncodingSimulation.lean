/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.EncodingSimulation
public import HashSigTest.GXMSS.SplicedView
import all HashSig.GXMSS.Security.Interval.Reductions.EncodingSimulation
import all HashSigTest.GXMSS.SplicedView
import HashSig.GXMSS.Chain

/-!
# Active encoding records and all-request budget controls

Seven signing requests produce two eligible records, including one returned exhausted retry.
The recorded successful message and a distinct candidate message share a codeword. Sampling,
first-message history and the native encoding collision observation are retained explicitly.
-/

public section
namespace GXMSS.EncodingSimulationProbe
open GXMSS.IntervalMerkle GXMSS.Interval.Reductions GXMSS.Reductions GXMSS.SplicedViewProbe
open SyncSignatureUnforgeability IncomparableEncoding OracleComp OracleSpec

/-- Epoch four exhausts; every message at every other epoch shares one incomparable word. -/
@[expose] def encoding : IncomparableEncoding Unit Bool Unit (Fin 8) 1 2 where
  code := {fun _ => 1}
  incomparable := by
    intro x hx y hy hne
    exact (hne ((Set.mem_singleton_iff.mp hx).trans
      (Set.mem_singleton_iff.mp hy).symm)).elim
  encode := fun _ _ _ ep =>
    if ep = 4 then none else some ⟨fun _ => 1, Set.mem_singleton _⟩

/-- Every issued request counts, including three repeats and two fresh inactive epochs. -/
theorem seven_requests : SigningQueryBound 7 adversary := by
  intro pk
  suffices ∀ a b c d e f g : Option (GXMSS.Signature Unit Bool 3 1),
      IsQueryBoundP (pure (3,
        a.isNone && b.isNone && c.isSome && d.isNone && e.isNone && f.isNone && g.isNone &&
          (c.map fun sig => sig.ots 0).getD false,
        c.getD (signature false)) :
        OracleComp
          (unifSpec + signingSpec (GXMSS.Reductions.Epoch 3) Bool (GXMSS.Signature Unit Bool 3 1))
          (Forgery (GXMSS.Reductions.Epoch 3) Bool (GXMSS.Signature Unit Bool 3 1)))
        (fun q => q.isRight = true) 0 by
    simpa [adversary, signingQuery] using this
  intro a b c d e f g
  trivial

/-- Fewer than seven calls does not bound this program, despite its two eligible records. -/
theorem not_six_requests : ¬ SigningQueryBound 6 adversary := by
  let : Nonempty (GXMSS.PublicKey Unit Bool) := ⟨⟨false, ()⟩⟩
  simp [SigningQueryBound, adversary, signingQuery]

/-- The actual configured target problem keeps the admitted all-request budget. -/
theorem actual_capacity : (encodingTCRProblem hash encoding 7 1).numRecords = 7 := rfl

/-- The first active record succeeds and the second consumes its epoch with returned failure. -/
@[expose] def expectedRecords : TargetCollisionResistance.Transcript Bool Unit (Fin 8) 1 2 :=
  [⟨3, true, some ((fun _ => 1), ())⟩, ⟨4, false, none⟩]

/-- The ordinary complete signature uses the fixed source keys and their actual interval path. -/
@[expose] def successSignature : GXMSS.Signature Unit Bool 3 1 :=
  GXMSS.Interval.signatureOfWord hash middle
    (GXMSS.Interval.keys hash middle () starts fillers).2 3 ((fun _ => 1), ())

/-- All four first messages remain, including both inactive epochs and exhausted epoch four. -/
@[expose] def sourceHistory : History (Fin 8) Bool (GXMSS.Signature Unit Bool 3 1) :=
  let h₁ := Function.update emptyHistory 2 (some (false, none))
  let h₂ := Function.update h₁ 3 (some (true, some successSignature))
  let h₃ := Function.update h₂ 4 (some (false, none))
  Function.update h₃ 6 (some (true, none))

/-- The candidate's distinct message retains the exact successful signature and complete history. -/
@[expose] def sourceOutput : ExperimentResult (GXMSS.PublicKey Unit Bool) (Fin 8) Bool
    (GXMSS.Signature Unit Bool 3 1) :=
  ((GXMSS.Interval.keys hash middle () starts fillers).1,
    (3, false, successSignature), sourceHistory)

private theorem source_program :
    (simulateQ (intervalEncodingSourceImpl hash encoding 1 middle
      (GXMSS.Interval.keys hash middle () starts fillers).2)
      (adversary.forge (GXMSS.Interval.keys hash middle () starts fillers).1)).run
        (emptyHistory, []) = (do
          let _ ← ($ᵗ Unit : ProbComp Unit)
          let _ ← ($ᵗ Unit : ProbComp Unit)
          pure ((3, false, successSignature), (sourceHistory, expectedRecords))) := by
  have hots (i : Fin 1) : hash.chain () 3 i 0 1 (starts 3 i) = false := by
    simpa only [GXMSS.SplicedViewProbe.hash] using
      (hash.chain_succ () 3 i 0 0 (starts 3 i) (by decide))
  dsimp only [adversary, signingQuery, Forgery]
  simp only [run_simulateQ_query_bind, simulateQ_pure, StateT.run_pure]
  dsimp only [StateT.run, StateT.bind, StateT.pure, intervalEncodingSourceImpl]
  simp [IncomparableEncoding.retry_one, IncomparableEncoding.attempt, encoding,
    IncomparableEncoding.value, emptyHistory, Function.update, Epoch.IsActive, middle,
    successSignature, sourceHistory, expectedRecords, GXMSS.Interval.keys, GXMSS.keys,
    GXMSS.Interval.signatureOfWord, GXMSS.signatureOfWord, hots,
    map_eq_bind_pure_comp, bind_assoc]

/-- The actual source observation recognizes the distinct-message encoding collision. -/
private theorem source_collision :
    intervalEncodingCollision (w := 1) encoding middle sourceOutput = true := by
  simp [intervalEncodingCollision, sourceOutput, sourceHistory, successSignature,
    encoding, IncomparableEncoding.value, Epoch.IsActive, middle, Function.update,
    GXMSS.Interval.signatureOfWord, GXMSS.signatureOfWord, GXMSS.Interval.keys, GXMSS.keys]

/-- The native target predicate accepts the successful first record and exact pair freshness. -/
theorem target_collision :
    TargetCollisionResistance.valid encoding () expectedRecords (false, (), 3) = true := by
  simp [TargetCollisionResistance.valid, expectedRecords, encoding, IncomparableEncoding.value]

end GXMSS.EncodingSimulationProbe
