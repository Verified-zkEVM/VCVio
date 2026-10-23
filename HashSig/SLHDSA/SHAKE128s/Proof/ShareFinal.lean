/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ShareEvent
public import HashSig.SLHDSA.SHAKE128s.Proof.AnswerFired
public import HashSig.SLHDSA.SHAKE128s.Proof.RecordedWalkTable

/-!
# The shared half at one setup

At one setup the chain is: the real game has the law of the capped real game (the cap never
fires, `ShareRealCap`); the capped real game is coupled with the lenient game so that the event
raises the lenient flag (`ShareWhole`, `ShareEvent`); the lenient flag has the law of the blind
flag (`ShareUntilBad`). `BySourceShared` averages this over `SK.prf`, the public seed and the
table. This file states the real event at a setup (`RealEvent`), the setup a drawn walk is
(`setupOf`), and the commutation of expectations (`ex_comm`) used to average.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

namespace SlhDsaSecurity.ShareFinal

open Security CanonicalGraph ShareGame ShareCouple ShareInv ShareWhole ShareEvent

/-! ## At one setup -/

/-- The real event at a setup, on the flattened real game's output. -/
def RealEvent (setup : Setup)
    (real : (((Forgery × Multiplicative RecordedQueries.Tally) × (Bool × RecordedQueries.Tally)) ×
      SigningLog) × QueryCache HashSpec) : Prop :=
  RoutedSplit.InputBad (SharedJoin.recordedTraceOf (realPair setup real)) ∨
    Target127.Late (realPair setup real)

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Security.countQueries

/-! ## At one walk -/

/-- The setup a drawn walk is. -/
def setupOf (prfSeed publicSeed : Digest) (table : Cells × Padding) : Setup :=
  ⟨prfSeed, publicSeed, table⟩

theorem goodWalk_iff (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    Target.GoodWalk (WalkTable.walkOfTable prfSeed publicSeed table) ↔
      (setupOf prfSeed publicSeed table).Good := Iff.rfl

/-! ## Expectations commute -/

open BlindCharge in
theorem ex_comm {α β : Type} (mx : ProbComp α) (my : ProbComp β) (f : α → β → ℝ≥0∞) :
    ex mx (fun a => ex my (f a)) = ex my (fun b => ex mx (fun a => f a b)) := by
  unfold ex
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun b => tsum_congr fun a => ?_
  ring

end SlhDsaSecurity.ShareFinal
