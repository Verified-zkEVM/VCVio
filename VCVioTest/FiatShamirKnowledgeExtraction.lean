/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.FiatShamir.Sigma.ExtractionCost

/-!
# Fiat–Shamir final-query and replay-cost boundaries

The verifier in this fixture accepts independently of its challenge. A final query is still
needed to put a zero-query prover's proof into the forkable log. An adaptive prover makes that
final query either a cache hit or a fresh request, depending on its first answer.
-/

public section

open OracleComp OracleSpec FiatShamir

namespace FiatShamirKnowledgeExtractionTest

/-- An always-valid relation with a challenge-independent verifier. -/
@[expose]
def protocol : SigmaProtocol Unit Unit Bool Unit Bool Unit (fun _ _ => true) where
  commit _ _ := pure (false, ())
  respond _ _ _ _ := pure ()
  verify _ _ _ _ := true
  sim _ := pure false
  extract _ _ _ _ := pure ()

/-- Deterministic generation of the fixture's sole instance and witness. -/
@[expose]
def relation : GenerableRelation Unit Unit (fun _ _ => true) where
  gen := pure ((), ())
  gen_sound _ _ _ := rfl

/-- A proof emitted without consulting the random oracle. -/
@[expose]
def noQuery : KnowledgeProver (Stmt := Unit) (Commit := Bool) (Chal := Bool) (Resp := Unit) Unit :=
  fun _ _ => pure (false, ())

/-- The first hash answer chooses the final proof's commitment. -/
@[expose]
def adaptive : KnowledgeProver (Stmt := Unit) (Commit := Bool) (Chal := Bool) (Resp := Unit) Unit :=
  fun _ _ => do
    let reply ← HasQuery.query (spec := Unit × Bool →ₒ Bool) ((), false)
    pure (reply, ())

/-- Fixed replies for inspecting structural executions of the wrapped oracle. -/
@[expose]
def answers (reply : Bool) : QueryImpl (Fork.wrappedSpec Bool) Id :=
  QueryImpl.ofFn (fun n : ℕ => (0 : Fin (n + 1))) + QueryImpl.ofFn (fun _ : Unit => reply)

example : nmaHashQueryBound Unit (noQuery () ()) 0 := by trivial

theorem adaptive_bound : nmaHashQueryBound Unit (adaptive () ()) 1 := by
  change IsQueryBoundP
    ((liftM ((unifSpec + (Unit × Bool →ₒ Bool)).query (.inr ((), false))) :
      OracleComp (unifSpec + (Unit × Bool →ₒ Bool)) Bool) >>= fun reply => pure (reply, ())) _ 1
  simp

example : nmaHashQueryBound Unit
    ((proverWithFinalQuery protocol relation Unit noQuery ()).main ()) 1 :=
  proverWithFinalQuery_hash_bound protocol relation Unit noQuery () () 0 (by trivial)

example : IsQueryBoundP
    (nmaForkExtract protocol relation Unit
      (proverWithFinalQuery protocol relation Unit noQuery ()) 0 ()) (· = .inr ()) 2 :=
  knowledgeExtractor_challenge_bound protocol relation Unit noQuery () () 0 (by trivial)

example : IsQueryBoundP
    (nmaForkExtract protocol relation Unit
      (proverWithFinalQuery protocol relation Unit adaptive ()) 1 ()) (· = .inr ()) 4 :=
  knowledgeExtractor_challenge_bound protocol relation Unit adaptive () () 1
    adaptive_bound

example : evalWithAnswerFn (answers false)
    ((fun t => t.queryLog.length) <$>
      Fork.runTrace protocol relation Unit (proverWithFinalQuery protocol relation Unit noQuery ())
        ()) = 1 := rfl

example : evalWithAnswerFn (answers false)
    ((fun t => t.queryLog.length) <$>
      Fork.runTrace protocol relation Unit (proverWithFinalQuery protocol relation Unit adaptive ())
        ()) = 1 := rfl

example : evalWithAnswerFn (answers true)
    ((fun t => t.queryLog.length) <$>
      Fork.runTrace protocol relation Unit (proverWithFinalQuery protocol relation Unit adaptive ())
        ()) = 2 := rfl

example : evalWithAnswerFn (answers false)
    ((fun t => (Fork.forkPoint Unit 0 t).isSome) <$>
      Fork.runTrace protocol relation Unit (proverWithFinalQuery protocol relation Unit noQuery ())
        ()) = true := rfl

example :
    let acc := knowledgeAcceptance protocol relation Unit noQuery () ()
    acc * (acc / (0 + 1 : ENNReal) - challengeSpaceInv Bool) ≤
      Pr{let w ← knowledgeExtractor protocol relation Unit noQuery () 0 ()}[(fun _ _ => true) () w =
        true] := by
  simpa only [Nat.cast_zero] using knowledgeExtractor_success protocol relation Unit
    (by intro x pc c₁ c₂ p₁ p₂ hne hv₁ hv₂ w hw; rfl)
    noQuery () () 0 (by trivial)

-- A rejected selection still consumes its first path; it does not replay a second one.
example : contextFork (pure () : OracleComp coinSpec Unit)
    (fun _ => 0) () (fun _ => none) = pure none := rfl

end FiatShamirKnowledgeExtractionTest
