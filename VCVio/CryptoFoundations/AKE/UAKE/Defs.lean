/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.AKE.UAKE.Party
import VCVio.CryptoFoundations.AKE.UAKE.Transcript

/-
# UAKE Core Definitions

This file defines a Unilaterally Authenticated Key Exchange (UAKE) scheme from
Dodis and Fiore 2017 (https://eprint.iacr.org/2017/109.pdf). A UAKE scheme is a
possibly interactive scheme between two parties: A keyed party T, and an
unkeyed party U. At the end of the protocol, both parties output a key, which
is guaranteed to be indistinguishable from random, and T is authenticated to U
(but not vice-versa).
-/

open OracleSpec OracleComp

namespace AKE.UAKE

variable {K UK TK W : Type}

/- A UAKE scheme with a fixed number of rounds. The keyed (authenticated) party
   is T; the unkeyed (unauthenticated) party is U. -/
structure Scheme (m : Type → Type) (K UK TK W : Type) where
  rounds : ℕ
  setup : m (UK × TK)
  U : Party m UK W (Option K)
  T : Party m TK W (Option K)

/- The UAKE correctness experiment (Def. 7). The parties' keys are sampled
   using the setup routine, then both parties are run honestly to completion.
   The protocol is correct if both (honest) parties output the same key. -/
def CorrectExp [DecidableEq K] (proto : Scheme ProbComp K UK TK W) : ProbComp Bool := do
  let (uk, tk) ← proto.setup
  let (uOut, tOut) ← runHonest proto.U proto.T uk tk (proto.rounds + 1)
  return decide (uOut.join = none ∨ tOut.join = none ∨ uOut.join = tOut.join)

def PerfectlyCorrect [DecidableEq K] (proto : Scheme ProbComp K UK TK W) : Prop :=
  Pr[= true | CorrectExp proto] = 1

structure TSession {m : Type → Type} (proto : Scheme m K UK TK W) where
  state : proto.T.State
  transcript : Transcript W
  key : Option (Option K)
  revealed : Bool

structure Env {m : Type → Type} (proto : Scheme m K UK TK W) where
  clock : ℕ
  challenge : Session proto.U.State W
  challengeDone : Bool
  tSessions : List (TSession proto)

inductive Op (W : Type) where
  | openT : Op W
  | stepT : ℕ → W → Op W
  | revealT : ℕ → Op W
  | stepChallenge : W → Op W

def oracleSpec (K W : Type) : OracleSpec (Op W)
  | .openT => ℕ × Option W
  | .stepT _ _ => W ⊕ Unit
  | .revealT _ => Option K
  | .stepChallenge _ => W ⊕ Unit

def oracleImpl {m : Type → Type} [Monad m] (proto : Scheme m K UK TK W) (tk : TK) :
    QueryImpl (oracleSpec K W) (StateT (Env proto) m) := fun op =>
  match op with
  | .openT => do
      let r ← (proto.T.init tk : m _)
      let env ← get
      let (tr, c') := recordOpt ⟨[]⟩ r.opening env.clock
      let sid := env.tSessions.length
      let t0 : TSession proto := ⟨r.state, tr, none, false⟩
      set { env with clock := c', tSessions := env.tSessions ++ [t0] }
      pure (sid, r.opening)
  | .stepT sid w => do
      let env ← get
      match env.tSessions[sid]? with
      | none => pure (.inr ())
      | some t =>
        match t.key with
        | some _ => pure (.inr ())
        | none => do
          match ← (proto.T.step t.state w : m _) with
          | .reject => pure (.inr ())
          | .acceptAndSend st' w' done =>
              let (tr1, c1) := recordOne t.transcript w env.clock
              let (tr2, c2) := recordOne tr1 w' c1
              let key ← if done then (proto.T.output st' : m _) else pure none
              let t' : TSession proto := ⟨st', tr2, key, t.revealed⟩
              set { env with clock := c2, tSessions := env.tSessions.set sid t' }
              pure (.inl w')
          | .complete st' =>
              let (tr1, c1) := recordOne t.transcript w env.clock
              let key ← (proto.T.output st' : m _)
              let t' : TSession proto := ⟨st', tr1, key, t.revealed⟩
              set { env with clock := c1, tSessions := env.tSessions.set sid t' }
              pure (.inr ())
  | .revealT sid => do
      let env ← get
      match env.tSessions[sid]? with
      | none => pure none
      | some t =>
        set { env with tSessions := env.tSessions.set sid { t with revealed := true } }
        pure t.key.join
  | .stepChallenge w => do
      let env ← get
      if env.challengeDone then pure (.inr ())
      else do
          match ← (proto.U.step env.challenge.state w : m _) with
          | .reject => pure (.inr ())
          | .acceptAndSend st' w' done =>
              let (tr1, c1) := recordOne env.challenge.transcript w env.clock
              let (tr2, c2) := recordOne tr1 w' c1
              set { env with clock := c2, challenge := ⟨st', tr2⟩, challengeDone := done }
              pure (.inl w')
          | .complete st' =>
              let (tr1, c1) := recordOne env.challenge.transcript w env.clock
              set { env with clock := c1, challenge := ⟨st', tr1⟩, challengeDone := true }
              pure (.inr ())

structure Adversary {m : Type → Type} (proto : Scheme m K UK TK W) where
  State : Type
  challenge : UK → Option W → OracleComp (unifSpec + oracleSpec K W) State
  post : State → Option K → OracleComp (unifSpec + oracleSpec K W) Bool

structure ChallengeResult {m : Type → Type} (proto : Scheme m K UK TK W) where
  K0 : Option K
  challengeTr : Transcript W
  oracleTrs : List (Transcript W)

def challengeSession {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    {proto : Scheme m K UK TK W} (A : Adversary proto) (uk : UK) (tk : TK) :
    m (ChallengeResult proto × (A.State × Env proto × TK)) := do
  let u0 ← (proto.U.init uk : m _)
  let (tr0, c0) := recordOpt ⟨[]⟩ u0.opening 0
  let init : Env proto := ⟨c0, ⟨u0.state, tr0⟩, false, []⟩
  let (st, env) ← (simulateQ (withUnif (oracleImpl proto tk)) (A.challenge uk u0.opening)).run init
  let k0 ← (proto.U.output env.challenge.state : m _)
  pure (⟨k0.join, env.challenge.transcript, env.tSessions.map (·.transcript)⟩,
    (st, env, tk))

def isPingPong [DecidableEq W] {m : Type → Type} {proto : Scheme m K UK TK W}
    (cr : ChallengeResult proto) : Bool :=
  pingPong (proto.rounds % 2 == 1) cr.oracleTrs cr.challengeTr

def fullPingPong [DecidableEq W] {m : Type → Type} {proto : Scheme m K UK TK W}
    (env : Env proto) (cr : ChallengeResult proto) : Bool :=
  pingPong (proto.rounds % 2 == 1)
    ((env.tSessions.filter (·.revealed)).map (·.transcript)) cr.challengeTr

def finalize [DecidableEq W] {proto : Scheme ProbComp K UK TK W} (A : Adversary proto)
    (st : A.State × Env proto × TK) (cr : ChallengeResult proto) (b : Bool) (K1 : Option K) :
    ProbComp Bool := do
  let (aSt, env, tk) := st
  let Kb := if b then K1 else cr.K0
  let (b', env') ← (simulateQ (withUnif (oracleImpl proto tk)) (A.post aSt Kb)).run env
  if fullPingPong env' cr then $ᵗ Bool
  else pure (b' == b)

def Exp [SampleableType K] [DecidableEq W] {proto : Scheme ProbComp K UK TK W}
    (A : Adversary proto) : ProbComp Bool := do
  let (uk, tk) ← proto.setup
  let b ← $ᵗ Bool
  let (cr, st) ← challengeSession A uk tk
  if cr.K0.isNone then
    let K1 := none
    finalize A st cr b K1
  else if !isPingPong cr then
    return true
  else
    let K1 ← some <$> ($ᵗ K)
    finalize A st cr b K1

noncomputable def advantage [SampleableType K] [DecidableEq W]
    {proto : Scheme ProbComp K UK TK W} (A : Adversary proto) : ℝ :=
  |(Pr[= true | Exp A]).toReal - 1 / 2|

end AKE.UAKE
