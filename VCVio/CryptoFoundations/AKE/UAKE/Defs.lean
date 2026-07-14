/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.AKE.UAKE.Party
import VCVio.CryptoFoundations.AKE.UAKE.Transcript
import VCVio.OracleComp.ProbCompLift

/-!
# UAKE Core Definitions

This file defines a Unilaterally Authenticated Key Exchange (UAKE) scheme from
Dodis and Fiore 2017 (https://eprint.iacr.org/2017/109.pdf). A UAKE scheme is a
possibly interactive scheme between two parties: A keyed party T, and an
unkeyed party U. At the end of the protocol, both parties output a key, which
is guaranteed to be indistinguishable from random, and T is authenticated to U
(but not vice-versa).

Model simplifications
* **Revealing unfinished sessions:** DF'17 only allows the reveal query after
  T's last message. We accept reveal queries at any time, but a reveal before
  completion returns none (the session key is recorded only at completion)
  while still marking the session revealed for the full-ping-pong check. This
  penalizes only the adversary, and is WLOG because an early reveal returns no
  information: any adversary making one has an equivalent adversary that defers
  it.
* **Rejected protocol messages:** DF'17 does not talk about what happens when a
  protocol message is rejected, but it seems necessary to model this in real
  protocols. We allow protocol messages to be rejected, in which case we a)
  drop the message from the transcript and b) continue the session. Other
  choices would be to record the message and halt the session (record and
  continue is degenerate, since an adversary could avoid ping-pong by injecting
  a garbage message), however allowing the adversary to retry is the
  alternative that gives the adversary the most power, so we choose that option
  here.
* **WLOG protocol assumptions:** DF'17 assumes (explicitly) that T speaks last.
  We do not enforce this in our model, nor do we enforce that a protocol has
  the stated number of rounds. Moreover, we do not enforce that U outputs K0
  only at completion, which DF'17 (implicitly) assumes. Such ill-formed
  protocols will be vacuously insecure (if they are correct), because the
  ping-pong predicate will not fire on an honest relay, allowing the trivial
  adversary to win.
* **No 1-round protocols:** Our model can represent only ≥2-round protocols, since a
  party's init function has no variant to indicate that it is done at that
  stage. This is fine for UAKE, since such protocols (where only T contributes
  to the final key) are trivially insecure (if they are correct).
-/

open OracleSpec OracleComp

namespace AKE.UAKE

variable {K UK TK W : Type} {m : Type → Type}

/-- A UAKE scheme with a fixed number of rounds. The keyed (authenticated) party
  is T; the unkeyed (unauthenticated) party is U. -/
structure Scheme (m : Type → Type) (K UK TK W : Type) where
  /-- The total number of protocol messages sent (not round trips) in an honest
    execution of the protocol, which we assume to be fixed for a given
    protocol. We do *not* enforce that the two parties follow this behavior. We
    use this field in conjunction with the "T speaks last" convention of DF'17
    to determine the first speaker in the ping-pong predicates used in the
    security game. -/
  rounds : ℕ
  /-- Create the initial key material used by U and T. In the security game,
    this is called just once by the challenger (as opposed to T's init
    function, which is called each time a new party instance is spun up by the
    adversary), so the parameters it creates are long term and global. -/
  setup : m (UK × TK)
  /-- Unkeyed (unauthenticated) party -/
  U : Party m UK W (Option K)
  /-- Keyed (authenticated) party -/
  T : Party m TK W (Option K)

/-- The UAKE correctness experiment (Def. 7). The parties' keys are sampled
  using the setup routine, then both parties are run honestly to completion.
  The protocol is correct if both (honest) parties output the same key (or
  either party outputs ⊥). -/
def CorrectExp [DecidableEq K] [Monad m] (proto : Scheme m K UK TK W) : m Bool := do
  let (uk, tk) ← proto.setup
  let (uOut, tOut) ← proto.U.runHonest proto.T uk tk (proto.rounds + 1)
  return decide (uOut.join = none ∨ tOut.join = none ∨ uOut.join = tOut.join)

def PerfectlyCorrect [DecidableEq K] [Monad m] (proto : Scheme m K UK TK W)
    (runtime : ProbCompRuntime m) : Prop :=
  Pr[= true | runtime.evalDist (CorrectExp proto)] = 1

/-- The state of a single copy of the T oracle state in the UAKE security
  experiment. -/
structure TSession (proto : Scheme m K UK TK W) where
  /-- T's state -/
  state : proto.T.State
  /-- The transcript for this session -/
  transcript : Transcript W
  /-- The final key output by T for this session:
    * none: Session has not yet completed
    * some none: Session completed with T outputing ⊥
    * some (some k): Session completed with T outputing k -/
  key : Option (Option K)
  /-- Whether the adversary has called reveal on this session -/
  revealed : Bool

/-- Challenge environment for the UAKE security experiment -/
structure Env (proto : Scheme m K UK TK W) where
  /-- The global clock, incremented once for each message sent by a party -/
  clock : ℕ
  /-- The challenge session -/
  challenge : Session proto.U.State W
  /-- Whether the challenge session has completed -/
  challengeDone : Bool
  /-- List of sessions the adversary has opened with copies of T -/
  tSessions : List (TSession proto)

/-- Adversary's oracle operations for UAKE security experiment -/
inductive Op (W : Type) where
  /-- Start a new session. Returns the new session id and the initial protocol
    message (or ⊥ if T is not the first speaker). -/
  | openT : Op W
  /-- Increment an existing session with a given message. Returns the next
    protocol message. -/
  | stepT : ℕ → W → Op W
  /-- Reveal the key for this session -/
  | revealT : ℕ → Op W
  /-- Increment the challenge session (created up front) -/
  | stepChallenge : W → Op W

def oracleSpec (K W : Type) : OracleSpec (Op W)
  | .openT => ℕ × Option W
  | .stepT _ _ => W ⊕ Unit
  | .revealT _ => Option K
  | .stepChallenge _ => W ⊕ Unit

/-- Logic for the UAKE experiment's `Op` queries: the T-session and
  challenge-session oracles. -/
def opImpl [Monad m] (proto : Scheme m K UK TK W) (tk : TK) :
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

/-- Full oracle for the UAKE experiment. `unifSpec` queries (the adversary's
  coin flips) are forwarded to the ambient monad; the remaining queries are
  handled by `opImpl`. -/
def oracleImpl [Monad m] (lift : ProbCompLift m) (proto : Scheme m K UK TK W) (tk : TK) :
    QueryImpl (unifSpec + oracleSpec K W) (StateT (Env proto) m) :=
  let unifImpl : QueryImpl unifSpec (StateT (Env proto) m) := fun q =>
    liftM (lift.liftProbComp ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) q))
  unifImpl + opImpl proto tk

/-- An adversary in the UAKE security game -/
structure Adversary (proto : Scheme m K UK TK W) where
  State : Type
  challenge : UK → Option W → OracleComp (unifSpec + oracleSpec K W) State
  post : State → Option K → OracleComp (unifSpec + oracleSpec K W) Bool

structure ChallengeResult (proto : Scheme m K UK TK W) where
  K0 : Option K
  challengeTr : Transcript W
  oracleTrs : List (Transcript W)

def challengeSession [Monad m] (lift : ProbCompLift m)
    {proto : Scheme m K UK TK W} (A : Adversary proto) (uk : UK) (tk : TK) :
    m (ChallengeResult proto × (A.State × Env proto × TK)) := do
  let u0 ← proto.U.init uk
  let (tr0, c0) := recordOpt ⟨[]⟩ u0.opening 0
  let init : Env proto := ⟨c0, ⟨u0.state, tr0⟩, false, []⟩
  let (st, env) ← (simulateQ (oracleImpl lift proto tk) (A.challenge uk u0.opening)).run init
  let k0 ← (proto.U.output env.challenge.state : m _)
  pure (⟨k0.join, env.challenge.transcript, env.tSessions.map (·.transcript)⟩,
    (st, env, tk))

/-- True if an oracle session matches challenge transcript, meaning that the
  adversary is trivial: It simply relayed the oracle session in the challenge. -/
def isPingPong [DecidableEq W] {proto : Scheme m K UK TK W}
    (cr : ChallengeResult proto) : Bool :=
  pingPong (proto.rounds % 2 == 1) cr.oracleTrs cr.challengeTr

/-- True if the challenge transcript is ping-pong and the adversary called
   reveal on the session. -/
def fullPingPong [DecidableEq W] {proto : Scheme m K UK TK W}
    (env : Env proto) (cr : ChallengeResult proto) : Bool :=
  pingPong (proto.rounds % 2 == 1)
    ((env.tSessions.filter (·.revealed)).map (·.transcript)) cr.challengeTr

def finalize [DecidableEq W] [Monad m] (lift : ProbCompLift m)
    {proto : Scheme m K UK TK W} (A : Adversary proto)
    (st : A.State × Env proto × TK) (cr : ChallengeResult proto) (b : Bool) (K1 : Option K) :
    m Bool := do
  let (aSt, env, tk) := st
  let Kb := if b then K1 else cr.K0
  let (b', env') ← (simulateQ (oracleImpl lift proto tk) (A.post aSt Kb)).run env
  if fullPingPong env' cr then lift.liftProbComp ($ᵗ Bool) else pure (b' == b)

/-- The security experiment from Sec. 3 of DF'17 -/
def Exp [SampleableType K] [DecidableEq W] [Monad m] (lift : ProbCompLift m)
    {proto : Scheme m K UK TK W} (A : Adversary proto) : m Bool := do
  let (uk, tk) ← proto.setup
  let b ← lift.liftProbComp ($ᵗ Bool)
  let (cr, st) ← challengeSession lift A uk tk
  if cr.K0.isNone then
    let K1 := none
    finalize lift A st cr b K1
  else if !isPingPong cr then
    return true
  else
    let K1 ← some <$> lift.liftProbComp ($ᵗ K)
    finalize lift A st cr b K1

noncomputable def advantage [SampleableType K] [DecidableEq W] [Monad m]
    {proto : Scheme m K UK TK W} (runtime : ProbCompRuntime m)
    (A : Adversary proto) : ℝ :=
  |(Pr[= true | runtime.evalDist (Exp runtime.toProbCompLift A)]).toReal - 1 / 2|

end AKE.UAKE
