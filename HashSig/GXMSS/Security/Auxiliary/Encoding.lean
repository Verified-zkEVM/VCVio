/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Encoding.Retry
public import VCVio.OracleComp.SimSemantics.Append

/-!
# Adaptive target collisions for incomparable encodings

Definition 15 of ePrint 2025/055 uses a public parameter sampled once, classical adaptive queries,
independent randomizer draws, bounded retries and a bound on recorded epochs. Eligible exhausted
queries consume a record; rejected queries leave the transcript intact. A collision has the same
epoch and successful word and a different message/randomizer pair. The game uses `ProbComp` for
public sampling and adversarial randomness, and only the named challenge oracle for adaptive
queries. `UniformSamplingLaws` records the separate finite uniform sampling laws for the paper
interpretation. Bounds quantify over explicitly chosen adversary classes; efficiency remains an
external obligation. No concrete encoding security or retry amplification bound is proved.
-/

public section

namespace GXMSS.Encoding.TargetCollisionResistance

open OracleComp OracleSpec ENNReal

variable {PP M R E : Type} {n radix : ℕ}

/-- One eligible query, including an explicit empty result after retry exhaustion. -/
structure Record (M R E : Type) (n radix : ℕ) where
  /-- The epoch consumed by this query. -/
  epoch : E
  /-- The requested message, retained even after exhaustion. -/
  message : M
  /-- The successful word and its randomizer, or returned failure. -/
  result : Option (Codeword n radix × R)

/-- An ordered list of eligible query records. -/
abbrev Transcript (M R E : Type) (n radix : ℕ) := List (Record M R E n radix)

/-- A consumed epoch cannot be queried again, including after a failed result. -/
@[expose] def used [DecidableEq E] (s : Transcript M R E n radix) (ep : E) : Bool :=
  s.any fun entry => decide (entry.epoch = ep)

/-- Reject a repeated epoch or a query beyond the record cap. -/
@[expose] def rejected [DecidableEq E] (p : ℕ) (s : Transcript M R E n radix) (ep : E) : Bool :=
  decide (p ≤ s.length) || used s ep

/-- Finish a query by appending exactly one record if eligible, including on exhaustion. -/
@[expose] def finish [DecidableEq E] (p : ℕ) (s : Transcript M R E n radix)
    (msg : M) (ep : E) (answer : Option (Codeword n radix × R)) :
    Option (Codeword n radix × R) × Transcript M R E n radix :=
  if rejected p s ep then (none, s) else (answer, s ++ [⟨ep, msg, answer⟩])

/-- Rejection preserves the entire first record and all older records. -/
theorem finish_of_rejected [DecidableEq E] (p : ℕ) (s : Transcript M R E n radix)
    (msg : M) (ep : E) (answer : Option (Codeword n radix × R))
    (h : rejected p s ep = true) : finish p s msg ep answer = (none, s) := by
  simp [finish, h]

/-- An eligible exhausted query appends its message and consumed epoch with a failed result. -/
theorem finish_none_of_eligible [DecidableEq E] (p : ℕ) (s : Transcript M R E n radix)
    (msg : M) (ep : E) (h : rejected p s ep = false) :
    finish p s msg ep none = (none, s ++ [⟨ep, msg, none⟩]) := by
  simp [finish, h]

/-- Every completed transition preserves the record bound from a bounded transcript. -/
theorem length_finish_le [DecidableEq E] (p : ℕ) (s : Transcript M R E n radix)
    (msg : M) (ep : E) (answer : Option (Codeword n radix × R)) (h : s.length ≤ p) :
    let result := finish p s msg ep answer
    let transcript := result.2
    transcript.length ≤ p := by
  dsimp
  unfold finish
  split_ifs with hr
  · exact h
  · have hp : s.length < p ∧ used s ep = false := by simpa [rejected] using hr
    simpa using Nat.succ_le_of_lt hp.1

/-- Every old record remains in the transcript after any transition. -/
theorem mem_finish_of_mem [DecidableEq E] (p : ℕ) (s : Transcript M R E n radix)
    (msg : M) (ep : E) (answer : Option (Codeword n radix × R))
    (entry : Record M R E n radix) (h : entry ∈ s) : entry ∈ (finish p s msg ep answer).2 := by
  unfold finish
  split_ifs <;> simp_all

/-- An eligible completed query consumes its epoch for either successful or failed answers. -/
theorem used_finish_of_eligible [DecidableEq E] (p : ℕ) (s : Transcript M R E n radix)
    (msg : M) (ep : E) (answer : Option (Codeword n radix × R))
    (h : rejected p s ep = false) : used (finish p s msg ep answer).2 ep = true := by
  simp [finish, h, used]

/-- A repeated epoch is rejected regardless of the message and the earlier outcome. -/
theorem rejected_of_used [DecidableEq E] (p : ℕ) (s : Transcript M R E n radix)
    (ep : E) (h : used s ep = true) : rejected p s ep = true := by
  simp [rejected, h]

/-- A zero record budget rejects every request. -/
theorem rejected_zero [DecidableEq E] (s : Transcript M R E n radix) (ep : E) :
    rejected 0 s ep = true := by simp [rejected]

section Retry

variable {m : Type → Type*} [Monad m]

/-- First-success encoding with fresh randomness and a finite attempt budget. -/
abbrev retry := @IncomparableEncoding.retry

/-- Zero retries perform no draw and return exhaustion. -/
theorem retry_zero (enc : IncomparableEncoding PP M R E n radix) (sample : m R)
    (pp : PP) (msg : M) (ep : E) : retry enc sample pp msg ep 0 = pure none :=
  enc.retry_zero sample pp msg ep

/-- One attempt returns exactly the optional word paired with its sampled randomizer. -/
theorem retry_one (enc : IncomparableEncoding PP M R E n radix) (sample : m R)
    (pp : PP) (msg : M) (ep : E) :
    retry enc sample pp msg ep 1 =
      sample >>= fun r => pure ((enc.value pp msg r ep).map fun word => (word, r)) :=
  enc.retry_one sample pp msg ep

end Retry

/-- The query exposes both the successful word and the sampled randomizer. -/
abbrev challengeSpec (M R E : Type) (n radix : ℕ) : OracleSpec (M × E) :=
  (M × E) →ₒ Option (Codeword n radix × R)

/-- Explicit sampling and resource parameters around an arbitrary incomparable encoding. -/
structure Problem (PP M R E : Type) (n radix : ℕ) where
  /-- The global incomparable encoding interface. -/
  enc : IncomparableEncoding PP M R E n radix
  /-- Public parameter sampling, performed once before the adversary starts. -/
  paramGen : ProbComp PP
  /-- The randomizer computation rerun for each encoding attempt. -/
  randomGen : ProbComp R
  /-- The maximum number of eligible recorded requests. -/
  numRecords : ℕ
  /-- The maximum number of randomizer draws per eligible request. -/
  numRetries : ℕ

/-- A fully adaptive classical adversary sees the public parameter and each oracle reply. -/
structure Adversary (prob : Problem PP M R E n radix) where
  /-- Private random draws and challenge queries can be interleaved and depend on prior replies. -/
  find : PP → OracleComp (unifSpec + challengeSpec M R E n radix) (M × R × E)

/-- The challenge handler rejects before sampling, and records returned exhaustion as data. -/
@[expose] def challengeOracle [DecidableEq E] (prob : Problem PP M R E n radix) (pp : PP) :
    QueryImpl (challengeSpec M R E n radix)
      (StateT (Transcript M R E n radix) ProbComp) := fun q => do
  let s ← get
  if rejected prob.numRecords s q.2 then return none
  else
    let answer ← ((retry prob.enc prob.randomGen pp q.1 q.2 prob.numRetries :
      ProbComp (Option (Codeword n radix × R))) :
      StateT (Transcript M R E n radix) ProbComp (Option (Codeword n radix × R)))
    let result := finish prob.numRecords s q.1 q.2 answer
    set result.2
    return result.1

/-- Rejected queries return without drawing randomness or changing the transcript. -/
theorem challengeOracle_run_of_rejected [DecidableEq E]
    (prob : Problem PP M R E n radix) (pp : PP) (q : M × E)
    (s : Transcript M R E n radix) (h : rejected prob.numRecords s q.2 = true) :
    (challengeOracle prob pp q).run s = pure (none, s) := by
  simp [challengeOracle, h]

/-- Every eligible returned answer records exactly one query, including returned exhaustion. -/
theorem challengeOracle_run_of_eligible [DecidableEq E]
    (prob : Problem PP M R E n radix) (pp : PP) (q : M × E)
    (s : Transcript M R E n radix) (h : rejected prob.numRecords s q.2 = false) :
    (challengeOracle prob pp q).run s =
      retry prob.enc prob.randomGen pp q.1 q.2 prob.numRetries >>= fun answer =>
        pure (answer, s ++ [⟨q.2, q.1, answer⟩]) := by
  simp [challengeOracle, h, finish]

/-- Forward private random draws while retaining the same challenge transcript. -/
@[expose] def oracles [DecidableEq E] (prob : Problem PP M R E n radix) (pp : PP) :
    QueryImpl (unifSpec + challengeSpec M R E n radix)
      (StateT (Transcript M R E n radix) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (Transcript M R E n radix) ProbComp) + challengeOracle prob pp

/-- Check the same epoch and word and a distinct message/randomizer pair.
Failed entries never provide a collision target. -/
@[expose] def valid [DecidableEq M] [DecidableEq R] [DecidableEq E]
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (s : Transcript M R E n radix)
    (collision : M × R × E) : Bool :=
  let candidate := collision.2
  match enc.value pp collision.1 candidate.1 candidate.2 with
  | none => false
  | some word => s.any fun entry =>
      match entry.result with
      | none => false
      | some (target, r) => decide (entry.epoch = candidate.2 ∧ target = word ∧
          (entry.message, r) ≠ (collision.1, candidate.1))

/-- The Boolean experiment preserves missing mass from generation or adversarial interaction. -/
@[expose] def experiment [DecidableEq M] [DecidableEq R] [DecidableEq E]
    {prob : Problem PP M R E n radix} (adv : Adversary prob) : ProbComp Bool := do
  let pp ← prob.paramGen
  let (collision, transcript) ← (simulateQ (oracles prob pp) (adv.find pp)).run []
  return valid prob.enc pp transcript collision

/-- The public successful-output measure, with no conditioning on experiment termination. -/
@[expose] noncomputable def outputMeasure [DecidableEq M] [DecidableEq R] [DecidableEq E]
    {prob : Problem PP M R E n radix}
    (adv : Adversary prob) : MeasureTheory.Measure Bool := 𝒟[experiment adv]

/-- Winning mass is measured at the returned Boolean value `true`. -/
@[expose] noncomputable def advantage [DecidableEq M] [DecidableEq R] [DecidableEq E]
    {prob : Problem PP M R E n radix}
    (adv : Adversary prob) : ℝ≥0∞ := outputMeasure adv {true}

/-- The paper's finite uniform sampling specialization requires runtime laws for fresh draws. -/
@[expose] def UniformSamplingLaws [Fintype PP] [Fintype R]
    (prob : Problem PP M R E n radix) : Prop :=
  UniformSampler ProbCompRuntime.probComp prob.paramGen ∧
    UniformSampler ProbCompRuntime.probComp prob.randomGen ∧
    SamplingLaws ProbCompRuntime.probComp

/-- A failed encoding cannot win against any transcript. -/
theorem valid_of_failure [DecidableEq M] [DecidableEq R] [DecidableEq E]
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (s : Transcript M R E n radix)
    (collision : M × R × E)
    (h : let candidate := collision.2; enc.value pp collision.1 candidate.1 candidate.2 = none) :
    valid enc pp s collision = false := by simp [valid, h]

/-- An empty transcript has no target, even if the collision encodes successfully. -/
theorem valid_nil [DecidableEq M] [DecidableEq R] [DecidableEq E]
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (collision : M × R × E) :
    valid enc pp [] collision = false := by
  let candidate := collision.2
  change (match enc.value pp collision.1 candidate.1 candidate.2 with
    | none => false
    | some _ => false) = false
  split <;> rfl

/-- The public measure agrees with the pinned Boolean output probability. -/
theorem advantage_eq_probability [DecidableEq M] [DecidableEq R] [DecidableEq E]
    {prob : Problem PP M R E n radix}
    (adv : Adversary prob) :
    advantage adv = 𝒟[experiment adv] {true} := rfl

end GXMSS.Encoding.TargetCollisionResistance
