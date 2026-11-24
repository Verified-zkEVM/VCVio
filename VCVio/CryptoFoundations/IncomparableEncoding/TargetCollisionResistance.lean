/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.Retry
public import VCVio.OracleComp.SimSemantics.Append

/-!
# Target-collision resistance of an incomparable encoding

The experiment samples public parameters `pp` and runs the adversary with a challenge oracle. On a
query `(msg, ep)` the oracle runs the encoding's retry loop for at most `numRetries` draws and
records the epoch, the message and the result. A query whose draws all fail is still recorded,
with result `none`, so it uses up one of the `numRecords` slots and its epoch. The oracle rejects a
query without sampling once `numRecords` records exist, or when its epoch was used before.

The adversary outputs `(m*, r*, ep*)`. It wins if `m*` and `r*` encode at `ep*` to the word of a
successful record at `ep*` whose message/randomizer pair differs from `(m*, r*)`.

The paper samples the public parameters and the randomizers uniformly. `Problem` takes both
samplers as parameters instead.

## References

- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), Definition 15 (T-COLL-RES).
-/

public section

namespace IncomparableEncoding.TargetCollisionResistance

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
    let answer ← ((prob.enc.retry prob.randomGen pp q.1 q.2 prob.numRetries :
      ProbComp (Option (Codeword n radix × R))) :
      StateT (Transcript M R E n radix) ProbComp (Option (Codeword n radix × R)))
    let result := finish prob.numRecords s q.1 q.2 answer
    set result.2
    return result.1

/-- Forward private random draws while retaining the same challenge transcript. -/
@[expose] def oracles [DecidableEq E] (prob : Problem PP M R E n radix) (pp : PP) :
    QueryImpl (unifSpec + challengeSpec M R E n radix)
      (StateT (Transcript M R E n radix) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (Transcript M R E n radix) ProbComp) + challengeOracle prob pp

/-- Whether one transcript entry is a target that the submitted collision hits. The entry must
hold a successful word at the same epoch, equal to the word that the collision encodes to, from a
different message/randomizer pair. A failed entry is never a target. -/
@[expose] def witnesses [DecidableEq M] [DecidableEq R] [DecidableEq E]
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (collision : M × R × E)
    (entry : Record M R E n radix) : Bool :=
  match enc.encode pp collision.1 collision.2.1 collision.2.2, entry.result with
  | some word, some (target, r) =>
      decide (entry.epoch = collision.2.2 ∧ target = word ∧
        (entry.message, r) ≠ (collision.1, collision.2.1))
  | _, _ => false

/-- The adversary wins if some transcript entry witnesses its collision. -/
@[expose] def valid [DecidableEq M] [DecidableEq R] [DecidableEq E]
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (s : Transcript M R E n radix)
    (collision : M × R × E) : Bool :=
  s.any (witnesses enc pp collision)

/-- Sample the public parameters, run the adversary against the challenge oracle, and check its
output against the final transcript. -/
@[expose] def experiment [DecidableEq M] [DecidableEq R] [DecidableEq E]
    {prob : Problem PP M R E n radix} (adv : Adversary prob) : ProbComp Bool := do
  let pp ← prob.paramGen
  let (collision, transcript) ← (simulateQ (oracles prob pp) (adv.find pp)).run []
  return valid prob.enc pp transcript collision

/-- The probability that the experiment returns `true`. -/
@[expose] noncomputable def advantage [DecidableEq M] [DecidableEq R] [DecidableEq E]
    {prob : Problem PP M R E n radix}
    (adv : Adversary prob) : ℝ≥0∞ := 𝒟[experiment adv] {true}

end IncomparableEncoding.TargetCollisionResistance
