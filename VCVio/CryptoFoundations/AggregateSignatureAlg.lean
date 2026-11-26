/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.SignatureAlg
public import VCVio.CryptoFoundations.SignatureAlg.RomQueryCount

/-! # Aggregate signatures and chosen-key unforgeability

The aggregate-signature interface and chosen-key game of Boneh, Gentry, Lynn and Shacham,
*Aggregate and Verifiably Encrypted Signatures from Bilinear Maps* (EUROCRYPT 2003).
The adversary controls all keys except one honest key and may request signatures under
that key. A successful aggregate contains an unsigned message under the honest key.
-/

public section

universe u v

open OracleComp OracleSpec
open scoped ENNReal

/-- A signature scheme with signature aggregation and verification of key–message lists.
The aggregation input contains only signatures; validity conditions on the key–message
list belong to `aggregateVerify`. This is the BGLS aggregate-signature interface. -/
structure AggregateSignatureAlg (m : Type → Type v) [Monad m] (M PK SK S : Type)
    extends SignatureAlg m M PK SK S where
  /-- Combine a list of signatures into one signature. -/
  aggregate : List S → m S
  /-- Verify an aggregate against its claimed key–message pairs. -/
  aggregateVerify : List (PK × M) → S → m Bool

namespace AggregateSignatureAlg

variable {ι : Type u} {spec : OracleSpec ι} {M PK SK S : Type}

/-- A BGLS chosen-key adversary receives one honest public key, accesses the ambient
oracles and its signing oracle, and returns arbitrary key–message pairs and an aggregate. -/
structure UnforgeableAdversary
    (_sigAlg : AggregateSignatureAlg (OracleComp spec) M PK SK S) where
  /-- Produce the aggregate forgery after interacting with the ambient and signing oracles. -/
  main (pk : PK) : OracleComp (spec + (M →ₒ S)) (List (PK × M) × S)

/-- In the random-oracle model, the adversary makes, on every path and for every public key, at
most `qH` hash queries and at most `qS` signing queries, and every forgery it can output names at
most `N` key–message pairs. This is `SignatureAlg.UnforgeableAdversary.RomQueryBound` with a bound
on the forgery's length. -/
@[expose] def UnforgeableAdversary.RomQueryBound {ι : Type} {hs : OracleSpec ι}
    {sigAlg : AggregateSignatureAlg (OracleComp (unifSpec + hs)) M PK SK S}
    (adv : UnforgeableAdversary sigAlg) (qH qS N : ℕ) : Prop :=
  ∀ pk, IsQueryBoundP (adv.main pk) (SignatureAlg.IsHashQuery (hs := hs) (M := M) (S := S)) qH ∧
    IsQueryBoundP (adv.main pk) (SignatureAlg.IsSignQuery (hs := hs) (M := M) (S := S)) qS ∧
    ∀ z ∈ support (adv.main pk), z.1.length ≤ N

open scoped Classical in
/-- The BGLS chosen-key experiment. Acceptance requires a valid aggregate containing
at least one pair with the honest key and a message never submitted to its signing oracle.
Other public keys are chosen freely by the adversary. -/
@[expose] noncomputable def unforgeableExperiment
    {sigAlg : AggregateSignatureAlg (OracleComp spec) M PK SK S}
    (adv : UnforgeableAdversary sigAlg) : OracleComp spec Bool := do
  let (pk, sk) ← sigAlg.keygen
  let ((pairs, σ), log) ← sigAlg.toSignatureAlg.runWithSigningOracle pk sk (adv.main pk)
  let verified ← sigAlg.aggregateVerify pairs σ
  return pairs.any (fun p => decide (p.1 = pk) && !log.wasQueried p.2) && verified

/-- Success probability in the BGLS chosen-key game under the supplied runtime.
A random-oracle runtime shares its cache across signing and aggregate verification. -/
@[expose] noncomputable def unforgeableAdvantage
    {sigAlg : AggregateSignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : UnforgeableAdversary sigAlg) : ℝ≥0∞ :=
  runtime.evalDist (unforgeableExperiment adv) {true}

end AggregateSignatureAlg
