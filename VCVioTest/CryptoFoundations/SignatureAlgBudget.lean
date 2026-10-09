/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.SignatureAlg.Tagged

/-!
# Signing budgets through the unforgeability experiment

A toy scheme over a one-point oracle spends one query on each signature and none on key
generation or verification. An adversary that asks for two signatures, and whose ambient oracle
is answered by a constant, runs a transcript experiment with at most two oracle queries.

When the ambient oracle is forwarded instead and verification also reads the oracle once, an
adversary with one ambient query and one signing query runs a transcript experiment with at most
three oracle queries: one for each query of its budget and one for verification.
-/

public section

open OracleComp OracleSpec

namespace VCVioTest.SignatureAlgBudget

/-- One oracle with a single query point. -/
abbrev bitSpec : OracleSpec Unit := Unit →ₒ Bool

/-- Signing reads the oracle once; key generation and verification make no query. -/
def coinSigAlg : SignatureAlg (OracleComp bitSpec) Bool Unit Unit Bool where
  keygen := pure ((), ())
  sign _ _ _ := bitSpec.query ()
  verify _ _ _ := pure true

/-- The adversary asks for two signatures and returns the second as a forgery. -/
def twoSignAdv : SignatureAlg.UnforgeableAdversary coinSigAlg where
  main _ := do
    let _ ← (bitSpec + (Bool →ₒ Bool)).query (.inr false)
    let σ ← (bitSpec + (Bool →ₒ Bool)).query (.inr true)
    return (true, σ)

/-- The signing queries of `twoSignAdv`. -/
def IsSignQuery : Unit ⊕ Bool → Prop := fun t => t.isRight

instance : DecidablePred IsSignQuery := fun t => inferInstanceAs (Decidable (t.isRight = true))

/-- The constant interpretation of the ambient oracle, which makes no query. -/
def constImpl : QueryImpl bitSpec (OracleComp bitSpec) := fun _ => pure false

/-- Two signing queries bound the oracle queries of the transcript experiment by two. -/
example : IsQueryBoundP (SignatureAlg.unforgeableTranscriptExperiment
    (twoSignAdv.mapOracles constImpl (sigAlg' := coinSigAlg))) (fun _ => True) 2 :=
  SignatureAlg.isQueryBoundP_unforgeableTranscriptExperiment_mapOracles_sign constImpl
    (p := IsSignQuery)
    (fun _ => by simp [twoSignAdv, IsSignQuery, isQueryBoundP_query_bind_iff])
    (fun _ => rfl)
    (fun _ => isQueryBoundP_pure _ _ _) (isQueryBoundP_pure _ _ _)
    (fun _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
    (fun _ _ _ => isQueryBoundP_pure _ _ _)

/-- Signing and verification each read the oracle once; key generation makes no query. -/
def readSigAlg : SignatureAlg (OracleComp bitSpec) Bool Unit Unit Bool where
  keygen := pure ((), ())
  sign _ _ _ := bitSpec.query ()
  verify _ _ _ := bitSpec.query ()

/-- The adversary reads the ambient oracle once, asks for one signature and returns it. -/
def mixedAdv : SignatureAlg.UnforgeableAdversary readSigAlg where
  main _ := do
    let _ ← (bitSpec + (Bool →ₒ Bool)).query (.inl ())
    let σ ← (bitSpec + (Bool →ₒ Bool)).query (.inr true)
    return (true, σ)

/-- The interpretation of the ambient oracle that forwards each query. -/
def fwdImpl : QueryImpl bitSpec (OracleComp bitSpec) := fun _ => bitSpec.query ()

/-- One charged ambient query, one charged signing query and one verification query bound the
oracle queries of the transcript experiment by three. -/
example : IsQueryBoundP (SignatureAlg.unforgeableTranscriptExperiment
    (mixedAdv.mapOracles fwdImpl (sigAlg' := readSigAlg))) (fun _ => True) (2 + 1) :=
  SignatureAlg.isQueryBoundP_unforgeableTranscriptExperiment_mapOracles_add fwdImpl
    (p := fun _ => True)
    (fun _ => by simp [mixedAdv, isQueryBoundP_query_bind_iff])
    (fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
    (fun _ h => (h trivial).elim) (isQueryBoundP_pure _ _ _)
    (fun _ _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
    (fun _ _ _ h => (h trivial).elim)
    (fun _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)

end VCVioTest.SignatureAlgBudget
