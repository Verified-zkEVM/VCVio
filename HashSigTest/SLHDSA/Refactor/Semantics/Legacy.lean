/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.RomQueryCount

/-!
# Signature experiment and structural budget equations

The equations retain the exact returned-pair log, the final verification call and the
per-public-key structural bounds on the adversary's own query program.
-/

public section

open OracleSpec OracleComp

namespace SLHDSA.Refactor.Semantics

universe u v

/-- The signing interface records the exact reply returned by the scheme. -/
theorem signingOracleEquation {m : Type → Type v} [Monad m] {M PK SK S : Type}
    (algorithm : SignatureAlg m M PK SK S) (pk : PK) (sk : SK) :
    algorithm.signingOracle pk sk = QueryImpl.withLogging (algorithm.sign pk sk) := rfl

/-- Ambient and signing calls share one interpreter and one chronological writer log. -/
theorem signingRunEquation {ι : Type u} {spec : OracleSpec ι} {M PK SK S α : Type}
    (algorithm : SignatureAlg (OracleComp spec) M PK SK S) (pk : PK) (sk : SK)
    (program : OracleComp (spec + (M →ₒ S)) α) :
    algorithm.runWithSigningOracle pk sk program =
      (simulateQ (spec.passthrough + algorithm.signingOracle pk sk) program).run := rfl

/-- Strong freshness compares the returned message and signature together. -/
theorem returnedPairEquation {M S : Type} [DecidableEq M] [DecidableEq S]
    (signed : QueryLog (M →ₒ S)) (message : M) (signature : S) :
    SignatureAlg.signingLogContains signed message signature =
      decide (⟨message, signature⟩ ∈ signed) := rfl

open scoped Classical in
/-- Verification is performed after the adversary even if its candidate is not fresh. -/
theorem strongExperimentEquation {ι : Type u} {spec : OracleSpec ι} {M PK SK S : Type}
    (algorithm : SignatureAlg (OracleComp spec) M PK SK S)
    (adversary : SignatureAlg.StrongUnforgeableAdversary algorithm) :
    SignatureAlg.strongUnforgeableExperiment adversary = (do
      let (pk, sk) ← algorithm.keygen
      let ((message, signature), signed) ←
        algorithm.runWithSigningOracle pk sk (adversary.main pk)
      let verified ← algorithm.verify pk message signature
      return !decide (⟨message, signature⟩ ∈ signed) && verified) := rfl

/-- Structural hash and signing bounds quantify every public key and every query path. -/
theorem structuralBudgetEquation {ι : Type} {hs : OracleSpec ι} {M PK SK S : Type}
    (algorithm : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S)
    (adversary : SignatureAlg.StrongUnforgeableAdversary algorithm) (qh qs : Nat) :
    adversary.RomQueryBound qh qs ↔
      ∀ pk, IsQueryBoundP (adversary.main pk)
          (SignatureAlg.IsHashQuery (hs := hs) (M := M) (S := S)) qh ∧
        IsQueryBoundP (adversary.main pk)
          (SignatureAlg.IsSignQuery (hs := hs) (M := M) (S := S)) qs := Iff.rfl

/-- The structural hash observer excludes private sampling and signing calls. -/
theorem structuralHashSelectorEquation {ι : Type} {hs : OracleSpec ι} {M S : Type}
    (input : ((unifSpec + hs) + (M →ₒ S)).Domain) :
    SignatureAlg.IsHashQuery input ↔ match input with
      | .inl (.inr _) => True
      | _ => False := Iff.rfl

/-- The structural signing observer counts exactly the signing summand. -/
theorem structuralSigningSelectorEquation {ι : Type} {hs : OracleSpec ι} {M S : Type}
    (input : ((unifSpec + hs) + (M →ₒ S)).Domain) :
    SignatureAlg.IsSignQuery input ↔ match input with
      | .inr _ => True
      | _ => False := Iff.rfl

end SLHDSA.Refactor.Semantics
