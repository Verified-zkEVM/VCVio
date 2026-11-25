/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.BLS.Generic.Adversary
public import VCVio.CryptoFoundations.GroupModel.PairingMetadata
public import VCVio.CryptoFoundations.GroupModel.Certificate
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.LazyExecution
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-! # Generic programs for the two BLS extraction branches

The reduction keeps its outer handles private. The adversary sees a virtual table containing
only its initial inputs and subsequent receipts. An independent zero-valued tracker retains
chronological coefficients; equality replies always come from the outer group oracle.

A single private scalar oracle is shared by hashing, signing, transcript replay, and the final
target lookup. Closing that oracle with a lazy random oracle produces a generic pairing program.
-/

public section

open OracleComp OracleSpec GroupModel GroupModel.Interaction

namespace BLS.Generic

variable {F M R : Type}

attribute [local implicit_reducible] spec handleSpec

/-- Pairing operations and coins together with the reduction's private scalar lookup oracle. -/
abbrev reductionSpec (F M R : Type) := spec F pairingSig + (unifSpec + (M →ₒ R))

/-- Embed a generic pairing computation into the interface with private scalar lookups. -/
@[expose] def reductionLift : QueryImpl (genSpec F pairingSig)
    (OracleComp (reductionSpec F M R))
  | .inl q => (reductionSpec F M R).query (.inl q)
  | .inr n => (reductionSpec F M R).query (.inr (.inl n))

/-- Private virtual handles, chronological coefficient metadata, and reply labels. -/
structure ReductionState (F M : Type) where
  /-- The adversary's local handles translated to the reduction's outer handles. -/
  handles : Tbl (fun _ : PSort => Handle)
  /-- A value-independent source tracker and target table. -/
  metadata : Pairing.Tracked F (fun _ : Bool => F) F
  /-- Each hash or signing reply contributes one chronological occurrence. -/
  transcript : LinearFunctional.Transcript M

/-- Initial source bases contain the generator and public key, even if their values coincide. -/
@[expose] def initialReductionState [Zero F] [One F] (pk₁ pk₂ : Handle) : ReductionState F M :=
  ⟨(fun | .g₁ => [0, pk₁] | .g₂ => [0, pk₂] | .gₜ => []),
    ((fun _ => [0, 1], trackInputs (fun _ : Bool => [(0 : F), 0])), []), []⟩

/-- The adversary's initial local handles are independent of the reduction's allocations. -/
@[expose] def reductionInput : Message Unit (fun _ : PSort => Handle) :=
  ⟨(), fun | .g₁ => [0, 1] | .g₂ => [0, 1] | .gₜ => []⟩

/-- Install one externally computed first-source point as a fresh adversarial receipt. -/
@[expose] def reductionReceive [Zero F] [One F]
    (st : ReductionState F M) (kind : Bool) (m : M) (h : Handle) : ReductionState F M :=
  ⟨append st.handles .g₁ h,
    (receive st.metadata.1 (fun | false => [0] | true => []), st.metadata.2),
    st.transcript ++ [(kind, m)]⟩

/-- Interpret the adversary using virtual handles, real equality, and private scalar lookups. -/
@[expose] def reductionHandler [CommSemiring F] [DecidableEq F]
    (z : PSort → Handle) (hash sign : R → OracleComp (genSpec F pairingSig) Handle) :
    QueryImpl (adversarySpec F M)
      (StateT (ReductionState F M) (OracleComp (reductionSpec F M R)))
  | .inl q => fun st => do
      let (a, handles) ← simulateQ reductionLift ((virtualizeImpl z (.inl q)).run st.handles)
      return (a, ⟨handles, (Pairing.step (0 : F →ₗ[F] F →ₗ[F] F) q st.metadata).2,
        st.transcript⟩)
  | .inr (.inl _) => fun st => pure ((), st)
  | .inr (.inr (.inl n)) => fun st => do
      let a ← (reductionSpec F M R).query (.inr (.inl n))
      return (a, st)
  | .inr (.inr (.inr q)) => fun st => do
      let (kind, m) := match q.data with | .inl m => (false, m) | .inr m => (true, m)
      let r ← (reductionSpec F M R).query (.inr (.inr m))
      let h ← simulateQ reductionLift (if kind then sign r else hash r)
      return (⟨(), fun | .g₁ => [(st.handles .g₁).length] | .g₂ => [] | .gₜ => []⟩,
        reductionReceive st kind m h)

/-- Replay the shared private scalar oracle to recover the chronological extraction basis. -/
@[expose] def reductionExtract [CommSemiring F] [DecidableEq F]
    (A : Adversary F M) (z : PSort → Handle) (pk₁ pk₂ : Handle)
    (hash sign : R → OracleComp (genSpec F pairingSig) Handle)
    (hashRep signRep : R → F × F) (initial : List (F × F)) :
    OracleComp (reductionSpec F M R) (F × F × R) := do
  let (out, st) ← (simulateQ (reductionHandler z hash sign) (A reductionInput)).run
    (initialReductionState pk₁ pk₂)
  let coefficients :=
    ((explain st.metadata.1 (Pairing.sourceMessage out)).coefficients false).headD []
  let basis ← simulateQ (fun q => ((reductionSpec F M R).query (.inr q) :
      OracleComp (reductionSpec F M R) _))
    (LinearFunctional.readTranscript hashRep signRep st.transcript)
  let target ← (reductionSpec F M R).query (.inr (.inr out.data))
  let repr := evaluate coefficients (initial ++ basis)
  return (repr.1, repr.2, target)

/-- Answer scalar lookups with one cache while forwarding group queries and private coins. -/
@[expose] def reductionCache [DecidableEq M] [SampleableType R] :
    QueryImpl (reductionSpec F M R)
      (StateT (M →ₒ R).QueryCache (OracleComp (genSpec F pairingSig)))
  | .inl q => fun cache => (fun h => (h, cache)) <$> (genSpec F pairingSig).query (.inl q)
  | .inr (.inl n) => fun cache => (fun r => (r, cache)) <$> (genSpec F pairingSig).query (.inr n)
  | .inr (.inr m) => fun cache => liftM (((M →ₒ R).randomOracle m).run cache)

/-- Close the shared scalar oracle, leaving only generic pairing operations and coins. -/
@[expose] def closeReduction [DecidableEq M] [SampleableType R] {α : Type}
    (program : OracleComp (reductionSpec F M R) α) : OracleComp (genSpec F pairingSig) α :=
  (simulateQ reductionCache program).run' ∅

/-- Allocate one persistent zero handle per sort for invalid local handle lookups. -/
@[expose] def reductionZeros [Zero F] : OracleComp (genSpec F pairingSig) (PSort → Handle) := do
  let z₁ ← (genSpec F pairingSig).query (.inl (.smul .g₁ 0 0))
  let z₂ ← (genSpec F pairingSig).query (.inl (.smul .g₂ 0 0))
  let zₜ ← (genSpec F pairingSig).query (.inl (.smul .gₜ 0 0))
  return fun | .g₁ => z₁ | .g₂ => z₂ | .gₜ => zₜ

/-- The good-branch generic program hashes into the generator and signs into the challenge. -/
@[expose] def goodProgram [Field F] [DecidableEq F] [SampleableType F] [DecidableEq M]
    (A : Adversary F M) : OracleComp (genSpec F pairingSig) F :=
  closeReduction (M := M) (R := F) do
    let z ← simulateQ reductionLift reductionZeros
    let (a, b, target) ← reductionExtract A z 1 1
      (fun r => (genSpec F pairingSig).query (.inl (.smul .g₁ r 0)))
      (fun r => (genSpec F pairingSig).query (.inl (.smul .g₁ r 1)))
      (fun r => (r, 0)) (fun r => (0, r)) [(1, 0), (0, 1)]
    return a / (target - b)

/-- Compute a masked challenge point using two scalar multiplications and one addition. -/
@[expose] def maskedPoint (r : F × F) : OracleComp (genSpec F pairingSig) Handle := do
  let x ← (genSpec F pairingSig).query (.inl (.smul .g₁ r.1 1))
  let y ← (genSpec F pairingSig).query (.inl (.smul .g₁ r.2 0))
  (genSpec F pairingSig).query (.inl (.add .g₁ x y))

/-- The bad-branch generic program samples a signing key and uses paired scalar masks. -/
@[expose] def badProgram [Field F] [DecidableEq F] [SampleableType F] [DecidableEq M]
    (A : Adversary F M) : OracleComp (genSpec F pairingSig) F :=
  closeReduction (M := M) (R := F × F) do
    let κ ← liftM ($ᵗ F)
    let z ← simulateQ reductionLift reductionZeros
    let pk₁ ← (reductionSpec F M (F × F)).query (.inl (.smul .g₁ κ 0))
    let pk₂ ← (reductionSpec F M (F × F)).query (.inl (.smul .g₂ κ 0))
    let (a, b, target) ← reductionExtract A z pk₁ pk₂ maskedPoint
      (fun r => do
        let h ← maskedPoint r
        (genSpec F pairingSig).query (.inl (.smul .g₁ κ h)))
      (fun _ => (0, 0)) id [(0, 0), (0, 1)]
    return (b - target.2) / (target.1 - a)

end BLS.Generic
