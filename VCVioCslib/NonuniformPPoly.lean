/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import VCVio.CryptoFoundations.Asymptotics.Security
public import VCVio.OracleComp.Coinductive.SecurityFamily
public import PolyFunCslib.Nontriviality

/-!
# Non-uniform P/poly oracle adversaries backed by cslib

This optional library is VCVio's thin crypto-facing facade over PolyFun's cslib-backed P/poly
certificate. The machine model, canonical bit encodings, resource accounting,
and structural closure API live in PolyFun. VCVio contributes only the oracle
specialization, a fair-coin boundary, and the connection to security games.

The name intentionally says `NonuniformPPT`/`PPoly`. It is distinct from
`IsOraclePPTBy`, VCVio's uniform, backend-relative, pathwise oracle-PPT notion.
-/

@[expose] public section

universe u

open OracleSpec ToCslib.Computability ENNReal

namespace OracleComp.Complexity

variable {index input output : ℕ → Type u}

/-- Canonical binary boundaries for an `OracleSpec` family, represented by the
generic PolyFun P/poly boundary of its underlying polynomial functors. -/
abbrev NonuniformBoundary (spec : (n : ℕ) → OracleSpec.{u, u} (index n))
    (input output : ℕ → Type u) :=
  PFunctor.CslibPPoly.Boundary (fun n ↦ (spec n).toPFunctor) input output

namespace NonuniformBoundary

variable {spec : (n : ℕ) → OracleSpec.{u, u} (index n)}

/-- Replace the canonical input representation. -/
abbrev withInput (boundary : NonuniformBoundary spec input output)
    {nextInput : ℕ → Type u} (encoding : BitEncFam nextInput) :=
  PFunctor.CslibPPoly.Boundary.withInput boundary encoding

/-- Replace the canonical returned-value representation. -/
abbrev withOutput (boundary : NonuniformBoundary spec input output)
    {nextOutput : ℕ → Type u} (encoding : BitEncFam nextOutput) :=
  PFunctor.CslibPPoly.Boundary.withOutput boundary encoding

end NonuniformBoundary

noncomputable def coinIndexEncoding :
    BitEncFam fun _ ↦ (coinSpec.toPFunctor).Idx where
  wid _ := 1
  widBound := .C 1
  wid_le _ := by simp
  enc _ index := [index.2]
  len_eq _ _ := rfl
  enc_injective _ left right equality := by
    rcases left with ⟨⟨⟩, leftBit⟩
    rcases right with ⟨⟨⟩, rightBit⟩
    congr
    simpa using equality

/-- The standard fair-coin P/poly boundary: the sole query position has width
zero and a tagged Boolean answer has width one. -/
noncomputable def NonuniformBoundary.coin
    {coinInput coinOutput : ℕ → Type}
    (inputEncoding : BitEncFam coinInput) (outputEncoding : BitEncFam coinOutput) :
    NonuniformBoundary (fun _ ↦ coinSpec) coinInput coinOutput where
  input := inputEncoding
  output := outputEncoding
  position := BitEncFam.const Unit
  index := coinIndexEncoding

variable {spec : (n : ℕ) → OracleSpec.{u, u} (index n)}
  [∀ n, DecidableEq (index n)]
  {boundary : NonuniformBoundary spec input output}
  {program : (n : ℕ) → input n → OracleComp (spec n) (output n)}

/-- The proof-relevant non-uniform P/poly witness for an oracle-program family. -/
abbrev NonuniformPPTWitness
    (boundary : NonuniformBoundary spec input output)
    (program : (n : ℕ) → input n → OracleComp (spec n) (output n)) :=
  PFunctor.CslibPPoly.Witness boundary fun n value ↦ (program n value).toFreeM

/-- An oracle-program family has non-uniform polynomial-size machine
certificates at the pinned canonical boundary. -/
def IsNonuniformPPTBy
    (boundary : NonuniformBoundary spec input output)
    (program : (n : ℕ) → input n → OracleComp (spec n) (output n)) : Prop :=
  PFunctor.CslibPPoly.IsPPolyBy boundary fun n value ↦ (program n value).toFreeM

/-- Explicit synonym exposing the underlying complexity class name. -/
abbrev IsOraclePPolyBy := @IsNonuniformPPTBy

namespace NonuniformPPTWitness

/-- Every certified oracle computation has the witness's polynomial total query bound. -/
theorem queryBound (witness : NonuniformPPTWitness boundary program)
    (n : ℕ) (value : input n) :
    OracleComp.IsTotalQueryBound (program n value)
      (witness.realization.rounds.eval n) :=
  witness.isTotalRollBound n value

end NonuniformPPTWitness

namespace IsNonuniformPPTBy

/-- Transport a non-uniform certificate along pointwise equality. -/
theorem congr {program' : (n : ℕ) → input n → OracleComp (spec n) (output n)}
    (equality : ∀ n value, program n value = program' n value)
    (certificate : IsNonuniformPPTBy boundary program) :
    IsNonuniformPPTBy boundary program' :=
  PFunctor.CslibPPoly.IsPPolyBy.congr
    (fun n value ↦ congrArg OracleComp.toFreeM (equality n value)) certificate

end IsNonuniformPPTBy

/-! ## Non-triviality -/

/-- The oracle specification whose underlying polynomial functor is PolyFun's
canonical one-position Boolean-answer counting interface. Keeping this bridge in
VCVio lets the backend theorem be stated for actual `OracleComp` programs without
duplicating its machine-counting proof. -/
abbrev countingCoinSpec (_n : ℕ) : OracleSpec PUnit :=
  OracleSpec.ofPFunctor PFunctor.CslibPPoly.Coin

/-- The pinned counting boundary, viewed as a VCVio oracle boundary. -/
noncomputable abbrev NonuniformBoundary.countingCoin :
    NonuniformBoundary countingCoinSpec (fun n ↦ BitVec n) (fun _ ↦ Bool) :=
  PFunctor.CslibPPoly.coinBoundary

/-- The VCVio non-uniform class is non-trivial: some Boolean predicate family
cannot be implemented, even by pure oracle programs, at the pinned counting
boundary. -/
theorem exists_not_isNonuniformPPTBy_pure :
    ∃ function : (n : ℕ) → BitVec n → Bool,
      ¬ IsNonuniformPPTBy NonuniformBoundary.countingCoin
        (fun n value ↦ pure (function n value)) := by
  simpa [IsNonuniformPPTBy, NonuniformBoundary.countingCoin, countingCoinSpec] using
    PFunctor.CslibPPoly.exists_not_isPPolyBy_pure

end OracleComp.Complexity

namespace SecurityGame

open OracleComp.Complexity

variable {index input output : ℕ → Type} [∀ n, DecidableEq (index n)]

/-- Security against non-uniform cslib-backed P/poly oracle adversaries at a
pinned canonical boundary. -/
abbrev secureAgainstNonuniformPPT
    {spec : (n : ℕ) → OracleSpec (index n)}
    (boundary : NonuniformBoundary spec input output)
    (game : SecurityGame ((n : ℕ) → input n → OracleComp (spec n) (output n))) : Prop :=
  game.secureAgainst (IsNonuniformPPTBy boundary)

/-- A negligible per-query loss remains negligible against every certified
non-uniform adversary because its total query count is polynomially bounded. -/
theorem secureAgainstNonuniformPPT_of_advantage_le_mul_totalQueries
    {spec : (n : ℕ) → OracleSpec (index n)}
    (boundary : NonuniformBoundary spec input output)
    (game : SecurityGame ((n : ℕ) → input n → OracleComp (spec n) (output n)))
    {error : ℕ → ℝ≥0∞} (errorNegligible : negligible error)
    (advantageBound :
      ∀ (adversary : (n : ℕ) → input n → OracleComp (spec n) (output n))
        (queries : ℕ → ℕ),
        (∀ n value, OracleComp.IsTotalQueryBound (adversary n value) (queries n)) →
        ∀ n, game.advantage adversary n ≤ (queries n : ℝ≥0∞) * error n) :
    game.secureAgainstNonuniformPPT boundary := by
  rintro adversary ⟨witness⟩
  exact negligible_of_le
    (advantageBound adversary
      (fun n ↦ witness.realization.rounds.eval n)
      (NonuniformPPTWitness.queryBound witness))
    (negligible_polynomial_mul errorNegligible witness.realization.rounds)

end SecurityGame
