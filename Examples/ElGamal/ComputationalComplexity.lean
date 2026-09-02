/-
Copyright (c) 2026 Devon Tuma, Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Examples.ElGamal.ReductionCost
public import VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Syntactic computational complexity of the ElGamal reduction

This file gives the one-time ElGamal DDH reduction a fully syntactic oracle boundary. Its two
adversary procedures and its random challenge bit are three first-class queries in
`OracleComp (oneTimeINDCPASpec ... + coinSpec)`, so their use can be checked before choosing an
adversary implementation or probability semantics.

The reduction has an unconditional structural upper bound of three queries. When the adversary
state type is nonempty, three is also the exact total bound and each of `chooseMessages`, `coin`,
and `distinguish` is used exactly once. The nonemptiness condition is necessary only for the lower
bounds: if `State` is empty, the first query has no typed response and the later queries are
structurally unreachable.

Closing the two ports with a concrete adversary and the fair-coin handler definitionally recovers
`IND_CPA_OneTime_DDHReduction`. A future quantitative construction must provide its local group
and Boolean operations through the selected backend together with the backend's structural
product, sum, and option code; this file does not export a disconnected bundle of unused fields.
-/

@[expose] public section

open OracleSpec OracleComp

namespace elGamalAsymmEnc

/-! ## Oracle capabilities and primitive code -/

/-- The three external capabilities used by the syntactic one-time DDH reduction. -/
inductive OneTimeDDHOracleCapability
  | chooseMessages
  | coin
  | distinguish
  deriving DecidableEq, Repr

/-- Classify every position of the reduction's sum oracle by its external capability. -/
def oneTimeDDHOracleCapability {G State : Type} :
    (oneTimeINDCPASpec G G State (G × G) + coinSpec).Domain →
      OneTimeDDHOracleCapability
  | .inl (.chooseMessages _) => .chooseMessages
  | .inl (.distinguish _ _) => .distinguish
  | .inr _ => .coin

/-! ## Fully syntactic open reduction -/

section OpenReduction

variable {G : Type} [AddCommGroup G]

local instance : Inhabited G := ⟨0⟩

/-- The left-port query invoking the message-selection phase of a one-time adversary. -/
def oneTimeINDCPAChooseMessagesOracle {State : Type} (pk : G) :
    OracleComp (oneTimeINDCPASpec G G State (G × G) + coinSpec) (G × G × State) :=
  (oneTimeINDCPASpec G G State (G × G) + coinSpec).query
    (.inl (.chooseMessages pk))

/-- The right-port query sampling the challenge bit. -/
def oneTimeDDHCoinOracle {State : Type} :
    OracleComp (oneTimeINDCPASpec G G State (G × G) + coinSpec) Bool :=
  (oneTimeINDCPASpec G G State (G × G) + coinSpec).query (.inr ())

/-- The left-port query invoking the distinguishing phase of a one-time adversary. -/
def oneTimeINDCPADistinguishOracle {State : Type} (state : State) (c : G × G) :
    OracleComp (oneTimeINDCPASpec G G State (G × G) + coinSpec) Bool :=
  (oneTimeINDCPASpec G G State (G × G) + coinSpec).query
    (.inl (.distinguish state c))

/-- Fully syntactic open form of the one-time ElGamal DDH reduction.

The adversary procedures occupy the left summand of the oracle specification and the challenge
coin occupies the right summand. No query has been interpreted by a handler. -/
def IND_CPA_OneTime_DDHReduction_openOracle
    {State : Type} (_gen A B T : G) :
    OracleComp (oneTimeINDCPASpec G G State (G × G) + coinSpec) Bool :=
  oneTimeDDHReductionBody
    (oneTimeINDCPAChooseMessagesOracle (State := State) A)
    (oneTimeDDHCoinOracle (G := G) (State := State))
    oneTimeINDCPADistinguishOracle B T

/-! ## Exact structural query accounting -/

/-- The open reduction makes at most three queries on every typed response path. -/
theorem IND_CPA_OneTime_DDHReduction_openOracle_isTotalQueryBound
    {State : Type} (g A B T : G) :
    IsTotalQueryBound
      (IND_CPA_OneTime_DDHReduction_openOracle (State := State) g A B T) 3 := by
  change 0 < 3 ∧ ∀ _ : G × G × State,
    0 < 3 - 1 ∧ ∀ _ : Bool, 0 < (3 - 1) - 1 ∧ ∀ _ : Bool, True
  simp

/-- Three is the exact total structural query bound when the first query has a typed response. -/
theorem IND_CPA_OneTime_DDHReduction_openOracle_isTotalQueryBound_iff
    {State : Type} [Nonempty State] (g A B T : G) (n : ℕ) :
    IsTotalQueryBound
      (IND_CPA_OneTime_DDHReduction_openOracle (State := State) g A B T) n ↔
      3 ≤ n := by
  change (0 < n ∧ ∀ _ : G × G × State,
    0 < n - 1 ∧ ∀ _ : Bool, 0 < (n - 1) - 1 ∧ ∀ _ : Bool, True) ↔ 3 ≤ n
  simp only [forall_const, and_true]
  omega

/-- Each classified capability is used exactly once when all three query sites are reachable. -/
theorem IND_CPA_OneTime_DDHReduction_openOracle_isQueryBoundP_iff
    {State : Type} [Nonempty State] (g A B T : G)
    (capability : OneTimeDDHOracleCapability) (n : ℕ) :
    IsQueryBoundP
      (IND_CPA_OneTime_DDHReduction_openOracle (State := State) g A B T)
      (fun position ↦
        oneTimeDDHOracleCapability (G := G) (State := State) position = capability)
      n ↔ 1 ≤ n := by
  let choose : OneTimeDDHOracleCapability := .chooseMessages
  let random : OneTimeDDHOracleCapability := .coin
  let decide : OneTimeDDHOracleCapability := .distinguish
  cases capability
  · change ((¬(choose = choose) ∨ 0 < n) ∧
      ∀ _ : G × G × State, (¬(random = choose) ∨ 0 < n - 1) ∧
        ∀ _ : Bool, (¬(decide = choose) ∨ 0 < n - 1) ∧
          ∀ _ : Bool, True) ↔ 1 ≤ n
    simp
    omega
  · change ((¬(choose = random) ∨ 0 < n) ∧
      ∀ _ : G × G × State, (¬(random = random) ∨ 0 < n) ∧
        ∀ _ : Bool, (¬(decide = random) ∨ 0 < n - 1) ∧
          ∀ _ : Bool, True) ↔ 1 ≤ n
    simp
    omega
  · change ((¬(choose = decide) ∨ 0 < n) ∧
      ∀ _ : G × G × State, (¬(random = decide) ∨ 0 < n) ∧
        ∀ _ : Bool, (¬(decide = decide) ∨ 0 < n) ∧
          ∀ _ : Bool, True) ↔ 1 ≤ n
    simp
    omega

end OpenReduction

/-! ## Semantic closing -/

/-- Fair-coin implementation for the right port of the syntactic reduction. -/
def oneTimeDDHFairCoinImpl : QueryImpl coinSpec ProbComp
  | () => ($ᵗ Bool)

section Closing

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]

/-- Closing the open syntax with a concrete adversary and fair coin recovers the established
one-time ElGamal DDH reduction definitionally. -/
@[simp]
theorem IND_CPA_OneTime_DDHReduction_openOracle_eval
    {gen : G}
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen))
    (g A B T : G) :
    simulateQ
      (oneTimeINDCPAImpl (gen := gen) adv + oneTimeDDHFairCoinImpl)
      (IND_CPA_OneTime_DDHReduction_openOracle (State := adv.State) g A B T) =
      IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv g A B T := by
  rfl

end Closing

end elGamalAsymmEnc
