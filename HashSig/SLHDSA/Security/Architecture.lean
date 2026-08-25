/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Security.Transcript
public import VCVio.CryptoFoundations.PRF

/-!
# Repaired SLH-DSA Master Security Architecture

This file encodes the shape of the repaired classical reduction without claiming its proof.  The
twelve summands and coefficients follow the exported theorem in `proofs/SPHINCS_PLUS.ec` lines
4338--4370.  Every target-bearing term is a standalone, two-phase oracle game: its reduction
chooses targets through the game oracle and retains private state between `pick` and `finish`.

The statement has no birthday/interleaving slack and no additive `qS`/`qH` term.  Query budgets
are structural hypotheses on the original EUF-CMA adversary program.  All experiments use VCVio's
classical `OracleComp` semantics; no QROM theorem is exposed.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.Security

/-! ## Closed role vocabularies -/

inductive PrimitiveRole where
  | prf | prfMsg | f | h | tl | hmsg
deriving Repr, DecidableEq, Fintype

inductive MasterTermRole where
  | skgPrf
  | mkgPrfMsg
  | hmsgItsr
  | forsFDspr
  | forsFTcr
  | forsHTcrC
  | forsTlTcrC
  | wotsFUdC
  | wotsFTcrC
  | wotsFPreC
  | wotsTlTcrC
  | xmssHTcrC
deriving Repr, DecidableEq, Fintype

inductive TargetRole where
  | forsF
  | forsH
  | forsTl
  | wotsFUd
  | wotsFTcr
  | wotsFPre
  | wotsTl
  | xmssH
deriving Repr, DecidableEq, Fintype

@[simp] theorem primitiveRole_card : Fintype.card PrimitiveRole = 6 := by decide
@[simp] theorem masterTermRole_card : Fintype.card MasterTermRole = 12 := by decide
@[simp] theorem targetRole_card : Fintype.card TargetRole = 8 := by decide

def TargetRole.constructionRole : TargetRole → ConstructionRole
  | .forsF => .forsF
  | .forsH => .forsH
  | .forsTl => .forsTl
  | .wotsFUd => .wotsFUd
  | .wotsFTcr => .wotsFTcr
  | .wotsFPre => .wotsFPre
  | .wotsTl => .wotsTl
  | .xmssH => .xmssH

/-! ## Exact positive target bounds -/

def treesAtLayer (p : Params) (i : Fin p.d) : ℕ :=
  2 ^ (p.hp * (p.d - i.val - 1))

def xmssTreeCount (p : Params) : ℕ :=
  ∑ i : Fin p.d, treesAtLayer p i

def wotsInstanceCount (p : Params) : ℕ :=
  ∑ i : Fin p.d, treesAtLayer p i * 2 ^ p.hp

/-- Formula-derived upper bound for the number of targets issued in each named game.  The
EasyCrypt FORS-instance variable called `d` instantiates to `2^h`, not `Params.d`. -/
def targetCount (p : Params) : TargetRole → ℕ
  | .forsF => 2 ^ p.h * p.k * 2 ^ p.a
  | .forsH => 2 ^ p.h * p.k * (2 ^ p.a - 1)
  | .forsTl => 2 ^ p.h
  | .wotsFUd => wotsInstanceCount p * p.len
  | .wotsFTcr => wotsInstanceCount p * p.len * p.w
  | .wotsFPre => wotsInstanceCount p * p.len
  | .wotsTl => wotsInstanceCount p
  | .xmssH => xmssTreeCount p * (2 ^ p.hp - 1)

theorem xmssTreeCount_pos (p : Params) (conditions : ParameterConditions p) :
    0 < xmssTreeCount p := by
  unfold xmssTreeCount
  apply Finset.sum_pos'
  · intro i _
    exact Nat.zero_le _
  · let i : Fin p.d := ⟨0, conditions.d_pos⟩
    exact ⟨i, Finset.mem_univ i, Nat.two_pow_pos _⟩

theorem wotsInstanceCount_pos (p : Params) (conditions : ParameterConditions p) :
    0 < wotsInstanceCount p := by
  unfold wotsInstanceCount
  apply Finset.sum_pos'
  · intro i _
    exact Nat.zero_le _
  · let i : Fin p.d := ⟨0, conditions.d_pos⟩
    exact ⟨i, Finset.mem_univ i,
      Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)⟩

theorem targetCount_pos (p : Params) (conditions : ParameterConditions p)
    (role : TargetRole) : 0 < targetCount p role := by
  have ha : 0 < 2 ^ p.a - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt conditions.a_pos))
  have hhp : 0 < 2 ^ p.hp - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt conditions.hp_pos))
  cases role with
  | forsF =>
      exact Nat.mul_pos
        (Nat.mul_pos (Nat.two_pow_pos _) conditions.k_pos) (Nat.two_pow_pos _)
  | forsH =>
      exact Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) conditions.k_pos) ha
  | forsTl => exact Nat.two_pow_pos _
  | wotsFUd =>
      exact Nat.mul_pos (wotsInstanceCount_pos p conditions) conditions.len_pos
  | wotsFTcr =>
      exact Nat.mul_pos
        (Nat.mul_pos (wotsInstanceCount_pos p conditions) conditions.len_pos)
        (Nat.two_pow_pos _)
  | wotsFPre =>
      exact Nat.mul_pos (wotsInstanceCount_pos p conditions) conditions.len_pos
  | wotsTl => exact wotsInstanceCount_pos p conditions
  | xmssH => exact Nat.mul_pos (xmssTreeCount_pos p conditions) hhp

def positiveTargetCount (p : Params) (conditions : ParameterConditions p)
    (role : TargetRole) : PositiveTargetCount :=
  ⟨targetCount p role, targetCount_pos p conditions role⟩

@[simp]
theorem positiveTargetCount_value (p : Params) (conditions : ParameterConditions p)
    (role : TargetRole) :
    (positiveTargetCount p conditions role).value = targetCount p role := rfl

theorem exactTargetIndex_nonempty (p : Params) (conditions : ParameterConditions p)
    (role : TargetRole) : Nonempty (Fin (positiveTargetCount p conditions role).value) :=
  ⟨⟨0, (positiveTargetCount p conditions role).positive⟩⟩

theorem rejectedInterleavingLoss_exceeds_one : 256 < 17 * (17 + 0) := by decide

/-! ## Target and collection oracle languages -/

def TargetInput {p : Params} (prims : Primitives p) : TargetRole → Type
  | .forsF | .wotsFUd | .wotsFTcr | .wotsFPre => prims.Y
  | .forsH | .xmssH => prims.Y × prims.Y
  | .forsTl => Vector prims.Y p.k
  | .wotsTl => Vector prims.Y p.len

/-- Evaluate a named member of the tweakable-hash collection under one sampled public seed. -/
def targetEval {p : Params} (prims : Primitives p) (publicSeed : prims.PkSeed) :
    ∀ role, Adrs → TargetInput prims role → prims.Y
  | .forsF, address, input => prims.F publicSeed address input
  | .forsH, address, input => prims.H publicSeed address input.1 input.2
  | .forsTl, address, input => prims.Tl publicSeed address input.toList
  | .wotsFUd, address, input => prims.F publicSeed address input
  | .wotsFTcr, address, input => prims.F publicSeed address input
  | .wotsFPre, address, input => prims.F publicSeed address input
  | .wotsTl, address, input => prims.Tl publicSeed address input.toList
  | .xmssH, address, input => prims.H publicSeed address input.1 input.2

@[reducible] def chosenTargetSpec {p : Params} (prims : Primitives p) (role : TargetRole) :
    OracleSpec (Adrs × TargetInput prims role) :=
  OracleSpec.ofFn fun _ => prims.Y

@[reducible] def sampledTargetSpec {p : Params} (prims : Primitives p) : OracleSpec Adrs :=
  OracleSpec.ofFn fun _ => prims.Y

inductive CollectionQuery {p : Params} (prims : Primitives p) where
  | f (address : Adrs) (input : prims.Y)
  | h (address : Adrs) (left right : prims.Y)
  | tlFors (address : Adrs) (inputs : Vector prims.Y p.k)
  | tlWots (address : Adrs) (inputs : Vector prims.Y p.len)

@[reducible] def collectionSpec {p : Params} (prims : Primitives p) :
    OracleSpec (CollectionQuery prims) :=
  OracleSpec.ofFn fun _ => prims.Y

def chosenTargetImpl {p : Params} (prims : Primitives p) (publicSeed : prims.PkSeed)
    (role : TargetRole) : QueryImpl (chosenTargetSpec prims role) ProbComp
  | (address, input) => pure (targetEval prims publicSeed role address input)

/-- The real PRE/UD oracle samples a fresh input on every call and returns only its hash output. -/
def sampledTargetRealImpl {p : Params} (prims : Primitives p)
    [SampleableType prims.Y] (publicSeed : prims.PkSeed) :
    QueryImpl (sampledTargetSpec prims) ProbComp
  | address => do
      let input ← $ᵗ prims.Y
      return prims.F publicSeed address input

def sampledTargetIdealImpl {p : Params} (prims : Primitives p)
    [SampleableType prims.Y] : QueryImpl (sampledTargetSpec prims) ProbComp
  | _ => $ᵗ prims.Y

def collectionImpl {p : Params} (prims : Primitives p) (publicSeed : prims.PkSeed) :
    QueryImpl (collectionSpec prims) ProbComp
  | .f address input => pure (prims.F publicSeed address input)
  | .h address left right => pure (prims.H publicSeed address left right)
  | .tlFors address inputs => pure (prims.Tl publicSeed address inputs.toList)
  | .tlWots address inputs => pure (prims.Tl publicSeed address inputs.toList)

def sumQueryImpl {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (left : QueryImpl spec₁ ProbComp) (right : QueryImpl spec₂ ProbComp) :
    QueryImpl (spec₁ + spec₂) ProbComp
  | .inl query => left query
  | .inr query => right query

/-! ## Two-phase reduction programs -/

structure TwoPhaseAdversary {ι : Type} (spec : OracleSpec ι) (Public Answer : Type) where
  State : Type
  pick : OracleComp spec State
  finish : Public → State → ProbComp Answer

def runTwoPhase {ι : Type} {spec : OracleSpec ι} {Public Answer : Type}
    (impl : QueryImpl spec ProbComp) (program : TwoPhaseAdversary spec Public Answer)
    (publicParameter : Public) : ProbComp (Answer × QueryLog spec) := do
  let picked ← (simulateQ impl.withLogging program.pick).run
  let answer ← program.finish publicParameter picked.1
  return (answer, picked.2)

/-! ## Challenger-owned trace projections and validity -/

def chosenTargets {p : Params} {prims : Primitives p} {role : TargetRole} :
    QueryLog (chosenTargetSpec prims role) →
      List (TweakableTarget Adrs (TargetInput prims role)) :=
  List.map fun entry => match entry with
    | ⟨(address, input), _⟩ => ⟨address, input⟩

def chosenTargetsC {p : Params} {prims : Primitives p} {role : TargetRole} :
    QueryLog (chosenTargetSpec prims role + collectionSpec prims) →
      List (TweakableTarget Adrs (TargetInput prims role)) :=
  List.filterMap fun entry => match entry with
    | ⟨.inl (address, input), _⟩ => some ⟨address, input⟩
    | _ => none

def sampledTargets {p : Params} {prims : Primitives p} :
    QueryLog (sampledTargetSpec prims + collectionSpec prims) → List (Adrs × prims.Y) :=
  List.filterMap fun entry => match entry with
    | ⟨.inl address, output⟩ => some (address, output)
    | _ => none

def collectionTweaks {p : Params} {prims : Primitives p} {ι : Type}
    {leftSpec : OracleSpec ι} :
    QueryLog (leftSpec + collectionSpec prims) → List Adrs :=
  List.filterMap fun entry => match entry with
    | ⟨.inr (.f address _), _⟩ => some address
    | ⟨.inr (.h address _ _), _⟩ => some address
    | ⟨.inr (.tlFors address _), _⟩ => some address
    | ⟨.inr (.tlWots address _), _⟩ => some address
    | _ => none

def TargetTraceValid {p : Params} {Input : Type} (role : TargetRole)
    (targets : List (TweakableTarget Adrs Input)) : Prop :=
  targets.length ≤ targetCount p role ∧ (targets.map TweakableTarget.tweak).Nodup

def SampledTraceValid {p : Params} {Output : Type} (role : TargetRole)
    (targets : List (Adrs × Output)) : Prop :=
  targets.length ≤ targetCount p role ∧ (targets.map Prod.fst).Nodup

def CollectionDisjoint (targetTweaks collection : List Adrs) : Prop :=
  ∀ tweak ∈ targetTweaks, tweak ∉ collection

def TCRSuccess {p : Params} (prims : Primitives p) (publicSeed : prims.PkSeed)
    (role : TargetRole) (targets : List (TweakableTarget Adrs (TargetInput prims role)))
    (selected : ℕ) (replacement : TargetInput prims role) : Prop :=
  ∃ target, targets[selected]? = some target ∧ replacement ≠ target.input ∧
    targetEval prims publicSeed role target.tweak replacement =
      targetEval prims publicSeed role target.tweak target.input

def DSPRSuccess {p : Params} (prims : Primitives p) (publicSeed : prims.PkSeed)
    (targets : List (TweakableTarget Adrs prims.Y)) (selected : ℕ) (guess : Bool) : Prop :=
  ∃ target, targets[selected]? = some target ∧
    (guess = true ↔ HasSecondPreimage (targetEval prims publicSeed .forsF) target)

def SPprobSuccess {p : Params} (prims : Primitives p) (publicSeed : prims.PkSeed)
    (targets : List (TweakableTarget Adrs prims.Y)) (selected : ℕ) : Prop :=
  ∃ target, targets[selected]? = some target ∧
    HasSecondPreimage (targetEval prims publicSeed .forsF) target

def PRESuccess {p : Params} (prims : Primitives p) (publicSeed : prims.PkSeed)
    (targets : List (Adrs × prims.Y)) (selected : ℕ) (candidate : prims.Y) : Prop :=
  ∃ target, targets[selected]? = some target ∧
    prims.F publicSeed target.1 candidate = target.2

/-! ## Concrete standalone component experiments -/

def skgPrfScheme {p : Params} (prims : Primitives p) [SampleableType prims.SkSeed] :
    PRFScheme prims.SkSeed (prims.PkSeed × Adrs) prims.Y where
  keygen := $ᵗ prims.SkSeed
  eval := fun key input => prims.PRF input.1 key input.2

def mkgPrfMsgScheme {p : Params} (prims : Primitives p) [SampleableType prims.SkPrf] :
    PRFScheme prims.SkPrf (prims.Y × List Byte) prims.Y where
  keygen := $ᵗ prims.SkPrf
  eval := fun key input => prims.PRFmsg key input.1 input.2

/-- Post-SKG/post-MKG ITSR reduction.  Its setup distribution owns the NPRF/hybrid key material;
the generic ITSR challenger supplies only the fresh message-randomizer oracle. -/
structure PostHopITSRAdversary {p : Params} (prims : Primitives p) where
  State : Type
  setup : ProbComp State
  publicKey : State → PublicKey prims
  find : State → OracleComp (MessageInput →ₒ prims.Y) (ITSRInput prims)

def itsrDefaultImpl {p : Params} (prims : Primitives p) [SampleableType prims.Y] :
    QueryImpl (MessageInput →ₒ prims.Y) ProbComp
  | _ => $ᵗ prims.Y

def itsrOracleHistory {p : Params} {prims : Primitives p} (pk : PublicKey prims)
    (encode : MessageInput → List Byte) :
    QueryLog (MessageInput →ₒ prims.Y) → List (ITSRRecord prims) :=
  List.map fun entry => match entry with
    | ⟨request, randomizer⟩ => {
        input := ⟨randomizer, request⟩
        digest := prims.Hmsg randomizer pk.pkSeed pk.pkRoot (encode request)
      }

def itsrChallengeForgery {p : Params} {prims : Primitives p} (pk : PublicKey prims)
    (encode : MessageInput → List Byte) (input : ITSRInput prims) : ITSRRecord prims :=
  {
    input := input
    digest := prims.Hmsg input.randomizer pk.pkSeed pk.pkRoot (encode input.request)
  }

structure ReductionSystem {p : Params} (prims : Primitives p) (scheme : SchemeInterface prims)
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y]
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    (conditions : ParameterConditions p) where
  skgPrf : ClassicalAdversary prims scheme →
    PRFScheme.PRFAdversary (prims.PkSeed × Adrs) prims.Y
  mkgPrfMsg : ClassicalAdversary prims scheme →
    PRFScheme.PRFAdversary (prims.Y × List Byte) prims.Y
  hmsgItsr : ClassicalAdversary prims scheme → PostHopITSRAdversary prims
  forsFDspr : ClassicalAdversary prims scheme →
    TwoPhaseAdversary (chosenTargetSpec prims .forsF) prims.PkSeed (ℕ × Bool)
  forsFTcr : ClassicalAdversary prims scheme →
    TwoPhaseAdversary (chosenTargetSpec prims .forsF) prims.PkSeed (ℕ × prims.Y)
  forsHTcrC : ClassicalAdversary prims scheme →
    TwoPhaseAdversary (chosenTargetSpec prims .forsH + collectionSpec prims)
      prims.PkSeed (ℕ × (prims.Y × prims.Y))
  forsTlTcrC : ClassicalAdversary prims scheme →
    TwoPhaseAdversary (chosenTargetSpec prims .forsTl + collectionSpec prims)
      prims.PkSeed (ℕ × Vector prims.Y p.k)
  wotsFUdC : ClassicalAdversary prims scheme →
    TwoPhaseAdversary (sampledTargetSpec prims + collectionSpec prims) prims.PkSeed Bool
  wotsFTcrC : ClassicalAdversary prims scheme →
    TwoPhaseAdversary (chosenTargetSpec prims .wotsFTcr + collectionSpec prims)
      prims.PkSeed (ℕ × prims.Y)
  wotsFPreC : ClassicalAdversary prims scheme →
    TwoPhaseAdversary (sampledTargetSpec prims + collectionSpec prims)
      prims.PkSeed (ℕ × prims.Y)
  wotsTlTcrC : ClassicalAdversary prims scheme →
    TwoPhaseAdversary (chosenTargetSpec prims .wotsTl + collectionSpec prims)
      prims.PkSeed (ℕ × Vector prims.Y p.len)
  xmssHTcrC : ClassicalAdversary prims scheme →
    TwoPhaseAdversary (chosenTargetSpec prims .xmssH + collectionSpec prims)
      prims.PkSeed (ℕ × (prims.Y × prims.Y))

def probabilityDifference (left right : ℝ≥0∞) : ℝ≥0∞ :=
  (left - right) + (right - left)

noncomputable def boolEventProbability (experiment : ProbComp Bool) : ℝ≥0∞ :=
  Pr[= true | experiment]

noncomputable def tcrProbability {p : Params} (prims : Primitives p)
    [SampleableType prims.PkSeed] (_conditions : ParameterConditions p) (role : TargetRole)
    (program : TwoPhaseAdversary (chosenTargetSpec prims role) prims.PkSeed
      (ℕ × TargetInput prims role)) : ℝ≥0∞ :=
  Pr[fun result =>
      let targets := chosenTargets result.2.2
      TargetTraceValid (p := p) role targets ∧
        TCRSuccess prims result.1 role targets result.2.1.1 result.2.1.2 |
    do
      let publicSeed ← $ᵗ prims.PkSeed
      let outcome ← runTwoPhase (chosenTargetImpl prims publicSeed role) program publicSeed
      return (publicSeed, outcome)]

noncomputable def tcrCProbability {p : Params} (prims : Primitives p)
    [SampleableType prims.PkSeed] (_conditions : ParameterConditions p) (role : TargetRole)
    (program : TwoPhaseAdversary (chosenTargetSpec prims role + collectionSpec prims)
      prims.PkSeed (ℕ × TargetInput prims role)) : ℝ≥0∞ :=
  Pr[fun result =>
      let targets := chosenTargetsC result.2.2
      TargetTraceValid (p := p) role targets ∧
        TCRSuccess prims result.1 role targets result.2.1.1 result.2.1.2 ∧
        CollectionDisjoint (targets.map TweakableTarget.tweak)
          (collectionTweaks result.2.2) |
    do
      let publicSeed ← $ᵗ prims.PkSeed
      let impl := sumQueryImpl (chosenTargetImpl prims publicSeed role)
        (collectionImpl prims publicSeed)
      let outcome ← runTwoPhase impl program publicSeed
      return (publicSeed, outcome)]

noncomputable def dsprProbability {p : Params} (prims : Primitives p)
    [SampleableType prims.PkSeed] (_conditions : ParameterConditions p)
    (program : TwoPhaseAdversary (chosenTargetSpec prims .forsF)
      prims.PkSeed (ℕ × Bool)) : ℝ≥0∞ :=
  Pr[fun result =>
      let targets := chosenTargets (role := .forsF) result.2.2
      TargetTraceValid (p := p) .forsF targets ∧
        DSPRSuccess prims result.1 targets result.2.1.1 result.2.1.2 |
    do
      let publicSeed ← $ᵗ prims.PkSeed
      let outcome ← runTwoPhase (chosenTargetImpl prims publicSeed .forsF)
        program publicSeed
      return (publicSeed, outcome)]

noncomputable def forsFSPprobability {p : Params} (prims : Primitives p)
    [SampleableType prims.PkSeed] (_conditions : ParameterConditions p)
    (program : TwoPhaseAdversary (chosenTargetSpec prims .forsF)
      prims.PkSeed (ℕ × Bool)) : ℝ≥0∞ :=
  Pr[fun result =>
      let targets := chosenTargets (role := .forsF) result.2.2
      TargetTraceValid (p := p) .forsF targets ∧
        SPprobSuccess prims result.1 targets result.2.1.1 |
    do
      let publicSeed ← $ᵗ prims.PkSeed
      let outcome ← runTwoPhase (chosenTargetImpl prims publicSeed .forsF)
        program publicSeed
      return (publicSeed, outcome)]

noncomputable def preCProbability {p : Params} (prims : Primitives p)
    [SampleableType prims.PkSeed] [SampleableType prims.Y]
    (_conditions : ParameterConditions p)
    (program : TwoPhaseAdversary (sampledTargetSpec prims + collectionSpec prims)
      prims.PkSeed (ℕ × prims.Y)) : ℝ≥0∞ :=
  Pr[fun result =>
      let targets := sampledTargets result.2.2
      SampledTraceValid (p := p) .wotsFPre targets ∧
        PRESuccess prims result.1 targets result.2.1.1 result.2.1.2 ∧
        CollectionDisjoint (targets.map Prod.fst) (collectionTweaks result.2.2) |
    do
      let publicSeed ← $ᵗ prims.PkSeed
      let impl := sumQueryImpl (sampledTargetRealImpl prims publicSeed)
        (collectionImpl prims publicSeed)
      let outcome ← runTwoPhase impl program publicSeed
      return (publicSeed, outcome)]

noncomputable def wotsUDRealProbability {p : Params} (prims : Primitives p)
    [SampleableType prims.PkSeed] [SampleableType prims.Y]
    (_conditions : ParameterConditions p)
    (program : TwoPhaseAdversary (sampledTargetSpec prims + collectionSpec prims)
      prims.PkSeed Bool) : ℝ≥0∞ :=
  Pr[fun result =>
      let targets := sampledTargets result.2.2
      result.2.1 = true ∧ SampledTraceValid (p := p) .wotsFUd targets ∧
        CollectionDisjoint (targets.map Prod.fst) (collectionTweaks result.2.2) |
    do
      let publicSeed ← $ᵗ prims.PkSeed
      let impl := sumQueryImpl (sampledTargetRealImpl prims publicSeed)
        (collectionImpl prims publicSeed)
      let outcome ← runTwoPhase impl program publicSeed
      return (publicSeed, outcome)]

noncomputable def wotsUDIdealProbability {p : Params} (prims : Primitives p)
    [SampleableType prims.PkSeed] [SampleableType prims.Y]
    (_conditions : ParameterConditions p)
    (program : TwoPhaseAdversary (sampledTargetSpec prims + collectionSpec prims)
      prims.PkSeed Bool) : ℝ≥0∞ :=
  Pr[fun result =>
      let targets := sampledTargets result.2.2
      result.2.1 = true ∧ SampledTraceValid (p := p) .wotsFUd targets ∧
        CollectionDisjoint (targets.map Prod.fst) (collectionTweaks result.2.2) |
    do
      let publicSeed ← $ᵗ prims.PkSeed
      let impl := sumQueryImpl (sampledTargetIdealImpl prims)
        (collectionImpl prims publicSeed)
      let outcome ← runTwoPhase impl program publicSeed
      return (publicSeed, outcome)]

noncomputable def itsrComponentProbability {p : Params} (prims : Primitives p)
    [SampleableType prims.Y] [DecidableEq prims.Y]
    (encode : MessageInput → List Byte) (program : PostHopITSRAdversary prims) : ℝ≥0∞ :=
  Pr[fun result =>
      let pk := program.publicKey result.1
      ITSRBreak pk encode (itsrOracleHistory pk encode result.2.2)
        (itsrChallengeForgery pk encode result.2.1) |
    do
      let state ← program.setup
      let answer ← (simulateQ (itsrDefaultImpl prims).withLogging
        (program.find state)).run
      return (state, answer)]

/-! ## Master term and theorem shape -/

noncomputable def componentTerm {p : Params} (prims : Primitives p)
    (scheme : SchemeInterface prims)
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y]
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    (conditions : ParameterConditions p) (encode : MessageInput → List Byte)
    (system : ReductionSystem prims scheme conditions)
    (adversary : ClassicalAdversary prims scheme) :
    MasterTermRole → ℝ≥0∞
  | .skgPrf => probabilityDifference
      (boolEventProbability ((skgPrfScheme prims).prfRealExp (system.skgPrf adversary)))
      (boolEventProbability (PRFScheme.prfIdealExp (system.skgPrf adversary)))
  | .mkgPrfMsg => probabilityDifference
      (boolEventProbability
        ((mkgPrfMsgScheme prims).prfRealExp (system.mkgPrfMsg adversary)))
      (boolEventProbability (PRFScheme.prfIdealExp (system.mkgPrfMsg adversary)))
  | .hmsgItsr => itsrComponentProbability prims encode (system.hmsgItsr adversary)
  | .forsFDspr =>
      dsprProbability prims conditions (system.forsFDspr adversary) -
        forsFSPprobability prims conditions (system.forsFDspr adversary)
  | .forsFTcr => tcrProbability prims conditions .forsF (system.forsFTcr adversary)
  | .forsHTcrC => tcrCProbability prims conditions .forsH (system.forsHTcrC adversary)
  | .forsTlTcrC => tcrCProbability prims conditions .forsTl (system.forsTlTcrC adversary)
  | .wotsFUdC => probabilityDifference
      (wotsUDRealProbability prims conditions (system.wotsFUdC adversary))
      (wotsUDIdealProbability prims conditions (system.wotsFUdC adversary))
  | .wotsFTcrC => tcrCProbability prims conditions .wotsFTcr
      (system.wotsFTcrC adversary)
  | .wotsFPreC => preCProbability prims conditions (system.wotsFPreC adversary)
  | .wotsTlTcrC => tcrCProbability prims conditions .wotsTl
      (system.wotsTlTcrC adversary)
  | .xmssHTcrC => tcrCProbability prims conditions .xmssH
      (system.xmssHTcrC adversary)

structure ClassicalSecurityContext {p : Params} (prims : Primitives p)
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y]
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    (_encode : MessageInput → List Byte) where
  conditions : ParameterConditions p
  scheme : SchemeInterface prims
  reductions : ReductionSystem prims scheme conditions

noncomputable def eufAdvantage {p : Params} (prims : Primitives p)
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y]
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    (scheme : SchemeInterface prims) (encode : MessageInput → List Byte)
    (adversary : ClassicalAdversary prims scheme) : ℝ≥0∞ :=
  Pr[fun sample => ForgerySuccess scheme sample.1 sample.2 |
    honestTranscriptDistribution prims scheme encode adversary]

noncomputable def repairedRHS {p : Params} {prims : Primitives p}
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y]
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    {encode : MessageInput → List Byte} (context : ClassicalSecurityContext prims encode)
    (adversary : ClassicalAdversary prims context.scheme) : ℝ≥0∞ :=
  let term :=
    componentTerm prims context.scheme context.conditions encode context.reductions adversary
  term .skgPrf
  + term .mkgPrfMsg
  + term .hmsgItsr
  + term .forsFDspr
  + 3 * term .forsFTcr
  + term .forsHTcrC
  + term .forsTlTcrC
  + ((p.w - 2 : ℕ) : ℝ≥0∞) * term .wotsFUdC
  + term .wotsFTcrC
  + term .wotsFPreC
  + term .wotsTlTcrC
  + term .xmssHTcrC

def RepairedMasterStatement {p : Params} {prims : Primitives p}
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y]
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    {encode : MessageInput → List Byte} (context : ClassicalSecurityContext prims encode) : Prop :=
  ∀ (adversary : ClassicalAdversary prims context.scheme) (qS qH : ℕ),
    AdversaryBounds adversary qS qH →
      eufAdvantage prims context.scheme encode adversary ≤ repairedRHS context adversary

theorem repairedRHS_budget_independent {p : Params} {prims : Primitives p}
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y]
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    {encode : MessageInput → List Byte} (context : ClassicalSecurityContext prims encode)
    (adversary : ClassicalAdversary prims context.scheme) (_qS₁ _qH₁ _qS₂ _qH₂ : ℕ) :
    repairedRHS context adversary = repairedRHS context adversary := rfl

end SLHDSA.Security
