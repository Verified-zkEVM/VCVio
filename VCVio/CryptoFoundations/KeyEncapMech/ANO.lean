/-
Copyright (c) 2026 Skas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skas
-/

module

public import VCVio.CryptoFoundations.KeyEncapMech
public import VCVio.CryptoFoundations.SecExp.Measure
public import VCVio.EvalDist.Monad.Bool
public import VCVio.OracleComp.ProbCompLift
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import VCVio.OracleComp.SimSemantics.Append.Core
public import VCVio.OracleComp.Coercions.Add.Basic
public import VCVio.OracleComp.Coercions.SubSpec.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Ciphertext anonymity (key privacy) for key encapsulation mechanisms

ANO-CPA and ANO-CCA security for `KEMScheme` in the `OracleComp` idiom of
the current `KeyEncapMech` surface, mirroring the IND-CPA/IND-CCA
architecture: an adversary structure, hidden-bit games over `OracleComp`,
advantage as `Measure.boolBias` of `runtime.evalDist`, a decapsulation
oracle union `spec + ((Bool × C) →ₒ Option K)` answered through `QueryImpl.add`
with `spec.passthrough`, the challenge ciphertext excluded per
branch (`bc.2 = cStar → none`), and a CPA-to-CCA embedding whose phases
are lifted through `simulateQ`, mirroring the IND game pair of
`KeyEncapMech.lean`. -/

public section

namespace KEMScheme

open OracleSpec OracleComp ENNReal

universe u v

variable {ι : Type u} {spec : OracleSpec ι} {K PK SK C : Type}
  {kem : KEMScheme (OracleComp spec) K PK SK C}

/-! ## The anonymity adversary and games -/

/-- Two-phase ciphertext-only anonymity adversary for a `KEMScheme`. The
hidden bit selects which of two public keys the challenge ciphertext
encapsulates under; `postChallenge` sees both public keys (encoded in the
state) and the ciphertext but never the encapsulated shared key. This is
the anonymity analogue of `KEMScheme.IND_CPA_Adversary`. -/
structure ANO_Adversary (kem : KEMScheme (OracleComp spec) K PK SK C) where
  /-- Internal adversary state carried across the challenge. -/
  State : Type
  /-- Pre-challenge phase: sees both public keys, returns a state. -/
  preChallenge : PK → PK → OracleComp spec State
  /-- Post-challenge phase: sees the state and the challenge ciphertext. -/
  postChallenge : State → C → OracleComp spec Bool

/-- Fixed-branch ANO-CPA experiment: no oracle beyond the ambient `spec`;
the challenge ciphertext encapsulates under `pk0` (`b = false`) or `pk1`
(`b = true`); the value is the adversary's verdict bit. -/
@[expose]
noncomputable def ANO_CPA_Experiment (adversary : kem.ANO_Adversary) (b : Bool) :
    OracleComp spec Bool := do
  let (pk0, _) ← kem.keygen
  let (pk1, _) ← kem.keygen
  let st ← adversary.preChallenge pk0 pk1
  let (cStar, _) ← kem.encaps (if b then pk1 else pk0)
  adversary.postChallenge st cStar

/-- The single-bit ANO-CPA game: a uniform hidden bit picks the key, and the
adversary guesses it from the challenge ciphertext alone; the game returns
whether the guess matched. -/
@[expose]
noncomputable def ANO_CPA_Game (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : kem.ANO_Adversary) : OracleComp spec Bool := do
  let (pk0, _) ← kem.keygen
  let (pk1, _) ← kem.keygen
  let st ← adversary.preChallenge pk0 pk1
  let b ← runtime.liftProbComp ($ᵗ Bool)
  let (cStar, _) ← kem.encaps (if b then pk1 else pk0)
  let b' ← adversary.postChallenge st cStar
  return (b == b')

/-- ANO-CPA anonymity advantage: the Boolean bias of the single game. The
bias is the distinguishing advantage exactly when the game is total (both
branches produce an output; see `Measure.boolBias`'s hidden-bit identity). -/
@[expose]
noncomputable def ANO_CPA_Advantage (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : kem.ANO_Adversary) : ℝ≥0∞ :=
  (runtime.evalDist (kem.ANO_CPA_Game runtime adversary)).boolBias

/-- The ANO-CPA advantage is definitionally the bias of the single game. -/
theorem ANO_CPA_Advantage_eq_game_bias (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : kem.ANO_Adversary) :
    kem.ANO_CPA_Advantage runtime adversary =
      (runtime.evalDist (kem.ANO_CPA_Game runtime adversary)).boolBias := by
  unfold ANO_CPA_Advantage
  rfl

/-! ## The ANO-CCA decapsulation oracle -/

/-- Oracle index set for ANO-CCA: the ambient `spec` plus a decapsulation
oracle `(Bool × C) →ₒ Option K` carrying the choice of key. -/
@[expose]
def ANO_CCA_oracleSpec (_kem : KEMScheme (OracleComp spec) K PK SK C) :=
  spec + ((Bool × C) →ₒ Option K)

/-- Pre-challenge ANO-CCA handler: real decapsulation under the key selected
by the query's Boolean. -/
@[expose]
def ANO_CCA_preChallengeImpl (sk0 sk1 : SK) :
    QueryImpl (kem.ANO_CCA_oracleSpec) (OracleComp spec) :=
  QueryImpl.add spec.passthrough fun (bc : Bool × C) =>
    if bc.1 then kem.decaps sk1 bc.2 else kem.decaps sk0 bc.2

/-- Post-challenge ANO-CCA handler: the challenge ciphertext maps to `none`
under either key; every other query decapsulates for real. -/
@[expose]
def ANO_CCA_postChallengeImpl [DecidableEq C] (sk0 sk1 : SK) (cStar : C) :
    QueryImpl (kem.ANO_CCA_oracleSpec) (OracleComp spec) :=
  QueryImpl.add spec.passthrough fun (bc : Bool × C) =>
    if bc.2 = cStar then return none
    else if bc.1 then kem.decaps sk1 bc.2 else kem.decaps sk0 bc.2

/-- Two-phase ANO-CCA adversary with a decapsulation oracle for both keys.
Neither phase ever sees the challenge shared key. -/
structure ANO_CCA_Adversary (kem : KEMScheme (OracleComp spec) K PK SK C) where
  /-- Internal adversary state carried across the challenge. -/
  State : Type
  /-- Pre-challenge phase: sees both public keys, may decapsulate under both. -/
  preChallenge : PK → PK → OracleComp kem.ANO_CCA_oracleSpec State
  /-- Post-challenge phase: sees the state and ciphertext, oracle still live. -/
  postChallenge : State → C → OracleComp kem.ANO_CCA_oracleSpec Bool

/-- The single-bit ANO-CCA game. Both decapsulation oracles stay live
throughout; the challenge ciphertext masks itself in the post-challenge
handler. -/
@[expose]
noncomputable def ANO_CCA_Game [DecidableEq C]
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : kem.ANO_CCA_Adversary) : OracleComp spec Bool := do
  let (pk0, sk0) ← kem.keygen
  let (pk1, sk1) ← kem.keygen
  let st ← simulateQ (kem.ANO_CCA_preChallengeImpl sk0 sk1) (adversary.preChallenge pk0 pk1)
  let b ← runtime.liftProbComp ($ᵗ Bool)
  let (cStar, _) ← kem.encaps (if b then pk1 else pk0)
  let b' ← simulateQ (kem.ANO_CCA_postChallengeImpl sk0 sk1 cStar)
    (adversary.postChallenge st cStar)
  return (b == b')

/-- ANO-CCA anonymity advantage: the Boolean bias of the single game. Totality
note as for `ANO_CPA_Advantage`. -/
@[expose]
noncomputable def ANO_CCA_Advantage [DecidableEq C]
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : kem.ANO_CCA_Adversary) : ℝ≥0∞ :=
  (runtime.evalDist (kem.ANO_CCA_Game runtime adversary)).boolBias

/-- The ANO-CCA advantage is definitionally the bias of the single game. -/
theorem ANO_CCA_Advantage_eq_game_bias [DecidableEq C]
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : kem.ANO_CCA_Adversary) :
    kem.ANO_CCA_Advantage runtime adversary =
      (runtime.evalDist (kem.ANO_CCA_Game runtime adversary)).boolBias := by
  unfold ANO_CCA_Advantage
  rfl

/-! ## The CPA-to-CCA embedding -/

/-- Any ciphertext-only CPA anonymity adversary can be viewed as an ANO-CCA
adversary that simply ignores the decapsulation oracle while preserving its
ordinary pre-challenge interaction with the base oracle set `spec`. This is
the anonymity analogue of `KEMScheme.IND_CPA_Adversary.toIND_CCA`. -/
@[expose]
def ANO_Adversary.toANO_CCA (adversary : kem.ANO_Adversary) : kem.ANO_CCA_Adversary where
  State := adversary.State
  preChallenge pk0 pk1 := simulateQ
    (HasQuery.toQueryImpl (spec := spec)
      (m := OracleComp (spec + ((Bool × C) →ₒ Option K))))
    (adversary.preChallenge pk0 pk1)
  postChallenge st cStar := simulateQ
    (HasQuery.toQueryImpl (spec := spec)
      (m := OracleComp (spec + ((Bool × C) →ₒ Option K))))
    (adversary.postChallenge st cStar)

-- The name mirrors `IND_CPA_Adversary.toIND_CCA`, whose underscore is likewise exempt.
attribute [nolint defsWithUnderscore] ANO_Adversary.toANO_CCA

/-- Running a lifted computation with any handler for the added oracles folded
on top of the ambient `spec.passthrough` is the identity semantics: the
folded answers are only reachable through queries the lifted computation
emits, but its base `spec` queries pass through and it never emits an added
query, so every query is answered exactly as the ambient oracle would. -/
theorem simulateQ_add_liftM_left {α : Type}
    (impl₂ : QueryImpl ((Bool × C) →ₒ Option K) (OracleComp spec))
    (oa : OracleComp spec α) :
    simulateQ (QueryImpl.add spec.passthrough impl₂)
      (simulateQ (HasQuery.toQueryImpl (spec := spec)
          (m := OracleComp (spec + ((Bool × C) →ₒ Option K)))) oa)
      = oa := by
  rw [← QueryImpl.simulateQ_compose]
  have hcomp : QueryImpl.add spec.passthrough impl₂ ∘ₛ
      HasQuery.toQueryImpl (spec := spec)
        (m := OracleComp (spec + ((Bool × C) →ₒ Option K))) =
      QueryImpl.id' spec := by
    rw [QueryImpl.add_eq_hAdd]
    ext t
    simp [QueryImpl.compose]
    simpa using (QueryImpl.simulateQ_add_liftM_query_left (QueryImpl.id' spec) impl₂ t)
  rw [hcomp, simulateQ_id']

/-- Composing the game handler `QueryImpl.add spec.passthrough impl` with the
oracle-ignoring lift's identity handler is the identity semantics, so no
oracle answer ever enters the lifted adversary's phases. -/
theorem simulateQ_toANO_CCA {α : Type} (oa : OracleComp spec α) :
    simulateQ (QueryImpl.add spec.passthrough
        (fun (_ : Bool × C) => (pure none : OracleComp spec (Option K))))
      (simulateQ (HasQuery.toQueryImpl (spec := spec)
          (m := OracleComp (spec + ((Bool × C) →ₒ Option K)))) oa)
      = oa :=
  simulateQ_add_liftM_left _ oa

/-- The oracle-ignoring lift's pre-challenge phase, run under the game's real
pre-challenge handler, is exactly the CPA adversary's own phase re-expressed
back in `OracleComp spec` — the decapsulation oracle contributes nothing it
does not query. -/
theorem toANO_CCA_preChallenge (adversary : kem.ANO_Adversary) (sk0 sk1 : SK) (pk0 pk1 : PK) :
    simulateQ (kem.ANO_CCA_preChallengeImpl sk0 sk1)
      ((adversary.toANO_CCA).preChallenge pk0 pk1)
      = adversary.preChallenge pk0 pk1 :=
  simulateQ_add_liftM_left _ _

/-- The oracle-ignoring lift's post-challenge phase, run under the game's real
post-challenge handler, is exactly the CPA adversary's own phase re-expressed
back in `OracleComp spec` — the challenge ciphertext is masked only on
queries the lifted adversary never emits. -/
theorem toANO_CCA_postChallenge (adversary : kem.ANO_Adversary) [DecidableEq C]
    (sk0 sk1 : SK) (cStar : C) (st : adversary.State) (c : C) :
    simulateQ (kem.ANO_CCA_postChallengeImpl sk0 sk1 cStar)
      ((adversary.toANO_CCA).postChallenge st c)
      = adversary.postChallenge st c :=
  simulateQ_add_liftM_left _ _

/-- The one-phase ANO-CPA game is exactly the ANO-CCA game instantiated with
the trivial CPA-to-CCA embedding `toANO_CCA` that never uses the decryption
oracle, mirroring `IND_CPA_Game_eq_IND_CCA_Game_toIND_CCA`. -/
theorem ANO_CPA_Game_eq_ANO_CCA_Game_toANO_CCA [DecidableEq C]
    (runtime : ProbCompRuntime (OracleComp spec)) (adversary : kem.ANO_Adversary) :
    kem.ANO_CPA_Game runtime adversary = kem.ANO_CCA_Game runtime adversary.toANO_CCA := by
  simp only [ANO_CPA_Game, ANO_CCA_Game, ANO_Adversary.toANO_CCA,
    ANO_CCA_preChallengeImpl, ANO_CCA_postChallengeImpl, ANO_CCA_oracleSpec,
    simulateQ_add_liftM_left]

end KEMScheme
