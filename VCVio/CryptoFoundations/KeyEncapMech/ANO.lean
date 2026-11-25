/-
Copyright (c) 2026 Skas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skas
-/

module

public import VCVio.CryptoFoundations.KeyEncapMech

/-!
# Recipient anonymity for key encapsulation mechanisms

Anonymity (key privacy) asks that a ciphertext reveal nothing about which public key it was
encapsulated under. The adversary sees two honestly generated public keys and a challenge
encapsulation under one of them, chosen by a hidden bit, and guesses the bit. The game is
key-revealing: the adversary is handed the whole encapsulation, both the challenge ciphertext and
the encapsulated key, the shape used by Grubbs, Maram and Paterson. In `ANO_CPA_Game` it has only
the ambient oracles `spec`; `ANO_CCA_Game` adds a decapsulation oracle under either secret key,
which refuses the challenge ciphertext after the challenge. The advantages are the
`Measure.boolBias` of the games, as for `KEMScheme.IND_CPA_Advantage`, and
`ANO_CPA_Game_eq_ANO_CCA_Game_toANO_CCA` embeds the CPA game in the CCA game.

## References

* M. Bellare, A. Boldyreva, A. Desai and D. Pointcheval, *Key-Privacy in Public-Key Encryption*,
  ASIACRYPT 2001.
* P. Grubbs, V. Maram and K. G. Paterson, *Anonymous, Robust Post-quantum Public Key Encryption*,
  EUROCRYPT 2022. DOI 10.1007/978-3-031-07082-2_15.
-/

public section

namespace KEMScheme

open OracleSpec OracleComp ENNReal

universe u

variable {ι : Type u} {spec : OracleSpec ι} {K PK SK C : Type}
  {kem : KEMScheme (OracleComp spec) K PK SK C}

/-! ## The anonymity adversary and games -/

/-- Two-phase key-revealing anonymity adversary for a `KEMScheme`. The
hidden bit selects which of two public keys the challenge ciphertext
encapsulates under; `postChallenge` sees both public keys (encoded in the
state) together with the full challenge encapsulation, ciphertext and
encapsulated key. This is the anonymity analogue of
`KEMScheme.IND_CPA_Adversary`, which likewise hands its second phase the
challenge key. Ciphertext-only anonymity is the special case that ignores
the key argument. -/
structure ANO_CPA_Adversary (kem : KEMScheme (OracleComp spec) K PK SK C) where
  /-- Internal adversary state carried across the challenge. -/
  State : Type
  /-- Pre-challenge phase: sees both public keys, returns a state. -/
  preChallenge : PK → PK → OracleComp spec State
  /-- Post-challenge phase: sees the state, the challenge ciphertext and the
  encapsulated key. -/
  postChallenge : State → C → K → OracleComp spec Bool

/-- Fixed-branch ANO-CPA experiment: no oracle beyond the ambient `spec`;
the challenge encapsulation is under `pk0` (`b = false`) or `pk1`
(`b = true`), and both halves of it reach the adversary; the value is the
adversary's verdict bit. -/
@[expose]
noncomputable def ANO_CPA_Experiment (adversary : kem.ANO_CPA_Adversary) (b : Bool) :
    OracleComp spec Bool := do
  let (pk0, _) ← kem.keygen
  let (pk1, _) ← kem.keygen
  let st ← adversary.preChallenge pk0 pk1
  let (cStar, kStar) ← kem.encaps (if b then pk1 else pk0)
  adversary.postChallenge st cStar kStar

/-- The single-bit ANO-CPA game: a uniform hidden bit picks the key, and the
adversary guesses it from the challenge encapsulation; the game returns
whether the guess matched. -/
@[expose]
noncomputable def ANO_CPA_Game (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : kem.ANO_CPA_Adversary) : OracleComp spec Bool := do
  let (pk0, _) ← kem.keygen
  let (pk1, _) ← kem.keygen
  let st ← adversary.preChallenge pk0 pk1
  let b ← runtime.liftProbComp ($ᵗ Bool)
  let (cStar, kStar) ← kem.encaps (if b then pk1 else pk0)
  let b' ← adversary.postChallenge st cStar kStar
  return (b == b')

/-- ANO-CPA anonymity advantage: the Boolean bias of the single game. The
bias is the distinguishing advantage exactly when the game is total (both
branches produce an output; see `Measure.boolBias`'s hidden-bit identity). -/
@[expose]
noncomputable def ANO_CPA_Advantage (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : kem.ANO_CPA_Adversary) : ℝ≥0∞ :=
  (runtime.evalDist (kem.ANO_CPA_Game runtime adversary)).boolBias

/-- The ANO-CPA advantage is definitionally the bias of the single game. -/
theorem ANO_CPA_Advantage_eq_game_bias (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : kem.ANO_CPA_Adversary) :
    kem.ANO_CPA_Advantage runtime adversary =
      (runtime.evalDist (kem.ANO_CPA_Game runtime adversary)).boolBias := rfl

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
  QueryImpl.add spec.passthrough ⟨fun (bc : Bool × C) =>
    if bc.1 then kem.decaps sk1 bc.2 else kem.decaps sk0 bc.2⟩

/-- Post-challenge ANO-CCA handler: the challenge ciphertext maps to `none`
under either key; every other query decapsulates for real. -/
@[expose]
def ANO_CCA_postChallengeImpl [DecidableEq C] (sk0 sk1 : SK) (cStar : C) :
    QueryImpl (kem.ANO_CCA_oracleSpec) (OracleComp spec) :=
  QueryImpl.add spec.passthrough ⟨fun (bc : Bool × C) =>
    if bc.2 = cStar then return none
    else if bc.1 then kem.decaps sk1 bc.2 else kem.decaps sk0 bc.2⟩

/-- Two-phase key-revealing ANO-CCA adversary with a decapsulation oracle for
both keys. The second phase sees the whole challenge encapsulation,
ciphertext and encapsulated key, alongside its still-live oracle. -/
structure ANO_CCA_Adversary (kem : KEMScheme (OracleComp spec) K PK SK C) where
  /-- Internal adversary state carried across the challenge. -/
  State : Type
  /-- Pre-challenge phase: sees both public keys, may decapsulate under both. -/
  preChallenge : PK → PK → OracleComp kem.ANO_CCA_oracleSpec State
  /-- Post-challenge phase: sees the state, the challenge ciphertext and the
  encapsulated key, oracle still live. -/
  postChallenge : State → C → K → OracleComp kem.ANO_CCA_oracleSpec Bool

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
  let (cStar, kStar) ← kem.encaps (if b then pk1 else pk0)
  let b' ← simulateQ (kem.ANO_CCA_postChallengeImpl sk0 sk1 cStar)
    (adversary.postChallenge st cStar kStar)
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
      (runtime.evalDist (kem.ANO_CCA_Game runtime adversary)).boolBias := rfl

/-! ## The CPA-to-CCA embedding -/

/-- Any CPA anonymity adversary can be viewed as an ANO-CCA adversary that
simply ignores the decapsulation oracle while preserving its ordinary
pre-challenge interaction with the base oracle set `spec`. This is the
anonymity analogue of `KEMScheme.IND_CPA_Adversary.toIND_CCA`. -/
@[expose]
def ANO_CPA_Adversary.toANO_CCA (adversary : kem.ANO_CPA_Adversary) : kem.ANO_CCA_Adversary where
  State := adversary.State
  preChallenge pk0 pk1 := simulateQ
    (HasQuery.toQueryImpl (spec := spec)
      (m := OracleComp (spec + ((Bool × C) →ₒ Option K))))
    (adversary.preChallenge pk0 pk1)
  postChallenge st cStar kStar := simulateQ
    (HasQuery.toQueryImpl (spec := spec)
      (m := OracleComp (spec + ((Bool × C) →ₒ Option K))))
    (adversary.postChallenge st cStar kStar)

-- The name mirrors `IND_CPA_Adversary.toIND_CCA`, whose underscore is likewise exempt.
attribute [nolint defsWithUnderscore] ANO_CPA_Adversary.toANO_CCA

/-- The oracle-ignoring lift's pre-challenge phase, run under the game's real
pre-challenge handler, is exactly the CPA adversary's own phase re-expressed
back in `OracleComp spec` — the decapsulation oracle contributes nothing it
does not query. -/
theorem toANO_CCA_preChallenge (adversary : kem.ANO_CPA_Adversary) (sk0 sk1 : SK) (pk0 pk1 : PK) :
    simulateQ (kem.ANO_CCA_preChallengeImpl sk0 sk1)
      ((adversary.toANO_CCA).preChallenge pk0 pk1)
      = adversary.preChallenge pk0 pk1 := by
  simp only [ANO_CCA_preChallengeImpl, ANO_CPA_Adversary.toANO_CCA, ANO_CCA_oracleSpec,
    QueryImpl.add_eq_hAdd, QueryImpl.simulateQ_add_simulateQ_toQueryImpl_left]
  simp

/-- The oracle-ignoring lift's post-challenge phase, run under the game's real
post-challenge handler, is exactly the CPA adversary's own phase re-expressed
back in `OracleComp spec` — the challenge ciphertext is masked only on
queries the lifted adversary never emits, and the challenge key passes
through untouched. -/
theorem toANO_CCA_postChallenge (adversary : kem.ANO_CPA_Adversary) [DecidableEq C]
    (sk0 sk1 : SK) (cStar : C) (st : adversary.State) (c : C) (k : K) :
    simulateQ (kem.ANO_CCA_postChallengeImpl sk0 sk1 cStar)
      ((adversary.toANO_CCA).postChallenge st c k)
      = adversary.postChallenge st c k := by
  simp only [ANO_CCA_postChallengeImpl, ANO_CPA_Adversary.toANO_CCA, ANO_CCA_oracleSpec,
    QueryImpl.add_eq_hAdd, QueryImpl.simulateQ_add_simulateQ_toQueryImpl_left]
  simp

/-- The one-phase ANO-CPA game is exactly the ANO-CCA game instantiated with
the trivial CPA-to-CCA embedding `toANO_CCA` that never uses the decryption
oracle, mirroring `IND_CPA_Game_eq_IND_CCA_Game_toIND_CCA`. -/
theorem ANO_CPA_Game_eq_ANO_CCA_Game_toANO_CCA [DecidableEq C]
    (runtime : ProbCompRuntime (OracleComp spec)) (adversary : kem.ANO_CPA_Adversary) :
    kem.ANO_CPA_Game runtime adversary = kem.ANO_CCA_Game runtime adversary.toANO_CCA := by
  simp only [ANO_CPA_Game, ANO_CCA_Game, ANO_CPA_Adversary.toANO_CCA, ANO_CCA_preChallengeImpl,
    ANO_CCA_postChallengeImpl, ANO_CCA_oracleSpec, QueryImpl.add_eq_hAdd,
    QueryImpl.simulateQ_add_simulateQ_toQueryImpl_left]
  simp

end KEMScheme
