/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.PRF.HiddenBit
public import VCVio.Schemes.PointerChainPuzzle.Hiding

/-!
# Time-lock encryption with the pointer-chain puzzle: the indexed hybrid and the PRF distinguisher

The hiding proof replaces the subkeys of the challenger's encryptions by keys of independent PRF
instances, one pair per encryption, and then the PRF instances by random functions. This file sets
up that step: the challenger whose envelopes evaluate PRF instances given as oracles, and the PRF
distinguisher that runs the hiding adversary against it.

## The indexed challenger

For an encryption budget `qEnc` there are `2 qEnc` PRF instances (`instanceSpec`). The `j`-th
encryption, for `j < qEnc`, takes its keystream from instance `(0, j)` and its tag from instance
`(1, j)` (`instanceIndex`): a uniform nonce, then the envelope `sealBy` with the two PRF evaluations
answered by queries to these instances (`indexedEncrypt`). The challenger's counter is the number
of accepted requests: the left-or-right oracle calls the encryption only on a pair of messages of
equal length, and each call advances the counter. An encryption beyond the `qEnc`-th, which no
adversary within the budget asks for, is the empty byte string and queries no instance.

The hybrid `indexedExperiment` is the hiding experiment of the oracles with subkeys with this
challenger in place of the envelope DEM: the puzzle and subkey queries of the adversary and of the
generator are forwarded to the oracles with subkeys, which are left unanswered, and so are the
instance queries.

## The PRF distinguisher

`indexedRun` answers the oracles with subkeys itself, as a lazily sampled random oracle, forwards
local coins, and forwards every instance query `(i, x)` to its function oracle. Run in the real
world of `prf.multiKey (Fin (2 * qEnc))` it is the hybrid with the subkeys of each encryption
replaced by independent keys of `prf`, the hybrid `G₂` of the hiding proof; run in the ideal
world, with independent random functions, it is the hybrid `G₃`, the paper's last game
(`app:hiding`), in which
every envelope has its own random encryption and tag functions and the view does not depend on
the hidden bit.
`hidingDistinguisher` draws the hidden bit itself, runs `indexedRun` at that bit and outputs
whether the adversary guessed it. In either world it outputs `true` with probability
`(p₁ + (1 - p₀)) / 2`, where `p_b` is the probability that the adversary outputs `true` against
the hybrid at bit `b` in that world (`prfRealExperiment_hidingDistinguisher`,
`prfIdealExperiment_hidingDistinguisher`); these are instances of
`PRFScheme.prfRealExperiment_guessBit` and `PRFScheme.prfIdealExperiment_guessBit`.

## Main definitions

* `PointerChainPuzzle.instanceSpec`, `PointerChainPuzzle.instanceIndex`: the `2 qEnc` PRF
  instances as one function oracle, and the instance of each kind of each encryption.
* `PointerChainPuzzle.indexedSpec`: local coins, the oracles with subkeys and the instances.
* `PointerChainPuzzle.indexedEncrypt`: the encryption of the indexed challenger.
* `PointerChainPuzzle.indexedExperiment`: the hiding experiment with the indexed challenger.
* `PointerChainPuzzle.indexedRun`: the indexed hybrid as a PRF distinguisher's game.
* `PointerChainPuzzle.hidingDistinguisher`: the PRF distinguisher of the hiding proof.

## Main statements

* `PointerChainPuzzle.prfRealExperiment_hidingDistinguisher`,
  `PointerChainPuzzle.prfIdealExperiment_hidingDistinguisher`: the success probability of the
  distinguisher is `(p₁ + (1 - p₀)) / 2` in the real and in the ideal world.
-/

public section

open OracleSpec OracleComp TimeLockPuzzle PRFScheme
open scoped ENNReal

namespace PointerChainPuzzle

open LeanSeal Envelope

variable {n m : ℕ} {S L Salt Ctx N K : Type}

/-! ## The PRF instances -/

/-- The `2 qEnc` PRF instances of the indexed hybrid as one function oracle: a query `(i, x)`
evaluates instance `i` at `x`. -/
abbrev instanceSpec (qEnc : ℕ) : OracleSpec (Fin (2 * qEnc) × ByteArray) :=
  Fin (2 * qEnc) × ByteArray →ₒ Bytes 32

/-- The instance of kind `i` of encryption `j`: the keystream (`i = 0`) is instance `j` and the tag
(`i = 1`) is instance `qEnc + j`. -/
@[expose]
def instanceIndex {qEnc : ℕ} (i : Fin 2) (j : Fin qEnc) : Fin (2 * qEnc) := finProdFinEquiv (i, j)

variable (n S L Salt Ctx N K) in
/-- The oracles of the indexed hybrid: local coins, the oracles with subkeys and the PRF
instances. -/
abbrev indexedSpec (qEnc : ℕ) := unifSpec + (sealSpec n S L Salt Ctx N K + instanceSpec qEnc)

/-! ## The indexed challenger -/

variable {w : ℕ} (codec : FixedCodec N w) (encodePuzzle : Puzzle n S L Salt → ByteArray)
  (qEnc : ℕ)

/-- The encryption of the indexed challenger under the puzzle bytes `pz`, with the counter `j` as
state: it advances the counter and, for `j < qEnc`, draws a uniform nonce from local coins and
seals `msg` with the keystream of instance `(0, j)` and the tag of instance `(1, j)` (`sealBy`).
For `j ≥ qEnc` it is the empty byte string, with no coin drawn and no instance queried. -/
@[expose]
def indexedEncrypt [SampleableType N] (pz : ByteArray) (msg : Plaintext) :
    StateT ℕ (OracleComp (indexedSpec n S L Salt Ctx N K qEnc)) ByteArray := do
  let j ← get
  set (j + 1)
  if h : j < qEnc then
    let nonce ← (liftM ($ᵗ N : ProbComp N) : OracleComp (indexedSpec n S L Salt Ctx N K qEnc) N)
    liftM (sealBy codec (μ := OracleComp (indexedSpec n S L Salt Ctx N K qEnc))
      (fun x => liftM ((indexedSpec n S L Salt Ctx N K qEnc).query
        (.inr (.inr (instanceIndex 0 ⟨j, h⟩, x)))))
      (fun x => liftM ((indexedSpec n S L Salt Ctx N K qEnc).query
        (.inr (.inr (instanceIndex 1 ⟨j, h⟩, x)))))
      pz nonce msg)
  else return ByteArray.empty

variable (m) in
/-- **The indexed hybrid** at hidden bit `b`, with the oracles with subkeys and the PRF instances
unanswered: the hiding experiment of `sealScheme` against `adv`, whose challenge queries are
answered by the left-or-right oracle over `indexedEncrypt` under the puzzle's bytes, from the
counter `0`. Local coins, puzzle queries and subkey queries are forwarded. -/
@[expose]
def indexedExperiment [NeZero n] [AddCommGroup L] [DecidableEq S] [SampleableType Salt]
    [SampleableType L] [SampleableType N] (mkCtx : Salt → Ctx) (initAcc : Ctx → S)
    (adv : HidingAdversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Plaintext ByteArray)
    (b : Bool) : OracleComp (indexedSpec n S L Salt Ctx N K qEnc) Bool := do
  let σ ← liftComp adv.preprocess (indexedSpec n S L Salt Ctx N K qEnc)
  let (puzzle, _) ← liftComp (simulateQ (sealSpec n S L Salt Ctx N K).unbatch
    (sealScheme n m mkCtx initAcc N K).gen) (indexedSpec n S L Salt Ctx N K qEnc)
  StateT.run' (simulateQ
    (((QueryImpl.ofLift unifSpec (OracleComp (indexedSpec n S L Salt Ctx N K qEnc))).liftTarget
        (StateT ℕ (OracleComp (indexedSpec n S L Salt Ctx N K qEnc))) +
      LeftOrRight.oracle (indexedEncrypt (n := n) (S := S) (L := L) (Salt := Salt) (Ctx := Ctx)
        (K := K) codec qEnc (encodePuzzle puzzle)) plaintextLength b) +
      (fun t => liftM ((indexedSpec n S L Salt Ctx N K qEnc).query (.inr (.inl t))) :
        QueryImpl (sealSpec n S L Salt Ctx N K)
          (StateT ℕ (OracleComp (indexedSpec n S L Salt Ctx N K qEnc)))))
    (simulateQ (sealSpec n S L Salt Ctx N K).unbatch (adv.online σ puzzle))) 0

/-! ## The PRF distinguisher -/

section Distinguisher

variable [NeZero n] [AddCommGroup L] [DecidableEq S] [DecidableEq L] [DecidableEq Salt]
  [DecidableEq Ctx] [DecidableEq N] [SampleableType S] [SampleableType Salt] [SampleableType L]
  [SampleableType N] [SampleableType K]

variable (m) in
/-- The indexed hybrid at hidden bit `b` as the game of a PRF distinguisher against
`2 qEnc` instances: it answers the oracles with subkeys itself, as a random oracle sampled lazily
from the empty cache, forwards local coins, and forwards every instance query `(i, x)` to its
function oracle.

Time is not modelled here. In the paper the distinguisher runs in time `t + O(Q + P')`, where `t`
is the running time of the hiding adversary, `Q = Q_pre + Q_on` its number of oracle queries and
`P' = P + 2 qEnc`, with `P = solvePoints n m`. -/
@[expose]
def indexedRun (mkCtx : Salt → Ctx) (initAcc : Ctx → S)
    (adv : HidingAdversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Plaintext ByteArray)
    (b : Bool) : PRFAdversary (Fin (2 * qEnc) × ByteArray) (Bytes 32) :=
  (simulateQ
      ((QueryImpl.ofLift unifSpec
          (OracleComp (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32)))).liftTarget
        (StateT (sealSpec n S L Salt Ctx N K).QueryCache
          (OracleComp (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32)))) +
       ((sealSpec n S L Salt Ctx N K).randomOracle.liftTarget
          (StateT (sealSpec n S L Salt Ctx N K).QueryCache
            (OracleComp (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32)))) +
        (fun x => liftM (functionQuery (R := Bytes 32) x) : QueryImpl (instanceSpec qEnc)
          (StateT (sealSpec n S L Salt Ctx N K).QueryCache
            (OracleComp (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32)))))))
      (indexedExperiment m codec encodePuzzle qEnc mkCtx initAcc adv b)).run' ∅

variable (m) in
/-- **The PRF distinguisher of the hiding proof.** It draws a uniform hidden bit `b`, runs the
hiding adversary against the indexed challenger at `b` (`indexedRun`), sampling the oracles with
subkeys itself and forwarding the keystream and tag evaluations of encryption `j` to instances
`(0, j)` and `(1, j)` of its function oracle, and outputs whether the adversary guessed `b`. -/
@[expose]
def hidingDistinguisher (mkCtx : Salt → Ctx) (initAcc : Ctx → S)
    (adv : HidingAdversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Plaintext ByteArray) :
    PRFAdversary (Fin (2 * qEnc) × ByteArray) (Bytes 32) := (do
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) :
    OracleComp (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32)) Bool)
  let g ← indexedRun m codec encodePuzzle qEnc mkCtx initAcc adv b
  return decide (g = b) : OracleComp (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32)) Bool)

variable (mkCtx : Salt → Ctx) (initAcc : Ctx → S)
  (adv : HidingAdversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Plaintext ByteArray)

/-- **Hidden-bit normalization in the real world.** Against independent keys of `prf`, one per
instance, the distinguisher outputs `true` with probability `(p₁ + (1 - p₀)) / 2`, where `p_b` is
the probability that the indexed hybrid at bit `b` outputs `true` against the same keys. -/
theorem prfRealExperiment_hidingDistinguisher (prf : PRFScheme K ByteArray (Bytes 32)) :
    Pr{let g ← ((prf.multiKey (Fin (2 * qEnc))).prfRealExperiment
        (hidingDistinguisher m codec encodePuzzle qEnc mkCtx initAcc adv))}[g = true] =
      (Pr{let g ← ((prf.multiKey (Fin (2 * qEnc))).prfRealExperiment
          (indexedRun m codec encodePuzzle qEnc mkCtx initAcc adv true))}[g = true] +
        (1 - Pr{let g ← ((prf.multiKey (Fin (2 * qEnc))).prfRealExperiment
          (indexedRun m codec encodePuzzle qEnc mkCtx initAcc adv false))}[g = true])) / 2 := by
  rw [← prEvent_not_eq_one_sub]
  simp_rw [Bool.not_eq_true]
  exact prfRealExperiment_guessBit _ _

/-- **Hidden-bit normalization in the ideal world.** Against independent random functions, one per
instance, the distinguisher outputs `true` with probability `(p₁ + (1 - p₀)) / 2`, where `p_b` is
the probability that the indexed hybrid at bit `b` outputs `true` against random functions. -/
theorem prfIdealExperiment_hidingDistinguisher :
    Pr{let g ← (prfIdealExperiment
        (hidingDistinguisher m codec encodePuzzle qEnc mkCtx initAcc adv))}[g = true] =
      (Pr{let g ← (prfIdealExperiment
          (indexedRun m codec encodePuzzle qEnc mkCtx initAcc adv true))}[g = true] +
        (1 - Pr{let g ← (prfIdealExperiment
          (indexedRun m codec encodePuzzle qEnc mkCtx initAcc adv false))}[g = true])) / 2 := by
  rw [← prEvent_not_eq_one_sub]
  simp_rw [Bool.not_eq_true]
  exact prfIdealExperiment_guessBit _

end Distinguisher

end PointerChainPuzzle
