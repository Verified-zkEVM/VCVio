/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.Hiding

/-!
# Time-lock encryption with the pointer-chain puzzle: checks of the private-subkey hybrid

Checks through the public API, for two chains of one step (`n = 2`, `m = 1`) over `S = Fin 11`,
`L = Fin 5`, `Salt = Ctx = Fin 3`, nonces `N = Fin 4` and PRF keys `K = Fin 7`, with the PRF, the
nonce codec and the puzzle encoding left as parameters:

* `delayAdvantage_sealScheme_le` gives the bound of `delayAdvantage_scheme_le`,
  `Q_on / 5 + Q_pre / 15 + ((Q_pre + Q_on) 9 + 81 + 1) / 11`;
* `sealDerive` queries exactly the two subkey oracles, each once, at the key and the nonce, in that
  order: a trace against a fixed table logs `[.inr (.inl (key, nonce)), .inr (.inr (key, nonce))]`
  and returns the table's two answers;
* a concrete hiding adversary, which asks one challenge and submits one round holding the subkey
  point at the puzzle's commitment, has the budget `(0, (6, 1))`, which `privateAdversary` keeps
  (`isQueryBound_privateAdversary`), and `prEvent_privateExperiment_badK_le` bounds its `BadK` by
  `1 / 5 + (9 + 81 + 1) / 11`.
* for that adversary, `absDiff_hidingExperiment_privateExperiment_le` bounds the gap between the
  hiding experiment's probability of `true` and the hybrid's by `BadK`, and with the `BadK` bound
  by `1 / 5 + (9 + 81 + 1) / 11`, at either hidden bit.

The answer types are sampled through `SampleableType.Fin`, so loading this module enumerates no
type.
-/

public section

open OracleComp OracleSpec PointerChainPuzzle PointerChainPuzzle.LeanSeal
  PointerChainPuzzle.LeanSeal.Envelope
open scoped ENNReal

namespace VCVioTest.PointerChainPuzzle.Hiding

/-- States are `Fin 11`. -/
abbrev S := Fin 11

/-- Links are `Fin 5`. -/
abbrev L := Fin 5

/-- Salts and contexts are `Fin 3`. -/
abbrev Salt := Fin 3

/-- Nonces are `Fin 4`. -/
abbrev N := Fin 4

/-- PRF keys are `Fin 7`. -/
abbrev K := Fin 7

/-- The oracles with subkeys at these parameters. -/
abbrev spec := sealSpec 2 S L Salt Salt N K

/-- The context of a salt. -/
def mkCtx (salt : Salt) : Salt := salt + 1

/-- The initial accumulator of a context. -/
def initAcc (ctx : Salt) : S := ⟨ctx.val + 6, by omega⟩

/-- Adding one is injective on `Fin 3`. -/
lemma mkCtx_injective : Function.Injective mkCtx := fun a b h => by
  simpa [mkCtx] using h

/-! ## Delay of the puzzle over the oracles with subkeys -/

/-- `sealScheme` has the delay bound of `scheme`. -/
lemma delayAdvantage_sealScheme_small
    {adv : TimeLockPuzzle.Adversary spec (Puzzle 2 S L Salt) S}
    {Qpre Qon : ℕ} (hadv : adv.IsQueryBound Qpre (6, Qon)) :
    (sealScheme 2 1 mkCtx initAcc N K).delayAdvantage adv ≤
      (Qon : ℝ≥0∞) / 5 + Qpre / (3 * 5) + ((Qpre + Qon) * 9 + 9 ^ 2 + 1) / 11 := by
  have hP : solvePoints 2 1 = 9 := rfl
  simpa [hP] using delayAdvantage_sealScheme_le (m := 1) mkCtx initAcc mkCtx_injective hadv

/-! ## The subkey derivation -/

/-- The encryption subkey of the table: the sum of the key and the nonce. -/
@[expose]
def encKey (x : S × N) : K := ⟨(x.1.val + x.2.val) % 7, Nat.mod_lt _ (by decide)⟩

/-- The MAC subkey of the table: the key plus twice the nonce, plus one. -/
@[expose]
def macKey (x : S × N) : K := ⟨(x.1.val + 2 * x.2.val + 1) % 7, Nat.mod_lt _ (by decide)⟩

/-- Answers the puzzle oracles from `g` and the subkey oracles from `encKey` and `macKey`, and
logs every queried point. -/
@[expose]
def traceImpl (g : (p : Point 2 S L Salt Salt) → (oracleSpec 2 S L Salt Salt).Range p) :
    QueryImpl spec (StateM (List (Point 2 S L Salt Salt ⊕ (S × N ⊕ S × N))))
  | .inl p => do modify (· ++ [.inl p]); pure (g p)
  | .inr (.inl x) => do modify (· ++ [.inr (.inl x)]); pure (encKey x)
  | .inr (.inr x) => do modify (· ++ [.inr (.inr x)]); pure (macKey x)

/-- `sealDerive key nonce` queries the encryption subkey oracle at `(key, nonce)`, then the MAC
subkey oracle at `(key, nonce)`, and nothing else, and returns the two answers. -/
theorem sealDerive_trace (g : (p : Point 2 S L Salt Salt) → (oracleSpec 2 S L Salt Salt).Range p)
    (key : S) (nonce : N) :
    (simulateQ (traceImpl g) (sealDerive (n := 2) (L := L) (Salt := Salt) (Ctx := Salt)
      (K := K) key nonce)).run [] =
      ((encKey (key, nonce), macKey (key, nonce)),
        [.inr (.inl (key, nonce)), .inr (.inr (key, nonce))]) :=
  rfl

/-- At a concrete key and nonce: the subkeys `(5, 1)` from the points `(3, 2)` of both oracles. -/
example (g : (p : Point 2 S L Salt Salt) → (oracleSpec 2 S L Salt Salt).Range p) :
    (simulateQ (traceImpl g) (sealDerive (n := 2) (L := L) (Salt := Salt) (Ctx := Salt)
      (K := K) (3 : S) (2 : N))).run [] =
      (((5 : K), (1 : K)), [.inr (.inl ((3 : S), (2 : N))), .inr (.inr ((3 : S), (2 : N)))]) := by
  rw [sealDerive_trace]
  rfl

/-- With the oracles answered by a table, the derived subkeys are the table's answers at the two
subkey points. -/
example (f : QueryImpl spec Id) (key : S) :
    subkeysAt f (sealDerive (n := 2) (L := L) (Salt := Salt) (Ctx := Salt) (K := K) key) =
      fun nonce => (f (.inr (.inl (key, nonce))), f (.inr (.inr (key, nonce)))) :=
  rfl

/-! ## A concrete hiding adversary -/

variable (prf : PRFScheme K ByteArray (Bytes 32)) (codec : FixedCodec N 1)
  (encodePuzzle : Puzzle 2 S L Salt → ByteArray)

/-- No preprocessing; the online phase asks one challenge on two empty messages, submits one round
holding the encryption subkey point at the puzzle's commitment and the nonce `0`, and guesses
whether the challenge was answered. -/
def hidingAdv : TimeLockPuzzle.HidingAdversary spec (Puzzle 2 S L Salt) Plaintext ByteArray where
  State := Unit
  preprocess := pure ()
  online _ puzzle := do
    let c ← liftM (((unifSpec + LeftOrRight.spec Plaintext ByteArray) + spec.batch).query
      (.inl (.inr (default, default))))
    let _ ← liftM (((unifSpec + LeftOrRight.spec Plaintext ByteArray) + spec.batch).query
      (.inr [.inr (.inl (puzzle.commitment, 0))]))
    return c.isSome

/-- The adversary makes no preprocessing query and one round of one point; the challenge is
free. -/
lemma hidingAdv_isQueryBound : hidingAdv.IsQueryBound 0 (6, 1) :=
  ⟨trivial, fun _ _ => (isOnlineQueryBound_query_bind_inl_iff _ _ _).2 fun _ =>
    (isOnlineQueryBound_query_bind_inr_iff _ _ _).2
      ⟨by simp, fun _ => isOnlineQueryBound_pure _ _⟩⟩

/-- Inlining the private challenger keeps the budget, at either hidden bit. -/
lemma privateAdversary_hidingAdv_isQueryBound (b : Bool) :
    (privateAdversary prf codec encodePuzzle hidingAdv b).IsQueryBound 0 (6, 1) :=
  isQueryBound_privateAdversary prf codec encodePuzzle hidingAdv_isQueryBound b

/-- In the hybrid, the adversary caches a subkey point at the key with probability at most
`1 / 5 + (9 + 81 + 1) / 11`. -/
lemma prEvent_privateExperiment_hidingAdv_badK_le (b : Bool) :
    Pr{let z ← (simulateQ spec.romImpl
        (privateExperiment 1 prf codec encodePuzzle mkCtx initAcc hidingAdv b)).run ∅}[
        BadK z.1.2 z.2] ≤
      1 / 5 + (9 + 9 ^ 2 + 1) / 11 := by
  have hP : solvePoints 2 1 = 9 := rfl
  simpa [hP] using prEvent_privateExperiment_badK_le (m := 1) prf codec encodePuzzle mkCtx
    initAcc mkCtx_injective hidingAdv_isQueryBound b

/-- The first hop for the adversary: the hiding experiment's probability of `true` and the
hybrid's probability of the guess `true` differ by at most the probability of `BadK` in the hybrid,
at either hidden bit. -/
lemma absDiff_hidingExperiment_hidingAdv_le_badK (b : Bool) :
    ENNReal.absDiff
      ((ProbCompRuntime.rom spec).evalDist
        ((sealScheme 2 1 mkCtx initAcc N K).hidingExperiment
          (sealDEM (Ctx := Salt) prf codec encodePuzzle) plaintextLength hidingAdv b) {true})
      (Pr{let z ← (simulateQ spec.romImpl
        (privateExperiment 1 prf codec encodePuzzle mkCtx initAcc hidingAdv b)).run ∅}[
          z.1.1 = true]) ≤
      Pr{let z ← (simulateQ spec.romImpl
        (privateExperiment 1 prf codec encodePuzzle mkCtx initAcc hidingAdv b)).run ∅}[
          BadK z.1.2 z.2] :=
  absDiff_hidingExperiment_privateExperiment_le prf codec encodePuzzle mkCtx initAcc hidingAdv b

/-- With the `BadK` bound, the hiding experiment's probability of `true` and the hybrid's
probability of the guess `true` differ by at most `1 / 5 + (9 + 81 + 1) / 11`, at either hidden
bit. -/
lemma absDiff_hidingExperiment_hidingAdv_le (b : Bool) :
    ENNReal.absDiff
      ((ProbCompRuntime.rom spec).evalDist
        ((sealScheme 2 1 mkCtx initAcc N K).hidingExperiment
          (sealDEM (Ctx := Salt) prf codec encodePuzzle) plaintextLength hidingAdv b) {true})
      (Pr{let z ← (simulateQ spec.romImpl
        (privateExperiment 1 prf codec encodePuzzle mkCtx initAcc hidingAdv b)).run ∅}[
          z.1.1 = true]) ≤
      1 / 5 + (9 + 9 ^ 2 + 1) / 11 :=
  (absDiff_hidingExperiment_hidingAdv_le_badK prf codec encodePuzzle b).trans
    (prEvent_privateExperiment_hidingAdv_badK_le prf codec encodePuzzle b)

end VCVioTest.PointerChainPuzzle.Hiding
