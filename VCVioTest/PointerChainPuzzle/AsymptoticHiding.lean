/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.Schemes.PointerChainPuzzle.AsymptoticHiding
public import VCVio.Schemes.PointerChainPuzzle.LeanSealDelay
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Time-lock encryption with the pointer-chain puzzle: checks of asymptotic hiding

Checks through the public API:

* the asymptotic hiding theorems depend on the standard axioms only;
* **satisfiability of the hypotheses** (gotcha 14): one parameter family satisfies every hypothesis
  of `hidingSecurityGame_secureAgainst_of_card` at once, with a nonempty adversary class.

The family has two chains of one step at every parameter (`n = 2`, `m = 1`, so `P = 9` and
`keyRound 2 1 - 1 = 6` rounds), hashes, links and nonces of `lam` bytes, and one-byte salts,
contexts and PRF keys. The class is every adversary family with at most `lam` preprocessing
queries, at most `lam` online points within the round limit, and no challenge query. The PRF
assumption is then about zero independent keys, where the function oracle has an empty domain and
every distinguisher has advantage zero (`prfAdvantage_multiKey_of_eq_zero`), so it holds against
all distinguisher families. The idle adversary family is in the class.

This is a toy witness of logical consistency only. With a positive challenge budget the PRF
hypothesis is a computational assumption, which no unconditional witness can discharge against all
distinguishers: a PRF with finitely many keys on the infinite domain `ByteArray` is told apart
from a random function by an exhaustive distinguisher.
-/

public section

open OracleComp OracleSpec PRFScheme TimeLockPuzzle PointerChainPuzzle
  PointerChainPuzzle.LeanSeal PointerChainPuzzle.LeanSeal.Envelope
open scoped ENNReal

namespace VCVioTest.PointerChainPuzzle.AsymptoticHiding

/-! ## Axioms -/

/--
info: 'PointerChainPuzzle.hidingSecurityGame_secureAgainst' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hidingSecurityGame_secureAgainst

/--
info: 'PointerChainPuzzle.hidingSecurityGame_secureAgainst_of_card' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hidingSecurityGame_secureAgainst_of_card

/-! ## A PRF game with no keys -/

/-- With no instances, the multi-key PRF game is the same in both worlds: the function oracle has
an empty domain, so the real handler does not depend on the (empty) key family, and the lazy
random oracle answers only uniform queries. -/
theorem prfAdvantage_multiKey_of_eq_zero {K D R : Type} [DecidableEq D] [SampleableType R]
    (prf : PRFScheme K D R) {u : ℕ} (hu : u = 0) (adversary : PRFAdversary (Fin u × D) R) :
    prfAdvantage (prf.multiKey (Fin u)) adversary = 0 := by
  subst hu
  set impl : QueryImpl (PRFOracleSpec (Fin 0 × D) R) ProbComp :=
    (prf.multiKey (Fin 0)).prfRealQueryImpl Fin.elim0
  have hreal : ∀ ks, (prf.multiKey (Fin 0)).prfRealQueryImpl ks = impl := by
    intro ks
    funext t
    rcases t with t | ⟨i, _⟩
    · rfl
    · exact i.elim0
  have hideal : prfIdealQueryImpl (D := Fin 0 × D) (R := R) =
      impl.liftTarget (StateT ((Fin 0 × D →ₒ R).QueryCache) ProbComp) := by
    funext t
    rcases t with t | ⟨i, _⟩
    · rfl
    · exact i.elim0
  have hkey : (prf.multiKey (Fin 0)).keygen = pure Fin.elim0 := rfl
  rw [prfAdvantage, prfRealExperiment, prfIdealExperiment, hkey, pure_bind, hreal, hideal,
    simulateQ_liftTarget]
  have hrun : (liftM (simulateQ impl adversary) :
      StateT ((Fin 0 × D →ₒ R).QueryCache) ProbComp Bool).run' ∅ = simulateQ impl adversary := by
    simp
  rw [hrun]
  simp

/-! ## Growth of the byte strings -/

/-- `2^(-8 lam)` is negligible: it is at most `(1/2)^lam`, which decays superpolynomially. -/
theorem negligible_inv_card_bytes :
    negligible fun lam => (Fintype.card (Bytes lam) : ℝ≥0∞)⁻¹ := by
  have hdecay : negligible fun lam => ENNReal.ofReal ((1 / 2 : ℝ) ^ lam) :=
    (negligible_ofReal_iff fun _ => by positivity).2 fun k =>
      tendsto_pow_const_mul_const_pow_of_lt_one k (by norm_num) (by norm_num)
  refine negligible_of_le (fun lam => ?_) hdecay
  rw [card_bytes, ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos two_pos,
    ENNReal.ofReal_ofNat, Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]
  exact pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.2 one_le_two) (by omega)

/-! ## The family -/

/-- One-byte salts, contexts and PRF keys at every parameter. -/
abbrev OneByte : ℕ → Type := fun _ => Bytes 1

/-- A toy PRF with one-byte keys: every key and input gives the zero block. -/
@[expose]
def toyPRF : PRFScheme (Bytes 1) ByteArray (Bytes 32) where
  keygen := $ᵗ Bytes 1
  eval _ _ := 0

/-- The toy PRF draws its key uniformly. -/
theorem toyPRF_uniformKey : toyPRF.UniformKey :=
  rfl

/-- The adversary family that makes no query and guesses `false`. -/
@[expose]
def idleFamily : HidingAdversaryFamily (fun _ => 2) Bytes Bytes OneByte OneByte Bytes OneByte :=
  fun _ => { State := Unit, preprocess := pure (), online := fun _ _ => pure false }

/-- The idle family is in the class with at most `lam` preprocessing queries, at most `lam`
online points within `keyRound 2 1 - 1` rounds, no challenge query, and no efficiency condition. -/
theorem idleFamily_mem :
    hidingAdversaryClass (fun _ => 1) id id (fun _ => 0) (fun _ => True) idleFamily :=
  ⟨trivial, fun _ => ⟨⟨trivial, fun _ _ => isOnlineQueryBound_pure _ _⟩,
    fun _ _ => isQueryBoundP_pure _ _ _⟩⟩

/-- The asymptotic hiding game of the toy family: `n = 2`, `m = 1`, hashes, links and nonces of
`lam` bytes, one-byte salts, contexts and keys, the toy PRF, nonces encoded as themselves, the
empty puzzle encoding, the identity context and the zero initial accumulator. -/
noncomputable abbrev toyGame :
    SecurityGame (HidingAdversaryFamily (fun _ => 2) Bytes Bytes OneByte OneByte Bytes OneByte) :=
  hidingSecurityGame (fun _ => 1) (fun _ => toyPRF) FixedCodec.bytes (fun _ _ => ByteArray.empty)
    (fun _ => id) (fun _ _ => 0)

/-- **Satisfiability of the hypotheses of asymptotic hiding.** For the toy family, budgets
`Q_pre = Q_on = lam` and `q_enc = 0`, and the polynomial `X + 9`, every hypothesis of
`hidingSecurityGame_secureAgainst_of_card` holds, with the class of all distinguisher families as
`isPPT'`. -/
theorem toyGame_secureAgainst :
    toyGame.secureAgainst (hidingAdversaryClass (fun _ => 1) id id (fun _ => 0) fun _ => True) :=
  hidingSecurityGame_secureAgainst_of_card (p := Polynomial.X + Polynomial.C 9)
    (isPPT' := fun _ => True) _ _ _ _ _ (fun _ => toyPRF_uniformKey)
    (fun _ => Function.injective_id) negligible_inv_card_bytes negligible_inv_card_bytes
    negligible_inv_card_bytes (fun _ => by simp [solvePoints]) (fun _ => by simp)
    (fun _ => by simp) (fun _ => by simp) (fun _ _ => trivial)
    (fun _ _ => negligible_of_zero fun _ => prfAdvantage_multiKey_of_eq_zero _ rfl _)

/-- The idle family has negligible advantage, as a member of the class. -/
example : negligible (toyGame.advantage idleFamily) :=
  toyGame_secureAgainst _ idleFamily_mem

end VCVioTest.PointerChainPuzzle.AsymptoticHiding
