/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.Schemes.PointerChainPuzzle.HidingTheorem
public import VCVio.CryptoFoundations.PRF.Asymptotic

/-!
# Asymptotic hiding of time-lock encryption with the pointer-chain puzzle

`hidingAdvantage_sealScheme_le` bounds the hiding advantage of one adversary against one instance
of `sealScheme` with `sealDEM`, at fixed sizes, types and budgets, by statistical terms plus twice
the advantage of the named PRF distinguisher `hidingDistinguisher`. This file states the
asymptotic form: for families of all of these indexed by a security parameter `lam`, every
adversary family in a budgeted class has negligible hiding advantage, provided the statistical
terms are negligible along the family and the multi-key PRF family is secure against a class
containing the distinguishers of the adversaries in the class
(`hidingSecurityGame_secureAgainst`). With superpolynomially growing hash, link and nonce spaces
and polynomial budgets and puzzle sizes the statistical terms are negligible
(`negligible_hidingStatisticalBound`, `hidingSecurityGame_secureAgainst_of_card`).

## Concrete and asymptotic statements

A class of adversary families defined by asymptotic efficiency restricts nothing at a single
parameter: a polynomial-time family may run exhaustive search at any fixed `lam`, because its cost
at finitely many parameters is a constant. A bound at one parameter for the members of such
families must therefore hold for every adversary at that parameter. The statement here is about
families and concludes negligible advantage (`SecurityGame.secureAgainst`). It follows from the
concrete theorem at every `lam` by `SecurityGame.secureAgainst_of_close_poly_reduction`, with loss
`2`, the reduction `hidingReduction`, and twice the statistical terms as the negligible slack.

The leanSeal byte instantiation (`LeanSeal.hidingAdvantage_byteScheme_le`) stays concrete. Its
sizes are fixed by the specification (32-byte hashes, 16-byte salts and nonces, links of at most
32 bytes), so it is one parameter, not a family, and has no asymptotic statement of its own.

## Parameter families

Everything is indexed by `lam : ℕ`: the sizes `n lam` and `m lam`; the types `S lam`, `L lam`,
`Salt lam`, `Ctx lam`, `N lam` and `K lam`, as dependent families with their instances at every
`lam`; and the data `prf lam`, `codec lam`, `encodePuzzle lam`, `mkCtx lam` and `initAcc lam`.
The PRF's domain `ByteArray` and range `Bytes 32`, the plaintexts and the ciphertexts are the same
at every `lam`, as in `sealDEM`.

## The adversary class

An adversary is a family `A : HidingAdversaryFamily n S L Salt Ctx N K`, one hiding adversary for
each `lam`. The class `hidingAdversaryClass m Qpre Qon qEnc isEff` holds the families that satisfy
an efficiency predicate `isEff` and whose member at `lam` makes at most `Qpre lam` preprocessing
queries, has an online phase within `keyRound (n lam) (m lam) - 1` rounds holding at most
`Qon lam` points, and makes at most `qEnc lam` challenge queries.

* **The round bound is part of the class.** Polynomial time does not bound sequential depth: a
  polynomial-time adversary may solve the puzzle by evaluating the chain one round at a time, in
  `keyRound` rounds, and then decrypt. Hiding holds only before the solver could finish, so the
  round limit must be stated separately from efficiency.
* **The query budgets are part of the class** because the statistical terms are stated in them.
  They are functions of `lam` fixed by the class, as `TimeLockPuzzle.HidingSecure` fixes them at
  one parameter. Every polynomial-time family has polynomial budgets, so quantifying the theorem
  over all budget functions with negligible statistical terms covers every such family.
* **Efficiency is abstract.** `isEff` is a predicate on families. The theorem uses only the
  hypothesis `hreduce` that the reduction maps the class into the PRF adversary class `isPPT'`;
  that hypothesis is the efficiency obligation of the reduction (`hidingDistinguisher` runs the
  adversary and simulates the random oracles), to be discharged by a cost model such as
  `VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity`.

## The PRF assumption

The reduction `hidingReduction` maps a family `A` to the family of distinguishers
`hidingDistinguisher` against `2 * qEnc lam` independent keys of `prf lam`. Because `qEnc` is fixed
by the class rather than chosen by the adversary, the number of keys is a function of `lam` alone,
and the assumption is the security of the PRF family
`fun lam => (prf lam).multiKey (Fin (2 * qEnc lam))` (`PRFScheme.prfSecurityGame`) against
`isPPT'`. For polynomial `qEnc` this is PRF security with polynomially many independent keys, the
paper's `Adv^prf_{2 Q_enc}`.

## Main definitions

* `PointerChainPuzzle.HidingAdversaryFamily`: hiding adversaries indexed by the security
  parameter.
* `PointerChainPuzzle.hidingAdversaryClass`: the budgeted adversary class.
* `PointerChainPuzzle.hidingStatisticalBound`: the statistical terms of the concrete bound.
* `PointerChainPuzzle.hidingSecurityGame`: the asymptotic hiding game of the scheme family.
* `PointerChainPuzzle.hidingReduction`: the family of PRF distinguishers of an adversary family.

## Main statements

* `PointerChainPuzzle.hidingSecurityGame_advantage_le`: the concrete bound at each parameter.
* `PointerChainPuzzle.hidingSecurityGame_secureAgainst`: asymptotic hiding, for negligible
  statistical terms and a secure multi-key PRF family.
* `PointerChainPuzzle.negligible_hidingStatisticalBound`: the statistical terms are negligible
  for superpolynomial `|S|`, `|L|` and `|N|` and polynomial budgets and puzzle sizes.
* `PointerChainPuzzle.hidingSecurityGame_secureAgainst_of_card`: asymptotic hiding under those
  growth conditions.
-/

public section

open OracleSpec OracleComp TimeLockPuzzle PRFScheme
open scoped ENNReal

namespace PointerChainPuzzle

open LeanSeal Envelope

variable {n m : ℕ → ℕ} {S L Salt Ctx N K : ℕ → Type}

/-! ## Adversary families and the class -/

variable (n S L Salt Ctx N K) in
/-- A family of hiding adversaries against the sealed scheme, one for each security parameter
`lam`, against the oracles `sealSpec` at the sizes and types of `lam`. -/
abbrev HidingAdversaryFamily : Type 1 :=
  (lam : ℕ) → HidingAdversary
    (sealSpec (n lam) (S lam) (L lam) (Salt lam) (Ctx lam) (N lam) (K lam))
    (Puzzle (n lam) (S lam) (L lam) (Salt lam)) Plaintext ByteArray

variable (m) in
/-- The adversary class of the asymptotic hiding theorem: the families `A` satisfying the
efficiency predicate `isEff` whose member at every `lam` makes at most `Qpre lam` preprocessing
queries, has an online phase within `keyRound (n lam) (m lam) - 1` rounds holding at most
`Qon lam` points, and makes at most `qEnc lam` challenge queries. The round bound is separate from
`isEff` because efficiency does not bound sequential depth. -/
@[expose]
def hidingAdversaryClass (Qpre Qon qEnc : ℕ → ℕ)
    (isEff : HidingAdversaryFamily n S L Salt Ctx N K → Prop)
    (A : HidingAdversaryFamily n S L Salt Ctx N K) : Prop :=
  isEff A ∧ ∀ lam, (A lam).IsQueryBound (Qpre lam) (keyRound (n lam) (m lam) - 1, Qon lam) ∧
    (A lam).MakesAtMostQueries (qEnc lam)

/-! ## The statistical terms -/

variable (n m S L Salt N) in
/-- The statistical terms of the hiding bound at the security parameter `lam`:
`[n ≥ 2] Q_on / |L| + Q_pre / (|Salt| |L|) + (Q (P + 1) + P²) / |S| + q_enc² / (2 |N|)`, with
`P = solvePoints (n lam) (m lam)` and `Q = Q_pre + Q_on`, at the sizes and budgets of `lam`.
The concrete bound `hidingAdvantage_sealScheme_le` is twice this plus twice the PRF advantage. -/
@[expose]
noncomputable def hidingStatisticalBound [∀ lam, Fintype (S lam)] [∀ lam, Fintype (L lam)]
    [∀ lam, Fintype (Salt lam)] [∀ lam, Fintype (N lam)] (Qpre Qon qEnc : ℕ → ℕ) (lam : ℕ) :
    ℝ≥0∞ :=
  (if 2 ≤ n lam then (Qon lam : ℝ≥0∞) / Fintype.card (L lam) else 0) +
    Qpre lam / (Fintype.card (Salt lam) * Fintype.card (L lam)) +
      ((Qpre lam + Qon lam) * (solvePoints (n lam) (m lam) + 1) +
          (solvePoints (n lam) (m lam) : ℝ≥0∞) ^ 2) / Fintype.card (S lam) +
      (qEnc lam : ℝ≥0∞) ^ 2 / (2 * Fintype.card (N lam))

/-- The statistical terms are negligible when the hash, link and nonce spaces grow
superpolynomially, salts exist, and the budgets and the puzzle work `solvePoints` are bounded by a
polynomial `p` in `lam`. Each term is a polynomial numerator over one of `|L|`, `|S|` and `|N|`;
the salt factor only enlarges a denominator. -/
theorem negligible_hidingStatisticalBound [∀ lam, Fintype (S lam)] [∀ lam, Fintype (L lam)]
    [∀ lam, Fintype (Salt lam)] [∀ lam, Fintype (N lam)] [∀ lam, Nonempty (Salt lam)]
    (hS : negligible fun lam => (Fintype.card (S lam) : ℝ≥0∞)⁻¹)
    (hL : negligible fun lam => (Fintype.card (L lam) : ℝ≥0∞)⁻¹)
    (hN : negligible fun lam => (Fintype.card (N lam) : ℝ≥0∞)⁻¹)
    {Qpre Qon qEnc : ℕ → ℕ} {p : Polynomial ℕ}
    (hP : ∀ lam, solvePoints (n lam) (m lam) ≤ p.eval lam) (hQpre : ∀ lam, Qpre lam ≤ p.eval lam)
    (hQon : ∀ lam, Qon lam ≤ p.eval lam) (hqEnc : ∀ lam, qEnc lam ≤ p.eval lam) :
    negligible (hidingStatisticalBound n m S L Salt N Qpre Qon qEnc) := by
  refine negligible_add (negligible_add (negligible_add ?_ ?_) ?_) ?_
  · refine negligible_of_le (fun lam => ?_) (negligible_natMul_of_poly_bound hL hQon)
    split_ifs
    · rw [div_eq_mul_inv]
    · exact zero_le
  · refine negligible_of_le (fun lam => ?_) (negligible_natMul_of_poly_bound hL hQpre)
    rw [div_eq_mul_inv]
    gcongr
    exact le_mul_of_one_le_left zero_le (Nat.one_le_cast.2 Fintype.card_pos)
  · refine negligible_of_le (fun lam => le_of_eq ?_) (negligible_natMul_of_poly_bound hS
      (g := fun lam => (Qpre lam + Qon lam) * (solvePoints (n lam) (m lam) + 1) +
        solvePoints (n lam) (m lam) ^ 2) (p := (p + p) * (p + 1) + p ^ 2) fun lam => ?_)
    · push_cast
      rw [div_eq_mul_inv]
    · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_one]
      gcongr
      · exact hQpre lam
      · exact hQon lam
      · exact hP lam
      · exact hP lam
  · refine negligible_of_le (fun lam => ?_) (negligible_natMul_of_poly_bound hN
      (g := fun lam => qEnc lam ^ 2) (p := p ^ 2) fun lam => by
        rw [Polynomial.eval_pow]
        exact Nat.pow_le_pow_left (hqEnc lam) 2)
    push_cast
    rw [div_eq_mul_inv]
    gcongr
    exact le_mul_of_one_le_left zero_le one_le_two

/-! ## The game and the reduction -/

section Game

variable [∀ lam, NeZero (n lam)] [∀ lam, AddCommGroup (L lam)] [∀ lam, DecidableEq (S lam)]
  [∀ lam, DecidableEq (L lam)] [∀ lam, DecidableEq (Salt lam)] [∀ lam, DecidableEq (Ctx lam)]
  [∀ lam, DecidableEq (N lam)] [∀ lam, SampleableType (S lam)] [∀ lam, SampleableType (Salt lam)]
  [∀ lam, SampleableType (L lam)] [∀ lam, SampleableType (N lam)] [∀ lam, SampleableType (K lam)]

variable (prf : (lam : ℕ) → PRFScheme (K lam) ByteArray (Bytes 32)) {w : ℕ → ℕ}
  (codec : (lam : ℕ) → FixedCodec (N lam) (w lam))
  (encodePuzzle : (lam : ℕ) → Puzzle (n lam) (S lam) (L lam) (Salt lam) → ByteArray)
  (mkCtx : (lam : ℕ) → Salt lam → Ctx lam) (initAcc : (lam : ℕ) → Ctx lam → S lam)

variable (m) in
/-- The asymptotic hiding game of the sealed scheme family: the advantage of an adversary family
`A` at `lam` is the hiding advantage of `A lam` against `sealScheme` with `sealDEM` at the sizes,
types and data of `lam`, with the message length as leakage. -/
@[expose]
noncomputable def hidingSecurityGame :
    SecurityGame (HidingAdversaryFamily n S L Salt Ctx N K) where
  advantage A lam := hidingAdvantage (sealScheme (n lam) (m lam) (mkCtx lam) (initAcc lam) (N lam)
    (K lam)) (sealDEM (prf lam) (codec lam) (encodePuzzle lam)) plaintextLength (A lam)

variable (m) in
/-- The reduction of the asymptotic hiding theorem: the family of PRF distinguishers
`hidingDistinguisher` of the members of `A`, the member at `lam` against `2 * qEnc lam` instances.
-/
@[expose]
def hidingReduction (qEnc : ℕ → ℕ) (A : HidingAdversaryFamily n S L Salt Ctx N K)
    (lam : ℕ) : PRFAdversary (Fin (2 * qEnc lam) × ByteArray) (Bytes 32) :=
  hidingDistinguisher (m lam) (codec lam) (encodePuzzle lam) (qEnc lam) (mkCtx lam) (initAcc lam)
    (A lam)

/-! ## Asymptotic hiding -/

variable [∀ lam, Finite (Ctx lam)] [∀ lam, Fintype (S lam)] [∀ lam, Fintype (L lam)]
  [∀ lam, Fintype (N lam)]

/-- **The hiding theorem at each parameter.** For a family within the budgets at every `lam`, its
advantage in `hidingSecurityGame` at `lam` is at most twice the advantage of its reduction in the
multi-key PRF game plus twice the statistical terms: `hidingAdvantage_sealScheme_le` at `lam`. -/
theorem hidingSecurityGame_advantage_le [∀ lam, Fintype (Salt lam)]
    (hprf : ∀ lam, (prf lam).UniformKey) (hctx : ∀ lam, Function.Injective (mkCtx lam))
    {Qpre Qon qEnc : ℕ → ℕ}
    {A : HidingAdversaryFamily n S L Salt Ctx N K}
    (hA : ∀ lam, (A lam).IsQueryBound (Qpre lam) (keyRound (n lam) (m lam) - 1, Qon lam) ∧
      (A lam).MakesAtMostQueries (qEnc lam)) (lam : ℕ) :
    (hidingSecurityGame m prf codec encodePuzzle mkCtx initAcc).advantage A lam ≤
      2 * (prfSecurityGame fun lam => (prf lam).multiKey (Fin (2 * qEnc lam))).advantage
          (hidingReduction m codec encodePuzzle mkCtx initAcc qEnc A) lam +
        2 * hidingStatisticalBound n m S L Salt N Qpre Qon qEnc lam :=
  (hidingAdvantage_sealScheme_le (prf lam) (codec lam) (encodePuzzle lam) (hprf lam) (mkCtx lam)
    (initAcc lam) (hctx lam) (hA lam).1 (hA lam).2).trans_eq (by
      rw [mul_add, add_comm]
      rfl)

/-- **Asymptotic hiding (`thm:hiding` for parameter families).** Let the statistical terms be
negligible along the family, and let the PRF family with `2 * qEnc lam` independent keys at `lam`
be secure against a class `isPPT'` of distinguisher families into which the reduction
`hidingReduction` maps the adversary class (`hreduce`, the efficiency obligation of the
reduction). Then every family in `hidingAdversaryClass m Qpre Qon qEnc isEff` has negligible
advantage in `hidingSecurityGame`.

The class bounds the rounds of the online phase by `keyRound (n lam) (m lam) - 1`, which
efficiency does not imply. The key count `2 * qEnc lam` of the PRF assumption is fixed by the
class's challenge budget, not chosen by the adversary, so the assumption is security of one PRF
family. -/
theorem hidingSecurityGame_secureAgainst [∀ lam, Fintype (Salt lam)]
    (hprf : ∀ lam, (prf lam).UniformKey) (hctx : ∀ lam, Function.Injective (mkCtx lam))
    {Qpre Qon qEnc : ℕ → ℕ}
    {isEff : HidingAdversaryFamily n S L Salt Ctx N K → Prop}
    {isPPT' : ((lam : ℕ) → PRFAdversary (Fin (2 * qEnc lam) × ByteArray) (Bytes 32)) → Prop}
    (hstat : negligible (hidingStatisticalBound n m S L Salt N Qpre Qon qEnc))
    (hreduce : ∀ A, hidingAdversaryClass m Qpre Qon qEnc isEff A →
      isPPT' (hidingReduction m codec encodePuzzle mkCtx initAcc qEnc A))
    (hsecure : (prfSecurityGame fun lam => (prf lam).multiKey (Fin (2 * qEnc lam))).secureAgainst
      isPPT') :
    (hidingSecurityGame m prf codec encodePuzzle mkCtx initAcc).secureAgainst
      (hidingAdversaryClass m Qpre Qon qEnc isEff) :=
  SecurityGame.secureAgainst_of_close_poly_reduction (loss := Polynomial.C 2)
    (negligible_const_mul hstat ENNReal.ofNat_ne_top) hreduce
    (fun _ hA lam => by
      simpa only [Polynomial.eval_C, Nat.cast_ofNat] using
        hidingSecurityGame_advantage_le prf codec encodePuzzle mkCtx initAcc hprf hctx hA.2 lam)
    hsecure

/-- **Asymptotic hiding from growth conditions.** If `|S lam|`, `|L lam|` and `|N lam|` grow
superpolynomially, salts exist, and the budgets and the puzzle work `solvePoints` are bounded by a
polynomial in `lam`, the statistical terms are negligible (`negligible_hidingStatisticalBound`),
and `hidingSecurityGame_secureAgainst` applies. -/
theorem hidingSecurityGame_secureAgainst_of_card [∀ lam, Nonempty (Salt lam)]
    (hprf : ∀ lam, (prf lam).UniformKey) (hctx : ∀ lam, Function.Injective (mkCtx lam))
    (hS : negligible fun lam => (Fintype.card (S lam) : ℝ≥0∞)⁻¹)
    (hL : negligible fun lam => (Fintype.card (L lam) : ℝ≥0∞)⁻¹)
    (hN : negligible fun lam => (Fintype.card (N lam) : ℝ≥0∞)⁻¹)
    {Qpre Qon qEnc : ℕ → ℕ} {p : Polynomial ℕ}
    (hP : ∀ lam, solvePoints (n lam) (m lam) ≤ p.eval lam) (hQpre : ∀ lam, Qpre lam ≤ p.eval lam)
    (hQon : ∀ lam, Qon lam ≤ p.eval lam) (hqEnc : ∀ lam, qEnc lam ≤ p.eval lam)
    {isEff : HidingAdversaryFamily n S L Salt Ctx N K → Prop}
    {isPPT' : ((lam : ℕ) → PRFAdversary (Fin (2 * qEnc lam) × ByteArray) (Bytes 32)) → Prop}
    (hreduce : ∀ A, hidingAdversaryClass m Qpre Qon qEnc isEff A →
      isPPT' (hidingReduction m codec encodePuzzle mkCtx initAcc qEnc A))
    (hsecure : (prfSecurityGame fun lam => (prf lam).multiKey (Fin (2 * qEnc lam))).secureAgainst
      isPPT') :
    (hidingSecurityGame m prf codec encodePuzzle mkCtx initAcc).secureAgainst
      (hidingAdversaryClass m Qpre Qon qEnc isEff) :=
  let _ := fun lam => Fintype.ofFinite (Salt lam)
  hidingSecurityGame_secureAgainst prf codec encodePuzzle mkCtx initAcc hprf hctx
    (negligible_hidingStatisticalBound hS hL hN hP hQpre hQon hqEnc) hreduce hsecure

end Game

end PointerChainPuzzle
