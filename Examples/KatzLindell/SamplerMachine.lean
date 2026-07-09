/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.CoinFold
import ToMathlib.Data.BitVec

/-!
# The Reduction Sampler and Its Polynomial-Time Witness

The choose phase of the Katz–Lindell Claim 3.11 reduction samples two `n`-bit messages,
forced to differ in bit `i`, by filling `2 * n` fair coins into an accumulator coin by
coin (`fillBits` / `chooseProg`). This file supplies the polynomial-time witness
`isPolyTime_chooseProg`, so the reduction adversary built from it in
`Examples.KatzLindell.SingleBit` is probabilistic polynomial time.

The witness is a one-line application of the generic bounded-coin-fold combinator
`OracleComp.isPolyTime_coinFold`: `chooseProg` is exactly a coin fold that overwrites bit
`s.1 - 1` of a `BitVec (2 * n)` accumulator each round and reads out the two forced
messages, so all that remains is the *binary* state/output encodings
(`Computability.finEncodingBitVec` — the unary encoding of a `BitVec (2 * n)` would be
exponential) and their linear length bounds.
-/

open OracleSpec OracleComp Computability

namespace KatzLindell

/-! ## The coin-fill sampler -/

/-- Sample `r` fresh coins into bits `r-1, …, 0` of the accumulator. -/
def fillBits {w : ℕ} : ℕ → BitVec w → OracleComp coinSpec (BitVec w)
  | 0, acc => pure acc
  | r + 1, acc => OracleComp.queryBind () fun b => fillBits r (acc.overwriteBit r b)

/-- `fillBits r acc` makes at most `r` queries. -/
theorem isTotalQueryBound_fillBits {w : ℕ} (r : ℕ) (acc : BitVec w) :
    IsTotalQueryBound (fillBits r acc) r := by
  induction r generalizing acc with
  | zero => trivial
  | succ r ih => exact ⟨Nat.succ_pos r, fun b => ih (acc.overwriteBit r b)⟩

/-- The choose phase of the Katz–Lindell Claim 3.11 reduction: fill `2 * n` uniform
coins, split them into two `n`-bit messages, and force bit `i` to `0` in the first and
`1` in the second. -/
def chooseProg (i n : ℕ) : OracleComp coinSpec (BitVec n × BitVec n × Unit) := do
  let w ← fillBits (2 * n) (0 : BitVec (2 * n))
  pure ((w.extractLsb' 0 n).overwriteBit i false, (w.extractLsb' n n).overwriteBit i true, ())

/-- The coin-fill loop with a read-out is exactly the bounded coin fold that overwrites bit
`r` each round: `fillBits` is `OracleComp.coinFoldProg` with `step = overwriteBit`. -/
theorem fillBits_bind_pure_eq_coinFoldProg {w : ℕ} {β : Type} (readout : BitVec w → β)
    (k : ℕ) (acc : BitVec w) :
    (fillBits k acc >>= fun v => pure (readout v))
      = OracleComp.coinFoldProg (fun a r b => BitVec.overwriteBit r b a) readout k acc := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih =>
    rw [OracleComp.coinFoldProg_succ]
    change (OracleComp.queryBind () (fun b => fillBits k (acc.overwriteBit k b))) >>=
        (fun v => pure (readout v)) = _
    exact congrArg (OracleComp.queryBind ()) (funext fun b => ih (acc.overwriteBit k b))

/-! ## Polynomial time of the sampler -/

/-- Boolified length of the paired counter/accumulator state is linear: the binary
`finEncodingBitVec` keeps the `BitVec (2 * n)` accumulator at `3 * (2 * n)`, not `2 ^ (2 * n)`. -/
private theorem encState_len_le (n : ℕ) (s : Fin (2 * n + 1) × BitVec (2 * n)) :
    ((finEncodingPair (finEncodingOfFinEnum (Fin (2 * n + 1)))
      (finEncodingBitVec (2 * n))).boolify s).length ≤ 16 * n := by
  have hlen1 : ((finEncodingOfFinEnum (Fin (2 * n + 1))).encode s.1).length ≤ 2 * n := by
    simp only [finEncodingOfFinEnum, List.length_replicate]
    have h := (FinEnum.equiv s.1).isLt
    have hc : FinEnum.card (Fin (2 * n + 1)) = 2 * n + 1 := by simp [FinEnum.card_eq_fintypeCard]
    omega
  rw [length_boolify_finEncodingPair, length_encode_finEncodingBitVec,
    show Fintype.card (finEncodingOfFinEnum (Fin (2 * n + 1))).Γ = 1 from rfl,
    show Fintype.card (finEncodingBitVec (2 * n)).Γ = 2 from rfl]
  omega

/-- Boolified length of the optional two-message output is linear. -/
private theorem encOption_len_le (n : ℕ) (x : Option (BitVec n × BitVec n × Unit)) :
    ((finEncodingOption (finEncodingPair (finEncodingBitVec n)
        (finEncodingPair (finEncodingBitVec n) (finEncodingOfFinEnum Unit)))).boolify x).length
      ≤ 14 * n + 7 := by
  have hlen : ((finEncodingOption (finEncodingPair (finEncodingBitVec n)
      (finEncodingPair (finEncodingBitVec n) (finEncodingOfFinEnum Unit)))).encode x).length
      ≤ 2 * n + 1 := by
    cases x with
    | none => simp [finEncodingOption]
    | some v =>
      simp only [finEncodingOption, List.length_cons, List.length_map]
      rw [length_encode_finEncodingPair, length_encode_finEncodingPair,
        length_encode_finEncodingBitVec, length_encode_finEncodingBitVec]
      simp only [finEncodingOfFinEnum, List.length_replicate]
      have hu := (FinEnum.equiv v.2.2).isLt
      have hc : FinEnum.card Unit = 1 := rfl
      omega
  rw [length_boolify_finEncodingOption,
    show Fintype.card (finEncodingPair (finEncodingBitVec n)
      (finEncodingPair (finEncodingBitVec n) (finEncodingOfFinEnum Unit))).Γ = 5 from rfl]
  omega

/-- **The choose phase is polynomial time.** Filling `2 * n` coins and reading out the two
forced messages is polynomial time, witnessed end to end by concrete Turing machines via
the bounded-coin-fold combinator. This is the choose-phase half of "the reduction adversary
is PPT since the predictor is". -/
theorem isPolyTime_chooseProg (i : ℕ) :
    OracleComp.IsPolyTime fun n (_ : Unit) => chooseProg i n := by
  have hstate : ∀ n (s : Fin (2 * n + 1) × BitVec (2 * n)),
      ((finEncodingPair (finEncodingOfFinEnum (Fin (2 * n + 1)))
          (finEncodingBitVec (2 * n))).boolify s).length
        ≤ (Polynomial.C 16 * Polynomial.X).eval n := fun n s => by
    simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using encState_len_le n s
  have hout : ∀ n (x : Option (BitVec n × BitVec n × Unit)),
      ((finEncodingOption (finEncodingPair (finEncodingBitVec n)
          (finEncodingPair (finEncodingBitVec n) (finEncodingOfFinEnum Unit)))).boolify x).length
        ≤ (Polynomial.C 14 * Polynomial.X + Polynomial.C 7).eval n := fun n x => by
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      using encOption_len_le n x
  refine OracleComp.IsPolyTime.congr (fun n _ =>
    (fillBits_bind_pure_eq_coinFoldProg _ (2 * n) 0).symm)
    (OracleComp.isPolyTime_coinFold
      (fun n (acc : BitVec (2 * n)) r b => acc.overwriteBit r b)
      (fun n w => ((w.extractLsb' 0 n).overwriteBit i false,
        (w.extractLsb' n n).overwriteBit i true, ()))
      (fun _ => 0) (fun n => 2 * n) (Polynomial.C 2 * Polynomial.X)
      (fun n => by simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X])
      (fun n => finEncodingPair (finEncodingOfFinEnum (Fin (2 * n + 1)))
        (finEncodingBitVec (2 * n)))
      (Polynomial.C 16 * Polynomial.X) hstate
      (fun n => finEncodingPair (finEncodingBitVec n)
        (finEncodingPair (finEncodingBitVec n) (finEncodingOfFinEnum Unit)))
      (Polynomial.C 14 * Polynomial.X + Polynomial.C 7) hout)

end KatzLindell
