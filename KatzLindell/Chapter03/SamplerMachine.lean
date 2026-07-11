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
coin (`fillBits` / `chooseProg`). This file supplies its polynomial-time story in the
honest hypothesis form `isPolyTime_chooseProg`, feeding the reduction adversary of
`KatzLindell.Chapter03.SingleBit`.

`chooseProg` is exactly a bounded coin fold (`fillBits_bind_pure_eq_coinFoldProg`), and
the binary counter/accumulator state representation `chooseState` keeps the encoded
state linear. But the accumulator type itself has cardinality `4 ^ n`, so the
finite-table machine witnesses of `OracleComp.isPolyTime_coinFold` would carry
exponential *description size* — exactly the unbounded-advice collapse the machine
model's advice bound forbids. The theorem therefore routes through
`OracleComp.isPolyTime_coinFold_of_witnesses`, discharging all coalgebraic content
while taking uniform machine families for the four step functions as hypotheses,
pending the base-machine library deferred in `ToMathlib.Computability.PolyTimeTM`.
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

/-- The fold machine of the choose phase: overwrite bit `r` each round for `2 * n` rounds,
read out the two forced messages. -/
def chooseMachine (i n : ℕ) : OracleMachine coinSpec Unit (BitVec n × BitVec n × Unit) :=
  OracleComp.coinFoldMachine (fun (acc : BitVec (2 * n)) r b => acc.overwriteBit r b)
    (fun w => ((w.extractLsb' 0 n).overwriteBit i false,
      (w.extractLsb' n n).overwriteBit i true, ())) (2 * n) 0

/-- The counter/accumulator state representation of the choose-phase fold: binary
counter appended to the raw accumulator bits. -/
noncomputable def chooseState : StrEncFam (fun n => Fin (2 * n + 1) × BitVec (2 * n)) :=
  ((BitEncFam.fin (fun n => 2 * n) (.C 2 * .X)
      (fun n => by simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X])).pair
    (BitEncFam.bitVec (fun n => 2 * n) (.C 2 * .X)
      (fun n => by simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]))).toStrEncFam

/-- The canonical output boundary of the choose phase: two messages and a unit. -/
noncomputable def chooseOut : BitEncFam (fun n => BitVec n × BitVec n × Unit) :=
  BitEncFam.bitVecX.pair (BitEncFam.bitVecX.pair BitEncFam.unit)

/-- **The choose phase is polynomial time, given machine families for the fold's step
functions.** The fold's accumulator is `BitVec (2 * n)` — cardinality `4 ^ n` — so the
generic table witnesses of `OracleComp.isPolyTime_coinFold` would exceed every
polynomial advice bound (see the `## Model` notes of
`VCVio.OracleComp.Coinductive.PolyTime`); uniform machine families for initialization,
query selection, the bit-overwrite update, and the two-message readout must be
supplied, pending the base-machine library deferred in
`ToMathlib.Computability.PolyTimeTM`. The coalgebraic content (implements, stability,
the state-size invariant) is discharged here. -/
theorem isPolyTime_chooseProg (i : ℕ)
    (initF : EncPolyTimeFam BitEncFam.unit.enc chooseState.enc
      (fun n => (chooseMachine i n).init))
    (exposeF : EncPolyTimeFam chooseState.enc InterfaceBitEnc.coin.encQuery.enc
      (fun n => (chooseMachine i n).expose))
    (updateF : EncPolyTimeFam (chooseState.pairVar InterfaceBitEnc.coin.encAns).enc
      chooseState.enc (fun n => (chooseMachine i n).updateFlat))
    (outputF : EncPolyTimeFam chooseState.enc (chooseOut.option).enc
      (fun n => (chooseMachine i n).output)) :
    OracleComp.IsPolyTime (BoundaryData.coin BitEncFam.unit chooseOut)
      (fun n (_ : Unit) => chooseProg i n) :=
  OracleComp.IsPolyTime.congr (fun n _ =>
    (fillBits_bind_pure_eq_coinFoldProg _ (2 * n) 0).symm)
    (OracleComp.isPolyTime_coinFold_of_witnesses
      (fun n (acc : BitVec (2 * n)) r b => acc.overwriteBit r b)
      (fun n w => ((w.extractLsb' 0 n).overwriteBit i false,
        (w.extractLsb' n n).overwriteBit i true, ()))
      (fun _ => 0) (fun n => 2 * n) (Polynomial.C 2 * Polynomial.X)
      (fun n => by simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X])
      chooseState chooseOut initF exposeF updateF outputF)

end KatzLindell
