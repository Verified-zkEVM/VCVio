/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.CoinFold
import ToMathlib.Data.BitVec

/-!
# Practical Polynomial-Time Constructions

Reusable polynomial-time facts built on the coin-fold combinator and the pure-function
witness constructor, at pinned canonical boundaries:

* **Randomized generation** — `uniformBitVec n` samples a uniform `BitVec n` by flipping
  `n` coins (a `coinFoldProg` that overwrites one bit per round).
  `isPolyTime_uniformBitVec` certifies it in the honest hypothesis form: the fold's
  accumulator is `BitVec n`, of cardinality `2 ^ n`, so the finite-table witnesses of
  `isPolyTime_coinFold` would exceed every polynomial advice bound; the caller supplies
  genuine uniform machine families for the step functions, pending a base-machine
  library.
* **Deterministic computation** — `isPolyTime_pure_ofFintype` certifies any function on
  a per-parameter finite input type of *polynomially bounded cardinality* as polynomial
  time via finite tables. There is deliberately no hypothesis-free bitvector-function
  version: "every function `BitVec (a n) → BitVec (b n)` is polynomial time" is exactly
  the unbounded-advice collapse the advice bound exists to prevent — a genuine `f`
  needs a genuine machine, supplied through `OracleComp.isPolyTime_pure_of_witnesses`.
-/

open OracleSpec Computability

namespace OracleComp

/-! ## The single coin flip -/

/-- The state representation of the one-round coin fold: a one-bit round counter and a
Boolean accumulator. -/
noncomputable def coinFlipState : StrEncFam (fun _ => Fin 2 × Bool) :=
  ((BitEncFam.fin (fun _ => 1) (.C 1) (fun _ => by simp)).pair
    (BitEncFam.const Bool)).toStrEncFam

/-- A single coin flip is polynomial time at the canonical boundaries: the one-round
bounded coin fold with a Boolean accumulator, witnessed end to end by finite tables. -/
theorem isPolyTime_coin :
    OracleComp.IsPolyTime (BoundaryData.coin BitEncFam.unit BitEncFam.bool)
      (fun _ (_ : Unit) => OracleComp.coin) := by
  refine OracleComp.IsPolyTime.congr (oa := fun n (_ : Unit) =>
      coinFoldProg (fun (_ : Bool) _ b => b) id 1 false) (fun n _ => ?_)
    (isPolyTime_coinFold (fun _ (_ : Bool) _ b => b) (fun _ => id) (fun _ => false)
      (fun _ => 1) (.C 1) (fun _ => by simp) coinFlipState BitEncFam.bool
      (.C 2) (fun _ => by simp))
  rfl

/-! ## Uniform `BitVec` generation -/

/-- Sample a uniform `BitVec n` by flipping `n` coins, folding the `r`-th answer into bit
`r` of the accumulator. This is the bounded coin fold with `step = overwriteBit` and the
identity read-out. -/
def uniformBitVec (n : ℕ) : OracleComp coinSpec (BitVec n) :=
  coinFoldProg (fun (acc : BitVec n) r b => acc.overwriteBit r b) id n 0

/-- The counter/accumulator state representation of the `uniformBitVec` fold: binary
counter appended to the raw accumulator bits, total width `2 * n`. -/
noncomputable def uniformBitVecState : StrEncFam (fun n => Fin (n + 1) × BitVec n) :=
  ((BitEncFam.fin id .X fun n => (Polynomial.eval_X (x := n)).ge).pair
    BitEncFam.bitVecX).toStrEncFam

/-- **Generating a uniform `BitVec n` is polynomial time, given machine families for the
fold's step functions.** The accumulator is `BitVec n` — cardinality `2 ^ n` — so the
generic table witnesses of `isPolyTime_coinFold` are unavailable (they would exceed
every polynomial advice bound); uniform machine families for initialization, query
selection, the bit-overwrite update, and the readout must be supplied. Discharging them
generically is the base-machine library deferred in
`ToMathlib.Computability.PolyTimeTM`. -/
theorem isPolyTime_uniformBitVec
    (initF : EncPolyTimeFam BitEncFam.unit.enc uniformBitVecState.enc
      (fun n => (coinFoldMachine (fun (acc : BitVec n) r b => acc.overwriteBit r b)
        id n 0).init))
    (exposeF : EncPolyTimeFam uniformBitVecState.enc InterfaceBitEnc.coin.encQuery.enc
      (fun n => (coinFoldMachine (fun (acc : BitVec n) r b => acc.overwriteBit r b)
        id n 0).expose))
    (updateF : EncPolyTimeFam
      (uniformBitVecState.pairVar InterfaceBitEnc.coin.encAns).enc uniformBitVecState.enc
      (fun n => (coinFoldMachine (fun (acc : BitVec n) r b => acc.overwriteBit r b)
        id n 0).updateFlat))
    (outputF : EncPolyTimeFam uniformBitVecState.enc (BitEncFam.bitVecX.option).enc
      (fun n => (coinFoldMachine (fun (acc : BitVec n) r b => acc.overwriteBit r b)
        id n 0).output)) :
    OracleComp.IsPolyTime (BoundaryData.coin BitEncFam.unit BitEncFam.bitVecX)
      (fun n (_ : Unit) => uniformBitVec n) :=
  isPolyTime_coinFold_of_witnesses
    (fun n (acc : BitVec n) r b => acc.overwriteBit r b) (fun _ => id) (fun _ => 0)
    id Polynomial.X (fun n => by simp)
    uniformBitVecState BitEncFam.bitVecX initF exposeF updateF outputF

/-! ## Deterministic functions on finite inputs -/

/-- **Any deterministic function on a per-parameter finite input type of polynomially
bounded cardinality is polynomial time.** An ergonomic wrapper over
`isPolyTime_pure_of_witnesses`: the machine is `ofPureFn (f n)` (state = the input,
output `= some ∘ f`), so the query-selection witness is a constant machine and the
update (projection) and output (`some ∘ f`) witnesses are finite tables — within the
advice budget exactly because the input cardinality (`cardIn`) and the tagged-answer
cardinality (`cardIface`) are polynomially bounded. -/
theorem isPolyTime_pure_ofFintype {ι : ℕ → Type} [∀ n, DecidableEq (ι n)]
    [∀ n, Inhabited (ι n)] [∀ n, Finite (ι n)]
    {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)} [∀ n, (spec n).Fintype]
    {α β : ℕ → Type} [∀ n, Finite (α n)] (bd : BoundaryData spec α β)
    (f : (n : ℕ) → α n → β n)
    (cardIn : Polynomial ℕ) (hcardIn : ∀ n, Nat.card (α n) ≤ cardIn.eval n)
    (cardIface : Polynomial ℕ)
    (hcardIface : ∀ n, Nat.card ((t : ι n) × (spec n).Range t) ≤ cardIface.eval n) :
    OracleComp.IsPolyTime bd fun n x => (pure (f n x) : OracleComp (spec n) (β n)) := by
  letI : ∀ n, Fintype (ι n) := fun n => Fintype.ofFinite (ι n)
  letI : ∀ n, Fintype (α n) := fun n => Fintype.ofFinite (α n)
  have hcardIn' : ∀ n, Fintype.card (α n) ≤ cardIn.eval n := fun n => by
    simpa [Nat.card_eq_fintype_card] using hcardIn n
  refine OracleComp.isPolyTime_pure_of_witnesses bd f
    (.const bd.eIn.enc (fun n => (default : ι n)) bd.eIface.encQuery.widBound
      (fun n => (bd.eIface.encQuery.len_eq n _).le.trans (bd.eIface.encQuery.wid_le n)))
    (.ofFintype (bd.eIn.toStrEncFam.pairVar bd.eIface.encAns).enc_injective
      (fun _ => Prod.fst)
      (cardIn * cardIface)
      (fun n => by
        rw [Fintype.card_prod]
        simp only [Polynomial.eval_mul]
        exact Nat.mul_le_mul (hcardIn' n)
          (by simpa [Nat.card_eq_fintype_card] using hcardIface n))
      (bd.eIn.widBound + bd.eIface.encAns.widBound)
      (fun n p => by
        have h1 := (bd.eIn.len_eq n p.1).le.trans (bd.eIn.wid_le n)
        have h2 := (bd.eIface.encAns.len_eq n p.2).le.trans (bd.eIface.encAns.wid_le n)
        simp only [StrEncFam.pairVar_enc, List.length_append, BitEncFam.toStrEncFam_enc,
          Polynomial.eval_add]
        omega)
      bd.eIn.widBound
      (fun n p => (bd.eIn.len_eq n _).le.trans (bd.eIn.wid_le n)))
    (.ofFintype bd.eIn.enc_injective (fun n x => some (f n x))
      cardIn hcardIn'
      bd.eIn.widBound (fun n x => (bd.eIn.len_eq n x).le.trans (bd.eIn.wid_le n))
      (bd.eOut.option).widBound
      (fun n x => ((bd.eOut.option).len_eq n _).le.trans ((bd.eOut.option).wid_le n)))

end OracleComp
