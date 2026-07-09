/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.CoinFold
import VCVio.OracleComp.Coinductive.PolyTimeClosure
import Examples.DynamicalSystems.Basic

/-!
# The n-Flip XOR Adversary via the Bounded Coin Fold

`xorFlips n` flips the coin `n` times, XOR-accumulating the answers in finite state, and
reports the parity after `n` rounds — the paradigmatic bounded query fold. This file gets
its complete polynomial-time story from the reusable combinator
`OracleComp.isPolyTime_coinFold`, with no hand-built machine:

* `xorProg` — the accumulator program family, exactly `OracleComp.coinFoldProg` with
  `step = xor` and `readout = id` (`xorProg_eq_coinFoldProg`).
* `xorFoldAdversary` / `isPolyTime_xorProg` — the bundled `PolyTimeAdversary` and the
  hypothesis-free `OracleComp.IsPolyTime` instance, obtained from the combinator by
  supplying the (unary) `Fin (n+1) × Bool` state encoding and its linear length bounds.
* Game wiring — `xorGame` demonstrates the advantage transfer
  `OneShotGame.advantage_toPolyGame_eq` on the concrete bundle, and `zeroGame` yields an
  unconditional `SecurityGame.secureAgainstPolyTime` instance.
-/

open OracleSpec OracleComp Computability

namespace DynSystemExamples

/-! ## The program family -/

/-- Flip the coin `r` more times, XOR-accumulating into `acc`. -/
def xorProg : ℕ → Bool → OracleComp coinSpec Bool
  | 0, acc => pure acc
  | r + 1, acc => OracleComp.queryBind () fun b => xorProg r (xor acc b)

@[simp] theorem xorProg_zero (acc : Bool) : xorProg 0 acc = pure acc := rfl

@[simp] theorem xorProg_succ (r : ℕ) (acc : Bool) :
    xorProg (r + 1) acc = OracleComp.queryBind () fun b => xorProg r (xor acc b) := rfl

/-- `xorProg r acc` makes at most `r` queries. -/
theorem isTotalQueryBound_xorProg (r : ℕ) (acc : Bool) :
    IsTotalQueryBound (xorProg r acc) r := by
  induction r generalizing acc with
  | zero => trivial
  | succ r ih => exact ⟨Nat.succ_pos r, fun b => ih (xor acc b)⟩

/-- `xorProg n false` is the bounded coin fold with `step = xor` and identity read-out. -/
theorem xorProg_eq_coinFoldProg (k : ℕ) (acc : Bool) :
    xorProg k acc = OracleComp.coinFoldProg (fun a _ b => xor a b) id k acc := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih =>
    rw [xorProg_succ, OracleComp.coinFoldProg_succ]
    exact congrArg (OracleComp.queryBind ()) (funext fun b => ih (xor acc b))

/-! ## Encoded-size bounds

The state `Fin (n+1) × Bool` is encoded with the unary `finEncodingOfFinEnum` (the `Bool`
accumulator has card `2`, so the whole state stays small), giving linear boolified lengths
via `Computability.length_boolify_finEncodingOfFinEnum`. -/

private theorem xorEncState_length_le (n : ℕ) (s : Fin (n + 1) × Bool) :
    ((finEncodingOfFinEnum (Fin (n + 1) × Bool)).boolify s).length ≤ 4 * n + 4 := by
  refine (length_boolify_finEncodingOfFinEnum s).trans ?_
  have hcard : ∀ I : Fintype (Fin (n + 1) × Bool), @Fintype.card _ I = (n + 1) * 2 :=
    fun I => (@Fintype.card_congr _ _ I (instFintypeProd _ _) (Equiv.refl _)).trans (by simp)
  rw [hcard]
  omega

private theorem xorEncOption_length_le (x : Option Bool) :
    ((finEncodingOption (finEncodingOfFinEnum Bool)).boolify x).length ≤ 6 := by
  have hlen : ((finEncodingOption (finEncodingOfFinEnum Bool)).encode x).length ≤ 2 := by
    cases x with
    | none => simp [finEncodingOption]
    | some b =>
      simp only [finEncodingOption, List.length_cons, List.length_map, finEncodingOfFinEnum,
        List.length_replicate]
      have hb := (FinEnum.equiv b).isLt
      have hc : FinEnum.card Bool = 2 := rfl
      omega
  rw [length_boolify_finEncodingOption,
    show Fintype.card (finEncodingOfFinEnum Bool).Γ = 1 from rfl]
  omega

/-! ## The concrete polynomial-time adversary -/

/-- The n-flip XOR adversary, from the bounded coin fold: state `Fin (n+1) × Bool`, round
bound `n`, unary state encoding, linear size and step-time polynomials. -/
noncomputable def xorFoldAdversary :
    PolyTimeAdversary (fun _ => coinSpec) (fun _ => Unit) (fun _ => Bool) :=
  OracleComp.coinFoldAdversary (fun _ acc _ b => xor acc b) (fun _ a => a) (fun _ => false)
    id Polynomial.X (fun n => by simp)
    (fun n => finEncodingOfFinEnum (Fin (n + 1) × Bool))
    (Polynomial.C 4 * Polynomial.X + Polynomial.C 4)
    (fun n s => by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        using xorEncState_length_le n s)
    (fun _ => finEncodingOfFinEnum Bool) (Polynomial.C 6)
    (fun _ x => by simpa only [Polynomial.eval_C] using xorEncOption_length_le x)

/-- The bundled XOR adversary implements the `n`-flip program family. -/
theorem xorFoldAdversary_implements :
    xorFoldAdversary.Implements fun n (_ : Unit) => xorProg n false := by
  rw [show (fun n (_ : Unit) => xorProg n false)
      = fun n (_ : Unit) => OracleComp.coinFoldProg (fun a _ b => xor a b) id n false from
    funext fun n => funext fun _ => xorProg_eq_coinFoldProg n false]
  exact OracleComp.coinFoldAdversary_implements (fun _ acc _ b => xor acc b) (fun _ a => a)
    (fun _ => false) id Polynomial.X (fun n => by simp)
    (fun n => finEncodingOfFinEnum (Fin (n + 1) × Bool))
    (Polynomial.C 4 * Polynomial.X + Polynomial.C 4)
    (fun n s => by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        using xorEncState_length_le n s)
    (fun _ => finEncodingOfFinEnum Bool) (Polynomial.C 6)
    (fun _ x => by simpa only [Polynomial.eval_C] using xorEncOption_length_le x)

/-- **A hypothesis-free polynomial-time instance**: flipping the coin `n` times and
reporting the parity is polynomial time, witnessed end to end by concrete Turing machines,
now as a one-line application of the bounded-coin-fold combinator. -/
theorem isPolyTime_xorProg :
    OracleComp.IsPolyTime fun n (_ : Unit) => xorProg n false :=
  OracleComp.IsPolyTime.congr (fun n _ => (xorProg_eq_coinFoldProg n false).symm)
    (OracleComp.isPolyTime_coinFold (fun _ acc _ b => xor acc b) (fun _ a => a) (fun _ => false)
      id Polynomial.X (fun n => by simp)
      (fun n => finEncodingOfFinEnum (Fin (n + 1) × Bool))
      (Polynomial.C 4 * Polynomial.X + Polynomial.C 4)
      (fun n s => by
        simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
          using xorEncState_length_le n s)
      (fun _ => finEncodingOfFinEnum Bool) (Polynomial.C 6)
      (fun _ x => by simpa only [Polynomial.eval_C] using xorEncOption_length_le x))

/-- Polynomially many queries follow by the generic bridge. -/
example : Nonempty (OracleComp.PolyQueries fun n (_ : Unit) => xorProg n false) :=
  isPolyTime_xorProg.polyQueries

/-- Post-composing a pure map onto the fold is polynomial time, via the output-map closure
`OracleComp.IsPolyTime.map_of_adversary` on the exposed finite-state bundle: negating the
reported parity stays polynomial time. -/
noncomputable example :
    OracleComp.IsPolyTime fun n (_ : Unit) => (! ·) <$> xorProg n false :=
  letI : ∀ n, Fintype (xorFoldAdversary.M n).State := fun n =>
    inferInstanceAs (Fintype (Fin (n + 1) × Bool))
  OracleComp.IsPolyTime.map_of_adversary xorFoldAdversary (fun _ b => !b)
    (fun _ => finEncodingOfFinEnum Bool) (Polynomial.C 6)
    (fun n s => by simpa only [Polynomial.eval_C] using xorEncOption_length_le _)
    xorFoldAdversary_implements fun n _ => by
      rw [show xorFoldAdversary.steps = Polynomial.X from rfl, Polynomial.eval_X]
      exact isTotalQueryBound_xorProg n false

/-! ## Game wiring

`xorGame` is deliberately winnable — it exists to demonstrate the advantage transfer
between the machine and program presentations of the concrete adversary. `zeroGame`
is unwinnable, giving an unconditional `secureAgainstPolyTime` instance. -/

/-- A fair coin as a randomized oracle. -/
noncomputable def fairCoin : ProbHandler coinSpec :=
  fun _ => liftM (PMF.uniformOfFintype Bool)

/-- Guess-the-parity game: run the adversary against a fair coin, win on a report of
`true`. -/
noncomputable def xorGame :
    OneShotGame (fun _ => coinSpec) (fun _ => Unit) (fun _ => Bool) where
  oracle _ := fairCoin
  gen _ := pure ()
  score _ _ b := pure (b.getD false)

/-- Advantage transfer, concretely: the machine-level advantage of the bundled XOR
adversary is exactly the program-level advantage of `xorProg`. -/
example (n : ℕ) :
    xorGame.toPolyGame.advantage xorFoldAdversary n =
      xorGame.toProgGame.advantage (fun n _ => xorProg n false) n :=
  xorGame.advantage_toPolyGame_eq xorFoldAdversary_implements n

/-- A game nobody wins: the score is constantly `false`. -/
noncomputable def zeroGame :
    OneShotGame (fun _ => coinSpec) (fun _ => Unit) (fun _ => Bool) where
  oracle _ := fairCoin
  gen _ := pure ()
  score _ _ _ := pure false

theorem zeroGame_advantage_toPolyGame
    (D : PolyTimeAdversary (fun _ => coinSpec) (fun _ => Unit) (fun _ => Bool))
    (n : ℕ) : zeroGame.toPolyGame.advantage D n = 0 := by
  have h : zeroGame.toPolyGame.advantage D n =
      (D.exec n fairCoin () >>= fun _ => (pure false : SPMF Bool)) true := by
    simp only [OneShotGame.toPolyGame, zeroGame, pure_bind]
  rw [h, SPMF.bind_apply_eq_tsum]
  simp [SPMF.pure_apply]

/-- An unconditional end-to-end security instance: the unwinnable game is secure
against all polynomial-time program families. -/
theorem zeroGame_secureAgainstPolyTime :
    zeroGame.toProgGame.secureAgainstPolyTime :=
  zeroGame.secureAgainst_isPolyTime_of_polyGame fun D =>
    negligible_of_zero (zeroGame_advantage_toPolyGame D)

end DynSystemExamples
