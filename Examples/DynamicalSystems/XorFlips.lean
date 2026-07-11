/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.Asymptotics.Game.Challenger
import VCVio.OracleComp.Coinductive.CoinFold
import Examples.DynamicalSystems.Basic

/-!
# The n-Flip XOR Adversary via the Bounded Coin Fold

`xorFlips n` flips the coin `n` times, XOR-accumulating the answers in finite state, and
reports the parity after `n` rounds — the paradigmatic bounded query fold. This file gets
its complete polynomial-time story from the reusable combinator
`OracleComp.isPolyTime_coinFold`, with no hand-built machine, at the pinned canonical
boundaries `BoundaryData.coin BitEncFam.unit BitEncFam.bool`:

* `xorProg` — the accumulator program family, exactly `OracleComp.coinFoldProg` with
  `step = xor` and `readout = id` (`xorProg_eq_coinFoldProg`).
* `xorFoldAdversary` / `isPolyTime_xorProg` — the bundled `MachineAdversary` and the
  hypothesis-free `OracleComp.IsPolyTime` instance, obtained from the combinator by
  supplying the binary counter/accumulator state representation `xorState` and the
  constant accumulator-cardinality bound.
* the output-map closure in action — negating the reported parity stays polynomial
  time, by `OracleComp.IsPolyTime.map` on the abstract instance.
* Game wiring — `xorGame` demonstrates the advantage transfer
  `Challenger.advantage_toMachineGame_eq` on the concrete bundle, and `zeroGame` yields
  an unconditional `SecurityGame.secureAgainstPolyTime` instance.
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

/-! ## The concrete polynomial-time adversary -/

/-- The fold state representation: binary round counter appended to the accumulator
bit, total width `n + 1`. -/
noncomputable def xorState : StrEncFam (fun n => Fin (n + 1) × Bool) :=
  ((BitEncFam.fin id .X fun n => (Polynomial.eval_X (x := n)).ge).pair
    (BitEncFam.const Bool)).toStrEncFam

/-- The n-flip XOR adversary, from the bounded coin fold: state `Fin (n+1) × Bool`,
round bound `n`, constant accumulator cardinality. -/
noncomputable def xorFoldAdversary :
    MachineAdversary (BoundaryData.coin BitEncFam.unit BitEncFam.bool) :=
  OracleComp.coinFoldAdversary (fun _ acc _ b => xor acc b) (fun _ a => a) (fun _ => false)
    id Polynomial.X (fun n => by simp) xorState BitEncFam.bool
    (.C 2) (fun n => by simp)

/-- The certified fold witness for the `coinFoldProg` presentation. -/
noncomputable def xorFoldWitness :
    PolyTimeWitness (BoundaryData.coin BitEncFam.unit BitEncFam.bool)
      (fun n (_ : Unit) => OracleComp.coinFoldProg (fun a _ b => xor a b) id n false) :=
  OracleComp.coinFoldWitness (fun _ acc _ b => xor acc b) (fun _ a => a) (fun _ => false)
    id Polynomial.X (fun n => by simp) xorState BitEncFam.bool
    (.C 2) (fun n => by simp)

/-- The bundled XOR adversary implements the `n`-flip program family. -/
theorem xorFoldAdversary_implements :
    xorFoldAdversary.Implements fun n (_ : Unit) => xorProg n false := by
  rw [show (fun n (_ : Unit) => xorProg n false)
      = fun n (_ : Unit) => OracleComp.coinFoldProg (fun a _ b => xor a b) id n false from
    funext fun n => funext fun _ => xorProg_eq_coinFoldProg n false]
  exact xorFoldWitness.implements

/-- **A hypothesis-free polynomial-time instance**: flipping the coin `n` times and
reporting the parity is polynomial time at the canonical boundaries, witnessed end to
end by concrete Turing machines, as a one-line application of the bounded-coin-fold
combinator. -/
theorem isPolyTime_xorProg :
    OracleComp.IsPolyTime (BoundaryData.coin BitEncFam.unit BitEncFam.bool)
      (fun n (_ : Unit) => xorProg n false) :=
  OracleComp.IsPolyTime.congr (fun n _ => (xorProg_eq_coinFoldProg n false).symm)
    ⟨xorFoldWitness⟩

/-- Polynomially many queries follow by the generic bridge. -/
example : Nonempty (OracleComp.PolyQueries fun n (_ : Unit) => xorProg n false) :=
  isPolyTime_xorProg.polyQueries

/-- Post-composing a pure map onto the fold is polynomial time, via the abstract
output-map closure `OracleComp.IsPolyTime.map` — derivable exactly because the output
boundary is canonical: negating the reported parity stays polynomial time. -/
example :
    OracleComp.IsPolyTime (BoundaryData.coin BitEncFam.unit BitEncFam.bool)
      (fun n (_ : Unit) => (! ·) <$> xorProg n false) :=
  isPolyTime_xorProg.map (fun _ b => !b) BitEncFam.bool (.C 2) (fun n => by simp)

/-! ## Game wiring

`xorGame` is deliberately winnable — it exists to demonstrate the advantage transfer
between the machine and program presentations of the concrete adversary. `zeroGame`
is unwinnable, giving an unconditional `secureAgainstPolyTime` instance. -/

/-- A fair coin as a randomized oracle. -/
noncomputable def fairCoin : ProbHandler coinSpec :=
  fun _ => liftM (PMF.uniformOfFintype Bool)

/-- Guess-the-parity game: run the adversary against a fair coin, win on a report of
`true`. A memoryless challenger, via `Challenger.ofProbHandler`. -/
noncomputable def xorGame :
    Challenger (fun _ => coinSpec) (fun _ => Unit) (fun _ => Bool) :=
  Challenger.ofProbHandler (fun _ => fairCoin) (fun _ => pure ())
    (fun _ _ b => pure (b.getD false))

/-- Advantage transfer, concretely: the machine-level advantage of the bundled XOR
adversary is exactly the program-level advantage of `xorProg`. -/
example (n : ℕ) :
    (xorGame.toMachineGame (BoundaryData.coin BitEncFam.unit BitEncFam.bool)).advantage
        xorFoldAdversary n =
      xorGame.toProgGame.advantage (fun n _ => xorProg n false) n :=
  xorGame.advantage_toMachineGame_eq xorFoldAdversary_implements n

/-- A game nobody wins: the score is constantly `false`. -/
noncomputable def zeroGame :
    Challenger (fun _ => coinSpec) (fun _ => Unit) (fun _ => Bool) :=
  Challenger.ofProbHandler (fun _ => fairCoin) (fun _ => pure ())
    (fun _ _ _ => pure false)

theorem zeroGame_advantage_toMachineGame
    (D : MachineAdversary (BoundaryData.coin BitEncFam.unit BitEncFam.bool))
    (n : ℕ) :
    (zeroGame.toMachineGame (BoundaryData.coin BitEncFam.unit BitEncFam.bool)).advantage
      D n = 0 := by
  have h : (zeroGame.toMachineGame
        (BoundaryData.coin BitEncFam.unit BitEncFam.bool)).advantage D n =
      ((D.exec n (QueryImpl.stateless Unit fairCoin) ()).run () >>= fun _ =>
        (pure false : SPMF Bool)) true := by
    simp only [Challenger.toMachineGame, zeroGame, Challenger.ofProbHandler, map_pure,
      pure_bind]
    rfl
  rw [h, SPMF.bind_apply_eq_tsum]
  simp [SPMF.pure_apply]

/-- An unconditional end-to-end security instance: the unwinnable game is secure
against all polynomial-time program families. -/
theorem zeroGame_secureAgainstPolyTime :
    zeroGame.toProgGame.secureAgainstPolyTime
      (BoundaryData.coin BitEncFam.unit BitEncFam.bool) :=
  zeroGame.secureAgainst_isPolyTime_of_machineGame _ fun D =>
    negligible_of_zero (zeroGame_advantage_toMachineGame D)

end DynSystemExamples
