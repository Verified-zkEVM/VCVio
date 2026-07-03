/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.Asymptotics.PolyTime
import ToMathlib.Computability.PolyTimeTM
import Examples.DynamicalSystems.Basic

/-!
# The n-Flip XOR Adversary: a Fully Concrete Polynomial-Time Machine

The first machine family whose round count genuinely grows with the security
parameter: `xorFlips n` flips the coin `n` times, XOR-accumulating the answers in
finite state, and reports the parity after `n` rounds. The file assembles the complete
polynomial-time story for it, with no hypotheses left open:

* `xorProg` / `xorFlips` — the accumulator program family and the machine family,
  related by the simulation relation `XorRel` (`xorFlips_implements`), with the round
  invariant giving steadiness at exactly `n` rounds (`xorFlips_steadyBy`).
* `xorFlipsAdversary` — a fully concrete `PolyTimeAdversary`: all four per-step
  machine witnesses come from the generic finite-table machine
  (`Computability.EncPolyTime.ofFintype`), the state-size invariant and uniform step
  times are explicit linear polynomials.
* `isPolyTime_xorProg` — the first hypothesis-free `OracleComp.IsPolyTime` instance,
  with `OracleComp.PolyQueries` following by the generic bridge.
* Game wiring — `xorGame` demonstrates the advantage transfer
  `OneShotGame.advantage_toPolyGame_eq` on the concrete adversary, and `zeroGame`
  yields an unconditional `SecurityGame.secureAgainstPolyTime` instance.
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

/-! ## The machine family -/

/-- Flip the coin `n` times, XOR-accumulating, and report after `n` rounds. The state
is (rounds remaining, accumulator); zero remaining rounds is absorbing, which makes
the readout stable. -/
def xorFlips (n : ℕ) : OracleMachine coinSpec Unit Bool where
  State := Fin (n + 1) × Bool
  expose _ := ()
  update s b :=
    if (s.1 : ℕ) = 0 then s
    else (⟨(s.1 : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) s.1.isLt⟩, xor s.2 b)
  init _ := (Fin.last n, false)
  output s := if (s.1 : ℕ) = 0 then some s.2 else none

/-- The readout never changes once set. -/
theorem xorFlips_stableOutput (n : ℕ) : (xorFlips n).StableOutput := by
  intro s b hb u
  by_cases h : (s.1 : ℕ) = 0
  · simpa [xorFlips, h] using hb
  · simp [xorFlips, h] at hb

/-! ## Simulation and implementation -/

/-- The simulation relation: the machine state determines the residual accumulator
program. -/
def XorRel (n : ℕ) (s : Fin (n + 1) × Bool) (ob : OracleComp coinSpec Bool) : Prop :=
  ob = xorProg (s.1 : ℕ) s.2

theorem xorFlips_isSimulation (n : ℕ) : (xorFlips n).IsSimulation (XorRel n) where
  output_pure := by
    intro s b hR
    simp only [XorRel] at hR
    cases hv : (s.1 : ℕ) with
    | zero =>
      rw [hv, xorProg_zero, OracleComp.pure_inj] at hR
      simp [xorFlips, hv, hR]
    | succ m =>
      rw [hv, xorProg_succ] at hR
      exact Bool.noConfusion (congrArg OracleComp.isPure hR)
  output_queryBind := by
    intro s t k hR
    simp only [XorRel] at hR
    cases hv : (s.1 : ℕ) with
    | zero =>
      rw [hv, xorProg_zero] at hR
      exact Bool.noConfusion (congrArg OracleComp.isPure hR)
    | succ m => simp [xorFlips, hv]
  expose_eq := by intro s t k hR; rfl
  update_rel := by
    intro s t k hR r
    change XorRel n _ (k r)
    simp only [XorRel] at hR ⊢
    cases hv : (s.1 : ℕ) with
    | zero =>
      rw [hv, xorProg_zero] at hR
      exact Bool.noConfusion (congrArg OracleComp.isPure hR)
    | succ m =>
      rw [hv, xorProg_succ] at hR
      obtain ⟨ht, hk⟩ := (PFunctor.FreeM.roll_inj _ _ _ _).mp hR
      rw [show k = fun b => xorProg m (xor s.2 b) from hk]
      simp [xorFlips, hv]

/-- `xorFlips n` implements the `n`-flip program at fuel `n`. -/
theorem xorFlips_implements (n : ℕ) :
    (xorFlips n).Implements (fun _ : Unit => xorProg n false) n :=
  OracleMachine.implements_of_isSimulation (xorFlips_isSimulation n)
    (fun _ => rfl) (fun _ => isTotalQueryBound_xorProg n false)

/-! ## Steadiness: the round bound -/

private theorem xorFlips_advanceOnce_val (n : ℕ) (h : OracleHandler coinSpec)
    (s : Fin (n + 1) × Bool) (hs : ¬(s.1 : ℕ) = 0) :
    ((OracleStrategy.advanceOnce h (xorFlips n).toStrategy s).1 : ℕ) = (s.1 : ℕ) - 1 := by
  simp [OracleStrategy.advanceOnce, xorFlips, hs]

/-- Round invariant: after `j ≤ n` handler-answered rounds, `n - j` rounds remain. -/
theorem xorFlips_stateAfter_val (n : ℕ) (h : OracleHandler coinSpec) :
    ∀ j, j ≤ n →
      ((OracleStrategy.stateAfter h (xorFlips n).toStrategy
        ((xorFlips n).init ()) j).1 : ℕ) = n - j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hpeel : OracleStrategy.stateAfter h (xorFlips n).toStrategy
        ((xorFlips n).init ()) (j + 1) =
        OracleStrategy.advanceOnce h (xorFlips n).toStrategy
          (OracleStrategy.stateAfter h (xorFlips n).toStrategy
            ((xorFlips n).init ()) j) :=
      Function.iterate_succ_apply' _ _ _
    rw [hpeel,
      xorFlips_advanceOnce_val n h _ (by rw [ih (Nat.le_of_succ_le hj)]; omega),
      ih (Nat.le_of_succ_le hj)]
    omega

private theorem xorFlips_output_isSome (n : ℕ) {s : Fin (n + 1) × Bool}
    (hs : (s.1 : ℕ) = 0) : ((xorFlips n).output s).isSome := by
  simp [xorFlips, hs]

/-- The machine resolves within `n` rounds, against every handler. -/
theorem xorFlips_steadyBy (n : ℕ) (h : OracleHandler coinSpec) (x : Unit) :
    (xorFlips n).SteadyBy h ((xorFlips n).init x) n := by
  cases x
  exact xorFlips_output_isSome n
    (by rw [xorFlips_stateAfter_val n h n le_rfl]; omega)

/-! ## Encoded-size bounds

All encodings are `finEncodingOfFinEnum` unary encodings (or the `Option` wrapper on
one), so every encoded length is linearly bounded via
`Computability.length_boolify_finEncodingOfFinEnum`. -/

private theorem xorEncState_length_le (n : ℕ) (s : Fin (n + 1) × Bool) :
    ((finEncodingOfFinEnum (Fin (n + 1) × Bool)).boolify s).length ≤ 4 * n + 4 := by
  refine (length_boolify_finEncodingOfFinEnum s).trans ?_
  have hfresh : Fintype.card (Fin (n + 1) × Bool) = (n + 1) * 2 := by simp
  have hcard : ∀ I : Fintype (Fin (n + 1) × Bool), @Fintype.card _ I = (n + 1) * 2 :=
    fun I => (@Fintype.card_congr _ _ I (instFintypeProd _ _) (Equiv.refl _)).trans hfresh
  rw [hcard]
  omega

private theorem card_option_bool_gamma_le :
    Fintype.card (finEncodingOption (finEncodingOfFinEnum Bool)).Γ ≤ 2 := by
  refine Fintype.card_le_of_injective (Sum.elim (fun _ => (0 : Fin 2)) fun _ => 1) ?_
  rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) h
  · rfl
  · exact Nat.noConfusion (congrArg Fin.val h)
  · exact Nat.noConfusion (congrArg Fin.val h)
  · rfl

private theorem encode_option_bool_length_le (x : Option Bool) :
    ((finEncodingOption (finEncodingOfFinEnum Bool)).encode x).length ≤ 2 := by
  have hcard : FinEnum.card Bool = 2 := rfl
  rcases x with _ | b
  · simp [finEncodingOption]
  · have hb : (FinEnum.equiv b : ℕ) < 2 := hcard ▸ (FinEnum.equiv b).isLt
    simp only [finEncodingOption, finEncodingOfFinEnum, List.length_cons,
      List.length_map, List.length_replicate]
    omega

private theorem xorEncOption_length_le (x : Option Bool) :
    ((finEncodingOption (finEncodingOfFinEnum Bool)).boolify x).length ≤ 6 := by
  rw [FinEncoding.length_boolify]
  have h := Nat.mul_le_mul (Nat.add_le_add_right card_option_bool_gamma_le 1)
    (encode_option_bool_length_le x)
  omega

/-! ## The concrete polynomial-time adversary

Every field is explicit data: the round bound is the identity polynomial, the size
bound and step time are linear polynomials, and all four per-step machine witnesses
are instances of the generic finite-table machine `EncPolyTime.ofFintype`. -/

/-- The n-flip XOR adversary: the first fully concrete, hypothesis-free
`PolyTimeAdversary`. -/
noncomputable def xorFlipsAdversary :
    PolyTimeAdversary (fun _ => coinSpec) (fun _ => Unit) (fun _ => Bool) where
  M n := xorFlips n
  steps := .X
  stable n := xorFlips_stableOutput n
  steady n h x := by rw [Polynomial.eval_X]; exact xorFlips_steadyBy n h x
  encState n := finEncodingOfFinEnum (Fin (n + 1) × Bool)
  encIn _ := finEncodingOfFinEnum Unit
  encOut _ := finEncodingOfFinEnum Bool
  encIface _ := .ofFinEnum coinSpec
  sizeBound := .C 4 * .X + .C 4
  encState_length_le n h x j _ := by
    refine (xorEncState_length_le n _).trans ?_
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    omega
  initTM n :=
    letI : Fintype (xorFlips n).State := inferInstanceAs (Fintype (Fin (n + 1) × Bool))
    EncPolyTime.ofFintype _ (FinEncoding.boolify_injective _) _ _
  exposeTM n :=
    letI : Fintype (xorFlips n).State := inferInstanceAs (Fintype (Fin (n + 1) × Bool))
    EncPolyTime.ofFintype _ (FinEncoding.boolify_injective _) _ _
  updateTM n :=
    letI : Fintype (xorFlips n).State := inferInstanceAs (Fintype (Fin (n + 1) × Bool))
    EncPolyTime.ofFintype _ (FinEncoding.boolify_injective _) _ _
  outputTM n :=
    letI : Fintype (xorFlips n).State := inferInstanceAs (Fintype (Fin (n + 1) × Bool))
    EncPolyTime.ofFintype _ (FinEncoding.boolify_injective _) _ _
  stepTime := .C 4 * .X + .C 8
  initTM_time_le n k := by
    letI : Fintype (xorFlips n).State := inferInstanceAs (Fintype (Fin (n + 1) × Bool))
    refine (EncPolyTime.time_ofFintype_eval_le _
      (fun x => xorEncState_length_le n ((xorFlips n).init x)) k).trans ?_
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    omega
  exposeTM_time_le n k := by
    letI : Fintype (xorFlips n).State := inferInstanceAs (Fintype (Fin (n + 1) × Bool))
    refine (EncPolyTime.time_ofFintype_eval_le (B := 2) _ (fun s =>
      (length_boolify_finEncodingOfFinEnum (γ := Unit) ()).trans
        (by simp [Fintype.card_unique])) k).trans ?_
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    omega
  updateTM_time_le n k := by
    letI : Fintype (xorFlips n).State := inferInstanceAs (Fintype (Fin (n + 1) × Bool))
    refine (EncPolyTime.time_ofFintype_eval_le _
      (fun p => xorEncState_length_le n ((xorFlips n).updateFlat p)) k).trans ?_
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    omega
  outputTM_time_le n k := by
    letI : Fintype (xorFlips n).State := inferInstanceAs (Fintype (Fin (n + 1) × Bool))
    refine (EncPolyTime.time_ofFintype_eval_le _
      (fun s => xorEncOption_length_le ((xorFlips n).output s)) k).trans ?_
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    omega

/-- The bundled adversary implements the program family. -/
theorem xorFlipsAdversary_implements :
    xorFlipsAdversary.Implements fun n (_ : Unit) => xorProg n false := by
  intro n
  rw [show xorFlipsAdversary.steps = Polynomial.X from rfl, Polynomial.eval_X]
  exact xorFlips_implements n

/-- **The first hypothesis-free polynomial-time instance**: flipping the coin `n`
times and reporting the parity is polynomial time, witnessed end to end by concrete
Turing machines. -/
theorem isPolyTime_xorProg :
    OracleComp.IsPolyTime fun n (_ : Unit) => xorProg n false :=
  ⟨xorFlipsAdversary, xorFlipsAdversary_implements, fun n x => by
    rw [show xorFlipsAdversary.steps = Polynomial.X from rfl, Polynomial.eval_X]
    exact isTotalQueryBound_xorProg n false⟩

/-- Polynomially many queries follow by the generic bridge. -/
example : Nonempty (OracleComp.PolyQueries fun n (_ : Unit) => xorProg n false) :=
  isPolyTime_xorProg.polyQueries

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
    xorGame.toPolyGame.advantage xorFlipsAdversary n =
      xorGame.toProgGame.advantage (fun n _ => xorProg n false) n :=
  xorGame.advantage_toPolyGame_eq xorFlipsAdversary_implements n

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
