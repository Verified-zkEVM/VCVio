/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.Asymptotics.PolyTime
import ToMathlib.Computability.PolyTimeTM
import ToMathlib.Computability.Encoding

/-!
# Bounded Coin Fold: a Reusable Polynomial-Time Construction

Many polynomial-time oracle computations have the same shape: flip the coin a polynomial
number of times, folding each answer into a finite-state accumulator, then read out a
value. `coinFoldProg step readout` is that program family, and `isPolyTime_coinFold`
bundles the whole Turing-machine polynomial-time witness for it once and for all, so a
concrete instance collapses to supplying `step`/`readout`, the encodings, and two
encoding-length bounds — no hand-built `OracleMachine`/`PolyTimeAdversary` needed.

* `coinFoldProg` — the fold program; `coinFoldMachine` — the machine realizing it, with the
  read-out map folded into `output` and the round counter as `Fin (rounds + 1)`.
* `coinFoldMachine_implements` (via the simulation relation `CoinFoldRel`) and
  `coinFoldMachine_steadyBy` (via the round invariant) give the coalgebraic side.
* `coinFoldAdversary` / `isPolyTime_coinFold` — the fully assembled `PolyTimeAdversary` and
  `OracleComp.IsPolyTime`.

Worked instances: `Examples.DynamicalSystems.XorFlips` (single-`Bool` accumulator, `readout`
the identity) and `Examples.KatzLindell.SamplerMachine` (`BitVec` accumulator, nontrivial
`readout`), which collapse onto this combinator.

Specialized to `coinSpec` (the coin oracle, answers `Bool`): both current consumers use it,
and it keeps the simulation free of the dependent answer-type transport that an
arbitrary-spec version would incur. Generalizing the fold to an arbitrary oracle is future
work.
-/

open OracleSpec OracleComp Computability

namespace OracleComp

/-- `IsPolyTime` transports along pointwise program equality: a family equal to a
polynomial-time family is polynomial time. Lets a call site name its program directly and
bridge to the combinator's `coinFoldProg` form. -/
theorem IsPolyTime.congr {ι : Type} [DecidableEq ι] {spec : ℕ → OracleSpec.{0, 0} ι}
    {α β : ℕ → Type}
    {oa oa' : (n : ℕ) → α n → OracleComp (spec n) (β n)} (h : ∀ n x, oa n x = oa' n x)
    (hp : OracleComp.IsPolyTime oa) : OracleComp.IsPolyTime oa' :=
  (funext fun n => funext fun x => h n x : oa = oa') ▸ hp

/-! ## The fold program and its machine -/

section Machine

variable {σ β : Type}

/-- Flip the coin `r` times, folding each answer into `acc` with `step`, then read out
`readout` of the final accumulator. The round index (remaining count minus one) is passed to
`step`, so bit-position-dependent folds are expressible. -/
def coinFoldProg (step : σ → ℕ → Bool → σ) (readout : σ → β) :
    ℕ → σ → OracleComp coinSpec β
  | 0, acc => pure (readout acc)
  | r + 1, acc => OracleComp.queryBind () fun b => coinFoldProg step readout r (step acc r b)

theorem coinFoldProg_succ (step : σ → ℕ → Bool → σ) (readout : σ → β) (r : ℕ) (acc : σ) :
    coinFoldProg step readout (r + 1) acc =
      OracleComp.queryBind () fun b => coinFoldProg step readout r (step acc r b) := rfl

theorem isTotalQueryBound_coinFoldProg (step : σ → ℕ → Bool → σ) (readout : σ → β)
    (r : ℕ) (acc : σ) : IsTotalQueryBound (coinFoldProg step readout r acc) r := by
  induction r generalizing acc with
  | zero => trivial
  | succ r ih => exact ⟨Nat.succ_pos r, fun b => ih (step acc r b)⟩

variable (step : σ → ℕ → Bool → σ) (readout : σ → β)

/-- The fold machine: state `(remaining rounds, accumulator)`; each step decrements the
counter and folds the answer at the next index; at zero rounds it reads out `readout`, and
zero is absorbing so the read-out is stable. -/
def coinFoldMachine (rounds : ℕ) (init₀ : σ) : OracleMachine coinSpec Unit β where
  State := Fin (rounds + 1) × σ
  expose _ := ()
  update s b :=
    if (s.1 : ℕ) = 0 then s
    else (⟨(s.1 : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) s.1.isLt⟩, step s.2 ((s.1 : ℕ) - 1) b)
  init _ := (Fin.last rounds, init₀)
  output s := if (s.1 : ℕ) = 0 then some (readout s.2) else none

theorem coinFoldMachine_stableOutput (rounds : ℕ) (init₀ : σ) :
    (coinFoldMachine step readout rounds init₀).StableOutput := by
  intro s b hb u
  by_cases h : (s.1 : ℕ) = 0
  · simpa [coinFoldMachine, h] using hb
  · simp [coinFoldMachine, h] at hb

/-- The simulation relation: the machine state determines the residual fold program. -/
def CoinFoldRel (rounds : ℕ) (s : Fin (rounds + 1) × σ) (ob : OracleComp coinSpec β) : Prop :=
  ob = coinFoldProg step readout (s.1 : ℕ) s.2

theorem coinFoldMachine_isSimulation (rounds : ℕ) (init₀ : σ) :
    (coinFoldMachine step readout rounds init₀).IsSimulation
      (CoinFoldRel step readout rounds) where
  output_pure := by
    intro s b hR
    simp only [CoinFoldRel] at hR
    cases hv : (s.1 : ℕ) with
    | zero =>
      rw [hv, coinFoldProg, OracleComp.pure_inj] at hR
      simp [coinFoldMachine, hv, hR]
    | succ m =>
      rw [hv, coinFoldProg_succ] at hR
      exact Bool.noConfusion (congrArg OracleComp.isPure hR)
  output_queryBind := by
    intro s t k hR
    simp only [CoinFoldRel] at hR
    cases hv : (s.1 : ℕ) with
    | zero =>
      rw [hv, coinFoldProg] at hR
      exact Bool.noConfusion (congrArg OracleComp.isPure hR)
    | succ m => simp [coinFoldMachine, hv]
  expose_eq := by intro s t k hR; rfl
  update_rel := by
    intro s t k hR r
    change CoinFoldRel step readout rounds _ (k r)
    simp only [CoinFoldRel] at hR ⊢
    cases hv : (s.1 : ℕ) with
    | zero =>
      rw [hv, coinFoldProg] at hR
      exact Bool.noConfusion (congrArg OracleComp.isPure hR)
    | succ m =>
      rw [hv, coinFoldProg_succ] at hR
      obtain ⟨ht, hk⟩ := (PFunctor.FreeM.roll_inj _ _ _ _).mp hR
      rw [show k = fun b => coinFoldProg step readout m (step s.2 m b) from hk]
      simp [coinFoldMachine, hv]

theorem coinFoldMachine_implements (rounds : ℕ) (init₀ : σ) :
    (coinFoldMachine step readout rounds init₀).Implements
      (fun _ : Unit => coinFoldProg step readout rounds init₀) rounds :=
  OracleMachine.implements_of_isSimulation
    (coinFoldMachine_isSimulation step readout rounds init₀)
    (fun _ => rfl) (fun _ => isTotalQueryBound_coinFoldProg step readout rounds init₀)

/-! ### Steadiness: the round bound -/

private theorem coinFoldMachine_advanceOnce_val (rounds : ℕ) (init₀ : σ)
    (h : OracleHandler coinSpec) (s : Fin (rounds + 1) × σ) (hs : ¬(s.1 : ℕ) = 0) :
    ((OracleStrategy.advanceOnce h (coinFoldMachine step readout rounds init₀).toStrategy s).1
      : ℕ) = (s.1 : ℕ) - 1 := by
  simp [OracleStrategy.advanceOnce, coinFoldMachine, hs]

theorem coinFoldMachine_stateAfter_val (rounds : ℕ) (init₀ : σ) (h : OracleHandler coinSpec) :
    ∀ j, j ≤ rounds →
      ((OracleStrategy.stateAfter h (coinFoldMachine step readout rounds init₀).toStrategy
        ((coinFoldMachine step readout rounds init₀).init ()) j).1 : ℕ) = rounds - j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hpeel :
        OracleStrategy.stateAfter h (coinFoldMachine step readout rounds init₀).toStrategy
          ((coinFoldMachine step readout rounds init₀).init ()) (j + 1) =
        OracleStrategy.advanceOnce h (coinFoldMachine step readout rounds init₀).toStrategy
          (OracleStrategy.stateAfter h (coinFoldMachine step readout rounds init₀).toStrategy
            ((coinFoldMachine step readout rounds init₀).init ()) j) :=
      Function.iterate_succ_apply' _ _ _
    rw [hpeel,
      coinFoldMachine_advanceOnce_val step readout rounds init₀ h _
        (by rw [ih (Nat.le_of_succ_le hj)]; omega),
      ih (Nat.le_of_succ_le hj)]
    omega

private theorem coinFoldMachine_output_isSome (rounds : ℕ) (init₀ : σ)
    {s : Fin (rounds + 1) × σ} (hs : (s.1 : ℕ) = 0) :
    ((coinFoldMachine step readout rounds init₀).output s).isSome := by
  simp [coinFoldMachine, hs]

theorem coinFoldMachine_steadyBy (rounds : ℕ) (init₀ : σ) (h : OracleHandler coinSpec) (x : Unit) :
    (coinFoldMachine step readout rounds init₀).SteadyBy h
      ((coinFoldMachine step readout rounds init₀).init x) rounds := by
  cases x
  exact coinFoldMachine_output_isSome step readout rounds init₀
    (by rw [coinFoldMachine_stateAfter_val step readout rounds init₀ h rounds le_rfl]; omega)

end Machine

/-! ## The polynomial-time adversary and `IsPolyTime`

The actual per-parameter round count is a plain `rnd : ℕ → ℕ` (so a call site's `2 * n`
stays definitionally equal, keeping the state encoding `Fin (rnd n + 1) × σ n` unadorned);
`steps` is the `Polynomial ℕ` round *bound* with `hrnd : ∀ n, rnd n = steps.eval n`. -/

section Adversary

variable {σ β : ℕ → Type} [∀ n, Fintype (σ n)]
  (step : (n : ℕ) → σ n → ℕ → Bool → σ n)
  (readout : (n : ℕ) → σ n → β n) (init₀ : (n : ℕ) → σ n)
  (rnd : ℕ → ℕ) (steps : Polynomial ℕ) (hrnd : ∀ n, rnd n = steps.eval n)
  (encState : (n : ℕ) → FinEncoding (Fin (rnd n + 1) × σ n))
  (Sσ : Polynomial ℕ) (hstate : ∀ n s, ((encState n).boolify s).length ≤ Sσ.eval n)
  (encβ : (n : ℕ) → FinEncoding (β n))
  (Sβ : Polynomial ℕ)
  (hout : ∀ n (x : Option (β n)), ((finEncodingOption (encβ n)).boolify x).length ≤ Sβ.eval n)

/-- The bounded coin fold as a fully concrete `PolyTimeAdversary`: round bound `steps`, size
bound `Sσ`, step time dominating the four per-step machine witnesses (all instances of the
finite-table machine `EncPolyTime.ofFintype`). -/
noncomputable def coinFoldAdversary :
    PolyTimeAdversary (fun _ => coinSpec) (fun _ => Unit) β where
  M n := coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)
  steps := steps
  stable n := coinFoldMachine_stableOutput (step n) (readout n) (rnd n) (init₀ n)
  steady n h x := by
    rw [← hrnd n]; exact coinFoldMachine_steadyBy (step n) (readout n) (rnd n) (init₀ n) h x
  encState := encState
  encIn _ := finEncodingOfFinEnum Unit
  encOut := encβ
  encIface _ := .ofFinEnum coinSpec
  sizeBound := Sσ
  encState_length_le n _ _ _ _ := hstate n _
  initTM n := EncPolyTime.ofFintype _ (FinEncoding.boolify_injective _) _ _
  exposeTM n :=
    letI : Fintype (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).State :=
      inferInstanceAs (Fintype (Fin (rnd n + 1) × σ n))
    EncPolyTime.ofFintype _ (FinEncoding.boolify_injective _) _ _
  updateTM n :=
    letI : Fintype (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).State :=
      inferInstanceAs (Fintype (Fin (rnd n + 1) × σ n))
    EncPolyTime.ofFintype _ (FinEncoding.boolify_injective _) _ _
  outputTM n :=
    letI : Fintype (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).State :=
      inferInstanceAs (Fintype (Fin (rnd n + 1) × σ n))
    EncPolyTime.ofFintype _ (FinEncoding.boolify_injective _) _ _
  stepTime := .X + Sσ + Sβ + .C 3
  initTM_time_le n k := by
    refine (EncPolyTime.time_ofFintype_eval_le _
      (fun x => hstate n
        ((coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).init x)) k).trans ?_
    have h1 : Sσ.eval n ≤ Sσ.eval (n + k) := Polynomial.eval_le_eval (Nat.le_add_right n k)
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    omega
  exposeTM_time_le n k := by
    letI : Fintype (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).State :=
      inferInstanceAs (Fintype (Fin (rnd n + 1) × σ n))
    refine (EncPolyTime.time_ofFintype_eval_le (B := 2) _ (fun s =>
      (length_boolify_finEncodingOfFinEnum (γ := Unit) ()).trans
        (by simp [Fintype.card_unique])) k).trans ?_
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    omega
  updateTM_time_le n k := by
    letI : Fintype (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).State :=
      inferInstanceAs (Fintype (Fin (rnd n + 1) × σ n))
    refine (EncPolyTime.time_ofFintype_eval_le _
      (fun p => hstate n
        ((coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).updateFlat p)) k).trans ?_
    have h1 : Sσ.eval n ≤ Sσ.eval (n + k) := Polynomial.eval_le_eval (Nat.le_add_right n k)
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    omega
  outputTM_time_le n k := by
    letI : Fintype (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).State :=
      inferInstanceAs (Fintype (Fin (rnd n + 1) × σ n))
    refine (EncPolyTime.time_ofFintype_eval_le _
      (fun s => hout n
        ((coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).output s)) k).trans ?_
    have h1 : Sβ.eval n ≤ Sβ.eval (n + k) := Polynomial.eval_le_eval (Nat.le_add_right n k)
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    omega

/-- The bundled fold adversary implements the fold program family. -/
theorem coinFoldAdversary_implements {σ β : ℕ → Type} [∀ n, Fintype (σ n)]
    (step : (n : ℕ) → σ n → ℕ → Bool → σ n) (readout : (n : ℕ) → σ n → β n)
    (init₀ : (n : ℕ) → σ n) (rnd : ℕ → ℕ) (steps : Polynomial ℕ) (hrnd : ∀ n, rnd n = steps.eval n)
    (encState : (n : ℕ) → FinEncoding (Fin (rnd n + 1) × σ n))
    (Sσ : Polynomial ℕ) (hstate : ∀ n s, ((encState n).boolify s).length ≤ Sσ.eval n)
    (encβ : (n : ℕ) → FinEncoding (β n)) (Sβ : Polynomial ℕ)
    (hout : ∀ n (x : Option (β n)),
      ((finEncodingOption (encβ n)).boolify x).length ≤ Sβ.eval n) :
    (coinFoldAdversary step readout init₀ rnd steps hrnd encState Sσ hstate encβ Sβ hout).Implements
      fun n (_ : Unit) => coinFoldProg (step n) (readout n) (rnd n) (init₀ n) := by
  intro n
  show (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).Implements
    (fun _ => coinFoldProg (step n) (readout n) (rnd n) (init₀ n)) (steps.eval n)
  rw [← hrnd n]
  exact coinFoldMachine_implements (step n) (readout n) (rnd n) (init₀ n)

/-- **The bounded coin fold is polynomial time.** Filling `rnd n` coin answers into a finite
accumulator and reading out is polynomial time, witnessed end to end by concrete Turing
machines — no hand-built machine required at the call site. -/
theorem isPolyTime_coinFold {σ β : ℕ → Type} [∀ n, Fintype (σ n)]
    (step : (n : ℕ) → σ n → ℕ → Bool → σ n) (readout : (n : ℕ) → σ n → β n)
    (init₀ : (n : ℕ) → σ n) (rnd : ℕ → ℕ) (steps : Polynomial ℕ) (hrnd : ∀ n, rnd n = steps.eval n)
    (encState : (n : ℕ) → FinEncoding (Fin (rnd n + 1) × σ n))
    (Sσ : Polynomial ℕ) (hstate : ∀ n s, ((encState n).boolify s).length ≤ Sσ.eval n)
    (encβ : (n : ℕ) → FinEncoding (β n)) (Sβ : Polynomial ℕ)
    (hout : ∀ n (x : Option (β n)),
      ((finEncodingOption (encβ n)).boolify x).length ≤ Sβ.eval n) :
    OracleComp.IsPolyTime
      fun n (_ : Unit) => coinFoldProg (step n) (readout n) (rnd n) (init₀ n) :=
  ⟨coinFoldAdversary step readout init₀ rnd steps hrnd encState Sσ hstate encβ Sβ hout,
    coinFoldAdversary_implements step readout init₀ rnd steps hrnd encState Sσ hstate encβ Sβ hout,
    fun n _ => (isTotalQueryBound_coinFoldProg (step n) (readout n) (rnd n) (init₀ n)).mono
      (le_of_eq (hrnd n))⟩

end Adversary

end OracleComp
