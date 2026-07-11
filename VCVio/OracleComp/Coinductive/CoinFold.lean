/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.PolyTimeClosure

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
the identity) and `KatzLindell.Chapter03.SamplerMachine` (`BitVec` accumulator, nontrivial
`readout`), which collapse onto this combinator.

Specialized to `coinSpec` (the coin oracle, answers `Bool`): both current consumers use it,
and it keeps the simulation free of the dependent answer-type transport that an
arbitrary-spec version would incur. Generalizing the fold to an arbitrary oracle is future
work.
-/

open OracleSpec OracleComp Computability
open scoped OracleMachine

namespace OracleComp

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
    coinFoldMachine step readout rounds init₀ ⊨[rounds]
      fun _ : Unit => coinFoldProg step readout rounds init₀ :=
  OracleMachine.implements_of_isSimulation
    (coinFoldMachine_isSimulation step readout rounds init₀)
    (fun _ => rfl) (fun _ => isTotalQueryBound_coinFoldProg step readout rounds init₀)

/-! ### Steadiness: the round bound -/

private theorem coinFoldMachine_advanceOnce_val (rounds : ℕ) (init₀ : σ)
    (h : OracleHandler coinSpec) (s : Fin (rounds + 1) × σ) (hs : ¬(s.1 : ℕ) = 0) :
    ((OracleStrategy.advanceOnce h (coinFoldMachine step readout rounds init₀).toDynSystem s).1
      : ℕ) = (s.1 : ℕ) - 1 := by
  simp [OracleStrategy.advanceOnce, coinFoldMachine, hs]

theorem coinFoldMachine_stateAfter_val (rounds : ℕ) (init₀ : σ) (h : OracleHandler coinSpec) :
    ∀ j, j ≤ rounds →
      ((OracleStrategy.stateAfter h (coinFoldMachine step readout rounds init₀).toDynSystem
        ((coinFoldMachine step readout rounds init₀).init ()) j).1 : ℕ) = rounds - j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hpeel :
        OracleStrategy.stateAfter h (coinFoldMachine step readout rounds init₀).toDynSystem
          ((coinFoldMachine step readout rounds init₀).init ()) (j + 1) =
        OracleStrategy.advanceOnce h (coinFoldMachine step readout rounds init₀).toDynSystem
          (OracleStrategy.stateAfter h (coinFoldMachine step readout rounds init₀).toDynSystem
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
stays definitionally equal, keeping the state family `Fin (rnd n + 1) × σ n` unadorned);
`steps` is the `Polynomial ℕ` round *bound* with `hrnd : ∀ n, rnd n = steps.eval n`.
Boundaries are pinned to the canonical `BoundaryData.coin BitEncFam.unit eβ`; the fold
state representation `st` is machine-internal data supplied by the caller. -/

section Adversary

variable {σ β : ℕ → Type} [∀ n, Fintype (σ n)]
  (step : (n : ℕ) → σ n → ℕ → Bool → σ n)
  (readout : (n : ℕ) → σ n → β n) (init₀ : (n : ℕ) → σ n)
  (rnd : ℕ → ℕ) (steps : Polynomial ℕ) (hrnd : ∀ n, rnd n = steps.eval n)
  (st : StrEncFam (fun n => Fin (rnd n + 1) × σ n)) (eβ : BitEncFam β)
  (Sc : Polynomial ℕ) (hcard : ∀ n, Fintype.card (σ n) ≤ Sc.eval n)

/-- The bounded coin fold as a fully concrete `MachineAdversary` at the canonical
coin boundaries: round bound `steps`, state representation `st`, and all four step
witnesses discharged by finite tables (`Computability.EncPolyTimeFam.ofFintype`) —
within the advice budget exactly because the accumulator cardinality is polynomially
bounded (`Sc`). Folds into superpolynomially large accumulators need
`coinFoldAdversaryOfWitnesses` instead. -/
noncomputable def coinFoldAdversary :
    MachineAdversary (BoundaryData.coin BitEncFam.unit eβ) where
  M n := coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)
  steps := steps
  stable n := coinFoldMachine_stableOutput (step n) (readout n) (rnd n) (init₀ n)
  state := st
  initF := .ofFintype BitEncFam.unit.enc_injective
    (fun n => (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).init)
    (.C 1) (fun n => by simp)
    BitEncFam.unit.widBound
    (fun n x => (BitEncFam.unit.len_eq n x).le.trans (BitEncFam.unit.wid_le n))
    st.bound (fun n _ => st.len_le n _)
  exposeF :=
    letI : ∀ n, Fintype (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).State :=
      fun n => inferInstanceAs (Fintype (Fin (rnd n + 1) × σ n))
    .ofFintype st.enc_injective
      (fun n => (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).expose)
      ((steps + .C 1) * Sc)
      (fun n => by
        show Fintype.card (Fin (rnd n + 1) × σ n) ≤ _
        rw [Fintype.card_prod, Fintype.card_fin, hrnd n]
        simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C]
        exact Nat.mul_le_mul_left _ (hcard n))
      st.bound (fun n _ => st.len_le n _)
      InterfaceBitEnc.coin.encQuery.widBound
      (fun n x => (InterfaceBitEnc.coin.encQuery.len_eq n _).le.trans
        (InterfaceBitEnc.coin.encQuery.wid_le n))
  updateF :=
    letI : ∀ n, Fintype (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).State :=
      fun n => inferInstanceAs (Fintype (Fin (rnd n + 1) × σ n))
    .ofFintype (st.pairVar InterfaceBitEnc.coin.encAns).enc_injective
      (fun n => (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).updateFlat)
      ((steps + .C 1) * Sc * .C 2)
      (fun n => by
        have hAns : Fintype.card ((t : Unit) × coinSpec.Range t) = 2 := by
          simp [Fintype.card_sigma]
        show Fintype.card ((Fin (rnd n + 1) × σ n) × ((t : Unit) × coinSpec.Range t)) ≤ _
        rw [Fintype.card_prod, hAns, Fintype.card_prod, Fintype.card_fin, hrnd n]
        simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hcard n)))
      (st.bound + .C 1)
      (fun n p => by
        have h1 := st.len_le n p.1
        have h2 := InterfaceBitEnc.coin.encAns.len_eq n p.2
        have h3 : InterfaceBitEnc.coin.encAns.wid n = 1 := rfl
        simp only [StrEncFam.pairVar_enc, List.length_append, h2, h3, Polynomial.eval_add,
          Polynomial.eval_C]
        omega)
      st.bound (fun n _ => st.len_le n _)
  outputF :=
    letI : ∀ n, Fintype (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).State :=
      fun n => inferInstanceAs (Fintype (Fin (rnd n + 1) × σ n))
    .ofFintype st.enc_injective
      (fun n => (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).output)
      ((steps + .C 1) * Sc)
      (fun n => by
        show Fintype.card (Fin (rnd n + 1) × σ n) ≤ _
        rw [Fintype.card_prod, Fintype.card_fin, hrnd n]
        simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C]
        exact Nat.mul_le_mul_left _ (hcard n))
      st.bound (fun n _ => st.len_le n _)
      (eβ.option).widBound
      (fun n x => ((eβ.option).len_eq n _).le.trans ((eβ.option).wid_le n))

/-- The bundled fold adversary certifies the fold program family. -/
noncomputable def coinFoldWitness :
    PolyTimeWitness (BoundaryData.coin BitEncFam.unit eβ)
      (fun n (_ : Unit) => coinFoldProg (step n) (readout n) (rnd n) (init₀ n)) where
  A := coinFoldAdversary step readout init₀ rnd steps hrnd st eβ Sc hcard
  implements n := by
    show coinFoldMachine (step n) (readout n) (rnd n) (init₀ n) ⊨[steps.eval n]
      fun _ => coinFoldProg (step n) (readout n) (rnd n) (init₀ n)
    rw [← hrnd n]
    exact coinFoldMachine_implements (step n) (readout n) (rnd n) (init₀ n)
  queryBound n _ := (isTotalQueryBound_coinFoldProg (step n) (readout n) (rnd n)
    (init₀ n)).mono (le_of_eq (hrnd n))

include steps hrnd st Sc hcard in
/-- **The bounded coin fold is polynomial time.** Filling `rnd n` coin answers into an
accumulator of *polynomially bounded cardinality* and reading out is polynomial time,
witnessed end to end by concrete Turing machines — no hand-built machine required at
the call site. The cardinality bound `Sc` keeps the table witnesses within the advice
budget; folds into superpolynomially large accumulators (e.g. `BitVec n`) need
`isPolyTime_coinFold_of_witnesses`. -/
theorem isPolyTime_coinFold :
    OracleComp.IsPolyTime (BoundaryData.coin BitEncFam.unit eβ)
      (fun n (_ : Unit) => coinFoldProg (step n) (readout n) (rnd n) (init₀ n)) :=
  ⟨coinFoldWitness step readout init₀ rnd steps hrnd st eβ Sc hcard⟩

end Adversary

/-! ## The witness-parameterized fold adversary

For folds whose accumulator type is *not* polynomially small (e.g. a `BitVec n`
accumulator), the table witnesses of `coinFoldAdversary` would exceed any polynomial
advice bound, so the machine witnesses must be supplied: uniform machine families for
the fold's step functions. All coalgebraic content (implements, stability, the
state-size invariant) is still discharged here; only the four `EncPolyTimeFam`
witnesses are hypotheses, pending a base-machine library. -/

section AdversaryOfWitnesses

variable {σ β : ℕ → Type}
  (step : (n : ℕ) → σ n → ℕ → Bool → σ n)
  (readout : (n : ℕ) → σ n → β n) (init₀ : (n : ℕ) → σ n)
  (rnd : ℕ → ℕ) (steps : Polynomial ℕ) (hrnd : ∀ n, rnd n = steps.eval n)
  (st : StrEncFam (fun n => Fin (rnd n + 1) × σ n)) (eβ : BitEncFam β)
  (initF : EncPolyTimeFam BitEncFam.unit.enc st.enc
    (fun n => (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).init))
  (exposeF : EncPolyTimeFam st.enc InterfaceBitEnc.coin.encQuery.enc
    (fun n => (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).expose))
  (updateF : EncPolyTimeFam (st.pairVar InterfaceBitEnc.coin.encAns).enc st.enc
    (fun n => (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).updateFlat))
  (outputF : EncPolyTimeFam st.enc (eβ.option).enc
    (fun n => (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)).output))

/-- The bounded coin fold as a `MachineAdversary`, from supplied step-function machine
families: the coalgebraic fields are discharged by the `coinFoldMachine` lemmas, the
machine fields are the hypotheses. -/
noncomputable def coinFoldAdversaryOfWitnesses :
    MachineAdversary (BoundaryData.coin BitEncFam.unit eβ) where
  M n := coinFoldMachine (step n) (readout n) (rnd n) (init₀ n)
  steps := steps
  stable n := coinFoldMachine_stableOutput (step n) (readout n) (rnd n) (init₀ n)
  state := st
  initF := initF
  exposeF := exposeF
  updateF := updateF
  outputF := outputF

/-- The witness-parameterized fold adversary certifies the fold program family. -/
noncomputable def coinFoldWitnessOfWitnesses :
    PolyTimeWitness (BoundaryData.coin BitEncFam.unit eβ)
      (fun n (_ : Unit) => coinFoldProg (step n) (readout n) (rnd n) (init₀ n)) where
  A := coinFoldAdversaryOfWitnesses step readout init₀ rnd steps st eβ
    initF exposeF updateF outputF
  implements n := by
    show coinFoldMachine (step n) (readout n) (rnd n) (init₀ n) ⊨[steps.eval n]
      fun _ => coinFoldProg (step n) (readout n) (rnd n) (init₀ n)
    rw [← hrnd n]
    exact coinFoldMachine_implements (step n) (readout n) (rnd n) (init₀ n)
  queryBound n _ := (isTotalQueryBound_coinFoldProg (step n) (readout n) (rnd n)
    (init₀ n)).mono (le_of_eq (hrnd n))

include steps hrnd st initF exposeF updateF outputF in
/-- **The bounded coin fold is polynomial time, given machine families for its step
functions** — the honest hypothesis form for folds into accumulators of superpolynomial
cardinality, where the table witnesses of `isPolyTime_coinFold` would smuggle
superpolynomial advice. -/
theorem isPolyTime_coinFold_of_witnesses :
    OracleComp.IsPolyTime (BoundaryData.coin BitEncFam.unit eβ)
      (fun n (_ : Unit) => coinFoldProg (step n) (readout n) (rnd n) (init₀ n)) :=
  ⟨coinFoldWitnessOfWitnesses step readout init₀ rnd steps hrnd st eβ
    initF exposeF updateF outputF⟩

end AdversaryOfWitnesses

end OracleComp
