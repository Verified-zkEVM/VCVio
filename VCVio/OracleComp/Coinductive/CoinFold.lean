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
encoding-length bounds — no hand-built `OracleMachine`/`MachineAdversary` needed.

* `coinFoldProg` — the fold program; `coinFoldMachine` — the machine realizing it, with
  the read-out map folded into `output` and the round counter as `Fin (rounds + 1)`.
* `coinFoldMachine_implementsWithin` — the machine implements the program family within
  `rounds` rounds, by a direct induction on the fuelled unrolling (returns are absorbing
  by construction, so no separate stability argument is needed).
* `coinFoldAdversary` / `coinFoldWitness` / `isPolyTime_coinFold` — the fully assembled
  `MachineAdversary`, its certificate, and `OracleComp.IsPolyTime`, with all four step
  witnesses discharged by finite tables for accumulators of polynomially bounded
  cardinality; the `…OfWitnesses` variants accept explicit machine families for
  superpolynomially large accumulators.

Specialized to `coinSpec` (the coin oracle, answers `Bool`): this keeps the simulation
free of the dependent answer-type transport that an arbitrary-spec version would incur.
Generalizing the fold to an arbitrary oracle is future work.
-/

open OracleSpec OracleComp Computability

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

/-- Build a machine from a one-step transition returning either a value or a query
with an explicit continuation, together with an initialization. Generic over the
spec; upstream candidate for `DynComputation`. Reducible so that the state type of a
machine built from it is transparently the supplied carrier. -/
@[reducible] def OracleMachine.ofStep {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β S : Type}
    (stepFn : S → β ⊕ spec.toPFunctor.Obj S) (init : α → S) :
    OracleMachine spec α β where
  State := S
  toDynSystem :=
    (fun s => (PFunctor.Resumption.pack (stepFn s)).1) ⇆
      (fun s => (PFunctor.Resumption.pack (stepFn s)).2)
  init := init

@[simp] theorem OracleMachine.view_ofStep {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {α β S : Type} (stepFn : S → β ⊕ spec.toPFunctor.Obj S) (init : α → S) (s : S) :
    (OracleMachine.ofStep (α := α) stepFn init).view s = stepFn s := by
  change PFunctor.Resumption.unpack (PFunctor.Resumption.pack (stepFn s)) = stepFn s
  cases stepFn s <;> rfl

/-- The fold machine: state `(remaining rounds, accumulator)`; each step decrements the
counter and folds the answer at the next index; at zero rounds it returns `readout` of
the accumulator (returns are absorbing by construction). Reducible so that the state
type stays transparently `Fin (rounds + 1) × σ` for the encoding witnesses. -/
@[reducible] def coinFoldMachine (rounds : ℕ) (init₀ : σ) : OracleMachine coinSpec Unit β :=
  OracleMachine.ofStep (S := Fin (rounds + 1) × σ)
    (fun s =>
      if _h : (s.1 : ℕ) = 0 then Sum.inl (readout s.2)
      else Sum.inr ⟨(), fun b =>
        (⟨(s.1 : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) s.1.isLt⟩,
          step s.2 ((s.1 : ℕ) - 1) b)⟩)
    (fun _ => (Fin.last rounds, init₀))

theorem coinFoldMachine_view_zero (rounds : ℕ) (init₀ : σ)
    {s : Fin (rounds + 1) × σ} (hs : (s.1 : ℕ) = 0) :
    (coinFoldMachine step readout rounds init₀).view s = Sum.inl (readout s.2) := by
  rw [OracleMachine.view_ofStep, dif_pos hs]

theorem coinFoldMachine_view_succ (rounds : ℕ) (init₀ : σ)
    {s : Fin (rounds + 1) × σ} (hs : ¬(s.1 : ℕ) = 0) :
    (coinFoldMachine step readout rounds init₀).view s =
      Sum.inr ⟨(), fun b =>
        (⟨(s.1 : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) s.1.isLt⟩,
          step s.2 ((s.1 : ℕ) - 1) b)⟩ := by
  rw [OracleMachine.view_ofStep, dif_neg hs]

/-- The fuelled unrolling from a state with `m` rounds remaining is the fold program
at `m`, for any sufficient fuel. -/
theorem coinFoldMachine_unroll (rounds : ℕ) (init₀ : σ) :
    ∀ (m k : ℕ) (hm : m ≤ rounds) (acc : σ), m ≤ k →
      (coinFoldMachine step readout rounds init₀).unroll k
          (⟨m, Nat.lt_succ_of_le hm⟩, acc) =
        PFunctor.FreeM.map some (coinFoldProg step readout m acc)
  | 0, k, hm, acc, _ => by
    rw [(coinFoldMachine step readout rounds init₀).unroll_return k _ (readout acc)
      (coinFoldMachine_view_zero step readout rounds init₀ rfl)]
    rfl
  | m + 1, 0, hm, acc, hk => absurd hk (by omega)
  | m + 1, k + 1, hm, acc, hk => by
    rw [(coinFoldMachine step readout rounds init₀).unroll_query_succ k _ () _
      (coinFoldMachine_view_succ step readout rounds init₀ (s := ⟨_, acc⟩) (by simp))]
    exact congrArg (PFunctor.FreeM.liftBind ())
      (funext fun b => coinFoldMachine_unroll rounds init₀ m k (by omega)
        (step acc m b) (by omega))

/-- The fold machine implements the fold program family within `rounds` rounds, by a
direct induction on the fuelled unrolling: returns are absorbing by construction, and
resolution within the budget is derivable via
`DynComputation.ImplementsWithin.resolvesIn`. -/
theorem coinFoldMachine_implementsWithin (rounds : ℕ) (init₀ : σ) :
    (coinFoldMachine step readout rounds init₀).ImplementsWithin
      (fun _ : Unit => coinFoldProg step readout rounds init₀) rounds := fun _ =>
  coinFoldMachine_unroll step readout rounds init₀ rounds rounds le_rfl init₀ le_rfl

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
        change Fintype.card ((Fin (rnd n + 1) × σ n) × ((t : Unit) × coinSpec.Range t)) ≤ _
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
    change PFunctor.DynSystem.DynComputation.ImplementsWithin
      (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n))
      (fun _ => coinFoldProg (step n) (readout n) (rnd n) (init₀ n)) (steps.eval n)
    rw [← hrnd n]
    exact coinFoldMachine_implementsWithin (step n) (readout n) (rnd n) (init₀ n)

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
    change PFunctor.DynSystem.DynComputation.ImplementsWithin
      (coinFoldMachine (step n) (readout n) (rnd n) (init₀ n))
      (fun _ => coinFoldProg (step n) (readout n) (rnd n) (init₀ n)) (steps.eval n)
    rw [← hrnd n]
    exact coinFoldMachine_implementsWithin (step n) (readout n) (rnd n) (init₀ n)

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
