/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Classical
public import VCVio.Quantum.Oracle.Comb

/-!
# Quantum oracle regression tests

Oracles `Fin 2 → Fin 2`, queried on the register `Fin 2 × Fin 2`.

* **Deutsch's algorithm**, as a one-query comb, reports `H 0 + H 1` with certainty. Its program
  (`Quantum.QuantumComb.toComp`) runs as the comb does (Proposition 1), with one call.
* **Classical algorithms.** The program of the algorithm that queries `0` reports `H 0`; its law
  in the quantum random-oracle model is its law under the lazily sampled random oracle, with no
  query bound. The adaptive algorithm that queries `H 0` next reports `H (H 0)`. Running the
  program of a sequenced algorithm is sequencing the runs (`Quantum.QuantumRuntime.run_bind`).
* **An adaptive program** measures a bit and calls the oracle only when it reads `1`: it has
  budget one, and not budget zero.
* **An ancilla** is allocated, carried through a call as the remainder of the register, and
  discarded.
* **Two ports.** A program calling each port once has budget one per port, and not budget one
  on one port alone. A program that calls only one port runs in the same way whatever the other
  port does.
* **A stateful runtime.** The counting runtime of the design note's Proposition 3 counts the
  calls in its private register. A program that flips a coin and calls twice on heads and once
  on tails leaves the counter at `2` or `1` according to the coin; a comb with a fixed number of
  slots cannot.
* **Guessing without queries.** A lossless program with budget zero, over any primitive
  signature and interpretation, guesses a point of a uniformly sampled oracle with probability
  `1 / 2`, whether it returns its guess on a fixed final register or reads it off a leaf whose
  register depends on the outcome.
* **A register that depends on an outcome.** A program calls the oracle with an ancilla as the
  remainder, measures the ancilla and keeps it on `0` or discards it on `1`, so that its final
  register depends on the outcome. Against the oracle unitary it is lossless, makes one call, and
  keeps the trace of its input; on `|x, y, 0⟩` it ends in `|x, y + H x, 0⟩` on the register with
  the ancilla, and on `|x, y, 1⟩` in `|x, y + H x⟩` on the register without it. Its law in the
  quantum random-oracle model has total mass the trace of its input.
* **Infinitely many outcomes.** The geometric distribution over `ℕ`, a dependent subinstrument on
  the trivial register with outcome `n` of weight `2⁻¹ ^ (n + 1)`, is lossless; a program that
  draws from it reaches the leaf of `n` with that weight, and keeps the trace of its input.
* **Higher universes.** A measurement whose outcomes lie in `Type 1`, and a program whose leaves
  (its final registers) lie in `Type 1`, run against the oracle unitary and keep the trace of
  their input.
* **A gate set.** A primitive signature of two named gates, interpreted by the bit flip and the
  phase flip: the bit flip moves `|0⟩` to `|1⟩` and the phase flip moves `|+⟩` to `|-⟩`. A
  program applying both uses two gates and not one, and runs to a lossless subinstrument.
* **The fixed-register run.** The run of the coin program as a fixed-register program is the run
  of its tree read at the leaf on its final register; Proposition 3 holds for both.
-/

public section

open Quantum Matrix MeasureTheory OracleSpec
open scoped ComplexOrder ENNReal Kronecker

namespace VCVioTest.QuantumOracle

/-- The random-oracle signature for oracles `Fin 2 → Fin 2`. It is noncomputable: it is only used
in types and noncomputable programs, and is not evaluated when the module is loaded. -/
noncomputable abbrev qrom2 : QuantumOracleSpec :=
  qromSpec (Fin 2) (Fin 2)

/-! ## Deutsch's algorithm -/

/-- The register of Deutsch's algorithm: one query qubit and one response qubit. -/
abbrev Reg : Type := Fin 2 × Fin 2

/-- The sign `(-1) ^ y` of a bit. -/
def sgn (y : Fin 2) : ℂ :=
  if y = 0 then 1 else -1

/-- The amplitudes of the state `|+⟩|-⟩`. -/
noncomputable def amp : Reg → ℂ :=
  fun m ↦ sgn m.2 / 2

/-- The projector onto `|+⟩` (for `b = 0`) or `|-⟩` (for `b = 1`) of the query qubit. -/
noncomputable def proj (b : Fin 2) : Matrix Reg Reg ℂ :=
  Matrix.of fun m m' ↦ if m.2 = m'.2 then sgn (b * (m.1 + m'.1)) / 2 else 0

theorem eq_zero_or_one (a : Fin 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> simp

/-- The projectors onto `|+⟩` and `|-⟩` satisfy the completeness relation. -/
theorem sum_conjTranspose_proj_mul_proj : ∑ b, (proj b)ᴴ * proj b = 1 := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  rcases eq_zero_or_one x with rfl | rfl <;> rcases eq_zero_or_one y with rfl | rfl <;>
    rcases eq_zero_or_one x' with rfl | rfl <;> rcases eq_zero_or_one y' with rfl | rfl <;>
    norm_num [Fin.sum_univ_two, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type, proj,
      sgn, map_ofNat]

/-- The state `|+⟩|-⟩`. -/
noncomputable def plusMinus : SubState Reg where
  matrix := vecMulVec amp (star amp)
  posSemidef := Matrix.posSemidef_vecMulVec_self_star amp
  trace_re_le_one := by
    norm_num [Matrix.trace, vecMulVec_apply, Fintype.sum_prod_type, Fin.sum_univ_two, amp, sgn]

/-- Deutsch's algorithm: start in `|+⟩|-⟩`, query once, and measure the query qubit in the
`|±⟩` basis. -/
noncomputable def deutsch : QuantumComb Reg (Fin 2) 1 where
  init := plusMinus
  step _ := SubInstrument.pure ()
  lossless_step _ := SubInstrument.lossless_pure ()
  final := SubInstrument.ofKraus proj sum_conjTranspose_proj_mul_proj
  lossless_final := SubInstrument.lossless_ofKraus _ _

/-- The weight of a Kraus branch on a pure state is the squared norm of the image vector. -/
theorem trace_conj_vecMulVec {A B : Type} [Fintype A] [Fintype B] (K : Matrix B A ℂ)
    (v : A → ℂ) :
    (MatrixMap.conj K (vecMulVec v (star v))).trace = ∑ i, (K *ᵥ v) i * star ((K *ᵥ v) i) := by
  rw [MatrixMap.conj_apply, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec,
    Matrix.trace_vecMulVec]
  rfl

/-- After the query, the measurement reports `H 0 + H 1` with weight one. -/
theorem trace_conj_proj (H : Fin 2 → Fin 2) (b : Fin 2) :
    (MatrixMap.conj (proj b)
      (MatrixMap.conj (oracleUnitary H) (vecMulVec amp (star amp)))).trace =
      if b = H 0 + H 1 then 1 else 0 := by
  have h : MatrixMap.conj (oracleUnitary H) (vecMulVec amp (star amp)) =
      vecMulVec (fun m ↦ amp ((oracleEquiv H).symm m))
        (star fun m ↦ amp ((oracleEquiv H).symm m)) := by
    rw [oracleUnitary, conj_basisMatrix_equiv]
    rfl
  rw [h, trace_conj_vecMulVec]
  rcases eq_zero_or_one (H 0) with h0 | h0 <;> rcases eq_zero_or_one (H 1) with h1 | h1 <;>
    rcases eq_zero_or_one b with rfl | rfl <;>
    norm_num [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, proj, amp, sgn,
      oracleEquiv_symm_apply, h0, h1]

/-- Deutsch's algorithm reports `H 0 + H 1` with certainty. -/
theorem outcomeMeasure_deutsch (H : Fin 2 → Fin 2) :
    (deutsch.run (oracleQuery H)).outcomeMeasure deutsch.init = Measure.dirac (H 0 + H 1) := by
  rw [QuantumComb.outcomeMeasure_run, show Fin.last 1 = (0 : Fin 1).succ from rfl,
    QuantumComb.stateAfterStep_succ]
  change deutsch.final.outcomeMeasure ((SubInstrument.pure ()).post
    ((oracleQuery H).post ((SubInstrument.pure ()).post plusMinus ()) ()) ()) = _
  rw [SubInstrument.post_pure_self, SubInstrument.post_pure_self,
    SubInstrument.outcomeMeasure_eq_sum_univ, Fin.sum_univ_two]
  have h : ∀ b, (deutsch.final.branch b ((oracleQuery H).post plusMinus ()).matrix).trace =
      if b = H 0 + H 1 then 1 else 0 := fun b ↦ by
    have h₁ : ((oracleQuery H).post plusMinus ()).matrix =
        MatrixMap.conj (oracleUnitary H) (vecMulVec amp (star amp)) := by
      simp [MatrixMap.conj_apply, plusMinus]
    rw [h₁]
    change ((SubInstrument.ofKraus proj sum_conjTranspose_proj_mul_proj).branch b _).trace = _
    rw [SubInstrument.branch_ofKraus_apply]
    exact trace_conj_proj H b
  rw [h, h]
  rcases eq_zero_or_one (H 0) with h0 | h0 <;> rcases eq_zero_or_one (H 1) with h1 | h1 <;>
    simp [h0, h1]

/-- On a constant oracle, Deutsch's algorithm reports `0` with certainty. -/
example (H : Fin 2 → Fin 2) (h : H 0 = H 1) :
    (deutsch.run (oracleQuery H)).outcomeMeasure deutsch.init {0} = 1 := by
  rcases eq_zero_or_one (H 1) with h1 | h1 <;> simp [outcomeMeasure_deutsch, h, h1]

/-- On a balanced oracle, Deutsch's algorithm reports `1` with certainty. -/
example (H : Fin 2 → Fin 2) (h : H 0 ≠ H 1) :
    (deutsch.run (oracleQuery H)).outcomeMeasure deutsch.init {1} = 1 := by
  rcases eq_zero_or_one (H 0) with h0 | h0 <;> rcases eq_zero_or_one (H 1) with h1 | h1 <;>
    simp [outcomeMeasure_deutsch, h0, h1] at h ⊢

/-- Deutsch's algorithm as a program over the random-oracle signature: its call goes to the
whole register, with the trivial remainder. -/
noncomputable def deutschComp : QComp qrom2 (QReg.of Reg) (QReg.of Reg) (Fin 2) :=
  deutsch.toComp () (QReg.of Unit) (Equiv.prodPUnit Reg).symm (Equiv.prodPUnit Reg)

/-- **Proposition 1** for Deutsch's algorithm: against the oracle runtime, the program runs as the
comb, framed by the runtime register, against the runtime's query step. -/
example (H : Fin 2 → Fin 2) :
    (xorRuntime H).run₂ .instruments deutschComp =
      (deutsch.frame (xorRuntime H).D (xorRuntime H).init).run
        ((xorRuntime H).combQuery () (QReg.of Unit) (Equiv.prodPUnit Reg).symm
          (Equiv.prodPUnit Reg)) :=
  QuantumComb.run_toComp ..

/-- The program of Deutsch's algorithm makes one call, and is lossless. -/
example :
    deutschComp.IsQueryBound (Pi.single (() : qrom2.Port) 1) ∧ deutschComp.Lossless .instruments :=
  ⟨deutsch.isQueryBound_toComp (spec := qrom2) () _ _ _,
    deutsch.lossless_toComp (spec := qrom2) () _ _ _⟩

/-! ## Classical algorithms -/

/-- The classical algorithm that queries the oracle at `0` and returns the answer. -/
def queryZero : OracleComp (Fin 2 →ₒ Fin 2) (Fin 2) :=
  liftM ((Fin 2 →ₒ Fin 2).query 0)

/-- The algorithm makes at most one query. -/
theorem isTotalQueryBound_queryZero : OracleComp.IsTotalQueryBound queryZero 1 := by
  rw [queryZero, ← bind_pure (liftM _), OracleComp.isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.one_pos, fun _ ↦ trivial⟩

/-- Against the oracle unitary of `H`, the program of the algorithm reports `H 0` with
certainty. -/
example (H : Fin 2 → Fin 2) :
    (xorRuntime H).outcomeLaw₂ .instruments queryZero.toQuantum (SubState.basis ()) =
      Measure.dirac (H 0) :=
  outcomeLaw_xorRuntime_toQuantum H queryZero

/-- The program makes one call. -/
example : queryZero.toQuantum.IsQueryBound fun _ ↦ 1 :=
  OracleComp.isQueryBound_toQuantum isTotalQueryBound_queryZero

/-- The law of the program in the quantum random-oracle model is the law of the algorithm under
the lazily sampled random oracle; no query bound is used. -/
example :
    qromLaw₂ .instruments queryZero.toQuantum (SubState.basis ()) =
      𝒟[(simulateQ randomOracle queryZero).run' ∅] :=
  qromLaw₂_toQuantum_eq_randomOracle queryZero

/-- The adaptive algorithm that queries `0`, and then queries the answer. -/
def queryTwice : OracleComp (Fin 2 →ₒ Fin 2) (Fin 2) := do
  let y ← liftM ((Fin 2 →ₒ Fin 2).query 0)
  liftM ((Fin 2 →ₒ Fin 2).query y)

/-- Its program, whose second call depends on the measured result of the first, reports
`H (H 0)` with certainty. -/
example (H : Fin 2 → Fin 2) :
    (xorRuntime H).outcomeLaw₂ .instruments queryTwice.toQuantum (SubState.basis ()) =
      Measure.dirac (H (H 0)) :=
  outcomeLaw_xorRuntime_toQuantum H queryTwice

/-- Running the program of a sequenced algorithm is sequencing the runs of the programs. -/
example {α β : Type} (H : Fin 2 → Fin 2) (oa : OracleComp (Fin 2 →ₒ Fin 2) α)
    (f : α → OracleComp (Fin 2 →ₒ Fin 2) β) :
    (xorRuntime H).run₂ .instruments (oa >>= f).toQuantum =
      ((xorRuntime H).run₂ .instruments oa.toQuantum).bind fun a ↦
        (xorRuntime H).run₂ .instruments (f a).toQuantum := by
  rw [OracleComp.toQuantum, simulateQ_bind]
  exact QuantumRuntime.run₂_bind _ _ _ _

/-! ## An adaptive program -/

/-- Measure the query bit; on `1`, call the oracle and return to the register `Fin 2 × Fin 2`;
then return the bit. The number of calls depends on the measured outcome. -/
noncomputable def callIfOne : QComp qrom2 (QReg.of Reg) (QReg.of Reg) (Fin 2) :=
  (QComp.act (A := QReg.of Reg) (B := QReg.of Reg)
      (SubInstrument.classical id fun m : Reg ↦ m.1)).bind fun b ↦
    if b = 1 then
      ((QuantumComp₂.query (L := LocalSig.instruments) () (QReg.of Unit)
          (Equiv.prodPUnit Reg).symm).bind fun _ ↦
        QComp.act (B := QReg.of Reg) (SubInstrument.relabel (Equiv.prodPUnit Reg))).bind
          fun _ ↦ QuantumComp₂.pure b
    else QuantumComp₂.pure b

/-- The adaptive program makes at most one call on every path. -/
example : callIfOne.IsQueryBound fun _ ↦ 1 := by
  rw [callIfOne, QComp.isQueryBound_act_bind_iff]
  intro b
  split_ifs
  · refine (QuantumComp₂.isQueryBound_bind (QuantumComp₂.isQueryBound_bind
      ((QuantumComp₂.isQueryBound_query_iff _ _ _ (fun _ ↦ 1)).mpr Nat.one_pos)
        fun _ ↦ QComp.isQueryBound_act _ 0) (b₂ := 0)
          fun _ ↦ QuantumComp₂.isQueryBound_pure _ _).mono fun _ ↦ ?_
    simp
  · exact QuantumComp₂.isQueryBound_pure _ _

/-- The adaptive program calls the oracle on the path where it reads `1`. -/
example : ¬ callIfOne.IsQueryBound 0 := by
  intro h
  rw [callIfOne, QComp.isQueryBound_act_bind_iff] at h
  have h₁ := h 1
  simp only [↓reduceIte] at h₁
  rw [QuantumComp₂.bind_assoc, QuantumComp₂.query_bind] at h₁
  exact Nat.lt_irrefl 0 (QuantumComp.IsQueryBound.of_queryBind h₁).1

/-! ## Allocating and discarding an ancilla -/

/-- Allocate an ancilla qubit in `|0⟩`: the isometry `|a⟩ ↦ |a, 0⟩`. -/
noncomputable def alloc (A : Type) [Fintype A] [DecidableEq A] : SubInstrument A (A × Fin 2) Unit :=
  SubInstrument.ofIsometry (basisMatrix fun a : A ↦ (a, (0 : Fin 2)))
    (conjTranspose_basisMatrix_mul_self fun _ _ h ↦ congrArg Prod.fst h)

/-- The Kraus operators `1 ⊗ ⟨r|` of the partial trace over an ancilla qubit. -/
def discardKraus (A : Type) [DecidableEq A] (r : Fin 2) : Matrix A (A × Fin 2) ℂ :=
  Matrix.of fun a p ↦ if p = (a, r) then 1 else 0

/-- The Kraus operators of the partial trace satisfy the completeness relation. -/
theorem sum_discardKraus (A : Type) [Fintype A] [DecidableEq A] :
    ∑ r, (discardKraus A r)ᴴ * discardKraus A r = 1 := by
  ext ⟨a, s⟩ ⟨a', s'⟩
  rw [Matrix.sum_apply, Matrix.one_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, discardKraus, Matrix.of_apply,
    Prod.mk.injEq, apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single s (fun r _ hr ↦ by simp [Ne.symm hr]) (by simp),
    Finset.sum_eq_single a (fun x _ hx ↦ by simp [Ne.symm hx]) (by simp)]
  by_cases ha : a' = a
  · subst ha
    by_cases hs : s' = s
    · subst hs
      simp
    · simp [hs, Ne.symm hs]
  · simp [ha, Ne.symm ha]

/-- Discard an ancilla qubit: the partial trace over it. -/
noncomputable def discard (A : Type) [Fintype A] [DecidableEq A] :
    SubInstrument (A × Fin 2) A Unit :=
  (SubInstrument.ofKraus (discardKraus A) (sum_discardKraus A)).map fun _ ↦ ()

/-- Allocate an ancilla, call the oracle with the ancilla as the remainder of the register, and
discard the ancilla. -/
noncomputable def queryWithAncilla : QComp qrom2 (QReg.of Reg) (QReg.of Reg) Unit :=
  (QComp.act (B := QReg.of (Reg × Fin 2)) (alloc Reg)).bind fun _ ↦
    (QuantumComp₂.query (L := LocalSig.instruments) () (QReg.of (Fin 2))
        (Equiv.refl (Reg × Fin 2))).bind fun _ ↦
      QComp.act (B := QReg.of Reg) (discard Reg)

/-- The program with an ancilla is lossless and makes one call. -/
theorem lossless_queryWithAncilla : queryWithAncilla.Lossless .instruments :=
  QuantumComp₂.lossless_bind (QComp.lossless_act (SubInstrument.lossless_ofIsometry _ _)) fun _ ↦
    QuantumComp₂.lossless_bind (QuantumComp₂.lossless_query _ _ _) fun _ ↦
      QComp.lossless_act ((SubInstrument.lossless_ofKraus _ _).map _)

example : queryWithAncilla.IsQueryBound fun _ ↦ 1 := by
  rw [queryWithAncilla, QComp.isQueryBound_act_bind_iff]
  intro _
  exact (QuantumComp₂.isQueryBound_bind
    ((QuantumComp₂.isQueryBound_query_iff _ _ _ (fun _ ↦ 1)).mpr Nat.one_pos)
      fun _ ↦ QComp.isQueryBound_act _ 0).mono fun _ ↦ le_of_eq (add_zero _)

/-- Against the oracle unitary, the program with an ancilla keeps the trace of its input. -/
example (H : Fin 2 → Fin 2) (ρ : SubState (QReg.of Reg)) :
    (xorRuntime H).outcomeLaw₂ .instruments queryWithAncilla ρ Set.univ =
      ENNReal.ofReal ρ.matrix.trace.re := by
  rw [(xorRuntime H).outcomeLaw₂_apply_univ_of_lossless .instruments
    (lossless_run₂_xorRuntime .instruments lossless_queryWithAncilla H),
    trace_re_xorRuntime_init, mul_one]

/-! ## Two ports -/

/-- Two oracles `Fin 2 → Fin 2`, one on each port. It is noncomputable: it is only used in types
and noncomputable programs, and is not evaluated when the module is loaded. -/
@[expose, reducible]
noncomputable def twoSpec : QuantumOracleSpec where
  Port := Bool
  In _ := QReg.of Reg
  Out _ := QReg.of Reg
  Result _ := Unit

/-- The runtime that answers port `true` with the oracle unitary of `H` and port `false` with that
of `G`. -/
@[expose]
noncomputable def twoXor (H G : Fin 2 → Fin 2) : QuantumRuntime twoSpec where
  D := QReg.of Unit
  init := SubState.basis ()
  step b := (oracleQuery (cond b H G)).frame Unit

/-- Call port `true`, then port `false`. -/
noncomputable def callBoth : QComp twoSpec (QReg.of Reg) (QReg.of (Reg × Unit)) Unit :=
  (QuantumComp₂.query (L := LocalSig.instruments) true (QReg.of Unit)
      (Equiv.prodPUnit Reg).symm).bind fun _ ↦
    QuantumComp₂.query false (QReg.of Unit) (Equiv.refl (Reg × Unit))

/-- The program calls each port once. -/
example : callBoth.IsQueryBound fun _ ↦ 1 := by
  refine (QuantumComp₂.isQueryBound_bind (spec := twoSpec) (b₁ := Pi.single true 1)
    (b₂ := Pi.single false 1)
    ((QuantumComp₂.isQueryBound_query_iff _ _ _ _).mpr (by simp))
    fun _ ↦ (QuantumComp₂.isQueryBound_query_iff _ _ _ _).mpr (by simp)).mono fun b ↦ ?_
  cases b <;> simp

/-- A budget on port `true` alone does not cover the call of port `false`. -/
example : ¬ callBoth.IsQueryBound (Pi.single (true : twoSpec.Port) 1) := by
  intro h
  rw [callBoth, QuantumComp₂.query_bind] at h
  have h₁ : (QuantumComp₂.query (L := LocalSig.instruments) (spec := twoSpec)
      (A := QReg.of (Reg × Unit)) false (QReg.of Unit)
      (Equiv.refl (Reg × Unit))).IsQueryBound (Pi.single (true : twoSpec.Port) 1) :=
    (QuantumComp.IsQueryBound.of_queryBind h).2 ()
  rw [QuantumComp₂.isQueryBound_query_iff] at h₁
  simp at h₁

/-- Call port `true` only. -/
noncomputable def callTrue : QComp twoSpec (QReg.of Reg) (QReg.of (Reg × Unit)) Unit :=
  QuantumComp₂.query true (QReg.of Unit) (Equiv.prodPUnit Reg).symm

/-- A program that calls only port `true` runs in the same way whatever port `false` does. -/
example (H G G' : Fin 2 → Fin 2) :
    (twoXor H G).run₂ .instruments callTrue = (twoXor H G').run₂ .instruments callTrue := by
  refine QuantumRuntime.run₂_congr_of_isQueryBound .instruments (D := QReg.of Unit)
    (σ₁ := SubState.basis ()) (σ₂ := SubState.basis ()) (s₁ := (twoXor H G).step)
    (s₂ := (twoXor H G').step) (b := Pi.single (true : twoSpec.Port) 1)
    ((QuantumComp₂.isQueryBound_query_iff _ _ _ _).mpr (by simp)) fun i hi ↦ ?_
  cases i
  · simp at hi
  · rfl

/-! ## A stateful runtime -/

/-- One port with trivial registers: a call only acts on the runtime's private register. -/
@[expose, reducible]
def countSpec : QuantumOracleSpec where
  Port := Unit
  In _ := QReg.of Unit
  Out _ := QReg.of Unit
  Result _ := Unit

/-- Count one more call, saturating at `2`. -/
@[expose]
def tick (d : Fin 3) : Fin 3 :=
  if d = 2 then 2 else d + 1

/-- **The counting runtime.** Its private register `Fin 3` starts at `0` and counts the calls,
saturating at `2`. It is reducible, so that its register unfolds to `Fin 3` when rewriting. -/
@[expose, reducible]
noncomputable def countRuntime : QuantumRuntime countSpec where
  D := QReg.of (Fin 3)
  init := SubState.basis 0
  step _ := SubInstrument.classical (fun m : Unit × Fin 3 ↦ ((), tick m.2)) fun _ ↦ ()

/-- A call of the counting runtime on a basis state advances the counter. -/
theorem countRuntime_step_branch_single (d : Fin 3) :
    (countRuntime.step ()).branch () (Matrix.single ((), d) ((), d) 1) =
      Matrix.single ((), tick d) ((), tick d) 1 :=
  (SubInstrument.branch_classical_basis (fun m : Unit × Fin 3 ↦ ((), tick m.2)) (fun _ ↦ ())
    ((), d) ()).trans (by simp)

/-- Measure a coin; call twice on heads (`1`) and once on tails (`0`); return the coin. -/
@[expose]
noncomputable def coinProg :
    QComp countSpec (QReg.of (Fin 2)) (QReg.of (Unit × Fin 2)) (Fin 2) :=
  (QComp.act (A := QReg.of (Fin 2)) (B := QReg.of (Fin 2))
      (SubInstrument.classical id id)).bind fun b ↦
    (QuantumComp₂.query (L := LocalSig.instruments) () (QReg.of (Fin 2))
        (Equiv.punitProd (Fin 2)).symm).bind fun _ ↦
      if b = 1 then
        (QuantumComp₂.query () (QReg.of (Fin 2)) (Equiv.refl (Unit × Fin 2))).bind fun _ ↦
          QuantumComp₂.pure b
      else QuantumComp₂.pure b

/-- The coin program makes at most two calls on every path. -/
example : coinProg.IsQueryBound fun _ ↦ 2 := by
  rw [coinProg, QComp.isQueryBound_act_bind_iff]
  intro b
  refine (QuantumComp₂.isQueryBound_bind (b₁ := fun _ ↦ 1) (b₂ := fun _ ↦ 1)
    ((QuantumComp₂.isQueryBound_query_iff _ _ _ _).mpr Nat.one_pos) fun _ ↦ ?_).mono
      fun _ ↦ le_refl _
  split_ifs
  · exact QuantumComp₂.isQueryBound_bind (b₂ := 0)
      ((QuantumComp₂.isQueryBound_query_iff _ _ _ _).mpr Nat.one_pos)
      (fun _ ↦ QuantumComp₂.isQueryBound_pure _ _) |>.mono fun _ ↦ le_of_eq (add_zero _)
  · exact QuantumComp₂.isQueryBound_pure _ _

/-- The run of the coin program on a basis state `|b, d⟩`. -/
theorem run_coinProg_branch_single (b c : Fin 2) (d : Fin 3) :
    (countRuntime.run₂ .instruments coinProg).branch c (Matrix.single (b, d) (b, d) 1) =
      if b = c then
        Matrix.single (((), b), if b = 1 then tick (tick d) else tick d)
          (((), b), if b = 1 then tick (tick d) else tick d) 1
      else 0 := by
  rw [coinProg, QuantumRuntime.run₂_act_bind, SubInstrument.branch_bind_apply_univ,
    LinearMap.sum_apply, Finset.sum_eq_single b (fun b' _ hb' ↦ ?_) (by simp),
    LinearMap.comp_apply, SubInstrument.branch_frame_single, SubInstrument.branch_classical_basis]
  · simp only [id, ↓reduceIte, Matrix.single_kronecker_single, one_mul]
    rw [QuantumRuntime.run₂_query_bind, SubInstrument.branch_bind_unit, LinearMap.comp_apply,
      QuantumRuntime.queryStep_branch_single, Equiv.punitProd_symm_apply,
      countRuntime_step_branch_single, Matrix.single_kronecker_single, one_mul,
      SubInstrument.branch_relabel, conj_basisMatrix_equiv_single,
      QuantumRuntime.queryEquivOut_apply]
    rcases eq_zero_or_one b with rfl | rfl
    · simp [SubInstrument.branch_pure, Pi.single_apply]
      split_ifs <;> simp_all
    · simp only [↓reduceIte]
      rw [QuantumRuntime.run₂_query_bind, SubInstrument.branch_bind_unit, LinearMap.comp_apply,
        QuantumRuntime.queryStep_branch_single, Equiv.refl_apply,
        countRuntime_step_branch_single, Matrix.single_kronecker_single, one_mul,
        SubInstrument.branch_relabel, conj_basisMatrix_equiv_single,
        QuantumRuntime.queryEquivOut_apply]
      simp [SubInstrument.branch_pure, Pi.single_apply]
      split_ifs <;> simp_all
  · rw [LinearMap.comp_apply, SubInstrument.branch_frame_single,
      SubInstrument.branch_classical_basis]
    simp [Ne.symm hb']

/-- **Proposition 3.** On heads the counting runtime ends at `2`, on tails at `1`: the final
state of its private register depends on the path of the program. A comb with a fixed number of
slots calls the same number of times on every path. -/
theorem jointPost₂_coinProg :
    countRuntime.jointPost₂ .instruments coinProg (SubState.basis 1) 1 =
        SubState.basis (((), 1), (2 : Fin 3)) ∧
      countRuntime.jointPost₂ .instruments coinProg (SubState.basis 0) 0 =
        SubState.basis (((), 0), (1 : Fin 3)) := by
  constructor <;>
  · refine SubState.ext ?_
    rw [QuantumRuntime.matrix_jointPost₂, SubState.matrix_basis, SubState.matrix_basis,
      SubState.matrix_basis, Matrix.single_kronecker_single, one_mul, run_coinProg_branch_single]
    rfl

/-! ## Guessing without queries -/

/-- A lossless program with budget zero, over any primitive signature and interpretation, started
in a state of trace one, guesses a point of the oracle with probability `1 / 2`. -/
example {L : LocalSig} (I : L.Interp) {A B : QReg} (x : QuantumComp₂ L qrom2 A B (Fin 2 × Fin 2))
    (hx : x.IsQueryBound 0) (hl : x.Lossless I) {ρ : SubState A} (h : ρ.matrix.trace = 1) :
    qromLawWith₂ I x ρ (fun H a ↦ a.2 = H a.1) {True} = 2⁻¹ := by
  simpa using qromLawWith₂_guess_zero_of_trace_eq_one I hx hl h

/-- The same for a general program, whose final register may depend on the outcome: a lossless
program with budget zero whose leaves carry guesses guesses a point of the oracle with probability
`1 / 2`. -/
example {L : LocalSig} (I : L.Interp) {W : QReg → Type} {A : QReg}
    (x : QuantumComp L qrom2 W A) (hx : x.IsQueryBound 0) (hl : x.Lossless I)
    (gx gy : (Σ u, W u) → Fin 2) {ρ : SubState A} (h : ρ.matrix.trace = 1) :
    qromLawWith I x ρ (fun H p ↦ gy p = H (gx p)) {True} = 2⁻¹ := by
  simpa using qromLawWith_guess_zero_of_trace_eq_one I hx hl gx gy h

/-! ## The fixed-register run is the general run -/

/-- The run of the coin program as a fixed-register program is the run of its tree, read at the
leaf on its final register `Unit × Fin 2`. -/
example (c : Fin 2) :
    (countRuntime.run₂ .instruments coinProg).branch c =
      (countRuntime.run .instruments coinProg).branch ⟨QReg.of (Unit × Fin 2), rfl, c⟩ :=
  QuantumRuntime.branch_run₂ ..

/-- **Proposition 3** on the general form: the joint post-measurement state of the tree at the
leaf on `Unit × Fin 2`. -/
example :
    countRuntime.jointPost .instruments coinProg (SubState.basis 1) ⟨_, rfl, 1⟩ =
        SubState.basis (((), 1), (2 : Fin 3)) ∧
      countRuntime.jointPost .instruments coinProg (SubState.basis 0) ⟨_, rfl, 0⟩ =
        SubState.basis (((), 0), (1 : Fin 3)) :=
  ⟨(QuantumRuntime.jointPost₂_eq_jointPost ..).symm.trans jointPost₂_coinProg.1,
    (QuantumRuntime.jointPost₂_eq_jointPost ..).symm.trans jointPost₂_coinProg.2⟩

/-! ## A register that depends on an outcome -/

/-- The register after measuring the ancilla of `Reg × Fin 2`: on `0` the ancilla is kept, on `1`
it is discarded. -/
@[expose, reducible]
def ancReg : Fin 2 → QReg
  | 0 => QReg.of (Reg × Fin 2)
  | 1 => QReg.of Reg

/-- Removing an ancilla in the state `|r⟩` after embedding it is the identity. -/
theorem discardKraus_mul_conjTranspose (A : Type) [Fintype A] [DecidableEq A] (r : Fin 2) :
    discardKraus A r * (discardKraus A r)ᴴ = 1 := by
  ext a a'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, discardKraus, Matrix.of_apply,
    apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul, Matrix.one_apply]
  rw [Finset.sum_eq_single (a, r) (fun p _ hp ↦ by simp [hp]) (by simp)]
  simp

/-- Keep the ancilla after reading `0`: the operator `1 ⊗ |0⟩⟨0|`. -/
def keepZero (A : Type) [Fintype A] [DecidableEq A] : Matrix (A × Fin 2) (A × Fin 2) ℂ :=
  (discardKraus A 0)ᴴ * discardKraus A 0

/-- Keeping the ancilla on `0` and discarding it on `1` satisfy the completeness relation. -/
theorem keepZero_discardKraus_complete (A : Type) [Fintype A] [DecidableEq A] :
    (keepZero A)ᴴ * keepZero A + (discardKraus A 1)ᴴ * discardKraus A 1 = 1 := by
  have h : (keepZero A)ᴴ * keepZero A = (discardKraus A 0)ᴴ * discardKraus A 0 := by
    rw [keepZero, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (discardKraus A 0), discardKraus_mul_conjTranspose, Matrix.one_mul]
  rw [h, ← sum_discardKraus A, Fin.sum_univ_two]

/-- The Kraus operators of the measurement that keeps the ancilla on `0` and discards it on
`1`. -/
def ancKraus : (b : Fin 2) → Matrix (ancReg b) (Reg × Fin 2) ℂ
  | 0 => keepZero Reg
  | 1 => discardKraus Reg 1

/-- The keep-or-discard Kraus operators satisfy the completeness relation. -/
theorem sum_ancKraus : ∑ b, (ancKraus b)ᴴ * ancKraus b = 1 := by
  rw [Fin.sum_univ_two]
  exact keepZero_discardKraus_complete Reg

/-- Measure the ancilla; keep it on `0` and discard it on `1`. Its output register depends on the
outcome. -/
noncomputable def measureAnc : DSubInstrument (Reg × Fin 2) (Fin 2) fun b ↦ ancReg b :=
  DSubInstrument.ofKraus ancKraus sum_ancKraus

/-- The keep-or-discard measurement of the ancilla is lossless. -/
theorem lossless_measureAnc : measureAnc.Lossless :=
  DSubInstrument.lossless_ofKraus _ _

/-- Call the oracle with an ancilla as the remainder of the register, then measure the ancilla
and keep it on `0` or discard it on `1`. The leaf of outcome `b` sits on the register
`ancReg b`. -/
noncomputable def queryKeepOrDiscard :
    QuantumComp LocalSig.instruments qrom2 (fun u ↦ {b : Fin 2 // ancReg b = u})
      (QReg.of (Reg × Fin 2)) :=
  QuantumComp.queryBind () (QReg.of (Fin 2)) (Equiv.refl (Reg × Fin 2)) fun _ ↦
    QuantumComp.prim (L := LocalSig.instruments) (spec := qrom2)
      (⟨Fin 2, ancReg, measureAnc⟩ : LocalSig.instruments.Op (QReg.of (Reg × Fin 2)))

/-- The program that keeps or discards the ancilla is lossless. -/
theorem lossless_queryKeepOrDiscard : queryKeepOrDiscard.Lossless .instruments :=
  (QuantumComp.lossless_queryBind_iff _ _ _ _).mpr fun _ ↦
    (QuantumComp.lossless_primBind_iff _ _).mpr
      ⟨lossless_measureAnc, fun _ ↦ trivial⟩

/-- The program that keeps or discards the ancilla makes one call. -/
theorem isQueryBound_queryKeepOrDiscard : queryKeepOrDiscard.IsQueryBound fun _ ↦ 1 :=
  (QuantumComp.isQueryBound_queryBind_iff (spec := qrom2) _ _ _ _ _).mpr
    ⟨Nat.one_pos, fun _ ↦ QuantumComp.isQueryBound_prim _ _⟩

/-- Against the oracle unitary, the program runs to a lossless dependent subinstrument. -/
example (H : Fin 2 → Fin 2) :
    ((xorRuntime H).run .instruments queryKeepOrDiscard).Lossless :=
  lossless_run_xorRuntime .instruments lossless_queryKeepOrDiscard H

/-- Against the oracle unitary, the program keeps the trace of its input, summed over both final
registers. -/
example (H : Fin 2 → Fin 2) (ρ : SubState (QReg.of (Reg × Fin 2))) :
    (xorRuntime H).outcomeLaw .instruments queryKeepOrDiscard ρ Set.univ =
      ENNReal.ofReal ρ.matrix.trace.re := by
  rw [(xorRuntime H).outcomeLaw_apply_univ_of_lossless .instruments
    (lossless_run_xorRuntime .instruments lossless_queryKeepOrDiscard H),
    trace_re_xorRuntime_init, mul_one]

/-- In the quantum random-oracle model, the law of the leaf of the program that keeps or discards
the ancilla, whose two leaves sit on different registers, has the trace of its input as total
mass. -/
example [MeasurableSpace (Σ u, {b : Fin 2 // ancReg b = u})]
    (ρ : SubState (QReg.of (Reg × Fin 2))) :
    qromLaw .instruments queryKeepOrDiscard ρ Set.univ = ENNReal.ofReal ρ.matrix.trace.re :=
  qromLaw_apply_univ_of_lossless lossless_queryKeepOrDiscard ρ

/-- Each branch of a framed dependent subinstrument on a product basis state acts on the first
factor and keeps the second. -/
theorem branch_frame_single {A : Type} [Fintype A] [DecidableEq A] {ι : Type} {B : ι → Type}
    [∀ i, Fintype (B i)] {R : Type} [Fintype R] [DecidableEq R] (p : DSubInstrument A ι B) (i : ι)
    (a : A) (r : R) :
    (p.frame R).branch i (Matrix.single (a, r) (a, r) 1) =
      p.branch i (Matrix.single a a 1) ⊗ₖ Matrix.single r r 1 := by
  rw [DSubInstrument.branch_frame_apply, ← MatrixMap.amplify_kronecker,
    Matrix.single_kronecker_single, one_mul]

/-- The Kraus map of `K` sends the basis projector `|a⟩⟨a|` to the projector onto the column of
`K` at `a`. -/
theorem conj_single_apply {A B : Type} [Fintype A] [DecidableEq A] (K : Matrix B A ℂ) (a : A)
    (b b' : B) : MatrixMap.conj K (Matrix.single a a 1) b b' = K b a * star (K b' a) := by
  simp only [MatrixMap.conj_apply, Matrix.mul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single a (fun c _ hc ↦ by simp [Ne.symm hc]) (by simp),
    Finset.sum_eq_single a (fun c _ hc ↦ by simp [Ne.symm hc]) (by simp)]
  simp

/-- Removing the ancilla `|r⟩` from the basis state `|a, r⟩` leaves `|a⟩`. -/
theorem conj_discardKraus_single (A : Type) [Fintype A] [DecidableEq A] (a : A) (r : Fin 2) :
    MatrixMap.conj (discardKraus A r) (Matrix.single (a, r) (a, r) 1) = Matrix.single a a 1 := by
  ext b b'
  rw [conj_single_apply]
  by_cases h₁ : a = b <;> by_cases h₂ : a = b' <;>
    simp [h₁, h₂, discardKraus, Matrix.single_apply, eq_comm]

/-- Keeping the ancilla on `0` leaves the basis state `|a, 0⟩` unchanged. -/
theorem conj_keepZero_single (A : Type) [Fintype A] [DecidableEq A] (a : A) :
    MatrixMap.conj (keepZero A) (Matrix.single (a, 0) (a, 0) 1) =
      Matrix.single (a, 0) (a, 0) 1 := by
  rw [keepZero, MatrixMap.conj_mul, LinearMap.comp_apply, conj_discardKraus_single]
  ext b b'
  rw [conj_single_apply]
  by_cases h₁ : b = (a, 0) <;> by_cases h₂ : b' = (a, 0) <;>
    simp [h₁, h₂, discardKraus, Matrix.conjTranspose_apply, eq_comm]

/-- The Kronecker product of two basis projectors is a basis projector. -/
theorem single_kronecker_single_one {A B : Type} [DecidableEq A] [DecidableEq B] (a : A) (b : B) :
    Matrix.single a a (1 : ℂ) ⊗ₖ Matrix.single b b (1 : ℂ) = Matrix.single (a, b) (a, b) 1 := by
  rw [Matrix.single_kronecker_single, one_mul]

/-- The run of the keep-or-discard program on a basis state `|x, y, r⟩ ⊗ |d⟩`, at the leaf of
the outcome `r`: the call moves the query register to `|x, y + H x⟩`, and the measurement keeps
the ancilla `|0⟩` or discards the ancilla `|1⟩`. -/
theorem run_queryKeepOrDiscard_branch_single (H : Fin 2 → Fin 2) (x y : Fin 2)
    (d : (xorRuntime H).D) :
    ((xorRuntime H).run .instruments queryKeepOrDiscard).branch ⟨ancReg 0, 0, rfl⟩
        (Matrix.single (((x, y), 0), d) (((x, y), 0), d) 1) =
      Matrix.single (((x, y + H x), 0), d) (((x, y + H x), 0), d) 1 ∧
    ((xorRuntime H).run .instruments queryKeepOrDiscard).branch ⟨ancReg 1, 1, rfl⟩
        (Matrix.single (((x, y), 1), d) (((x, y), 1), d) 1) =
      Matrix.single ((x, y + H x), d) ((x, y + H x), d) 1 := by
  have hne : (⟨ancReg 1, 1, rfl⟩ : Σ u, {b : Fin 2 // ancReg b = u}) ≠ ⟨ancReg 0, 0, rfl⟩ :=
    fun h ↦ absurd (congrArg (fun p : Σ u, {b : Fin 2 // ancReg b = u} ↦ p.2.1) h) (by decide)
  constructor <;>
  ( rw [queryKeepOrDiscard, QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply_univ,
      Fintype.sum_unique, LinearMap.comp_apply, SubInstrument.branch_toD_apply,
      QuantumRuntime.queryStep_branch_single, xorRuntime_step_branch_single,
      Matrix.single_kronecker_single, one_mul, SubInstrument.branch_relabel,
      conj_basisMatrix_equiv_single, QuantumRuntime.queryEquivOut_apply, QuantumComp.prim,
      QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply_univ, Fin.sum_univ_two,
      LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    simp only [Equiv.refl_apply, branch_frame_single, QuantumRuntime.run_pure,
      LocalSig.InstrumentOp.next, LocalSig.Interp.instruments_apply, measureAnc,
      DSubInstrument.branch_ofKraus_apply] )
  · rw [DSubInstrument.branch_ret_self, DSubInstrument.branch_ret_of_ne _ hne.symm,
      LinearMap.id_apply, LinearMap.zero_apply, add_zero]
    simp only [ancKraus]
    rw [conj_keepZero_single, single_kronecker_single_one]
  · rw [DSubInstrument.branch_ret_of_ne _ hne, DSubInstrument.branch_ret_self,
      LinearMap.id_apply, LinearMap.zero_apply, zero_add]
    simp only [ancKraus]
    rw [conj_discardKraus_single, single_kronecker_single_one]

/-- The post-states of both branches of the keep-or-discard program. On `|x, y, 0⟩` it reaches
the leaf on `Reg × Fin 2` in the state `|x, y + H x, 0⟩`; on `|x, y, 1⟩` it reaches the leaf on
`Reg` in the state `|x, y + H x⟩`. -/
theorem jointPost_queryKeepOrDiscard (H : Fin 2 → Fin 2) (x y : Fin 2) :
    (xorRuntime H).jointPost .instruments queryKeepOrDiscard (SubState.basis ((x, y), 0))
        ⟨ancReg 0, 0, rfl⟩ = SubState.basis (((x, y + H x), 0), ()) ∧
      (xorRuntime H).jointPost .instruments queryKeepOrDiscard (SubState.basis ((x, y), 1))
        ⟨ancReg 1, 1, rfl⟩ = SubState.basis ((x, y + H x), ()) := by
  constructor
  · refine SubState.ext ?_
    exact (congrArg (((xorRuntime H).run .instruments queryKeepOrDiscard).branch
      ⟨ancReg 0, 0, rfl⟩) (single_kronecker_single_one ((x, y), (0 : Fin 2)) ())).trans
        (run_queryKeepOrDiscard_branch_single H x y ()).1
  · refine SubState.ext ?_
    exact (congrArg (((xorRuntime H).run .instruments queryKeepOrDiscard).branch
      ⟨ancReg 1, 1, rfl⟩) (single_kronecker_single_one ((x, y), (1 : Fin 2)) ())).trans
        (run_queryKeepOrDiscard_branch_single H x y ()).2

/-! ## Infinitely many outcomes -/

/-- The weight `2⁻¹ ^ (n + 1)` of the outcome `n` of the geometric distribution. -/
noncomputable def geomWeight (n : ℕ) : ℝ :=
  2⁻¹ ^ (n + 1)

/-- The weights of the geometric distribution are nonnegative. -/
theorem geomWeight_nonneg (n : ℕ) : 0 ≤ geomWeight n := by
  unfold geomWeight
  positivity

/-- The weights of the geometric distribution as a geometric sequence. -/
theorem geomWeight_eq : geomWeight = fun n ↦ (2⁻¹ : ℝ) ^ n * 2⁻¹ :=
  funext fun n ↦ pow_succ _ n

/-- The weights of the geometric distribution are summable. -/
theorem summable_geomWeight : Summable geomWeight := by
  rw [geomWeight_eq]
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _

/-- The weights of the geometric distribution sum to one. -/
theorem tsum_geomWeight : ∑' n, geomWeight n = 1 := by
  rw [geomWeight_eq, tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-- The Kraus operator of the outcome `n` of the geometric distribution on the trivial register:
the scalar `√(2⁻¹ ^ (n + 1))`. -/
noncomputable def geomKraus (n : ℕ) : Matrix Unit Unit ℂ :=
  ((Real.sqrt (geomWeight n) : ℝ) : ℂ) • 1

/-- The Kraus operator of the outcome `n` contributes the weight of `n`. -/
theorem conjTranspose_geomKraus_mul_self (n : ℕ) :
    (geomKraus n)ᴴ * geomKraus n = (geomWeight n : ℂ) • 1 := by
  rw [geomKraus, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, smul_smul, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, Real.mul_self_sqrt (geomWeight_nonneg n)]

/-- The branch of the outcome `n` multiplies the trace by the weight of `n`. -/
theorem trace_conj_geomKraus (n : ℕ) (ρ : Matrix Unit Unit ℂ) :
    (MatrixMap.conj (geomKraus n) ρ).trace = (geomWeight n : ℂ) * ρ.trace := by
  rw [MatrixMap.trace_conj_apply, conjTranspose_geomKraus_mul_self, Matrix.smul_mul,
    Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]

/-- **The geometric distribution** as a dependent subinstrument on the trivial register, with
outcome `n : ℕ` of weight `2⁻¹ ^ (n + 1)`: infinitely many outcomes of positive weight. -/
noncomputable def geometric : DSubInstrument (QReg.of Unit) ℕ fun _ ↦ QReg.of Unit where
  branch n := MatrixMap.conj (geomKraus n)
  isCP_branch n := MatrixMap.isCP_conj _
  trace_le s ρ hρ := by
    simp_rw [trace_conj_geomKraus, Complex.re_ofReal_mul]
    rw [← Finset.sum_mul]
    calc (∑ n ∈ s, geomWeight n) * ρ.trace.re ≤ 1 * ρ.trace.re := by
          refine mul_le_mul_of_nonneg_right ?_ hρ.trace_re_nonneg
          rw [← tsum_geomWeight]
          exact summable_geomWeight.sum_le_tsum s fun n _ ↦ geomWeight_nonneg n
      _ = ρ.trace.re := one_mul _

/-- The outcome `n` of the geometric distribution has weight `2⁻¹ ^ (n + 1)`. -/
theorem trace_geometric_branch (n : ℕ) (ρ : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) :
    (geometric.branch n ρ).trace = (geomWeight n : ℂ) * ρ.trace :=
  trace_conj_geomKraus n ρ

/-- The geometric distribution is lossless: its weights sum to one. -/
theorem lossless_geometric : geometric.Lossless := fun ρ ↦ by
  rw [geometric.isCPTNIFamily.familyTrace_apply]
  refine (tsum_congr fun n ↦ trace_geometric_branch n ρ).trans ?_
  rw [tsum_mul_right, ← Complex.ofReal_tsum, tsum_geomWeight, Complex.ofReal_one, one_mul]

/-- The geometric distribution as one local operation of the signature of instruments. -/
@[expose, reducible]
noncomputable def geomOp : LocalSig.instruments.Op (QReg.of Unit) :=
  ⟨ℕ, fun _ ↦ QReg.of Unit, geometric⟩

/-- Draw from the geometric distribution and stop; the leaf of outcome `n` sits on the trivial
register. -/
@[expose]
noncomputable def geomProg :
    QuantumComp LocalSig.instruments qrom2 (LocalSig.instruments.OutcomeAt geomOp)
      (QReg.of Unit) :=
  QuantumComp.prim geomOp

/-- Against the oracle unitary, the program reaches the leaf of outcome `n` with weight
`2⁻¹ ^ (n + 1)` times the trace of its input. -/
theorem trace_jointPost_geomProg (H : Fin 2 → Fin 2) (ρ : SubState (QReg.of Unit)) (n : ℕ) :
    ((xorRuntime H).jointPost .instruments geomProg ρ ⟨_, n, rfl⟩).matrix.trace =
      (geomWeight n : ℂ) * ρ.matrix.trace := by
  have hi : (xorRuntime H).init.matrix.trace = 1 := SubState.trace_basis (A := Unit) ()
  rw [QuantumRuntime.matrix_jointPost, geomProg, QuantumComp.prim, QuantumRuntime.run_primBind,
    DSubInstrument.branch_bind_apply, tsum_eq_single n fun b hb ↦ ?_]
  · simp only [QuantumRuntime.run_pure, LocalSig.Interp.instruments_apply]
    rw [DSubInstrument.branch_ret_self, LinearMap.id_apply, DSubInstrument.branch_frame_apply,
      MatrixMap.amplify_kronecker, Matrix.trace_kronecker, hi, mul_one]
    exact trace_geometric_branch n ρ.matrix
  · simp only [QuantumRuntime.run_pure]
    rw [DSubInstrument.branch_ret_of_ne _ fun h ↦ hb ?_, LinearMap.zero_apply]
    exact (congrArg (fun p : Σ u, LocalSig.instruments.OutcomeAt geomOp u ↦ p.2.1) h).symm

/-- The program that draws from the geometric distribution is lossless. -/
theorem lossless_geomProg : geomProg.Lossless .instruments :=
  (QuantumComp.lossless_primBind_iff (L := LocalSig.instruments) (spec := qrom2) geomOp _).mpr
    ⟨lossless_geometric, fun _ ↦ trivial⟩

/-- Against the oracle unitary, the program keeps the trace of its input, summed over its
infinitely many leaves. -/
example [MeasurableSpace (Σ u, LocalSig.instruments.OutcomeAt geomOp u)] (H : Fin 2 → Fin 2)
    (ρ : SubState (QReg.of Unit)) :
    (xorRuntime H).outcomeLaw .instruments geomProg ρ Set.univ =
      ENNReal.ofReal ρ.matrix.trace.re := by
  rw [(xorRuntime H).outcomeLaw_apply_univ_of_lossless .instruments
    (lossless_run_xorRuntime .instruments lossless_geomProg H),
    trace_re_xorRuntime_init, mul_one]

/-! ## Outcomes and leaves in a higher universe -/

/-- Measure a qubit in the computational basis and report the bit lifted to `Type 1`: a local
operation of the signature of instruments `LocalSig.instruments.{1}`, whose outcomes lie in
`Type 1`. -/
noncomputable def measureLift :
    QComp qrom2 (QReg.of (Fin 2)) (QReg.of (Fin 2)) (ULift.{1} (Fin 2)) :=
  QComp.act (SubInstrument.classical id ULift.up)

/-- The measurement with outcomes in `Type 1` is lossless. -/
theorem lossless_measureLift : measureLift.Lossless .instruments :=
  QComp.lossless_act (SubInstrument.lossless_classical _ _)

/-- Against the oracle unitary, the measurement with outcomes in `Type 1` keeps the trace of its
input. -/
example [MeasurableSpace (ULift.{1} (Fin 2))] (H : Fin 2 → Fin 2)
    (ρ : SubState (QReg.of (Fin 2))) :
    (xorRuntime H).outcomeLaw₂ .instruments measureLift ρ Set.univ =
      ENNReal.ofReal ρ.matrix.trace.re := by
  rw [(xorRuntime H).outcomeLaw₂_apply_univ_of_lossless .instruments
    (lossless_run₂_xorRuntime .instruments lossless_measureLift H),
    trace_re_xorRuntime_init, mul_one]

/-- The final register of a leaf, as a leaf: a family in `Type 1`. -/
abbrev RegLeaf (u : QReg) : Type 1 :=
  {v : QReg // v = u}

/-- The keep-or-discard program, returning its final register as its leaf: its leaves lie in
`Type 1`, while those of `queryKeepOrDiscard` lie in `Type`. -/
noncomputable def queryKeepOrDiscardReg :
    QuantumComp LocalSig.instruments qrom2 RegLeaf (QReg.of (Reg × Fin 2)) :=
  queryKeepOrDiscard.bind fun u _ ↦ QuantumComp.pure ⟨u, rfl⟩

/-- The program with leaves in `Type 1` is lossless. -/
theorem lossless_queryKeepOrDiscardReg : queryKeepOrDiscardReg.Lossless .instruments :=
  lossless_queryKeepOrDiscard.bind fun _ _ ↦ QuantumComp.lossless_pure _

/-- Against the oracle unitary, the program with leaves in `Type 1` keeps the trace of its
input. -/
example [MeasurableSpace (Σ u, RegLeaf u)] (H : Fin 2 → Fin 2)
    (ρ : SubState (QReg.of (Reg × Fin 2))) :
    (xorRuntime H).outcomeLaw .instruments queryKeepOrDiscardReg ρ Set.univ =
      ENNReal.ofReal ρ.matrix.trace.re := by
  rw [(xorRuntime H).outcomeLaw_apply_univ_of_lossless .instruments
    (lossless_run_xorRuntime .instruments lossless_queryKeepOrDiscardReg H),
    trace_re_xorRuntime_init, mul_one]

/-! ## A gate set -/

/-- Two named gates on a qubit: the bit flip `x` and the phase flip `z`. -/
inductive Gate : QReg → Type 1
  /-- The bit flip. -/
  | x : Gate (QReg.of (Fin 2))
  /-- The phase flip. -/
  | z : Gate (QReg.of (Fin 2))

/-- The signature of the gate set: a gate has one outcome and keeps its register. -/
@[expose, reducible]
def gates : LocalSig where
  Op := Gate
  Outcome _ := Unit
  next {A} _ _ := A

/-- The bit flip, the permutation matrix of `b ↦ b + 1`. -/
noncomputable def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  basisMatrix fun b : Fin 2 ↦ b + 1

/-- The bit flip is unitary. -/
theorem conjTranspose_pauliX_mul_self : pauliXᴴ * pauliX = 1 :=
  conjTranspose_basisMatrix_mul_self (add_left_injective 1)

/-- The phase flip, the diagonal matrix of signs. -/
noncomputable def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal sgn

/-- The phase flip is unitary. -/
theorem conjTranspose_pauliZ_mul_self : pauliZᴴ * pauliZ = 1 := by
  rw [pauliZ, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext y
  rcases eq_zero_or_one y with rfl | rfl <;> simp [sgn]

/-- The interpretation of the gate set: each gate is the gate of its unitary. -/
noncomputable def gateInterp : gates.Interp := fun _ g ↦
  match g with
  | .x => SubInstrument.toD (SubInstrument.ofIsometry pauliX conjTranspose_pauliX_mul_self)
  | .z => SubInstrument.toD (SubInstrument.ofIsometry pauliZ conjTranspose_pauliZ_mul_self)

/-- The interpretation of the gate set is lossless. -/
theorem lossless_gateInterp : gateInterp.Lossless := fun _ g ↦ by
  cases g <;> exact SubInstrument.lossless_toD_iff.mpr (SubInstrument.lossless_ofIsometry _ _)

/-- The bit flip moves the basis state `|0⟩` to `|1⟩`, so it is not the identity. -/
theorem gateInterp_x_branch_single_zero :
    (gateInterp Gate.x).branch () (Matrix.single (0 : Fin 2) 0 1) =
      Matrix.single (1 : Fin 2) 1 1 := by
  change MatrixMap.conj (basisMatrix (Equiv.addRight (1 : Fin 2))) (Matrix.single 0 0 1) = _
  rw [conj_basisMatrix_equiv_single]
  rfl

/-- The state `|+⟩⟨+|` (for `b = 0`) or `|-⟩⟨-|` (for `b = 1`) of a qubit. -/
noncomputable def plusMinusProj (b : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j ↦ sgn (b * (i + j)) / 2

/-- The phase flip moves `|+⟩` to `|-⟩`, so it is not the identity; it fixes the basis states, so
it is not the bit flip either. -/
theorem gateInterp_z_branch_plus :
    (gateInterp Gate.z).branch () (plusMinusProj 0) = plusMinusProj 1 := by
  change MatrixMap.conj pauliZ (plusMinusProj 0) = _
  ext i j
  rcases eq_zero_or_one i with rfl | rfl <;> rcases eq_zero_or_one j with rfl | rfl <;>
    simp [MatrixMap.conj_apply, pauliZ, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
      Matrix.mul_diagonal, plusMinusProj, sgn, neg_div]

/-- Apply one gate. -/
noncomputable def gate {A : QReg} (g : Gate A) : QuantumComp₂ gates qrom2 A A Unit :=
  QuantumComp₂.primBind g fun _ ↦ QuantumComp₂.pure ()

/-- One gate costs one gate. -/
theorem isCostBound_gate {A : QReg} (g : Gate A) : (gate g).IsCostBound (fun _ _ ↦ 1) 1 :=
  (QuantumComp.isCostBound_primBind_iff _ _ _).mpr
    ⟨le_rfl, fun _ ↦ QuantumComp.isCostBound_pure _ _⟩

/-- Apply the bit flip, then the phase flip. -/
noncomputable def xThenZ : QuantumComp₂ gates qrom2 (QReg.of (Fin 2)) (QReg.of (Fin 2)) Unit :=
  (gate .x).bind fun _ ↦ gate .z

/-- The program uses two gates. -/
example : xThenZ.IsCostBound (fun _ _ ↦ 1) 2 :=
  QuantumComp₂.isCostBound_bind (n := 1) (m := 1) (isCostBound_gate _) fun _ ↦ isCostBound_gate _

/-- The program does not fit in one gate. -/
example : ¬ xThenZ.IsCostBound (fun _ _ ↦ 1) 1 := by
  intro h
  have h' : (QuantumComp₂.primBind (L := gates) (spec := qrom2) Gate.x fun _ ↦
      QuantumComp₂.primBind Gate.z fun _ ↦ QuantumComp₂.pure ()).IsCostBound (fun _ _ ↦ 1) 1 := h
  have h₂ := ((QuantumComp.isCostBound_primBind_iff _ _ _).mp h').2 ()
  exact absurd ((QuantumComp.isCostBound_primBind_iff _ _ _).mp h₂).1 (by decide)

/-- Under the gate interpretation, against the oracle unitary, the program runs to a lossless
subinstrument. -/
example (H : Fin 2 → Fin 2) : ((xorRuntime H).run₂ gateInterp xThenZ).Lossless :=
  lossless_run₂_xorRuntime gateInterp (QuantumComp.lossless_of_interp lossless_gateInterp _) H

end VCVioTest.QuantumOracle
