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
  (`Quantum.QuantumComb.toComp`) runs as the comb does (`Quantum.QuantumComb.run_toComp`),
  with one call.
* **Classical algorithms.** The program of the algorithm that queries `0` reports `H 0`; its
  distribution in the quantum random-oracle model is its distribution under the lazily sampled
  random oracle, with no query bound. The adaptive algorithm that queries `H 0` next reports `H (H
  0)`. Running the program of a sequenced algorithm is sequencing the runs
  (`Quantum.QuantumRuntime.run_bind`).
* **An adaptive program** measures a bit and calls the oracle only when it reads `1`: it has
  budget one, and not budget zero.
* **An ancilla** is allocated, carried through a call as the remainder of the register, and
  discarded.
* **Two ports.** A program calling each port once has budget one per port, and not budget one
  on one port alone. A program that calls only one port runs in the same way whatever the other
  port does.
* **A stateful runtime.** A program measures a bit, calls twice on `1` and once on `0`, and
  returns the bit. From the fair mixture of the two basis states, the joint distribution of
  that bit and a final basis measurement of the private counter is
  `(1/2) δ_(0,1) + (1/2) δ_(1,2)` (`coinCounterDist_eq`). The counter retains information about
  the path taken by the program.
* **Guessing without queries.** A lossless program with budget zero, over any primitive
  signature and interpretation, started from a normalized state, guesses a point of a uniformly
  sampled oracle with probability `1 / 2`, whether it returns its guess on a fixed final register
  or reads it off a leaf whose register depends on the outcome.
* **A register that depends on an outcome.** A program calls the oracle with an ancilla as the
  remainder, measures the ancilla and keeps it on `0` or discards it on `1`, so that its final
  register depends on the outcome. Against the oracle unitary it is lossless, makes one call, and
  keeps the trace of its input; on `|x, y, 0⟩` it ends in `|x, y + H x, 0⟩` on the register with
  the ancilla, and on `|x, y, 1⟩` in `|x, y + H x⟩` on the register without it. Its distribution in
  the quantum random-oracle model has total mass the trace of its input.
* **Infinitely many outcomes.** The geometric distribution over `ℕ`, a dependent subinstrument on
  the trivial register with outcome `n` of weight `2⁻¹ ^ (n + 1)`, is lossless; a program that
  draws from it reaches the leaf of `n` with that weight, and keeps the trace of its input.
* **Higher universes.** A runtime parameter in `Type 1` selects a constant oracle; querying it
  gives a fair mixture of the two answers (`sampledEvalDist₂_ulift_bool`). A measurement whose
  outcomes lie in `Type 1`, and a program whose leaves (its final registers) lie in `Type 1`,
  run against the oracle unitary and keep the trace of their input.
* **A gate set.** A primitive signature of two named gates, interpreted by the bit flip and the
  phase flip: the bit flip moves `|0⟩` to `|1⟩` and the phase flip moves `|+⟩` to `|-⟩`. A
  program applying both uses two gates and not one, and runs to a lossless subinstrument.
* **The fixed-register run.** The run of the coin program as a fixed-register program is the run
  of its tree read at the leaf on its final register; the counter calculation holds for both.
* **Constant-output facades.** Mapping and losslessness chain after sequencing or framing;
  constant map laws and explicit unfolding support rewrites through ordinary imports.
-/

public section

open Quantum Matrix MeasureTheory OracleSpec
open scoped ComplexOrder ENNReal Kronecker

namespace VCVioTest.QuantumOracle

/-! ## Constant-output composition through ordinary imports -/

noncomputable section constantOutput

variable {A B C R α β γ : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype R]

/-- Relabelling a sequenced computation exposes its cast-free branch fibre. -/
example (p : SubInstrument A B α) (k : α → SubInstrument B C β)
    (f : β → γ) (c : γ) (ρ : Matrix A A ℂ) :
    ((p.bind k).map f).branch c ρ = ∑' b : f ⁻¹' {c}, (p.bind k).branch b ρ := by
  rw [SubInstrument.branch_map_apply]

/-- Relabelling a framed computation exposes its cast-free branch fibre. -/
example (p : SubInstrument A B α) (f : α → β) (b : β) (ρ : Matrix (A × R) (A × R) ℂ) :
    ((p.frame R).map f).branch b ρ = ∑' a : f ⁻¹' {b}, (p.frame R).branch a ρ := by
  rw [SubInstrument.branch_map_apply]

/-- Sequencing and relabelling preserve losslessness without output-family annotations. -/
example (p : SubInstrument A B α) (k : α → SubInstrument B C β)
    (hp : p.Lossless) (hk : ∀ a, (k a).Lossless) (f : β → γ) :
    ((p.bind k).map f).Lossless :=
  (hp.bind hk).map f

/-- Framing and relabelling preserve losslessness without output-family annotations. -/
example (p : SubInstrument A B α) (hp : p.Lossless) (f : α → β) :
    ((p.frame R).map f).Lossless :=
  (hp.frame R).map f

/-- Qualified mapping also accepts a composite explicitly formed by dependent bind. -/
example (p : SubInstrument A B α) (k : α → SubInstrument B C β) (f : β → γ) :=
  SubInstrument.map f (DSubInstrument.bind p k)

/-- Qualified losslessness mapping accepts a proof formed by the dependent bind law. -/
example (p : SubInstrument A B α) (k : α → SubInstrument B C β)
    (hp : p.Lossless) (hk : ∀ a, (k a).Lossless) (f : β → γ) :
    (SubInstrument.map f (DSubInstrument.bind p k)).Lossless :=
  SubInstrument.Lossless.map (DSubInstrument.Lossless.bind hp hk) f

/-- The constant map-as-bind law supports a bare rewrite. -/
example (p : SubInstrument A B α) (f : α → β) :
    p.map f = p.bind (fun a ↦ SubInstrument.pure (f a)) := by
  rw [SubInstrument.map_eq_bind_pure]

/-- Simplification applies the dependent map-as-bind law through the constant facades. -/
example (p : SubInstrument A B α) (f : α → β) :
    p.map f = p.bind (fun a ↦ SubInstrument.pure (f a)) := by
  simp only [DSubInstrument.map_eq_bind_ret]

/-- Exposing the map facade permits the dependent map-as-bind law to rewrite. -/
example (p : SubInstrument A B α) (f : α → β) :
    p.map f = p.bind (fun a ↦ SubInstrument.pure (f a)) := by
  rw [SubInstrument.map, DSubInstrument.map_eq_bind_ret]

/-- Exposing the map facade permits the dependent identity law to rewrite. -/
example (p : SubInstrument A B α) : p.map id = p := by
  rw [SubInstrument.map, DSubInstrument.map_id]

/-- Simplification also handles identity relabelling directly. -/
example (p : SubInstrument A B α) : p.map id = p := by
  simp

end constantOutput

/-- The random-oracle signature for oracles `Fin 2 → Fin 2`. It is noncomputable: it is only used
in types and noncomputable programs, and is not evaluated when the module is loaded. -/
noncomputable abbrev qrom2 : QuantumOracleSpec :=
  qromSpec (Fin 2) (Fin 2)

/-- Over `Fin 3`, two constant-one calls send `|0,0⟩` to `|0,2⟩`. -/
example (d : (additiveOracleRuntime (fun _ : Fin 3 ↦ (1 : Fin 3))).D) :
    ((additiveOracleRuntime (fun _ : Fin 3 ↦ (1 : Fin 3))).step ()).branch ()
      (((additiveOracleRuntime (fun _ : Fin 3 ↦ (1 : Fin 3))).step ()).branch ()
        (Matrix.single ((0, 0), d) ((0, 0), d) 1)) =
      Matrix.single ((0, 2), d) ((0, 2), d) 1 := by
  rw [additiveOracleRuntime_step_branch_single, additiveOracleRuntime_step_branch_single]
  rfl

/-- Over bits, two constant-one calls restore the projector `|0,0⟩⟨0,0|`. -/
example (d : (additiveOracleRuntime (fun _ : Fin 2 ↦ (1 : Fin 2))).D) :
    ((additiveOracleRuntime (fun _ : Fin 2 ↦ (1 : Fin 2))).step ()).branch ()
      (((additiveOracleRuntime (fun _ : Fin 2 ↦ (1 : Fin 2))).step ()).branch ()
        (Matrix.single ((0, 0), d) ((0, 0), d) 1)) =
      Matrix.single ((0, 0), d) ((0, 0), d) 1 := by
  rw [additiveOracleRuntime_step_branch_single, additiveOracleRuntime_step_branch_single]
  rfl

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

/-- Every bit is zero or one. -/
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
  lossless_step _ := DSubInstrument.lossless_ret (fun _ : Unit ↦ Reg) ()
  final := DSubInstrument.ofKraus proj sum_conjTranspose_proj_mul_proj
  lossless_final := DSubInstrument.lossless_ofKraus _ _

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
  rw [DSubInstrument.post_ret_self, DSubInstrument.post_ret_self,
    DSubInstrument.outcomeMeasure_eq_sum_univ, Fin.sum_univ_two]
  have h : ∀ b, (deutsch.final.branch b ((oracleQuery H).post plusMinus ()).matrix).trace =
      if b = H 0 + H 1 then 1 else 0 := fun b ↦ by
    have h₁ : ((oracleQuery H).post plusMinus ()).matrix =
        MatrixMap.conj (oracleUnitary H) (vecMulVec amp (star amp)) := by
      simp [MatrixMap.conj_apply, plusMinus]
    rw [h₁]
    change ((DSubInstrument.ofKraus proj sum_conjTranspose_proj_mul_proj).branch b _).trace = _
    rw [DSubInstrument.branch_ofKraus_apply]
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

/-- Against the oracle runtime, Deutsch's program runs as the
comb, framed by the runtime register, against the runtime's query step. -/
example (H : Fin 2 → Fin 2) :
    (additiveOracleRuntime H).run₂ .instruments deutschComp =
      (deutsch.frame (additiveOracleRuntime H).D (additiveOracleRuntime H).init).run
        ((additiveOracleRuntime H).combQuery () (QReg.of Unit) (Equiv.prodPUnit Reg).symm
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
    (additiveOracleRuntime H).evalDist₂ .instruments queryZero.toQuantum (SubState.basis ()) =
      Measure.dirac (H 0) :=
  evalDist_additiveOracleRuntime_toQuantum H queryZero

/-- The program makes one call. -/
example : queryZero.toQuantum.IsQueryBound fun _ ↦ 1 :=
  OracleComp.isQueryBound_toQuantum isTotalQueryBound_queryZero

/-- The distribution of the program in the quantum random-oracle model is the distribution of the
algorithm under the lazily sampled random oracle; no query bound is used. -/
example :
    qromEvalDist₂ .instruments queryZero.toQuantum (SubState.basis ()) =
      𝒟[(simulateQ randomOracle queryZero).run' ∅] :=
  qromEvalDist₂_toQuantum_eq_randomOracle queryZero

/-- The adaptive algorithm that queries `0`, and then queries the answer. -/
def queryTwice : OracleComp (Fin 2 →ₒ Fin 2) (Fin 2) := do
  let y ← liftM ((Fin 2 →ₒ Fin 2).query 0)
  liftM ((Fin 2 →ₒ Fin 2).query y)

/-- Its program, whose second call depends on the measured result of the first, reports
`H (H 0)` with certainty. -/
example (H : Fin 2 → Fin 2) :
    (additiveOracleRuntime H).evalDist₂ .instruments queryTwice.toQuantum (SubState.basis ()) =
      Measure.dirac (H (H 0)) :=
  evalDist_additiveOracleRuntime_toQuantum H queryTwice

/-- Running the program of a sequenced algorithm is sequencing the runs of the programs. -/
example {α β : Type} (H : Fin 2 → Fin 2) (oa : OracleComp (Fin 2 →ₒ Fin 2) α)
    (f : α → OracleComp (Fin 2 →ₒ Fin 2) β) :
    (additiveOracleRuntime H).run₂ .instruments (oa >>= f).toQuantum =
      ((additiveOracleRuntime H).run₂ .instruments oa.toQuantum).bind fun a ↦
        (additiveOracleRuntime H).run₂ .instruments (f a).toQuantum := by
  rw [OracleComp.toQuantum, simulateQ_bind]
  exact QuantumRuntime.run₂_bind _ _ _ _

/-! ## An adaptive program -/

/-- Measure the query bit; on `1`, call the oracle and return to the register `Fin 2 × Fin 2`;
then return the bit. The number of calls depends on the measured outcome. -/
noncomputable def callIfOne : QComp qrom2 (QReg.of Reg) (QReg.of Reg) (Fin 2) :=
  (QComp.act (A := QReg.of Reg) (B := QReg.of Reg)
      (DSubInstrument.classical (B := fun _ ↦ Reg) (fun m : Reg ↦ m.1) id)).bind fun b ↦
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
  (DSubInstrument.ofKraus (discardKraus A) (sum_discardKraus A)).map fun _ ↦ ()

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
      QComp.lossless_act (DSubInstrument.lossless_ofKraus _ _).map

example : queryWithAncilla.IsQueryBound fun _ ↦ 1 := by
  rw [queryWithAncilla, QComp.isQueryBound_act_bind_iff]
  intro _
  exact (QuantumComp₂.isQueryBound_bind
    ((QuantumComp₂.isQueryBound_query_iff _ _ _ (fun _ ↦ 1)).mpr Nat.one_pos)
      fun _ ↦ QComp.isQueryBound_act _ 0).mono fun _ ↦ le_of_eq (add_zero _)

/-- Against the oracle unitary, the program with an ancilla keeps the trace of its input. -/
example (H : Fin 2 → Fin 2) (ρ : SubState (QReg.of Reg)) :
    (additiveOracleRuntime H).evalDist₂ .instruments queryWithAncilla ρ Set.univ =
      ENNReal.ofReal ρ.matrix.trace.re := by
  rw [(additiveOracleRuntime H).evalDist₂_apply_univ_of_lossless .instruments
    (lossless_run₂_additiveOracleRuntime .instruments lossless_queryWithAncilla H),
    trace_re_additiveOracleRuntime_init, mul_one]

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
  step _ := DSubInstrument.classical (B := fun _ ↦ Unit × Fin 3) (fun _ ↦ ())
    (fun m : Unit × Fin 3 ↦ ((), tick m.2))

/-- A call of the counting runtime on a basis state advances the counter. -/
theorem countRuntime_step_branch_single (d : Fin 3) :
    (countRuntime.step ()).branch () (Matrix.single ((), d) ((), d) 1) =
      Matrix.single ((), tick d) ((), tick d) 1 :=
  (DSubInstrument.branch_classical_basis (B := fun _ ↦ Unit × Fin 3) (fun _ ↦ ())
    (fun m : Unit × Fin 3 ↦ ((), tick m.2))
    ((), d) ()).trans (by simp)

/-- Measure a coin; call twice on heads (`1`) and once on tails (`0`); return the coin. -/
@[expose]
noncomputable def coinProg :
    QComp countSpec (QReg.of (Fin 2)) (QReg.of (Unit × Fin 2)) (Fin 2) :=
  (QComp.act (A := QReg.of (Fin 2)) (B := QReg.of (Fin 2))
      (DSubInstrument.classical (B := fun _ ↦ _) id id)).bind fun b ↦
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
  rw [coinProg, QuantumRuntime.run₂_act_bind, DSubInstrument.branch_bind_apply_univ,
    LinearMap.sum_apply, Finset.sum_eq_single b (fun b' _ hb' ↦ ?_) (by simp),
    LinearMap.comp_apply, DSubInstrument.branch_frame_single, DSubInstrument.branch_classical_basis]
  · simp only [id, ↓reduceDIte, cast_eq, Matrix.single_kronecker_single, one_mul]
    rw [QuantumRuntime.run₂_query_bind, DSubInstrument.branch_bind_unit, LinearMap.comp_apply,
      QuantumRuntime.queryStep_branch_single, Equiv.punitProd_symm_apply,
      countRuntime_step_branch_single, Matrix.single_kronecker_single, one_mul,
      SubInstrument.branch_relabel, conj_basisMatrix_equiv_single,
      QuantumRuntime.queryEquivOut_apply]
    rcases eq_zero_or_one b with rfl | rfl
    · simp [SubInstrument.branch_pure, Pi.single_apply]
      split_ifs <;> simp_all
    · simp only [↓reduceIte]
      rw [QuantumRuntime.run₂_query_bind, DSubInstrument.branch_bind_unit, LinearMap.comp_apply,
        QuantumRuntime.queryStep_branch_single, Equiv.refl_apply,
        countRuntime_step_branch_single, Matrix.single_kronecker_single, one_mul,
        SubInstrument.branch_relabel, conj_basisMatrix_equiv_single,
        QuantumRuntime.queryEquivOut_apply]
      simp [SubInstrument.branch_pure, Pi.single_apply]
      split_ifs <;> simp_all
  · rw [LinearMap.comp_apply, DSubInstrument.branch_frame_single,
      DSubInstrument.branch_classical_basis]
    simp [Ne.symm hb']

/-- The counting runtime after the coin program: from `|1⟩` the counter ends at `2`, and from `|0⟩`
at `1`. The number of calls, and so the final state of the private register, depends on the path the
program takes. -/
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
    qromEvalDistMap₂ I x ρ (fun H a ↦ a.2 = H a.1) {True} = 2⁻¹ := by
  simpa using qromEvalDistMap₂_guess_zero_of_trace_eq_one I hx hl h

/-- The same for a general program, whose final register may depend on the outcome: a lossless
program with budget zero whose leaves carry guesses guesses a point of the oracle with probability
`1 / 2`. -/
example {L : LocalSig} (I : L.Interp) {W : QReg → Type} {A : QReg}
    (x : QuantumComp L qrom2 W A) (hx : x.IsQueryBound 0) (hl : x.Lossless I)
    (gx gy : (Σ u, W u) → Fin 2) {ρ : SubState A} (h : ρ.matrix.trace = 1) :
    qromEvalDistMap I x ρ (fun H p ↦ gy p = H (gx p)) {True} = 2⁻¹ := by
  simpa using qromEvalDistMap_guess_zero_of_trace_eq_one I hx hl gx gy h

/-! ## The fixed-register run is the general run -/

/-- The run of the coin program as a fixed-register program is the run of its tree, read at the
leaf on its final register `Unit × Fin 2`. -/
example (c : Fin 2) :
    (countRuntime.run₂ .instruments coinProg).branch c =
      (countRuntime.run .instruments coinProg).branch ⟨QReg.of (Unit × Fin 2), rfl, c⟩ :=
  QuantumRuntime.branch_run₂ ..

/-- The joint post-measurement state of the tree at the
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
    ((additiveOracleRuntime H).run .instruments queryKeepOrDiscard).Lossless :=
  lossless_run_additiveOracleRuntime .instruments lossless_queryKeepOrDiscard H

/-- Against the oracle unitary, the program keeps the trace of its input, summed over both final
registers. -/
example (H : Fin 2 → Fin 2) (ρ : SubState (QReg.of (Reg × Fin 2))) :
    (additiveOracleRuntime H).evalDist .instruments queryKeepOrDiscard ρ Set.univ =
      ENNReal.ofReal ρ.matrix.trace.re := by
  rw [(additiveOracleRuntime H).evalDist_apply_univ_of_lossless .instruments
    (lossless_run_additiveOracleRuntime .instruments lossless_queryKeepOrDiscard H),
    trace_re_additiveOracleRuntime_init, mul_one]

/-- In the quantum random-oracle model, the distribution of the leaf of the program that keeps or
discards the ancilla, whose two leaves sit on different registers, has the trace of its input as
total mass. -/
example [MeasurableSpace (Σ u, {b : Fin 2 // ancReg b = u})]
    (ρ : SubState (QReg.of (Reg × Fin 2))) :
    qromEvalDist .instruments queryKeepOrDiscard ρ Set.univ = ENNReal.ofReal ρ.matrix.trace.re :=
  qromEvalDist_apply_univ_of_lossless lossless_queryKeepOrDiscard ρ

/-- Each branch of a framed dependent subinstrument on a product basis state acts on the first
factor and keeps the second. -/
theorem branch_frame_single {A : Type} [Fintype A] [DecidableEq A] {ι : Type} {B : ι → Type}
    [∀ i, Fintype (B i)] {R : Type} [Fintype R] [DecidableEq R] (p : DSubInstrument A ι B) (i : ι)
    (a : A) (r : R) :
    (p.frame R).branch i (Matrix.single (a, r) (a, r) 1) =
      p.branch i (Matrix.single a a 1) ⊗ₖ Matrix.single r r 1 := by
  rw [DSubInstrument.branch_frame_apply, ← MatrixMap.amplify_kronecker,
    Matrix.single_kronecker_single, one_mul]

/-- The Kraus map of `K` sends the basis projector `|a⟩⟨a|` to the positive outer-product
operator `v v†`, where `v` is column `a` of `K`. This is a rank-one orthogonal projector when
`v` has norm one. -/
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
    (d : (additiveOracleRuntime H).D) :
    ((additiveOracleRuntime H).run .instruments queryKeepOrDiscard).branch ⟨ancReg 0, 0, rfl⟩
        (Matrix.single (((x, y), 0), d) (((x, y), 0), d) 1) =
      Matrix.single (((x, y + H x), 0), d) (((x, y + H x), 0), d) 1 ∧
    ((additiveOracleRuntime H).run .instruments queryKeepOrDiscard).branch ⟨ancReg 1, 1, rfl⟩
        (Matrix.single (((x, y), 1), d) (((x, y), 1), d) 1) =
      Matrix.single ((x, y + H x), d) ((x, y + H x), d) 1 := by
  have hne : (⟨ancReg 1, 1, rfl⟩ : Σ u, {b : Fin 2 // ancReg b = u}) ≠ ⟨ancReg 0, 0, rfl⟩ :=
    fun h ↦ absurd (congrArg (fun p : Σ u, {b : Fin 2 // ancReg b = u} ↦ p.2.1) h) (by decide)
  constructor <;>
  ( rw [queryKeepOrDiscard, QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply_univ,
      Fintype.sum_unique, LinearMap.comp_apply,
      QuantumRuntime.queryStep_branch_single, additiveOracleRuntime_step_branch_single,
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
    (additiveOracleRuntime H).jointPost .instruments queryKeepOrDiscard (SubState.basis ((x, y), 0))
        ⟨ancReg 0, 0, rfl⟩ = SubState.basis (((x, y + H x), 0), ()) ∧
      (additiveOracleRuntime H).jointPost .instruments queryKeepOrDiscard (SubState.basis ((x, y),
        1))
        ⟨ancReg 1, 1, rfl⟩ = SubState.basis ((x, y + H x), ()) := by
  constructor
  · refine SubState.ext ?_
    exact (congrArg (((additiveOracleRuntime H).run .instruments queryKeepOrDiscard).branch
      ⟨ancReg 0, 0, rfl⟩) (single_kronecker_single_one ((x, y), (0 : Fin 2)) ())).trans
        (run_queryKeepOrDiscard_branch_single H x y ()).1
  · refine SubState.ext ?_
    exact (congrArg (((additiveOracleRuntime H).run .instruments queryKeepOrDiscard).branch
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
    ((additiveOracleRuntime H).jointPost .instruments geomProg ρ ⟨_, n, rfl⟩).matrix.trace =
      (geomWeight n : ℂ) * ρ.matrix.trace := by
  have hi : (additiveOracleRuntime H).init.matrix.trace = 1 := SubState.trace_basis (A := Unit) ()
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
    (additiveOracleRuntime H).evalDist .instruments geomProg ρ Set.univ =
      ENNReal.ofReal ρ.matrix.trace.re := by
  rw [(additiveOracleRuntime H).evalDist_apply_univ_of_lossless .instruments
    (lossless_run_additiveOracleRuntime .instruments lossless_geomProg H),
    trace_re_additiveOracleRuntime_init, mul_one]

/-! ## Sampled parameters, outcomes and leaves in a higher universe -/

/-- A uniformly sampled parameter in `Type 1` selects the constant-zero or constant-one
oracle. Querying it gives the fair mixture of the two answers. -/
theorem sampledEvalDist₂_ulift_bool :
    sampledEvalDist₂
        (fun ω : ULift.{1} Bool ↦
          additiveOracleRuntime (fun _ : Fin 2 ↦ if ω.down then (1 : Fin 2) else 0))
        .instruments queryZero.toQuantum (SubState.basis ()) =
      (2 : ℝ≥0∞)⁻¹ • Measure.dirac (0 : Fin 2) +
        (2 : ℝ≥0∞)⁻¹ • Measure.dirac (1 : Fin 2) := by
  have h (H : Fin 2 → Fin 2) :
      (additiveOracleRuntime H).evalDist₂ .instruments queryZero.toQuantum (SubState.basis ()) =
        Measure.dirac (H 0) :=
    evalDist_additiveOracleRuntime_toQuantum H queryZero
  rw [sampledEvalDist₂_eq_sum, ← Equiv.ulift.symm.sum_comp, Fintype.sum_bool]
  simp [h, smul_add, add_comm]

/-- Measure a qubit in the computational basis and report the bit lifted to `Type 1`: a local
operation of the signature of instruments `LocalSig.instruments.{1}`, whose outcomes lie in
`Type 1`. -/
noncomputable def measureLift :
    QComp qrom2 (QReg.of (Fin 2)) (QReg.of (Fin 2)) (ULift.{1} (Fin 2)) :=
  QComp.act (DSubInstrument.classical (B := fun _ ↦ _) ULift.up id)

/-- The measurement with outcomes in `Type 1` is lossless. -/
theorem lossless_measureLift : measureLift.Lossless .instruments :=
  QComp.lossless_act (DSubInstrument.lossless_classical _ _)

/-- Against the oracle unitary, the measurement with outcomes in `Type 1` keeps the trace of its
input. -/
example [MeasurableSpace (ULift.{1} (Fin 2))] (H : Fin 2 → Fin 2)
    (ρ : SubState (QReg.of (Fin 2))) :
    (additiveOracleRuntime H).evalDist₂ .instruments measureLift ρ Set.univ =
      ENNReal.ofReal ρ.matrix.trace.re := by
  rw [(additiveOracleRuntime H).evalDist₂_apply_univ_of_lossless .instruments
    (lossless_run₂_additiveOracleRuntime .instruments lossless_measureLift H),
    trace_re_additiveOracleRuntime_init, mul_one]

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
    (additiveOracleRuntime H).evalDist .instruments queryKeepOrDiscardReg ρ Set.univ =
      ENNReal.ofReal ρ.matrix.trace.re := by
  rw [(additiveOracleRuntime H).evalDist_apply_univ_of_lossless .instruments
    (lossless_run_additiveOracleRuntime .instruments lossless_queryKeepOrDiscardReg H),
    trace_re_additiveOracleRuntime_init, mul_one]

/-- A comb returning a lifted bit has the same execution as its program. -/
example (c : QuantumComb Reg (ULift.{1} Bool) 1) (H : Fin 2 → Fin 2) :
    (additiveOracleRuntime H).run₂ .instruments
        (c.toComp () (QReg.of Unit) (Equiv.prodPUnit Reg).symm (Equiv.prodPUnit Reg)) =
      (c.frame (additiveOracleRuntime H).D (additiveOracleRuntime H).init).run
        ((additiveOracleRuntime H).combQuery () (QReg.of Unit)
          (Equiv.prodPUnit Reg).symm (Equiv.prodPUnit Reg)) :=
  c.run_toComp (additiveOracleRuntime H) () (QReg.of Unit)
    (Equiv.prodPUnit Reg).symm (Equiv.prodPUnit Reg)

/-- The lifted-bit comb and its program also have equal observed distributions. -/
example [MeasurableSpace (ULift.{1} Bool)] (c : QuantumComb Reg (ULift.{1} Bool) 1)
    (H : Fin 2 → Fin 2) :
    (additiveOracleRuntime H).evalDist₂ .instruments
        (c.toComp () (QReg.of Unit) (Equiv.prodPUnit Reg).symm (Equiv.prodPUnit Reg)) c.init =
      ((c.frame (additiveOracleRuntime H).D (additiveOracleRuntime H).init).run
        ((additiveOracleRuntime H).combQuery () (QReg.of Unit)
          (Equiv.prodPUnit Reg).symm (Equiv.prodPUnit Reg))).outcomeMeasure
            (c.frame (additiveOracleRuntime H).D (additiveOracleRuntime H).init).init :=
  c.evalDist_toComp (additiveOracleRuntime H) () (QReg.of Unit)
    (Equiv.prodPUnit Reg).symm (Equiv.prodPUnit Reg)

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
  | .x => SubInstrument.ofIsometry pauliX conjTranspose_pauliX_mul_self
  | .z => SubInstrument.ofIsometry pauliZ conjTranspose_pauliZ_mul_self

/-- The interpretation of the gate set is lossless. -/
theorem lossless_gateInterp : gateInterp.Lossless := fun _ g ↦ by
  cases g with
  | x => exact SubInstrument.lossless_ofIsometry _ conjTranspose_pauliX_mul_self
  | z => exact SubInstrument.lossless_ofIsometry _ conjTranspose_pauliZ_mul_self

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
example (H : Fin 2 → Fin 2) : ((additiveOracleRuntime H).run₂ gateInterp xThenZ).Lossless :=
  lossless_run₂_additiveOracleRuntime gateInterp (QuantumComp.lossless_of_interp
    lossless_gateInterp _) H

/-! ## Entangled spectators and persistent oracle functions -/

/-- An additive bit oracle with an untouched private qubit initially in `|1⟩`. -/
@[expose, reducible]
noncomputable def spectatorRuntime (H : Fin 2 → Fin 2) : QuantumRuntime qrom2 where
  D := QReg.of (Fin 2)
  init := SubState.basis 1
  step _ := (oracleQuery H).frame (Fin 2)

/-- Call the bit oracle while retaining a qubit as the adversary's remainder. -/
noncomputable def spectatorCall :
    QComp qrom2 (QReg.of (Reg × Fin 2)) (QReg.of (Reg × Fin 2)) Unit :=
  QuantumComp₂.query () (QReg.of (Fin 2)) (Equiv.refl (Reg × Fin 2))

/-- A call changes only response indices, including on off-diagonal spectator blocks. -/
theorem run_spectatorCall_apply (H : Fin 2 → Fin 2)
    (ρ : Matrix ((Reg × Fin 2) × Fin 2) ((Reg × Fin 2) × Fin 2) ℂ)
    (x y e d x' y' e' d' : Fin 2) :
    ((spectatorRuntime H).run₂ .instruments spectatorCall).branch () ρ
        (((x, y), e), d) (((x', y'), e'), d') =
      ρ (((x, y - H x), e), d) (((x', y' - H x'), e'), d') := by
  rw [spectatorCall, QuantumRuntime.run₂_query, SubInstrument.bind_pure]
  simp only [QuantumRuntime.queryStep, DSubInstrument.branch_bind_unit,
    SubInstrument.branch_pure_self, LinearMap.id_comp, LinearMap.comp_apply,
    SubInstrument.relabel_branch_apply, DSubInstrument.branch_frame_apply,
    spectatorRuntime, branch_oracleQuery_apply, MatrixMap.amplify_apply,
    conj_oracleUnitary_apply, Matrix.submatrix_apply]
  rfl

/-- The Bell projector on query and remainder, with response `b` and private qubit `|1⟩`. -/
noncomputable def bellSpectator (b : Fin 2) :
    Matrix ((Reg × Fin 2) × Fin 2) ((Reg × Fin 2) × Fin 2) ℂ :=
  fun m n ↦ if m.1.1.1 = m.1.2 ∧ n.1.1.1 = n.1.2 ∧
    m.1.1.2 = b ∧ n.1.1.2 = b ∧ m.2 = 1 ∧ n.2 = 1 then 1 / 2 else 0

/-- The constant-one runtime sends the Bell state with response zero to response one.
The four Bell entries, including both off-diagonal coherences, remain `1/2`; all others vanish. -/
example :
    ((spectatorRuntime fun _ ↦ 1).run₂ .instruments spectatorCall).branch ()
      (bellSpectator 0) = bellSpectator 1 := by
  ext ⟨⟨⟨x, y⟩, e⟩, d⟩ ⟨⟨⟨x', y'⟩, e'⟩, d'⟩
  rw [run_spectatorCall_apply]
  fin_cases y <;> fin_cases y' <;> simp [bellSpectator]

/-- For each fixed bit function, two calls restore every operator, including entangled inputs. -/
example (H : Fin 2 → Fin 2)
    (ρ : Matrix ((Reg × Fin 2) × Fin 2) ((Reg × Fin 2) × Fin 2) ℂ) :
    ((spectatorRuntime H).run₂ .instruments
      (spectatorCall.bind fun _ ↦ spectatorCall)).branch () ρ = ρ := by
  rw [QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_unit, LinearMap.comp_apply]
  ext ⟨⟨⟨x, y⟩, e⟩, d⟩ ⟨⟨⟨x', y'⟩, e'⟩, d'⟩
  rw [run_spectatorCall_apply, run_spectatorCall_apply]
  have h (a b : Fin 2) : a - b - b = a := by decide +revert
  rw [h, h]

/-- Evaluate the same oracle input twice and report whether its answers agree. -/
noncomputable def repeatRead : OracleComp (Fin 2 →ₒ Fin 2) Bool := do
  let a : Fin 2 ← query (spec := Fin 2 →ₒ Fin 2) 0
  let b : Fin 2 ← query (spec := Fin 2 →ₒ Fin 2) 0
  pure (decide (a = b))

/-- Each fixed function gives the exact distribution `δ_true` for repeated evaluation. -/
theorem repeatRead_fixed (H : Fin 2 → Fin 2) :
    (additiveOracleRuntime H).evalDist₂ .instruments repeatRead.toQuantum
      (SubState.basis ()) = Measure.dirac true := by
  rw [evalDist_additiveOracleRuntime_toQuantum]
  simp [repeatRead, evalWithAnswerFn_bind]

/-- Sampling one function for the whole QROM execution gives `δ_true`, with no disagreements. -/
example : qromEvalDist₂ .instruments repeatRead.toQuantum (SubState.basis ()) =
    Measure.dirac true := by
  rw [qromEvalDist₂_eq_sum]
  trans ((Fintype.card (Fin 2) : ℝ≥0∞) ^ Fintype.card (Fin 2))⁻¹ •
    ∑ _ : Fin 2 → Fin 2, (Measure.dirac true : Measure Bool)
  · congr 1
    exact Finset.sum_congr rfl fun H _ ↦ repeatRead_fixed H
  · norm_num [Finset.sum_const, Fintype.card_fun,
      ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul, ENNReal.inv_mul_cancel]

/-! ## Order and missing mass -/

/-- Reset a qubit to zero, discarding its input. -/
noncomputable def resetZero : SubInstrument (Fin 2) (Fin 2) Unit :=
  DSubInstrument.classical (B := fun _ ↦ _) (fun _ ↦ ()) (fun _ ↦ 0)

/-- Apply the bit flip then reset: on `|0⟩⟨0|`, the exact output is `diag(1,0)`. -/
example (H : Fin 2 → Fin 2) (d : (additiveOracleRuntime H).D) :
    ((additiveOracleRuntime H).run₂ .instruments
      ((QComp.act (A := QReg.of (Fin 2)) (B := QReg.of (Fin 2))
        (SubInstrument.ofIsometry pauliX conjTranspose_pauliX_mul_self)).bind
        fun _ ↦ QComp.act (A := QReg.of (Fin 2)) (B := QReg.of (Fin 2)) resetZero)).branch ()
      (Matrix.single (0, d) (0, d) 1) =
      Matrix.single (0, d) (0, d) 1 := by
  rw [QuantumRuntime.run₂_bind, QuantumRuntime.run₂_act, QuantumRuntime.run₂_act,
    SubInstrument.bind_pure, SubInstrument.bind_pure, DSubInstrument.branch_bind_unit,
    LinearMap.comp_apply, DSubInstrument.branch_frame_single,
    SubInstrument.branch_ofIsometry_apply]
  change (resetZero.frame _).branch ()
    (MatrixMap.conj (basisMatrix (Equiv.addRight (1 : Fin 2))) (Matrix.single 0 0 1) ⊗ₖ
      Matrix.single d d 1) = _
  rw [conj_basisMatrix_equiv_single, Matrix.single_kronecker_single, one_mul,
    DSubInstrument.branch_frame_single, resetZero, DSubInstrument.branch_classical_basis]
  simp [Matrix.single_kronecker_single]

/-- Reset then flip gives `diag(0,1)`, so the two channels do not commute. -/
example (H : Fin 2 → Fin 2) (d : (additiveOracleRuntime H).D) :
    ((additiveOracleRuntime H).run₂ .instruments
      ((QComp.act (A := QReg.of (Fin 2)) (B := QReg.of (Fin 2)) resetZero).bind fun _ ↦
        QComp.act (A := QReg.of (Fin 2)) (B := QReg.of (Fin 2))
        (SubInstrument.ofIsometry pauliX conjTranspose_pauliX_mul_self))).branch ()
      (Matrix.single (0, d) (0, d) 1) = Matrix.single (1, d) (1, d) 1 := by
  rw [QuantumRuntime.run₂_bind, QuantumRuntime.run₂_act, QuantumRuntime.run₂_act,
    SubInstrument.bind_pure, SubInstrument.bind_pure, DSubInstrument.branch_bind_unit,
    LinearMap.comp_apply, DSubInstrument.branch_frame_single, resetZero,
    DSubInstrument.branch_classical_basis]
  simp only [↓reduceDIte, cast_eq, Matrix.single_kronecker_single, one_mul]
  rw [DSubInstrument.branch_frame_single, SubInstrument.branch_ofIsometry_apply]
  change MatrixMap.conj (basisMatrix (Equiv.addRight (1 : Fin 2))) (Matrix.single 0 0 1) ⊗ₖ
    Matrix.single d d 1 = _
  rw [conj_basisMatrix_equiv_single, Matrix.single_kronecker_single, one_mul]
  rfl

/-- The geometric branch zero has input mass `1/2`; a pure program's observed distribution keeps
exactly that mass rather than normalizing it to one. -/
example (H : Fin 2 → Fin 2) :
    (additiveOracleRuntime H).evalDist₂ .instruments
      (QuantumComp₂.pure (L := LocalSig.instruments) (A := QReg.of Unit) ())
      (geometric.post (SubState.basis ()) 0) Set.univ = 2⁻¹ := by
  rw [QuantumRuntime.evalDist₂_apply_univ_of_lossless _ _
    (lossless_run₂_additiveOracleRuntime .instruments (QuantumComp₂.lossless_pure ()) H),
    trace_re_additiveOracleRuntime_init, mul_one]
  change ENNReal.ofReal (geometric.branch 0 (SubState.basis ()).matrix).trace.re = _
  rw [trace_geometric_branch, SubState.trace_basis, mul_one]
  norm_num [geomWeight, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]

/-! ## Erasing an unused query counter -/

/-- The trivial oracle with no counter and no effect on its port. -/
@[expose, reducible]
noncomputable def idleRuntime : QuantumRuntime countSpec where
  D := QReg.of Unit
  init := SubState.basis ()
  step _ := SubInstrument.pure ()

/-- The same trivial oracle with a private counter modulo three. -/
@[expose, reducible]
noncomputable def counterRuntime : QuantumRuntime countSpec where
  D := QReg.of (Unit × Fin 3)
  init := SubState.basis ((), 0)
  step _ := SubInstrument.relabel
    (Equiv.prodCongr (Equiv.refl Unit)
      (Equiv.prodCongr (Equiv.refl Unit) (Equiv.addRight (1 : Fin 3))))

/-- Partial trace forgets the private counter. -/
noncomputable abbrev eraseCounter : MatrixMap counterRuntime.D idleRuntime.D :=
  MatrixMap.traceRight Unit (Fin 3)

/-- Erasing the counter preserves trace. -/
theorem eraseCounter_isTP : eraseCounter.IsTP := MatrixMap.trace_traceRight

/-- Erasing the initial zero counter gives the initial state of the trivial oracle. -/
theorem eraseCounter_init : eraseCounter counterRuntime.init.matrix = idleRuntime.init.matrix := by
  ext ⟨⟩ ⟨⟩
  simp [eraseCounter, counterRuntime, idleRuntime, SubState.matrix_basis,
    MatrixMap.traceRight_apply, Matrix.single_apply]

/-- Incrementing the hidden counter commutes with forgetting it: the diagonal sum is unchanged. -/
theorem eraseCounter_step (i r : Unit) :
    (idleRuntime.step i).branch r ∘ₗ eraseCounter.amplifyLeft (countSpec.In i) =
      eraseCounter.amplifyLeft (countSpec.Out i) ∘ₗ (counterRuntime.step i).branch r := by
  cases i
  cases r
  ext ρ ⟨⟨⟩, ⟨⟩⟩ ⟨⟨⟩, ⟨⟩⟩
  simp only [SubInstrument.branch_pure_self, LinearMap.id_comp, MatrixMap.amplifyLeft_apply,
    MatrixMap.traceRight_apply, Matrix.submatrix_apply, LinearMap.coe_comp, Function.comp_apply,
    SubInstrument.relabel_branch_apply, Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.addRight_symm,
    Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.coe_addRight, Matrix.submatrix_submatrix,
    Prod.map_apply, id_eq, Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  change ρ ((), (), 0) ((), (), 0) +
      (ρ ((), (), 1) ((), (), 1) + ρ ((), (), 2) ((), (), 2)) =
    ρ ((), (), -1) ((), (), -1) +
      (ρ ((), (), 0) ((), (), 0) + ρ ((), (), 2 + -1) ((), (), 2 + -1))
  rw [show -(1 : Fin 3) = 2 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
  ring

/-- The simulation theorem applies to the adaptive coin program and the counter erasure. -/
example (b : Fin 2) :
    (idleRuntime.run₂ .instruments coinProg).branch b ∘ₗ
        eraseCounter.amplifyLeft (QReg.of (Fin 2)) =
      eraseCounter.amplifyLeft (QReg.of (Unit × Fin 2)) ∘ₗ
        (counterRuntime.run₂ .instruments coinProg).branch b :=
  QuantumRuntime.simulation₂ .instruments eraseCounter_step coinProg b

/-- Both runtimes leave exactly the same reduced operator on every adaptive-program branch. -/
example (ρ : SubState (Fin 2)) (b : Fin 2) :
    idleRuntime.reducedPost₂ .instruments coinProg ρ b =
      counterRuntime.reducedPost₂ .instruments coinProg ρ b :=
  QuantumRuntime.reducedPost₂_eq_of_simulation .instruments eraseCounter_step
    eraseCounter_isTP eraseCounter_init coinProg ρ b

/-- Forgetting the unused counter leaves the entire observed distribution unchanged. -/
example (ρ : SubState (Fin 2)) :
    idleRuntime.evalDist₂ .instruments coinProg ρ =
      counterRuntime.evalDist₂ .instruments coinProg ρ :=
  QuantumRuntime.evalDist₂_eq_of_simulation .instruments eraseCounter_step
    eraseCounter_isTP eraseCounter_init coinProg ρ

/-! ## The mixed-input counter distribution -/

/-- The fair classical coin, with density matrix `diag(1/2,1/2)`. -/
noncomputable def fairCoin : SubState (Fin 2) where
  matrix := Matrix.diagonal fun _ ↦ 1 / 2
  posSemidef := Matrix.PosSemidef.diagonal fun _ ↦ by norm_num [Complex.nonneg_iff]
  trace_re_le_one := by norm_num [Matrix.trace, Fin.sum_univ_two]

/-- The fair coin is the equal mixture of the two basis projectors. -/
theorem matrix_fairCoin : fairCoin.matrix =
    (1 / 2 : ℂ) • (Matrix.single 0 0 1 + Matrix.single 1 1 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [fairCoin, Matrix.diagonal, Matrix.single_apply]

/-- On a fair coin, branch `b` has weight `1/2` and counter `1` on zero or `2` on one. -/
theorem matrix_jointPost₂_coinProg_fairCoin (b : Fin 2) :
    (countRuntime.jointPost₂ .instruments coinProg fairCoin b).matrix =
      (1 / 2 : ℂ) •
        Matrix.single (((), b), if b = 1 then (2 : Fin 3) else 1)
          (((), b), if b = 1 then (2 : Fin 3) else 1) 1 := by
  rw [QuantumRuntime.matrix_jointPost₂, matrix_fairCoin, SubState.matrix_basis,
    Matrix.smul_kronecker, Matrix.add_kronecker, Matrix.single_kronecker_single,
    Matrix.single_kronecker_single, one_mul, map_smul, map_add,
    run_coinProg_branch_single, run_coinProg_branch_single]
  fin_cases b <;> simp [tick]

/-- Measuring a basis projector of weight `1/2` reports its label with that same weight. -/
theorem outcomeMeasure_classical_half_basis {A α : Type} [Fintype A] [DecidableEq A]
    {B : α → Type} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
    [MeasurableSpace α] (g : A → α) (f : (a : A) → B (g a)) (a : A) (ρ : SubState A)
    (hρ : ρ.matrix = (1 / 2 : ℂ) • Matrix.single a a 1) :
    (DSubInstrument.classical g f).outcomeMeasure ρ =
      (2 : ℝ≥0∞)⁻¹ • Measure.dirac (g a) := by
  rw [DSubInstrument.classical, DSubInstrument.outcomeMeasure_map_univ,
    Finset.sum_eq_single a (fun a' _ ha' ↦ ?_) (by simp)]
  · norm_num [hρ, Matrix.trace_smul,
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  · simp [hρ, ha']

/-- The joint distribution of the coin and a final computational-basis measurement of the private
counter. -/
noncomputable def coinCounterDist : Measure (Fin 2 × Fin 3) :=
  ∑ b : Fin 2,
    (DSubInstrument.classical (B := fun _ ↦ _)
      (fun m : (Unit × Fin 2) × Fin 3 ↦ (b, m.2)) id).outcomeMeasure
      (countRuntime.jointPost₂ .instruments coinProg fairCoin b)

/-- From the uniform mixture of `|0⟩` and `|1⟩`, the joint distribution of the returned bit and
the counter is `(1/2) δ(0, 1) + (1/2) δ(1, 2)`. -/
theorem coinCounterDist_eq : coinCounterDist =
    (2 : ℝ≥0∞)⁻¹ • Measure.dirac (0, 1) + (2 : ℝ≥0∞)⁻¹ • Measure.dirac (1, 2) := by
  unfold coinCounterDist
  simp_rw [outcomeMeasure_classical_half_basis (B := fun _ ↦ (Unit × Fin 2) × Fin 3) _ id _ _
    (matrix_jointPost₂_coinProg_fairCoin _)]
  simp [Fin.sum_univ_two]

end VCVioTest.QuantumOracle
