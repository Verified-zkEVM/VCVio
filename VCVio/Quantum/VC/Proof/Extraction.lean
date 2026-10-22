/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.Oracle.ClassicalCalls
public import VCVio.Quantum.Oracle.Compressed.Consistency
public import VCVio.Quantum.VC.CheckedRead
public import VCVio.Quantum.VC.Conditions

/-!
# Extraction correctness for compressed oracles

The checked accepting branch is conjugation by `C P C`, where `P` tests the prescribed
partial-table contents and `C` compresses all databases. Condition 3 puts every extracted
opening under `P`. The overlap identity `P (C P C) P = a P` therefore gives its exact
accepting weight, including zero-valued prescriptions.

An opening budget `h` bounds the error by `1 - (1 - 1/N)^(2 n h)`, independently of the
adversary's query bound and query masses. The arbitrary-proof budget `q2` supplies the
existing corollaries. Opening coins and extraction outcomes retain their original weights.

The ordinary-port basis-call equation is stated separately from checked acceptance.

The argument follows Chiesa, Di, Hu and Zheng, ePrint 2025/2166, Lemma 9.3, pp. 59–61.
-/

public section

open Matrix OracleSpec OracleComp
open scoped Kronecker ENNReal ComplexOrder

universe u v w u₁ v₁

namespace Quantum

/-! ## A projector against its compressed conjugate -/

section trace

variable {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]

/-- The conjugated pass projector retains exactly its overlap factor on a supported state. -/
theorem trace_re_conj_one_kronecker_eq {C P : Matrix S S ℂ} (hC : Cᴴ = C) (hCC : C * C = 1)
    (hP : Pᴴ = P) (hPP : P * P = P)
    {a : ℝ} (ha : P * (C * P * C) * P = (a : ℂ) • P) {φ : Matrix (B × S) (B × S) ℂ}
    (hφ : φ.PosSemidef) (hφP : ((1 : Matrix B B ℂ) ⊗ₖ P) * φ = φ) :
    a * φ.trace.re =
      (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (C * P * C)) φ).trace.re := by
  have hφPr : φ * ((1 : Matrix B B ℂ) ⊗ₖ P) = φ := by
    have h := congrArg conjTranspose hφP
    rwa [conjTranspose_mul, conjTranspose_kronecker, conjTranspose_one, hP,
      hφ.isHermitian.eq] at h
  set Q := (1 : Matrix B B ℂ) ⊗ₖ (C * P * C) with hQ
  have hQH : Qᴴ = Q := by
    rw [hQ, conjTranspose_kronecker, conjTranspose_one, conjTranspose_mul, conjTranspose_mul, hC,
      hP, Matrix.mul_assoc]
  have hQQ : Q * Q = Q := by
    rw [hQ, ← mul_kronecker_mul, Matrix.one_mul]
    congr 1
    rw [show C * P * C * (C * P * C) = C * P * (C * C) * P * C by simp only [Matrix.mul_assoc],
      hCC, Matrix.mul_one, Matrix.mul_assoc C P P, hPP]
  -- the trace of the Kraus map is the trace of `Q φ`
  have h1 : (MatrixMap.conj Q φ).trace = (Q * φ).trace := by
    rw [MatrixMap.conj_apply, hQH, Matrix.trace_mul_cycle, hQQ]
  have h2 : (((1 : Matrix B B ℂ) ⊗ₖ (C * P * C)) * φ).trace = (a : ℂ) * φ.trace := by
    calc (((1 : Matrix B B ℂ) ⊗ₖ (C * P * C)) * φ).trace
        = (((1 : Matrix B B ℂ) ⊗ₖ (C * P * C)) *
            (((1 : Matrix B B ℂ) ⊗ₖ P) * φ * ((1 : Matrix B B ℂ) ⊗ₖ P))).trace := by
          rw [hφP, hφPr]
      _ = ((((1 : Matrix B B ℂ) ⊗ₖ P) * ((1 : Matrix B B ℂ) ⊗ₖ (C * P * C)) *
            ((1 : Matrix B B ℂ) ⊗ₖ P)) * φ).trace := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
          simp only [Matrix.mul_assoc]
      _ = (a : ℂ) * φ.trace := by
          rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul, ha,
            kronecker_smul, smul_mul_assoc, trace_smul, hφP, smul_eq_mul]
  rw [h1, h2]
  simp

/-- `trace_re_conj_one_kronecker_eq` for a substate supported on a projector `Q ≤ P`: the
hypothesis `(1 ⊗ P) φ = φ` follows from `(1 ⊗ Q) φ (1 ⊗ Q)ᴴ = φ`. -/
theorem trace_re_conj_one_kronecker_eq_of_conj {C P Q : Matrix S S ℂ} (hC : Cᴴ = C)
    (hCC : C * C = 1) (hP : Pᴴ = P) (hPP : P * P = P) {a : ℝ}
    (ha : P * (C * P * C) * P = (a : ℂ) • P) (hPQ : P * Q = Q)
    {φ : Matrix (B × S) (B × S) ℂ} (hφ : φ.PosSemidef)
    (hφQ : MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ Q) φ = φ) :
    a * φ.trace.re =
      (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (C * P * C)) φ).trace.re := by
  refine trace_re_conj_one_kronecker_eq hC hCC hP hPP ha hφ ?_
  rw [← hφQ, MatrixMap.conj_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mul_kronecker_mul,
    Matrix.one_mul, hPQ]

end trace

/-! ## Classical checks against a conjugated table oracle -/

section checks

variable {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]

/-- Composing the Kraus maps of `1 ⊗ C D_p C` and then `1 ⊗ C D_q C`, for diagonal projectors
`D_p`, `D_q` and an involution `C`, gives the Kraus map of `1 ⊗ C D_{p ∧ q} C`. -/
theorem conj_one_kronecker_comp_conj_one_kronecker {C : Matrix S S ℂ} (hCC : C * C = 1)
    (p q : S → Prop) [DecidablePred p] [DecidablePred q] :
    MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (C * diagonal (fun d ↦ if q d then 1 else 0) * C)) ∘ₗ
        MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (C * diagonal (fun d ↦ if p d then 1 else 0) * C)) =
      MatrixMap.conj
        ((1 : Matrix B B ℂ) ⊗ₖ (C * diagonal (fun d ↦ if p d ∧ q d then 1 else 0) * C)) := by
  rw [← MatrixMap.conj_mul, ← mul_kronecker_mul, Matrix.one_mul]
  congr 2
  rw [show C * diagonal (fun d ↦ if q d then (1 : ℂ) else 0) * C *
      (C * diagonal (fun d ↦ if p d then 1 else 0) * C) =
      C * diagonal (fun d ↦ if q d then (1 : ℂ) else 0) * (C * C) *
        diagonal (fun d ↦ if p d then 1 else 0) * C by simp only [Matrix.mul_assoc],
    hCC, Matrix.mul_one, Matrix.mul_assoc C, diagonal_mul_diagonal]
  congr 3
  funext d
  by_cases hp : p d <;> by_cases hq : q d <;> simp [hp, hq]

/-- The Kraus map of `1 ⊗ C D C` for the full diagonal projector and an involution `C` is the
identity. -/
theorem conj_one_kronecker_true {C : Matrix S S ℂ} (hCC : C * C = 1) :
    MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
        (C * diagonal (fun _ : S ↦ if True then (1 : ℂ) else 0) * C)) = LinearMap.id := by
  simp only [↓reduceIte, diagonal_one, Matrix.mul_one, hCC, one_kronecker_one, MatrixMap.conj_one]

omit [Fintype B] [DecidableEq B] [Fintype S] in
/-- A diagonal `0/1` matrix is Hermitian. -/
theorem conjTranspose_diagonal_ite (p : S → Prop) [DecidablePred p] :
    (diagonal fun d ↦ if p d then (1 : ℂ) else 0)ᴴ = diagonal fun d ↦ if p d then 1 else 0 := by
  rw [diagonal_conjTranspose]
  congr 1
  funext d
  by_cases h : p d <;> simp [h]

omit [Fintype B] [DecidableEq B] in
/-- The product of two diagonal `0/1` matrices is the diagonal `0/1` matrix of the
conjunction. -/
theorem diagonal_ite_mul_diagonal_ite (p q : S → Prop) [DecidablePred p] [DecidablePred q] :
    (diagonal fun d ↦ if p d then (1 : ℂ) else 0) * (diagonal fun d ↦ if q d then 1 else 0) =
      diagonal fun d ↦ if p d ∧ q d then 1 else 0 := by
  rw [diagonal_mul_diagonal]
  congr 1
  funext d
  by_cases hp : p d <;> by_cases hq : q d <;> simp [hp, hq]

omit [Fintype B] [DecidableEq B] in
/-- A diagonal `0/1` matrix is idempotent. -/
theorem diagonal_ite_mul_self (p : S → Prop) [DecidablePred p] :
    (diagonal fun d ↦ if p d then (1 : ℂ) else 0) * (diagonal fun d ↦ if p d then 1 else 0) =
      diagonal fun d ↦ if p d then 1 else 0 := by
  rw [diagonal_ite_mul_diagonal_ite]
  simp only [and_self]

end checks

section runs

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {B : QReg}

/-- A classical algorithm run from inside an experiment, sequenced: the program of `oa >>= f` is
the program of `oa` followed by the programs of `f`. -/
theorem _root_.OracleComp.toQuantumAt_bind {ι : Type u} {ospec : OracleSpec.{u, v} ι}
    {α β : Type v} (q : QueryImpl ospec (QComp spec B B)) (oa : OracleComp ospec α)
    (f : α → OracleComp ospec β) :
    (oa >>= f).toQuantumAt q = (oa.toQuantumAt q).bind fun a ↦ (f a).toQuantumAt q := by
  rw [toQuantumAt, simulateQ_bind]
  rfl

variable {X Y : Type} [Fintype Y] [DecidableEq Y]

omit [Fintype Y] in
/-- **`CheckIO` against a conjugated table oracle.** Let every classical query `call t` have the
branch at the reading `y` given by the Kraus map of `1_B ⊗ C D_{t,y} C`, where `C` is an
involution of the runtime register and `D_{t,y}` the diagonal projector onto the registers `d`
with `read d t = y`. Then running `CheckIO` on the list `io` from the verdict `acc` accepts on the
Kraus map of `1_B ⊗ C D_io C`, with `D_io` the diagonal projector onto the registers that read
every listed output, when `acc` holds, and never otherwise. -/
theorem branch_run₂_toQuantumAt_foldlM_checkIOStep [Finite Y]
    (call : QueryImpl (X →ₒ Y) (QComp spec B B)) {C : Matrix R.D R.D ℂ} (hCC : C * C = 1)
    (read : R.D → X → Y)
    (hcall : ∀ t y, (R.run₂ .instruments (call t)).branch y =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
        (C * diagonal (fun d ↦ if read d t = y then 1 else 0) * C)))
    (io : List (X × Y)) (acc : Bool) :
    (R.run₂ .instruments ((io.foldlM checkIOStep acc).toQuantumAt call)).branch true =
      if acc then MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
        (C * diagonal (fun d ↦ if ∀ p ∈ io, read d p.1 = p.2 then 1 else 0) * C)) else 0 := by
  have : Fintype Y := Fintype.ofFinite Y
  induction io generalizing acc with
  | nil =>
    rw [List.foldlM_nil, toQuantumAt_pure, QuantumRuntime.run₂_pure]
    cases acc
    · exact SubInstrument.branch_pure_of_ne (by decide)
    · rw [SubInstrument.branch_pure_self, ite_eq_left rfl]
      simp only [List.not_mem_nil, false_imp_iff, imp_true_iff]
      exact (conj_one_kronecker_true hCC).symm
  | cons p io ih =>
    have hprog : ((p :: io).foldlM checkIOStep acc).toQuantumAt call =
        (call p.1).bind fun y ↦ (io.foldlM checkIOStep (acc && decide (y = p.2))).toQuantumAt
          call := by
      rw [List.foldlM_cons, checkIOStep, bind_assoc]
      simp only [pure_bind]
      exact toQuantumAt_query_bind call p.1 _
    rw [hprog, QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply_univ,
      Finset.sum_eq_single p.2]
    · rw [ih, hcall]
      simp only [decide_true, Bool.and_true]
      cases acc
      · simp
      · simp only [↓reduceIte]
        rw [conj_one_kronecker_comp_conj_one_kronecker hCC]
        congr 4
        funext d
        simp only [List.forall_mem_cons]
    · intro y _ hy
      rw [ih]
      simp [hy]
    · simp

/-- **A conjunction of checks against a conjugated table oracle.** If every check `f i`, `i ∈ W`,
accepts on the Kraus map of `1_B ⊗ C D_i C`, with `C` an involution and `D_i` the diagonal
projector onto the registers satisfying `g i`, then their conjunction `Quantum.QComp.allIn W f`
accepts on the Kraus map of `1_B ⊗ C D C`, with `D` the projector onto the registers satisfying
every `g i`, `i ∈ W`. -/
theorem branch_run₂_allIn {k : ℕ} (W : Finset (Fin k)) (f : Fin k → QComp spec B B Bool)
    {C : Matrix R.D R.D ℂ} (hCC : C * C = 1) (g : Fin k → R.D → Prop)
    [∀ i, DecidablePred (g i)]
    (hf : ∀ i ∈ W, (R.run₂ .instruments (f i)).branch true =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
        (C * diagonal (fun d ↦ if g i d then 1 else 0) * C))) :
    (R.run₂ .instruments (QComp.allIn W f)).branch true =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
        (C * diagonal (fun d ↦ if ∀ i ∈ W, g i d then 1 else 0) * C)) := by
  have key : ∀ (l : List (Fin k)) (acc : Bool),
      (R.run₂ .instruments (l.foldlM (fun acc i ↦ if i ∈ W then (acc && ·) <$> f i
        else pure acc) acc)).branch true =
      if acc then MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
        (C * diagonal (fun d ↦ if ∀ i ∈ l, i ∈ W → g i d then 1 else 0) * C)) else 0 := by
    intro l
    induction l with
    | nil =>
      intro acc
      rw [List.foldlM_nil, QuantumComp₂.pure_eq, QuantumRuntime.run₂_pure]
      cases acc
      · exact SubInstrument.branch_pure_of_ne (by decide)
      · rw [SubInstrument.branch_pure_self, ite_eq_left rfl]
        simp only [List.not_mem_nil, false_imp_iff, imp_true_iff]
        exact (conj_one_kronecker_true hCC).symm
    | cons i l ih =>
      intro acc
      rw [List.foldlM_cons]
      by_cases hi : i ∈ W
      · simp only [hi, ↓reduceIte, bind_map_left]
        rw [QuantumComp₂.bind_eq, QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply_univ,
          Fintype.sum_bool, ih, ih]
        cases acc
        · simp
        · simp only [Bool.true_and, ↓reduceIte, Bool.false_eq_true, LinearMap.zero_comp,
            add_zero]
          rw [hf i hi, conj_one_kronecker_comp_conj_one_kronecker hCC]
          congr 4
          funext d
          simp only [List.forall_mem_cons, hi, true_imp_iff]
      · simp only [hi, ↓reduceIte, pure_bind]
        rw [ih]
        congr 5
        funext d
        simp only [List.forall_mem_cons, hi, false_imp_iff, true_and]
  rw [QComp.allIn, key, ite_eq_left rfl]
  congr 4
  funext d
  simp only [List.mem_finRange, true_imp_iff]

/-! ### Coins -/

omit [Fintype Y] [DecidableEq Y] in
/-- **Coins act as scalars.** A randomized classical algorithm without oracle queries, run from
inside an experiment with its coins answered by uniform coins, has every branch a scalar multiple
of the identity, and the scalar vanishes at every value outside the support of the algorithm. -/
theorem exists_branch_run₂_toQuantumAt_coinImpl_eq_smul {α : Type} (oa : ProbComp α) (a : α) :
    ∃ c : ℂ, (R.run₂ .instruments (oa.toQuantumAt (QComp.coinImpl spec B))).branch a =
      c • LinearMap.id ∧ (a ∉ support oa → c = 0) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    rw [toQuantumAt_pure, QuantumRuntime.run₂_pure]
    by_cases h : a = x
    · subst h
      exact ⟨1, by rw [SubInstrument.branch_pure_self, one_smul], fun h' ↦ absurd (by simp) h'⟩
    · exact ⟨0, by rw [SubInstrument.branch_pure_of_ne h, zero_smul], fun _ ↦ rfl⟩
  | query_bind t k ih =>
    choose c hc hs using ih
    have hcoin (y : Fin (t + 1)) :
        (R.run₂ .instruments (QComp.coinImpl spec B t)).branch y =
          ((Fintype.card (Fin (t + 1)) : ℂ)⁻¹) • LinearMap.id := by
      rw [QComp.coinImpl, QuantumRuntime.run₂_act, SubInstrument.bind_pure,
        DSubInstrument.branch_frame_apply]
      refine LinearMap.ext fun ρ ↦ ?_
      ext x x'
      simp [SubInstrument.branch_uniform_apply]
    rw [toQuantumAt_query_bind, QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply_univ]
    refine ⟨∑ y, c y * (Fintype.card (Fin (t + 1)) : ℂ)⁻¹, ?_, fun ha ↦ ?_⟩
    · refine LinearMap.ext fun ρ ↦ ?_
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, hc, hcoin, LinearMap.smul_apply,
        LinearMap.id_apply, smul_smul, Finset.sum_smul]
    · refine Finset.sum_eq_zero fun y _ ↦ ?_
      rw [hs y fun hy ↦ ha ((mem_support_bind_iff _ _ _).mpr ⟨y, by simp, hy⟩), zero_mul]

omit [Fintype Y] [DecidableEq Y] in
/-- **Sequenced scalar programs act as scalars.** If every program `f i` has its branches scalar
multiples of the identity, vanishing off a set `S i`, so does `Quantum.QComp.pi f`, with the
scalar vanishing at every tuple that leaves some `S i`. -/
theorem exists_branch_run₂_pi_eq_smul : {k : ℕ} → {β : Fin k → Type w} →
    (f : (i : Fin k) → QComp spec B B (β i)) → (S : (i : Fin k) → Set (β i)) →
    (∀ i (b : β i), ∃ c : ℂ, (R.run₂ .instruments (f i)).branch b = c • LinearMap.id ∧
      (b ∉ S i → c = 0)) → (v : (i : Fin k) → β i) →
    ∃ c : ℂ, (R.run₂ .instruments (QComp.pi f)).branch v = c • LinearMap.id ∧
      ((∃ i, v i ∉ S i) → c = 0)
  | 0, _, f, S, _, v => by
    have hv : v = fun i ↦ i.elim0 := funext fun i ↦ i.elim0
    refine ⟨1, ?_, fun ⟨i, _⟩ ↦ i.elim0⟩
    rw [QComp.pi, QuantumRuntime.run₂_pure, hv, SubInstrument.branch_pure_self, one_smul]
  | k + 1, β, f, S, hf, v => by
    obtain ⟨c₀, hc₀, hs₀⟩ := hf 0 (v 0)
    obtain ⟨c₁, hc₁, hs₁⟩ := exists_branch_run₂_pi_eq_smul (fun i ↦ f i.succ)
      (fun i ↦ S i.succ) (fun i b ↦ hf i.succ b) (Fin.tail v)
    refine ⟨c₁ * c₀, ?_, fun ⟨i, hi⟩ ↦ ?_⟩
    · refine LinearMap.ext fun ρ ↦ ?_
      rw [QComp.pi, QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply,
        tsum_eq_single (v 0)]
      · rw [QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply, tsum_eq_single (Fin.tail v)]
        · rw [QuantumRuntime.run₂_pure, Fin.cons_self_tail, SubInstrument.branch_pure_self,
            LinearMap.id_apply, hc₁, hc₀]
          simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
        · intro bs hbs
          rw [QuantumRuntime.run₂_pure, SubInstrument.branch_pure_of_ne, LinearMap.zero_apply]
          intro h
          exact hbs (by rw [h, Fin.tail_cons])
      · intro b hb
        rw [QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply]
        refine (tsum_congr fun bs ↦ ?_).trans tsum_zero
        rw [QuantumRuntime.run₂_pure, SubInstrument.branch_pure_of_ne, LinearMap.zero_apply]
        intro h
        exact hb (by rw [h, Fin.cons_zero])
    · refine Fin.cases (fun h ↦ by rw [hs₀ h, mul_zero]) (fun j h ↦ ?_) i hi
      rw [hs₁ ⟨j, h⟩, zero_mul]

end runs

/-! ## Classical queries of the compressed oracles -/

section oracleCall

/-- A block of a matrix conjugated by `1 ⊗ C` is the block conjugated by `C`. -/
theorem submatrix_one_kronecker_mul_mul_one_kronecker {A S : Type*} [Fintype A] [DecidableEq A]
    [Fintype S] (C : Matrix S S ℂ) (M : Matrix (A × S) (A × S) ℂ) (a b : A) :
    (((1 : Matrix A A ℂ) ⊗ₖ C) * M * ((1 : Matrix A A ℂ) ⊗ₖ C)).submatrix (fun d ↦ (a, d))
        (fun d ↦ (b, d)) =
      C * M.submatrix (fun d ↦ (a, d)) (fun d ↦ (b, d)) * C := by
  ext d d'
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, Finset.sum_mul,
    ite_mul, mul_ite]

variable {X Y T : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [Fintype T] [DecidableEq T]

omit [Fintype X] [Fintype Y] [Fintype T] in
/-- A block of the table oracle on a query input `|t, 0⟩` is diagonal: it is the projector onto
the tables that read `y'` at `t`, if the output is `|t', y'⟩` with `t' = t`, and zero otherwise. -/
theorem submatrix_tableOracle (read : T → X → Y) (t t' : X) (y' : Y) :
    (tableOracle read).submatrix (fun d ↦ (((t', y') : X × Y), d))
        (fun d ↦ (((t, 0) : X × Y), d)) =
      diagonal fun d ↦ if t' = t ∧ read d t = y' then 1 else 0 := by
  ext d d'
  simp only [submatrix_apply, tableOracle_apply, tableOracleEquiv_apply, oracleEquiv_apply,
    zero_add, Prod.mk.injEq, diagonal_apply]
  by_cases h : d = d'
  · subst h
    by_cases h₁ : t' = t <;> by_cases h₂ : read d t = y' <;> simp_all [eq_comm]
  · simp [h]

section compressed

variable {k : ℕ} {X Y Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  {Dm : Fin k → Type} (ME : MultiExtractor k Cm Dm (compressedVCOracle k X Y).S)
  (code : TpDCode k Dm Z)

/-- **A classical query of a compressed oracle.** Querying oracle `j` at `t` from inside an
experiment against `EO^(Ext)` for the `k` compressed oracles reads `y` on the Kraus map of
`1_B ⊗ C D C`, where `C` compresses every database and `D` is the diagonal projector onto the
databases with `D_j(t) = y`, an empty cell reading `0`. This is
`Quantum.compressedVCOracle_U_eq_conj` on the block of the query input `|t, 0⟩`. -/
theorem branch_run₂_oracleCall_compressedVCOracle (B : QReg) (j : Fin k) (t : X) (y : Y) :
    (((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime.run₂ .instruments
        (oracleCall (Cm := Cm) (Z := Z) B j t)).branch y =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (compressDatabases k X Y *
        diagonal (fun D : Fin k → Database X Y ↦ if (D j).lookup t = y then 1 else 0) *
        compressDatabases k X Y)) := by
  have hblock : ∀ (t' : X) (y' : Y),
      ((compressedVCOracle k X Y).withExtract ME code).coherent.block ()
          ⟨.inl j, ((t', y') : X × Y)⟩ ⟨.inl j, ((t, 0) : X × Y)⟩ =
        compressDatabases k X Y *
          diagonal (fun D : Fin k → Database X Y ↦ if t' = t ∧ (D j).lookup t = y' then 1 else 0) *
          compressDatabases k X Y := by
    intro t' y'
    ext d d'
    have h := congrFun (congrFun (submatrix_one_kronecker_mul_mul_one_kronecker
      (compressDatabases k X Y) (tableOracle fun D : Fin k → Database X Y ↦ (D j).lookup)
      ((t', y') : X × Y) ((t, 0) : X × Y)) d) d'
    rw [submatrix_tableOracle] at h
    refine (EmulatedOracle.coherent_U_apply_self _ (Sum.inl j) _ _ _ _).trans (Eq.trans ?_ h)
    exact congrFun (congrFun (compressedVCOracle_U_eq_conj j) _) _
  have hread : ∀ (i : Fin k) (m : X × Y),
      readY (Cm := Cm) (Z := Z) (⟨.inl i, m⟩ : Σ i, extIn k X Y Cm Z i) = m.2 := fun _ _ ↦ rfl
  rw [oracleCall, EmulatedOracle.branch_run₂_callBasis,
    Finset.sum_eq_single (⟨.inl j, ((t, y) : X × Y)⟩ : Σ i, extIn k X Y Cm Z i)]
  · simp only [hread, ↓reduceIte, hblock, true_and]
  · rintro ⟨i | u, m⟩ _ hne
    · by_cases hij : i = j
      · subst hij
        obtain ⟨t', y'⟩ := m
        by_cases hy : y' = y
        · subst hy
          have ht : t' ≠ t := fun ht ↦ hne (by rw [ht])
          have hb : ((compressedVCOracle k X Y).withExtract ME code).coherent.block ()
              ⟨.inl i, ((t', y') : X × Y)⟩ ⟨.inl i, ((t, 0) : X × Y)⟩ = 0 := by
            rw [hblock]
            ext d d'
            simp only [ht, false_and, ↓reduceIte, diagonal_zero, Matrix.mul_zero]
            exact congrFun (congrFun (Matrix.zero_mul (compressDatabases k X Y)) d) d'
          rw [hb, kronecker_zero, MatrixMap.conj_zero, ite_self]
        · exact ite_eq_right_of_eq_false _ _ (eq_false hy)
      · have hb : ((compressedVCOracle k X Y).withExtract ME code).coherent.block ()
            ⟨.inl i, m⟩ ⟨.inl j, ((t, 0) : X × Y)⟩ = 0 := by
          ext d d'
          rw [EmulatedOracle.block_apply]
          exact EmulatedOracle.coherent_U_apply_of_ne _ (fun h ↦ hij (Sum.inl_injective h)) _ _ _ _
        rw [hb, kronecker_zero, MatrixMap.conj_zero, ite_self]
    · have hb : ((compressedVCOracle k X Y).withExtract ME code).coherent.block ()
          ⟨.inr u, m⟩ ⟨.inl j, ((t, 0) : X × Y)⟩ = 0 := by
        ext d d'
        rw [EmulatedOracle.block_apply]
        exact EmulatedOracle.coherent_U_apply_of_ne _ Sum.inr_ne_inl _ _ _ _
      rw [hb, kronecker_zero, MatrixMap.conj_zero, ite_self]
  · simp

end compressed

end oracleCall

/-! ## The law of an experiment -/

section experiment

open MeasureTheory

/-- **Bounding the law of an experiment leaf by leaf.** If, from every joint substate `σ` at
every leaf `⟨u, y⟩` of the adversary, the challenger `chal u y` reports `true` with weight at
most `ε` times the trace of `σ`, then the experiment reports `true` with probability at most
`ε`. -/
theorem outcomeLawWith_experiment_true_le {spec : QuantumOracleSpec.{u₁, v₁}} {A : QReg}
    {W : QReg → Type w} (R : QuantumRuntime spec)
    (x : QuantumComp LocalSig.instruments.{v} spec W A)
    (chal : ∀ u, W u → QComp.{u₁, v₁, 0} spec u u Bool) (ρ : SubState A) {ε : ℝ≥0∞}
    (h : ∀ u (y : W u) (σ : SubState (u × R.D)),
      (R.run₂ .instruments (chal u y)).outcomeMeasure σ {true} ≤
        ε * ENNReal.ofReal σ.matrix.trace.re) :
    R.evalDistMap .instruments (experiment x chal) ρ Sigma.snd {true} ≤ ε := by
  let _ : MeasurableSpace (Σ u, W u) := ⊤
  rw [evalDistMap_experiment_true_eq_tsum]
  calc ∑' p, (R.run₂ .instruments (chal p.1 p.2)).outcomeMeasure
          ((R.run .instruments x).post (ρ.prod R.init) p) {true}
      ≤ ∑' p : Σ u, W u, ε * ENNReal.ofReal
          ((R.run .instruments x).post (ρ.prod R.init) p).matrix.trace.re :=
        ENNReal.tsum_le_tsum fun p ↦ h p.1 p.2 _
    _ = ε * (R.run .instruments x).outcomeMeasure (ρ.prod R.init) Set.univ := by
        rw [ENNReal.tsum_mul_left, DSubInstrument.outcomeMeasure_apply _ _ MeasurableSet.univ]
        simp [DSubInstrument.matrix_post]
    _ ≤ ε * 1 := by gcongr; exact DSubInstrument.outcomeMeasure_apply_univ_le_one _ _
    _ = ε := mul_one ε

/-- **A uniform bound through a composite.** If, after every outcome `a` of `p`, the continuation
`k a` puts weight at most `ε` times the trace of the post-branch substate on `s`, then the
composite puts weight at most `ε` times the trace of the input on `s`. -/
theorem SubInstrument.outcomeMeasure_bind_le {A B C : Type*} [Fintype A] [Fintype B]
    [Fintype C] {α β : Type*} [MeasurableSpace β] (p : SubInstrument A B α)
    (k : α → SubInstrument B C β) (ρ : SubState A) {s : Set β} (hs : MeasurableSet s)
    {ε : ℝ≥0∞}
    (h : ∀ a, (k a).outcomeMeasure (p.post ρ a) s ≤
      ε * ENNReal.ofReal (p.branch a ρ.matrix).trace.re) :
    (p.bind k).outcomeMeasure ρ s ≤ ε * ENNReal.ofReal ρ.matrix.trace.re := by
  let _ : MeasurableSpace α := ⊤
  rw [DSubInstrument.outcomeMeasure_bind, Measure.sum_apply _ hs]
  calc ∑' a, (k a).outcomeMeasure (p.post ρ a) s
      ≤ ∑' a, ε * ENNReal.ofReal (p.branch a ρ.matrix).trace.re := ENNReal.tsum_le_tsum h
    _ = ε * p.outcomeMeasure ρ Set.univ := by
        rw [ENNReal.tsum_mul_left, DSubInstrument.outcomeMeasure_apply _ _ MeasurableSet.univ]
        simp
    _ ≤ ε * ENNReal.ofReal ρ.matrix.trace.re := by
        rw [SubInstrument.outcomeMeasure_apply_univ]
        exact mul_le_mul_of_nonneg_left
          (ENNReal.ofReal_le_ofReal (p.isTNI_total _ ρ.posSemidef)) zero_le

/-- A substate with zero matrix has the zero outcome measure. -/
theorem SubInstrument.outcomeMeasure_eq_zero_of_matrix_eq_zero {A B : Type*} [Fintype A]
    [Fintype B] {α : Type*} [MeasurableSpace α] (p : SubInstrument A B α) {ρ : SubState A}
    (hρ : ρ.matrix = 0) : p.outcomeMeasure ρ = 0 := by
  rw [DSubInstrument.outcomeMeasure_eq_sum, hρ]
  simp

/-- For a lossless subinstrument with two outcomes, the traces of the two branches add up to the
trace of the input. -/
theorem SubInstrument.trace_re_branch_add_of_lossless {A B : Type*} [Fintype A] [Fintype B]
    {p : SubInstrument A B Bool} (hp : p.Lossless) (ρ : Matrix A A ℂ) :
    (p.branch true ρ).trace.re + (p.branch false ρ).trace.re = ρ.trace.re := by
  rw [← hp ρ, MatrixMap.familyTrace_apply_univ, Fintype.sum_bool, Complex.add_re]

end experiment

/-! ## The pass projector of a set of checks -/

section passProjector

variable {k : ℕ} {X Y Msg Cm : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)} (io : ∀ i, (VC i).NonadaptiveCheck)

/-- **The pass projector of the checks on `W`** (ePrint 2025/2166, p. 61): the diagonal
projector onto the tuples of databases `D` on which every check `VC_i.Check^{D_{idx i}}` with
`i ∈ W` passes, read on the partial tables themselves (`checkOn`). Conjugating this projector
`P` by database compression `C` gives the checked accepting projector `C P C`. -/
@[expose]
noncomputable def checkPassProjector (W : Finset (Fin k)) (idx : Fin k → Fin k) (cm : Fin k → Cm)
    (ans : ∀ i, PartialVec (ℓ i) Msg) (pf : ∀ i, Pf i) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  diagonal fun D ↦ if ∀ i ∈ W, (io i).checkOn (D (idx i)) (cm i) (ans i) (pf i) = true then 1 else 0

/-- The pass projector against its compressed conjugate, with an explicit bound `q` on
these proofs' output lists: the acceptance factor is at least `(1 - 1/N)^(2 n q)`. -/
theorem exists_le_checkPassProjector_conj_of_length_le (n : ℕ) (W : Finset (Fin k))
    (hW : W.card ≤ n)
    (idx : Fin k → Fin k) (cm : Fin k → Cm) (ans : ∀ i, PartialVec (ℓ i) Msg) (pf : ∀ i, Pf i)
    (q : ℕ)
    (hlen : ∀ i, (((io i).pairs (cm i) (ans i) (pf i)).getD []).length ≤ q) :
    ∃ a : ℝ, (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * n * q) ≤ a ∧
      checkPassProjector io W idx cm ans pf *
          (compressDatabases k X Y * checkPassProjector io W idx cm ans pf *
            compressDatabases k X Y) * checkPassProjector io W idx cm ans pf =
        (a : ℂ) • checkPassProjector io W idx cm ans pf := by
  have hN : (0 : ℝ) ≤ 1 - (Fintype.card Y : ℝ)⁻¹ :=
    sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos))
  have hN1 : 1 - (Fintype.card Y : ℝ)⁻¹ ≤ 1 := sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  by_cases hall : ∀ i ∈ W, ((io i).pairs (cm i) (ans i) (pf i)).isSome
  · -- the prescriptions on each database
    let L : Fin k → List (X × Y) := fun j ↦ (List.finRange k).flatMap fun i ↦
      if i ∈ W ∧ idx i = j then ((io i).pairs (cm i) (ans i) (pf i)).getD [] else []
    have hmem : ∀ j p, p ∈ L j ↔ ∃ i, (i ∈ W ∧ idx i = j) ∧
        p ∈ ((io i).pairs (cm i) (ans i) (pf i)).getD [] := by
      intro j p
      simp only [L, List.mem_flatMap, List.mem_finRange, true_and]
      refine exists_congr fun i ↦ ?_
      split_ifs with h <;> simp [h]
    have hc : ∀ (D : Fin k → Database X Y), ∀ i ∈ W,
        ((io i).checkOn (D (idx i)) (cm i) (ans i) (pf i) = true ↔
          ∀ p ∈ ((io i).pairs (cm i) (ans i) (pf i)).getD [], D (idx i) p.1 = some p.2) := by
      intro D i hi
      obtain ⟨Li, hLi⟩ := Option.isSome_iff_exists.mp (hall i hi)
      simp [VectorCommitment.NonadaptiveCheck.checkOn, hLi, checkIOOn_eq_true_iff]
    have hP : checkPassProjector io W idx cm ans pf = piKron fun j ↦ checkProjector Y (L j) := by
      ext D D'
      rw [checkPassProjector, piKron_apply, diagonal_apply]
      simp_rw [checkProjector_apply]
      by_cases hD : D = D'
      · subst hD
        have key : (∀ i ∈ W, (io i).checkOn (D (idx i)) (cm i) (ans i) (pf i) = true) ↔
            ∀ j, ∀ p ∈ L j, D j p.1 = some p.2 := by
          refine ⟨fun h j p hp ↦ ?_, fun h i hi ↦ (hc D i hi).mpr fun p hp ↦ ?_⟩
          · obtain ⟨i, ⟨hiW, rfl⟩, hpi⟩ := (hmem j p).mp hp
            exact (hc D i hiW).mp (h i hiW) p hpi
          · exact h (idx i) p ((hmem _ p).mpr ⟨i, ⟨hi, rfl⟩, hp⟩)
        simp only [true_and, ↓reduceIte]
        rw [Finset.prod_boole]
        simp only [Finset.mem_univ, forall_const]
        split_ifs with h₁ h₂ h₂
        · rfl
        · exact absurd (key.mp h₁) h₂
        · exact absurd (key.mpr h₂) h₁
        · rfl
      · obtain ⟨j, hj⟩ := Function.ne_iff.mp hD
        simp only [hD, ↓reduceIte]
        exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm
    have hcells : ∑ j, (ioCells (L j)).card ≤ n * q :=
      calc ∑ j, (ioCells (L j)).card
          ≤ ∑ j, (L j).length := Finset.sum_le_sum fun j _ ↦ card_ioCells_le_length _
        _ = ∑ i ∈ W, (((io i).pairs (cm i) (ans i) (pf i)).getD []).length := by
            simp only [L, List.length_flatMap, ← Fin.sum_univ_def, apply_ite List.length,
              List.length_nil, ite_and]
            simp only [Finset.sum_ite_mem, Finset.univ_inter]
            rw [Finset.sum_comm]
            simp
        _ ≤ ∑ i ∈ W, q := Finset.sum_le_sum fun i _ ↦ hlen i
        _ = W.card * q := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ n * q := Nat.mul_le_mul_right _ hW
    refine ⟨(1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * ∑ j, (ioCells (L j)).card),
      pow_le_pow_of_le_one hN hN1 (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 2 hcells), ?_⟩
    have hCPC : compressDatabases k X Y * piKron (fun j ↦ checkProjector Y (L j)) *
        compressDatabases k X Y = piKron fun j ↦ compressedCheckProjector (L j) := by
      rw [compressDatabases, piKron_mul, piKron_mul]
      rfl
    rw [hP, hCPC, piKron_checkProjector_mul_piKron_compressedCheckProjector_mul]
    push_cast
    rfl
  · simp only [not_forall] at hall
    obtain ⟨i, hi, hn⟩ := hall
    have hP0 : checkPassProjector io W idx cm ans pf = 0 := by
      rw [checkPassProjector, ← diagonal_zero]
      congr 1
      funext D
      refine ite_eq_right_iff.mpr fun h ↦ ?_
      have := h i hi
      simp [VectorCommitment.NonadaptiveCheck.checkOn, Option.not_isSome_iff_eq_none.mp hn] at this
    exact ⟨_, le_rfl, by simp [hP0]⟩

/-- The pass projector against its compressed conjugate. For `|W| ≤ n`, `P (C P C) P = a P` with
`a ≥ (1 - 1/N)^{2 n q2}`, where `C` compresses every database. When every check on `W` parses,
`P` is the product of the consistency projectors of the prescriptions on each database, and `a`
is `(1 - 1/N)^{2d}` for the number `d ≤ n q2` of prescribed cells; otherwise `P = 0`. -/
theorem exists_le_checkPassProjector_conj (n : ℕ) (W : Finset (Fin k)) (hW : W.card ≤ n)
    (idx : Fin k → Fin k) (cm : Fin k → Cm) (ans : ∀ i, PartialVec (ℓ i) Msg) (pf : ∀ i, Pf i) :
    ∃ a : ℝ, (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * n * q2 io) ≤ a ∧
      checkPassProjector io W idx cm ans pf *
          (compressDatabases k X Y * checkPassProjector io W idx cm ans pf *
            compressDatabases k X Y) * checkPassProjector io W idx cm ans pf =
        (a : ℂ) • checkPassProjector io W idx cm ans pf := by
  apply exists_le_checkPassProjector_conj_of_length_le io n W hW idx cm ans pf (q2 io)
  intro i
  cases h : (io i).pairs (cm i) (ans i) (pf i) with
  | none => simp
  | some L => exact ((io i).length_le _ _ _ _ h).trans (qVC_card_dom_le_q2 io i (ans i))

end passProjector

section filledBatch

variable {k : ℕ} {X Y Msg Cm : Type} [DecidableEq Y] {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)}
  (io : ∀ i, (VC i).NonadaptiveCheck) [Fintype X] [DecidableEq X] [Fintype Y] [AddCommGroup Y]

/-- The accepting projector of the batch of checked reads. -/
@[expose]
noncomputable def filledBatch (W : Finset (Fin k)) (c : OpeningClaim k Cm Msg ℓ Pf) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  compressDatabases k X Y * checkPassProjector io W c.idx c.cm c.ans c.pf *
    compressDatabases k X Y

end filledBatch

/-- The extraction projector `Π_tdm` is idempotent. -/
theorem extractProj_mul_self {k : ℕ} {Cm : Type} {S : Type*} [Fintype S] [DecidableEq S]
    {Dm : Fin k → Type} [∀ i, DecidableEq (Dm i)] (ME : MultiExtractor k Cm Dm S)
    (tic : TpIC k Cm) (tdm : TpDLen k Dm tic.1) :
    extractProj ME tic tdm * extractProj ME tic tdm = extractProj ME tic tdm :=
  diagonal_ite_mul_self _

/-! ## The error of Lemma 9.3 -/

section extractError

variable {k : ℕ} {X Y Msg Cm : Type} [Fintype Y] [DecidableEq Y] {ℓ : Fin k → ℕ}
  {Td Pf : Fin k → Type} {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)}
  (io : ∀ i, (VC i).NonadaptiveCheck)

/-- **The error of Lemma 9.3, exact form**: `1 - (1 - 1/N)^{2 n q2}` (ePrint 2025/2166),
with `N = |Y|`. It is at most `2 n q2 / N`
(`Quantum.extractError_le_two_mul`); the paper has `8 n q2 / N` (p. 59). -/
@[expose]
noncomputable def extractError (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * n * q2 io))

/-- The exact error of Lemma 9.3 is at most its leading order `2 n q2 / N`. -/
theorem extractError_le_two_mul (n : ℕ) :
    extractError io n ≤ (2 * n * q2 io : ℝ≥0∞) / Fintype.card Y := by
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with h0 | hpos
  · simp [extractError, h0]
  have hN : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr hpos
  have hN1 : (1 : ℝ) ≤ Fintype.card Y := Nat.one_le_cast.mpr hpos
  calc extractError io n
      ≤ ENNReal.ofReal (((2 * n * q2 io : ℕ) : ℝ) / Fintype.card Y) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_eq_mul_inv]
        exact one_sub_one_sub_pow_le _ ((inv_le_one_of_one_le₀ hN1).trans one_le_two)
    _ = (2 * n * q2 io : ℝ≥0∞) / Fintype.card Y := by
        rw [ENNReal.ofReal_div_of_pos hN, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
        push_cast
        rfl

end extractError

/-! ## The P3 challenger against the compressed oracles -/

section challenger

variable {k : ℕ} {X Y Msg Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)} (io : ∀ i, (VC i).NonadaptiveCheck)
  (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) (compressedVCOracle k X Y).S)
  (code : TpDCode k (DmOf ℓ Msg Td) Z) {tdBot : ∀ i, Td i} {Pgood : Set (Database X Y)}

/-- A batch of checked reads accepts exactly by conjugation with its filled batch projector,
including malformed claims and conflicting prescriptions. -/
theorem branch_run₂_filledBatch_compressedVCOracle (B : QReg) (W : Finset (Fin k))
    (c : OpeningClaim k Cm Msg ℓ Pf) :
    (((compressedVCOracle k X Y).mixedExtractRuntime ME code).run₂ .instruments
      (QComp.allIn W fun i ↦ checkAt VC B i (c.idx i) (c.cm i) (c.ans i) (c.pf i))).branch true =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ filledBatch io W c) := by
  exact branch_run₂_allIn ((compressedVCOracle k X Y).mixedExtractRuntime ME code) W
    (fun i ↦ checkAt VC B i (c.idx i) (c.cm i) (c.ans i) (c.pf i))
    (compressDatabases_mul_self k X Y)
    (fun i (D : Fin k → Database X Y) ↦
      (io i).checkOn (D (c.idx i)) (c.cm i) (c.ans i) (c.pf i) = true)
    (fun i _ ↦ branch_run₂_checkAt_compressedVCOracle VC ME code io B i (c.idx i) (c.cm i)
      (c.ans i) (c.pf i))

/-- The checks after extraction with an opening-specific cell budget. -/
theorem outcomeMeasure_run₂_checks_le_of_openingQueryBound [∀ i, DecidableEq (DmOf ℓ Msg Td i)]
    (q : ℕ) (hq : OpeningQueryBound io q)
    (hC : Conditions VC io ME tdBot Pgood) (hk : 1 ≤ k) (n : ℕ) (c : ExtractClaim k Cm)
    {B : QReg} (tdm : TpDLen k (DmOf ℓ Msg Td) (TpIC.full hk c.idx c.cm).1) (pf : ∀ i, Pf i)
    (hpf : ∀ i, pf i ∈ support ((VC i).opening (tdm i).1.dom (tdm i).2))
    (ρ : SubState (B × ((compressedVCOracle k X Y).mixedExtractRuntime ME code).D))
    (hρ : MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ diagonal fun D : Fin k → Database X Y ↦
      if ME.extract (TpIC.full hk c.idx c.cm) D = tdm then 1 else 0) ρ.matrix = ρ.matrix) :
    (((compressedVCOracle k X Y).mixedExtractRuntime ME code).run₂ .instruments
        ((QComp.allIn c.W fun i ↦ checkAt (Z := Z) VC B i (c.idx i) (c.cm i) (tdm i).1
          (pf i)).bind fun b ↦ QuantumComp₂.pure
            (!b && decide (c.W.card ≤ n) && decide (Function.Injective c.idx)))).outcomeMeasure
        ρ {true} ≤
      ENNReal.ofReal (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * n * q)) *
        ENNReal.ofReal ρ.matrix.trace.re := by
  rw [QuantumRuntime.run₂_bind, DSubInstrument.outcomeMeasure_apply_singleton,
    DSubInstrument.branch_bind_apply_univ, Fintype.sum_bool]
  simp only [QuantumRuntime.run₂_pure, Bool.not_true, Bool.false_and, Bool.not_false,
    Bool.true_and]
  rw [SubInstrument.branch_pure_of_ne (by decide : true ≠ false), LinearMap.zero_comp, zero_add]
  by_cases hcond : c.W.card ≤ n ∧ Function.Injective c.idx
  · obtain ⟨hW, hinj⟩ := hcond
    simp only [hW, hinj, decide_true, Bool.and_self, SubInstrument.branch_pure_self,
      LinearMap.id_comp]
    have hN : (0 : ℝ) ≤ 1 - (Fintype.card Y : ℝ)⁻¹ :=
      sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos))
    have hN1 : 1 - (Fintype.card Y : ℝ)⁻¹ ≤ 1 :=
      sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))
    have hCC := compressDatabases_mul_self (k := k) (X := X) (Y := Y)
    have hloss := QuantumRuntime.lossless_run₂
      ((compressedVCOracle k X Y).mixedExtractRuntime ME code) .instruments
      (QComp.lossless_allIn (W := c.W) (B := B) (f := fun i ↦ checkAt (Z := Z) VC B i (c.idx i)
        (c.cm i) (tdm i).1 (pf i)) fun i _ ↦ lossless_checkAt VC _ _ _ _ _ _)
      ((compressedVCOracle k X Y).lossless_mixedExtractRuntime_step ME code)
    have hsum := SubInstrument.trace_re_branch_add_of_lossless hloss ρ.matrix
    obtain ⟨a, ha0, ha⟩ := exists_le_checkPassProjector_conj_of_length_le io n c.W hW c.idx c.cm
      (fun i ↦ (tdm i).1) pf q (by
        intro i
        cases hL : (io i).pairs (c.cm i) (tdm i).1 (pf i) with
        | none => simp
        | some L => exact hq i (c.cm i) (tdm i).1 (tdm i).2 (pf i) (hpf i) L hL)
    -- the checks on the partial tables pass under the extraction outcome (condition 3)
    have hPQ : checkPassProjector io c.W c.idx c.cm (fun i ↦ (tdm i).1) pf *
        (diagonal fun D : Fin k → Database X Y ↦
          if ME.extract (TpIC.full hk c.idx c.cm) D = tdm then 1 else 0) =
        diagonal fun D : Fin k → Database X Y ↦
          if ME.extract (TpIC.full hk c.idx c.cm) D = tdm then 1 else 0 := by
      rw [checkPassProjector, diagonal_ite_mul_diagonal_ite]
      congr 1
      funext D
      by_cases hD : ME.extract (TpIC.full hk c.idx c.cm) D = tdm
      · have hD' : @MultiExtractor.extract _ _ _ (Fin k → Database X Y) ME
            (TpIC.full hk c.idx c.cm) D = tdm := hD
        refine (ite_eq_left_iff.mpr fun h ↦ absurd ⟨fun i _ ↦ ?_, hD⟩ h).trans
          (ite_eq_left_iff.mpr fun h ↦ absurd hD h).symm
        have hv := hC.valid hk c.idx hinj c.cm D i
        rw [hD'] at hv
        exact hv (pf i) (hpf i)
      · simp [hD]
    have htrue : a * ρ.matrix.trace.re ≤
        ((((compressedVCOracle k X Y).mixedExtractRuntime ME code).run₂ .instruments
          (QComp.allIn c.W fun i ↦ checkAt (Z := Z) VC B i (c.idx i) (c.cm i) (tdm i).1
            (pf i))).branch true ρ.matrix).trace.re := by
      rw [branch_run₂_filledBatch_compressedVCOracle io ME code B c.W
        ⟨c.idx, c.cm, (fun i ↦ (tdm i).1), pf, c.W⟩]
      exact le_of_eq (trace_re_conj_one_kronecker_eq_of_conj
        (conjTranspose_compressDatabases k X Y) hCC
        (conjTranspose_diagonal_ite _) (diagonal_ite_mul_self _) ha hPQ ρ.posSemidef hρ)
    have hmono : (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * n * q) * ρ.matrix.trace.re ≤
        a * ρ.matrix.trace.re := mul_le_mul_of_nonneg_right ha0 ρ.trace_re_nonneg
    rw [← ENNReal.ofReal_mul (sub_nonneg.mpr (pow_le_one₀ hN hN1))]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith
  · have hf : (decide (c.W.card ≤ n) && decide (Function.Injective c.idx)) = false := by
      simpa using hcond
    rw [hf, SubInstrument.branch_pure_of_ne (by decide), LinearMap.zero_comp,
      LinearMap.zero_apply, Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero]
    exact zero_le

/-- **The checks after extraction** (ePrint 2025/2166, p. 61). On a substate supported on the
extraction outcome `tdm`, and for openings `pf` in the support of `VC_i.Open(Dom(m_i), td_i)`,
the checks on `W` fail with the event's other conditions
holding with weight at most `1 - (1 - 1/N)^{2 n q2}` times the trace. By condition 3 the substate
lies under the pass projector `P` of the checks on the partial tables, while the checks run
against the compressed oracles accept on `C P C`; its overlap with `P` bounds acceptance. -/
theorem outcomeMeasure_run₂_checks_le [∀ i, DecidableEq (DmOf ℓ Msg Td i)]
    (hC : Conditions VC io ME tdBot Pgood) (hk : 1 ≤ k) (n : ℕ) (c : ExtractClaim k Cm)
    {B : QReg} (tdm : TpDLen k (DmOf ℓ Msg Td) (TpIC.full hk c.idx c.cm).1) (pf : ∀ i, Pf i)
    (hpf : ∀ i, pf i ∈ support ((VC i).opening (tdm i).1.dom (tdm i).2))
    (ρ : SubState (B × ((compressedVCOracle k X Y).mixedExtractRuntime ME code).D))
    (hρ : MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ diagonal fun D : Fin k → Database X Y ↦
      if ME.extract (TpIC.full hk c.idx c.cm) D = tdm then 1 else 0) ρ.matrix = ρ.matrix) :
    (((compressedVCOracle k X Y).mixedExtractRuntime ME code).run₂ .instruments
        ((QComp.allIn c.W fun i ↦ checkAt (Z := Z) VC B i (c.idx i) (c.cm i) (tdm i).1
          (pf i)).bind fun b ↦ QuantumComp₂.pure
            (!b && decide (c.W.card ≤ n) && decide (Function.Injective c.idx)))).outcomeMeasure
        ρ {true} ≤
      ENNReal.ofReal (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * n * q2 io)) *
        ENNReal.ofReal ρ.matrix.trace.re :=
  outcomeMeasure_run₂_checks_le_of_openingQueryBound io ME code (q2 io)
    (openingQueryBound_q2 io) hC hk n c tdm pf hpf ρ hρ

/-- The openings and checks after extraction with an opening-specific cell budget. -/
theorem outcomeMeasure_run₂_openings_le_of_openingQueryBound [∀ i, DecidableEq (DmOf ℓ Msg Td i)]
    (q : ℕ) (hq : OpeningQueryBound io q)
    (hC : Conditions VC io ME tdBot Pgood) (hk : 1 ≤ k) (n : ℕ) (c : ExtractClaim k Cm)
    {B : QReg} (tdm : TpDLen k (DmOf ℓ Msg Td) (TpIC.full hk c.idx c.cm).1)
    (φ : SubState (B × ((compressedVCOracle k X Y).mixedExtractRuntime ME code).D))
    (hφ : MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ diagonal fun D : Fin k → Database X Y ↦
      if ME.extract (TpIC.full hk c.idx c.cm) D = tdm then 1 else 0) φ.matrix = φ.matrix) :
    (((compressedVCOracle k X Y).mixedExtractRuntime ME code).run₂ .instruments
        ((QComp.pi fun i : Fin k ↦ openAt VC B i (tdm i).1.dom (tdm i).2).bind fun pf ↦
          (QComp.allIn c.W fun i ↦ checkAt (Z := Z) VC B i (c.idx i) (c.cm i) (tdm i).1
            (pf i)).bind fun b ↦ QuantumComp₂.pure
              (!b && decide (c.W.card ≤ n) && decide (Function.Injective c.idx)))).outcomeMeasure
        φ {true} ≤
      ENNReal.ofReal (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * n * q)) *
        ENNReal.ofReal φ.matrix.trace.re := by
  rw [QuantumRuntime.run₂_bind]
  refine SubInstrument.outcomeMeasure_bind_le _ _ _ (measurableSet_singleton _) fun pf ↦ ?_
  obtain ⟨c₀, hc₀, hz⟩ := exists_branch_run₂_pi_eq_smul
    ((compressedVCOracle k X Y).mixedExtractRuntime ME code)
    (fun i ↦ openAt VC B i (tdm i).1.dom (tdm i).2)
    (fun i ↦ support ((VC i).opening (tdm i).1.dom (tdm i).2))
    (fun i b ↦ exists_branch_run₂_toQuantumAt_coinImpl_eq_smul _ _ b) pf
  by_cases hs : ∃ i, pf i ∉ support ((VC i).opening (tdm i).1.dom (tdm i).2)
  · rw [SubInstrument.outcomeMeasure_eq_zero_of_matrix_eq_zero _ (by
      rw [DSubInstrument.matrix_post, hc₀, hz hs, zero_smul, LinearMap.zero_apply])]
    exact zero_le
  · refine outcomeMeasure_run₂_checks_le_of_openingQueryBound io ME code q hq hC hk n c tdm pf
      (fun i ↦ Classical.byContradiction fun h ↦ hs ⟨i, h⟩) _ ?_
    rw [DSubInstrument.matrix_post, hc₀, LinearMap.smul_apply, LinearMap.id_apply]
    exact (LinearMap.map_smul _ c₀ φ.matrix).trans (congrArg (c₀ • ·) hφ)

/-- **The openings and checks after extraction.** On a substate supported on the extraction
outcome `tdm`, opening every position and running the checks on `W` reports the P3 event with
weight at most `1 - (1 - 1/N)^{2 n q2}` times the trace. The openings use only coins, so each
opening outcome scales the substate; outcomes outside the support of `Open` have weight zero. -/
theorem outcomeMeasure_run₂_openings_le [∀ i, DecidableEq (DmOf ℓ Msg Td i)]
    (hC : Conditions VC io ME tdBot Pgood) (hk : 1 ≤ k) (n : ℕ) (c : ExtractClaim k Cm)
    {B : QReg} (tdm : TpDLen k (DmOf ℓ Msg Td) (TpIC.full hk c.idx c.cm).1)
    (φ : SubState (B × ((compressedVCOracle k X Y).mixedExtractRuntime ME code).D))
    (hφ : MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ diagonal fun D : Fin k → Database X Y ↦
      if ME.extract (TpIC.full hk c.idx c.cm) D = tdm then 1 else 0) φ.matrix = φ.matrix) :
    (((compressedVCOracle k X Y).mixedExtractRuntime ME code).run₂ .instruments
        ((QComp.pi fun i : Fin k ↦ openAt VC B i (tdm i).1.dom (tdm i).2).bind fun pf ↦
          (QComp.allIn c.W fun i ↦ checkAt (Z := Z) VC B i (c.idx i) (c.cm i) (tdm i).1
            (pf i)).bind fun b ↦ QuantumComp₂.pure
              (!b && decide (c.W.card ≤ n) && decide (Function.Injective c.idx)))).outcomeMeasure
        φ {true} ≤
      ENNReal.ofReal (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * n * q2 io)) *
        ENNReal.ofReal φ.matrix.trace.re :=
  outcomeMeasure_run₂_openings_le_of_openingQueryBound io ME code (q2 io)
    (openingQueryBound_q2 io) hC hk n c tdm φ hφ

/-- The extraction challenger with an opening-specific cell budget. -/
theorem outcomeMeasure_run₂_extractChallenger_le_of_openingQueryBound
    (q : ℕ) (hq : OpeningQueryBound io q)
    (hC : Conditions VC io ME tdBot Pgood)
    (hk : 1 ≤ k) (n : ℕ) (c : ExtractClaim k Cm) {B : QReg}
    (σ : SubState (B × ((compressedVCOracle k X Y).mixedExtractRuntime ME code).D)) :
    (((compressedVCOracle k X Y).mixedExtractRuntime ME code).run₂ .instruments
        (extractChallenger VC code hk n c B)).outcomeMeasure σ {true} ≤
      ENNReal.ofReal (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * n * q)) *
        ENNReal.ofReal σ.matrix.trace.re := by
  let _ : ∀ i, DecidableEq (DmOf ℓ Msg Td i) := fun _ ↦ Classical.decEq _
  unfold extractChallenger
  erw [QuantumRuntime.run₂_bind]
  refine SubInstrument.outcomeMeasure_bind_le _ _ _ (measurableSet_singleton _) fun o ↦ ?_
  cases o with
  | none =>
    rw [QuantumRuntime.run₂_pure, DSubInstrument.outcomeMeasure_ret]
    simp
  | some tdm =>
    refine outcomeMeasure_run₂_openings_le_of_openingQueryBound io ME code q hq hC hk n c tdm _ ?_
    have hlift : ((compressedVCOracle k X Y).mixedExtractRuntime ME code).run₂ .instruments
        (QuantumComp.liftOrdinary (extractQuery code B (TpIC.full hk c.idx c.cm))) =
        ((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime.run₂ .instruments
          (extractQuery code B (TpIC.full hk c.idx c.cm)) := by
      unfold QuantumRuntime.run₂ VCOracle.mixedExtractRuntime
      erw [QuantumRuntime.run_liftOrdinary]
      rfl
    rw [DSubInstrument.matrix_post, hlift,
      run₂_extractQuery_branch (compressedVCOracle k X Y) ME code B]
    have hK := (mul_kronecker_mul (1 : Matrix B B ℂ) (1 : Matrix B B ℂ)
      (extractProj ME (TpIC.full hk c.idx c.cm) tdm)
      (extractProj ME (TpIC.full hk c.idx c.cm) tdm)).symm.trans
      (congrArg₂ (· ⊗ₖ ·) (Matrix.one_mul 1) (extractProj_mul_self ME _ tdm))
    exact (LinearMap.congr_fun (MatrixMap.conj_mul _ _) σ.matrix).symm.trans
      (congrArg (fun M ↦ MatrixMap.conj M σ.matrix) hK)

/-- **The P3 challenger against the compressed oracles, leaf by leaf** (ePrint 2025/2166,
pp. 59–61). From every joint substate of the adversary's register and the databases, the P3
challenger reports its event with weight at most `1 - (1 - 1/N)^{2 n q2}` times the trace.
Extraction is the measurement of `MultiExtract(tic, ·)` (game G0, p. 59), so each extraction
outcome leaves a substate supported on it. -/
theorem outcomeMeasure_run₂_extractChallenger_le (hC : Conditions VC io ME tdBot Pgood)
    (hk : 1 ≤ k) (n : ℕ) (c : ExtractClaim k Cm) {B : QReg}
    (σ : SubState (B × ((compressedVCOracle k X Y).mixedExtractRuntime ME code).D)) :
    (((compressedVCOracle k X Y).mixedExtractRuntime ME code).run₂ .instruments
        (extractChallenger VC code hk n c B)).outcomeMeasure σ {true} ≤
      ENNReal.ofReal (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * n * q2 io)) *
        ENNReal.ofReal σ.matrix.trace.re :=
  outcomeMeasure_run₂_extractChallenger_le_of_openingQueryBound io ME code (q2 io)
    (openingQueryBound_q2 io) hC hk n c σ

/-! ## Lemma 9.3 -/

/-- P3 with error `1 - (1 - 1/N)^(2 n q)` when opening outputs use at most `q` cells. -/
theorem extractionCorrect_compressedVCOracle_of_openingQueryBound
    (q : ℕ) (hq : OpeningQueryBound io q)
    (hC : Conditions VC io ME tdBot Pgood) :
    ExtractionCorrect.{v, w} VC (compressedVCOracle k X Y) ME code
      fun _ _ _ n ↦ ENNReal.ofReal (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * n * q)) := by
  intro hk t n wVC wME A W x claim ρ _ _ _ _
  exact outcomeLawWith_experiment_true_le _ (QuantumComp.liftOrdinary x) _ ρ fun u y σ ↦
    outcomeMeasure_run₂_extractChallenger_le_of_openingQueryBound
      io ME code q hq hC hk n (claim u y) σ

/-- **Lemma 9.3 of ePrint 2025/2166, exact form** (pp. 59–61): `EO^(Ext)` for the `k`
compressed oracles is multi-extraction correct (P3, `Quantum.ExtractionCorrect`) under the
algebraic conditions of Theorem 8.4 (`Quantum.Conditions`), with error
`1 - (1 - 1/N)^{2 n q2}`, independent of the query bound and of the oracle and extraction masses.

Proof: extraction is the measurement of `MultiExtract(tic, ·)`
(game G0, p. 59), and the openings use only coins, so it suffices to bound the event from a
substate supported on one extraction outcome `tdm` with openings `pf` in the support of `Open`.
By condition 3 (p. 54) the substate lies under the pass projector `P` of the checks on the
partial tables, so the ideal failure probability is zero. Against the compressed oracles the
checks accept exactly on `C P C`, and `P (C P C) P = a P` with `a ≥ (1 - 1/N)^{2 n q2}`
because there are at most `n q2` prescribed cells, so the checks fail with weight at most
`1 - a` times the trace. -/
theorem extractionCorrect_compressedVCOracle (hC : Conditions VC io ME tdBot Pgood) :
    ExtractionCorrect.{v, w} VC (compressedVCOracle k X Y) ME code
      fun _ _ _ n ↦ extractError io n :=
  extractionCorrect_compressedVCOracle_of_openingQueryBound io ME code (q2 io)
    (openingQueryBound_q2 io) hC

/-- **Lemma 9.3 of ePrint 2025/2166, leading order**: P3 with error `2 n q2 / N`, a corollary of
`Quantum.extractionCorrect_compressedVCOracle`. -/
theorem extractionCorrect_compressedVCOracle_two_mul (hC : Conditions VC io ME tdBot Pgood) :
    ExtractionCorrect.{v, w} VC (compressedVCOracle k X Y) ME code
      fun _ _ _ n ↦ (2 * n * q2 io : ℝ≥0∞) / Fintype.card Y :=
  (extractionCorrect_compressedVCOracle io ME code hC).mono fun _ _ _ n ↦
    extractError_le_two_mul io n

/-- **Lemma 9.3 of ePrint 2025/2166 with the paper's error `8 n q2 / N`** (p. 59): a corollary of
`Quantum.extractionCorrect_compressedVCOracle`. -/
theorem extractionCorrect_compressedVCOracle_eight_mul (hC : Conditions VC io ME tdBot Pgood) :
    ExtractionCorrect.{v, w} VC (compressedVCOracle k X Y) ME code
      fun _ _ _ n ↦ (8 * n * q2 io : ℝ≥0∞) / Fintype.card Y :=
  (extractionCorrect_compressedVCOracle_two_mul io ME code hC).mono fun _ _ _ n ↦ by
    change (2 * n * q2 io : ℝ≥0∞) / Fintype.card Y ≤ 8 * n * q2 io / Fintype.card Y
    gcongr
    norm_num

end challenger

end Quantum
