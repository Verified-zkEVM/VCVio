/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.HadamardChecking

/-!
# Classical checker execution against the extended witness

Each successful classical reading is a single Kraus branch. Sequencing readings multiplies
those operators, so the actual checker realizes the list amplitudes of the repair note,
including every repeated query. These identities connect the matrix estimates to the existing
challenger programs without changing their semantics.
-/

public section

open Matrix OracleSpec OracleComp
open scoped Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe u₁ v₁

namespace Quantum

section runs

variable {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]

/-- Composing accepting Kraus maps multiplies their decompressed diagonal amplitudes. -/
theorem conj_diagonal_amplitudes_comp {C : Matrix S S ℂ} (hCC : C * C = 1)
    (f g : S → ℂ) :
    MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (C * diagonal g * C)) ∘ₗ
        MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (C * diagonal f * C)) =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
        (C * diagonal (fun d ↦ f d * g d) * C)) := by
  rw [← MatrixMap.conj_mul, ← mul_kronecker_mul, Matrix.one_mul,
    conj_diagonal_mul_conj_diagonal hCC]
  simp only [mul_comm]

end runs

section programs

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {B : QReg}
  {X Y : Type} [Finite Y] [DecidableEq Y]

/-- The actual successful branch of `CheckIO` is the product of its accepting amplitudes.
The fold retains all occurrences, regardless of whether the prescriptions are consistent. -/
theorem branch_run₂_foldlM_acceptWeight
    (call : QueryImpl (X →ₒ Y) (QComp spec B B)) {C : Matrix R.D R.D ℂ}
    (hCC : C * C = 1) (g : Y → ℂ) (read : R.D → X → Option Y)
    (hcall : ∀ t y, (R.run₂ .instruments (call t)).branch y =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
        (C * diagonal (fun d ↦ acceptValue g y (read d t)) * C)))
    (io : List (X × Y)) (acc : Bool) :
    (R.run₂ .instruments ((io.foldlM checkIOStep acc).toQuantumAt call)).branch true =
      if acc then MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ acceptingList C g io read) else 0 := by
  let : Fintype Y := Fintype.ofFinite Y
  induction io generalizing acc with
  | nil =>
    rw [List.foldlM_nil, toQuantumAt_pure, QuantumRuntime.run₂_pure]
    cases acc
    · exact SubInstrument.branch_pure_of_ne (by decide)
    · rw [SubInstrument.branch_pure_self, ite_eq_left rfl]
      simp [acceptingList, hCC, MatrixMap.conj_one]
  | cons p io ih =>
    have hprog : ((p :: io).foldlM checkIOStep acc).toQuantumAt call =
        (call p.1).bind fun y ↦ (io.foldlM checkIOStep (acc && decide (y = p.2))).toQuantumAt
          call := by
      rw [List.foldlM_cons, checkIOStep, bind_assoc]
      simp only [pure_bind]
      exact toQuantumAt_query_bind call p.1 _
    rw [hprog, QuantumRuntime.run₂_bind, SubInstrument.branch_bind_apply_univ,
      Finset.sum_eq_single p.2]
    · rw [ih, hcall]
      simp only [decide_true, Bool.and_true]
      cases acc
      · simp
      · simp only [↓reduceIte, acceptingList]
        rw [conj_diagonal_amplitudes_comp hCC]
        rfl
    · intro y _ hy
      rw [ih]
      simp [hy]
    · simp

end programs

section allIn

variable {k : ℕ} {S : Type*}

/-- The joint accepting amplitude of the checks selected by `W`, in the checker's order. -/
@[expose]
def allCheckWeight (W : Finset (Fin k)) (f : Fin k → S → ℂ) (d : S) : ℂ :=
  ((List.finRange k).map fun i ↦ if i ∈ W then f i d else 1).prod

/-- If every selected check has accepting amplitude one, so does their conjunction. -/
theorem allCheckWeight_eq_one (W : Finset (Fin k)) (f : Fin k → S → ℂ) (d : S)
    (hf : ∀ i ∈ W, f i d = 1) : allCheckWeight W f d = 1 := by
  apply List.prod_eq_one
  intro z hz
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
  split_ifs with hi
  · exact hf i hi
  · rfl

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {B : QReg}

/-- The successful branch of a conjunction multiplies the individual diagonal amplitudes. -/
theorem branch_run₂_allIn_amplitudes (W : Finset (Fin k))
    (f : Fin k → QComp spec B B Bool) {C : Matrix R.D R.D ℂ} (hCC : C * C = 1)
    (g : Fin k → R.D → ℂ)
    (hf : ∀ i ∈ W, (R.run₂ .instruments (f i)).branch true =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (C * diagonal (g i) * C))) :
    (R.run₂ .instruments (QComp.allIn W f)).branch true =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (C * diagonal (allCheckWeight W g) * C)) := by
  have key : ∀ (l : List (Fin k)) (acc : Bool),
      (R.run₂ .instruments (l.foldlM (fun acc i ↦ if i ∈ W then (acc && ·) <$> f i
        else pure acc) acc)).branch true =
      if acc then MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
        (C * diagonal (fun d ↦ (l.map fun i ↦ if i ∈ W then g i d else 1).prod) * C))
      else 0 := by
    intro l
    induction l with
    | nil =>
      intro acc
      rw [List.foldlM_nil, QuantumComp₂.pure_eq, QuantumRuntime.run₂_pure]
      cases acc
      · exact SubInstrument.branch_pure_of_ne (by decide)
      · rw [SubInstrument.branch_pure_self, ite_eq_left rfl]
        simp [hCC, MatrixMap.conj_one]
    | cons i l ih =>
      intro acc
      rw [List.foldlM_cons]
      by_cases hi : i ∈ W
      · simp only [hi, ↓reduceIte, bind_map_left]
        rw [QuantumComp₂.bind_eq, QuantumRuntime.run₂_bind, SubInstrument.branch_bind_apply_univ,
          Fintype.sum_bool, ih, ih]
        cases acc
        · simp
        · simp only [Bool.true_and, ↓reduceIte, Bool.false_eq_true, LinearMap.zero_comp,
            add_zero]
          rw [hf i hi, conj_diagonal_amplitudes_comp hCC]
          simp only [List.map_cons, List.prod_cons, hi, ↓reduceIte]
      · simp only [hi, ↓reduceIte, pure_bind]
        rw [ih]
        simp only [List.map_cons, List.prod_cons, hi, ↓reduceIte, one_mul]
  rw [QComp.allIn, key, ite_eq_left rfl]
  rfl

end allIn

section queries

variable {X Y T : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq T] [AddCommGroup Y]

/-- The accepting matrix element of the decompressed table extension. Changing the query
input has amplitude zero. -/
theorem submatrix_extendedTableOracle (W : Matrix Y Y ℂ) (read : T → X → Option Y)
    (t t' : X) (y : Y) :
    (extendedTableOracle W read).submatrix (fun d ↦ (((t', y) : X × Y), d))
        (fun d ↦ (((t, 0) : X × Y), d)) =
      diagonal fun d ↦ if t' = t then acceptValue (fun z ↦ W z 0) y (read d t) else 0 := by
  ext d e
  by_cases ht : t' = t
  · subst t'
    by_cases hd : d = e
    · subst e
      cases hh : read d t <;>
        simp [extendedTableOracle_apply, emptyExtensionBlock, acceptValue, hh, eq_comm]
    · simp [extendedTableOracle_apply, hd]
  · simp [extendedTableOracle_apply, ht, diagonal_apply]

end queries

section runtimeQueries

variable {k : ℕ} {X Y Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  (W : Matrix Y Y ℂ) (hW : W ∈ unitaryGroup Y ℂ)
  {Dm : Fin k → Type} (ME : MultiExtractor k Cm Dm (Fin k → Database X Y))
  (code : TpDCode k Dm Z)

/-- A classical query of an extended VC port has the Kraus operator with its actual accepting
amplitude on the empty sector. The coherent extraction port is retained in the runtime. -/
theorem branch_run₂_oracleCall_extendedVCOracle (B : QReg) (j : Fin k) (t : X) (y : Y) :
    (((extendedVCOracle k X Y W hW).withExtract ME code).coherent.toRuntime.run₂ .instruments
        (oracleCall (Cm := Cm) (Z := Z) B j t)).branch y =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (compressDatabases k X Y *
        diagonal (fun D : Fin k → Database X Y ↦ acceptValue (fun z ↦ W z 0) y (D j t)) *
        compressDatabases k X Y)) := by
  have hblock : ∀ (t' : X) (y' : Y),
      ((extendedVCOracle k X Y W hW).withExtract ME code).coherent.block ()
          ⟨.inl j, ((t', y') : X × Y)⟩ ⟨.inl j, ((t, 0) : X × Y)⟩ =
        compressDatabases k X Y *
          diagonal (fun D : Fin k → Database X Y ↦
            if t' = t then acceptValue (fun z ↦ W z 0) y' (D j t) else 0) *
          compressDatabases k X Y := by
    intro t' y'
    ext d d'
    have h := congrFun (congrFun (submatrix_one_kronecker_mul_mul_one_kronecker
      (compressDatabases k X Y) (extendedTableOracle W (fun D : Fin k → Database X Y ↦ D j))
      ((t', y') : X × Y) ((t, 0) : X × Y)) d) d'
    rw [submatrix_extendedTableOracle] at h
    refine (EmulatedOracle.coherent_U_apply_self _ (Sum.inl j) _ _ _ _).trans (Eq.trans ?_ h)
    rfl
  have hread : ∀ (i : Fin k) (m : X × Y),
      readY (Cm := Cm) (Z := Z) (⟨.inl i, m⟩ : Σ i, extIn k X Y Cm Z i) = m.2 := fun _ _ ↦ rfl
  rw [oracleCall, EmulatedOracle.branch_run₂_callBasis,
    Finset.sum_eq_single (⟨.inl j, ((t, y) : X × Y)⟩ : Σ i, extIn k X Y Cm Z i)]
  · simp only [hread, ↓reduceIte, hblock]
    rfl
  · rintro ⟨i | u, m⟩ _ hne
    · by_cases hij : i = j
      · subst hij
        obtain ⟨t', y'⟩ := m
        by_cases hy : y' = y
        · subst hy
          have ht : t' ≠ t := fun ht ↦ hne (by rw [ht])
          have hb : ((extendedVCOracle k X Y W hW).withExtract ME code).coherent.block ()
              ⟨.inl i, ((t', y') : X × Y)⟩ ⟨.inl i, ((t, 0) : X × Y)⟩ = 0 := by
            rw [hblock]
            ext d d'
            simp only [ht, ↓reduceIte, diagonal_zero, Matrix.mul_zero]
            exact congrFun (congrFun (Matrix.zero_mul (compressDatabases k X Y)) d) d'
          rw [hb, kronecker_zero, MatrixMap.conj_zero, ite_self]
        · exact ite_eq_right_of_eq_false _ _ (eq_false hy)
      · have hb : ((extendedVCOracle k X Y W hW).withExtract ME code).coherent.block ()
            ⟨.inl i, m⟩ ⟨.inl j, ((t, 0) : X × Y)⟩ = 0 := by
          ext d d'
          rw [EmulatedOracle.block_apply]
          exact EmulatedOracle.coherent_U_apply_of_ne _ (fun h ↦ hij (Sum.inl_injective h)) _ _ _ _
        rw [hb, kronecker_zero, MatrixMap.conj_zero, ite_self]
    · have hb : ((extendedVCOracle k X Y W hW).withExtract ME code).coherent.block ()
          ⟨.inr u, m⟩ ⟨.inl j, ((t, 0) : X × Y)⟩ = 0 := by
        ext d d'
        rw [EmulatedOracle.block_apply]
        exact EmulatedOracle.coherent_U_apply_of_ne _ Sum.inr_ne_inl _ _ _ _
      rw [hb, kronecker_zero, MatrixMap.conj_zero, ite_self]
  · simp


end runtimeQueries

section checkWeight

variable {k : ℕ} {X Y Msg Cm : Type} [DecidableEq Y]
  {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)}

/-- The accepting amplitude of one VC check on a decompressed table. Syntactic failure has
amplitude zero; a parsed list retains every oracle query. -/
@[expose]
noncomputable def checkAcceptWeight (io : ∀ i, (VC i).CheckIOForm) (g : Y → ℂ)
    (i : Fin k) (cm : Cm) (ans : PartialVec (ℓ i) Msg) (pf : Pf i) (d : Database X Y) : ℂ :=
  ((io i).outputIO cm ans pf).elim 0 (fun l ↦ acceptWeight g l d)

/-- A check satisfied on its partial database has accepting amplitude one for every choice
of empty-sector response amplitudes. -/
theorem checkAcceptWeight_eq_one (io : ∀ i, (VC i).CheckIOForm) (g : Y → ℂ)
    (i : Fin k) (cm : Cm) (ans : PartialVec (ℓ i) Msg) (pf : Pf i) (d : Database X Y)
    (h : (io i).checkOn d cm ans pf = true) : checkAcceptWeight io g i cm ans pf d = 1 := by
  cases hl : (io i).outputIO cm ans pf with
  | none => simp [VectorCommitment.CheckIOForm.checkOn, hl] at h
  | some l =>
    simp only [VectorCommitment.CheckIOForm.checkOn, hl, Option.elim] at h
    rw [checkAcceptWeight, hl, Option.elim]
    exact acceptWeight_eq_one g l d ((checkIOOn_eq_true_iff d l).mp h)

end checkWeight

section checks

variable {k : ℕ} {X Y Msg Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)} (io : ∀ i, (VC i).CheckIOForm)
  (W : Matrix Y Y ℂ) (hW : W ∈ unitaryGroup Y ℂ)
  {Dm : Fin k → Type} (ME : MultiExtractor k Cm Dm (Fin k → Database X Y))
  (code : TpDCode k Dm Z)

/-- The actual successful Kraus branch of a VC check against the extended witness. -/
theorem branch_run₂_checkAt_extendedVCOracle (B : QReg) (i j : Fin k) (cm : Cm)
    (ans : PartialVec (ℓ i) Msg) (pf : Pf i) :
    (((extendedVCOracle k X Y W hW).withExtract ME code).coherent.toRuntime.run₂ .instruments
        (checkAt (Z := Z) VC B i j cm ans pf)).branch true =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (compressDatabases k X Y *
        diagonal (fun D : Fin k → Database X Y ↦
          checkAcceptWeight io (fun z ↦ W z 0) i cm ans pf (D j)) * compressDatabases k X Y)) := by
  have hCC := compressDatabases_mul_self (k := k) (X := X) (Y := Y)
  rw [checkAt_eq_toQuantumAt io]
  cases h : (io i).outputIO cm ans pf with
  | none =>
    simp only [Option.elim, toQuantumAt_pure, QuantumRuntime.run₂_pure,
      checkAcceptWeight, h]
    rw [SubInstrument.branch_pure_of_ne (by decide)]
    simp only [diagonal_zero, Matrix.mul_zero]
    erw [Matrix.zero_mul, kronecker_zero, MatrixMap.conj_zero]
    rfl
  | some l =>
    simp only [Option.elim, checkIO]
    rw [branch_run₂_foldlM_acceptWeight
      ((extendedVCOracle k X Y W hW).withExtract ME code).coherent.toRuntime
      (fun t ↦ oracleCall (Cm := Cm) (Z := Z) B j t) hCC (fun z ↦ W z 0)
      (fun D t ↦ D j t)
      (fun t y ↦ branch_run₂_oracleCall_extendedVCOracle W hW ME code B j t y),
      ite_eq_left rfl]
    simp only [acceptingList, checkAcceptWeight, h, Option.elim]
    rfl

end checks

end Quantum
