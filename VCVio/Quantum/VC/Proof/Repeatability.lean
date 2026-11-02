/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.ClassicalRepeatability
public import VCVio.Quantum.VC.Proof.Extraction

/-!
# Exact replay for the compressed oracle

The ordinary answer projectors and the checked read projectors commute on the entire
private space. Their transcript identities apply to arbitrary joint substates, including
states produced by extraction before the first read. Extraction between repetitions is
excluded, as required for Chiesa, Di, Hu and Zheng, ePrint 2025/2166, Lemma 11.12.
-/

public section

open Matrix OracleComp OracleSpec
open scoped Kronecker

universe uL vL w

namespace Quantum
namespace ProjectiveClassicalAnswers

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg}
  {E : EmulatedOracle P In} {X Y : Type} [Fintype Y] [DecidableEq Y]
  (H : ProjectiveClassicalAnswers E X Y)

/-- The accepting branch of the complete checker fold. Calls continue after a failed comparison;
all rejected answer histories have zero contribution to the accepting branch. -/
theorem actual_fold_accept (B : QReg) (log : QueryLog (X →ₒ Y)) (acc : Bool) :
    ((E.withClassicalReads H).run₂ .instruments
      ((log.foldlM QueryLog.recheckStep acc).toQuantumAt (H.classicalCall B))).branch true =
        if acc then H.transcriptBranch B log else 0 := by
  induction log generalizing acc with
  | nil =>
    rw [List.foldlM_nil, toQuantumAt_pure, QuantumRuntime.run₂_pure]
    cases acc
    · exact SubInstrument.branch_pure_of_ne (by decide)
    · rw [SubInstrument.branch_pure_self]
      simp only [ite_true, transcriptBranch_nil]
      rfl
  | cons p log ih =>
    have hp : ((p :: log).foldlM QueryLog.recheckStep acc).toQuantumAt (H.classicalCall B) =
        (H.classicalCall B p.1).bind fun y ↦
          (log.foldlM QueryLog.recheckStep (acc && decide (y = p.2))).toQuantumAt
            (H.classicalCall B) := by
      rw [List.foldlM_cons, QueryLog.recheckStep, bind_assoc]
      simp only [pure_bind]
      exact toQuantumAt_query_bind (H.classicalCall B) p.1 _
    rw [hp, QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply_univ,
      Finset.sum_eq_single p.2]
    · rw [ih]
      simp only [decide_true, Bool.and_true]
      cases acc
      · simp
      · simp only [↓reduceIte]
        rw [H.branch_classicalCall]
        exact (H.transcriptBranch_cons B p log).symm
    · intro y _ hy
      rw [ih]
      simp only [hy, decide_false, Bool.and_false, Bool.false_eq_true, ite_false]
      rfl
    · simp

/-- The actual classical `recheck` of a query log accepts on the product of its answer
projectors, including repeated and contradictory prescriptions, on any entangled
reference/private input matrix. -/
theorem actual_accept_eq_projectorProduct (B : QReg) (log : QueryLog (X →ₒ Y)) :
    ((E.withClassicalReads H).run₂ .instruments
      ((QueryLog.recheck log).toQuantumAt (H.classicalCall B))).branch true =
        MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ H.projector log) := by
  simpa only [QueryLog.recheck, ↓reduceIte, transcriptBranch] using
    H.actual_fold_accept B log true

/-- Transcript projectors commute through general quantum programs that coherently choose
ordinary ports. This lifts portwise commutation without assuming a classical port schedule. -/
theorem commute_coherent_run {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w}
    {B : QReg} (prog : QuantumComp L (EmulatedOracle.cohSpec In) W B)
    (leaf : Σ u, W u) (tr : QueryLog (X →ₒ Y)) :
    (E.coherent.toRuntime.run I prog).branch leaf ∘ₗ H.transcriptBranch B tr =
      H.transcriptBranch leaf.1 tr ∘ₗ (E.coherent.toRuntime.run I prog).branch leaf := by
  have hs := QuantumRuntime.simulation (R₁ := E.coherent.toRuntime)
    (R₂ := E.coherent.toRuntime) (V := MatrixMap.conj (H.projector tr)) I
    (fun p r ↦ ?_) prog leaf
  · simpa only [MatrixMap.amplifyLeft_conj, transcriptBranch] using hs
  · cases p
    rw [E.coherent.toRuntime_step_branch, MatrixMap.amplifyLeft_conj]
    simp only [← MatrixMap.conj_mul]
    rw [EmulatedOracle.coherent_U_mul_one_kronecker E E (H.projector tr)
      (fun p ↦ H.ordinary_commute_projector p tr)]

/-- Exact replay after any quantum program using coherent ordinary ports. The full joint
subnormalized branch is preserved on each possibly register-dependent final leaf. -/
theorem replay_after_coherent_run {L : LocalSig.{uL, vL}} (I : L.Interp)
    {W : QReg → Type w} {B : QReg} (prog : QuantumComp L (EmulatedOracle.cohSpec In) W B)
    (leaf : Σ u, W u) (tr : QueryLog (X →ₒ Y)) :
    H.transcriptBranch leaf.1 tr ∘ₗ (E.coherent.toRuntime.run I prog).branch leaf ∘ₗ
        H.transcriptBranch B tr =
      (E.coherent.toRuntime.run I prog).branch leaf ∘ₗ H.transcriptBranch B tr := by
  rw [← LinearMap.comp_assoc, ← H.commute_coherent_run I prog leaf tr,
    LinearMap.comp_assoc, H.replay_transcript]

/-- Each leaf of a mixed program commutes with the retained transcript. The program may use
ordinary coherent queries, checked reads and external operations, but has no extraction port. -/
theorem commute_mixed_run {Addr Ans : Type} [Fintype Ans] [DecidableEq Ans]
    (K : ProjectiveClassicalAnswers E Addr Ans)
    (hcomm : ∀ x y c a, H.A x y * K.A c a = K.A c a * H.A x y)
    {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w}
    {B : QReg} (prog : QuantumComp L
      (withReadSpec (EmulatedOracle.cohSpec In) Addr Ans) W B)
    (leaf : Σ u, W u) (tr : QueryLog (X →ₒ Y)) :
    ((E.withClassicalReads K).run I prog).branch leaf ∘ₗ H.transcriptBranch B tr =
      H.transcriptBranch leaf.1 tr ∘ₗ ((E.withClassicalReads K).run I prog).branch leaf := by
  have hs := QuantumRuntime.simulation (R₁ := E.withClassicalReads K)
    (R₂ := E.withClassicalReads K) (V := MatrixMap.conj (H.projector tr)) I
    (fun p r ↦ ?_) prog leaf
  · dsimp +instances only [EmulatedOracle.withClassicalReads, QuantumRuntime.extend,
      EmulatedOracle.toRuntime, EmulatedOracle.coherent] at hs ⊢
    simpa only [MatrixMap.amplifyLeft_conj, transcriptBranch] using hs
  · cases p with
    | inl p =>
      change Unit at r
      change (E.coherent.toRuntime.step p).branch r ∘ₗ
          (MatrixMap.conj (H.projector tr)).amplifyLeft (EmulatedOracle.cohIn In) =
        (MatrixMap.conj (H.projector tr)).amplifyLeft (EmulatedOracle.cohIn In) ∘ₗ
          (E.coherent.toRuntime.step p).branch r
      cases p
      rw [E.coherent.toRuntime_step_branch, MatrixMap.amplifyLeft_conj]
      simp only [← MatrixMap.conj_mul]
      rw [EmulatedOracle.coherent_U_mul_one_kronecker E E (H.projector tr)
        (fun p ↦ H.ordinary_commute_projector p tr)]
    | inr x =>
      change Ans at r
      change (K.step x).branch r ∘ₗ (MatrixMap.conj (H.projector tr)).amplifyLeft Unit =
        (MatrixMap.conj (H.projector tr)).amplifyLeft Unit ∘ₗ (K.step x).branch r
      rw [K.step_branch, MatrixMap.amplifyLeft_conj]
      have hc : K.A x r * H.projector tr = H.projector tr * K.A x r := by
        simpa only [projector_cons, projector_nil, Matrix.mul_one] using
          (H.projector_commute K hcomm tr [⟨x, r⟩]).symm
      simp only [← MatrixMap.conj_mul, ← mul_kronecker_mul, Matrix.one_mul, hc]

/-- Exact replay on arbitrary initial joint substates after a mixed program, separately on
its complete leaves. Any extraction used to prepare the initial state precedes the first read. -/
theorem replay_after_mixed_run {Addr Ans : Type} [Fintype Ans] [DecidableEq Ans]
    (K : ProjectiveClassicalAnswers E Addr Ans)
    (hcomm : ∀ x y c a, H.A x y * K.A c a = K.A c a * H.A x y)
    {L : LocalSig.{uL, vL}} (I : L.Interp)
    {W : QReg → Type w} {B : QReg} (prog : QuantumComp L
      (withReadSpec (EmulatedOracle.cohSpec In) Addr Ans) W B)
    (leaf : Σ u, W u) (tr : QueryLog (X →ₒ Y)) :
    H.transcriptBranch leaf.1 tr ∘ₗ ((E.withClassicalReads K).run I prog).branch leaf ∘ₗ
        H.transcriptBranch B tr =
      ((E.withClassicalReads K).run I prog).branch leaf ∘ₗ H.transcriptBranch B tr := by
  erw [← LinearMap.comp_assoc, ← H.commute_mixed_run K hcomm I prog leaf tr,
    LinearMap.comp_assoc, H.replay_transcript]
  rfl

/-- Retained ordinary and checked transcripts can be replayed together after a mixed
program, with the same fixed inputs and coins and an arbitrary initial joint substate. -/
theorem replay_mixed_transcripts_after_run {Addr Ans : Type} [Fintype Ans] [DecidableEq Ans]
    (K : ProjectiveClassicalAnswers E Addr Ans)
    (hcomm : ∀ x y c a, H.A x y * K.A c a = K.A c a * H.A x y)
    {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w} {B : QReg}
    (prog : QuantumComp L (withReadSpec (EmulatedOracle.cohSpec In) Addr Ans) W B)
    (leaf : Σ u, W u) (ts : QueryLog (X →ₒ Y)) (us : QueryLog (Addr →ₒ Ans)) :
    (H.transcriptBranch leaf.1 ts ∘ₗ K.transcriptBranch leaf.1 us) ∘ₗ
        ((E.withClassicalReads K).run I prog).branch leaf ∘ₗ
        (H.transcriptBranch B ts ∘ₗ K.transcriptBranch B us) =
      ((E.withClassicalReads K).run I prog).branch leaf ∘ₗ
        (H.transcriptBranch B ts ∘ₗ K.transcriptBranch B us) := by
  have hc : ((E.withClassicalReads K).run I prog).branch leaf ∘ₗ
        (H.transcriptBranch B ts ∘ₗ K.transcriptBranch B us) =
      (H.transcriptBranch leaf.1 ts ∘ₗ K.transcriptBranch leaf.1 us) ∘ₗ
        ((E.withClassicalReads K).run I prog).branch leaf := by
    erw [← LinearMap.comp_assoc, H.commute_mixed_run K hcomm I prog leaf ts,
      LinearMap.comp_assoc, K.commute_mixed_run K K.commute_cells I prog leaf us,
      ← LinearMap.comp_assoc]
  erw [← LinearMap.comp_assoc, ← hc, LinearMap.comp_assoc,
    H.replay_mixed_transcripts K hcomm]
  rfl

end ProjectiveClassicalAnswers

namespace CompressedReplay

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- Prescribed present answers form the checked transcript projector. -/
theorem filledCheck_eq_projector (log : QueryLog ((Fin k × X) →ₒ Y)) :
    filledCheck log = (compressedVCOracle k X Y).classicalRead.projector
      (log.map fun p ↦ ⟨p.1, some p.2⟩) := by
  induction log with
  | nil =>
    simp only [filledCheck_nil, List.map_nil, ProjectiveClassicalAnswers.projector_nil]
    rfl
  | cons p log ih =>
    rw [filledCheck_cons, List.map_cons, ProjectiveClassicalAnswers.projector_cons, ih]
    rfl

/-- The implemented short-circuiting checked interpreter accepts on exactly its transcript
projector, including zero prescriptions. A missing read returns rejection. -/
theorem checked_accept_eq_projectorProduct
    {Cm Z : Type} [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
    {Dm : Fin k → Type} (ME : MultiExtractor k Cm Dm (compressedVCOracle k X Y).S)
    (code : TpDCode k Dm Z) (B : QReg) (j : Fin k) (log : QueryLog (X →ₒ Y)) :
    (((compressedVCOracle k X Y).mixedExtractRuntime ME code).run₂ .instruments
      (runClassicalChecked B j (liftComp (QueryLog.recheck log) (unifSpec + (X →ₒ Y))))).branch
        (some true) =
      (compressedVCOracle k X Y).classicalRead.transcriptBranch B
        (log.map fun p ↦ ⟨(j, p.1), some p.2⟩) := by
  simp only [QueryLog.recheck, branch_run₂_checked_fold, ite_true, filledCheck_eq_projector,
    List.map_map, Function.comp_def, ProjectiveClassicalAnswers.transcriptBranch]
  rfl

/-- The ordinary answer projector, expressed by lookup in the decompressed basis. -/
noncomputable def answer (x : Fin k × X) (y : Y) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  compressDatabases k X Y *
    diagonal (fun D ↦ if (D x.1).lookup x.2 = y then 1 else 0) * compressDatabases k X Y

/-- The ordinary zero answer includes the missing sector on every private state. -/
theorem answer_eq_checked_projectors (x : Fin k × X) (y : Y) :
    answer x y = compressedReadProjector k X Y x (some y) +
      if y = 0 then compressedReadProjector k X Y x none else 0 := by
  have hd : (diagonal fun D : Fin k → Database X Y ↦
        if (D x.1).lookup x.2 = y then (1 : ℂ) else 0) =
      (diagonal fun D ↦ if D x.1 x.2 = some y then 1 else 0) +
        if y = 0 then (diagonal fun D ↦ if D x.1 x.2 = none then 1 else 0) else 0 := by
    ext D D'
    by_cases h : D = D'
    · subst D'
      simp only [diagonal_apply_eq, Matrix.add_apply]
      cases he : D x.1 x.2 <;> by_cases hy : y = 0 <;>
        simp [Database.lookup_apply, he, hy, eq_comm]
    · by_cases hy : y = 0 <;> simp [hy, h]
  unfold answer compressedReadProjector
  rw [hd]
  split_ifs
  · rw [Matrix.mul_add, Matrix.add_mul]
  · simp only [add_zero]

/-- Every ordinary answer projector is Hermitian. -/
theorem answer_hermitian (x : Fin k × X) (y : Y) : (answer x y)ᴴ = answer x y := by
  simp only [answer, conjTranspose_mul, conjTranspose_compressDatabases,
    conjTranspose_diagonal_ite, Matrix.mul_assoc]

/-- Orthogonality of distinct ordinary answers, with idempotency for equal answers. -/
theorem answer_orthogonal (x : Fin k × X) (z y : Y) :
    answer x z * answer x y = if z = y then answer x y else 0 := by
  rw [answer, answer, compressed_conjugate_mul _ (compressDatabases_mul_self k X Y),
    diagonal_ite_mul_diagonal_ite]
  by_cases h : z = y
  · subst z
    simp only [and_self, ↓reduceIte]
  · have hd : (diagonal fun D : Fin k → Database X Y ↦
        if (D x.1).lookup x.2 = z ∧ (D x.1).lookup x.2 = y then (1 : ℂ) else 0) = 0 := by
      ext D D'
      simp only [diagonal_apply, Matrix.zero_apply]
      split_ifs with hD hc
      · exact False.elim (h (hc.1.symm.trans hc.2))
      all_goals rfl
    rw [hd]
    simp [h]

/-- Ordinary classical answers resolve the identity, with no reachable-state restriction. -/
theorem answer_complete (x : Fin k × X) : ∑ y : Y, answer x y = 1 := by
  have hd : (∑ y : Y, diagonal fun D : Fin k → Database X Y ↦
      if (D x.1).lookup x.2 = y then (1 : ℂ) else 0) = 1 := by
    ext D D'
    by_cases h : D = D'
    · subst D'
      simp [Matrix.sum_apply, eq_comm]
    · simp [Matrix.sum_apply, h]
  simp only [answer, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [hd, Matrix.mul_one, compressDatabases_mul_self]

/-- All ordinary answer projectors commute, including at different oracle indices. -/
theorem answer_commute (x x' : Fin k × X) (y y' : Y) :
    answer x y * answer x' y' = answer x' y' * answer x y := by
  simp only [answer, compressed_conjugate_mul _ (compressDatabases_mul_self k X Y),
    diagonal_ite_mul_diagonal_ite]
  simp only [and_comm]

/-- Ordinary answer projectors commute with checked answers at every pair of cells. -/
theorem answer_commute_checked (x x' : Fin k × X) (y : Y) (a : Option Y) :
    answer x y * compressedReadProjector k X Y x' a =
      compressedReadProjector k X Y x' a * answer x y := by
  simp only [answer, compressedReadProjector,
    compressed_conjugate_mul _ (compressDatabases_mul_self k X Y), diagonal_ite_mul_diagonal_ite]
  simp only [and_comm]

/-- The classical basis-call branch of the ordinary oracle on an arbitrary reference register. -/
theorem branch_eq (B : QReg) (x : Fin k × X) (y : Y) :
    ((compressedVCOracle k X Y).toRuntime.run₂ .instruments
      (QComp.callBasis x.1 B (x.2, 0) (fun o _ ↦ o.2))).branch y =
        MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ answer x y) := by
  have hb (t : X) (z : Y) :
      (compressedVCOracle k X Y).block x.1 (t, z) (x.2, 0) =
        compressDatabases k X Y *
          diagonal (fun D : Fin k → Database X Y ↦
            if t = x.2 ∧ (D x.1).lookup x.2 = z then 1 else 0) *
          compressDatabases k X Y := by
    ext d d'
    have h := congrFun (congrFun (submatrix_one_kronecker_mul_mul_one_kronecker
      (compressDatabases k X Y) (tableOracle fun D : Fin k → Database X Y ↦ (D x.1).lookup)
      ((t, z) : X × Y) ((x.2, 0) : X × Y)) d) d'
    rw [submatrix_tableOracle] at h
    exact (congrFun (congrFun (compressedVCOracle_U_eq_conj x.1) _) _).trans h
  rw [EmulatedOracle.branch_run₂_callBasis, Finset.sum_eq_single (x.2, y)]
  · simp only [↓reduceIte, hb, true_and]
    rfl
  · rintro ⟨t, z⟩ _ hne
    by_cases hz : z = y
    · subst z
      have ht : t ≠ x.2 := fun h ↦ hne (by simp [h])
      have hzero : (compressedVCOracle k X Y).block x.1 (t, y) (x.2, 0) = 0 := by
        rw [hb]
        change (compressDatabases k X Y *
          diagonal (fun D : Fin k → Database X Y ↦
            if t = x.2 ∧ (D x.1).lookup x.2 = y then 1 else 0) *
          compressDatabases k X Y : Matrix (Fin k → Database X Y) _ ℂ) = 0
        simp [ht]
      simp only [↓reduceIte, hzero, kronecker_zero, MatrixMap.conj_zero]
    · simp [hz]
  · simp

/-- An ordinary answer projector commutes with every ordinary query on a separate call register. -/
theorem answer_commute_ordinary (p : Fin k) (x : Fin k × X) (y : Y) :
    (show Matrix ((X × Y) × (Fin k → Database X Y))
      ((X × Y) × (Fin k → Database X Y)) ℂ from (compressedVCOracle k X Y).U p) *
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ answer x y) =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ answer x y) *
        (show Matrix ((X × Y) × (Fin k → Database X Y))
          ((X × Y) × (Fin k → Database X Y)) ℂ from (compressedVCOracle k X Y).U p) := by
  let C := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressDatabases k X Y
  let D : Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
    diagonal fun d ↦ if (d x.1).lookup x.2 = y then 1 else 0
  have hCC : C * C = 1 := by
    simp [C, ← mul_kronecker_mul, compressDatabases_mul_self]
  have hT : tableOracle (fun d : Fin k → Database X Y ↦ (d p).lookup) *
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ D) =
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ D) *
          tableOracle (fun d : Fin k → Database X Y ↦ (d p).lookup) := by
    apply tableOracle_mul_one_kronecker_comm
    intro d d' h
    have he : d = d' := by
      by_contra hn
      exact h (by simp [D, diagonal_apply_ne _ hn])
    rw [he]
  have hA : (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ answer x y =
      C * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ D) * C := by
    simp [C, D, answer, ← mul_kronecker_mul]
  rw [compressedVCOracle_U_eq_conj, hA]
  change (C * _ * C) * (C * _ * C) = (C * _ * C) * (C * _ * C)
  rw [compressed_conjugate_mul C hCC, compressed_conjugate_mul C hCC, hT]

/-- The compressed oracle has complete projective classical answers on all states.
The generic API supplies fixed-coin adaptive replay and rejection of contradictory lists. -/
@[expose]
noncomputable def projectiveClassicalAnswers :
    ProjectiveClassicalAnswers (compressedVCOracle k X Y).toEmulatedOracle (Fin k × X) Y where
  A := answer
  hermitian := answer_hermitian
  orthogonal x z y := by
    change answer x z * answer x y = if z = y then answer x z else 0
    rw [answer_orthogonal]
    split_ifs with h <;> simp_all
  complete := answer_complete
  commute_cells x y x' y' := answer_commute x x' y y'
  commute_ordinary := answer_commute_ordinary

/-- The mixed answer certificate preserves the distinction between an ordinary answer and
both kinds of checked outcome. It supplies algebra, not an additional runtime port. -/
@[expose]
noncomputable def mixedAnswers :=
  (projectiveClassicalAnswers (k := k) (X := X) (Y := Y)).sumAnswers
    (compressedVCOracle k X Y).classicalRead (fun x y c a ↦ answer_commute_checked x c y a)

/-- An ordinary basis call uses the live coherent ordinary port; a checked call uses the
implemented read port. The sum tag records which capability produced the answer. -/
@[expose]
noncomputable def mixedCall (B : QReg) :
    (Fin k × X) ⊕ (Fin k × X) → QComp (mixedOracleSpec k X Y) B B (Y ⊕ Option Y)
  | .inl x =>
    QuantumComp₂.map Sum.inl
      ((QComp.callBasis (spec := uSpec (Fin k) (oIn k X Y)) x.1 B (x.2, 0)
        (fun o _ ↦ o.2)).toCoherent.liftOrdinary)
  | .inr x => ((compressedVCOracle k X Y).classicalRead.classicalCall B x).map Sum.inr

/-- Both capabilities realize their own projectors in the actual checked runtime. -/
theorem branch_mixedCall (B : QReg) (x : (Fin k × X) ⊕ (Fin k × X)) (a : Y ⊕ Option Y) :
    ((compressedVCOracle k X Y).mixedRuntime.run₂ .instruments (mixedCall B x)).branch a =
      (mixedAnswers (k := k) (X := X) (Y := Y)).branch B x a := by
  have ho (x : Fin k × X) (y : Y) :
      ((compressedVCOracle k X Y).mixedRuntime.run₂ .instruments
        ((QComp.callBasis (spec := uSpec (Fin k) (oIn k X Y)) x.1 B (x.2, 0)
          (fun o _ ↦ o.2)).toCoherent.liftOrdinary)).branch y =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ answer x y) := by
    erw [QuantumRuntime.branch_run₂]
    change (((compressedVCOracle k X Y).coherent.toRuntime.extend
      (t := classicalReadSpec (Fin k × X) (Option Y))
      (compressedVCOracle k X Y).classicalRead.step).run .instruments _).branch _ = _
    erw [QuantumRuntime.run_liftOrdinary, EmulatedOracle.run_toCoherent]
    exact branch_eq B x y
  cases x <;> cases a
  all_goals
    erw [mixedCall, QuantumRuntime.run₂_map]
    change (DSubInstrument.map _ _).branch _ = _
    erw [DSubInstrument.branch_map_apply_univ]
    simp only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
      cast_eq, dite_eq_ite, ite_false, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · erw [ho]
    rfl
  · simp only [ProjectiveClassicalAnswers.branch, mixedAnswers,
      ProjectiveClassicalAnswers.sumAnswers, kronecker_zero, MatrixMap.conj_zero]
    rfl
  · simp only [ProjectiveClassicalAnswers.branch, mixedAnswers,
      ProjectiveClassicalAnswers.sumAnswers, kronecker_zero, MatrixMap.conj_zero]
    rfl
  · erw [ProjectiveClassicalAnswers.branch_classicalCall]
    rfl

/-- A fixed mixed policy is realized by alternating actual ordinary and checked calls.
The retained branch is the product of the mixed projectors selected by the answer history. -/
theorem branch_mixedAdaptive (B : QReg)
    (next : List (Y ⊕ Option Y) → (Fin k × X) ⊕ (Fin k × X)) (ys : List (Y ⊕ Option Y)) :
    ((compressedVCOracle k X Y).mixedRuntime.run₂ .instruments
      (ProjectiveClassicalAnswers.checkMixedTranscript (mixedCall B) next ys)).branch true =
      (mixedAnswers (k := k) (X := X) (Y := Y)).transcriptBranch B
        (ProjectiveClassicalAnswers.adaptiveTranscript next ys) :=
  (mixedAnswers (k := k) (X := X) (Y := Y)).branch_checkMixedTranscript
    (compressedVCOracle k X Y).classicalRead B (mixedCall B) (branch_mixedCall B) next ys

/-- Terminal histories of the actual mixed execution replay with the same coins, including
answer-dependent stopping and checked failures. Distinct terminal histories have zero branch. -/
theorem replay_mixedAdaptive {Coins : Type*} (B : QReg)
    (next : Coins → List (Y ⊕ Option Y) → (Fin k × X) ⊕ (Fin k × X))
    (stop : Coins → List (Y ⊕ Option Y) → Bool) (coins : Coins)
    (ys zs : List (Y ⊕ Option Y))
    (hy : ProjectiveClassicalAnswers.TerminalTranscript (stop coins) ys)
    (hz : ProjectiveClassicalAnswers.TerminalTranscript (stop coins) zs) :
    ((compressedVCOracle k X Y).mixedRuntime.run₂ .instruments
        (ProjectiveClassicalAnswers.checkMixedTranscript
          (mixedCall B) (next coins) zs)).branch true ∘ₗ
      ((compressedVCOracle k X Y).mixedRuntime.run₂ .instruments
        (ProjectiveClassicalAnswers.checkMixedTranscript
          (mixedCall B) (next coins) ys)).branch true =
      if zs = ys then ((compressedVCOracle k X Y).mixedRuntime.run₂ .instruments
        (ProjectiveClassicalAnswers.checkMixedTranscript (mixedCall B) (next coins) ys)).branch true
      else 0 :=
  (mixedAnswers (k := k) (X := X) (Y := Y)).replay_checkMixedTranscript
    (compressedVCOracle k X Y).classicalRead B (mixedCall B) (branch_mixedCall B)
    next stop coins ys zs hy hz

end CompressedReplay

end Quantum
