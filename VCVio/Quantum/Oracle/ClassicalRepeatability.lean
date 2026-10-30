/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.ClassicalCalls
public import VCVio.Quantum.Oracle.ClassicalRead

/-!
# Projective classical answers and exact replay

The sufficient condition for Definition 10.3(2) of Chiesa, Di, Hu and Zheng,
ePrint 2025/2166, is an instrument of commuting Hermitian projectors with complete
classical outcomes. All identities below act on matrices, hence on arbitrary
subnormalized states entangled with a reference register. No reachable-state condition
or normalization is used. Ordinary queries commute on a separate call register;
no commutation with extraction is assumed.

A fixed coin tape determines a function from answer prefixes to the next query.
`adaptiveTranscript` records its first finitely many queries. Stopping, inputs and coins
may all be parameters of that function. Replay is branchwise: it retains the probability
of the original transcript and leaves its residual joint state unchanged.
-/

public section

open Matrix OracleSpec
open scoped Kronecker

universe uL vL w

namespace Quantum

namespace ProjectiveClassicalAnswers

variable {P : Type*} {In : P → QReg} {E : EmulatedOracle P In}
  {X Y : Type} [Fintype Y] [DecidableEq Y]
  (H : ProjectiveClassicalAnswers E X Y)

/-- The classical-answer branch on a joint reference/private register. -/
@[expose]
noncomputable def branch (B : QReg) (x : X) (y : Y) : MatrixMap (B × E.S) (B × E.S) :=
  MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ H.A x y)

/-- Repeating a classical call preserves exactly the recorded branch; other answers vanish. -/
theorem repeat_branch (B : QReg) (x : X) (z y : Y) :
    H.branch B x z ∘ₗ H.branch B x y = if z = y then H.branch B x y else 0 := by
  rw [branch, branch, ← MatrixMap.conj_mul, ← mul_kronecker_mul, Matrix.one_mul,
    H.orthogonal]
  split_ifs with h <;> simp [h]

/-- Forgetting the answer gives an idempotent channel, including on substates. -/
theorem forget_repeat (B : QReg) (x : X) :
    (∑ y, H.branch B x y) ∘ₗ (∑ y, H.branch B x y) = ∑ y, H.branch B x y := by
  apply LinearMap.ext
  intro ρ
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  have h (z y : Y) : H.branch B x z (H.branch B x y ρ) =
      if z = y then H.branch B x y ρ else 0 := by
    by_cases he : z = y <;> simpa [he] using
      LinearMap.congr_fun (H.repeat_branch B x z y) ρ
  simp_rw [h]
  simp

/-- Product of the projectors prescribed by a classical transcript. -/
noncomputable def projector (tr : QueryLog (X →ₒ Y)) : Matrix E.S E.S ℂ :=
  (tr.map fun q ↦ H.A q.1 q.2).prod

/-- The empty transcript has identity projector. -/
@[simp] theorem projector_nil : H.projector [] = 1 := by simp [projector]

/-- A transcript starts with its first answer projector. -/
@[simp] theorem projector_cons (q : (_ : X) × Y) (tr : QueryLog (X →ₒ Y)) :
    H.projector (q :: tr) = H.A q.1 q.2 * H.projector tr := by simp [projector]

/-- Every answer commutes with every transcript projector. -/
theorem answer_commute_projector (x : X) (y : Y) (tr : QueryLog (X →ₒ Y)) :
    H.A x y * H.projector tr = H.projector tr * H.A x y := by
  exact (Commute.list_prod_right _ _ fun A hA ↦ by
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA
    exact H.commute_cells x y q.1 q.2).eq

/-- All transcript projectors are idempotent, including contradictory transcripts. -/
theorem projector_mul_self (tr : QueryLog (X →ₒ Y)) :
    H.projector tr * H.projector tr = H.projector tr := by
  induction tr with
  | nil => simp
  | cons q tr ih =>
    simp only [projector_cons]
    calc
      _ = H.A q.1 q.2 * (H.projector tr * H.A q.1 q.2) * H.projector tr := by
        simp only [Matrix.mul_assoc]
      _ = H.A q.1 q.2 * (H.A q.1 q.2 * H.projector tr) * H.projector tr := by
        rw [← H.answer_commute_projector]
      _ = _ := by rw [← Matrix.mul_assoc, H.orthogonal, ite_eq_left rfl, Matrix.mul_assoc, ih]

/-- The projector of a transcript is Hermitian. -/
theorem projector_hermitian (tr : QueryLog (X →ₒ Y)) :
    (H.projector tr)ᴴ = H.projector tr := by
  induction tr with
  | nil => simp
  | cons q tr ih =>
    rw [projector_cons, conjTranspose_mul, ih, H.hermitian, ← H.answer_commute_projector]

/-- Joint-state branch for a recorded transcript; no renormalization is performed. -/
@[expose]
noncomputable def transcriptBranch (B : QReg) (tr : QueryLog (X →ₒ Y)) :
    MatrixMap (B × E.S) (B × E.S) :=
  MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ H.projector tr)

/-- The empty transcript leaves the joint state unchanged. -/
@[simp] theorem transcriptBranch_nil (B : QReg) :
    H.transcriptBranch B [] = LinearMap.id := by
  simp [transcriptBranch]

/-- The transcript branch is the operational composition in query order. -/
theorem transcriptBranch_cons (B : QReg) (q : (_ : X) × Y) (tr : QueryLog (X →ₒ Y)) :
    H.transcriptBranch B (q :: tr) = H.transcriptBranch B tr ∘ₗ H.branch B q.1 q.2 := by
  rw [transcriptBranch, projector_cons, H.answer_commute_projector,
    ← Matrix.one_mul (1 : Matrix B B ℂ), mul_kronecker_mul, MatrixMap.conj_mul]
  rfl

/-- Replaying any recorded transcript leaves its whole subnormalized branch unchanged. -/
theorem replay_transcript (B : QReg) (tr : QueryLog (X →ₒ Y)) :
    H.transcriptBranch B tr ∘ₗ H.transcriptBranch B tr = H.transcriptBranch B tr := by
  rw [transcriptBranch, ← MatrixMap.conj_mul, ← mul_kronecker_mul, Matrix.one_mul,
    H.projector_mul_self]

/-- Products of cross-commuting answer families commute, so mixed transcripts may be grouped
by capability without changing the retained joint branch. -/
theorem projector_commute {Addr Ans : Type} [Fintype Ans] [DecidableEq Ans]
    (K : ProjectiveClassicalAnswers E Addr Ans)
    (hcomm : ∀ x y c a, H.A x y * K.A c a = K.A c a * H.A x y)
    (ts : QueryLog (X →ₒ Y)) (us : QueryLog (Addr →ₒ Ans)) :
    H.projector ts * K.projector us = K.projector us * H.projector ts := by
  have ha (x : X) (y : Y) : H.A x y * K.projector us = K.projector us * H.A x y := by
    induction us with
    | nil => simp
    | cons q us ih =>
      rw [projector_cons, ← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, ih,
        ← Matrix.mul_assoc]
  induction ts with
  | nil => simp
  | cons q ts ih =>
    rw [projector_cons, Matrix.mul_assoc, ih, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]

/-- Replay of a transcript containing both commuting answer families preserves its whole
branch. Fixing the query policies and coins fixes the two retained answer lists. -/
theorem replay_mixed_transcripts {Addr Ans : Type} [Fintype Ans] [DecidableEq Ans]
    (K : ProjectiveClassicalAnswers E Addr Ans)
    (hcomm : ∀ x y c a, H.A x y * K.A c a = K.A c a * H.A x y)
    (B : QReg) (ts : QueryLog (X →ₒ Y)) (us : QueryLog (Addr →ₒ Ans)) :
    (H.transcriptBranch B ts ∘ₗ K.transcriptBranch B us) ∘ₗ
        (H.transcriptBranch B ts ∘ₗ K.transcriptBranch B us) =
      H.transcriptBranch B ts ∘ₗ K.transcriptBranch B us := by
  simp only [transcriptBranch, ← MatrixMap.conj_mul, ← mul_kronecker_mul, Matrix.one_mul]
  congr 2
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (K.projector us),
    ← H.projector_commute K hcomm ts us, Matrix.mul_assoc,
    K.projector_mul_self, ← Matrix.mul_assoc, H.projector_mul_self]

/-- The adaptive transcript determined by a fixed choice of coins, inputs and answer prefix.
The caller chooses a finite stopping prefix; no bound on the policy or its computation is used. -/
@[expose]
def adaptiveTranscript (next : List Y → X) : List Y → QueryLog (X →ₒ Y)
  | [] => []
  | y :: ys => ⟨next [], y⟩ :: adaptiveTranscript (fun pre ↦ next (y :: pre)) ys

/-- Fixed-coin adaptive replay preserves the original joint branch, including its mass.
The policy may depend on arbitrary fixed public inputs, private coins and prior answers. -/
theorem replay_fixedCoins_transcript {Coins : Type*} (B : QReg)
    (next : Coins → List Y → X) (coins : Coins) (answers : List Y) :
    H.transcriptBranch B (adaptiveTranscript (next coins) answers) ∘ₗ
        H.transcriptBranch B (adaptiveTranscript (next coins) answers) =
      H.transcriptBranch B (adaptiveTranscript (next coins) answers) :=
  H.replay_transcript B _

/-- Factoring the first answers of two transcript products uses cross-cell commutation. -/
theorem projector_cons_mul_cons (q r : (_ : X) × Y) (ts us : QueryLog (X →ₒ Y)) :
    H.projector (q :: ts) * H.projector (r :: us) =
      (H.A q.1 q.2 * H.A r.1 r.2) * (H.projector ts * H.projector us) := by
  simp only [projector_cons]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (H.projector ts),
    ← H.answer_commute_projector]
  simp only [Matrix.mul_assoc]

/-- Two adaptive transcripts of the same length are orthogonal unless every answer agrees.
The query policy is recomputed from the same fixed inputs and coins in both executions. -/
theorem adaptive_projector_mul (next : List Y → X) (ys zs : List Y)
    (hlen : zs.length = ys.length) :
    H.projector (adaptiveTranscript next zs) * H.projector (adaptiveTranscript next ys) =
      if zs = ys then H.projector (adaptiveTranscript next ys) else 0 := by
  induction ys generalizing zs next with
  | nil =>
    have hz : zs = [] := List.length_eq_zero_iff.mp hlen
    subst zs
    simp [adaptiveTranscript]
  | cons y ys ih =>
    cases zs with
    | nil => simp at hlen
    | cons z zs =>
      have hl : zs.length = ys.length := Nat.succ.inj hlen
      simp only [adaptiveTranscript]
      rw [H.projector_cons_mul_cons, H.projector_cons]
      rw [H.orthogonal]
      by_cases hzy : z = y
      · subst z
        rw [ite_eq_left rfl, ih _ _ hl]
        by_cases hzs : zs = ys <;> simp [hzs]
      · simp [hzy]

/-- Replay returns the same adaptive answer transcript and preserves its joint branch.
An alternative answer transcript of the same length has zero residual branch. -/
theorem replay_fixedCoins_answers {Coins : Type*} (B : QReg)
    (next : Coins → List Y → X) (coins : Coins) (ys zs : List Y)
    (hlen : zs.length = ys.length) :
    H.transcriptBranch B (adaptiveTranscript (next coins) zs) ∘ₗ
        H.transcriptBranch B (adaptiveTranscript (next coins) ys) =
      if zs = ys then H.transcriptBranch B (adaptiveTranscript (next coins) ys) else 0 := by
  rw [transcriptBranch, transcriptBranch, ← MatrixMap.conj_mul, ← mul_kronecker_mul,
    Matrix.one_mul, H.adaptive_projector_mul _ _ _ hlen]
  split_ifs <;> simp

/-- A finite answer sequence at which a deterministic stopping policy first stops.
This permits answer-dependent stopping times without a uniform query bound. -/
@[expose]
def TerminalTranscript (stop : List Y → Bool) : List Y → Prop
  | [] => stop [] = true
  | y :: ys => stop [] = false ∧ TerminalTranscript (fun pre ↦ stop (y :: pre)) ys

/-- Complete stopped adaptive transcripts are orthogonal unless identical, even when their
lengths differ. Both runs use the same fixed coins, query policy and stopping policy. -/
theorem terminal_adaptive_projector_mul (next : List Y → X) (stop : List Y → Bool)
    (ys zs : List Y) (hy : TerminalTranscript stop ys) (hz : TerminalTranscript stop zs) :
    H.projector (adaptiveTranscript next zs) * H.projector (adaptiveTranscript next ys) =
      if zs = ys then H.projector (adaptiveTranscript next ys) else 0 := by
  induction ys generalizing next stop zs with
  | nil =>
    cases zs with
    | nil => simp [adaptiveTranscript]
    | cons z zs => simp_all [TerminalTranscript]
  | cons y ys ih =>
    cases zs with
    | nil => simp_all [TerminalTranscript]
    | cons z zs =>
      simp only [TerminalTranscript] at hy hz
      simp only [adaptiveTranscript]
      rw [H.projector_cons_mul_cons, H.projector_cons, H.orthogonal]
      by_cases he : z = y
      · subst z
        rw [ite_eq_left rfl, ih _ _ _ hy.2 hz.2]
        by_cases hs : zs = ys <;> simp [hs]
      · simp [he]

/-- Fixed-coin replay of a terminating adaptive classical algorithm has exactly its original
terminal transcript and residual joint branch. No equality of transcript lengths is assumed. -/
theorem replay_fixedCoins_terminal {Coins : Type*} (B : QReg)
    (next : Coins → List Y → X) (stop : Coins → List Y → Bool) (coins : Coins)
    (ys zs : List Y) (hy : TerminalTranscript (stop coins) ys)
    (hz : TerminalTranscript (stop coins) zs) :
    H.transcriptBranch B (adaptiveTranscript (next coins) zs) ∘ₗ
        H.transcriptBranch B (adaptiveTranscript (next coins) ys) =
      if zs = ys then H.transcriptBranch B (adaptiveTranscript (next coins) ys) else 0 := by
  rw [transcriptBranch, transcriptBranch, ← MatrixMap.conj_mul, ← mul_kronecker_mul,
    Matrix.one_mul, H.terminal_adaptive_projector_mul _ _ _ _ hy hz]
  split_ifs <;> simp

/-- Combine two commuting answer families while retaining the capability in both the action
and outcome. An outcome from the other capability has zero projector. -/
@[expose]
noncomputable def sumAnswers {Addr Ans : Type} [Fintype Ans] [DecidableEq Ans]
    (K : ProjectiveClassicalAnswers E Addr Ans)
    (hcomm : ∀ x y c a, H.A x y * K.A c a = K.A c a * H.A x y) :
    ProjectiveClassicalAnswers E (X ⊕ Addr) (Y ⊕ Ans) where
  A x a := match x, a with
    | .inl x, .inl y => H.A x y
    | .inr c, .inr a => K.A c a
    | _, _ => 0
  hermitian x a := by cases x <;> cases a <;> simp [H.hermitian, K.hermitian]
  orthogonal x a b := by
    cases x <;> cases a <;> cases b <;> simp [H.orthogonal, K.orthogonal]
  complete x := by cases x <;> simp [Fintype.sum_sum_type, H.complete, K.complete]
  commute_cells x a c b := by
    cases x <;> cases a <;> cases c <;> cases b <;>
      first | exact H.commute_cells _ _ _ _ | exact K.commute_cells _ _ _ _ |
        exact hcomm _ _ _ _ | exact (hcomm _ _ _ _).symm | simp
  commute_ordinary p x a := by
    cases x <;> cases a <;> simp [H.commute_ordinary, K.commute_ordinary]

/-- Retain an answer history under a fixed policy and an operational implementation of its
calls. The policy sees all earlier outcomes, including missing checked answers. -/
noncomputable def checkMixedTranscript {spec : QuantumOracleSpec} {B : QReg}
    (call : X → QComp spec B B Y) (next : List Y → X) : List Y → QComp spec B B Bool
  | [] => QuantumComp₂.pure true
  | y :: ys => (call (next [])).bind fun z ↦
      if z = y then checkMixedTranscript call (fun pre ↦ next (z :: pre)) ys
      else QuantumComp₂.pure false

section runtime

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg}
  {E : EmulatedOracle P In} (H : ProjectiveClassicalAnswers E X Y)

/-- Read a classical address through the dedicated read port. -/
@[expose]
noncomputable def classicalCall (_H : ProjectiveClassicalAnswers E X Y) (B : QReg) (x : X) :
    QComp (withReadSpec (EmulatedOracle.cohSpec In) X Y) B B Y :=
  QuantumComp₂.bind (QComp.act (B := QReg.of (Unit × B))
    (SubInstrument.relabel (Equiv.uniqueProd B Unit).symm)) fun _ ↦
    QuantumComp₂.bind (QuantumComp₂.query (spec := withReadSpec (EmulatedOracle.cohSpec In) X Y)
      (.inr x) B (Equiv.refl (Unit × B))) fun a ↦
      QuantumComp₂.bind (QComp.act (SubInstrument.relabel (Equiv.uniqueProd B Unit))) fun _ ↦
        QuantumComp₂.pure a

/-- A read restores the trivial public factor around the runtime's read-port step. -/
theorem run₂_classicalCall (B : QReg) (x : X) :
    (E.withClassicalReads H).run₂ .instruments (H.classicalCall B x) =
      E.read H x B := by
  let R := E.withClassicalReads H
  change R.run₂ .instruments (H.classicalCall B x) = _
  rw [classicalCall, EmulatedOracle.read, QuantumRuntime.run₂_act_bind,
    SubInstrument.frame_relabel]
  unfold SubInstrument.reindex
  refine congrArg (fun f : Unit → SubInstrument ((Unit × B) × R.D) (B × R.D) Y ↦
    (SubInstrument.relabel
      ((Equiv.uniqueProd B Unit).prodCongr (Equiv.refl R.D)).symm).bind f) ?_
  funext u
  have hq := R.run₂_query_bind (A := QReg.of (Unit × B)) (B := B)
    .instruments (.inr x) B
    (Equiv.refl (Unit × B)) (fun a ↦
      QuantumComp₂.bind (QComp.act (SubInstrument.relabel (Equiv.uniqueProd B Unit)))
        fun _ ↦ QuantumComp₂.pure a)
  refine hq.trans ?_
  refine congrArg (fun f : Y → SubInstrument ((Unit × B) × R.D) (B × R.D) Y ↦
    (R.queryStep (A := QReg.of (Unit × B)) (.inr x) B (Equiv.refl _)).bind f) ?_
  funext a
  rw [QuantumRuntime.run₂_act_bind]
  erw [SubInstrument.frame_relabel]
  exact congrArg (fun f : Unit → SubInstrument (B × R.D) (B × R.D) Y ↦
    (SubInstrument.relabel
      ((Equiv.uniqueProd B Unit).prodCongr (Equiv.refl R.D))).bind f)
    (funext fun _ ↦ R.run₂_pure .instruments a)

/-- The implemented read has the framed answer-projector branch. -/
theorem branch_classicalCall (B : QReg) (x : X) (y : Y) :
    ((E.withClassicalReads H).run₂ .instruments (H.classicalCall B x)).branch y =
      H.branch B x y := by
  rw [H.run₂_classicalCall, E.read_branch]
  rfl

/-- Any implementation of the certified calls in the mixed runtime realizes the adaptive
history projector. In particular the implementation may use both runtime ports. -/
theorem branch_checkMixedTranscript {Addr Ans : Type} [Fintype Ans] [DecidableEq Ans]
    (K : ProjectiveClassicalAnswers E Addr Ans) (B : QReg)
    (call : X → QComp (withReadSpec (EmulatedOracle.cohSpec In) Addr Ans) B B Y)
    (hcall : ∀ x y, ((E.withClassicalReads K).run₂ .instruments (call x)).branch y =
      H.branch B x y) (next : List Y → X) (ys : List Y) :
    ((E.withClassicalReads K).run₂ .instruments
      (checkMixedTranscript call next ys)).branch true =
      H.transcriptBranch B (adaptiveTranscript next ys) := by
  induction ys generalizing next with
  | nil =>
    rw [checkMixedTranscript, QuantumRuntime.run₂_pure, SubInstrument.branch_pure_self]
    simp only [adaptiveTranscript, transcriptBranch_nil]
    rfl
  | cons y ys ih =>
    rw [checkMixedTranscript, QuantumRuntime.run₂_bind,
      DSubInstrument.branch_bind_apply_univ, Finset.sum_eq_single y]
    · rw [ite_eq_left rfl, ih, hcall]
      exact (H.transcriptBranch_cons B ⟨next [], y⟩ _).symm
    · intro z _ hz
      rw [ite_eq_right hz, QuantumRuntime.run₂_pure,
        SubInstrument.branch_pure_of_ne (by decide), LinearMap.zero_comp]
    · simp

/-- Execute an adaptive query prefix and retain precisely the prescribed answer transcript.
Every call uses the actual emulated-oracle runtime; a mismatched answer returns `false`.
The program is the postselection of a deterministic classical algorithm with fixed coins. -/
noncomputable def checkAdaptiveTranscript (B : QReg) (next : List Y → X) :
    List Y → QComp (withReadSpec (EmulatedOracle.cohSpec In) X Y) B B Bool :=
  checkMixedTranscript (H.classicalCall B) next

/-- The actual accepting branch of adaptive transcript postselection is its projector product.
Rejected outcomes are retained as separate branches of the program, never renormalized away. -/
theorem branch_checkAdaptiveTranscript (B : QReg) (next : List Y → X) (ys : List Y) :
    ((E.withClassicalReads H).run₂ .instruments
      (H.checkAdaptiveTranscript B next ys)).branch true =
      H.transcriptBranch B (adaptiveTranscript next ys) :=
  H.branch_checkMixedTranscript H B (H.classicalCall B) (H.branch_classicalCall B) next ys

/-- Operational fixed-coin replay of any adaptive classical query prefix leaves its accepting
joint branch unchanged. The initial state can be the output of any preceding quantum program. -/
theorem replay_checkAdaptiveTranscript (B : QReg) (next : List Y → X) (ys : List Y) :
    ((E.withClassicalReads H).run₂ .instruments
        (H.checkAdaptiveTranscript B next ys)).branch true ∘ₗ
      ((E.withClassicalReads H).run₂ .instruments
        (H.checkAdaptiveTranscript B next ys)).branch true =
      ((E.withClassicalReads H).run₂ .instruments
        (H.checkAdaptiveTranscript B next ys)).branch true := by
  rw [H.branch_checkAdaptiveTranscript]
  exact H.replay_transcript B _

/-- With the same coins and stopping rule, replay of a terminal mixed execution retains
exactly its original history and substate; incompatible terminal histories vanish. -/
theorem replay_checkMixedTranscript {Addr Ans : Type} [Fintype Ans] [DecidableEq Ans]
    (K : ProjectiveClassicalAnswers E Addr Ans) (B : QReg)
    (call : X → QComp (withReadSpec (EmulatedOracle.cohSpec In) Addr Ans) B B Y)
    (hcall : ∀ x y, ((E.withClassicalReads K).run₂ .instruments (call x)).branch y =
      H.branch B x y) {Coins : Type*} (next : Coins → List Y → X)
    (stop : Coins → List Y → Bool) (coins : Coins) (ys zs : List Y)
    (hy : TerminalTranscript (stop coins) ys) (hz : TerminalTranscript (stop coins) zs) :
    ((E.withClassicalReads K).run₂ .instruments
        (checkMixedTranscript call (next coins) zs)).branch true ∘ₗ
      ((E.withClassicalReads K).run₂ .instruments
        (checkMixedTranscript call (next coins) ys)).branch true =
      if zs = ys then ((E.withClassicalReads K).run₂ .instruments
        (checkMixedTranscript call (next coins) ys)).branch true else 0 := by
  simp only [H.branch_checkMixedTranscript K B call hcall]
  exact H.replay_fixedCoins_terminal B next stop coins ys zs hy hz

end runtime

/-- An answer already present in a transcript is absorbed by its projector. -/
theorem answer_mul_projector_of_mem (q : (_ : X) × Y) (tr : QueryLog (X →ₒ Y))
    (hq : q ∈ tr) :
    H.A q.1 q.2 * H.projector tr = H.projector tr := by
  induction tr with
  | nil => simp at hq
  | cons r tr ih =>
    rcases List.mem_cons.mp hq with h | h
    · subst r
      rw [projector_cons, ← Matrix.mul_assoc, H.orthogonal, ite_eq_left rfl]
    · rw [projector_cons, ← Matrix.mul_assoc, H.commute_cells, Matrix.mul_assoc, ih h]

/-- A list prescribing two different answers at one address has zero projector. -/
theorem projector_eq_zero_of_contradiction (tr : QueryLog (X →ₒ Y)) (x : X) (y z : Y)
    (hy : ⟨x, y⟩ ∈ tr) (hz : ⟨x, z⟩ ∈ tr) (hne : z ≠ y) : H.projector tr = 0 := by
  calc
    H.projector tr = H.A x z * (H.A x y * H.projector tr) := by
      rw [H.answer_mul_projector_of_mem ⟨x, y⟩ tr hy,
        H.answer_mul_projector_of_mem ⟨x, z⟩ tr hz]
    _ = 0 := by rw [← Matrix.mul_assoc, H.orthogonal, ite_eq_right hne, Matrix.zero_mul]

/-- Contradictory transcripts have zero branch on every joint input. -/
theorem transcriptBranch_eq_zero_of_contradiction (B : QReg) (tr : QueryLog (X →ₒ Y))
    (x : X) (y z : Y) (hy : ⟨x, y⟩ ∈ tr) (hz : ⟨x, z⟩ ∈ tr) (hne : z ≠ y) :
    H.transcriptBranch B tr = 0 := by
  simp [transcriptBranch, H.projector_eq_zero_of_contradiction tr x y z hy hz hne]

/-- Inserting and then forgetting an unused check leaves every commuting retained effect
unchanged. This is an effect identity, not equality of the entire dephased state. -/
theorem sum_unused_check (x : X) (F : Matrix E.S E.S ℂ)
    (hF : ∀ y, H.A x y * F = F * H.A x y) :
    ∑ y, H.A x y * F * H.A x y = F := by
  calc
    _ = ∑ y, F * H.A x y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [hF, Matrix.mul_assoc, H.orthogonal, ite_eq_left rfl]
    _ = F := by rw [← Finset.mul_sum, H.complete, Matrix.mul_one]

/-- A retained transcript effect is unaffected by summing any unused check outcome. -/
theorem sum_unused_check_projector (x : X) (tr : QueryLog (X →ₒ Y)) :
    ∑ y, H.A x y * H.projector tr * H.A x y = H.projector tr :=
  H.sum_unused_check x _ fun y ↦ H.answer_commute_projector x y tr

/-- Removing unused check outcomes preserves every commuting joint effect, even one
involving the external reference register. -/
theorem sum_unused_check_framed (B : QReg) (x : X) (F : Matrix (B × E.S) (B × E.S) ℂ)
    (hF : ∀ y, ((1 : Matrix B B ℂ) ⊗ₖ H.A x y) * F =
      F * ((1 : Matrix B B ℂ) ⊗ₖ H.A x y)) :
    ∑ y, ((1 : Matrix B B ℂ) ⊗ₖ H.A x y) * F *
      ((1 : Matrix B B ℂ) ⊗ₖ H.A x y) = F := by
  have hsum : (∑ y, (1 : Matrix B B ℂ) ⊗ₖ H.A x y) = 1 := by
    change (∑ y, kroneckerBilinear (R := ℂ) (1 : Matrix B B ℂ) (H.A x y)) = 1
    rw [← map_sum, H.complete]
    exact one_kronecker_one
  calc
    _ = ∑ y, F * ((1 : Matrix B B ℂ) ⊗ₖ H.A x y) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [hF, Matrix.mul_assoc, ← mul_kronecker_mul, Matrix.one_mul,
        H.orthogonal, ite_eq_left rfl]
    _ = F := by rw [← Finset.mul_sum, hsum, Matrix.mul_one]

/-- Summing unused check outcomes preserves the unnormalized retained event probability.
The input can be any matrix; in particular it can be an entangled substate. -/
theorem trace_sum_unused_check (B : QReg) (x : X)
    (F ρ : Matrix (B × E.S) (B × E.S) ℂ)
    (hF : ∀ y, ((1 : Matrix B B ℂ) ⊗ₖ H.A x y) * F =
      F * ((1 : Matrix B B ℂ) ⊗ₖ H.A x y)) :
    ∑ y, trace (F * H.branch B x y ρ) = trace (F * ρ) := by
  have he (y : Y) : trace (F * H.branch B x y ρ) =
      trace ((((1 : Matrix B B ℂ) ⊗ₖ H.A x y) * F *
        ((1 : Matrix B B ℂ) ⊗ₖ H.A x y)) * ρ) := by
    simp only [branch, MatrixMap.conj_apply, conjTranspose_kronecker,
      conjTranspose_one, H.hermitian]
    rw [← Matrix.mul_assoc F, trace_mul_cycle]
    simp only [Matrix.mul_assoc]
  simp_rw [he]
  rw [← trace_sum, ← Finset.sum_mul, H.sum_unused_check_framed B x F hF]

/-- Ordinary queries may be interposed between a transcript and its replay, on a separate
call register, without changing the retained transcript projector. -/
theorem ordinary_commute_projector (p : P) (tr : QueryLog (X →ₒ Y)) :
    E.U p * ((1 : Matrix (In p) (In p) ℂ) ⊗ₖ H.projector tr) =
      ((1 : Matrix (In p) (In p) ℂ) ⊗ₖ H.projector tr) * E.U p := by
  induction tr with
  | nil => simp
  | cons q tr ih =>
    rw [projector_cons, ← Matrix.one_mul (1 : Matrix (In p) (In p) ℂ), mul_kronecker_mul]
    rw [← Matrix.mul_assoc, H.commute_ordinary, Matrix.mul_assoc, ih, ← Matrix.mul_assoc]

/-- An ordinary query on a separate register can intervene before replay without changing
the retained branch. The claim is an identity of joint-state maps, not only of probabilities. -/
theorem replay_after_ordinary (p : P) (tr : QueryLog (X →ₒ Y)) :
    H.transcriptBranch (In p) tr ∘ₗ MatrixMap.conj (E.U p) ∘ₗ
        H.transcriptBranch (In p) tr =
      MatrixMap.conj (E.U p) ∘ₗ H.transcriptBranch (In p) tr := by
  simp only [transcriptBranch, ← MatrixMap.conj_mul]
  congr 1
  rw [← Matrix.mul_assoc, ← H.ordinary_commute_projector, Matrix.mul_assoc,
    ← mul_kronecker_mul,
    Matrix.one_mul, H.projector_mul_self]

/-- A retained transcript commutes through every ordinary quantum program, including
adaptive local instruments, aborts and register changes, separately on every final leaf. -/
theorem commute_run {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w}
    {B : QReg} (prog : QuantumComp L (uSpec P In) W B) (leaf : Σ u, W u)
    (tr : QueryLog (X →ₒ Y)) :
    (E.toRuntime.run I prog).branch leaf ∘ₗ H.transcriptBranch B tr =
      H.transcriptBranch leaf.1 tr ∘ₗ (E.toRuntime.run I prog).branch leaf := by
  have hs := QuantumRuntime.simulation (R₁ := E.toRuntime) (R₂ := E.toRuntime)
    (V := MatrixMap.conj (H.projector tr)) I (fun p r ↦ ?_) prog leaf
  · simpa only [MatrixMap.amplifyLeft_conj, transcriptBranch] using hs
  · rw [E.toRuntime_step_branch, MatrixMap.amplifyLeft_conj]
    simp only [← MatrixMap.conj_mul]
    rw [H.ordinary_commute_projector]

/-- Exact replay after a general ordinary quantum program. Local operations can change or
measure the external registers; the private transcript remains fixed on each subnormalized leaf. -/
theorem replay_after_run {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w}
    {B : QReg} (prog : QuantumComp L (uSpec P In) W B) (leaf : Σ u, W u)
    (tr : QueryLog (X →ₒ Y)) :
    H.transcriptBranch leaf.1 tr ∘ₗ (E.toRuntime.run I prog).branch leaf ∘ₗ
        H.transcriptBranch B tr =
      (E.toRuntime.run I prog).branch leaf ∘ₗ H.transcriptBranch B tr := by
  rw [← LinearMap.comp_assoc, ← H.commute_run I prog leaf tr,
    LinearMap.comp_assoc, H.replay_transcript]

end ProjectiveClassicalAnswers
end Quantum
