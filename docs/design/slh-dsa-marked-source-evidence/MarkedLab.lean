/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import RelativeKernel
public import NativePotential
public import HashSig.SLHDSA.Security.HiddenUndrawn
import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.QueryBound
import VCVio.OracleComp.Coercions.Add.Basic
public import ForwardingBudgetGuard
public import FreeGuardInterpretation
public import VCVio.OracleComp.QueryTracking.ObservationOracle
public import HashSig.SLHDSA.Security.LabBudget
import all VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape.Position
import all RelativeKernel
import all NativePotential

/-! # Marked lab transcripts and their native source queries -/

public section
open OracleComp OracleSpec SignatureAlg
namespace SLHDSA.Security.MarkedLab
variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

section Construction
variable [SampleableType core.Y] [DecidableEq core.Y]
variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

/-- The lab algorithms with adjacent phase markers and explicit signing-attempt markers. -/
noncomputable def markedLabScheme
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed) :
    SignatureAlg (OracleComp (SigningView.Events.Spec (labSpec core) (List Byte)))
      (List Byte) (PublicKeyCore core) (PublicKeyCore core)
      (GeneralScheme.SignatureCore vp core) where
  keygen := simulateQ (SigningView.Events.phaseImpl (labSpec core) (List Byte) .keygen)
    (labScheme core optRand pkSeed).keygen
  sign pk sk msg := do
    SigningView.Events.emit (labSpec core) (List Byte) (.signingAttempt msg)
    simulateQ (SigningView.Events.phaseImpl (labSpec core) (List Byte) .signer)
      ((labScheme core optRand pkSeed).sign pk sk msg)
  verify pk msg sig :=
    simulateQ (SigningView.Events.phaseImpl (labSpec core) (List Byte) .verification)
      ((labScheme core optRand pkSeed).verify pk msg sig)

/-- The lab adversary with ambient phase markers and its original signing calls. -/
noncomputable def markedLabAdversary {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist))
    (pkSeed : core.PkSeed) : UnforgeableAdversary (markedLabScheme core optRand pkSeed) :=
  ⟨SigningView.Events.mainWithEvents (labAdversary core adv pkSeed).main⟩

/-- The complete marked lab transcript retaining keys, forgery, log and verification. -/
noncomputable def markedLabExperiment {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist))
    (pkSeed : core.PkSeed) :
    OracleComp (SigningView.Events.Spec (labSpec core) (List Byte)) (DeriveOutcome core) :=
  unforgeableTranscriptExperiment (markedLabAdversary core adv pkSeed)

/-- The marked transcript continuation at explicitly supplied public and secret keys. -/
noncomputable def markedLabSuffix
    (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed)
    (e : core.SkSeed ≃ core.Y)
    (adv : UnforgeableAdversary
      (romScheme core e (fun pk => pure (kappa pk)) (pure pkSeed)))
    (pk sk : PublicKeyCore core) :
    OracleComp (SigningView.Events.Spec (labSpec core) (List Byte)) (DeriveOutcome core) := do
  let ((msg, sig), log) ←
    (markedLabScheme core (fun pk => pure (kappa pk)) pkSeed).runWithSigningOracle pk sk
      ((markedLabAdversary core adv pkSeed).main pk)
  let verified ← (markedLabScheme core (fun pk => pure (kappa pk)) pkSeed).verify pk msg sig
  return ⟨pk, sk, log, msg, sig, verified⟩

/-- Native signer key constraints and the absence of forger nonce queries. -/
def SuffixShape (pkSeed : core.PkSeed) (sk : PublicKeyCore core) :
    (Coverage.roleSpec core).Domain → Prop
  | .inr (.inl (.inr (.inr _))) => False
  | .inr (.inr (.inl (.inl (.hmsg _ seed root _)))) =>
      seed = pkSeed ∧ root = sk.pkRoot
  | _ => True

end Construction

section Erasure
private abbrev erase := SigningView.Events.handlerWithEvents (Request := List Byte)
  (QueryImpl.id' (labSpec core))

private theorem erase_phase {α : Type} (phase : SigningView.Phase)
    (program : OracleComp (labSpec core) α) :
    simulateQ (erase core)
      (simulateQ (SigningView.Events.phaseImpl (labSpec core) (List Byte) phase) program) =
        program := by
  rw [← QueryImpl.simulateQ_compose]
  have h : erase core ∘ₛ SigningView.Events.phaseImpl (labSpec core) (List Byte) phase =
      QueryImpl.id' (labSpec core) := by
    funext input
    simp [erase, QueryImpl.apply_compose, SigningView.Events.phaseImpl,
      SigningView.Events.emit, SigningView.Events.handlerWithEvents]
  rw [h, simulateQ_id']

variable [SampleableType core.Y] [DecidableEq core.Y]

private theorem erase_scheme
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed) :
    (markedLabScheme core optRand pkSeed).map (simulateQ' (erase core)) =
      labScheme core optRand pkSeed := by
  apply SignatureAlg.ext
  · simp only [map_keygen, markedLabScheme]
    exact erase_phase core _ _
  · funext pk sk msg
    simp [map_sign, markedLabScheme, simulateQ_bind, SigningView.Events.emit,
      erase, SigningView.Events.handlerWithEvents, erase_phase]
  · funext pk msg sig
    simp only [map_verify, markedLabScheme]
    exact erase_phase core _ _

private theorem adversary_ext {ι : Type} {spec : OracleSpec ι} {M PK SK Sig : Type}
    {alg : SignatureAlg (OracleComp spec) M PK SK Sig}
    (a b : UnforgeableAdversary alg) (h : a.main = b.main) : a = b := by
  cases a
  cases b
  exact congrArg UnforgeableAdversary.mk h

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

private theorem erase_main
    {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist))
    (pkSeed : core.PkSeed) (pk : PublicKeyCore core) :
    ((markedLabAdversary core adv pkSeed).mapOracles (erase core)
      (sigAlg' := labScheme core optRand pkSeed)).main pk =
        (labAdversary core adv pkSeed).main pk := by
  rw [UnforgeableAdversary.mapOracles_main]
  simp only [markedLabAdversary]
  unfold SigningView.Events.mainWithEvents
  rw [← QueryImpl.simulateQ_compose]
  let : (labSpec core) ⊂ₒ
      (labSpec core + (List Byte →ₒ GeneralScheme.SignatureCore vp core)) :=
    OracleQuery.subSpec_add_left
  calc
    _ = simulateQ (QueryImpl.id'
        (labSpec core + (List Byte →ₒ GeneralScheme.SignatureCore vp core)))
          ((labAdversary core adv pkSeed).main pk) := by
      congr 1
      funext input
      rcases input with native | request
      · simp only [OracleSpec.add_apply_inl, erase, QueryImpl.addLift_def,
          ofPFunctor_toPFunctor, SigningView.Events.phaseImpl, SigningView.Events.emit,
          PFunctor.Handler.preInsert_apply, monadLift_self, simulateQ_seqRight,
          simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
          QueryImpl.apply_compose, QueryImpl.add, OracleSpec.add_apply_inr,
          QueryImpl.add_apply_inl, PFunctor.Handler.liftTarget_apply,
          SigningView.Events.handlerWithEvents, liftM_pure, map_pure, id_eq,
          QueryImpl.id'_apply, pure_seqRight]
        rw [← liftComp_eq_liftM, liftComp_liftM_query]
        rw [OracleComp.liftM_eq_liftM_liftM
          (superSpec := labSpec core + (List Byte →ₒ GeneralScheme.SignatureCore vp core))
          ((labSpec core).query native)]
        simp only [OracleQuery.liftM_add_left_query]
      · simp only [OracleSpec.add_apply_inr, QueryImpl.addLift_def,
          ofPFunctor_toPFunctor, QueryImpl.apply_compose, QueryImpl.add, simulateQ_query,
          OracleQuery.input_query, OracleQuery.cont_query, QueryImpl.add_apply_inr,
          PFunctor.Handler.liftTarget_apply, QueryImpl.id'_apply, id_map]
        rw [← liftComp_eq_liftM, liftComp_liftM_query]
        rw [OracleComp.liftM_eq_liftM_liftM
          (superSpec := labSpec core + (List Byte →ₒ GeneralScheme.SignatureCore vp core))
          ((List Byte →ₒ GeneralScheme.SignatureCore vp core).query request)]
        simp only [OracleQuery.liftM_add_right_query]
    _ = _ := simulateQ_id' _

/-- Erasing markers recovers the complete lab transcript as a free oracle program. -/
theorem erase_markedLabExperiment
    {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist))
    (pkSeed : core.PkSeed) :
    simulateQ
      (SigningView.Events.handlerWithEvents (Request := List Byte)
        (QueryImpl.id' (labSpec core)))
      (markedLabExperiment core adv pkSeed) = labExperiment core adv pkSeed := by
  rw [markedLabExperiment, simulateQ_unforgeableTranscriptExperiment,
    erase_scheme, labExperiment]
  congr 1
  apply adversary_ext
  funext pk
  simpa only [UnforgeableAdversary.mapOracles_main] using erase_main core adv pkSeed pk

end Erasure

section Components
private def Quiet : (labSpec core).Domain → Prop
  | .inl (.inl (.inr (.inl (.hmsg _ _ _ _)))) => False
  | .inl (.inr (.inr _)) => False
  | _ => True

private abbrev QuietProgram {α : Type} (program : OracleComp (labSpec core) α) :=
  AllQueriesSatisfy program (Quiet core)

private theorem quiet_pure {α : Type} (a : α) : QuietProgram core (pure a) :=
  allQueriesSatisfy_pure _ _

private theorem quiet_bind {α β : Type} (a : OracleComp (labSpec core) α)
    (b : α → OracleComp (labSpec core) β) (ha : QuietProgram core a)
    (hb : ∀ x, QuietProgram core (b x)) : QuietProgram core (a >>= b) :=
  allQueriesSatisfy_bind ha hb

private theorem quiet_touch (cell : DeriveQuery core ⊕ NodeKey core) :
    QuietProgram core (touchCell (some cell)) :=
  (allQueriesSatisfy_query_iff _ _).mpr trivial

private def ConstructionCell : Option (DeriveQuery core ⊕ NodeKey core) → Prop
  | some (.inl (.inr _)) => False
  | _ => True

private theorem construction_child (address : Adrs ⊕ Adrs) :
    ConstructionCell core (childCell core address) := by
  rcases address with address | address
  · cases h : childCell core (.inl address) with
    | none => trivial
    | some cell =>
      obtain ⟨key, _, _, rfl⟩ := (childCell_inl_eq_some_iff core).mp h
      trivial
  · cases h : childCell core (.inr address) with
    | none => trivial
    | some cell =>
      obtain ⟨key, _, _, rfl⟩ := (childCell_inr_eq_some_iff core).mp h
      trivial

private theorem construction_path (secret : Adrs) (nodes : Nat → Adrs) (index : Nat) :
    ConstructionCell core (pathCell core secret nodes index) := by
  cases index with
  | zero => exact construction_child core (.inl secret)
  | succ n => exact construction_child core (.inr (nodes n))

variable [SampleableType core.Y]

private theorem quiet_read (cell : Option (DeriveQuery core ⊕ NodeKey core))
    (hcell : ConstructionCell core cell) : QuietProgram core (readCell cell) := by
  rcases cell with _ | ((secret | nonce) | node)
  · exact quiet_pure core _
  · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  · exact hcell.elim
  · exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem quiet_labNode (address : Adrs) : QuietProgram core (labNode core address) :=
  quiet_read core _ (construction_child core (.inr address))

private theorem quiet_labChain (address : Adrs) (index steps : Nat) :
    QuietProgram core (labChain core address index steps) :=
  quiet_bind core _ _
    (touchUpTo_pred (quiet_pure core) (quiet_bind core)
      (quiet_touch core) _ _) fun _ => quiet_read core _ (construction_path core _ _ _)

private theorem quiet_labForsLeaf (address : Adrs) (index : Nat) :
    QuietProgram core (labForsLeaf core address index) :=
  quiet_bind core _ _
    (touchUpTo_pred (quiet_pure core) (quiet_bind core)
      (quiet_touch core) _ _) fun _ => quiet_read core _ (construction_path core _ _ _)

private theorem quiet_labWotsPkGenTops (adrs
    : Adrs) : (QuietProgram core) (labWotsPkGenTops core adrs) :=
  Vector.ofFnM_pred (QuietProgram core)
    (quiet_pure core) (quiet_bind core) _ fun _ => quiet_labChain core _ _ _

private theorem quiet_labWotsSign (msg
    : core.Y) (adrs : Adrs) : (QuietProgram core) (labWotsSign core msg adrs) :=
  Vector.ofFnM_pred (QuietProgram core)
    (quiet_pure core) (quiet_bind core) _ fun _ => quiet_labChain core _ _ _

private theorem quiet_labXmssLeaf (adrs
    : Adrs) (t : ℕ) : (QuietProgram core) (labXmssLeaf core adrs t) :=
  (quiet_bind core) _ _ (quiet_labWotsPkGenTops core _) fun _ =>
    quiet_labNode core _

private theorem quiet_labXmssNode (adrs : Adrs) (z t : Nat) :
    QuietProgram core (labXmssNode core adrs z t) := by
  change QuietProgram core (PerfectMerkleTree.merkleRootM (labXmssLeaf core adrs)
    (xmssNodeHashWith (labH core) adrs) z t)
  exact PerfectMerkleTree.merkleRootM_pred_of_subtree
    (m := OracleComp (labSpec core)) (Y := core.Y)
    (QuietProgram core) (quiet_bind core) (labXmssLeaf core adrs)
    (xmssNodeHashWith (labH core) adrs) z t
    (fun index _ => quiet_labXmssLeaf core adrs index)
    (fun height index _ _ _ left right => by
      simpa only [xmssNodeHashWith, labH] using
        quiet_labNode core (xmssNodeAdrs adrs height index))

private theorem quiet_labXmssSign (msg : core.Y) (adrs : Adrs) (idx : Nat) :
    QuietProgram core (labXmssSign core msg adrs idx) := by
  rw [labXmssSign]
  refine quiet_bind core _ _ ?_ fun _ =>
    quiet_bind core _ _ (quiet_labWotsSign core msg _) fun _ => quiet_pure core _
  exact PerfectMerkleTree.intrinsicAuthPathM_pred_of_tree
    (m := OracleComp (labSpec core)) (Y := core.Y)
    (QuietProgram core) (quiet_pure core) (quiet_bind core)
    (labXmssLeaf core adrs) (xmssNodeHashWith (labH core) adrs) idx vp.params.hp
    (fun index _ => quiet_labXmssLeaf core adrs index)
    (fun height index _ _ _ left right => by
      simpa only [xmssNodeHashWith, labH] using
        quiet_labNode core (xmssNodeAdrs adrs height index))

private theorem quiet_labForsSign (md : List Byte) (adrs : Adrs) :
    QuietProgram core (labForsSign core md adrs) := by
  rw [labForsSign]
  apply Vector.ofFnM_pred (QuietProgram core) (quiet_pure core) (quiet_bind core)
  intro i
  let idx := i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val
  have secret : QuietProgram core (labSecret core (forsSkAdrs adrs idx)) := by
    rw [labSecret_of_isSecretKey core (Adrs.isSecretKey_forsSkAdrs adrs idx)]
    exact quiet_read core _ trivial
  refine quiet_bind core _ _ secret fun _ => quiet_bind core _ _ ?_ fun _ => quiet_pure core _
  exact PerfectMerkleTree.intrinsicAuthPathM_pred_of_tree
    (m := OracleComp (labSpec core)) (Y := core.Y)
    (QuietProgram core) (quiet_pure core) (quiet_bind core)
    (labForsLeaf core adrs) (forsNodeHashWith (labH core) adrs) idx vp.params.a
    (fun index _ => quiet_labForsLeaf core adrs index)
    (fun height index _ _ _ left right => by
      simpa only [forsNodeHashWith, labH] using
        quiet_labNode core (forsNodeAdrs adrs height index))

private theorem component_xmssRecovery
    (Q : ∀ {α : Type}, OracleComp (labSpec core) α → Prop)
    (hpure : ∀ {α : Type} (x : α), Q (pure x))
    (hbind : ∀ {α β : Type} (oa : OracleComp (labSpec core) α)
      (ob : α → OracleComp (labSpec core) β), Q oa → (∀ x, Q (ob x)) → Q (oa >>= ob))
    (hnode : ∀ a, Q (labNode core a))
    (idx : Nat) (sig : XmssSig vp.params core) (msg : core.Y) (adrs : Adrs) :
    Q (xmssPkFromSigWith core (labF core) (labTl core) (labH core) idx sig msg adrs) :=
  xmssPkFromSigWith_pred Q hpure hbind core
    (fun a _ _ => hnode a) (fun a _ _ => hnode a) (fun a _ _ _ => hnode a) idx sig msg adrs

private theorem component_forsRecovery
    (Q : ∀ {α : Type}, OracleComp (labSpec core) α → Prop)
    (hpure : ∀ {α : Type} (x : α), Q (pure x))
    (hbind : ∀ {α β : Type} (oa : OracleComp (labSpec core) α)
      (ob : α → OracleComp (labSpec core) β), Q oa → (∀ x, Q (ob x)) → Q (oa >>= ob))
    (hnode : ∀ a, Q (labNode core a))
    (sig : ForsSigCore vp.params core) (md : List Byte) (adrs : Adrs) :
    Q (forsPkFromSigWith core (labF core) (labH core) (labTl core) sig md adrs) :=
  forsPkFromSigWith_pred Q hpure hbind core
    (fun a _ _ => hnode a) (fun a _ _ => hnode a) (fun a _ _ _ => hnode a) sig md adrs

private theorem quiet_xmssRecovery (idx : Nat) (sig : XmssSig vp.params core)
    (msg : core.Y) (adrs : Adrs) :
    QuietProgram core (xmssPkFromSigWith core (labF core) (labTl core) (labH core)
      idx sig msg adrs) :=
  component_xmssRecovery core (QuietProgram core) (quiet_pure core) (quiet_bind core)
    (quiet_labNode core) idx sig msg adrs

private theorem quiet_forsRecovery (sig : ForsSigCore vp.params core) (md : List Byte)
    (adrs : Adrs) :
    QuietProgram core (forsPkFromSigWith core (labF core) (labH core) (labTl core)
      sig md adrs) :=
  component_forsRecovery core (QuietProgram core) (quiet_pure core) (quiet_bind core)
    (quiet_labNode core) sig md adrs

private theorem quiet_labSignFromPosition (recoverFinal : Bool) (pos : LayerPosition vp) :
    ∀ (layers : ℕ) (h : pos.layer.val + layers = vp.params.d) (msg : core.Y),
      QuietProgram core (labSignFromPosition core recoverFinal pos layers h msg)
  | 0, _, _ => quiet_pure core _
  | 1, _, msg => by
      rw [labSignFromPosition]
      refine quiet_bind core _ _ (quiet_labXmssSign core msg pos.toAdrs pos.leaf.val)
        fun sig => ?_
      cases recoverFinal
      · exact quiet_pure core _
      · exact quiet_bind core _ _
          (quiet_xmssRecovery core pos.leaf.val sig msg pos.toAdrs) fun _ => quiet_pure core _
  | layers + 2, _, msg => by
      rw [labSignFromPosition]
      exact quiet_bind core _ _ (quiet_labXmssSign core msg pos.toAdrs pos.leaf.val) fun sig =>
        quiet_bind core _ _ (quiet_xmssRecovery core pos.leaf.val sig msg pos.toAdrs) fun root =>
          quiet_bind core _ _ (quiet_labSignFromPosition false _ (layers + 1) _ root)
            fun _ => quiet_pure core _

private theorem quiet_labKeygen : QuietProgram core (labKeygen core) :=
  quiet_labXmssNode core _ _ _

private theorem quiet_labSignInternal_of_hmsg_bind (pkSeed : core.PkSeed) (msg : List Byte)
    (pkRoot R : core.Y)
    {P : OracleComp (labSpec core) (GeneralScheme.SignatureCore vp core) → Prop}
    (hmsg : ∀ ob, (∀ x, QuietProgram core (ob x)) →
      P ((PublicHash.hmsg core R pkSeed pkRoot msg : OracleComp (labSpec core) _) >>= ob)) :
    P (labSignInternal core pkSeed msg pkRoot R) :=
  hmsg _ fun _ =>
    quiet_bind core _ _ (quiet_labForsSign core _ _) fun sig =>
      quiet_bind core _ _ (quiet_forsRecovery core sig _ _) fun _ =>
        quiet_bind core _ _ (quiet_labSignFromPosition core _ _ _ _ _) fun _ =>
          quiet_pure core _

end Components

section Native
private def Allowed (pk : PublicKeyCore core) (kappa : PublicKeyCore core → core.Y)
    (pkSeed : core.PkSeed) (sk : PublicKeyCore core) (phase : SigningView.Phase) :
    (labSpec core).Domain → Prop
  | .inl (.inl (.inr (.inl (.hmsg _ seed root _)))) =>
      CoverageDeferred.phaseRole phase = .signer → seed = pkSeed ∧ root = sk.pkRoot
  | .inl (.inr (.inr (salt, _))) =>
      CoverageDeferred.phaseRole phase = .signer ∧ salt = kappa pk
  | _ => True

private abbrev Target (pk : PublicKeyCore core) (kappa : PublicKeyCore core → core.Y)
    (pkSeed : core.PkSeed) (sk : PublicKeyCore core) :=
  fun input => Coverage.NativeThin1.GoodQuery core pk kappa input ∧
    SuffixShape core pkSeed sk input

private theorem uniform_safe {α : Type} (body : ProbComp α)
    (pk : PublicKeyCore core) (kappa : PublicKeyCore core → core.Y)
    (pkSeed : core.PkSeed) (sk : PublicKeyCore core) :
    AllQueriesSatisfy (CoverageDeferred.privateUniform core body)
      (Target core pk kappa pkSeed sk) := by
  unfold CoverageDeferred.privateUniform
  induction body using OracleComp.inductionOn with
  | pure x => exact allQueriesSatisfy_pure _ _
  | query_bind n k ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr ⟨trivial, trivial⟩) ih

variable [SampleableType core.Y] [DecidableEq core.Y]
variable [SampleableType (Bytes vp.params.m)]
variable [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

private theorem other_safe (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed) (sk : PublicKeyCore core)
    (policy : SigningView.Event (labSpec core) (List Byte) → Nat)
    (input : (labSpec core).Domain) (h : ¬CoverageDeferred.IsSelectedNative core input)
    (state : CoverageDeferred.S core) :
    AllQueriesSatisfy ((CoverageDeferred.relative core pkSeed policy (.inl input)).run state)
      (Target core pk kappa pkSeed sk) := by
  rw [CoverageDeferred.relative_other core pkSeed policy input h state]
  exact allQueriesSatisfy_bind (uniform_safe core _ pk kappa pkSeed sk)
    fun _ => allQueriesSatisfy_pure _ _

private theorem native_safe (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed) (sk : PublicKeyCore core)
    (policy : SigningView.Event (labSpec core) (List Byte) → Nat)
    (phase : SigningView.Phase) (input : (labSpec core).Domain)
    (h : Allowed core pk kappa pkSeed sk phase input)
    (graph : CoverageDeferred.D core) (cost : Nat) :
    AllQueriesSatisfy
      ((CoverageDeferred.relative core pkSeed policy (.inl input)).run (graph, cost, phase))
      (Target core pk kappa pkSeed sk) := by
  rcases input with (((n | (hash | prf)) | (secret | nonce)) | (touch | read))
  · exact other_safe core pk kappa pkSeed sk policy _
      (by simp [CoverageDeferred.IsSelectedNative]) _
  · cases hash with
    | thash seed address values =>
        exact other_safe core pk kappa pkSeed sk policy _
          (by simp [CoverageDeferred.IsSelectedNative]) _
    | hmsg R seed root message =>
        rw [CoverageDeferred.relative_hmsg]
        apply allQueriesSatisfy_bind
        · cases phase <;> simp_all [Coverage.roleImpl, CoverageDeferred.phaseRole, Target,
            Coverage.NativeThin1.GoodQuery, Coverage.NativeThin1.GoodPoint, SuffixShape,
            Allowed]
        · intro digest
          exact allQueriesSatisfy_pure _ _
  · exact other_safe core pk kappa pkSeed sk policy _
      (by simp [CoverageDeferred.IsSelectedNative]) _
  · exact other_safe core pk kappa pkSeed sk policy _
      (by simp [CoverageDeferred.IsSelectedNative]) _
  · rcases nonce with ⟨salt, message⟩
    rw [CoverageDeferred.relative_rand, map_eq_bind_pure_comp]
    apply allQueriesSatisfy_bind
    · cases phase <;> simp_all [Coverage.roleImpl, CoverageDeferred.phaseRole, Target,
        Coverage.NativeThin1.GoodQuery, Coverage.NativeThin1.GoodPoint, SuffixShape,
        Allowed]
    · intro R
      exact allQueriesSatisfy_pure _ _
  · exact other_safe core pk kappa pkSeed sk policy _
      (by simp [CoverageDeferred.IsSelectedNative]) _
  · exact other_safe core pk kappa pkSeed sk policy _
      (by simp [CoverageDeferred.IsSelectedNative]) _

private theorem atomic_safe (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed) (sk : PublicKeyCore core)
    (policy : SigningView.Event (labSpec core) (List Byte) → Nat)
    (phase : SigningView.Phase) (input : (labSpec core).Domain)
    (h : Allowed core pk kappa pkSeed sk phase input) (state : CoverageDeferred.S core) :
    AllQueriesSatisfy
      ((simulateQ (CoverageDeferred.relative core pkSeed policy)
        (SigningView.Events.phaseImpl (labSpec core) (List Byte) phase input)).run state)
      (Target core pk kappa pkSeed sk) := by
  simp only [SigningView.Events.phaseImpl, QueryImpl.preInsert_apply, monadLift_self,
    SigningView.Events.emit, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [CoverageDeferred.relative_marker]
  simpa only [pure_bind, CoverageDeferred.phaseCostAux] using
    native_safe core pk kappa pkSeed sk policy phase input h state.1
      (state.2.1 + policy (.ambient phase input))


private theorem phase_safe {α : Type} (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed) (sk : PublicKeyCore core)
    (policy : SigningView.Event (labSpec core) (List Byte) → Nat)
    (phase : SigningView.Phase) (body : OracleComp (labSpec core) α)
    (h : AllQueriesSatisfy body (Allowed core pk kappa pkSeed sk phase))
    (state : CoverageDeferred.S core) :
    AllQueriesSatisfy
      ((simulateQ (CoverageDeferred.relative core pkSeed policy)
        (simulateQ (SigningView.Events.phaseImpl (labSpec core) (List Byte) phase) body)).run state)
      (Target core pk kappa pkSeed sk) := by
  rw [← QueryImpl.simulateQ_compose]
  exact h.simulateQ_run (fun input hi s => atomic_safe core pk kappa pkSeed sk policy
    phase input hi s) state

omit [SampleableType core.Y] [DecidableEq core.Y] [SampleableType (Bytes vp.params.m)]
  [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf] in
private theorem quiet_allowed (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed) (sk : PublicKeyCore core)
    (phase : SigningView.Phase) (input : (labSpec core).Domain) (h : Quiet core input) :
    Allowed core pk kappa pkSeed sk phase input := by
  rcases input with (((n | (hash | prf)) | (secret | nonce)) | (touch | read))
  all_goals first | cases hash <;> simp_all [Quiet, Allowed] | simp_all [Quiet, Allowed]

private theorem marker_safe (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed) (sk : PublicKeyCore core)
    (policy : SigningView.Event (labSpec core) (List Byte) → Nat)
    (event : SigningView.Event (labSpec core) (List Byte)) (state : CoverageDeferred.S core) :
    AllQueriesSatisfy
      ((simulateQ (CoverageDeferred.relative core pkSeed policy)
        (SigningView.Events.emit (labSpec core) (List Byte) event)).run state)
      (Target core pk kappa pkSeed sk) := by
  simp only [SigningView.Events.emit, simulateQ_spec_query]
  exact allQueriesSatisfy_pure _ _

private theorem signer_safe (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed) (sk : PublicKeyCore core)
    (policy : SigningView.Event (labSpec core) (List Byte) → Nat)
    (msg : List Byte) (state : CoverageDeferred.S core) :
    AllQueriesSatisfy
      ((simulateQ (CoverageDeferred.relative core pkSeed policy)
        ((markedLabScheme core (fun pk => pure (kappa pk)) pkSeed).sign pk sk msg)).run state)
      (Target core pk kappa pkSeed sk) := by
  have hs : AllQueriesSatisfy
      ((labScheme core (fun pk => pure (kappa pk)) pkSeed).sign pk sk msg)
      (Allowed core pk kappa pkSeed sk .signer) := by
    simp only [labScheme, liftM_pure, pure_bind]
    apply allQueriesSatisfy_bind
    · exact (allQueriesSatisfy_query_iff _ _).mpr (by
        simp [Allowed, CoverageDeferred.phaseRole])
    · intro R
      apply quiet_labSignInternal_of_hmsg_bind core pkSeed msg sk.pkRoot R
        (P := fun body => AllQueriesSatisfy body (Allowed core pk kappa pkSeed sk .signer))
      intro ob hob
      apply allQueriesSatisfy_bind
      · exact (allQueriesSatisfy_query_iff _ _).mpr (by
          simp [Allowed, CoverageDeferred.phaseRole])
      · exact fun x => (hob x).mono (quiet_allowed core pk kappa pkSeed sk .signer)
  simp only [markedLabScheme, simulateQ_bind, StateT.run_bind]
  exact allQueriesSatisfy_bind (marker_safe core pk kappa pkSeed sk policy _ state)
    fun z => phase_safe core pk kappa pkSeed sk policy .signer _ hs z.2

variable (pk : PublicKeyCore core) (kappa : PublicKeyCore core → core.Y)
  (pkSeed : core.PkSeed) (sk : PublicKeyCore core)
  (policy : SigningView.Event (labSpec core) (List Byte) → Nat)

private theorem logged_safe {α : Type}
    (red : QueryImpl (labSpec core + (List Byte →ₒ GeneralScheme.SignatureCore vp core))
      (WriterT (QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core))
        (OracleComp (SigningView.Events.Spec (labSpec core) (List Byte)))))
    (body : OracleComp (labSpec core + (List Byte →ₒ GeneralScheme.SignatureCore vp core)) α)
    (h : AllQueriesSatisfy body (Sum.elim (IsAmbientLabQuery core) fun _ => True))
    (step : ∀ input, (Sum.elim (IsAmbientLabQuery core) fun _ => True) input →
      ∀ state, AllQueriesSatisfy
        ((simulateQ (CoverageDeferred.relative core pkSeed policy) (red input).run).run state)
        (Target core pk kappa pkSeed sk)) (state : CoverageDeferred.S core) :
    AllQueriesSatisfy
      ((simulateQ (CoverageDeferred.relative core pkSeed policy)
        (simulateQ red body).run).run state)
      (Target core pk kappa pkSeed sk) := by
  induction body using OracleComp.inductionOn generalizing state with
  | pure x => simp
  | query_bind input k ih =>
      obtain ⟨hi, hk⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind', StateT.run_bind]
      apply allQueriesSatisfy_bind (step input hi state)
      intro z
      rw [simulateQ_map, StateT.run_map, map_eq_bind_pure_comp]
      exact allQueriesSatisfy_bind (ih z.1.1 (hk z.1.1) z.2)
        fun _ => allQueriesSatisfy_pure _ _

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

private theorem callback_safe (e : core.SkSeed ≃ core.Y)
    (adv : UnforgeableAdversary
      (romScheme core e (fun pk => pure (kappa pk)) (pure pkSeed)))
    (state : CoverageDeferred.S core) :
    AllQueriesSatisfy
      ((simulateQ (CoverageDeferred.relative core pkSeed policy)
        ((markedLabScheme core (fun pk => pure (kappa pk)) pkSeed).runWithSigningOracle pk sk
          ((markedLabAdversary core adv pkSeed).main pk))).run state)
      (Target core pk kappa pkSeed sk) := by
  let alg := markedLabScheme core (fun pk => pure (kappa pk)) pkSeed
  let red : QueryImpl (labSpec core + (List Byte →ₒ GeneralScheme.SignatureCore vp core))
      (WriterT (QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core))
        (OracleComp (SigningView.Events.Spec (labSpec core) (List Byte)))) :=
    ((SigningView.Events.Spec (labSpec core) (List Byte)).passthrough +
      alg.signingOracle pk sk) ∘ₛ
        QueryImpl.add
          (fun input => simulateQ
            (fun native => liftM
              ((SigningView.Events.Spec (labSpec core) (List Byte) +
                (List Byte →ₒ GeneralScheme.SignatureCore vp core)).query (.inl native)))
            (SigningView.Events.phaseImpl (labSpec core) (List Byte) .adversary input))
          (fun request => liftM
            ((SigningView.Events.Spec (labSpec core) (List Byte) +
              (List Byte →ₒ GeneralScheme.SignatureCore vp core)).query (.inr request)))
  simp only [markedLabAdversary, runWithSigningOracle, SigningView.Events.mainWithEvents]
  rw [← QueryImpl.simulateQ_compose]
  change AllQueriesSatisfy
    ((simulateQ (CoverageDeferred.relative core pkSeed policy)
      (simulateQ red ((labAdversary core adv pkSeed).main pk)).run).run state) _
  apply logged_safe core pk kappa pkSeed sk policy red _
    (allQueriesSatisfy_labAdversary_main (core := core) adv pk)
  intro input hi initial
  cases input with
  | inl input =>
      have step : (red (.inl input)).run =
          (fun answer => (answer, [])) <$>
            SigningView.Events.phaseImpl (labSpec core) (List Byte) .adversary input := by
        simp only [red, QueryImpl.apply_compose, QueryImpl.add]
        have h : simulateQ
            ((SigningView.Events.Spec (labSpec core) (List Byte)).passthrough +
              alg.signingOracle pk sk)
            (simulateQ (fun native => liftM
              ((SigningView.Events.Spec (labSpec core) (List Byte) +
                (List Byte →ₒ GeneralScheme.SignatureCore vp core)).query (.inl native)))
              (SigningView.Events.phaseImpl (labSpec core) (List Byte) .adversary input)) =
            simulateQ ((QueryImpl.id'
              (SigningView.Events.Spec (labSpec core) (List Byte))).liftTarget
              (WriterT (QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core))
                (OracleComp (SigningView.Events.Spec (labSpec core) (List Byte)))))
              (SigningView.Events.phaseImpl (labSpec core) (List Byte) .adversary input) := by
          apply QueryImpl.simulateQ_simulateQ_eq_of_apply
          intro native
          simp only [simulateQ_spec_query, QueryImpl.passthrough_add, QueryImpl.add_apply_inl]
        rw [h, writerT_run_simulateQ_liftTarget, simulateQ_id']
        rfl
      rw [step, simulateQ_map, StateT.run_map, map_eq_bind_pure_comp]
      apply allQueriesSatisfy_bind
      · apply atomic_safe core pk kappa pkSeed sk policy .adversary input _ initial
        rcases input with (((n | (hash | prf)) | (secret | nonce)) | (touch | read))
        all_goals first | cases hash <;> simp_all [Allowed, IsAmbientLabQuery,
          CoverageDeferred.phaseRole] | simp_all [Allowed, IsAmbientLabQuery]
      · intro z
        exact allQueriesSatisfy_pure _ _
  | inr request =>
      have step : (red (.inr request)).run =
          (fun answer => (answer, [⟨request, answer⟩])) <$> alg.sign pk sk request := by
        simp [red, QueryImpl.add, signingOracle, QueryImpl.withLogging_apply]
      rw [step, simulateQ_map, StateT.run_map, map_eq_bind_pure_comp]
      exact allQueriesSatisfy_bind (signer_safe core pk kappa pkSeed sk policy request initial)
        fun _ => allQueriesSatisfy_pure _ _

/-- The actual marked continuation uses only correctly salted native queries and signer keys. -/
theorem allQueriesSatisfy_relative_markedLabSuffix
    (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed)
    (e : core.SkSeed ≃ core.Y)
    (adv : UnforgeableAdversary
      (romScheme core e (fun pk => pure (kappa pk)) (pure pkSeed)))
    (pk sk : PublicKeyCore core)
    (policy : SigningView.Event (labSpec core) (List Byte) → Nat)
    (initial : CoverageDeferred.S core) :
    AllQueriesSatisfy
      ((simulateQ (CoverageDeferred.relative core pkSeed policy)
        (markedLabSuffix core kappa pkSeed e adv pk sk)).run initial)
      (fun input => Coverage.NativeThin1.GoodQuery core pk kappa input ∧
        SuffixShape core pkSeed sk input) := by
  simp only [markedLabSuffix, simulateQ_bind, StateT.run_bind]
  apply allQueriesSatisfy_bind (callback_safe core pk kappa pkSeed sk policy e adv initial)
  intro z
  apply allQueriesSatisfy_bind
  · apply phase_safe core pk kappa pkSeed sk policy .verification _ _ z.2
    apply (allQueriesSatisfy_labScheme_verify (core := core)
      (fun pk => pure (kappa pk)) pk _ _).mono
    intro input hi
    rcases input with (((n | (hash | prf)) | (secret | nonce)) | (touch | read))
    all_goals first | cases hash <;> simp_all [Allowed, IsAmbientLabQuery,
      CoverageDeferred.phaseRole] | simp_all [Allowed, IsAmbientLabQuery]
  · intro result
    exact allQueriesSatisfy_pure _ _

#print axioms erase_markedLabExperiment
#print axioms allQueriesSatisfy_relative_markedLabSuffix
end Native

section Counts
variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)]
  [DecidableEq core.Y] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]
  [DecidableEq core.SkPrf]

private theorem native_cnt_step
    (input : (Coverage.roleSpec core).Domain) (state : Coverage.RoleState core)
    (result : (Coverage.roleSpec core).Range input × Coverage.RoleState core)
    (hr : result ∈ support ((Coverage.roleRunImpl core input).run state))
    (j : Coverage.TapeClass) :
    result.2.2.1.cnt j = state.2.1.cnt j +
      if AnswerTape.classOf (Coverage.tapeClass core) input = some j then 1 else 0 := by
  obtain ⟨_, haux⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ input state result).mp hr
  rw [congrArg (fun p => p.1.cnt j) haux]
  rcases input with n | t
  · simp [AnswerTape.classPosAuxFwd, AnswerTape.classOf]
  · have hstep : ∀ (k : Coverage.TapeClass) (t : (Coverage.jointSpec core).Domain) s u s'
        (p : AnswerTape.ClassPos (Coverage.jointSpec core).Domain Coverage.TapeClass),
        (AnswerTape.classPosStep (Coverage.tapeClassRange core) k t s u s' p).cnt =
          Function.update p.cnt k (p.cnt k + 1) := by
      intro k t s u s' p
      unfold AnswerTape.classPosStep
      split <;> rfl
    have hcnt : (AnswerTape.classPosAuxFwd (Coverage.tapeClassRange core)
        (Coverage.tapeClass core) (.inr t) state.1 result.1 result.2.1 state.2.1).cnt =
        Function.update state.2.1.cnt (Coverage.tapeClass core t)
          (state.2.1.cnt (Coverage.tapeClass core t) + 1) := by
      rcases t with t | t <;> exact hstep _ t state.1 result.1 result.2.1 state.2.1
    rw [hcnt]
    by_cases hj : Coverage.tapeClass core t = j
    · subst j; simp [AnswerTape.classOf]
    · simp [AnswerTape.classOf, hj, Function.update_of_ne (Ne.symm hj)]

private theorem native_cnt_le {α : Type} (program : OracleComp (Coverage.roleSpec core) α)
    (j : Coverage.TapeClass) {n : Nat}
    (hb : IsQueryBoundP program
      (fun input => AnswerTape.classOf (Coverage.tapeClass core) input = some j) n)
    (initial : Coverage.RoleState core) (result : α × Coverage.RoleState core)
    (hr : result ∈ support ((simulateQ (Coverage.roleRunImpl core) program).run initial)) :
    result.2.2.1.cnt j ≤ initial.2.1.cnt j + n := by
  apply hb.cost_le_of_mem_support_run_simulateQ (fun s => s.2.1.cnt j) _ _ initial result hr
  · intro input hi state result hr
    exact (by simpa [hi] using (native_cnt_step core input state result hr j).le)
  · intro input hi state result hr
    exact (by simpa [hi] using (native_cnt_step core input state result hr j).le)

omit [SampleableType core.Y] [SampleableType (Bytes vp.params.m)]
  [DecidableEq core.Y] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]
  [DecidableEq core.SkPrf] in
private theorem uniform_hmsg_bound {α : Type} (program : ProbComp α)
    (j : Coverage.TapeClass) :
    IsQueryBoundP (CoverageDeferred.privateUniform core program)
      (fun input => AnswerTape.classOf (Coverage.tapeClass core) input = some j) 0 := by
  induction program using OracleComp.inductionOn with
  | pure x => simp [CoverageDeferred.privateUniform]
  | query_bind n k ih =>
      rw [CoverageDeferred.privateUniform, simulateQ_bind, simulateQ_spec_query]
      exact isQueryBoundP_bind (n := 0) (m := 0)
        ((isQueryBoundP_query_iff _ _ _).mpr (by simp [AnswerTape.classOf]))
        (fun x _ => ih x)

private def activeClass : SigningView.Phase → Coverage.TapeClass
  | .keygen | .signer => .signer
  | .adversary | .verification => .forger

private theorem other_hmsg_bound (pkSeed : core.PkSeed)
    (input : (labSpec core).Domain) (hi : ¬ CoverageDeferred.IsSelectedNative core input)
    (state : CoverageDeferred.S core) (j : Coverage.TapeClass) :
    IsQueryBoundP ((CoverageDeferred.relative core pkSeed
      (fun _ : SigningView.Event (labSpec core) (List Byte) => 0) (.inl input)).run state)
      (fun input => AnswerTape.classOf (Coverage.tapeClass core) input = some j) 0 := by
  rw [CoverageDeferred.relative_other core pkSeed (fun _ => 0) input hi state]
  exact isQueryBoundP_bind (uniform_hmsg_bound core _ j)
    (fun _ _ => isQueryBoundP_pure _ _ 0)

private theorem relative_hmsg_bound (pkSeed : core.PkSeed)
    (input : (labSpec core).Domain) (state : CoverageDeferred.S core)
    (j : Coverage.TapeClass) (hj : j ≠ .other) :
    IsQueryBoundP ((CoverageDeferred.relative core pkSeed
      (fun _ : SigningView.Event (labSpec core) (List Byte) => 0) (.inl input)).run state)
      (fun input => AnswerTape.classOf (Coverage.tapeClass core) input = some j)
      (if IsPublicLabQuery core input ∧ j = activeClass state.2.2 then 1 else 0) := by
  rcases input with (((n | (hash | prf)) | (secret | nonce)) | (touch | read))
  · exact (other_hmsg_bound core pkSeed _ (by simp [CoverageDeferred.IsSelectedNative])
      state j).mono (Nat.zero_le _)
  · cases hash with
    | thash seed address values =>
        exact (other_hmsg_bound core pkSeed _
          (by simp [CoverageDeferred.IsSelectedNative]) state j).mono (Nat.zero_le _)
    | hmsg R seed root message =>
        rw [CoverageDeferred.relative_hmsg]
        rcases state with ⟨graph, cost, phase⟩
        cases phase <;> cases j <;>
          simp_all [CoverageDeferred.phaseRole, Coverage.roleImpl, activeClass,
            IsPublicLabQuery, Coverage.tapeClass, AnswerTape.classOf,
            isQueryBoundP_query_iff]
  · exact (other_hmsg_bound core pkSeed _ (by simp [CoverageDeferred.IsSelectedNative])
      state j).mono (Nat.zero_le _)
  · exact (other_hmsg_bound core pkSeed _ (by simp [CoverageDeferred.IsSelectedNative])
      state j).mono (Nat.zero_le _)
  · rcases nonce with ⟨salt, message⟩
    rw [CoverageDeferred.relative_rand]
    rcases state with ⟨graph, cost, phase⟩
    cases phase <;> cases j <;>
      simp_all [CoverageDeferred.phaseRole, Coverage.roleImpl, activeClass,
        IsPublicLabQuery, Coverage.tapeClass, AnswerTape.classOf, isQueryBoundP_query_iff]
  · exact (other_hmsg_bound core pkSeed _ (by simp [CoverageDeferred.IsSelectedNative])
      state j).mono (Nat.zero_le _)
  · exact (other_hmsg_bound core pkSeed _ (by simp [CoverageDeferred.IsSelectedNative])
      state j).mono (Nat.zero_le _)

private noncomputable abbrev nativeRelative (pkSeed : core.PkSeed) :=
  ((Coverage.roleRunImpl core).mapStateTBase
    (CoverageDeferred.relative core pkSeed
      (fun _ : SigningView.Event (labSpec core) (List Byte) => 0))).flattenStateT

private theorem nativeRelative_cnt (pkSeed : core.PkSeed) (input : (labSpec core).Domain)
    (state : CoverageDeferred.S core × Coverage.RoleState core)
    (result : (labSpec core).Range input ×
      (CoverageDeferred.S core × Coverage.RoleState core))
    (hr : result ∈ support ((nativeRelative core pkSeed (.inl input)).run state))
    (j : Coverage.TapeClass) (hj : j ≠ .other) :
    result.2.2.2.1.cnt j ≤ state.2.2.1.cnt j +
      if IsPublicLabQuery core input ∧ j = activeClass state.1.2.2 then 1 else 0 := by
  rw [nativeRelative, QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at hr
  obtain ⟨out, hout, rfl⟩ := hr
  exact native_cnt_le core _ j (relative_hmsg_bound core pkSeed input state.1 j hj)
    state.2 out hout

private noncomputable def baseWork : SigningView.Event (labSpec core) (List Byte) → Nat
  | .signingAttempt _ => 1
  | .ambient .adversary input | .ambient .verification input =>
      if IsPublicLabQuery core input then 1 else 0
  | _ => 0

private noncomputable def sourcePolicy (extra : SigningView.Event (labSpec core) (List Byte) → Nat)
    (event : SigningView.Event (labSpec core) (List Byte)) : Nat × Nat :=
  (baseWork core event + extra event, match event with | .signingAttempt _ => 1 | _ => 0)

private noncomputable abbrev controlled (pkSeed : core.PkSeed) (caps : Nat × Nat)
    (extra : SigningView.Event (labSpec core) (List Byte) → Nat)
    (fallback : (input : (SigningView.Events.Spec (labSpec core) (List Byte)).Domain) →
      (SigningView.Events.Spec (labSpec core) (List Byte)).Range input) :=
  QueryImpl.guardQueryBudget caps (Sum.elim (fun _ => (0, 0)) (sourcePolicy core extra))
    (nativeRelative core pkSeed) fallback

private theorem nativeRelative_marker (pkSeed : core.PkSeed)
    (event : SigningView.Event (labSpec core) (List Byte))
    (state : CoverageDeferred.S core × Coverage.RoleState core) :
    (nativeRelative core pkSeed (.inr event)).run state =
      pure (⟨⟩, ((state.1.1,
        CoverageDeferred.phaseCostAux core
          (fun _ : SigningView.Event (labSpec core) (List Byte) => 0) (.inr event)
          state.1.1 ⟨⟩ state.1.1 state.1.2), state.2)) := by
  rw [nativeRelative, QueryImpl.flattenStateT_mapStateTBase_apply_run,
    CoverageDeferred.relative_marker]
  simp

private theorem controlled_aborted (pkSeed : core.PkSeed) (caps : Nat × Nat)
    (extra : SigningView.Event (labSpec core) (List Byte) → Nat)
    (fallback : (input : (SigningView.Events.Spec (labSpec core) (List Byte)).Domain) →
      (SigningView.Events.Spec (labSpec core) (List Byte)).Range input)
    {α : Type} (program : OracleComp (SigningView.Events.Spec (labSpec core) (List Byte)) α)
    (initial : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool))
    (hi : initial.2.2 = true) (result : α ×
      ((CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool)))
    (hr : result ∈ support
      ((simulateQ (controlled core pkSeed caps extra fallback) program).run initial)) :
    result.2 = initial := by
  apply simulateQ_run_preservesInv (controlled core pkSeed caps extra fallback)
    (fun state => state = initial) _ program initial rfl result hr
  intro input state hs output hout
  subst state
  have heq : output = (fallback input, initial) := by
    simpa [controlled, QueryImpl.guardQueryBudget, hi] using hout
  exact congrArg Prod.snd heq

private theorem phase_step (pkSeed : core.PkSeed) (caps : Nat × Nat)
    (extra : SigningView.Event (labSpec core) (List Byte) → Nat)
    (fallback : (input : (SigningView.Events.Spec (labSpec core) (List Byte)).Domain) →
      (SigningView.Events.Spec (labSpec core) (List Byte)).Range input)
    (phase : SigningView.Phase) (input : (labSpec core).Domain)
    (state : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool))
    (result : (labSpec core).Range input ×
      ((CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool)))
    (hr : result ∈ support ((simulateQ (controlled core pkSeed caps extra fallback)
      (SigningView.Events.phaseImpl (labSpec core) (List Byte) phase input)).run state)) :
    result.2.2.1.2 = state.2.1.2 ∧
    result.2.1.2.2.1.cnt .signer ≤ state.1.2.2.1.cnt .signer +
      (if IsPublicLabQuery core input ∧ .signer = activeClass phase then 1 else 0) ∧
    result.2.1.2.2.1.cnt .forger + state.2.1.1 ≤
      state.1.2.2.1.cnt .forger + result.2.2.1.1 := by
  simp only [SigningView.Events.phaseImpl, QueryImpl.preInsert_apply, monadLift_self,
    SigningView.Events.emit, simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨middle, hm, hr⟩ := hr
  simp only [controlled, QueryImpl.guardQueryBudget, StateT.run_mk] at hm
  split_ifs at hm with hflag hcap
  · have heq : middle = (fallback (.inr (.ambient phase input)), state) := by
      simpa only [support_pure, Set.mem_singleton_iff] using hm
    subst middle
    have heq : result = (fallback (.inl input), state) := by
      simpa [controlled, QueryImpl.guardQueryBudget, hflag] using hr
    subst result
    dsimp only
    omega
  · rw [nativeRelative_marker] at hm
    simp only [map_pure, support_pure, Set.mem_singleton_iff] at hm
    subst middle
    have hcost : (Sum.elim (fun _ => (0, 0)) (sourcePolicy core extra))
        (.inl input) = (0, 0) := rfl
    simp only [controlled, QueryImpl.guardQueryBudget, StateT.run_mk, hcost,
      Sum.elim_inr, Bool.false_eq_true, ↓reduceIte] at hr
    simp only [Prod.mk_zero_zero, add_zero, Prod.le_def, Prod.fst_add, Prod.snd_add] at hr
    have hcap' : state.2.1.1 + (sourcePolicy core extra (.ambient phase input)).1 ≤ caps.1 ∧
        state.2.1.2 + (sourcePolicy core extra (.ambient phase input)).2 ≤ caps.2 := by
      simpa only [Sum.elim_inr, Prod.le_def, Prod.fst_add, Prod.snd_add] using hcap
    rw [ite_eq_left hcap', support_map] at hr
    obtain ⟨out, hout, rfl⟩ := hr
    have hc := nativeRelative_cnt core pkSeed input
      ((state.1.1.1,
        CoverageDeferred.phaseCostAux core
          (fun _ : SigningView.Event (labSpec core) (List Byte) => 0) (.inr (.ambient phase input))
          state.1.1.1 ⟨⟩ state.1.1.1 state.1.1.2), state.1.2) out hout
      .signer (by decide)
    have hm := nativeRelative_cnt core pkSeed input
      ((state.1.1.1,
        CoverageDeferred.phaseCostAux core
          (fun _ : SigningView.Event (labSpec core) (List Byte) => 0) (.inr (.ambient phase input))
          state.1.1.1 ⟨⟩ state.1.1.1 state.1.1.2), state.1.2) out hout
      .forger (by decide)
    simp only [CoverageDeferred.phaseCostAux, Nat.add_zero] at hc hm
    constructor
    · simp [sourcePolicy]
    constructor
    · exact hc
    · by_cases hp : IsPublicLabQuery core input <;> cases phase <;>
        simp [sourcePolicy, baseWork, activeClass, hp, Prod.fst_add] at hm ⊢ <;> omega
  · have heq : middle = (fallback (.inr (.ambient phase input)),
        (state.1, (state.2.1, true))) := by
      simpa only [support_pure, Set.mem_singleton_iff] using hm
    subst middle
    have heq : result = (fallback (.inl input), (state.1, (state.2.1, true))) := by
      simpa [controlled, QueryImpl.guardQueryBudget] using hr
    subst result
    dsimp only
    omega

variable (pkSeed : core.PkSeed) (caps : Nat × Nat)
  (extra : SigningView.Event (labSpec core) (List Byte) → Nat)
  (fallback : (input : (SigningView.Events.Spec (labSpec core) (List Byte)).Domain) →
    (SigningView.Events.Spec (labSpec core) (List Byte)).Range input)

private def sourceInv
    (state : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool)) : Prop :=
  state.1.2.2.1.cnt .signer ≤ state.2.1.2 ∧
    state.2.1.2 + state.1.2.2.1.cnt .forger ≤ state.2.1.1

private theorem phase_work {α : Type} (phase : SigningView.Phase)
    (program : OracleComp (labSpec core) α)
    (state : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool))
    (hR : state.2.1.2 + state.1.2.2.1.cnt .forger ≤ state.2.1.1)
    (result : α × ((CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool)))
    (hr : result ∈ support ((simulateQ (controlled core pkSeed caps extra fallback)
      (simulateQ (SigningView.Events.phaseImpl (labSpec core) (List Byte) phase)
        program)).run state)) :
    result.2.2.1.2 = state.2.1.2 ∧
      result.2.2.1.2 + result.2.1.2.2.1.cnt .forger ≤ result.2.2.1.1 := by
  let P := fun s : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool) =>
    s.2.1.2 = state.2.1.2 ∧ s.2.1.2 + s.1.2.2.1.cnt .forger ≤ s.2.1.1
  rw [← QueryImpl.simulateQ_compose] at hr
  apply simulateQ_run_preservesInv _ P _ program state ⟨rfl, hR⟩ result hr
  intro input before hb out hout
  have hs := phase_step core pkSeed caps extra fallback phase input before out hout
  dsimp only [P] at hb ⊢
  exact ⟨hs.1.trans hb.1, by omega⟩

private theorem phase_cnt_le {α : Type} (phase : SigningView.Phase)
    (program : OracleComp (labSpec core) α) {n : Nat}
    (hb : IsQueryBoundP program (IsPublicLabQuery core) n)
    (state : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool))
    (result : α × ((CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool)))
    (hr : result ∈ support ((simulateQ (controlled core pkSeed caps extra fallback)
      (simulateQ (SigningView.Events.phaseImpl (labSpec core) (List Byte) phase)
        program)).run state)) :
    result.2.1.2.2.1.cnt .signer ≤ state.1.2.2.1.cnt .signer + n := by
  rw [← QueryImpl.simulateQ_compose] at hr
  apply hb.cost_le_of_mem_support_run_simulateQ (fun s => s.1.2.2.1.cnt .signer) _ _
    state result hr
  · intro input hi before out hout
    have hs := (phase_step core pkSeed caps extra fallback phase input before out hout).2.1
    split_ifs at hs <;> omega
  · intro input hi before out hout
    simpa [hi] using
      (phase_step core pkSeed caps extra fallback phase input before out hout).2.1

private theorem phase_forger {α : Type} (phase : SigningView.Phase)
    (hp : activeClass phase = .forger) (program : OracleComp (labSpec core) α)
    (state : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool))
    (hI : sourceInv core state)
    (result : α × ((CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool)))
    (hr : result ∈ support ((simulateQ (controlled core pkSeed caps extra fallback)
      (simulateQ (SigningView.Events.phaseImpl (labSpec core) (List Byte) phase)
        program)).run state)) :
    sourceInv core result.2 := by
  rw [← QueryImpl.simulateQ_compose] at hr
  apply simulateQ_run_preservesInv _ (sourceInv core) _ program state hI result hr
  intro input before hb out hout
  have hs := phase_step core pkSeed caps extra fallback phase input before out hout
  have hc : out.2.1.2.2.1.cnt .signer ≤ before.1.2.2.1.cnt .signer := by
    simpa [hp] using hs.2.1
  dsimp only [sourceInv] at hb ⊢
  constructor <;> omega

private theorem entry_step (request : List Byte)
    (state : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool))
    (hI : sourceInv core state)
    (result : PUnit × ((CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool)))
    (hr : result ∈ support ((simulateQ (controlled core pkSeed caps extra fallback)
      (SigningView.Events.emit (labSpec core) (List Byte) (.signingAttempt request))).run state)) :
    sourceInv core result.2 ∧
      (result.2.2.2 = true ∨ result.2.1.2.2.1.cnt .signer + 1 ≤ result.2.2.1.2) := by
  simp only [SigningView.Events.emit, simulateQ_spec_query, controlled,
    QueryImpl.guardQueryBudget, StateT.run_mk] at hr
  split_ifs at hr with hflag hcap
  · have heq : result = (fallback (.inr (.signingAttempt request)), state) := by
      simpa only [support_pure, Set.mem_singleton_iff] using hr
    subst result
    exact ⟨hI, .inl hflag⟩
  · rw [nativeRelative_marker] at hr
    simp only [map_pure, support_pure, Set.mem_singleton_iff] at hr
    subst result
    dsimp only [sourceInv] at hI
    constructor
    · dsimp only [sourceInv, sourcePolicy, baseWork, Sum.elim_inr, Prod.fst_add, Prod.snd_add]
      constructor <;> omega
    · right
      dsimp only [sourcePolicy, Prod.snd_add, Sum.elim_inr]
      omega
  · have heq : result = (fallback (.inr (.signingAttempt request)),
        (state.1, (state.2.1, true))) := by
      simpa only [support_pure, Set.mem_singleton_iff] using hr
    subst result
    exact ⟨hI, .inl rfl⟩

private theorem signer_preserves (kappa : PublicKeyCore core → core.Y)
    (pk sk : PublicKeyCore core) (request : List Byte)
    (state : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool))
    (hI : sourceInv core state)
    (result : GeneralScheme.SignatureCore vp core ×
      ((CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool)))
    (hr : result ∈ support ((simulateQ (controlled core pkSeed caps extra fallback)
      ((markedLabScheme core (fun pk => pure (kappa pk)) pkSeed).sign pk sk request)).run state)) :
    sourceInv core result.2 := by
  simp only [markedLabScheme, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨entry, he, hr⟩ := hr
  obtain ⟨hentry, habort | hcredit⟩ :=
    entry_step core pkSeed caps extra fallback request state hI entry he
  · have hf := controlled_aborted core pkSeed caps extra fallback _ entry.2 habort result hr
    simpa only [hf] using hentry
  · have hb : IsQueryBoundP
        ((labScheme core (fun pk => pure (kappa pk)) pkSeed).sign pk sk request)
        (IsPublicLabQuery core) 1 :=
      isQueryBoundP_labScheme_sign_of_hmsg pkSeed (fun pk => pure (kappa pk))
        (fun _ h => h) pk sk request
        (fun _ => (isQueryBoundP_query_iff _ _ _).mpr (fun _ => by decide))
    have hw := phase_work core pkSeed caps extra fallback .signer _ entry.2 hentry.2 result hr
    have hc := phase_cnt_le core pkSeed caps extra fallback .signer _ hb entry.2 result hr
    exact ⟨by omega, hw.2⟩

private theorem logged_preserves {α : Type}
    (red : QueryImpl (labSpec core + (List Byte →ₒ GeneralScheme.SignatureCore vp core))
      (WriterT (QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core))
        (OracleComp (SigningView.Events.Spec (labSpec core) (List Byte)))))
    (body : OracleComp (labSpec core + (List Byte →ₒ GeneralScheme.SignatureCore vp core)) α)
    (step : ∀ input state, sourceInv core state → ∀ out ∈ support
      ((simulateQ (controlled core pkSeed caps extra fallback) (red input).run).run state),
      sourceInv core out.2)
    (state : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool))
    (hI : sourceInv core state) (result : (α × QueryLog
      (List Byte →ₒ GeneralScheme.SignatureCore vp core)) ×
      ((CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool)))
    (hr : result ∈ support ((simulateQ (controlled core pkSeed caps extra fallback)
      (simulateQ red body).run).run state)) : sourceInv core result.2 := by
  induction body using OracleComp.inductionOn generalizing state result with
  | pure x =>
      simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hr
      subst result
      exact hI
  | query_bind input k ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind', StateT.run_bind,
        mem_support_bind_iff] at hr
      obtain ⟨out, hout, hr⟩ := hr
      rw [simulateQ_map, StateT.run_map, support_map] at hr
      obtain ⟨rest, hrest, rfl⟩ := hr
      exact ih out.1.1 out.2 (step input state hI out hout) rest hrest

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

private theorem callback_preserves (kappa : PublicKeyCore core → core.Y)
    (e : core.SkSeed ≃ core.Y)
    (adv : UnforgeableAdversary
      (romScheme core e (fun pk => pure (kappa pk)) (pure pkSeed)))
    (pk sk : PublicKeyCore core)
    (state : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool))
    (hI : sourceInv core state)
    (result : ((List Byte × GeneralScheme.SignatureCore vp core) × QueryLog
      (List Byte →ₒ GeneralScheme.SignatureCore vp core)) ×
      ((CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool)))
    (hr : result ∈ support ((simulateQ (controlled core pkSeed caps extra fallback)
      ((markedLabScheme core (fun pk => pure (kappa pk)) pkSeed).runWithSigningOracle pk sk
        ((markedLabAdversary core adv pkSeed).main pk))).run state)) :
    sourceInv core result.2 := by
  let alg := markedLabScheme core (fun pk => pure (kappa pk)) pkSeed
  let red : QueryImpl (labSpec core + (List Byte →ₒ GeneralScheme.SignatureCore vp core))
      (WriterT (QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core))
        (OracleComp (SigningView.Events.Spec (labSpec core) (List Byte)))) :=
    ((SigningView.Events.Spec (labSpec core) (List Byte)).passthrough + alg.signingOracle pk sk) ∘ₛ
      QueryImpl.add
        (fun input => simulateQ (fun native => liftM
          ((SigningView.Events.Spec (labSpec core) (List Byte) +
            (List Byte →ₒ GeneralScheme.SignatureCore vp core)).query (.inl native)))
          (SigningView.Events.phaseImpl (labSpec core) (List Byte) .adversary input))
        (fun request => liftM ((SigningView.Events.Spec (labSpec core) (List Byte) +
          (List Byte →ₒ GeneralScheme.SignatureCore vp core)).query (.inr request)))
  simp only [markedLabAdversary, runWithSigningOracle, SigningView.Events.mainWithEvents] at hr
  rw [← QueryImpl.simulateQ_compose] at hr
  apply logged_preserves core pkSeed caps extra fallback red _ _ state hI result hr
  intro input initial hi out hout
  cases input with
  | inl input =>
      have step : (red (.inl input)).run = (fun answer => (answer, [])) <$>
          SigningView.Events.phaseImpl (labSpec core) (List Byte) .adversary input := by
        simp only [red, QueryImpl.apply_compose, QueryImpl.add]
        have h : simulateQ ((SigningView.Events.Spec (labSpec core) (List Byte)).passthrough +
            alg.signingOracle pk sk) (simulateQ (fun native => liftM
              ((SigningView.Events.Spec (labSpec core) (List Byte) +
                (List Byte →ₒ GeneralScheme.SignatureCore vp core)).query (.inl native)))
              (SigningView.Events.phaseImpl (labSpec core) (List Byte) .adversary input)) =
            simulateQ ((QueryImpl.id'
              (SigningView.Events.Spec (labSpec core) (List Byte))).liftTarget
              (WriterT (QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core))
                (OracleComp (SigningView.Events.Spec (labSpec core) (List Byte)))))
              (SigningView.Events.phaseImpl (labSpec core) (List Byte) .adversary input) := by
          apply QueryImpl.simulateQ_simulateQ_eq_of_apply
          intro native
          simp only [simulateQ_spec_query, QueryImpl.passthrough_add, QueryImpl.add_apply_inl]
        rw [h, writerT_run_simulateQ_liftTarget, simulateQ_id']
        rfl
      rw [step, simulateQ_map, StateT.run_map, support_map] at hout
      obtain ⟨native, hn, rfl⟩ := hout
      apply phase_forger core pkSeed caps extra fallback .adversary rfl
        (liftM ((labSpec core).query input)) initial hi native
      simpa only [simulateQ_spec_query] using hn
  | inr request =>
      have step : (red (.inr request)).run =
          (fun answer => (answer, [⟨request, answer⟩])) <$> alg.sign pk sk request := by
        simp [red, QueryImpl.add, signingOracle, QueryImpl.withLogging_apply]
      rw [step, simulateQ_map, StateT.run_map, support_map] at hout
      obtain ⟨signed, hs, rfl⟩ := hout
      exact signer_preserves core pkSeed caps extra fallback kappa pk sk request
        initial hi signed hs

private theorem experiment_preserves (kappa : PublicKeyCore core → core.Y)
    (e : core.SkSeed ≃ core.Y)
    (adv : UnforgeableAdversary
      (romScheme core e (fun pk => pure (kappa pk)) (pure pkSeed)))
    (state : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool))
    (hI : sourceInv core state)
    (result : DeriveOutcome core ×
      ((CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool)))
    (hr : result ∈ support ((simulateQ (controlled core pkSeed caps extra fallback)
      (markedLabExperiment core adv pkSeed)).run state)) : sourceInv core result.2 := by
  obtain ⟨first, second, hk, hf, hv⟩ :=
    exists_mem_support_run_of_mem_support_run_unforgeableTranscriptExperiment
      (controlled core pkSeed caps extra fallback) (markedLabAdversary core adv pkSeed) hr
  simp only [markedLabScheme] at hk hv
  have hb : IsQueryBoundP (labScheme core (fun pk => pure (kappa pk)) pkSeed).keygen
      (IsPublicLabQuery core) 0 :=
    isQueryBoundP_labScheme_keygen pkSeed (fun pk => pure (kappa pk))
      (by intro x; simp [IsPublicLabQuery]) (by intro cell; simp [IsPublicLabQuery])
  have hw := phase_work core pkSeed caps extra fallback .keygen _ state hI.2 _ hk
  have hc := phase_cnt_le core pkSeed caps extra fallback .keygen _ hb state _ hk
  dsimp only at hw hc
  have hfirst : sourceInv core first := ⟨by dsimp only [sourceInv] at hI ⊢; omega, hw.2⟩
  have hsecond := callback_preserves core pkSeed caps extra fallback kappa e adv
    result.1.pk result.1.sk first hfirst _ hf
  exact phase_forger core pkSeed caps extra fallback .verification rfl _ second hsecond
    (result.1.verified, result.2) hv

omit [SampleableType core.SkSeed] [SampleableType core.SkPrf] in
private theorem guard_native_reassoc {α : Type}
    (program : OracleComp (SigningView.Events.Spec (labSpec core) (List Byte)) α)
    (relativeState : CoverageDeferred.S core) (nativeState : Coverage.RoleState core)
    (counts : Nat × Nat) (flag : Bool) :
    (simulateQ (Coverage.roleRunImpl core)
      ((simulateQ (QueryImpl.guardQueryBudget caps
        (Sum.elim (fun _ => (0, 0)) (sourcePolicy core extra))
        (CoverageDeferred.relative core pkSeed
      (fun _ : SigningView.Event (labSpec core) (List Byte) => 0)) fallback) program).run
          (relativeState, (counts, flag)))).run nativeState =
    (fun out => ((out.1, (out.2.1.1, out.2.2)), out.2.1.2)) <$>
      (simulateQ (controlled core pkSeed caps extra fallback) program).run
        ((relativeState, nativeState), (counts, flag)) := by
  let cost : (SigningView.Events.Spec (labSpec core) (List Byte)).Domain → Nat × Nat :=
    Sum.elim (fun _ => (0, 0)) (sourcePolicy core extra)
  let inner := QueryImpl.guardQueryBudget caps cost
    (CoverageDeferred.relative core pkSeed
      (fun _ : SigningView.Event (labSpec core) (List Byte) => 0)) fallback
  let project : ((CoverageDeferred.S core × ((Nat × Nat) × Bool)) × Coverage.RoleState core) →
      (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool) :=
    fun state => ((state.1.1, state.2), state.1.2)
  have hstep : ∀ input state,
      Prod.map id project <$>
        ((((Coverage.roleRunImpl core).mapStateTBase inner).flattenStateT input).run state) =
      (controlled core pkSeed caps extra fallback input).run (project state) := by
    rintro input ⟨⟨rel, n, aborted⟩, native⟩
    cases aborted with
    | false =>
        by_cases hcap : n + cost input ≤ caps
        all_goals simp [QueryImpl.flattenStateT_mapStateTBase_apply_run, inner, controlled,
          nativeRelative, QueryImpl.guardQueryBudget, project, hcap, cost,
          simulateQ_map, StateT.run_map, Functor.map_map]
    | true =>
        simp [QueryImpl.flattenStateT_mapStateTBase_apply_run, inner, controlled,
          QueryImpl.guardQueryBudget, project]
  have hfold := map_run_simulateQ_eq_of_query_map_eq
    ((Coverage.roleRunImpl core).mapStateTBase inner).flattenStateT
    (controlled core pkSeed caps extra fallback) project hstep program
    ((relativeState, (counts, flag)), nativeState)
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  rw [← hfold, Functor.map_map]
  rfl

end Counts

/-- Native digest calls and fresh positions respect admitted signing attempts and joint work.
The complete source transcript, caches, resource pair and abort flag remain in one run. -/
theorem native_counts_markedLabExperiment
    {vp : ValidatedParams} (core : CorePrimitives vp.params)
    [SampleableType core.Y] [SampleableType (Bytes vp.params.m)]
    [DecidableEq core.Y] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]
    [DecidableEq core.SkPrf] [SampleableType core.SkSeed] [SampleableType core.SkPrf]
    (e : core.SkSeed ≃ core.Y)
    (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed)
    (adv : UnforgeableAdversary
      (romScheme core e (fun pk => pure (kappa pk)) (pure pkSeed)))
    (caps : Nat × Nat)
    (extra : SigningView.Event (labSpec core) (List Byte) → Nat)
    (fallback : (input : (SigningView.Events.Spec (labSpec core) (List Byte)).Domain) →
      (SigningView.Events.Spec (labSpec core) (List Byte)).Range input)
    (L : (j : Coverage.TapeClass) → List (Coverage.tapeClassRange core j)) :
    let base : SigningView.Event (labSpec core) (List Byte) → Nat := fun event =>
      match event with
      | .signingAttempt _ => 1
      | .ambient .adversary input | .ambient .verification input =>
          if IsPublicLabQuery core input then 1 else 0
      | _ => 0
    let policy : SigningView.Event (labSpec core) (List Byte) → Nat × Nat := fun event =>
      (base event + extra event, match event with | .signingAttempt _ => 1 | _ => 0)
    let guarded := QueryImpl.guardQueryBudget caps (Sum.elim (fun _ => (0, 0)) policy)
      (CoverageDeferred.relative core pkSeed
      (fun _ : SigningView.Event (labSpec core) (List Byte) => 0)) fallback
    let initial : CoverageDeferred.S core × ((Nat × Nat) × Bool) :=
      ((((∅, ∅), []), (0, .keygen)), ((0, 0), false))
    let source := markedLabExperiment core adv pkSeed
    let guardedNative := (simulateQ guarded source).run initial
    let run := (simulateQ (Coverage.roleRunImpl core) guardedNative).run
      ((∅, L), (AnswerTape.ClassPos.init, ∅))
    ∀ result ∈ support run,
      let resource := result.1.2.2.1
      let pos := result.2.2.1
      let S := resource.2
      let C := pos.cnt .signer
      let M := pos.cnt .forger
      C ≤ S ∧ pos.next .signer ≤ C ∧ S + M ≤ resource.1 ∧
        resource.1 ≤ caps.1 ∧ S ≤ caps.2 := by
  dsimp only
  intro result hr
  have hpos := simulateQ_run_preserves_inv_of_query (Coverage.roleRunImpl core)
    (fun state => AnswerTape.ClassPosInv (Coverage.tapeClass core) L state.1.1 state.1.2
      state.2.1.cls state.2.1.pos state.2.1.next state.2.1.cnt)
    (AnswerTape.classPosInvAuxFwd_step (Coverage.tapeClass core)
      (Coverage.range_eq_tapeClassRange core)
      (AnswerTape.freshHitAux (Coverage.IsRandPoint core) (Coverage.randRel core)) L)
    _ _ (AnswerTape.ClassPosInv.empty (Coverage.tapeClass core) L) result hr
  change result ∈ support ((simulateQ (Coverage.roleRunImpl core)
    ((simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ => (0, 0)) (sourcePolicy core extra))
      (CoverageDeferred.relative core pkSeed
      (fun _ : SigningView.Event (labSpec core) (List Byte) => 0)) fallback)
      (markedLabExperiment core adv pkSeed)).run
        ((((∅, ∅), []), (0, .keygen)), ((0, 0), false)))).run
          ((∅, L), (AnswerTape.ClassPos.init, ∅))) at hr
  rw [guard_native_reassoc core pkSeed caps extra fallback, support_map] at hr
  obtain ⟨out, hout, rfl⟩ := hr
  have hI := experiment_preserves core pkSeed caps extra fallback kappa e adv _
    (by simp [sourceInv, AnswerTape.ClassPos.init]) out hout
  have hcap := QueryImpl.guardQueryBudget_counts_le_caps caps
    (Sum.elim (fun _ => (0, 0)) (sourcePolicy core extra))
    (nativeRelative core pkSeed) fallback (markedLabExperiment core adv pkSeed)
    ((((∅, ∅), []), (0, .keygen)), ((∅, L), (AnswerTape.ClassPos.init, ∅))) out hout
  exact ⟨hI.1, hpos.next_le_cnt .signer, hI.2, hcap.1, hcap.2⟩

#print axioms native_counts_markedLabExperiment


universe v

/-- Deterministic phase observation retains the complete counted transcript and its keys. -/
theorem runObs_markedLabExperiment_eq_counted_full_transcript
    {vp : ValidatedParams} (core : CorePrimitives vp.params)
    [SampleableType core.Y] [DecidableEq core.Y]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf]
    {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist))
    (pkSeed : core.PkSeed)
    (policy : SigningView.Event (labSpec core) (List Byte) → Nat × Nat)
    {m : Type → Type v} [Monad m] [LawfulMonad m] {Cache : Type}
    (handler : QueryImpl (labSpec core) (StateT Cache m)) (initial : Cache) :
    let counted : SigningView.CostM (labSpec core) (Nat × Nat) (DeriveOutcome core) := do
      let keys ← SigningView.costed policy .keygen (labScheme core optRand pkSeed).keygen
      let outcome ← SigningView.countedAfterKeygen policy
        (SigningView.ofTotal (labScheme core optRand pkSeed)) keys.1 keys.2
        (labAdversary core adv pkSeed).main
      return ⟨keys.1, keys.2, outcome.rawLog,
        outcome.forgery.1, outcome.forgery.2, outcome.verified⟩
    (fun result => ((result.1.1, Multiplicative.toAdd result.1.2), result.2)) <$>
      (runObs handler (fun event => Multiplicative.ofAdd (policy event))
        (markedLabExperiment core adv pkSeed)).run initial =
      (simulateQ handler counted.runAdd).run initial := by
  intro counted
  let view := SigningView.ofTotal (labScheme core optRand pkSeed)
  let main := (labAdversary core adv pkSeed).main
  let pack := fun result : (PublicKeyCore core × PublicKeyCore core) ×
      SigningView.Outcome (List Byte) (GeneralScheme.SignatureCore vp core)
        (GeneralScheme.SignatureCore vp core) =>
    (⟨result.1.1, result.1.2, result.2.rawLog,
      result.2.forgery.1, result.2.forgery.2, result.2.verified⟩ : DeriveOutcome core)
  let markedFull : OracleComp (SigningView.Events.Spec (labSpec core) (List Byte))
      ((PublicKeyCore core × PublicKeyCore core) ×
        SigningView.Outcome (List Byte) (GeneralScheme.SignatureCore vp core)
          (GeneralScheme.SignatureCore vp core)) := do
    let keys ← (SigningView.Events.viewWithEvents view).keygen
    let (forgery, rawLog) ← (SigningView.Events.viewWithEvents view).runWithSigningOracle
      keys.1 keys.2 (SigningView.Events.mainWithEvents main keys.1)
    let verified ← (SigningView.Events.viewWithEvents view).verify
      keys.1 forgery.1 forgery.2
    return (keys, ⟨forgery, rawLog, verified⟩)
  let countedFull : SigningView.CostM (labSpec core) (Nat × Nat)
      ((PublicKeyCore core × PublicKeyCore core) ×
        SigningView.Outcome (List Byte) (GeneralScheme.SignatureCore vp core)
          (GeneralScheme.SignatureCore vp core)) := do
    let keys ← SigningView.costed policy .keygen view.keygen
    let outcome ← SigningView.countedAfterKeygen policy view keys.1 keys.2 main
    return (keys, outcome)
  have hmarked : markedLabExperiment core adv pkSeed = pack <$> markedFull := by
    rw [markedLabExperiment, unforgeableTranscriptExperiment_def]
    simp only [markedFull, map_bind, map_pure]
    rfl
  have hcounted : counted = pack <$> countedFull := by
    simp only [countedFull, map_bind, map_pure]
    rfl
  have h := SigningView.Events.runObs_fullKeys_eq_counted view main policy handler initial
  change (fun result => ((result.1.1, Multiplicative.toAdd result.1.2), result.2)) <$>
      (runObs handler (fun event => Multiplicative.ofAdd (policy event)) markedFull).run
        initial = (simulateQ handler countedFull.runAdd).run initial at h
  have mapped := congrArg
    (fun program => (fun result => ((pack result.1.1, result.1.2), result.2)) <$> program) h
  simpa only [hmarked, hcounted, runObs_map, AddWriterT.runAdd_map,
    StateT.run_map, simulateQ_map, Functor.map_map, Prod.map, id_eq] using mapped

#print axioms runObs_markedLabExperiment_eq_counted_full_transcript

end SLHDSA.Security.MarkedLab
