/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import NativePotential
import all NativePotential

/-! # Deterministic-nonce query discipline of the native signing suffix -/

public section
open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal
namespace SLHDSA.Security.Coverage.NativeThin1
variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-- Every non-randomizer query respects the deterministic nonce discipline in either role. -/
theorem good_roleQuery_of_not_rand (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y) (r : Role) (t : (deriveSpec core).Domain)
    (h : ¬IsRandQuery core t) : GoodQuery core pk kappa (roleQuery core r t) := by
  cases r <;> rcases t with ((n | hash) | (key | pair)) <;>
    simp_all [GoodQuery, GoodPoint, roleQuery, IsRandQuery]

variable [SampleableType core.Y] [DecidableEq core.Y]

omit [DecidableEq core.Y] [SampleableType core.Y] in
/-- A source program without nonce derivations has only allowed queries after role tagging. -/
theorem allowed_role_no_rand (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y) (r : Role) {α : Type}
    (program : OracleComp (deriveSpec core) α)
    (bound : program.IsQueryBoundP (IsRandQuery core) 0) :
    (simulateQ (roleImpl core r) program).AllQueriesSatisfy (GoodQuery core pk kappa) := by
  classical
  have allowed := (isQueryBoundP_zero_iff program (fun t => ¬IsRandQuery core t)).mp
    (by simpa only [not_not] using bound)
  apply allowed.simulateQ
  intro t ht
  exact (isQueryBoundP_zero_iff _ (GoodQuery core pk kappa)).mp
    ((isQueryBoundP_roleImpl_iff core r t).mpr fun bad =>
      (bad (good_roleQuery_of_not_rand core pk kappa r t ht)).elim)

/-- Deterministic signing makes nonce derivations only at its supplied public key's salt. -/
theorem allowed_role_sign (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed)
    (sk : PublicKeyCore core) (msg : List Byte) :
    ((roleScheme core (fun pk => pure (kappa pk)) pkSeed).sign pk sk msg).AllQueriesSatisfy
      (GoodQuery core pk kappa) := by
  change (simulateQ (roleImpl core .signer)
    ((deriveScheme core (fun pk => pure (kappa pk)) pkSeed).sign pk sk msg)).AllQueriesSatisfy _
  rw [deriveScheme_sign_eq]
  simp only [liftM_pure, pure_bind]
  rw [simulateQ_bind, simulateQ_HasQuery_query]
  apply allQueriesSatisfy_bind
  · simp only [roleImpl]
    exact (allQueriesSatisfy_query_iff _ _).mpr rfl
  · intro R
    rw [simulateQ_bind]
    apply allQueriesSatisfy_bind
    · exact allowed_role_no_rand core pk kappa .signer _
        ((isQueryBoundP_query_iff _ _ _).mpr False.elim)
    · intro digest
      exact allowed_role_no_rand core pk kappa .signer _
        ((isQueryBoundP_signTail core sk.pkSeed R digest).of_imp fun _ => Or.inr)

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

/-- The actual signing phase respects the fixed public key's deterministic nonce discipline. -/
theorem allowed_signing_phase (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed)
    (e : core.SkSeed ≃ core.Y)
    (adv : UnforgeableAdversary
      (romScheme core e (fun pk => pure (kappa pk)) (pure pkSeed)))
    (sk : PublicKeyCore core) :
    ((roleScheme core (fun pk => pure (kappa pk)) pkSeed).runWithSigningOracle pk sk
      (((deriveAdversary core adv pkSeed).mapOracles (roleImpl core .forger)
        (sigAlg' := roleScheme core (fun pk => pure (kappa pk)) pkSeed)).main pk)).AllQueriesSatisfy
      (GoodQuery core pk kappa) := by
  classical
  rw [UnforgeableAdversary.mapOracles_main]
  apply (isQueryBoundP_zero_iff _ (GoodQuery core pk kappa)).mp
  let sourceAllowed :
      ((deriveSpec core) + (List Byte →ₒ GeneralScheme.SignatureCore vp core)).Domain → Prop :=
    Sum.elim (fun t => t.isLeft = true) fun _ => True
  have sourceBound := (isQueryBoundP_zero_iff _ sourceAllowed).mpr
    (allQueriesSatisfy_deriveAdversary_main core adv pkSeed pk)
  refine isQueryBoundP_runWithSigningOracle_simulateQ_addLift _ pk sk _ sourceBound ?_ ?_ ?_ ?_
  · intro t _
    exact (isQueryBoundP_roleImpl_iff core .forger t).mpr fun _ => Nat.one_pos
  · intro t h
    apply (isQueryBoundP_zero_iff _ (GoodQuery core pk kappa)).mpr
    have ht : t.isLeft = true := not_not.mp h
    apply (isQueryBoundP_zero_iff _ (GoodQuery core pk kappa)).mp
    exact (isQueryBoundP_roleImpl_iff core .forger t).mpr fun bad => by
      exfalso
      apply bad
      rcases t with (n | hash) | derivation
      · exact trivial
      · exact trivial
      · cases ht
  · intro msg h
    exact (h trivial).elim
  · intro msg _
    exact (isQueryBoundP_zero_iff _ (GoodQuery core pk kappa)).mpr
      (allowed_role_sign core pk kappa pkSeed sk msg)

/-- The post-key-generation suffix of the native transcript experiment. -/
noncomputable def suffix (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed)
    (e : core.SkSeed ≃ core.Y)
    (adv : UnforgeableAdversary
      (romScheme core e (fun pk => pure (kappa pk)) (pure pkSeed)))
    (pk sk : PublicKeyCore core) : OracleComp (roleSpec core) (DeriveOutcome core) := do
  let ((msg, sig), log) ←
    (roleScheme core (fun pk => pure (kappa pk)) pkSeed).runWithSigningOracle pk sk
      (((deriveAdversary core adv pkSeed).mapOracles (roleImpl core .forger)
        (sigAlg' := roleScheme core (fun pk => pure (kappa pk)) pkSeed)).main pk)
  let verified ← (roleScheme core (fun pk => pure (kappa pk)) pkSeed).verify pk msg sig
  return ⟨pk, sk, log, msg, sig, verified⟩

/-- The native transcript's suffix contains only correctly salted randomizer derivations. -/
theorem allowed_suffix (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed)
    (e : core.SkSeed ≃ core.Y)
    (adv : UnforgeableAdversary
      (romScheme core e (fun pk => pure (kappa pk)) (pure pkSeed)))
    (pk sk : PublicKeyCore core) :
    (suffix core kappa pkSeed e adv pk sk).AllQueriesSatisfy (GoodQuery core pk kappa) := by
  unfold suffix
  apply allQueriesSatisfy_bind (allowed_signing_phase core pk kappa pkSeed e adv sk)
  rintro ⟨⟨msg, sig⟩, log⟩
  apply allQueriesSatisfy_bind
  · exact allowed_role_no_rand core pk kappa .forger _
      (isQueryBoundP_deriveScheme_verify_rand core (fun pk => pure (kappa pk)) pkSeed pk msg sig)
  · intro _
    exact allQueriesSatisfy_pure _ _

/-- The post-key-generation suffix returns the public key supplied to it. -/
theorem suffix_pk (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed)
    (e : core.SkSeed ≃ core.Y)
    (adv : UnforgeableAdversary
      (romScheme core e (fun pk => pure (kappa pk)) (pure pkSeed)))
    (pk sk : PublicKeyCore core) (z : DeriveOutcome core)
    (hz : z ∈ support (suffix core kappa pkSeed e adv pk sk)) : z.pk = pk := by
  simp only [suffix, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨⟨⟨msg, sig⟩, log⟩, _, verdict, _, rfl⟩ := hz
  rfl

/-- The native experiment keeps its key-generation prefix and its exact suffix in sequence. -/
theorem roleExperiment_eq_prefix_suffix (kappa : PublicKeyCore core → core.Y)
    (pkSeed : core.PkSeed) (e : core.SkSeed ≃ core.Y)
    (adv : UnforgeableAdversary
      (romScheme core e (fun pk => pure (kappa pk)) (pure pkSeed))) :
    roleExperiment core adv pkSeed =
      (roleScheme core (fun pk => pure (kappa pk)) pkSeed).keygen >>=
        fun keys => suffix core kappa pkSeed e adv keys.1 keys.2 := by
  rw [roleExperiment, unforgeableTranscriptExperiment_def]
  rfl

variable [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

omit [SampleableType core.SkSeed] [SampleableType core.SkPrf] in
/-- Every supported native key-generation prefix leaves every forger slot unassigned. -/
theorem prefix_potential (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed)
    (L : (j : TapeClass) → List (tapeClassRange core j)) (index : Nat)
    (z : (PublicKeyCore core × PublicKeyCore core) × RoleState core)
    (hz : z ∈ support ((simulateQ (roleRunImpl core)
      (roleScheme core (fun pk => pure (kappa pk)) pkSeed).keygen).run
        ((∅, L), (AnswerTape.ClassPos.init, ∅)))) :
    potential core z.1.1 kappa L index z.2 = (Nat.card core.Y : ℝ≥0∞)⁻¹ := by
  classical
  have initial : AnswerTape.HitInv (tapeClass core) L
      (((∅, L), (AnswerTape.ClassPos.init, ∅)) : RoleState core) :=
    ⟨AnswerTape.ClassPosInv.empty (tapeClass core) L, fun _ hit => hit.elim⟩
  have after := simulateQ_run_preserves_inv_of_query (roleRunImpl core)
    (AnswerTape.HitInv (tapeClass core) L)
    (fun _ _ hs _ hy => AnswerTape.hitInv_of_mem_support_classPosImplFwd_run
      (IsRandPoint core) (randRel core) (tapeClass core) (range_eq_tapeClassRange core) hs hy)
    _ _ initial z hz
  have hS0 : ∀ t, IsQueryBoundP (roleImpl core .signer t)
      (fun t => AnswerTape.classOf (tapeClass core) t = some .forger) 0 := fun t =>
    (isQueryBoundP_roleImpl_iff core _ t).mpr fun h =>
      absurd ((classOf_roleQuery_eq_some_iff core .signer .forger t).mp h).1 nofun
  have hb : IsQueryBoundP (roleScheme core (fun pk => pure (kappa pk)) pkSeed).keygen
      (fun t => AnswerTape.classOf (tapeClass core) t = some .forger) 0 :=
    isQueryBoundP_simulateQ_zero _ hS0
  have count := AnswerTape.cnt_le_of_isQueryBoundP (tapeClass core)
    (range_eq_tapeClassRange core) (AnswerTape.freshHitAux (IsRandPoint core) (randRel core))
    (∅ : Set (jointSpec core).Domain) L _ TapeClass.forger hb hz
  have noSlot : ¬ActualSlot core z.1.1 z.2 index := by
    intro slot
    have reached := actualSlot_reached core z.1.1 L after slot
    omega
  have noFired : ¬Fired core z.1.1 z.2 index := by
    rintro ⟨R, M, hc, hp, _⟩
    exact noSlot ⟨R, M, hc, hp⟩
  simp only [potential, after, noFired, noSlot, ↓reduceIte, not_false_eq_true, true_or]

/-- A simulated suffix retains its supplied public key in its full returned transcript. -/
theorem suffix_run_pk (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed)
    (e : core.SkSeed ≃ core.Y)
    (adv : UnforgeableAdversary
      (romScheme core e (fun pk => pure (kappa pk)) (pure pkSeed)))
    (pk sk : PublicKeyCore core) (s : RoleState core) (z : DeriveOutcome core × RoleState core)
    (hz : z ∈ support ((simulateQ (roleRunImpl core)
      (suffix core kappa pkSeed e adv pk sk)).run s)) : z.1.pk = pk := by
  simp only [suffix, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨⟨⟨⟨msg, sig⟩, log⟩, state⟩, _, ⟨verdict, state'⟩, _, rfl⟩ := hz
  rfl

/-- The actual-key potential has expectation at most one nonce credit in the native role run. -/
theorem whole_potential (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed)
    (e : core.SkSeed ≃ core.Y)
    (adv : UnforgeableAdversary
      (romScheme core e (fun pk => pure (kappa pk)) (pure pkSeed)))
    (L : (j : TapeClass) → List (tapeClassRange core j)) (hL : L .other = [])
    (index : Nat) :
    ∫⁻ r, r ∂𝒟[(fun z => potential core z.1.pk kappa L index z.2) <$>
      roleRun core adv pkSeed L] ≤ (Nat.card core.Y : ℝ≥0∞)⁻¹ := by
  classical
  change ∫⁻ r, r ∂𝒟[(fun z => potential core z.1.pk kappa L index z.2) <$>
    ((simulateQ (roleRunImpl core) (roleExperiment core adv pkSeed)).run
      ((∅, L), (AnswerTape.ClassPos.init, ∅)))] ≤ _
  rw [roleExperiment_eq_prefix_suffix core kappa pkSeed e adv, simulateQ_bind,
    StateT.run_bind, lintegral_id_evalDist_map_bind]
  apply lintegral_id_evalDist_map_le_of_le_of_mem_support
  intro z hz
  have init := prefix_potential core kappa pkSeed L index z hz
  have bound := potential_run core z.1.1 kappa L hL index
    (suffix core kappa pkSeed e adv z.1.1 z.1.2)
    (allowed_suffix core kappa pkSeed e adv z.1.1 z.1.2) z.2
  rw [init] at bound
  convert bound using 1
  let _ : MeasurableSpace (DeriveOutcome core × RoleState core) := ⊤
  rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map]
  apply lintegral_congr_ae
  exact evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete fun y hy => by
    dsimp only
    rw [suffix_run_pk core kappa pkSeed e adv z.1.1 z.1.2 z.2 y hy]

end SLHDSA.Security.Coverage.NativeThin1
#print axioms SLHDSA.Security.Coverage.NativeThin1.good_roleQuery_of_not_rand
#print axioms SLHDSA.Security.Coverage.NativeThin1.allowed_role_no_rand
#print axioms SLHDSA.Security.Coverage.NativeThin1.allowed_role_sign

#print axioms SLHDSA.Security.Coverage.NativeThin1.allowed_signing_phase

#print axioms SLHDSA.Security.Coverage.NativeThin1.allowed_suffix
#print axioms SLHDSA.Security.Coverage.NativeThin1.suffix_pk
#print axioms SLHDSA.Security.Coverage.NativeThin1.roleExperiment_eq_prefix_suffix
#print axioms SLHDSA.Security.Coverage.NativeThin1.prefix_potential

#print axioms SLHDSA.Security.Coverage.NativeThin1.suffix_run_pk
#print axioms SLHDSA.Security.Coverage.NativeThin1.whole_potential
