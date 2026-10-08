/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.CoverageHits
public import HashSig.SLHDSA.Security.DigestTransport
public import HashSig.SLHDSA.Security.RomSchemeUnion
import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# The instrumented role run of the secret-free SLH-DSA experiment

`roleRun core adv pkSeed L` runs the role-tagged experiment `roleExperiment` on the tape family
`L` under `roleRunImpl core`: the forwarded class-indexed tape oracle
`AnswerTape.classPosImplFwd` of the tape classes, with the position bookkeeping and the hit set
`AnswerTape.freshHitAux (IsRandPoint core) (randRel core)` written at fresh randomizer draws.

* *One step.* A step changes the cache and the class of a point only by querying it, and the
  class only if the point was uncached (`cache_cls_of_mem_support_roleRunImpl_run`). A query of
  the signer copy caches its answer, and a fresh randomizer derivation records the points it hits
  (`cache_cls_hits_of_mem_support_roleRunImpl_run_inr`).
* *The run invariant.* `RunInv core pk log s`: every point of class `signer` is the `H_msg`
  point `hmsgPoint core pk R M` of a logged signature, and the `H_msg` point of every logged
  signature and of every cached randomizer derivation is `Covered` (cached, and of class
  `signer` or hit). Frame queries (`IsFrameQuery`: neither a randomizer derivation nor of class
  `signer`) preserve it, and so does signing once its signature is logged (`RunInv.sign`): if
  the derivation of the randomizer is fresh, its draw hits the `H_msg` point when that point is
  already cached; if it is cached, an earlier signature on the same message covered the point;
  otherwise the `H_msg` query is fresh and takes class `signer`. Key generation, verification
  and the forger make frame queries only, the forger because it makes no derivation query
  (`allQueriesSatisfy_deriveAdversary_main`).
* *Consequences.* Every point of class `signer` is the `H_msg` point of a logged signature
  (`exists_mem_log_of_cls_eq_signer`), and the `H_msg` point of every logged signature is of
  class `signer` or in the hit set (`cls_eq_signer_or_mem_hits_of_mem_log`).
* *The event mapping.* Coverage of a fresh forgery (`RunItsrCovered`) on a run over a family
  drawn at the lengths `tapeLength qh qs` yields a witness `(n, f)`: the forger-tape position `n`
  of the forgery's `H_msg` point and a coverer slot `f i` for every FORS tree
  (`exists_witness_of_runItsrCovered`). Its tape event `TapeMatch` holds of the family, and the
  generic `AnswerTape.HitAll` holds of the run at its designated positions `desigPos`.

## Scope

* The statements are per public seed and per tape family, about the support of the run.
* This module bounds no probability.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.Security.Coverage

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-! ## Points, hits and the run state -/

/-- The `H_msg` point of the joint interface at randomizer `R` and message `M` under the public
key `pk`. -/
@[expose] def hmsgPoint (pk : PublicKeyCore core) (R : core.Y) (M : List Byte) :
    (jointSpec core).Domain :=
  .inl (.inl (.hmsg R pk.pkSeed pk.pkRoot M))

/-- Under one public key, distinct randomizer-message pairs have distinct `H_msg` points. -/
theorem hmsgPoint_inj (pk : PublicKeyCore core) {R R' : core.Y} {M M' : List Byte} :
    hmsgPoint core pk R M = hmsgPoint core pk R' M' ↔ R = R' ∧ M = M' := by
  simp only [hmsgPoint, Sum.inl.injEq, PublicHashQuery.hmsg.injEq, true_and]

/-- The state of the instrumented role run: the joint cache and the unconsumed tapes, the
position bookkeeping, and the hit set. -/
abbrev RoleState := AnswerTape.HitState (jointSpec core) (tapeClassRange core)

/-- A point is *covered* in a state of the instrumented run when it is cached and was either
first answered on the signer copy or hit by a fresh randomizer draw. -/
@[expose] def Covered (s : RoleState core) (p : (jointSpec core).Domain) : Prop :=
  s.1.1 p ≠ none ∧ (s.2.1.cls p = some .signer ∨ p ∈ s.2.2)

/-- A *frame query* of the role-tagged interface: neither a randomizer derivation nor of class
`signer`. -/
@[expose] def IsFrameQuery (t : (roleSpec core).Domain) : Prop :=
  ¬ IsRoleRandQuery core t ∧ AnswerTape.classOf (tapeClass core) t ≠ some .signer

/-- The invariant of the instrumented role run at signing key `pk` and signing log `log`: every
point of class `signer` is the `H_msg` point of a logged signature, and the `H_msg` point of
every logged signature and of every cached randomizer derivation is covered. -/
structure RunInv (pk : PublicKeyCore core)
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core)) (s : RoleState core) :
    Prop where
  /-- A point of class `signer` is the `H_msg` point of a logged signature. -/
  exists_mem_log : ∀ p, s.2.1.cls p = some .signer →
    ∃ en ∈ log, p = hmsgPoint core pk en.2.randomness en.1
  /-- The `H_msg` point of a logged signature is covered. -/
  covered_log : ∀ en ∈ log, Covered core s (hmsgPoint core pk en.2.randomness en.1)
  /-- The `H_msg` point at a cached randomizer derivation is covered. -/
  covered_rand : ∀ a M R, s.1.1 (.inr (.inr (a, M))) = some R →
    Covered core s (hmsgPoint core pk R M)

/-- The run invariant holds with the empty log on the empty cache, the empty bookkeeping and the
empty hit set. -/
theorem RunInv.init (pk : PublicKeyCore core)
    (L : (j : TapeClass) → List (tapeClassRange core j)) :
    RunInv core pk [] ((∅, L), (AnswerTape.ClassPos.init, ∅)) where
  exists_mem_log p hp := by simp at hp
  covered_log en hen := by simp at hen
  covered_rand a M R h := by simp at h

/-! ## Frame queries of the roles -/

/-- A role answers a program by a program of frame queries when the program makes no
`p`-query and every query the role sends outside the frame comes from a `p`-query. -/
theorem allQueriesSatisfy_simulateQ_roleImpl (r : Role) {α : Type}
    {oa : OracleComp (deriveSpec core) α} {p : (deriveSpec core).Domain → Prop} [DecidablePred p]
    (h : IsQueryBoundP oa p 0) (hp : ∀ t, ¬ IsFrameQuery core (roleQuery core r t) → p t) :
    AllQueriesSatisfy (simulateQ (roleImpl core r) oa) (IsFrameQuery core) := by
  classical
  exact (isQueryBoundP_zero_iff _ _).1 (isQueryBoundP_simulateQ_roleImpl core r h hp)

/-- A query the signer's role sends outside the frame comes from an `H_msg` query or a
randomizer derivation. -/
theorem isHmsgQuery_or_isRandQuery_of_not_isFrameQuery_roleQuery_signer
    (t : (deriveSpec core).Domain) (h : ¬ IsFrameQuery core (roleQuery core .signer t)) :
    IsHmsgQuery core t ∨ IsRandQuery core t := by
  by_contra hn
  refine h ⟨fun hr => hn (.inr ((isRoleRandQuery_roleQuery_iff core _ t).1 hr)), fun hc => ?_⟩
  exact hn (.inl ((classOf_roleQuery_eq_some_iff core .signer .signer t).1 hc).2)

/-- A query the forger's role sends outside the frame comes from a randomizer derivation. -/
theorem isRandQuery_of_not_isFrameQuery_roleQuery_forger (t : (deriveSpec core).Domain)
    (h : ¬ IsFrameQuery core (roleQuery core .forger t)) : IsRandQuery core t := by
  by_contra hn
  refine h ⟨fun hr => hn ((isRoleRandQuery_roleQuery_iff core _ t).1 hr), fun hc => ?_⟩
  exact absurd ((classOf_roleQuery_eq_some_iff core .forger .signer t).1 hc).1 nofun

/-! ## The events of a coverage witness -/

section Events

open SLHDSA.DigestTransport CanonicalGames

/-- The digest at a coverer slot, read off the forger tape `lF` and the signer tape `lS`: a slot
`inl s` is the signer-tape position `s`, and a slot `inr p` is the `p`-th forger-tape position
other than the target position `n`. -/
@[expose] def coverValue {qh qs : ℕ} (lF lS : List (Bytes vp.params.m)) (n : Fin (qh + 1)) :
    Fin qs ⊕ Fin qh → Option (Bytes vp.params.m)
  | .inl s => lS[(s : ℕ)]?
  | .inr p => lF[(n.succAbove p : ℕ)]?

/-- The tape event of the witness `(n, f)` on the two `H_msg` tapes: every digit `i` of the
target digest at forger position `n` is matched, leaf and digit, by the digest at coverer slot
`f i`. -/
@[expose] def TapeMatchOn {qh qs : ℕ} (w : Fin (qh + 1) × (Fin vp.params.k → Fin qs ⊕ Fin qh))
    (lF lS : List (Bytes vp.params.m)) : Prop :=
  ∀ i, ∃ dn dc : Bytes vp.params.m, lF[(w.1 : ℕ)]? = some dn ∧
    coverValue lF lS w.1 (w.2 i) = some dc ∧
    (coveringDigest vp dc).1 = (coveringDigest vp dn).1 ∧
    (coveringDigest vp dc).2 i = (coveringDigest vp dn).2 i

/-- The tape event of a witness on a tape family: `TapeMatchOn` on its forger and signer
tapes. -/
@[expose] def TapeMatch {qh qs : ℕ} (w : Fin (qh + 1) × (Fin vp.params.k → Fin qs ⊕ Fin qh))
    (L : (j : TapeClass) → List (tapeClassRange core j)) : Prop :=
  TapeMatchOn w (L .forger) (L .signer)

/-- The designated forger-tape positions of a witness: the forger-tape positions, other than the
target position, of its forger coverer slots. -/
@[expose] def desigPos {qh qs : ℕ} (w : Fin (qh + 1) × (Fin vp.params.k → Fin qs ⊕ Fin qh)) :
    Finset ℕ :=
  (Finset.univ.filter fun p : Fin qh => ∃ i, w.2 i = .inr p).image
    fun p => (w.1.succAbove p : ℕ)

/-- The tape lengths: `qh + 1` forger-side `H_msg` answers, `qs` signer-side ones, and no tape
for the other class. -/
@[expose] def tapeLength (qh qs : ℕ) : TapeClass → ℕ
  | .forger => qh + 1
  | .signer => qs
  | .other => 0

end Events

variable [SampleableType core.Y] [DecidableEq core.Y] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-! ## The instrumented run -/

/-- The instrumented role handler: the forwarded class-indexed tape oracle of the tape classes,
with the position bookkeeping and a hit set written at fresh randomizer draws. -/
noncomputable abbrev roleRunImpl : QueryImpl (roleSpec core) (StateT (RoleState core) ProbComp) :=
  AnswerTape.classPosImplFwd (tapeClassRange core) (tapeClass core)
    (range_eq_tapeClassRange core) (AnswerTape.freshHitAux (IsRandPoint core) (randRel core))

/-- The instrumented role run of the forger `adv` at public seed `pkSeed` on the tape family
`L`, from the empty cache, the empty bookkeeping and the empty hit set. -/
noncomputable abbrev roleRun [SampleableType core.SkSeed] [SampleableType core.SkPrf]
    {e : core.SkSeed ≃ core.Y} {optRand : PublicKeyCore core → ProbComp core.Y}
    {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) (pkSeed : core.PkSeed)
    (L : (j : TapeClass) → List (tapeClassRange core j)) :
    ProbComp (DeriveOutcome core × RoleState core) :=
  (simulateQ (roleRunImpl core) (roleExperiment core adv pkSeed)).run
    ((∅, L), (AnswerTape.ClassPos.init, ∅))

/-! ## One step of the instrumented run -/

section Step

variable {core}

/-- A tape step caches its answer at the queried point and changes the cache nowhere else. -/
private theorem cache_of_mem_support_tapeStep_run {j : TapeClass} {x : (jointSpec core).Domain}
    {h : (jointSpec core).Range x = tapeClassRange core j}
    {s : (jointSpec core).QueryCache × ((j : TapeClass) → List (tapeClassRange core j))}
    {y : (jointSpec core).Range x ×
      ((jointSpec core).QueryCache × ((j : TapeClass) → List (tapeClassRange core j)))}
    (hy : y ∈ support
      ((AnswerTape.tapeStep (spec := jointSpec core) (tapeClassRange core) j x h).run s)) :
    y.2.1 x = some y.1 ∧ (∀ p, p ≠ x → y.2.1 p = s.1 p) := by
  obtain ⟨c, L⟩ := s
  rcases hc : c x with _ | u₀
  · rcases hL : L j with _ | ⟨u, l⟩
    · rw [AnswerTape.tapeStep_run_nil hc hL, support_map] at hy
      obtain ⟨u, -, rfl⟩ := hy
      exact ⟨QueryCache.cacheQuery_self _ _ _, fun p hp => QueryCache.cacheQuery_of_ne _ _ hp⟩
    · rw [AnswerTape.tapeStep_run_cons hc hL, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨QueryCache.cacheQuery_self _ _ _, fun p hp => QueryCache.cacheQuery_of_ne _ _ hp⟩
  · rw [AnswerTape.tapeStep_run_some hc, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨hc, fun _ _ => rfl⟩

omit [SampleableType core.Y] in
/-- The class bookkeeping of a tape step gives a freshly queried point the class of the step and
keeps the class of every other point. -/
private theorem classPosStep_cls {j : TapeClass} {x : (jointSpec core).Domain}
    (s s' : (jointSpec core).QueryCache × ((j : TapeClass) → List (tapeClassRange core j)))
    (u : (jointSpec core).Range x) (q : AnswerTape.ClassPos (jointSpec core).Domain TapeClass)
    (p : (jointSpec core).Domain) :
    (AnswerTape.classPosStep (tapeClassRange core) j x s u s' q).cls p =
      if p = x ∧ s.1 x = none then some j else q.cls p := by
  obtain ⟨c, L⟩ := s
  rcases hc : c x with _ | u₀
  · rcases hL : L j with _ | ⟨v, l⟩
    · by_cases hpx : p = x
      · subst hpx; simp [AnswerTape.classPosStep_of_nil hc hL]
      · simp [AnswerTape.classPosStep_of_nil hc hL, hpx]
    · by_cases hpx : p = x
      · subst hpx; simp [AnswerTape.classPosStep_of_cons hc hL]
      · simp [AnswerTape.classPosStep_of_cons hc hL, hpx]
  · simp [AnswerTape.classPosStep_of_some hc]

variable {t : (roleSpec core).Domain} {s : RoleState core}
  {y : (roleSpec core).Range t × RoleState core}

/-- A step changes the cache and the class of a point only by querying it, on either copy, and
the class only if the point was uncached; a fresh point takes the class of its query. -/
theorem cache_cls_of_mem_support_roleRunImpl_run (hy : y ∈ support ((roleRunImpl core t).run s))
    (p : (jointSpec core).Domain) :
    ((∀ x, (t = .inr (.inl x) ∨ t = .inr (.inr x)) → x ≠ p) → y.2.1.1 p = s.1.1 p) ∧
    (¬ ((t = .inr (.inl p) ∨ t = .inr (.inr p)) ∧ s.1.1 p = none) →
      y.2.2.1.cls p = s.2.1.cls p) ∧
    ((t = .inr (.inl p) ∨ t = .inr (.inr p)) → s.1.1 p = none →
      y.2.2.1.cls p = AnswerTape.classOf (tapeClass core) t) := by
  obtain ⟨hv, hq⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ t s y).1 hy
  rw [hq]
  rcases t with n | (x | x)
  · simp only [AnswerTape.tapeImplFwd, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      StateT.run_monadLift, support_bind, support_pure, Set.mem_iUnion] at hv
    obtain ⟨u, -, hu⟩ := hv
    refine ⟨fun _ => by rw [(Prod.mk.inj (Set.mem_singleton_iff.mp hu)).2], fun _ => rfl, ?_⟩
    rintro (h | h) <;> cases h
  all_goals
    have hv' := cache_of_mem_support_tapeStep_run (by
      simpa [AnswerTape.tapeCachingImplClass_apply_inl, AnswerTape.tapeCachingImplClass_apply_inr]
        using hv)
    simp only [AnswerTape.classPosAuxFwd_inr, AnswerTape.classPosAux_inl,
      AnswerTape.classPosAux_inr, classPosStep_cls, Sum.inr.injEq, Sum.inl.injEq,
      reduceCtorEq, or_false, false_or, AnswerTape.classOf_inr]
    refine ⟨fun hp => hv'.2 p (hp x rfl).symm, fun hp => ite_eq_right_iff.2 fun h => absurd h ?_,
      fun h hc => ?_⟩
  · rintro ⟨rfl, hc⟩; exact hp ⟨rfl, hc⟩
  · subst h; simp [hc]
  · rintro ⟨rfl, hc⟩; exact hp ⟨rfl, hc⟩
  · subst h; simp [hc]

/-- A query of the signer copy at a point `x` caches its answer there. If `x` was uncached, it
takes the signer-copy class of `x`, and if `x` is moreover a randomizer derivation, every point
cached before the step that the answer hits joins the hit set. -/
theorem cache_cls_hits_of_mem_support_roleRunImpl_run_inr {x : (jointSpec core).Domain}
    {y : (roleSpec core).Range (.inr (.inr x)) × RoleState core}
    (hy : y ∈ support ((roleRunImpl core (.inr (.inr x))).run s)) :
    y.2.1.1 x = some y.1 ∧ (s.1.1 x = none →
      y.2.2.1.cls x = some (tapeClass core (.inr x)) ∧
        (IsRandPoint core x → ∀ p, s.1.1 p ≠ none → randRel core x y.1 p → p ∈ y.2.2.2)) := by
  obtain ⟨hv, hq⟩ := (QueryImpl.mem_support_extendState_run_iff _ _
    (Sum.inr (Sum.inr x) : (roleSpec core).Domain) s y).1 hy
  refine ⟨(cache_of_mem_support_tapeStep_run
      (by simpa [AnswerTape.tapeCachingImplClass_apply_inr] using hv)).1,
    fun hc => ⟨(cache_cls_of_mem_support_roleRunImpl_run hy x).2.2 (.inr rfl) hc,
      fun hx p hp hhit => ?_⟩⟩
  · rw [hq]
    change p ∈ AnswerTape.freshHitStep (IsRandPoint core) (randRel core) s.1.1 x y.1 s.2.2
    rw [AnswerTape.freshHitStep_of_eq_none _ _ hc hx]
    exact .inr ⟨hp, hhit⟩

end Step

/-! ## The run invariant -/

section Invariant

variable {core} {t : (roleSpec core).Domain}
  {s : RoleState core} {y : (roleSpec core).Range t × RoleState core}

/-- A covered point stays covered along a step. -/
theorem Covered.step {p : (jointSpec core).Domain} (hp : Covered core s p)
    (hy : y ∈ support ((roleRunImpl core t).run s)) : Covered core y.2 p := by
  obtain ⟨hle, hcls, hsub, -⟩ := AnswerTape.mono_of_mem_support_classPosImplFwd_run _ _ _ _ _ _ _ hy
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hp.1
  refine ⟨by rw [hle hv]; exact Option.some_ne_none v, ?_⟩
  rw [(hcls p hp.1).1]
  exact hp.2.imp_right fun h => hsub h

variable {pk : PublicKeyCore core}
  {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core)}

/-- A step at a frame query preserves the run invariant. -/
theorem RunInv.step (hI : RunInv core pk log s) (ht : IsFrameQuery core t)
    (hy : y ∈ support ((roleRunImpl core t).run s)) : RunInv core pk log y.2 where
  exists_mem_log p hp := by
    have hc := cache_cls_of_mem_support_roleRunImpl_run hy p
    by_cases hf : (t = .inr (.inl p) ∨ t = .inr (.inr p)) ∧ s.1.1 p = none
    · exact absurd ((hc.2.2 hf.1 hf.2).symm.trans hp) ht.2
    · exact hI.exists_mem_log p ((hc.2.1 hf).symm.trans hp)
  covered_log en hen := (hI.covered_log en hen).step hy
  covered_rand a M R h := by
    refine (hI.covered_rand a M R ?_).step hy
    rw [← (cache_cls_of_mem_support_roleRunImpl_run hy _).1 ?_, h]
    rintro x (rfl | rfl) rfl
    all_goals exact ht.1 trivial

/-- A run of a program making only frame queries preserves the run invariant. -/
theorem RunInv.run {α : Type} {oa : OracleComp (roleSpec core) α}
    (h : AllQueriesSatisfy oa (IsFrameQuery core)) (hI : RunInv core pk log s)
    {z : α × RoleState core} (hz : z ∈ support ((simulateQ (roleRunImpl core) oa).run s)) :
    RunInv core pk log z.2 :=
  h.holds_of_mem_support_run_simulateQ (RunInv core pk log)
    (fun _ ht _ hs _ hy => hs.step ht hy) hI hz

/-- **Signing preserves the run invariant.** A run of signing from a state satisfying the run
invariant at signing key `sk` ends in a state satisfying it with the signature logged: the
`H_msg` point at the derived randomizer is covered, by the fresh draw of the randomizer, by an
earlier signature that derived it, or by its own fresh query on the signer copy. -/
theorem RunInv.sign {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeed : core.PkSeed}
    {sk : PublicKeyCore core} {msg : List Byte} (hI : RunInv core sk log s)
    {z : GeneralScheme.SignatureCore vp core × RoleState core}
    (hz : z ∈ support ((simulateQ (roleRunImpl core)
      ((roleScheme core optRand pkSeed).sign pk sk msg)).run s)) :
    RunInv core sk (log ++ [⟨msg, z.1⟩]) z.2 := by
  simp only [roleScheme, deriveScheme_sign_eq, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hz
  obtain ⟨⟨addrnd, s₁⟩, h₁, ⟨R, s₂⟩, h₂, ⟨digest, s₃⟩, h₃, h₄⟩ := hz
  have h₂' : (R, s₂) ∈ support ((roleRunImpl core (.inr (.inr (.inr (.inr (addrnd, msg)))))).run
      s₁) := by
    simpa only [simulateQ_HasQuery_query, roleImpl, simulateQ_spec_query] using h₂
  have h₃' : (digest, s₃) ∈ support ((roleRunImpl core
      (.inr (.inr (hmsgPoint core sk R msg)))).run s₂) := by
    have e : simulateQ (roleImpl core .signer)
        (PublicHash.hmsg core R sk.pkSeed sk.pkRoot msg : OracleComp (deriveSpec core) _) =
        roleImpl core .signer (.inl (.inr (.inl (.hmsg R sk.pkSeed sk.pkRoot msg)))) := rfl
    simp only [e, roleImpl, simulateQ_spec_query] at h₃
    exact h₃
  have hsig := support_simulateQ_run'_subset (roleRunImpl core ∘ₛ roleImpl core .signer)
    (signTail core sk.pkSeed R digest) s₃ (by
      rw [StateT.run'_eq, support_map, QueryImpl.simulateQ_compose]; exact ⟨z, h₄, rfl⟩)
  have hrand : z.1.randomness = R := by
    simp only [signTail, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsig
    obtain ⟨_, _, _, _, _, _, h⟩ := hsig
    rw [h]
  have hI₁ : RunInv core sk log s₁ := hI.run (allQueriesSatisfy_simulateQ_roleImpl core .signer
    (isQueryBoundP_liftM_withDerivations (fun _ h => h.elim id id) _)
    (isHmsgQuery_or_isRandQuery_of_not_isFrameQuery_roleQuery_signer core)) h₁
  obtain ⟨hR₂, hfresh₂⟩ := cache_cls_hits_of_mem_support_roleRunImpl_run_inr h₂'
  obtain ⟨hD₃, hfresh₃⟩ := cache_cls_hits_of_mem_support_roleRunImpl_run_inr h₃'
  have hle₂ := (AnswerTape.mono_of_mem_support_classPosImplFwd_run _ _ _ _ _ _ _ h₂').1
  have hne₂ : ∀ p : (jointSpec core).Domain, p ≠ .inr (.inr (addrnd, msg)) →
      s₂.1.1 p = s₁.1.1 p ∧ (s₁.1.1 p = none → s₂.2.1.cls p = s₁.2.1.cls p) := fun p hp =>
    have hc := cache_cls_of_mem_support_roleRunImpl_run h₂' p
    ⟨hc.1 (by rintro q (hq | hq) rfl <;> cases hq; exact hp rfl),
      fun _ => hc.2.1 (by rintro ⟨hq | hq, -⟩ <;> cases hq; exact hp rfl)⟩
  have key₂ : s₂.1.1 (hmsgPoint core sk R msg) ≠ none →
      Covered core s₂ (hmsgPoint core sk R msg) := by
    intro hne
    rcases hx : s₁.1.1 (.inr (.inr (addrnd, msg))) with _ | R'
    · have hh : s₁.1.1 (hmsgPoint core sk R msg) ≠ none := by
        rwa [← (hne₂ _ (by simp [hmsgPoint])).1]
      exact ⟨hne, .inr ((hfresh₂ hx).2 trivial _ hh ⟨rfl, rfl⟩)⟩
    · obtain rfl : R' = R := Option.some_inj.1 ((hle₂ hx).symm.trans hR₂)
      exact (hI₁.covered_rand addrnd msg R' hx).step h₂'
  have hcov₃ : Covered core s₃ (hmsgPoint core sk R msg) := by
    rcases hc : s₂.1.1 (hmsgPoint core sk R msg) with _ | d
    · exact ⟨by rw [hD₃]; exact Option.some_ne_none _, .inl (hfresh₃ hc).1⟩
    · exact (key₂ (by rw [hc]; exact Option.some_ne_none _)).step h₃'
  have hne₃ : ∀ p : (jointSpec core).Domain, p ≠ hmsgPoint core sk R msg →
      s₃.1.1 p = s₂.1.1 p ∧ s₃.2.1.cls p = s₂.2.1.cls p := fun p hp =>
    have hc := cache_cls_of_mem_support_roleRunImpl_run h₃' p
    ⟨hc.1 (by rintro q (hq | hq) rfl <;> cases hq; exact hp rfl),
      hc.2.1 (by rintro ⟨hq | hq, -⟩ <;> cases hq; exact hp rfl)⟩
  refine RunInv.run (allQueriesSatisfy_simulateQ_roleImpl core .signer
    (isQueryBoundP_signTail core _ _ _)
    (isHmsgQuery_or_isRandQuery_of_not_isFrameQuery_roleQuery_signer core))
    ⟨fun p hp => ?_, fun en hen => ?_, fun a M R'' h => ?_⟩ h₄
  · by_cases hp₃ : p = hmsgPoint core sk R msg
    · exact ⟨⟨msg, z.1⟩, by simp, by rw [hp₃, hrand]⟩
    rw [(hne₃ p hp₃).2] at hp
    have hp₁ : s₁.2.1.cls p = some .signer := by
      rcases (cache_cls_of_mem_support_roleRunImpl_run h₂' p) with ⟨-, h₁, h₂⟩
      by_cases hf : ((Sum.inr (Sum.inr (Sum.inr (Sum.inr (addrnd, msg)))) : (roleSpec core).Domain)
          = .inr (.inl p) ∨ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (addrnd, msg)))) :
            (roleSpec core).Domain) = .inr (.inr p)) ∧ s₁.1.1 p = none
      · have hcls := hp.symm.trans (h₂ hf.1 hf.2)
        rcases hf with ⟨hq | hq, -⟩ <;> cases hq
        simp [AnswerTape.classOf, tapeClass] at hcls
      · rwa [← h₁ hf]
    obtain ⟨en, hen, rfl⟩ := hI₁.exists_mem_log p hp₁
    exact ⟨en, List.mem_append_left _ hen, rfl⟩
  · rcases List.mem_append.1 hen with hen | hen
    · exact ((hI₁.covered_log en hen).step h₂').step h₃'
    · obtain rfl : en = ⟨msg, z.1⟩ := List.mem_singleton.1 hen
      simpa only [hrand] using hcov₃
  · rw [(hne₃ _ (by simp [hmsgPoint])).1] at h
    by_cases hx : (a, M) = (addrnd, msg)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
      obtain rfl : R'' = R := Option.some_inj.1 (h.symm.trans hR₂)
      exact hcov₃
    · rw [(hne₂ _ (by simpa using hx)).1] at h
      exact ((hI₁.covered_rand a M R'' h).step h₂').step h₃'

end Invariant

/-! ## The run -/

section Experiment

variable {core} [SampleableType core.SkSeed] [SampleableType core.SkPrf]
  {e : core.SkSeed ≃ core.Y} {optRand : PublicKeyCore core → ProbComp core.Y}
  {pkSeedDist : ProbComp core.PkSeed}

omit [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf] in
/-- The forger of the role experiment makes only frame queries: its hash queries go to the forger
copy, and the lifted forger makes no derivation query. -/
theorem allQueriesSatisfy_roleExperiment_main
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) (pkSeed : core.PkSeed)
    (pk : PublicKeyCore core) :
    AllQueriesSatisfy (((deriveAdversary core adv pkSeed).mapOracles (roleImpl core .forger)
        (sigAlg' := roleScheme core optRand pkSeed)).main pk)
      (Sum.elim (IsFrameQuery core) fun _ => True) := by
  classical
  rw [UnforgeableAdversary.mapOracles_main]
  refine (allQueriesSatisfy_deriveAdversary_main core adv pkSeed pk).simulateQ ?_
  rintro ((u | x) | m) ht
  · simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply]
    refine (isQueryBoundP_zero_iff _ _).1 (IsQueryBoundP.liftComp_subSpec
      (p := fun t => ¬ IsFrameQuery core t) (fun _ => Iff.rfl) ?_)
    exact (isQueryBoundP_roleImpl_iff core .forger (.inl u)).2 fun h =>
      (isRandQuery_of_not_isFrameQuery_roleQuery_forger core _ h).elim
  · cases ht
  · simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply]
    exact (isQueryBoundP_zero_iff _ _).1 (IsQueryBoundP.liftComp_subSpec (p := fun _ => False)
      (fun _ => iff_of_false not_false (not_not_intro trivial)) (by simp))

variable {adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)} {pkSeed : core.PkSeed}
  {L : (j : TapeClass) → List (tapeClassRange core j)} {z : DeriveOutcome core × RoleState core}

/-- On every instrumented role run the signing key is the public key, and the run invariant
holds at the final signing log. -/
theorem runInv_of_mem_support_roleRun (hz : z ∈ support (roleRun core adv pkSeed L)) :
    z.1.pk = z.1.sk ∧ RunInv core z.1.sk z.1.log z.2 := by
  refine holds_of_mem_support_run_unforgeableTranscriptExperiment (roleRunImpl core)
    (allowed := IsFrameQuery core) (fun pk sk log s => pk = sk ∧ RunInv core sk log s)
    (fun y hy => ⟨?_, ?_⟩) (fun t ht _ _ _ _ h y hy => ⟨h.1, h.2.step ht hy⟩)
    (fun _ _ _ _ _ h y hy => ⟨h.1, h.2.sign hy⟩)
    (fun _ _ _ _ _ _ h y hy => ⟨h.1, h.2.run (allQueriesSatisfy_simulateQ_roleImpl core .forger
      (isQueryBoundP_deriveScheme_verify_rand core optRand pkSeed _ _ _)
      (isRandQuery_of_not_isFrameQuery_roleQuery_forger core)) hy⟩)
    _ (allQueriesSatisfy_roleExperiment_main adv pkSeed) hz
  · have hk := support_simulateQ_run'_subset (roleRunImpl core ∘ₛ roleImpl core .signer)
      (deriveScheme core optRand pkSeed).keygen _ (by
        rw [StateT.run'_eq, support_map, QueryImpl.simulateQ_compose]; exact ⟨y, hy, rfl⟩)
    simp only [deriveScheme, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hk
    obtain ⟨root, -, h⟩ := hk
    rw [h]
  · exact (RunInv.init _ _ L).run (allQueriesSatisfy_simulateQ_roleImpl core .signer
      (isQueryBoundP_deriveScheme_keygen_hmsg_rand core optRand pkSeed)
      (isHmsgQuery_or_isRandQuery_of_not_isFrameQuery_roleQuery_signer core)) hy

/-- **Signer-class points are logged.** On every instrumented role run, every point of class
`signer` is the `H_msg` point, under the public key, of a logged signature. -/
theorem exists_mem_log_of_cls_eq_signer (hz : z ∈ support (roleRun core adv pkSeed L))
    (p : (jointSpec core).Domain) (hp : z.2.2.1.cls p = some .signer) :
    ∃ en ∈ z.1.log, p = hmsgPoint core z.1.pk en.2.randomness en.1 := by
  obtain ⟨hpk, hI⟩ := runInv_of_mem_support_roleRun hz
  rw [hpk]
  exact hI.exists_mem_log p hp

/-- **Logged points are signer-class or hit.** On every instrumented role run, the `H_msg` point,
under the public key, of every logged signature is of class `signer` or in the hit set: it was
first queried by the signer, or a fresh draw of its randomizer hit it after it was cached. -/
theorem cls_eq_signer_or_mem_hits_of_mem_log (hz : z ∈ support (roleRun core adv pkSeed L))
    {en : (t : (List Byte →ₒ GeneralScheme.SignatureCore vp core).Domain) ×
      (List Byte →ₒ GeneralScheme.SignatureCore vp core).Range t} (hen : en ∈ z.1.log) :
    z.2.2.1.cls (hmsgPoint core z.1.pk en.2.randomness en.1) = some .signer ∨
      hmsgPoint core z.1.pk en.2.randomness en.1 ∈ z.2.2.2 := by
  obtain ⟨hpk, hI⟩ := runInv_of_mem_support_roleRun hz
  rw [hpk]
  exact (hI.covered_log en hen).2

end Experiment

/-! ## The event mapping -/

section EventMapping

open AnswerTape SLHDSA.DigestTransport CanonicalGames

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

/-- **The event mapping.** On the instrumented role run of a forger with hash budget `qh` and
signing budget `qs`, over a family drawn at the lengths `tapeLength qh qs`, coverage of a fresh
forgery yields a witness whose tape event holds of the family and whose run event holds of the
run. The forgery's `H_msg` point is not of class `signer`, since it would then be the point of a
logged signature on the forged message; so it sits at a forger-tape position `n`. Every FORS
digit of its digest is matched by a logged signature's digest, at a signer-tape position or at a
forger-tape position other than `n`, and in the second case the logged point is in the hit set,
since it is not of class `signer`. -/
theorem exists_witness_of_runItsrCovered {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    {adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) (pkSeed : core.PkSeed) (s : core.SkSeed × core.SkPrf)
    (L : (j : TapeClass) → List (tapeClassRange core j))
    (hL : L ∈ support (tapeFamily (tapeClassRange core) (tapeLength qh qs)))
    (z : DeriveOutcome core × RoleState core) (hz : z ∈ support (roleRun core adv pkSeed L))
    (hcov : RunItsrCovered core (DeriveOutcome.fill core s z.1, z.2.1.1.fst)) :
    ∃ w : Fin (qh + 1) × (Fin vp.params.k → Fin qs ⊕ Fin qh),
      TapeMatch core w L ∧ HitAll (randRel core) .forger (desigPos w) z.2 := by
  classical
  obtain ⟨⟨digest, hdig, hidx⟩, hfresh⟩ := hcov
  simp only [DeriveOutcome.fill, ForgerDigest, LoggedDigest, QueryCache.fst_apply] at hdig hidx
  rw [UnforgeableTranscript.mapSk_pk] at hdig hidx
  rw [UnforgeableTranscript.mapSk_sig, UnforgeableTranscript.mapSk_msg] at hdig
  rw [UnforgeableTranscript.mapSk_log] at hidx
  simp only [RunFresh, DeriveOutcome.fill, UnforgeableTranscript.mapSk_msg,
    UnforgeableTranscript.mapSk_log] at hfresh
  have hlen := length_of_mem_support_tapeFamily (tapeLength qh qs) hL
  have hF := cnt_le_of_isQueryBoundP (tapeClass core) (range_eq_tapeClassRange core)
    (freshHitAux (IsRandPoint core) (randRel core)) ∅ L _ .forger
    (isQueryBoundP_roleExperiment_forger core hadv pkSeed) hz
  have hS := cnt_le_of_isQueryBoundP (tapeClass core) (range_eq_tapeClassRange core)
    (freshHitAux (IsRandPoint core) (randRel core)) ∅ L _ .signer
    (isQueryBoundP_roleExperiment_signer core hadv pkSeed) hz
  obtain ⟨hpos, hinj⟩ := exists_pos_of_mem_support_run_classPosImplFwd (tapeClass core)
    (range_eq_tapeClassRange core) (freshHitAux (IsRandPoint core) (randRel core)) ∅ L _ hz
    {.forger, .signer} (by
      rintro j (rfl | rfl)
      · rw [hlen]; exact hF
      · rw [hlen]; exact hS)
  -- the target sits on the forger tape
  set tgt := hmsgPoint core z.1.pk z.1.sig.randomness z.1.msg
  obtain ⟨j₀, hcls₀, hj₀, hp₀⟩ := hpos tgt digest hdig
  have hj₀F : j₀ = .forger := by
    rcases hj₀ with h | h
    · exact h
    · obtain ⟨en, hen, heq⟩ := exists_mem_log_of_cls_eq_signer hz tgt (by rw [hcls₀, h]; rfl)
      exact absurd (List.mem_map.2 ⟨en, hen, ((hmsgPoint_inj core _).1 heq).2.symm⟩) hfresh
  subst hj₀F
  obtain ⟨n₀, hn₀, hn₀lt, _, hv₀⟩ := hp₀ (by simp)
  rw [hlen] at hn₀lt
  set n : Fin (qh + 1) := ⟨n₀, hn₀lt⟩
  -- every digit has a coverer slot
  have key : ∀ i : Fin vp.params.k, ∃ c : Fin qs ⊕ Fin qh, ∃ dc : Bytes vp.params.m,
      coverValue (L .forger) (L .signer) n c = some dc ∧
      (coveringDigest vp dc).1 = (coveringDigest vp digest).1 ∧
      (coveringDigest vp dc).2 i = (coveringDigest vp digest).2 i ∧
      ∀ p, c = .inr p → HitCleared .forger z.2 (n.succAbove p) ∧
        ∀ t, z.2.2.1.cls t = some .forger → z.2.2.1.pos t = some (n.succAbove p) →
          ∃ R M, t = hmsgPoint core z.1.pk R M := by
    intro i
    obtain ⟨en, hen, d', hd', hmem⟩ := hidx
      ⟨(splitDigest vp.params digest).idxTree, (splitDigest vp.params digest).idxLeaf, i,
        ⟨forsIdx vp.params (splitDigest vp.params digest).md.toList i.val, forsIdx_lt _ _ _⟩⟩
      ((mem_hmsgIndices _ _ _).2 ⟨rfl, rfl, rfl⟩)
    obtain ⟨hm1, hm2⟩ := coveringDigest_match_of_mem_hmsgIndices vp digest d' i hmem
    set ti := hmsgPoint core z.1.pk en.2.randomness en.1
    have hne : ti ≠ tgt := fun h =>
      hfresh (List.mem_map.2 ⟨en, hen, ((hmsgPoint_inj core _).1 h).2⟩)
    obtain ⟨j, hclsj, hj, hpj⟩ := hpos ti d' hd'
    rcases hj with hj | hj
    · -- forger tape: a position other than the target's, and a hit
      rw [show tapeClass core (Sum.inl ti) = .forger from rfl] at hj
      subst hj
      obtain ⟨ni, hni, hnilt, _, hvi⟩ := hpj (by simp)
      rw [hlen] at hnilt
      have hneq : (⟨ni, hnilt⟩ : Fin (qh + 1)) ≠ n := fun h =>
        hne (hinj ti tgt _ ni hclsj hni hcls₀
          (by rw [hn₀]; exact congrArg (some ∘ Fin.val) h.symm))
      obtain ⟨p, hp⟩ := Fin.exists_succAbove_eq hneq
      refine ⟨.inr p, d', ?_, hm1, hm2, fun p' hp' => ?_⟩
      · simp only [coverValue, hp]
        exact hvi.trans (by rfl)
      · cases hp'
        refine ⟨⟨ti, hclsj, by rw [hp]; exact hni, ?_⟩, fun t hc hpos =>
          ⟨_, _, hinj t ti _ _ hc hpos hclsj (by rw [hp]; exact hni)⟩⟩
        rcases cls_eq_signer_or_mem_hits_of_mem_log hz hen with h | h
        · rw [hclsj] at h; cases h
        · exact h
    · -- signer tape
      rw [show tapeClass core (Sum.inr ti) = .signer from rfl] at hj
      subst hj
      obtain ⟨ni, hni, hnilt, _, hvi⟩ := hpj (by simp)
      rw [hlen] at hnilt
      refine ⟨.inl ⟨ni, hnilt⟩, d', ?_, hm1, hm2, fun p' hp' => by cases hp'⟩
      simp only [coverValue]
      exact hvi.trans (by rfl)
  choose f dc hf using key
  have hmem : ∀ q, q ∈ desigPos (qs := qs) (n, f) →
      ∃ p, (∃ i, f i = .inr p) ∧ (n.succAbove p : ℕ) = q := fun q hq => by
    simpa [desigPos] using hq
  refine ⟨(n, f), fun i => ⟨digest, dc i, hv₀.trans (by rfl), (hf i).1, (hf i).2.1,
    (hf i).2.2.1⟩, fun q hq => ?_, fun t t' q q' hq hq' hc hp hc' hp' x u hr hr' => ?_⟩
  · obtain ⟨p, ⟨i, hi⟩, rfl⟩ := hmem q hq
    exact ((hf i).2.2.2 p hi).1
  · obtain ⟨p, ⟨i, hi⟩, rfl⟩ := hmem q hq
    obtain ⟨p', ⟨i', hi'⟩, rfl⟩ := hmem q' hq'
    obtain ⟨R, M, rfl⟩ := ((hf i).2.2.2 p hi).2 t hc hp
    obtain ⟨R', M', rfl⟩ := ((hf i').2.2.2 p' hi').2 t' hc' hp'
    rcases x with ((x | x) | (k | ⟨a, Mx⟩))
    iterate 3 exact hr.elim
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨rfl, rfl⟩ := hr'
    rfl

end EventMapping

end SLHDSA.Security.Coverage
