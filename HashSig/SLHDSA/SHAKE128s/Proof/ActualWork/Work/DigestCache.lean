/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Signing
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Signing
public import HashSig.SLHDSA.Security.PrfKeyBound
import all HashSig.SLHDSA.Security.NativeRelative
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Verification
import all HashSig.SLHDSA.Security.NativeCounts

/-! # Digest cache cardinality along a marked execution -/

public section

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.CacheCardinality
open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open Guarded VerificationOffsets SigningCounts

/-- Native public presence grows only at the supplied point, under the actual roles. -/
private theorem native_lab_domain_footprint
    (s : FIPS205.core.PkSeed) (input : Lab.Domain)
    (state : CoverageDeferred.S FIPS205.core) (role : Coverage.RoleState FIPS205.core) :
    let pointOf : Lab.Domain → Option H.Domain :=
      Sum.elim (Sum.elim (Sum.elim (fun _ => none) some) (fun _ => none)) (fun _ => none)
    ∀ out ∈ support ((simulateQ (Coverage.roleRunImpl FIPS205.core)
      ((CoverageDeferred.relative FIPS205.core s (metadataCost true s)
        (.inl input)).run state)).run role),
      {query | (state.1.1.1 query).isSome} ⊆ {query | (out.1.2.1.1.1 query).isSome} ∧
      ({query | (out.1.2.1.1.1 query).isSome} ⊆
        {query | (state.1.1.1 query).isSome} ∪ {query | pointOf input = some query}) ∧
      out.1.2.2 = state.2 := by
  classical
  dsimp only
  intro out hout
  let roles := Coverage.roleRunImpl FIPS205.core
  let relative := CoverageDeferred.relative FIPS205.core s (metadataCost true s)
  let pointOf : Lab.Domain → Option H.Domain :=
    Sum.elim (Sum.elim (Sum.elim (fun _ => none) some) (fun _ => none)) (fun _ => none)
  have hsource : out.1 ∈ support ((relative (.inl input)).run state) := by
    apply support_simulateQ_run'_subset roles _ role
    rw [StateT.run'_eq, support_map]
    exact ⟨out, hout, rfl⟩
  have ordinary (other : ¬CoverageDeferred.IsSelectedNative FIPS205.core input) :
      {query | (state.1.1.1 query).isSome} ⊆ {query | (out.1.2.1.1.1 query).isSome} ∧
      ({query | (out.1.2.1.1.1 query).isSome} ⊆
        {query | (state.1.1.1 query).isSome} ∪ {query | pointOf input = some query}) ∧
      out.1.2.2 = state.2 := by
    have eq := CoverageDeferred.relative_other FIPS205.core s (metadataCost true s)
      input other state
    rw [eq, mem_support_bind_iff] at hsource
    obtain ⟨middle, hm, hreturn⟩ := hsource
    simp only [support_pure, Set.mem_singleton_iff] at hreturn
    have hgraph := mem_support_of_mem_support_liftComp (Coverage.roleSpec FIPS205.core) _ _ hm
    have monotone := (slhGraph FIPS205.core s).le_of_mem_support_deferredImpl hgraph
    have footprint := (slhGraph FIPS205.core s).deferredImpl_cachesOnlyQueryPoint
      input state.1 middle hgraph
    rw [hreturn]
    exact ⟨fun query present => QueryCache.isSome_mono monotone.1 present, footprint, rfl⟩
  rcases input with (((sample | (hash | prf)) | (secret | nonce)) | (touch | node))
  · exact ordinary (by simp [CoverageDeferred.IsSelectedNative])
  · cases hash with
    | thash seed key values => exact ordinary (by simp [CoverageDeferred.IsSelectedNative])
    | hmsg randomness seed root message =>
      rw [CoverageDeferred.relative_hmsg, mem_support_bind_iff] at hsource
      obtain ⟨digest, _, hreturn⟩ := hsource
      simp only [support_pure, Set.mem_singleton_iff] at hreturn
      rw [hreturn]
      refine ⟨?_, ?_, rfl⟩
      · intro query present
        exact (QueryCache.isSome_cacheQuery_apply_iff _ _).2 (Or.inr present)
      · intro query present
        rcases (QueryCache.isSome_cacheQuery_apply_iff _ _).1 present with same | old
        · exact Or.inr (congrArg some same.symm)
        · exact Or.inl old
  · exact ordinary (by simp [CoverageDeferred.IsSelectedNative])
  · exact ordinary (by simp [CoverageDeferred.IsSelectedNative])
  · rcases nonce with ⟨salt, message⟩
    rw [CoverageDeferred.relative_rand, support_map] at hsource
    obtain ⟨answer, _, shape⟩ := hsource
    rw [← shape]
    exact ⟨fun _ present => present, Set.subset_union_left, rfl⟩
  · exact ordinary (by simp [CoverageDeferred.IsSelectedNative])
  · exact ordinary (by simp [CoverageDeferred.IsSelectedNative])

private abbrev digests (cache : H.QueryCache) : Set H.Domain :=
  {q | (cache q).isSome ∧ IsHmsgPoint (vp := FIPS205.params) (core := FIPS205.core) q}

private abbrev joint := CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core

private abbrev bound (st : joint) :=
  (digests st.1.1.1.1).encard ≤ (st.2.2.1.cnt .signer + st.2.2.1.cnt .forger : Nat)

private theorem card_step (s : FIPS205.core.PkSeed) (input : (Lab + O).Domain) (before : joint)
    (prior : bound before) (z : (Lab + O).Range input × joint)
    (h : z ∈ support ((NativeCounts.nativeImpl FIPS205.core s (metadataCost true s) input).run
      before)) : bound z.2 := by
  rw [NativeCounts.nativeImpl, QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at h
  obtain ⟨out, hout, rfl⟩ := h
  cases input with
  | inr e =>
    rw [CoverageDeferred.relative_marker, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hout
    subst out
    exact prior
  | inl n =>
    let pointOf : Lab.Domain → Option H.Domain :=
      Sum.elim (Sum.elim (Sum.elim (fun _ => none) some) (fun _ => none)) (fun _ => none)
    have footprint := (native_lab_domain_footprint s n before.1 before.2 out hout).2.1
    have mono (j : Coverage.TapeClass) : before.2.2.1.cnt j ≤ out.2.2.1.cnt j := by
      apply simulateQ_run_preserves_inv_of_query (Coverage.roleRunImpl FIPS205.core)
        (fun st => before.2.2.1.cnt j ≤ st.2.1.cnt j) _ _ before.2 le_rfl out hout
      intro query st hs res hr
      rw [NativeCounts.native_cnt_step FIPS205.core query st res hr j]
      exact hs.trans (Nat.le_add_right _ _)
    have ordinary (miss : ∀ p, pointOf n = some p → ¬IsHmsgPoint p) :
        bound (out.1.2, out.2) := by
      have sub : digests out.1.2.1.1.1 ⊆ digests before.1.1.1.1 := by
        intro point present
        rcases footprint present.1 with old | fresh
        · exact ⟨old, present.2⟩
        · exact (miss point fresh present.2).elim
      exact (Set.encard_le_encard sub).trans (prior.trans (by
        exact_mod_cast Nat.add_le_add (mono .signer) (mono .forger)))
    rcases n with (((sample | (hash | prf)) | (secret | rand)) | label)
    · exact ordinary (by simp [pointOf, IsHmsgPoint])
    · cases hash with
      | thash seed addr inputs => exact ordinary (by simp [pointOf, IsHmsgPoint])
      | hmsg randomness seed root message =>
        rw [CoverageDeferred.relative_hmsg] at hout
        cases phase : before.1.2.2 <;> simp only [phase, CoverageDeferred.phaseRole,
          Coverage.roleImpl, simulateQ_map, StateT.run_map, simulateQ_spec_query,
          bind_pure_comp, support_map] at hout
        all_goals
          obtain ⟨one, hone, rfl⟩ := hout
          have sCount := NativeCounts.native_cnt_step FIPS205.core _ before.2 _ hone .signer
          have fCount := NativeCounts.native_cnt_step FIPS205.core _ before.2 _ hone .forger
          have unit : one.2.2.1.cnt .signer + one.2.2.1.cnt .forger =
              before.2.2.1.cnt .signer + before.2.2.1.cnt .forger + 1 := by
            simp [Coverage.tapeClass, AnswerTape.classOf] at sCount fCount
            omega
          let p : H.Domain := .inl (.hmsg randomness seed root message)
          have sub : digests (before.1.1.1.1.cacheQuery p one.1) ⊆
              insert p (digests before.1.1.1.1) := by
            intro t ht
            exact ((QueryCache.isSome_cacheQuery_apply_iff _ _).mp ht.1).imp id
              (fun old => ⟨old, ht.2⟩)
          have card := (Set.encard_le_encard sub).trans (Set.encard_insert_le _ p)
          change (digests (before.1.1.1.1.cacheQuery p one.1)).encard ≤
            (one.2.2.1.cnt .signer + one.2.2.1.cnt .forger : Nat)
          rw [unit, Nat.cast_add, Nat.cast_one]
          exact card.trans (add_le_add prior (le_refl 1))
    all_goals exact ordinary (by simp [pointOf, IsHmsgPoint])

/-- The complete typed message-digest cache is covered by the two actual native counts. -/
theorem whole_digest_cache_card (s : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK) (caps : Nat × Nat)
    (fallback : (i : LabCommon.Domain) → LabCommon.Range i)
    (family : (j : Coverage.TapeClass) → List (Coverage.tapeClassRange FIPS205.core j))
    (out : Result Full)
    (mem : out ∈ support (SLHDSA.SHAKE128s.MarkedPrefix.wholeRun s adv caps fallback
      (((∅, ∅), []), (0, .keygen)) family)) :
    {p | (out.1.2.1.1.1 p).isSome ∧ IsHmsgPoint (vp := FIPS205.params)
        (core := FIPS205.core) p}.encard ≤
          (out.2.2.1.cnt .signer + out.2.2.1.cnt .forger : Nat) := by
  let rel : CoverageDeferred.S FIPS205.core := (((∅, ∅), []), (0, .keygen))
  let role : Coverage.RoleState FIPS205.core := ((∅, family), (AnswerTape.ClassPos.init, ∅))
  let source := guardedRoutedSource s adv true caps fallback
  let native := NativeCounts.nativeImpl FIPS205.core s (metadataCost true s)
  have flatten : SLHDSA.SHAKE128s.MarkedPrefix.wholeRun s adv caps fallback rel family =
      (fun v => ((v.1, v.2.1), v.2.2)) <$> (simulateQ native source).run (rel, role) := by
    rw [SLHDSA.SHAKE128s.MarkedPrefix.wholeRun, SLHDSA.SHAKE128s.MarkedPrefix.wholeRoleProgram,
      simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  rw [flatten, support_map] at mem
  obtain ⟨v, hv, rfl⟩ := mem
  exact simulateQ_run_preserves_inv_of_query native bound (card_step s) source (rel, role)
    (by simp [bound, digests, rel, role, AnswerTape.ClassPos.init]) v hv

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.CacheCardinality

open SLHDSA.SHAKE128s.Bridge.SharedExperiment.CacheCardinality
