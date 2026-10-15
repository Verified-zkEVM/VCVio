/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import Examples.PRFTagReader.Collision

/-!
# PRF Tag/Reader Protocol — Bad-Event Bound

The bad-event world for the multiple-session unlinkability game, which records nonce collisions
across repeated sessions of a tag. Proves the per-step bad-event bounds and the overall session
collision bound `unlinkBadExperiment_le_sessionCollisionBound`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section Theorems

variable {TagId Nonce Digest K : Type} {sessionsPerTag : ℕ}

/-- The number of still-available successful tag sessions in a bad-event state. -/
def unlinkBadRemaining [Fintype TagId] (st : UnlinkBadState TagId Nonce Digest) : ℕ :=
  (Finset.univ : Finset TagId).sum fun tag => sessionsPerTag - st.sessionsUsed tag

/-- Reachable bad-event states only cache nonces that came from successful tag sessions. For each
tag, we retain a finite witness set of cached nonces whose size is bounded by that tag's session
counter. -/
def unlinkBadCacheBounded (st : UnlinkBadState TagId Nonce Digest) : Prop :=
  ∀ tag : TagId, ∃ nonces : Finset Nonce,
    nonces.card ≤ st.sessionsUsed tag ∧
      ∀ nonce : Nonce, (st.responses (tag, nonce)).isSome = true → nonce ∈ nonces

/-- State produced by a successful `RF_bad` tag query after sampling `nonce` and `auth`. -/
def unlinkBadTagNext [DecidableEq TagId] [DecidableEq Nonce]
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (nonce : Nonce) (auth : Digest) : UnlinkBadState TagId Nonce Digest :=
  { sessionsUsed := Function.update st.sessionsUsed tag (st.sessionsUsed tag + 1)
    responses := st.responses.cacheQuery (tag, nonce)
      (auth :: Option.getD (st.responses (tag, nonce)) [])
    bad := st.bad || (st.responses (tag, nonce)).isSome
    cacheBad := st.cacheBad }

/-- The initial state satisfies `unlinkBadCacheBounded`: the response cache is empty, so the empty
witness set trivially bounds each tag's nonce count. -/
lemma unlinkBadCacheBounded_init :
    unlinkBadCacheBounded
      (UnlinkBadState.init (TagId := TagId) (Nonce := Nonce) (Digest := Digest)) := by
  refine fun tag => ⟨∅, by simp [UnlinkBadState.init], ?_⟩
  intro nonce hcached
  simp [UnlinkBadState.init] at hcached

/-- The `unlinkBadReaderQueryImpl` does not modify the state. -/
private lemma unlinkBadReaderQueryImpl_state_eq [Fintype TagId] [DecidableEq Digest]
    (transcript : TagTranscript Nonce Digest)
    (st : UnlinkBadState TagId Nonce Digest) :
    ∀ z ∈ support ((unlinkBadReaderQueryImpl transcript).run st), z.2 = st := by
  intro z hz
  unfold unlinkBadReaderQueryImpl at hz
  simpa using congrArg Prod.snd hz

/-- If any tag still has a free slot, the total remaining budget is positive. Used to justify
the `- 1` arithmetic in `unlinkBadRemaining_tagNext`. -/
lemma unlinkBadRemaining_pos_of_slot [Fintype TagId]
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag) :
    0 < unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st :=
  lt_of_lt_of_le (Nat.sub_pos_of_lt hslot) (by
    simpa [unlinkBadRemaining] using Finset.single_le_sum (s := (Finset.univ : Finset TagId))
      (f := fun tag' => sessionsPerTag - st.sessionsUsed tag')
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ tag))

variable [DecidableEq TagId] [DecidableEq Nonce]

/-- `unlinkBadCacheBounded` is preserved by a successful tag step: the new nonce is added to the
witness set, keeping its cardinality within the incremented session counter. -/
lemma unlinkBadTagNext_cacheBounded
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (nonce : Nonce) (auth : Digest)
    (hbounded : unlinkBadCacheBounded st) :
    unlinkBadCacheBounded (unlinkBadTagNext tag st nonce auth) := by
  intro tag'
  obtain ⟨S, hScard, hS⟩ := hbounded tag'
  by_cases htag : tag' = tag
  · subst tag'
    refine ⟨insert nonce S, ?_, ?_⟩
    · simpa [unlinkBadTagNext] using
        (Finset.card_insert_le nonce S).trans (by omega : S.card + 1 ≤ st.sessionsUsed tag + 1)
    · intro nonce' hcached
      by_cases hkey : (tag, nonce') = (tag, nonce)
      · simp only [Prod.mk.injEq, true_and] at hkey
        subst nonce'
        exact Finset.mem_insert_self nonce S
      · exact Finset.mem_insert_of_mem (hS nonce' (by
          simpa [unlinkBadTagNext, QueryCache.cacheQuery_of_ne _ _ hkey] using hcached))
  · refine ⟨S, ?_, ?_⟩
    · simpa [unlinkBadTagNext, Function.update_of_ne htag] using hScard
    · intro nonce' hcached
      have hkey : (tag', nonce') ≠ (tag, nonce) := fun h => htag (Prod.ext_iff.mp h).1
      exact hS nonce' (by
        simpa [unlinkBadTagNext, QueryCache.cacheQuery_of_ne _ _ hkey] using hcached)

/-- A successful tag step does not push any tag's session counter above `sessionsPerTag`,
preserving the `sessionsUsed ≤ sessionsPerTag` invariant needed by the induction. -/
lemma unlinkBadTagNext_sessionsUsed_le
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (nonce : Nonce) (auth : Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag)
    (hused : ∀ tag, st.sessionsUsed tag ≤ sessionsPerTag) :
    ∀ tag', (unlinkBadTagNext tag st nonce auth).sessionsUsed tag' ≤ sessionsPerTag := by
  intro tag'
  by_cases htag : tag' = tag
  · subst htag
    simp [unlinkBadTagNext, Function.update_self]
    omega
  · simpa [unlinkBadTagNext, Function.update_of_ne htag] using hused tag'

/-- A successful tag step decrements `unlinkBadRemaining` by exactly 1, which is the key
step in the union-bound induction. -/
lemma unlinkBadRemaining_tagNext [Fintype TagId]
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (nonce : Nonce) (auth : Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag) :
    unlinkBadRemaining (sessionsPerTag := sessionsPerTag)
        (unlinkBadTagNext tag st nonce auth) =
      unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 := by
  let remainingAt : TagId → ℕ := fun tag' => sessionsPerTag - st.sessionsUsed tag'
  have hpos : 0 < remainingAt tag := Nat.sub_pos_of_lt hslot
  have hpoint :
      (fun tag' : TagId =>
        sessionsPerTag -
          (unlinkBadTagNext tag st nonce auth).sessionsUsed tag') =
        Function.update remainingAt tag (remainingAt tag - 1) := by
    funext tag'
    by_cases htag : tag' = tag
    · subst htag
      simp [unlinkBadTagNext, remainingAt, Function.update_self]
      omega
    · simp [unlinkBadTagNext, remainingAt, Function.update_of_ne htag]
  calc
    unlinkBadRemaining (sessionsPerTag := sessionsPerTag)
        (unlinkBadTagNext tag st nonce auth)
        = ∑ tag' : TagId, Function.update remainingAt tag (remainingAt tag - 1) tag' := by
          simp [unlinkBadRemaining, hpoint]
    _ = (∑ tag' : TagId, remainingAt tag') - 1 := sum_update_pred hpos
    _ = unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 := by
          simp [unlinkBadRemaining, remainingAt]

variable [SampleableType Nonce] [SampleableType Digest]

/-- When the tag still has a free slot (`sessionsUsed tag < sessionsPerTag`), the tag oracle samples
a fresh nonce and digest and advances the state via `unlinkBadTagNext`. -/
private lemma unlinkBadTagQueryImpl_run_of_lt
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag) :
    (unlinkBadTagQueryImpl (sessionsPerTag := sessionsPerTag) tag).run st =
      (($ᵗ Nonce : ProbComp Nonce) >>= fun nonce =>
        ($ᵗ Digest : ProbComp Digest) >>= fun auth =>
          pure (some ({ nonce := nonce, auth := auth } : TagTranscript Nonce Digest),
            unlinkBadTagNext tag st nonce auth)) := by
  simp [unlinkBadTagQueryImpl, unlinkBadTagNext, hslot]

/-- When the tag has exhausted its slot budget, the tag oracle returns `none` and leaves the state
unchanged. -/
private lemma unlinkBadTagQueryImpl_run_of_not_lt
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (hslot : ¬ st.sessionsUsed tag < sessionsPerTag) :
    (unlinkBadTagQueryImpl (sessionsPerTag := sessionsPerTag) tag).run st = pure (none, st) := by
  simp [unlinkBadTagQueryImpl, hslot]

/-- Every outcome in the support of a successful tag query has the form
`(some ⟨nonce, auth⟩, unlinkBadTagNext tag st nonce auth)` for some sampled `nonce` and `auth`. -/
private lemma unlinkBadTagQueryImpl_support_of_lt
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag) :
    ∀ z ∈ support ((unlinkBadTagQueryImpl (sessionsPerTag := sessionsPerTag) tag).run st),
      ∃ nonce auth,
        z = (some ({ nonce := nonce, auth := auth } : TagTranscript Nonce Digest),
          unlinkBadTagNext tag st nonce auth) := by
  intro z hz
  rw [unlinkBadTagQueryImpl_run_of_lt (sessionsPerTag := sessionsPerTag) tag st hslot,
    mem_support_bind_iff] at hz
  rcases hz with ⟨nonce, _, hz⟩
  rw [mem_support_bind_iff] at hz
  rcases hz with ⟨auth, _, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  exact ⟨nonce, auth, hz⟩

/-- A single tag step raises `bad` with probability at most `sessionsUsed tag * maxNonceProb`:
the new nonce collides with one of the (at most `sessionsUsed tag`) previously cached nonces,
each matchable with probability at most `maxNonceProb`. -/
private lemma unlinkBadTagStep_bad_le
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (maxNonceProb : ℝ≥0∞)
    (hmax : ∀ n : Nonce, Pr{let x ← ($ᵗ Nonce : ProbComp Nonce)}[x = n] ≤ maxNonceProb)
    (hbad : st.bad = false)
    (hbounded : unlinkBadCacheBounded st) :
    Pr{let z ← (unlinkBadTagQueryImpl (sessionsPerTag := sessionsPerTag) tag).run st}[
      z.2.bad = true] ≤ (st.sessionsUsed tag : ℝ≥0∞) * maxNonceProb := by
  by_cases hslot : st.sessionsUsed tag < sessionsPerTag
  · rw [unlinkBadTagQueryImpl_run_of_lt (sessionsPerTag := sessionsPerTag) tag st hslot]
    simp only [expect_norm]
    -- `bad` fires exactly when the fresh nonce is already cached for this tag.
    have hinner : ∀ nonce, ¬ (st.responses (tag, nonce)).isSome = true →
        Pr{let auth ← ($ᵗ Digest : ProbComp Digest)}[
          (unlinkBadTagNext tag st nonce auth).bad = true] ≤ 0 := fun nonce hcached =>
      le_of_eq <| prEvent_eq_zero_of_forall_not _ _ fun _ => by
        simp [unlinkBadTagNext, hbad, Bool.eq_false_iff.mpr hcached]
    refine (wp_le_prEvent_add _ _ _ hinner fun _ => prEvent_le_one _).trans ?_
    rw [add_zero]
    obtain ⟨S, hScard, hS⟩ := hbounded tag
    calc Pr{let nonce ← ($ᵗ Nonce : ProbComp Nonce)}[(st.responses (tag, nonce)).isSome = true]
        ≤ Pr{let nonce ← ($ᵗ Nonce : ProbComp Nonce)}[∃ n ∈ S, nonce = n] :=
          prEvent_mono _ _ _ fun nonce hcached => ⟨nonce, hS nonce hcached, rfl⟩
      _ ≤ ∑ n ∈ S, Pr{let nonce ← ($ᵗ Nonce : ProbComp Nonce)}[nonce = n] :=
          prEvent_exists_finset_le S ($ᵗ Nonce : ProbComp Nonce) (fun n nonce => nonce = n)
      _ ≤ ∑ _n ∈ S, maxNonceProb := Finset.sum_le_sum fun n _ => hmax n
      _ = (S.card : ℝ≥0∞) * maxNonceProb := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (st.sessionsUsed tag : ℝ≥0∞) * maxNonceProb :=
          mul_le_mul' (Nat.cast_le.mpr hScard) le_rfl
  · rw [unlinkBadTagQueryImpl_run_of_not_lt (sessionsPerTag := sessionsPerTag) tag st hslot]
    simp [hbad]

variable [Fintype TagId] [DecidableEq Digest]

/-- For any adversary and state `st` with `bad = false`,
the probability that bad fires is at most
`(∑ tag, sessionsPerTag − st.sessionsUsed tag) * sessionsPerTag * maxNonceProb`. -/
private lemma simulateQ_unlinkBad_prob_le
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (maxNonceProb : ℝ≥0∞)
    (hmax : ∀ n : Nonce, Pr{let x ← ($ᵗ Nonce : ProbComp Nonce)}[x = n] ≤ maxNonceProb)
    (st : UnlinkBadState TagId Nonce Digest)
    (hbounded : unlinkBadCacheBounded st)
    (hbad : st.bad = false)
    (hused : ∀ tag, st.sessionsUsed tag ≤ sessionsPerTag) :
    Pr{let z ← ((simulateQ (unlinkBadQueryImpl (sessionsPerTag := sessionsPerTag)) adversary).run
      st)}[z.2.bad = true] ≤
      (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
        ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
  induction adversary using OracleComp.inductionOn generalizing st with
  | pure b =>
    simp only [simulateQ_pure, StateT.run_pure, prEvent_pure, hbad, Bool.false_eq_true,
      propInd_false]
    exact zero_le
  | query_bind t oa ih =>
    simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind, monadLift_self,
      prEvent_bind]
    cases t with
    | inl tag =>
      simp only [unlinkBadQueryImpl, QueryImpl.add_apply_inl]
      by_cases hslot : st.sessionsUsed tag < sessionsPerTag
      · let step := (unlinkBadTagQueryImpl (sessionsPerTag := sessionsPerTag) tag).run st
        let cont := fun z : Option (TagTranscript Nonce Digest) ×
            UnlinkBadState TagId Nonce Digest =>
          (simulateQ (unlinkBadQueryImpl (sessionsPerTag := sessionsPerTag)) (oa z.1)).run z.2
        have hstep :
            Pr{let z ← step}[z.2.bad = true] ≤ (sessionsPerTag : ℝ≥0∞) * maxNonceProb :=
          (unlinkBadTagStep_bad_le (sessionsPerTag := sessionsPerTag)
            tag st maxNonceProb hmax hbad hbounded).trans
              (mul_le_mul' (Nat.cast_le.mpr (hused tag)) le_rfl)
        have hRpos := unlinkBadRemaining_pos_of_slot
          (sessionsPerTag := sessionsPerTag) tag st hslot
        have hcont :
            ∀ z ∈ support step, ¬ z.2.bad = true →
              Pr{let y ← cont z}[y.2.bad = true] ≤
                ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 : ℕ) : ℝ≥0∞) *
                  ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
          intro z hz hzbad
          obtain ⟨nonce, auth, rfl⟩ :=
            unlinkBadTagQueryImpl_support_of_lt (sessionsPerTag := sessionsPerTag)
              tag st hslot z (by simpa [step] using hz)
          simpa [cont, unlinkBadRemaining_tagNext (sessionsPerTag := sessionsPerTag)
            tag st nonce auth hslot] using
            ih (some ({ nonce := nonce, auth := auth } : TagTranscript Nonce Digest))
              (unlinkBadTagNext tag st nonce auth)
              (unlinkBadTagNext_cacheBounded tag st nonce auth hbounded)
              (Bool.eq_false_iff.mpr hzbad)
              (unlinkBadTagNext_sessionsUsed_le (sessionsPerTag := sessionsPerTag)
                tag st nonce auth hslot hused)
        calc
          Pr{let x ← step; let z ← cont x}[z.2.bad = true]
              ≤ (sessionsPerTag : ℝ≥0∞) * maxNonceProb +
                  ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 : ℕ) :
                    ℝ≥0∞) * ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) :=
                (prEvent_bind_le_prEvent_add_of_support step cont _ _ hcont).trans
                  (add_le_add_left hstep _)
          _ = (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
                ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
                have hRcast : (1 : ℝ≥0∞) +
                    ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 : ℕ) : ℝ≥0∞) =
                    (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) := by
                  exact_mod_cast Nat.add_sub_cancel' (Nat.succ_le_iff.mpr hRpos)
                nth_rw 1 [← one_mul ((sessionsPerTag : ℝ≥0∞) * maxNonceProb)]
                rw [← add_mul, hRcast]
      · change Pr{let p ← (unlinkBadTagQueryImpl tag).run st;
                  let z ← (simulateQ unlinkBadQueryImpl (oa p.1)).run p.2}[z.2.bad = true] ≤ _
        rw [unlinkBadTagQueryImpl_run_of_not_lt (sessionsPerTag := sessionsPerTag) tag st hslot]
        simpa using ih none st hbounded hbad hused
    | inr transcript =>
      simp only [unlinkBadQueryImpl, QueryImpl.add_apply_inr]
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hmem => ?_
      rw [unlinkBadReaderQueryImpl_state_eq transcript st z hmem]
      exact ih z.1 st hbounded hbad hused

/-- A pointwise bound on the nonce sampler turns the bad-event probability into an explicit session
collision bound. -/
theorem unlinkBadExperiment_le_sessionCollisionBound
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (maxNonceProb : ℝ≥0∞)
    (hmax : ∀ n : Nonce, Pr{let x ← ($ᵗ Nonce : ProbComp Nonce)}[x = n] ≤ maxNonceProb) :
    𝒟[unlinkBadExperiment (sessionsPerTag := sessionsPerTag) adversary] {true} ≤
      ((sessionsPerTag ^ 2 * Fintype.card TagId : ℕ) : ℝ≥0∞) * maxNonceProb := by
  have hlhs : 𝒟[unlinkBadExperiment (sessionsPerTag := sessionsPerTag) adversary] {true} =
      Pr{let z ← ((simulateQ (unlinkBadQueryImpl (sessionsPerTag := sessionsPerTag)) adversary).run
        UnlinkBadState.init)}[z.2.bad = true] := by
    rw [← prEvent_eq_evalDist_singleton, unlinkBadExperiment]
    simp only [expect_norm]
  rw [hlhs]
  have hremaining :
      unlinkBadRemaining (sessionsPerTag := sessionsPerTag)
        (UnlinkBadState.init (TagId := TagId) (Nonce := Nonce) (Digest := Digest)) =
          sessionsPerTag * Fintype.card TagId := by
    simp [unlinkBadRemaining, UnlinkBadState.init, Finset.sum_const, Finset.card_univ, mul_comm]
  refine (simulateQ_unlinkBad_prob_le (sessionsPerTag := sessionsPerTag)
    adversary maxNonceProb hmax UnlinkBadState.init unlinkBadCacheBounded_init
    (by simp [UnlinkBadState.init]) (by simp [UnlinkBadState.init])).trans (le_of_eq ?_)
  rw [hremaining]
  push_cast
  ring

end Theorems

end PRFTagReader
