/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import Examples.PRFTagReader.DirectCoupling.Compose
public import Examples.PRFTagReader.MultipleToHybrid.EagerSetup
import Mathlib.Tactic.Positivity.Finset

/-!
# PRF Tag/Reader Protocol — Multiple-Bad Collision Bound

Discharges the multiple-bad collision term in closed form and packages the Boolean distance
between the multiple- and single-session random-function worlds of the headline reduction:

* `multipleBadStep_*` lemmas track the per-step bad-flag bound and the session counter;
* `simulateQ_multipleBad_prob_le` unrolls those step lemmas to a union bound, yielding
  `multipleBad_bad_le_sessionCollisionBound`;
* `unlinkPRFIdeal_boolDist_le_unlinkBad` packages the middle hop of the headline reduction.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section UnlinkReduction

variable {TagId Nonce Digest K : Type} {sessionsPerTag : ℕ}
  [DecidableEq TagId] [Fintype TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]

/-! ### Multiple-vs-single bound

The multiple-vs-single ideal-world coupling is supplied by the sorry-free, hypothesis-free
direct-coupling headline `UnlinkReduction.multipleIdeal_le_singleIdeal_add_bad_DC`: the
multiple-session ideal world is bounded by the single-session ideal world plus the within-tag
nonce-collision probability (the `bad` flag of the instrumented `multipleBadQueryImpl`) and five
unconditional cell-asymmetry and nonce-aliasing slack terms. The collision term is expressed in
the `multipleBadQueryImpl` shape, which the bound below discharges in closed form. -/

/-! ### Multiple-vs-single bound: session-collision bound for `multipleBadQueryImpl`

The induction port `simulateQ_multipleBad_prob_le` mirrors the proven
`simulateQ_unlinkBad_prob_le`: at each tag step the bad flag fires with probability at most
`sessionsUsed tag * maxNonceProb`, and the per-tag session counter (synchronised with the
multiple-ideal state) drops by exactly one. The composed bound is
`unlinkBadRemaining sB * sessionsPerTag * maxNonceProb`, which collapses at the initial state to
the explicit `sessionsPerTag^2 * |TagId| * maxNonceProb` session collision bound. -/

/-- Per-step tag bound for `multipleBadQueryImpl`: a single tag query raises the bad flag with
probability at most `sB.sessionsUsed tag * maxNonceProb`. The proof factors through
`multipleIdealQueryImpl_tag_run_of_lt`'s `idealCacheStep`-based form; the inner `idealCacheStep`
draw is distribution-neutral for the bad bit because `multipleBadAdvance` only inspects the
*nonce* component of the transcript via `(sB.responses (tag, nonce)).isSome`. -/
lemma multipleBadStep_bad_le
    (tag : TagId) (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (maxNonceProb : ℝ≥0∞)
    (hmax : ∀ n : Nonce, Pr{let x ← ($ᵗ Nonce : ProbComp Nonce)}[x = n] ≤ maxNonceProb)
    (hbad : sB.bad = false)
    (hbounded : unlinkBadCacheBounded sB) :
    Pr{let z ← ((multipleBadQueryImpl TagId Nonce Digest sessionsPerTag (Sum.inl tag))
      ((s, c), sB))}[z.2.2.bad = true] ≤ (sB.sessionsUsed tag : ℝ≥0∞) * maxNonceProb := by
  rw [multipleBadQueryImpl_tag_run tag ((s, c), sB)]
  by_cases hslot : s.sessionsUsed tag < sessionsPerTag
  · rw [multipleIdealQueryImpl_tag_run_of_lt tag s c hslot]
    -- The run's answer type is the tag oracle's range only up to unfolding the specification.
    erw [bind_assoc]
    -- `bad` fires exactly when the fresh nonce is already cached for this tag.
    refine (prEvent_bind_le_prEvent_add_of_support _ _
      (fun nonce => (sB.responses (tag, nonce)).isSome = true) _
      fun nonce _ hcached => le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _
        fun z hz => ?_)).trans ?_
    · obtain ⟨r, hr, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      obtain ⟨step, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
      erw [support_pure, Set.mem_singleton_iff] at hr
      subst hz hr
      simp [multipleBadAdvance, hbad, Bool.eq_false_iff.mpr hcached]
    rw [add_zero]
    obtain ⟨S, hScard, hS⟩ := hbounded tag
    calc Pr{let nonce ← ($ᵗ Nonce : ProbComp Nonce)}[(sB.responses (tag, nonce)).isSome = true]
        ≤ Pr{let nonce ← ($ᵗ Nonce : ProbComp Nonce)}[∃ n ∈ S, nonce = n] :=
          prEvent_mono _ _ _ fun nonce hcached => ⟨nonce, hS nonce hcached, rfl⟩
      _ ≤ ∑ n ∈ S, Pr{let nonce ← ($ᵗ Nonce : ProbComp Nonce)}[nonce = n] :=
          prEvent_exists_finset_le S ($ᵗ Nonce : ProbComp Nonce) (fun n nonce => nonce = n)
      _ ≤ ∑ _n ∈ S, maxNonceProb := Finset.sum_le_sum fun n _ => hmax n
      _ = (S.card : ℝ≥0∞) * maxNonceProb := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (sB.sessionsUsed tag : ℝ≥0∞) * maxNonceProb :=
          mul_le_mul' (Nat.cast_le.mpr hScard) le_rfl
  · -- Slot exhausted: the tag oracle returns `none`, bad stays `false`.
    rw [multipleIdealQueryImpl_tag_run_of_not_lt tag s c hslot]
    simp [multipleBadAdvance, hbad]

/-- Bad-bit invariant: in any reachable state of `multipleBadQueryImpl`, the bad-world component's
session counters equal the multiple-ideal state's session counters. Used to swap the slot check
from `s.sessionsUsed` to `sB.sessionsUsed` in the per-step bound. -/
lemma multipleBadStep_sessionsUsed_eq
    (tag : TagId) (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hsync : sB.sessionsUsed = s.sessionsUsed) :
    ∀ z ∈ support
        ((multipleBadQueryImpl TagId Nonce Digest sessionsPerTag (Sum.inl tag)) ((s, c), sB)),
      z.2.2.sessionsUsed = z.2.1.1.sessionsUsed := by
  intro z hz
  rw [multipleBadQueryImpl_tag_run tag ((s, c), sB)] at hz
  obtain ⟨r, hr, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  subst hz
  by_cases hslot : s.sessionsUsed tag < sessionsPerTag
  · rw [multipleIdealQueryImpl_tag_run_of_lt tag s c hslot] at hr
    set advU := ({ sessionsUsed :=
        Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } : UnlinkState TagId)
    obtain ⟨nonce, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
    obtain ⟨r', _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
    subst hr
    simp only [multipleBadAdvance]
    funext t
    by_cases htag : t = tag
    · subst htag; simp [advU, Function.update_self, hsync]
    · simp [advU, Function.update_of_ne htag, hsync]
  · rw [multipleIdealQueryImpl_tag_run_of_not_lt tag s c hslot] at hr
    subst hr
    simp [multipleBadAdvance, hsync]

/-- Reader queries leave the bad-world component untouched: in any reachable state of
`multipleBadQueryImpl` on a reader query, the bad-state is unchanged. -/
lemma multipleBadStep_reader_state_eq
    (transcript : TagTranscript Nonce Digest)
    (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest) :
    ∀ z ∈ support ((multipleBadQueryImpl TagId Nonce Digest sessionsPerTag (Sum.inr transcript))
        ((s, c), sB)),
      z.2.2 = sB := by
  intro z hz
  rw [multipleBadQueryImpl_reader_run transcript ((s, c), sB)] at hz
  obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  subst hz
  rfl

/-- Cache-bounded and sessions-used invariants of the bad-world state are preserved by reachable
states of `multipleBadQueryImpl`. The reader branch leaves `sB` untouched; the tag branch threads
through `unlinkBadTagNext_cacheBounded`/`unlinkBadTagNext_sessionsUsed_le` via the bridge between
`multipleBadAdvance` and `unlinkBadTagNext`. -/
lemma multipleBadStep_preserves
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hbounded : unlinkBadCacheBounded sB)
    (hused : ∀ tag : TagId, sB.sessionsUsed tag ≤ sessionsPerTag)
    (hsync : sB.sessionsUsed = s.sessionsUsed) :
    ∀ z ∈ support ((multipleBadQueryImpl TagId Nonce Digest sessionsPerTag t) ((s, c), sB)),
      unlinkBadCacheBounded z.2.2 ∧
        (∀ tag : TagId, z.2.2.sessionsUsed tag ≤ sessionsPerTag) ∧
        z.2.2.sessionsUsed = z.2.1.1.sessionsUsed := by
  cases t with
  | inl tag =>
    intro z hz
    rw [multipleBadQueryImpl_tag_run tag ((s, c), sB)] at hz
    obtain ⟨r, hr, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    subst hz
    by_cases hslot : s.sessionsUsed tag < sessionsPerTag
    · rw [multipleIdealQueryImpl_tag_run_of_lt tag s c hslot] at hr
      set advU := ({ sessionsUsed :=
          Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } : UnlinkState TagId)
      obtain ⟨nonce, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
      obtain ⟨r', _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
      subst hr
      have hsBslot : sB.sessionsUsed tag < sessionsPerTag := hsync ▸ hslot
      refine ⟨?_, ?_, ?_⟩
      · exact unlinkBadTagNext_cacheBounded tag sB nonce r'.1 hbounded
      · exact unlinkBadTagNext_sessionsUsed_le tag sB nonce r'.1 hsBslot hused
      · change (unlinkBadTagNext tag sB nonce r'.1).sessionsUsed = _
        funext t
        by_cases htag : t = tag
        · subst htag; simp [advU, unlinkBadTagNext, Function.update_self, hsync]
        · simp [advU, unlinkBadTagNext, Function.update_of_ne htag, hsync]
    · rw [multipleIdealQueryImpl_tag_run_of_not_lt tag s c hslot] at hr
      subst hr
      simp only [multipleBadAdvance]
      exact ⟨hbounded, hused, hsync⟩
  | inr transcript =>
    intro z hz
    rw [multipleBadQueryImpl_reader_run transcript ((s, c), sB)] at hz
    obtain ⟨r, hr, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    subst hz
    rw [multipleIdealQueryImpl_reader_run transcript s c] at hr
    obtain ⟨rs, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
    subst hr
    exact ⟨hbounded, hused, hsync⟩

/-- **Bad-event union bound for `multipleBadQueryImpl`.** Starting from a multiple-bad state
satisfying the cache-boundedness, session-used-≤-`sessionsPerTag`, and sync invariants, with the
bad flag unset, the probability that bad fires under any adversary is at most
`unlinkBadRemaining sB * sessionsPerTag * maxNonceProb`. Direct port of
`simulateQ_unlinkBad_prob_le` to the multiple-bad handler. -/
lemma simulateQ_multipleBad_prob_le
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (maxNonceProb : ℝ≥0∞)
    (hmax : ∀ n : Nonce, Pr{let x ← ($ᵗ Nonce : ProbComp Nonce)}[x = n] ≤ maxNonceProb)
    (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hbounded : unlinkBadCacheBounded sB)
    (hbad : sB.bad = false)
    (hused : ∀ tag, sB.sessionsUsed tag ≤ sessionsPerTag)
    (hsync : sB.sessionsUsed = s.sessionsUsed) :
    Pr{let z ← ((simulateQ (multipleBadQueryImpl TagId Nonce Digest sessionsPerTag)
      adversary).run ((s, c), sB))}[z.2.2.bad = true] ≤
      (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB : ℝ≥0∞) *
        ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
  induction adversary using OracleComp.inductionOn generalizing s c sB with
  | pure b =>
    simp only [simulateQ_pure, StateT.run_pure, prEvent_pure, hbad, Bool.false_eq_true,
      ite_false]
    exact zero_le
  | query_bind t oa ih =>
    rw [multipleBad_run_query_bind' t (fun r => oa r) ((s, c), sB)]
    -- Per-query bound (depends on the query case)
    cases t with
    | inl tag =>
      by_cases hslot : s.sessionsUsed tag < sessionsPerTag
      · -- Tag query, slot available: apply `multipleBadStep_bad_le`, then induct on the
        -- continuation with updated invariants.
        set step :=
          (multipleBadQueryImpl TagId Nonce Digest sessionsPerTag (Sum.inl tag)) ((s, c), sB)
        set cont := fun p : Option (TagTranscript Nonce Digest) ×
            MultipleBadState TagId Nonce Digest sessionsPerTag =>
          (simulateQ (multipleBadQueryImpl TagId Nonce Digest sessionsPerTag) (oa p.1)).run p.2
        have hstepBound :
            Pr{let z ← step}[z.2.2.bad = true] ≤ (sessionsPerTag : ℝ≥0∞) * maxNonceProb :=
          (multipleBadStep_bad_le (sessionsPerTag := sessionsPerTag) tag s c sB
            maxNonceProb hmax hbad hbounded).trans
            (mul_le_mul' (Nat.cast_le.mpr (hused tag)) le_rfl)
        have hRpos : 0 < unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB :=
          unlinkBadRemaining_pos_of_slot (sessionsPerTag := sessionsPerTag) tag sB (hsync ▸ hslot)
        have hcontBound :
            ∀ p ∈ support step, ¬ p.2.2.bad = true →
              Pr{let y ← cont p}[y.2.2.bad = true] ≤
                ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB - 1 : ℕ) : ℝ≥0∞) *
                  ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
          intro p hp hpbad
          replace hpbad := Bool.eq_false_iff.mpr hpbad
          have hp_real : p ∈ support
              (multipleBadQueryImpl TagId Nonce Digest sessionsPerTag (Sum.inl tag)
                ((s, c), sB)) := by
            simpa [step] using hp
          have hinvs := multipleBadStep_preserves (sessionsPerTag := sessionsPerTag)
            (Sum.inl tag) s c sB hbounded hused hsync p hp_real
          have hRdec :
              unlinkBadRemaining (sessionsPerTag := sessionsPerTag) p.2.2 =
                unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB - 1 := by
            -- The bad state advanced via `unlinkBadTagNext`; remaining drops by one.
            rw [multipleBadQueryImpl_tag_run tag ((s, c), sB)] at hp_real
            obtain ⟨r, hr, hp⟩ := (mem_support_bind_iff _ _ _).mp hp_real
            subst hp
            rw [multipleIdealQueryImpl_tag_run_of_lt tag s c hslot] at hr
            set advU := ({ sessionsUsed :=
                Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } : UnlinkState TagId)
            obtain ⟨nonce, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
            obtain ⟨r', _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
            subst hr
            exact unlinkBadRemaining_tagNext (sessionsPerTag := sessionsPerTag)
              tag sB nonce r'.1 (hsync ▸ hslot)
          have hih :=
            ih p.1 p.2.1.1 p.2.1.2 p.2.2 hinvs.1 hpbad hinvs.2.1 hinvs.2.2
          simpa [cont, hRdec, Prod.eq_iff_fst_eq_snd_eq, show (p.2.1.1, p.2.1.2) = p.2.1 from rfl]
            using hih
        calc
          Pr{let z ← step >>= cont}[z.2.2.bad = true]
              ≤ (sessionsPerTag : ℝ≥0∞) * maxNonceProb +
                  ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB - 1 : ℕ) :
                    ℝ≥0∞) * ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) :=
                (prEvent_bind_le_prEvent_add_of_support step cont _ _ hcontBound).trans
                  (add_le_add_left hstepBound _)
          _ = (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB : ℝ≥0∞) *
                ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
                have hR : (1 : ℝ≥0∞) +
                    ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB - 1 : ℕ) : ℝ≥0∞) =
                    (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB : ℝ≥0∞) := by
                  exact_mod_cast Nat.add_sub_cancel' (Nat.succ_le_iff.mpr hRpos)
                rw [← hR]; ring
      · -- Slot exhausted: the tag step is `pure (none, (s, c), sB)`; induct directly.
        rw [multipleBadQueryImpl_tag_run tag ((s, c), sB),
          multipleIdealQueryImpl_tag_run_of_not_lt tag s c hslot]
        simp only [multipleBadAdvance]
        exact ih none s c sB hbounded hbad hused hsync
    | inr transcript =>
      -- Reader branch: bad-world component untouched; induct on the continuation.
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hmem => ?_
      have hzeq := multipleBadStep_reader_state_eq (sessionsPerTag := sessionsPerTag)
        transcript s c sB z hmem
      have hinvs := multipleBadStep_preserves (sessionsPerTag := sessionsPerTag)
        (Sum.inr transcript) s c sB hbounded hused hsync z hmem
      rcases z with ⟨u, ⟨s', c'⟩, sB'⟩
      subst hzeq
      exact ih u s' c' sB' hinvs.1 hbad hinvs.2.1 hinvs.2.2

/-- **Final session-collision bound** for the multiple-bad handler. Chains
`simulateQ_multipleBad_prob_le` at the initial state, where the `unlinkBadRemaining` collapses to
`sessionsPerTag * |TagId|`, giving the explicit `sessionsPerTag^2 * |TagId| * maxNonceProb`
session-collision bound. The headline analogue of `unlinkBadExperiment_le_sessionCollisionBound`. -/
theorem multipleBad_bad_le_sessionCollisionBound
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (maxNonceProb : ℝ)
    (hmax : ∀ nonce : Nonce, (Pr{let n ← $ᵗ Nonce}[n = nonce]).toReal ≤ maxNonceProb) :
    (𝒟[(fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad) <$>
        (simulateQ (multipleBadQueryImpl TagId Nonce Digest sessionsPerTag) adversary).run
          ((UnlinkState.init, ∅), UnlinkBadState.init)] {true}).toReal ≤
      ((sessionsPerTag ^ 2 * Fintype.card TagId : ℕ) : ℝ) * maxNonceProb := by
  have hmax_ENNReal : ∀ n : Nonce,
      Pr{let x ← ($ᵗ Nonce : ProbComp Nonce)}[x = n] ≤ ENNReal.ofReal maxNonceProb := fun n =>
    (ENNReal.le_ofReal_iff_toReal_le (ne_top_of_le_ne_top one_ne_top (prEvent_le_one _))
      (ENNReal.toReal_nonneg.trans (hmax n))).2 (hmax n)
  rw [← prEvent_eq_evalDist_singleton, prEvent_map]
  have hcore := simulateQ_multipleBad_prob_le (sessionsPerTag := sessionsPerTag)
    adversary (ENNReal.ofReal maxNonceProb) hmax_ENNReal UnlinkState.init ∅
    UnlinkBadState.init unlinkBadCacheBounded_init
    (by simp [UnlinkBadState.init]) (by simp [UnlinkBadState.init])
    (by simp [UnlinkState.init, UnlinkBadState.init])
  have hremaining :
      unlinkBadRemaining (sessionsPerTag := sessionsPerTag)
        (UnlinkBadState.init (TagId := TagId) (Nonce := Nonce) (Digest := Digest)) =
          sessionsPerTag * Fintype.card TagId := by
    simp [unlinkBadRemaining, UnlinkBadState.init, Finset.sum_const, Finset.card_univ, mul_comm]
  have hmax_nonneg : 0 ≤ maxNonceProb :=
    ENNReal.toReal_nonneg.trans (hmax (Classical.arbitrary Nonce))
  have hconv := ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) hcore
  simp only [hremaining, Nat.cast_mul, toReal_mul, toReal_natCast,
    ENNReal.toReal_ofReal hmax_nonneg] at hconv
  grind

/-! ### Multiple-vs-single bound: bad-event bridge -/

/-- Coupling bound for the two random-function worlds (the ideal-PRF experiments of the multiple-
and single-session reductions): their Boolean distance is bounded by the within-tag
nonce-collision probability (carried by the instrumented `multipleBadQueryImpl`'s `bad` flag) plus
three additive slack terms. The two worlds are not identical-until-bad — their reader and tag
oracles diverge unconditionally because the single-session world keys
`Fintype.card TagId * sessionsPerTag` random-oracle cells against the multiple world's
`Fintype.card TagId` cells — so the bound carries reader-cell slacks
`qReader * Fintype.card TagId / Fintype.card Digest` and
`qReader * Fintype.card TagId * sessionsPerTag / Fintype.card Digest`, and a nonce-aliasing slack
`qReader * qTag / Fintype.card Nonce`. The bound holds for every adversary.

Both directions come from one coupling: `UnlinkReduction.multipleIdeal_le_singleIdeal_add_bad_DC`
bounds the multiple-world mass of each output bit by its single-world mass plus the same error, and
two probability measures on `Bool` with that property are within that Boolean distance
(`MeasureTheory.Measure.boolDist_le_of_apply_le`). -/
theorem unlinkPRFIdeal_boolDist_le_unlinkBad [NeZero sessionsPerTag] [Fintype Nonce]
    [Fintype Digest] (adversary : UnlinkAdversary TagId Nonce Digest) (qReader qTag : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (·.isRight) qReader)
    (hqTag : OracleComp.IsQueryBoundP adversary (·.isLeft) qTag) :
    𝒟[PRFScheme.prfIdealExperiment (unlinkToMultiplePRFReduction (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary)].boolDist
      𝒟[PRFScheme.prfIdealExperiment (unlinkToSinglePRFReduction (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary)] ≤
      𝒟[(fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad) <$>
        (simulateQ (multipleBadQueryImpl TagId Nonce Digest sessionsPerTag) adversary).run
          ((UnlinkState.init, ∅), UnlinkBadState.init)] {true} +
      ((qReader * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((qReader * qTag : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
      ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  refine MeasureTheory.Measure.boolDist_le_of_apply_le _ _ fun out => ?_
  rw [prfIdealExperiment_unlinkToMultiplePRFReduction_eq_run' adversary,
    prfIdealExperiment_unlinkToSinglePRFReduction_eq_run' adversary,
    ← prEvent_eq_evalDist_singleton ((fun z : Bool × MultipleBadState TagId Nonce Digest
      sessionsPerTag => z.2.2.bad) <$> _), prEvent_map]
  have h := UnlinkReduction.multipleIdeal_le_singleIdeal_add_bad_DC
    (sessionsPerTag := sessionsPerTag) out adversary qReader qTag hqReader hqTag
  rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton] at h
  simpa only [add_assoc] using h

end UnlinkReduction

end PRFTagReader
