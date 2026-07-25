/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

import VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies.Projections

/-!
# Ghost-layer machinery for Fiat-Shamir with aborts: BodyBounds

Real-versus-reprogrammed signing-body bounds: the within-signing-query
collision budget, the per-attempt collision and abort bounds, and the two
body-level cores of the Sign → Prog hop (the within-query total-variation
induction and the expected cache growth of the reprogramming loop).

Part of the hybrid signing-body development for the CMA-to-NMA reduction;
`VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies` re-exports all of
its modules and holds the overview docstring.
-/

open OracleComp OracleSpec
open scoped BigOperators ENNReal

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

variable [SampleableType Stmt]
variable [DecidableEq Commit] [SampleableType Chal]
variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
  (M : Type) [DecidableEq M] (maxAttempts : ℕ)
variable (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))

/-! ## Real-versus-reprogrammed signing-body bounds

Quantitative body-level core of the Sign → Prog hop
(`probOutput_hybridExpAtKey_real_le_prog`): run equations unfolding one attempt of the
real signing loop (`fsAbortSignLoop` under the caching random oracle) and of the
reprogramming loop (`progSignBody`), the per-attempt commitment-collision and abort
bounds, the within-signing-query total-variation induction
(`ofReal_tvDist_run_fsAbortSignLoop_progSignBody_le`), and the expected cache-growth
bound for the reprogramming loop (`tsum_probOutput_run_progSignBody_mul_enncard_le`). -/

/-- Expectation of a nonnegative functional under a `pure` computation. -/
lemma tsum_probOutput_pure_mul {β : Type} (y : β) (f : β → ℝ≥0∞) :
    ∑' z, Pr[= z | (pure y : ProbComp β)] * f z = f y := by
  rw [tsum_eq_single y fun z hz => by
    rw [probOutput_eq_zero_of_not_mem_support (by simp [hz]), zero_mul]]
  rw [probOutput_pure_self, one_mul]

/-- Tonelli-style rearrangement: the expectation of a nonnegative functional under a
bind is the outer expectation of the inner expectations. -/
lemma tsum_probOutput_bind_mul {α β : Type} (oa : ProbComp α)
    (g : α → ProbComp β) (f : β → ℝ≥0∞) :
    ∑' z, Pr[= z | oa >>= g] * f z =
      ∑' x, Pr[= x | oa] * ∑' z, Pr[= z | g x] * f z := by
  simp_rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left]

/-- Push a constant out of a pointwise expectation bound: a (sub)probability average of
`f ≤ C + g` is at most `C` plus the average of `g`. -/
lemma tsum_probOutput_mul_le_add_of_le {α : Type} (oa : ProbComp α)
    {f g : α → ℝ≥0∞} {C : ℝ≥0∞} (h : ∀ a, f a ≤ C + g a) :
    ∑' a, Pr[= a | oa] * f a ≤ C + ∑' a, Pr[= a | oa] * g a := by
  calc ∑' a, Pr[= a | oa] * f a
      ≤ ∑' a, (Pr[= a | oa] * C + Pr[= a | oa] * g a) :=
        ENNReal.tsum_le_tsum fun a => by rw [← mul_add]; exact mul_le_mul_right (h a) _
    _ = (∑' a, Pr[= a | oa]) * C + ∑' a, Pr[= a | oa] * g a := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ 1 * C + ∑' a, Pr[= a | oa] * g a := by
        gcongr
        exact tsum_probOutput_le_one
    _ = C + ∑' a, Pr[= a | oa] * g a := by rw [one_mul]

/-- `ENNReal` form of `tvDist_bind_left_le`: the lifted TV distance of a bind over a
shared base is at most the base-averaged lifted TV distance of the continuations. -/
lemma ofReal_tvDist_bind_le_tsum {α β : Type} (oa : ProbComp α) (f g : α → ProbComp β) :
    ENNReal.ofReal (tvDist (oa >>= f) (oa >>= g)) ≤
      ∑' x, Pr[= x | oa] * ENNReal.ofReal (tvDist (f x) (g x)) := by
  refine le_trans (ENNReal.ofReal_le_ofReal (tvDist_bind_left_le oa f g)) ?_
  have h_sum_ne_top : (∑' x : α, Pr[= x | oa]) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsum_probOutput_le_one
  have h_summable : Summable fun x : α => Pr[= x | oa].toReal * tvDist (f x) (g x) :=
    Summable.of_nonneg_of_le
      (fun x => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
      (fun x => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _))
      (ENNReal.summable_toReal h_sum_ne_top)
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun x => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _)) h_summable]
  refine ENNReal.tsum_le_tsum fun x => ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal probOutput_ne_top]

omit [SampleableType Stmt] in
/-- One-attempt unfolding of the reprogramming loop's cache-level run. -/
lemma run_progSignBody_succ (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ)
    (c : (M × Commit →ₒ Chal).QueryCache) :
    (progSignBody ids M pk sk msg (n + 1)).run c =
      ids.commit pk sk >>= fun ws =>
        uniformSample Chal >>= fun ch =>
          ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
            | none => (progSignBody ids M pk sk msg n).run (c.cacheQuery (msg, ws.1) ch) := by
  simp only [progSignBody, progSignAttempt, bind_assoc, StateT.run_bind,
    OracleComp.liftM_run_StateT, pure_bind, StateT.run_modify]
  refine congrArg (ids.commit pk sk >>= ·) (funext fun ws => ?_)
  obtain ⟨w, st⟩ := ws
  refine congrArg (uniformSample Chal >>= ·) (funext fun ch => ?_)
  refine congrArg (ids.respond pk sk st ch >>= ·) (funext fun oz => ?_)
  cases oz with
  | some z => rfl
  | none => rfl

omit [SampleableType Stmt] in
/-- One-attempt unfolding of the real signing loop's cache-level run under the caching
random oracle: commit, take one `roStep` at the commitment point, respond against the
returned challenge, and either return or recurse on the post-step cache. -/
lemma run_simulateQ_fsAbortSignLoop_succ (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ)
    (c : (M × Commit →ₒ Chal).QueryCache) :
    (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
        (randomOracle : QueryImpl (M × Commit →ₒ Chal)
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
      (fsAbortSignLoop ids M pk sk msg (n + 1))).run c =
      ids.commit pk sk >>= fun ws =>
        roStep M c (msg, ws.1) >>= fun chc =>
          ids.respond pk sk ws.2 chc.1 >>= fun oz =>
            match oz with
            | some z => pure (some (ws.1, z), chc.2)
            | none =>
                (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
                    (randomOracle : QueryImpl (M × Commit →ₒ Chal)
                      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
                  (fsAbortSignLoop ids M pk sk msg n)).run chc.2 := by
  simp only [fsAbortSignLoop, fsAbortSignAttempt, simulateQ_bind,
    roSim.simulateQ_HasQuery_query, bind_assoc, StateT.run_bind]
  rw [roSim.run_liftM, bind_map_left]
  refine congrArg (ids.commit pk sk >>= ·) (funext fun ws => ?_)
  obtain ⟨w, st⟩ := ws
  rw [randomOracle_run_eq_roStep]
  refine congrArg (roStep M c (msg, w) >>= ·) (funext fun chc => ?_)
  rw [roSim.run_liftM, bind_map_left]
  refine congrArg (ids.respond pk sk st chc.1 >>= ·) (funext fun oz => ?_)
  cases oz with
  | some z => rfl
  | none => rfl

/-! ### The within-signing-query collision budget -/

/-- Collision budget of one signing query of the Sign → Prog hop, as a function of the
attempt budget `n` and the starting cache size `N`: attempt `a` is reached with
probability at most `p ^ a` and collides with a cached point with probability at most
`(N + a) · ε`. -/
noncomputable def signCollisionBound (ε p : ℝ) (n : ℕ) (N : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal ε * ∑ a ∈ Finset.range n, ENNReal.ofReal p ^ a * (N + a)

@[simp]
lemma signCollisionBound_zero (ε p : ℝ) (N : ℝ≥0∞) :
    signCollisionBound ε p 0 N = 0 := by
  simp [signCollisionBound]

lemma signCollisionBound_succ (ε p : ℝ) (n : ℕ) (N : ℝ≥0∞) :
    signCollisionBound ε p (n + 1) N =
      N * ENNReal.ofReal ε +
        ENNReal.ofReal p * signCollisionBound ε p n (N + 1) := by
  have h : ∑ a ∈ Finset.range n, ENNReal.ofReal p ^ (a + 1) * (N + ↑(a + 1)) =
      ENNReal.ofReal p * ∑ a ∈ Finset.range n, ENNReal.ofReal p ^ a * (N + 1 + ↑a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    push_cast
    ring
  rw [signCollisionBound, signCollisionBound, Finset.sum_range_succ', h]
  push_cast
  ring

lemma signCollisionBound_mono (ε p : ℝ) (n : ℕ) {N N' : ℝ≥0∞} (h : N ≤ N') :
    signCollisionBound ε p n N ≤ signCollisionBound ε p n N' := by
  unfold signCollisionBound
  gcongr

/-- Splitting of the collision budget into a state-free part and a part linear in the
starting cache size, matching the `ζ + R s · β` query-slack shape of
`OracleComp.ProgramLogic.Relational.expectedQuerySlack_expected_resource_le`. -/
lemma signCollisionBound_eq (ε p : ℝ) (n : ℕ) (N : ℝ≥0∞) :
    signCollisionBound ε p n N =
      ENNReal.ofReal ε * ∑ a ∈ Finset.range n, (a : ℝ≥0∞) * ENNReal.ofReal p ^ a +
        N * (ENNReal.ofReal ε * ∑ a ∈ Finset.range n, ENNReal.ofReal p ^ a) := by
  rw [signCollisionBound]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-! ### Per-attempt collision and abort bounds -/

omit [SampleableType Stmt] [DecidableEq Commit] in
/-- Aggregate per-attempt abort bound: the commit-averaged probability that a fresh
uniform challenge is refused equals the abort probability of one honest execution. -/
lemma tsum_probOutput_commit_mul_abort_le (pk : Stmt) (sk : Wit) {p_abort : ℝ}
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
        Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch]
      ≤ ENNReal.ofReal p_abort := by
  classical
  refine le_trans (le_of_eq ?_) hAbort
  rw [IdenSchemeWithAbort.honestExecution, probOutput_bind_eq_tsum]
  refine tsum_congr fun ws => ?_
  obtain ⟨cm, st⟩ := ws
  congr 1
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun ch => ?_
  congr 1
  rw [probOutput_bind_eq_tsum, tsum_eq_single (none : Option Resp) ?_]
  · simp [probOutput_pure]
  · rintro (_ | z) hb
    · exact absurd rfl hb
    · simp [probOutput_pure]

omit [SampleableType Stmt] [SampleableType Chal] [DecidableEq M] [DecidableEq Commit] in
/-- Commitment-guessing bound for cache hits: under a pointwise commitment-guessing
bound `ε`, one commit lands on a cached point of `c` at message `msg` with probability
at most `enncard c · ε`. -/
lemma probEvent_commit_hit_le (pk : Stmt) (sk : Wit) {ε : ℝ}
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (msg : M) (c : (M × Commit →ₒ Chal).QueryCache) :
    Pr[fun ws : Commit × PrvState => c (msg, ws.1) ≠ none | ids.commit pk sk]
      ≤ QueryCache.enncard c * ENNReal.ofReal ε := by
  classical
  haveI : DecidableEq Commit := Classical.decEq Commit
  let commitDist : ProbComp Commit := Prod.fst <$> ids.commit pk sk
  let hit : Commit → Prop := fun w => c (msg, w) ≠ none
  let S : Finset Commit := (finSupport commitDist).filter hit
  have h_event :
      Pr[fun ws : Commit × PrvState => c (msg, ws.1) ≠ none | ids.commit pk sk]
        = Pr[hit | commitDist] := by
    simp [commitDist, hit]
  have h_sum : Pr[hit | commitDist] = ∑ w ∈ S, Pr[= w | commitDist] := by
    simp [S, probEvent_eq_sum_filter_finSupport]
  have h_sum_le : ∑ w ∈ S, Pr[= w | commitDist] ≤ ∑ w ∈ S, ENNReal.ofReal ε :=
    Finset.sum_le_sum fun w _ => hGuess w
  have h_card_le : (S.card : ℝ≥0∞) ≤ QueryCache.enncard c := by
    have hex : ∀ w : ↑(S : Set Commit), ∃ v : Chal, c (msg, w.1) = some v := fun w =>
      Option.ne_none_iff_exists'.mp ((Finset.mem_filter.mp w.2).2)
    let cacheEntryOfHit : ↑(S : Set Commit) → c.toSet := fun w =>
      ⟨⟨(msg, w.1), Classical.choose (hex w)⟩, Classical.choose_spec (hex w)⟩
    have h_inj : Function.Injective cacheEntryOfHit := by
      intro w₁ w₂ h
      apply Subtype.ext
      have hdomain : ((msg, w₁.1) : M × Commit) = (msg, w₂.1) :=
        congrArg (fun x : c.toSet => x.1.1) h
      exact congrArg Prod.snd hdomain
    have henc : (S : Set Commit).encard ≤ c.toSet.encard := by
      simpa using Function.Embedding.encard_le ⟨cacheEntryOfHit, h_inj⟩
    have henc_nat : (S.card : ℕ∞) ≤ c.toSet.encard := by simpa using henc
    exact ENat.toENNReal_mono henc_nat
  calc Pr[fun ws : Commit × PrvState => c (msg, ws.1) ≠ none | ids.commit pk sk]
      = Pr[hit | commitDist] := h_event
    _ = ∑ w ∈ S, Pr[= w | commitDist] := h_sum
    _ ≤ ∑ w ∈ S, ENNReal.ofReal ε := h_sum_le
    _ = (S.card : ℝ≥0∞) * ENNReal.ofReal ε := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ QueryCache.enncard c * ENNReal.ofReal ε := mul_le_mul' h_card_le le_rfl

/-! ### The two body-level cores of the Sign → Prog hop -/

omit [SampleableType Stmt] in
/-- **Within-signing-query TV induction for the Sign → Prog hop.** From a shared
starting cache, the real signing loop (live caching random oracle) and the
all-attempts-reprogramming loop are within total-variation distance
`ε · ∑_{a<n} p ^ a · (|c| + a)`: the two loops agree until an attempt commits to an
already-cached point, attempt `a` is reached only after `a` fresh-challenge rejections
(probability at most `p ^ a` each, by `hAbort`), and at that point the cache holds at
most `|c| + a` entries, each guessed with probability at most `ε` (`hGuess`). -/
lemma ofReal_tvDist_run_fsAbortSignLoop_progSignBody_le (pk : Stmt) (sk : Wit) (msg : M)
    {ε p_abort : ℝ}
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    ∀ (n : ℕ) (c : (M × Commit →ₒ Chal).QueryCache),
      ENNReal.ofReal (tvDist
        ((simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
            (randomOracle : QueryImpl (M × Commit →ₒ Chal)
              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
          (fsAbortSignLoop ids M pk sk msg n)).run c)
        ((progSignBody ids M pk sk msg n).run c))
        ≤ signCollisionBound ε p_abort n (QueryCache.enncard c) := by
  intro n
  induction n with
  | zero =>
      intro c
      simp [fsAbortSignLoop, progSignBody]
  | succ n ih =>
      intro c
      classical
      rw [run_simulateQ_fsAbortSignLoop_succ, run_progSignBody_succ]
      refine le_trans (ofReal_tvDist_bind_le_tsum _ _ _) ?_
      set B' := signCollisionBound ε p_abort n (QueryCache.enncard c + 1) with hB'
      have key : ∀ ws : Commit × PrvState,
          ENNReal.ofReal (tvDist
            (roStep M c (msg, ws.1) >>= fun chc =>
              ids.respond pk sk ws.2 chc.1 >>= fun oz =>
                match oz with
                | some z => pure (some (ws.1, z), chc.2)
                | none =>
                    (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
                        (randomOracle : QueryImpl (M × Commit →ₒ Chal)
                          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
                      (fsAbortSignLoop ids M pk sk msg n)).run chc.2)
            (uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
                | none =>
                    (progSignBody ids M pk sk msg n).run (c.cacheQuery (msg, ws.1) ch)))
          ≤ (if c (msg, ws.1) = none then 0 else 1) +
              Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] *
                B' := by
        intro ws
        cases hc : c (msg, ws.1) with
        | some v =>
            rw [if_neg (by simp)]
            exact le_add_right (ENNReal.ofReal_le_one.mpr (tvDist_le_one _ _))
        | none =>
            rw [if_pos rfl, zero_add, roStep_of_none M hc]
            simp only [bind_assoc, pure_bind]
            refine le_trans (ofReal_tvDist_bind_le_tsum _ _ _) ?_
            have hch : ∀ ch : Chal,
                ENNReal.ofReal (tvDist
                  (ids.respond pk sk ws.2 ch >>= fun oz =>
                    match oz with
                    | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
                    | none =>
                        (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
                            (randomOracle : QueryImpl (M × Commit →ₒ Chal)
                              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
                          (fsAbortSignLoop ids M pk sk msg n)).run
                            (c.cacheQuery (msg, ws.1) ch))
                  (ids.respond pk sk ws.2 ch >>= fun oz =>
                    match oz with
                    | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
                    | none =>
                        (progSignBody ids M pk sk msg n).run
                          (c.cacheQuery (msg, ws.1) ch)))
                ≤ Pr[= none | ids.respond pk sk ws.2 ch] * B' := by
              intro ch
              refine le_trans (ofReal_tvDist_bind_le_tsum _ _ _) ?_
              calc ∑' oz : Option Resp, Pr[= oz | ids.respond pk sk ws.2 ch] *
                    ENNReal.ofReal (tvDist _ _)
                  ≤ ∑' oz : Option Resp, Pr[= oz | ids.respond pk sk ws.2 ch] *
                      (if oz = none then B' else 0) := by
                    refine ENNReal.tsum_le_tsum fun oz => mul_le_mul_right ?_ _
                    cases oz with
                    | some z => simp
                    | none =>
                        rw [if_pos rfl]
                        exact le_trans (ih (c.cacheQuery (msg, ws.1) ch))
                          (signCollisionBound_mono ε p_abort n
                            (QueryCache.enncard_cacheQuery_le c (msg, ws.1) ch))
                _ = Pr[= none | ids.respond pk sk ws.2 ch] * B' := by
                    rw [tsum_eq_single (none : Option Resp)
                      fun oz hoz => by simp [hoz]]
                    simp
            calc ∑' ch : Chal, Pr[= ch | uniformSample Chal] *
                  ENNReal.ofReal (tvDist _ _)
                ≤ ∑' ch : Chal, Pr[= ch | uniformSample Chal] *
                    (Pr[= none | ids.respond pk sk ws.2 ch] * B') :=
                  ENNReal.tsum_le_tsum fun ch => mul_le_mul_right (hch ch) _
              _ = Pr[= none | uniformSample Chal >>= fun ch =>
                    ids.respond pk sk ws.2 ch] * B' := by
                  rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
                  exact tsum_congr fun ch => (mul_assoc _ _ _).symm
      calc ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
            ENNReal.ofReal (tvDist _ _)
          ≤ ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              ((if c (msg, ws.1) = none then 0 else 1) +
                Pr[= none | uniformSample Chal >>= fun ch =>
                  ids.respond pk sk ws.2 ch] * B') :=
            ENNReal.tsum_le_tsum fun ws => mul_le_mul_right (key ws) _
        _ = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              (if c (msg, ws.1) = none then 0 else 1)) +
            ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              (Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch] * B') := by
            simp_rw [mul_add]
            exact ENNReal.tsum_add
        _ ≤ QueryCache.enncard c * ENNReal.ofReal ε + ENNReal.ofReal p_abort * B' := by
            refine add_le_add ?_ ?_
            · refine le_trans (le_of_eq ?_)
                (probEvent_commit_hit_le ids M pk sk hGuess msg c)
              rw [probEvent_eq_tsum_ite]
              refine tsum_congr fun ws => ?_
              by_cases h : c (msg, ws.1) = none <;> simp [h]
            · calc ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
                    (Pr[= none | uniformSample Chal >>= fun ch =>
                      ids.respond pk sk ws.2 ch] * B')
                  = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
                      Pr[= none | uniformSample Chal >>= fun ch =>
                        ids.respond pk sk ws.2 ch]) * B' := by
                    rw [← ENNReal.tsum_mul_right]
                    exact tsum_congr fun ws => (mul_assoc _ _ _).symm
                _ ≤ ENNReal.ofReal p_abort * B' :=
                    mul_le_mul_left
                      (tsum_probOutput_commit_mul_abort_le ids pk sk hAbort) _
        _ = signCollisionBound ε p_abort (n + 1) (QueryCache.enncard c) :=
            (signCollisionBound_succ ε p_abort n (QueryCache.enncard c)).symm

omit [SampleableType Stmt] in
/-- **Expected cache growth of the reprogramming loop.** Each attempt of `progSignBody`
programs at most one new cache point and the loop continues only on a fresh-challenge
rejection, so the expected size of the final cache is at most `|c| + ∑_{a<n} p ^ a`. -/
lemma tsum_probOutput_run_progSignBody_mul_enncard_le (pk : Stmt) (sk : Wit) (msg : M)
    {p_abort : ℝ}
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    ∀ (n : ℕ) (c : (M × Commit →ₒ Chal).QueryCache),
      ∑' z : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= z | (progSignBody ids M pk sk msg n).run c] * QueryCache.enncard z.2
        ≤ QueryCache.enncard c + ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a := by
  intro n
  induction n with
  | zero =>
      intro c
      simp only [progSignBody, StateT.run_pure, tsum_probOutput_pure_mul]
      simp
  | succ n ih =>
      intro c
      classical
      set S : ℝ≥0∞ := ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a with hS
      have hSucc : ∑ a ∈ Finset.range (n + 1), ENNReal.ofReal p_abort ^ a =
          1 + ENNReal.ofReal p_abort * S := by
        rw [Finset.sum_range_succ', pow_zero, add_comm]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => pow_succ' _ _
      rw [run_progSignBody_succ, tsum_probOutput_bind_mul]
      have h_ws : ∀ ws : Commit × PrvState,
          (∑' z : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= z | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
                | none =>
                    (progSignBody ids M pk sk msg n).run (c.cacheQuery (msg, ws.1) ch)] *
              QueryCache.enncard z.2)
          ≤ (QueryCache.enncard c + 1) +
              Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] *
                S := by
        intro ws
        rw [tsum_probOutput_bind_mul]
        have h_ch : ∀ ch : Chal,
            (∑' z : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache,
              Pr[= z | ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
                | none =>
                    (progSignBody ids M pk sk msg n).run
                      (c.cacheQuery (msg, ws.1) ch)] *
                QueryCache.enncard z.2)
            ≤ (QueryCache.enncard c + 1) +
                Pr[= none | ids.respond pk sk ws.2 ch] * S := by
          intro ch
          rw [tsum_probOutput_bind_mul]
          have h_oz : ∀ oz : Option Resp,
              (∑' z : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache,
                Pr[= z | (match oz with
                  | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
                  | none =>
                      (progSignBody ids M pk sk msg n).run
                        (c.cacheQuery (msg, ws.1) ch) :
                  ProbComp (Option (Commit × Resp) ×
                    (M × Commit →ₒ Chal).QueryCache))] *
                  QueryCache.enncard z.2)
              ≤ (QueryCache.enncard c + 1) + (if oz = none then S else 0) := by
            intro oz
            cases oz with
            | some z =>
                rw [if_neg (by simp), add_zero, tsum_probOutput_pure_mul]
                exact QueryCache.enncard_cacheQuery_le c (msg, ws.1) ch
            | none =>
                rw [if_pos rfl]
                refine le_trans (ih (c.cacheQuery (msg, ws.1) ch)) ?_
                exact add_le_add_left
                  (QueryCache.enncard_cacheQuery_le c (msg, ws.1) ch) S
          refine le_trans (tsum_probOutput_mul_le_add_of_le _ h_oz) ?_
          refine add_le_add_right (le_of_eq ?_) _
          rw [tsum_eq_single (none : Option Resp) fun oz hoz => by simp [hoz]]
          simp [mul_comm]
        refine le_trans (tsum_probOutput_mul_le_add_of_le _ h_ch) ?_
        refine add_le_add_right (le_of_eq ?_) _
        rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
        exact tsum_congr fun ch => (mul_assoc _ _ _).symm
      refine le_trans (tsum_probOutput_mul_le_add_of_le _ h_ws) ?_
      rw [hSucc]
      have : ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
          (Pr[= none | uniformSample Chal >>= fun ch =>
            ids.respond pk sk ws.2 ch] * S)
          ≤ ENNReal.ofReal p_abort * S := by
        calc ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              (Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch] * S)
            = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
                Pr[= none | uniformSample Chal >>= fun ch =>
                  ids.respond pk sk ws.2 ch]) * S := by
              rw [← ENNReal.tsum_mul_right]
              exact tsum_congr fun ws => (mul_assoc _ _ _).symm
          _ ≤ ENNReal.ofReal p_abort * S :=
              mul_le_mul_left
                (tsum_probOutput_commit_mul_abort_le ids pk sk hAbort) _
      calc QueryCache.enncard c + 1 +
            ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              (Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch] * S)
          ≤ QueryCache.enncard c + 1 + ENNReal.ofReal p_abort * S :=
            add_le_add_right this _
        _ = QueryCache.enncard c + (1 + ENNReal.ofReal p_abort * S) := by
            rw [add_assoc]

end FiatShamirWithAbort
