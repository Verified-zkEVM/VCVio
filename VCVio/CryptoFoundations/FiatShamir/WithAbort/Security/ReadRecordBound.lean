/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.SignStepCharge

/-!
# EUF-CMA for Fiat-Shamir with aborts: ReadRecordBound

The expected read/reject coincidence bound of the read-recording run and the resulting
bad-event bounds `prEvent_ghostBlindImpl_bad_le` and `prEvent_ghostRead_bad_le`.

Part of the CMA-to-NMA security development for the Fiat-Shamir-with-aborts
transform; `VCVio.CryptoFoundations.FiatShamir.WithAbort.Security` assembles
the headline `euf_cma_to_nma` and holds the overview docstring.
-/

public section

universe u v

open OracleComp OracleSpec
open scoped BigOperators ENNReal

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

section EUF_CMA

variable [SampleableType Stmt]
variable [DecidableEq Commit] [SampleableType Chal]
variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel)
  (M : Type) [DecidableEq M] (maxAttempts : ℕ)

section scaffold

variable (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))
variable (adv : SignatureAlg.UnforgeableAdversary
  (FiatShamirWithAbort.inROM ids hr M maxAttempts))

omit [SampleableType Stmt] in
/-- **The general per-pair charge over the inline read-recording run (induction carrier).** For an
arbitrary start state `s`, the expected pair count `E[Σ_{rc ∈ readlist} drawnlist.count rc]` is at
most the *un-charged pre-existing* contribution `E[Σ_{rc ∈ readlist} s.drawnlist.count rc]` (the
start drawn list, which the adversary may target deterministically) plus `ε` times the expected
`readlist.length · #new-attempts`, where `#new-attempts` counts only the draws and signing queries
made *after* `s` (the new drawn-list and signed-list growth). The base instance (empty start drawn
list) has a zero pre-existing term, giving `readRecord_expected_pairs_le`.

By induction on `oa`:
* **pure** — readlist and drawn list are the start ones; the pre-existing term *is* the pair count
  and there are no new attempts (equality).
* **read** — the drawn and signed lists are unchanged, so the bound passes through the inductive
  hypothesis (the bound never references the start *read* list, only the final one).
* **sign** — the body's fresh rejected draws extend the drawn list; the inductive hypothesis charges
  them as part of the continuation's pre-existing term, which splits as the genuine pre-existing
  term plus the body's contribution `E[Σ_{rc ∈ readlist} body-rejects.count rc]`, bounded by
  `ε · E[readlist.length · #body-rejects]` via the body charge `signStep_pair_charge` (the
  body's rejected values are independent of the value-free final read list); the residual `#new`
  attempt slack (`+1` per query) is absorbed. -/
theorem readRecord_expected_pairs_general {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr{let x ← Prod.fst <$> ids.commit pk sk}[x = cm] ≤ ENNReal.ofReal ε)
    (hAbort : Pr{let x ← ids.honestExecution pk sk}[x = none] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (hQ : oa.IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH)
    (s : DeferredReadState M Commit Chal) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr{let x ← (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s}[x = z] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ (∑' z : γ × DeferredReadState M Commit Chal,
          Pr{let x ← (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s}[x = z] *
            ((z.2.2.map (fun rc => s.1.1.2.count rc)).sum : ℝ≥0∞))
        + ENNReal.ofReal ε * ((s.2.length + qH : ℕ) : ℝ≥0∞) *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr{let x ← (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s}[x = z] *
              (((z.2.1.1.2.length - s.1.1.2.length)
                + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞) := by
  classical
  induction oa using OracleComp.inductionOn generalizing s qH with
  | pure a =>
      simp only [simulateQ_pure, StateT.run_pure, OracleComp.tsum_prEvent_pure_mul]
      simp only [add_zero, Nat.sub_eq_zero_of_le (le_refl _), Nat.cast_zero, mul_zero, add_zero]
      exact le_refl _
  | query_bind t ob ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      rw [OracleComp.tsum_prEvent_bind_mul, OracleComp.tsum_prEvent_bind_mul,
          OracleComp.tsum_prEvent_bind_mul,
        ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
      rcases t with (n | mc) | msg
      · -- UNIFORM: the step is deterministic in the state (`x.2 = s`); factor per step output and
        -- apply the inductive hypothesis directly (drawn / signed / read lists unchanged, budget
        -- unchanged: uniform queries are not read queries).
        have hQ2' : ∀ u, (ob u).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH := by
          intro u; exact hQ2 u
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support ((deferredDrawReadImpl ids M maxAttempts pk sk
            (Sum.inl (Sum.inl n))).run s)
        · have hxs : x ∈ support ((fun u => (u, s)) <$>
              (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hx
          rw [support_map] at hxs
          obtain ⟨u, _, rfl⟩ := hxs
          beta_reduce
          rw [mul_left_comm (ENNReal.ofReal ε * ((s.2.length + qH : ℕ) : ℝ≥0∞)), ← mul_add]
          gcongr
          exact ih u qH (hQ2' u) s
        · rw [prEvent_eq_zero_of_not_mem_support _ hx]; simp
      · -- READ: the post-state drawn / signed lists are unchanged; the read list grows by one and
        -- the read budget decrements by one, so the constant `readlist.length + qH` is preserved.
        have hpos : 0 < qH := by
          rcases hQ1 with h | h
          · exact absurd rfl h
          · exact h
        have hQ2' : ∀ cu : Chal × (M × Commit →ₒ Chal).QueryCache,
            (ob cu.1).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) (qH - 1) := by
          intro cu; exact hQ2 cu.1
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support ((deferredDrawReadImpl ids M maxAttempts pk sk
            (Sum.inl (Sum.inr mc))).run s)
        · have hxs : x ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                  mc.2 :: s.2))) <$> roStep M s.1.1.1.1 mc) := hx
          rw [support_map] at hxs
          obtain ⟨cu, _, rfl⟩ := hxs
          beta_reduce
          have hconst : ((s.2.length + qH : ℕ) : ℝ≥0∞)
              = (((mc.2 :: s.2).length + (qH - 1) : ℕ) : ℝ≥0∞) := by
            simp only [List.length_cons]; congr 1; omega
          rw [hconst, mul_left_comm (ENNReal.ofReal ε * (((mc.2 :: s.2).length + (qH - 1) : ℕ) :
            ℝ≥0∞)), ← mul_add]
          gcongr
          exact ih cu.1 (qH - 1) (hQ2' cu) ((((cu.2, s.1.1.1.2), s.1.1.2),
            s.1.2 || decide (mc.2 ∈ s.1.1.2)), mc.2 :: s.2)
        · rw [prEvent_eq_zero_of_not_mem_support _ hx]; simp
      · -- SIGN: the body's fresh rejected draws extend the drawn list; the body charge must keep
        -- the body draws *averaged* (a fixed body output lets the adversary target the recorded
        -- value), so the sum over body outputs is retained. The read budget is unchanged (signing
        -- is not a read query), so the continuation's `readlist.length` is bounded by the same
        -- constant `s.2.length + qH`. This is the value-free sign-step charge.
        have hQ2' : ∀ u, (ob u).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH := by
          intro u; exact hQ2 u
        exact signStep_pair_charge ids M maxAttempts qH ε p_abort hp₀ hp hε pk sk hGuess
          hAbort msg ob s hQ2' (fun u s' hQ' => ih u qH hQ' s')

omit [SampleableType Stmt] in
/-- **The value-free per-pair charge over the read-recording run**, consumed by
`readRecord_expected_coincidences_le`. The expected pair count
`E[Σ_{rc ∈ readlist} drawnlist.count rc]` of the `deferredDrawReadImpl` run is at most `ε · qH`
times the expected attempt count.

In this representation each rejected commitment is drawn *inline* at its signing step, so each fresh
draw sits in the independent-of-the-readlist position required by the atomic value-free charge
`tsum_prEvent_commit_mul_count_le`: the recorded reads answer from `roStep` on the real layer and
never the drawn (rejected) values, so the final read list is independent of every rejected draw.
The proof instantiates the inline-run induction `readRecord_expected_pairs_general` at the
empty-drawn-list start state, where the pre-existing term vanishes and the constant read-length
factor collapses to the read budget `qH`.

The charge is against `#attempts := drawnlist.length + (signedlist.length − l.length)`
(= #rejects + #signing-queries), whose mean is `qSrem/(1-p)`; the `drawnlist.length`-only form is
unsound (it omits the accepting attempts' fresh draws). The start drawn list is empty
(no pre-existing draws the adversary could target deterministically). -/
theorem readRecord_expected_pairs_le {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr{let x ← Prod.fst <$> ids.commit pk sk}[x = cm] ≤ ENNReal.ofReal ε)
    (hAbort : Pr{let x ← ids.honestExecution pk sk}[x = none] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (hQ : oa.IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr{let x ← ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, l), []), false), []))}[x = z] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
        ∑' z : γ × DeferredReadState M Commit Chal,
          Pr{let x ← ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
              ((((re, l), []), false), []))}[x = z] *
            ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) :
              ℝ≥0∞) := by
  -- Instantiate the general carrier at the empty-drawn-list start state: the pre-existing term
  -- vanishes (`[].count _ = 0`), the constant read-length factor `s.2.length + qH` becomes `qH`
  -- (empty start read list), and `#new-attempts` becomes the target `#attempts`.
  have hgen := readRecord_expected_pairs_general ids M maxAttempts qH ε p_abort hp₀ hp hε
    pk sk hGuess hAbort oa hQ ((((re, l), []), false), [])
  simp only [List.count_nil, List.map_const', List.sum_replicate, smul_zero, Nat.sub_zero,
    List.length_nil, Nat.cast_zero, mul_zero, tsum_zero, zero_add] at hgen
  exact hgen

omit [SampleableType Stmt] in
/-- **The expected-coincidence-count bound.**
The read-recording run's expected coincidence count
`E[#{ rc ∈ readlist : rc ∈ drawnlist }]` — the first moment fed by the Markov step
`readRecord_pred_le_expected_coincidences` — is at most `qSrem · (qH+1) · ε / (1-p)`. This
numeric inequality is where the ghost-read bound is charged.

**Accounting.** The coincidence count is the double sum
`Σ_{rc ∈ readlist} Σ_{d ∈ drawnlist} 1[rc = d]`, so its expectation decomposes over
(read, draw) pairs; no conditioning on the output is involved.
* Each recorded drawn commit `d` is a fresh i.i.d. raw `Prod.fst <$> ids.commit pk sk` draw of
  mass `≤ ε` (`hGuess`), recorded write-only on rejected attempts (the accept branch records
  `[]`).
* The recorded read-commit list is value-free: the reads answer from the real random-oracle
  layer via `roStep`, never from the drawn values (`ghostHybridImpl_proj_trans`), so the read
  list is independent of the drawn values.
* Hence each pair contributes `E[1[rc = d]] ≤ ε`, and there are at most
  `(qH+1) · E[#attempts]` pairs (`qH + 1` reads by `hQ`, and `E[#attempts] ≤ qSrem/(1-p)` by
  `deferredDrawRead_attemptKn_mean_le`), giving
  `E[count] ≤ (qH+1) · ε · E[#attempts] ≤ qSrem · (qH+1) · ε / (1-p)`.

**Proof structure.**
* The coincidence count is dominated pointwise by the pair count
  `Σ_{rc ∈ readlist} drawnlist.count rc` (`countP_mem_le_sum_count`).
* The recorded read list has length `≤ qH` on the whole support, a deterministic bound from
  the read-query budget (`deferredDrawReadImpl_run_readlist_length_le`, empty start read list).
* The expected attempt count is `≤ qSrem · (1/(1-p))` (`deferredDrawRead_attemptKn_mean_le`,
  empty start drawn list).
* The value-free per-pair charge `readRecord_expected_pairs_le` gives
  `E[Σ_{rc ∈ readlist} drawnlist.count rc] ≤ ε · qH · E[#attempts]`.

The independence of each fresh draw from the recorded read list through the adversary's
`simulateQ` fold is supplied by `readRecord_expected_pairs_le`. A fold that charged
only the sign steps would not suffice: for a pair whose draw precedes its read, the read-step
increment `1[mc.2 ∈ drawnlist]` is determined by the pre-state and is not `≤ ε` at that step.
The global independence of the read-list law from the drawn values is the value-substitution
invariant `deferredDrawRead_run_count_dl_invariant`, carried through
`readRecord_expected_pairs_general` and `signStep_pair_charge`.

The start drawn list is empty: the adversary's read points do not depend on the run's fresh
draws but could target a fixed pre-existing commitment deterministically. -/
theorem readRecord_expected_coincidences_le {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr{let x ← Prod.fst <$> ids.commit pk sk}[x = cm] ≤ ENNReal.ofReal ε)
    (hAbort : Pr{let x ← ids.honestExecution pk sk}[x = none] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (qSrem : ℕ)
    (hQ : FiatShamir.signHashQueryBound M (S' := Option (Commit × Resp)) (oa := oa) qSrem qH)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr{let x ← ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, l), []), false), []))}[x = z] *
          (z.2.2.countP (fun rc => decide (rc ∈ z.2.1.1.2)) : ℝ≥0∞))
      ≤ ENNReal.ofReal ((qSrem : ℝ) * ((qH : ℝ) + 1) * ε / (1 - p_abort)) := by
  classical
  obtain ⟨hQS, hQH⟩ := hQ
  set run : ProbComp (γ × DeferredReadState M Commit Chal) :=
    (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run ((((re, l), []), false), [])
    with hrun
  -- Step 1+2: dominate the coincidence count pointwise by the pair count.
  have hstep12 :
      (∑' z : γ × DeferredReadState M Commit Chal, Pr{let x ← run}[x = z] *
          (z.2.2.countP (fun rc => decide (rc ∈ z.2.1.1.2)) : ℝ≥0∞))
        ≤ ∑' z : γ × DeferredReadState M Commit Chal, Pr{let x ← run}[x = z] *
            ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞) := by
    refine ENNReal.tsum_le_tsum fun z => ?_
    gcongr
    exact_mod_cast countP_mem_le_sum_count z.2.2 z.2.1.1.2
  -- Step 3 (the atom): the expected pair count is `≤ ε · qH · E[#attempts]`, where the read-list
  -- length is dominated *deterministically* by the read-query budget `qH` (the constant factor
  -- threaded through the carrier), and `#attempts := drawnlist.length + (signedlist.length −
  -- l.length)` (= #rejects + #queries). The `#attempts` (not `drawnlist.length = #rejects`) factor
  -- is the one that dominates the pair count: it covers every reached attempt, not only the
  -- rejected ones, and its mean is still `qSrem/(1-p)`.
  have hatom :
      (∑' z : γ × DeferredReadState M Commit Chal, Pr{let x ← run}[x = z] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
        ≤ ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
          ∑' z : γ × DeferredReadState M Commit Chal, Pr{let x ← run}[x = z] *
            ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) :
              ℝ≥0∞) := by
    rw [hrun]
    exact readRecord_expected_pairs_le ids M maxAttempts qH ε p_abort hp₀ hp hε pk sk
      hGuess hAbort oa hQH re l
  -- Step 5: `E[#attempts] ≤ qSrem · (1/(1-p))` (empty start drawnlist;
  -- `deferredDrawRead_attemptKn_mean_le`).
  have hdraw :
      (∑' z : γ × DeferredReadState M Commit Chal, Pr{let x ← run}[x = z] *
          ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞))
        ≤ (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
    rw [hrun]
    exact deferredDrawRead_attemptKn_mean_le ids M maxAttempts pk sk hp₀ hp hAbort
      oa qSrem hQS re l
  -- Assemble the chain and convert to the target `ofReal` form. The exposed `(qH+1)` constant is
  -- the (loose) weakening of the deterministic read-length bound `qH`.
  refine le_trans hstep12 (le_trans hatom ?_)
  have hchain : ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
        ∑' z : γ × DeferredReadState M Commit Chal, Pr{let x ← run}[x = z] *
          ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)
      ≤ ENNReal.ofReal ε * ((qH : ℝ≥0∞) + 1) * (qSrem : ℝ≥0∞) *
        ENNReal.ofReal (1 / (1 - p_abort)) := by
    calc ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
            ∑' z : γ × DeferredReadState M Commit Chal, Pr{let x ← run}[x = z] *
              ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)
        ≤ ENNReal.ofReal ε * ((qH : ℝ≥0∞) + 1) *
            ∑' z : γ × DeferredReadState M Commit Chal, Pr{let x ← run}[x = z] *
              ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞) := by
          gcongr
          · exact le_self_add
      _ ≤ ENNReal.ofReal ε * ((qH : ℝ≥0∞) + 1) *
            ((qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort))) := by
          rw [mul_assoc, mul_assoc]
          gcongr
      _ = ENNReal.ofReal ε * ((qH : ℝ≥0∞) + 1) * (qSrem : ℝ≥0∞) *
            ENNReal.ofReal (1 / (1 - p_abort)) := by ring
  refine le_trans hchain (le_of_eq ?_)
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  rw [show ((qH : ℝ≥0∞) + 1) = ENNReal.ofReal ((qH : ℝ) + 1) by
        rw [ENNReal.ofReal_add (by positivity) (by norm_num)]; simp,
      show ((qSrem : ℝ≥0∞)) = ENNReal.ofReal (qSrem : ℝ) by simp]
  rw [← ENNReal.ofReal_mul hε, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

omit [SampleableType Stmt] in
/-- **Ghost-blind ghost-read bound.** The ghost-blind run's adversarial-read bad mass is at
most `qS·(qH+1)·ε/(1-p)`: the ghost-blind bad mass is reduced to the deferred-draw run
(`ghostBlind_bad_le_deferredDraw`), then to the
read-recording final-state read-hit predicate (`deferredDraw_bad_le_readRecord`), then to the
expected coincidence count by the Markov step (`readRecord_pred_le_expected_coincidences`),
which is finally charged by the numeric value-free bound `readRecord_expected_coincidences_le`.
Chaining with `prEvent_ghostHybridImpl_bad_le_ghostBlind` discharges the eager form
(`prEvent_ghostRead_bad_le`). -/
theorem prEvent_ghostBlindImpl_bad_le
    (qS qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit,
      Pr{let x ← Prod.fst <$> ids.commit pk sk}[x = cm] ≤ ENNReal.ofReal ε)
    (hAbort : Pr{let x ← ids.honestExecution pk sk}[x = none] ≤ ENNReal.ofReal p_abort) :
    Pr{let z ← ((simulateQ (ghostBlindImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false))}[z.2.2 = true]
      ≤ ENNReal.ofReal (qS * ((qH : ℝ) + 1) * ε / (1 - p_abort)) := by
  -- Reduce the ghost-blind bad mass to the deferred-draw run, then to the
  -- read-recording final-state predicate, then to the expected coincidence count (the Markov
  -- step), and charge that count by the numeric value-free bound.
  refine le_trans (ghostBlind_bad_le_deferredDraw ids M maxAttempts pk sk (adv.main pk)
    ((((∅, ∅), []), false) : GhostState M Commit Chal)
    ((((∅, []), []), false) : DeferredState M Commit Chal)
    ⟨rfl, rfl, fun mc h => absurd rfl h, by simp⟩) ?_
  refine le_trans (deferredDraw_bad_le_readRecord ids M maxAttempts pk sk (adv.main pk)
    ((((∅, []), []), false) : DeferredState M Commit Chal)
    (((((∅, []), []), false), []) : DeferredReadState M Commit Chal)
    ⟨rfl, fun h => absurd h (by simp)⟩) ?_
  refine le_trans (readRecord_pred_le_expected_coincidences ids M maxAttempts pk sk (adv.main pk)
    (((((∅, []), []), false), []) : DeferredReadState M Commit Chal)) ?_
  exact readRecord_expected_coincidences_le ids M maxAttempts qH ε p_abort hp₀ hp hε pk sk
    hGuess hAbort (adv.main pk) qS (hQ pk) ∅ []

omit [SampleableType Stmt] in
/-- **Ghost-read collision bound** for the Prog → Trans hop: the probability that the
adversary ever queries the random oracle at a ghost point (a rejected signing attempt's
programmed point) is at most `qS·(qH+1)·ε/(1-p)`.

Probabilistic content (deferred sampling): a rejected attempt's commitment `w` enters
the ghost layer with the joint law of `(w, c)` conditioned on rejection, and influences
the run only through the ghost-domain membership tests of later adversarial queries.
Per (rejected attempt `j`, adversarial query `k`) pair, the conditional independence of
the post-rejection run from `w` given the rejection event yields
`Pr{…}[query k hits attempt j] ≤ Pr{…}[attempt j runs] · ε` (the `1/Pr{…}[reject]` skew of the
conditioned commitment law cancels against the rejection probability of the attempt).
Summing the expected number of attempts (`≤ 1/(1-p)` per signing query by `hAbort`)
against the `qH` adversarial queries (`hQ`) gives the bound; the budget `qH + 1` leaves
one unit of slack for a verification read, which the freshness check already rules out
(see `ghostHybridImpl_preserves_signed_inv`).

The abort probability is assumed to lie in `[0, 1)` (`hp₀`, `hp`), which is what makes the
geometric attempt factor `1/(1 - p_abort)` well defined and at least `1`; `hε : 0 ≤ ε` matches
the per-attempt guessing bound `hGuess`, and `hQ` pins the query budgets `(qS, qH)` of
`adv.main pk`. The proof reduces the eager ghost-read bad mass to the ghost-blind run
(`prEvent_ghostHybridImpl_bad_le_ghostBlind`, identical until bad) and closes it with the
first-moment bound `prEvent_ghostBlindImpl_bad_le`. -/
lemma prEvent_ghostRead_bad_le
    (qS qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit,
      Pr{let x ← Prod.fst <$> ids.commit pk sk}[x = cm] ≤ ENNReal.ofReal ε)
    (hAbort : Pr{let x ← ids.honestExecution pk sk}[x = none] ≤ ENNReal.ofReal p_abort) :
    Pr{let z ← ((simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false))}[z.2.2 = true]
      ≤ ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort)) := by
  -- Reduce the eager ghost-read bad mass to the ghost-blind run's bad mass
  -- (`prEvent_ghostHybridImpl_bad_le_ghostBlind`, identical until bad); the ghost-blind
  -- bound `prEvent_ghostBlindImpl_bad_le` closes it at
  -- `qS·(qH+1)·ε/(1-p)`, with the numeric charge supplied by
  -- `readRecord_expected_coincidences_le`.
  refine (prEvent_ghostHybridImpl_bad_le_ghostBlind ids hr M maxAttempts adv pk sk).trans ?_
  refine le_trans (prEvent_ghostBlindImpl_bad_le ids hr M maxAttempts adv qS qH ε p_abort
    hp₀ hp hε hQ pk sk hGuess hAbort) (le_of_eq ?_)
  norm_cast

end scaffold

end EUF_CMA

end FiatShamirWithAbort
