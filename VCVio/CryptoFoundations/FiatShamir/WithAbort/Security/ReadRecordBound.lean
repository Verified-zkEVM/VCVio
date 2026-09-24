/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.SignStepCharge

/-!
# EUF-CMA for Fiat-Shamir with aborts: ReadRecordBound

The expected read/reject coincidence bounds of the read-recording run, for the
non-tape and tape presentations, and the resulting bad-event bounds
`probEvent_ghostBlindImpl_bad_le` and `probEvent_ghostRead_bad_le`.

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
list) has a zero pre-existing term, giving `readRecord_expected_pairs_nontape_le`.

By induction on `oa`:
* **pure** — readlist and drawn list are the start ones; the pre-existing term *is* the pair count
  and there are no new attempts (equality).
* **read** — the drawn and signed lists are unchanged, so the bound passes through the inductive
  hypothesis (the bound never references the start *read* list, only the final one).
* **sign** — the body's fresh rejected draws extend the drawn list; the inductive hypothesis charges
  them as part of the continuation's pre-existing term, which splits as the genuine pre-existing
  term plus the body's contribution `E[Σ_{rc ∈ readlist} body-rejects.count rc]`, bounded by
  `ε · E[readlist.length · #body-rejects]` via the body-charge `nontape_signStep_body_charge` (the
  body's rejected values are independent of the value-free final read list); the residual `#new`
  attempt slack (`+1` per query) is absorbed. -/
theorem readRecord_expected_pairs_nontape_general {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (hQ : oa.IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH)
    (s : DeferredReadState M Commit Chal) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ (∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] *
            ((z.2.2.map (fun rc => s.1.1.2.count rc)).sum : ℝ≥0∞))
        + ENNReal.ofReal ε * ((s.2.length + qH : ℕ) : ℝ≥0∞) *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] *
              (((z.2.1.1.2.length - s.1.1.2.length)
                + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞) := by
  classical
  induction oa using OracleComp.inductionOn generalizing s qH with
  | pure a =>
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      simp only [add_zero, Nat.sub_eq_zero_of_le (le_refl _), Nat.cast_zero, mul_zero, add_zero]
      exact le_refl _
  | query_bind t ob ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      rw [tsum_probOutput_bind_mul, tsum_probOutput_bind_mul, tsum_probOutput_bind_mul,
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
        · rw [probOutput_eq_zero_of_not_mem_support hx]; simp
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
        · rw [probOutput_eq_zero_of_not_mem_support hx]; simp
      · -- SIGN: the body's fresh rejected draws extend the drawn list; the body charge must keep
        -- the body draws *averaged* (a fixed body output lets the adversary target the recorded
        -- value), so the sum over body outputs is retained. The read budget is unchanged (signing
        -- is not a read query), so the continuation's `readlist.length` is bounded by the same
        -- constant `s.2.length + qH`. This is the value-free sign-step charge.
        have hQ2' : ∀ u, (ob u).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH := by
          intro u; exact hQ2 u
        exact nontape_signStep_charge ids M maxAttempts qH ε p_abort hp₀ hp hε pk sk hGuess
          hAbort msg ob s hQ2' (fun u s' hQ' => ih u qH hQ' s')

omit [SampleableType Stmt] in
/-- **The value-free per-pair charge over the *inline* (non-tape) read-recording run — the direct
characterization consumed by `readRecord_expected_coincidences_le`.** The expected pair count
`E[Σ_{rc ∈ readlist} drawnlist.count rc]` of the `deferredDrawReadImpl` run is at most `ε · qH`
times the expected attempt count.

In this representation each rejected commitment is drawn *inline* at its signing step, so each fresh
draw sits in the independent-of-the-readlist position required by the atomic value-free charge
`tsum_probOutput_commit_mul_count_le`: the recorded reads answer from `roStep` on the real layer and
never the drawn (rejected) values, so the final read list is independent of every rejected draw.
The proof instantiates the inline-run induction `readRecord_expected_pairs_nontape_general` at the
empty-drawn-list start state, where the pre-existing term vanishes and the constant read-length
factor collapses to the read budget `qH`.

The charge is against `#attempts := drawnlist.length + (signedlist.length − l.length)`
(= #rejects + #signing-queries), whose mean is `qSrem/(1-p)`; the `drawnlist.length`-only form is
unsound (it omits the accepting attempts' fresh draws). The start drawn list is empty
(no pre-existing draws the adversary could target deterministically).

The same inequality over the front-loaded tape representation is
`readRecord_expected_pairs_tape_le`; see also `readRecord_expected_pairs_le`, which restates this
bound with the tape's signing-query budget `qSrem` in scope. Both are separate reusable
infrastructure and are not on the live path. -/
theorem readRecord_expected_pairs_nontape_le {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (hQ : oa.IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, l), []), false), [])] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
        ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
              ((((re, l), []), false), [])] *
            ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) :
              ℝ≥0∞) := by
  -- Instantiate the general carrier at the empty-drawn-list start state: the pre-existing term
  -- vanishes (`[].count _ = 0`), the constant read-length factor `s.2.length + qH` becomes `qH`
  -- (empty start read list), and `#new-attempts` becomes the target `#attempts`.
  have hgen := readRecord_expected_pairs_nontape_general ids M maxAttempts qH ε p_abort hp₀ hp hε
    pk sk hGuess hAbort oa hQ ((((re, l), []), false), [])
  simp only [List.count_nil, List.map_const', List.sum_replicate, smul_zero, Nat.sub_zero,
    List.length_nil, Nat.cast_zero, mul_zero, tsum_zero, zero_add] at hgen
  exact hgen

omit [SampleableType Stmt] in
/-- **The value-free per-pair charge in the tape-factored representation.** Separate reusable
infrastructure: the same bound as `readRecord_expected_pairs_nontape_le`, stated over the
front-loaded run produced by `evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead`, in which the
read-recording run reads `drawList (ids.commit pk sk) (maxAttempts·qSrem) >>= fun tape => …` with
the draw tape sampled *upfront* as one independent block. It is not on the live path of
`readRecord_expected_coincidences_le`, which consumes the inline form directly.

In this representation the recorded drawn list is a function of the tape (its rejected entries)
while the recorded read list is **value-free** (the reads answer from `roStep` on the real layer,
never the tape values), so the read list is manifestly independent of the tape values. The
proof transports each tape probability back to the corresponding inline `deferredDrawReadImpl`
probability through the fold equality and applies `readRecord_expected_pairs_nontape_le`.

**The charge is against `#attempts`, not `drawnlist.length`.** The per-position reading of the bound
takes each *consumed* tape position (dropping the reject check): `drawnlist.count rc ≤ #consumed
positions k with `tape[k].1 = rc``, and for a fixed position `tape[k]` is a fresh raw
`Prod.fst <$> ids.commit` draw of mass `≤ ε` (`hGuess`), independent of the value-free `rc` and of
whether `k` is reached (reach depends only on *earlier* tape entries), giving
`≤ ε · readlist.length · #consumed`. The RHS therefore uses
`#attempts := drawnlist.length + (signedlist.length − l.length)`
(= #rejects + #signing-queries `≥` #consumed), whose mean is `qSrem/(1-p)`
(`deferredDrawRead_attemptKn_mean_le`). A `drawnlist.length`-form RHS would be false, since
charging all consumed positions exceeds the rejected-only count by the accepted positions,
`ε · E[#accepts]`.

The structural fact underlying the tape reading is *functional*, not distributional: the
accept/reject decision of `tapeSignBody` on the head `(w, st)` is `ids.respond pk sk st c = none`,
which depends on the `PrvState` part `st` and the challenge `c` but **not on the `Commit` part
`w`**. So for any fixed state and challenge randomness, at a position the body *rejects*, replacing
`tape[k].1 = w` by any other `w'` leaves the output, the real cache, and (therefore, through the
value-free `roStep` read channel) the recorded read list unchanged — only the recorded drawn list
changes. The accept branch returns `(some (w, z), [])`, so `w` enters the output/signature there,
which is why the reject indicator excludes accepted positions; the reject branch records `w`
write-only into the drawn list. On the inline route this same value-substitution fact is
`deferredDrawRead_run_count_dl_invariant`. -/
theorem readRecord_expected_pairs_tape_le {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (qSrem : ℕ)
    (hQ : FiatShamir.signHashQueryBound M (S' := Option (Commit × Resp)) (oa := oa) qSrem qH)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | OracleComp.drawList (ids.commit pk sk) (maxAttempts * qSrem) >>= fun tape =>
            (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) oa).run
                (((((re, l), []), false), []), tape)] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
        ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | OracleComp.drawList (ids.commit pk sk) (maxAttempts * qSrem) >>= fun tape =>
              (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                  (p.1, p.2.1)) <$>
                (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) oa).run
                  (((((re, l), []), false), []), tape)] *
            ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) :
              ℝ≥0∞) := by
  -- The content is the per-position value-free charge. The independence it rests on is
  -- `readlist ⊥ (rejected tape position's VALUE)`: the tape→readlist channel runs only through
  -- signatures (= ACCEPTED entries), so a rejected position's `Commit` value never enters any read
  -- target or query answer (reads answer via `roStep` on the real layer). Front-loading the draws
  -- (`evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead`) exhibits the draws as one independent
  -- block but does not by itself supply that independence.
  -- Transport BACK to the non-tape run via the fold equality: every tape probability equals the
  -- corresponding non-tape `deferredDrawReadImpl` run probability. This makes the recorded draws
  -- *inline-fresh* (drawn at each sign step) rather than front-loaded, which is the position in
  -- which each rejected draw is independent of the (value-free) final read list, and lets
  -- `readRecord_expected_pairs_nontape_le` discharge the goal.
  have hfold := evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead ids M maxAttempts pk sk oa qSrem
    hQ.1 ((((re, l), []), false), [])
  have hpr : ∀ z : γ × DeferredReadState M Commit Chal,
      Pr[= z | OracleComp.drawList (ids.commit pk sk) (maxAttempts * qSrem) >>= fun tape =>
          (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
              (p.1, p.2.1)) <$>
            (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) oa).run
              (((((re, l), []), false), []), tape)] =
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, l), []), false), [])] :=
    fun z => by rw [probOutput_def, probOutput_def, ← hfold]
  simp only [hpr]
  exact readRecord_expected_pairs_nontape_le ids M maxAttempts qH ε p_abort hp₀ hp hε pk sk
    hGuess hAbort oa hQ.2 re l

omit [SampleableType Stmt] in
/-- **The value-free per-pair atom, stated with the signing-query budget `qSrem` in scope.**
Separate reusable infrastructure obtained by routing `readRecord_expected_pairs_nontape_le` through
the tape representation and back; it is not on the live path of
`readRecord_expected_coincidences_le`, which consumes the inline form directly.

The expected pair count — the expected number of coinciding
`(recorded read-commit, recorded drawn commit)` pairs, `E[Σ_{rc ∈ readlist} drawnlist.count rc]` —
is at most `ε · qH` times the expected attempt count. The content is the per-pair value-free
independence: for every `(read slot, draw slot)` pair, `E[1[rc = d]] ≤ ε`, because
* each recorded drawn commit `d` is a fresh i.i.d. raw `Prod.fst <$> ids.commit pk sk` draw of mass
  `≤ ε` (`hGuess`), recorded write-only on rejected attempts (the accept branch records `[]`);
* the recorded read-commit list is **value-free** — the reads answer from the real RO layer via
  `roStep`, never the drawn values (`blindStepProj_map_ghostBlindImpl_indep` /
  `ghostHybridImpl_proj_trans`), so the readlist is jointly independent of the drawn *values*.

Summing the per-pair bound over the `readlist.length · drawnlist.length` pairs gives the claim. The
factoring `E[Σ_pairs 1[rc=d]] = Σ_pairs E[1[rc=d]]` cannot be read off a single step of the opaque
adversary `simulateQ (oa)` fold: a draw-before-read pair has its draw resolved before the later
read, so the read-step increment is deterministic in the pre-state and is not `≤ ε` at that step.
What supplies the bound instead is the global independence of the readlist law from the
drawn-value law, established on the inline route by the value-substitution invariant
`deferredDrawRead_run_count_dl_invariant` inside `nontape_signStep_charge`.

**Tape factorization.** The same independence is exhibited representationally by the two halves of
the tape factorization: `evalSPMF_ghostSignDrawBody_eq_drawList_tapeSignBody` recasts one signing
body's inline attempt draws as consumption from a pre-drawn tape
(`𝒮[(ghostSignDrawBody … n).run re] = 𝒮[drawList (ids.commit pk sk) n >>= tapeSignBody … tape]`)
via the local i.i.d. resampling commute `evalSPMF_bind_comm_probComp`, and
`evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead` lifts that across the `simulateQ (oa)` fold, so
the per-query tape blocks of every interleaved signing query commute to the very front as a single
independent draw block of `maxAttempts · qSrem` commitments, past the adaptive read points.

The surrounding reduction is `countP_mem_le_sum_count`, the deterministic readlist-length bound
`deferredDrawReadImpl_run_readlist_length_le`, the expected drawn-list length fold
`deferredDrawRead_run_expected_drawnlist_length_le`, and the final arithmetic. -/
theorem readRecord_expected_pairs_le {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (qSrem : ℕ)
    (hQ : FiatShamir.signHashQueryBound M (S' := Option (Commit × Resp)) (oa := oa) qSrem qH)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, l), []), false), [])] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
        ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
              ((((re, l), []), false), [])] *
            ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) :
              ℝ≥0∞) := by
  classical
  -- STEP C: transport both expectations through the fold-level tape factorization, so the recorded
  -- draws become a function of the front tape and the value-free read list becomes independent of
  -- the tape values.
  have hfold := evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead ids M maxAttempts pk sk oa qSrem
    hQ.1 ((((re, l), []), false), [])
  have hpr : ∀ z : γ × DeferredReadState M Commit Chal,
      Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
          ((((re, l), []), false), [])] =
        Pr[= z | OracleComp.drawList (ids.commit pk sk) (maxAttempts * qSrem) >>= fun tape =>
            (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) oa).run
                (((((re, l), []), false), []), tape)] :=
    fun z => by rw [probOutput_def, probOutput_def, hfold]
  simp only [hpr]
  -- The per-pair charge in the tape-factored representation: with `drawnlist = f(tape)` (recorded
  -- rejected tape entries) and `readlist` value-free (`roStep`), each `(read slot, draw slot)` pair
  -- charges at most `ε` by `hGuess` (each tape entry is a fresh raw `Prod.fst <$> ids.commit` draw
  -- of mass `≤ ε`, independent of the value-free read points).
  exact readRecord_expected_pairs_tape_le ids M maxAttempts qH ε p_abort hp₀ hp hε pk sk
    hGuess hAbort oa qSrem hQ re l

omit [SampleableType Stmt] in
/-- **The expected-coincidence-count bound (the numeric core of the first-moment route).**
The read-recording run's expected coincidence count
`E[#{ rc ∈ readlist : rc ∈ drawnlist }]` — the first moment fed by the Markov step
`readRecord_pred_le_expected_coincidences` — is at most `qSrem · (qH+1) · ε / (1-p)`.

This is the σ-free numeric form of the ghost-read charge (no front-loaded game, no all-miss
strategy `σ`): both the headline ghost-read bound and the `euf_cma` proof are charged through this
single numeric inequality.

**The accounting (why this is TRUE and additive — no per-output skew).** The coincidence count is a
double sum `Σ_{rc ∈ readlist} Σ_{d ∈ drawnlist} 1[rc = d]`, hence purely additive; the
rejection-conditioning skew that broke every `Pr[bad]` / per-output route lives in
output-conditioning, never in a SUM. Bounding `E[count]` decomposes over (read, draw) pairs:
* each recorded drawn commit `d` is a fresh i.i.d. raw `Prod.fst <$> ids.commit pk sk` draw of mass
  `≤ ε` (`hGuess`), recorded write-only on rejected attempts (the accept branch records `[]`);
* the recorded read-commit list is **value-free** — the reads answer from the real RO layer via
  `roStep`, never the drawn values (`blindStepProj_map_ghostBlindImpl_indep` /
  `ghostHybridImpl_proj_trans`), so the readlist is jointly independent of the drawn *values*;
* by that independence, for each pair `E[1[rc = d]] ≤ ε`, and there are `≤ (qH+1) · E[#attempts]`
  pairs (`(qH+1)` reads by `hQ`, `E[#attempts] ≤ qSrem/(1-p)` by `deferredDraw_attemptKn_mean_le`),
  giving `E[count] ≤ (qH+1) · ε · E[#attempts] ≤ qSrem · (qH+1) · ε / (1-p)`.

**The reduction.** The bound reduces by elementary arithmetic to a
single value-free atom (see the scaffolding lemmas above):
* the coincidence count is dominated pointwise by the pair count
  `Σ_{rc ∈ readlist} drawnlist.count rc` (`countP_mem_le_sum_count`);
* the recorded readlist has length `≤ qH` on the whole support — a *deterministic* bound from the
  read-query budget (`deferredDrawReadImpl_run_readlist_length_le`, empty start readlist);
* the expected drawn-list length is `≤ qSrem · (1/(1-p))` (`deferredDrawRead_run_expected_…`, empty
  start drawnlist);
* the genuine content is the **value-free per-pair atom**
  `readRecord_expected_pairs_nontape_le`:
  `E[Σ_{rc ∈ readlist} drawnlist.count rc] ≤ ε · E[readlist.length · drawnlist.length]`.

**Where the probabilistic content sits.** The arithmetic after factoring the joint expectation is
linear and discharged here; the factoring itself — that each fresh draw is conditionally i.i.d. and
`⊥` the recorded readlist *through the opaque adversary `simulateQ (oa)` fold* — is supplied by
`readRecord_expected_pairs_nontape_le`. A threaded fold charges the *sign* steps directly (each
fresh draw `⊥` the *current* readlist, value-free, additive), but a *draw-before-read* pair has its
draw resolved before the later read, so the read-step increment `1[mc.2 ∈ drawnlist]` is
deterministic in the pre-state and is not `≤ ε` at that single step. What covers it is the global
independence of the readlist law from the drawn-value law, established as the value-substitution
invariant `deferredDrawRead_run_count_dl_invariant` carried through
`readRecord_expected_pairs_nontape_general` / `nontape_signStep_charge`.

The start drawn list is empty (`ws₀ = []`): the bound is sound only with no pre-existing draws,
since the adversary's read points are value-free w.r.t. the run's fresh draws but can
deterministically target a fixed pre-existing commitment. The headline instance uses the empty
start. -/
theorem readRecord_expected_coincidences_le {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (qSrem : ℕ)
    (hQ : FiatShamir.signHashQueryBound M (S' := Option (Commit × Resp)) (oa := oa) qSrem qH)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, l), []), false), [])] *
          (z.2.2.countP (fun rc => decide (rc ∈ z.2.1.1.2)) : ℝ≥0∞))
      ≤ ENNReal.ofReal ((qSrem : ℝ) * ((qH : ℝ) + 1) * ε / (1 - p_abort)) := by
  classical
  obtain ⟨hQS, hQH⟩ := hQ
  set run : ProbComp (γ × DeferredReadState M Commit Chal) :=
    (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run ((((re, l), []), false), [])
    with hrun
  -- Step 1+2: dominate the coincidence count pointwise by the pair count.
  have hstep12 :
      (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
          (z.2.2.countP (fun rc => decide (rc ∈ z.2.1.1.2)) : ℝ≥0∞))
        ≤ ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
            ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞) := by
    refine ENNReal.tsum_le_tsum fun z => ?_
    gcongr
    exact_mod_cast countP_mem_le_sum_count z.2.2 z.2.1.1.2
  -- Step 3 (the atom): the expected pair count is `≤ ε · qH · E[#attempts]`, where the read-list
  -- length is dominated *deterministically* by the read-query budget `qH` (the constant factor
  -- threaded through the carrier), and `#attempts := drawnlist.length + (signedlist.length −
  -- l.length)` (= #rejects + #queries). The `#attempts` (not `drawnlist.length = #rejects`) factor
  -- is the sound charge: charging per consumed tape position (drop-reject) covers all reached
  -- attempts, which dominates the rejected ones; its mean is the same `qSrem/(1-p)` as the drawn.
  have hatom :
      (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
        ≤ ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
          ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
            ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) :
              ℝ≥0∞) := by
    rw [hrun]
    exact readRecord_expected_pairs_nontape_le ids M maxAttempts qH ε p_abort hp₀ hp hε pk sk
      hGuess hAbort oa hQH re l
  -- Step 5: `E[#attempts] ≤ qSrem · (1/(1-p))` (empty start drawnlist;
  -- `deferredDrawRead_attemptKn_mean_le`).
  have hdraw :
      (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
          ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞))
        ≤ (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
    rw [hrun]
    exact deferredDrawRead_attemptKn_mean_le ids M maxAttempts pk sk hp₀ hp hAbort
      oa qSrem hQS re l
  -- Assemble the chain and convert to the target `ofReal` form. The exposed `(qH+1)` constant is
  -- the (loose) weakening of the deterministic read-length bound `qH`.
  refine le_trans hstep12 (le_trans hatom ?_)
  have hchain : ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
        ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
          ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)
      ≤ ENNReal.ofReal ε * ((qH : ℝ≥0∞) + 1) * (qSrem : ℝ≥0∞) *
        ENNReal.ofReal (1 / (1 - p_abort)) := by
    calc ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
            ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
              ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)
        ≤ ENNReal.ofReal ε * ((qH : ℝ≥0∞) + 1) *
            ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
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
/-- **Ghost-blind ghost-read bound** (the sound headline target). The ghost-blind run's
adversarial-read bad mass is at most `qS·(qH+1)·ε/(1-p)`, via the first-moment route: the eager bad
mass is reduced to the deferred-draw run (`ghostBlind_bad_le_deferredDraw`), then to the
read-recording final-state read-hit predicate (`deferredDraw_bad_le_readRecord`), then to the
expected coincidence count by the Markov step (`readRecord_pred_le_expected_coincidences`),
which is finally charged by the numeric value-free bound `readRecord_expected_coincidences_le`.
Chaining with `probEvent_ghostHybridImpl_bad_le_ghostBlind` discharges the eager form
(`probEvent_ghostRead_bad_le`). -/
theorem probEvent_ghostBlindImpl_bad_le
    (qS qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      ≤ ENNReal.ofReal (qS * ((qH : ℝ) + 1) * ε / (1 - p_abort)) := by
  -- The first-moment route: reduce the eager bad mass to the deferred-draw run, then to the
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
`Pr[query k hits attempt j] ≤ Pr[attempt j runs] · ε` (the `1/Pr[reject]` skew of the
conditioned commitment law cancels against the rejection probability of the attempt).
Summing the expected number of attempts (`≤ 1/(1-p)` per signing query by `hAbort`)
against the `qH` adversarial queries (`hQ`) gives the bound; the budget `qH + 1` leaves
one unit of slack for a verification read, which the freshness check already rules out
(see `ghostHybridImpl_preserves_signed_inv`).

The abort probability is assumed to lie in `[0, 1)` (`hp₀`, `hp`), which is what makes the
geometric attempt factor `1/(1 - p_abort)` well defined and at least `1`; `hε : 0 ≤ ε` matches
the per-attempt guessing bound `hGuess`, and `hQ` pins the query budgets `(qS, qH)` of
`adv.main pk`. The proof reduces the eager ghost-read bad mass to the ghost-blind run
(`probEvent_ghostHybridImpl_bad_le_ghostBlind`, identical until bad) and closes it with the
first-moment bound `probEvent_ghostBlindImpl_bad_le`. -/
lemma probEvent_ghostRead_bad_le
    (qS qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      ≤ ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort)) := by
  -- M1 reduces the eager ghost-read bad mass to the ghost-blind run's bad mass
  -- (`probEvent_ghostHybridImpl_bad_le_ghostBlind`, identical until bad), and the ghost-blind
  -- bound `probEvent_ghostBlindImpl_bad_le` (the first-moment route) closes it at
  -- `qS·(qH+1)·ε/(1-p)`, with the numeric charge supplied by
  -- `readRecord_expected_coincidences_le`.
  refine (probEvent_ghostHybridImpl_bad_le_ghostBlind ids hr M maxAttempts adv pk sk).trans ?_
  refine le_trans (probEvent_ghostBlindImpl_bad_le ids hr M maxAttempts adv qS qH ε p_abort
    hp₀ hp hε hQ pk sk hGuess hAbort) (le_of_eq ?_)
  norm_cast

end scaffold

end EUF_CMA

end FiatShamirWithAbort
