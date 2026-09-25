/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.ReadRecording

/-!
# EUF-CMA for Fiat-Shamir with aborts: FirstMoment

The first-moment reduction scaffolding for the coincidence-count bound: expected
drawn-list and attempt-count bounds for the deferred draw-and-read handler, its
never-fail and prefix invariants, and the list-counting identities the later charges
use.

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

/-! ### First-moment reduction scaffolding for the coincidence-count bound

The numeric residual `readRecord_expected_coincidences_le` reduces, by elementary arithmetic, to a
single value-free cross-term atom. The reduction chain:

* the coincidence count is dominated by the pair count
  `Σ_{rc ∈ readlist} drawnlist.count rc` (`List.countP_le_sum_count_mem`);
* the *number of recorded reads* is bounded **deterministically** by the read-query budget `qH`
  (`deferredDrawReadImpl_run_readlist_length_le`), so the read-recording run's readlist length is at
  most `s.readlist.length + qH`;
* the expected drawn-list length of the read-recording run is at most
  `s.drawnlist.length + qSrem · (1/(1-p))` (`deferredDrawRead_run_expected_drawnlist_length_le`, the
  read-recording counterpart of `deferredDraw_run_expected_length_le`);
* the genuine content is then the **value-free per-pair atom**
  `readRecord_expected_pairs_nontape_le`: the expected pair count is at most `ε` times the expected
  `readlist.length · drawnlist.length`, because each recorded drawn commit is a fresh raw
  `Prod.fst <$> ids.commit` draw (mass `≤ ε`) and is independent of the value-free recorded
  read-commit list.

`readRecord_expected_coincidences_le` chains these with the deterministic read bound
(`readlist.length ≤ qH+1` from the empty start) and the final-arithmetic conversion.

The tape factorization (`tapeDrawReadImpl`, `evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead`,
`readRecord_expected_pairs_tape_le`, `readRecord_expected_pairs_le`) is a separate, reusable
front-loading representation of the same run; it is not on the live path of the chain above. -/

/-- Domination of the membership count by the per-element coincidence count: the number of recorded
read-commits lying in the drawn list is at most `Σ_{rc ∈ readlist} drawnlist.count rc`, the total
number of coinciding `(read, draw)` pairs. -/
lemma countP_mem_le_sum_count {α : Type} [DecidableEq α] (l d : List α) :
    l.countP (fun rc => decide (rc ∈ d)) ≤ (l.map (fun rc => d.count rc)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.countP_cons, List.map_cons, List.sum_cons]
      by_cases h : a ∈ d
      · simp only [decide_eq_true_eq, h, ite_true]
        have : 1 ≤ d.count a := List.one_le_count_iff.mpr h
        omega
      · simp only [decide_eq_true_eq, h, ite_false]
        omega

/-- Expressing a `List.count` as a sum of equality indicators over the list. -/
private lemma count_eq_sum_map_ite {α : Type} [DecidableEq α] (d : List α) (a : α) :
    (d.map (fun w => (if w = a then 1 else 0))).sum = d.count a := by
  induction d with
  | nil => simp
  | cons x d ih =>
      simp only [List.map_cons, List.sum_cons, ih, List.count_cons]
      by_cases h : x = a
      · simp [h]; ring
      · simp [h]

/-- **Symmetric double-count of two lists.** Summing `d.count rc` over `rc ∈ l` equals summing
`l.count w` over `w ∈ d`; both count the coinciding `(read, draw)` pairs
(`Σ_x l.count x · d.count x`). This re-index lets the per-pair charge be organised by the
*draw* list (whose entries are fresh i.i.d. commitments) rather than the read list. -/
lemma sum_map_count_comm {α : Type} [DecidableEq α] (l d : List α) :
    (l.map (fun rc => d.count rc)).sum = (d.map (fun w => l.count w)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      have key : (d.map (fun w => (a :: l).count w)).sum
          = (d.map (fun w => (if w = a then 1 else 0))).sum + (d.map (fun w => l.count w)).sum := by
        rw [← List.sum_map_add]
        refine congrArg _ (List.map_congr_left fun w _ => ?_)
        rw [List.count_cons]
        by_cases h : w = a
        · subst h; simp [add_comm]
        · simp [h, Ne.symm h]
      rw [key, count_eq_sum_map_ite, add_comm]

omit [SampleableType Stmt] in
/-- **Deterministic readlist-length bound.** Every reachable final state of the read-recording run
records at most `qH` new read-commits, where `qH` bounds the random-oracle (read) queries `oa` makes
(the `(· matches .inl (.inr _))` component of `signHashQueryBound`): each read step prepends exactly
one commitment to the recorded read-commit list and uniform/signing steps leave it untouched. Hence
`readlist.length ≤ s.readlist.length + qH` on the whole support — a *deterministic* (support-wide)
bound, used to dominate the random `readlist.length` factor of the pair count by the constant
`qH`. -/
theorem deferredDrawReadImpl_run_readlist_length_le {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (qH : ℕ), oa.IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH →
      ∀ (s : DeferredReadState M Commit Chal)
        (z : γ × DeferredReadState M Commit Chal),
        z ∈ support ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s) →
        z.2.2.length ≤ s.2.length + qH := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qH _ s z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; simp
  | query_bind t ob ih =>
      intro qH hQ s z hz
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      rcases t with (n | mc) | msg
      · -- UNIFORM: readlist untouched; budget unchanged.
        have hxs : x ∈ support ((fun u => (u, s)) <$>
            (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hx
        rw [support_map] at hxs
        obtain ⟨u, _, rfl⟩ := hxs
        have hih := ih u qH (by simpa using hQ2 u) s z hzx
        simpa using hih
      · -- READ: readlist grows by one; budget decrements by one (`0 < qH`).
        have hpos : 0 < qH := by
          rcases hQ1 with hno | hpos
          · exact absurd rfl hno
          · exact hpos
        have hxs : x ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                mc.2 :: s.2))) <$>
              roStep M s.1.1.1.1 mc) := hx
        rw [support_map] at hxs
        obtain ⟨cu, _, rfl⟩ := hxs
        have hih := ih cu.1 (qH - 1) (by simpa using hQ2 cu.1)
          ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)), mc.2 :: s.2) z hzx
        simp only [List.length_cons] at hih
        omega
      · -- SIGN: readlist untouched; budget unchanged.
        have hxs : x ∈ support ((fun alc : (Option (Commit × Resp) × List Commit) ×
            (M × Commit →ₒ Chal).QueryCache =>
            (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1) := hx
        rw [support_map] at hxs
        obtain ⟨alc, _, rfl⟩ := hxs
        have hih := ih alc.1.1 qH (by simpa using hQ2 alc.1.1)
          ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2) z hzx
        simpa using hih

omit [SampleableType Stmt] in
/-- **Per-step expected drawn-list length growth of the read-recording handler.** One step of
`deferredDrawReadImpl` grows the expected drawn-list length by at most `1/(1-p)` on a signing query
and by `0` on uniform / random-oracle-read queries (which leave the drawn list `s.1.1.2`
untouched). Identical to `deferredDrawImpl_step_expected_length_le` on the underlying deferred
state; the extra read-commit list is irrelevant to the drawn-list length. -/
lemma deferredDrawReadImpl_step_expected_drawnlist_length_le (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : DeferredReadState M Commit Chal) :
    (∑' z : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t) ×
        DeferredReadState M Commit Chal,
      Pr[= z | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
        (z.2.1.1.2.length : ℝ≥0∞))
      ≤ (s.1.1.2.length : ℝ≥0∞) +
          (if (t matches Sum.inr _) then ENNReal.ofReal (1 / (1 - p_abort)) else 0) := by
  classical
  rcases t with (n | mc) | msg
  · -- UNIFORM: state untouched, drawn list `s.1.1.2` preserved.
    rw [ite_eq_right (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ (by simp [deferredDrawReadImpl]))
    intro z hz
    have hzs : z ∈ support ((fun u => (u, s)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hz
    rw [support_map] at hzs
    obtain ⟨u, _, rfl⟩ := hzs; rfl
  · -- READ: writes only the base cache / bad flag / readlist; drawn list `s.1.1.2` preserved.
    rw [ite_eq_right (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ ?_)
    · intro z hz
      have hzs : z ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
              mc.2 :: s.2))) <$>
            roStep M s.1.1.1.1 mc) := hz
      rw [support_map] at hzs
      obtain ⟨cu, _, rfl⟩ := hzs; rfl
    · simp only [deferredDrawReadImpl, StateT.run_mk]
      rcases hg : s.1.1.1.1 mc with _ | v <;> simp [roStep, hg]
  · -- SIGN: drawn list becomes `s.1.1.2 ++ alc.1.2`; expected new length ≤ 1/(1-p).
    rw [ite_eq_left (by simp)]
    have hrun : (deferredDrawReadImpl ids M maxAttempts pk sk (.inr msg)).run s =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1 := rfl
    rw [hrun]
    refine le_of_eq_of_le (tsum_probOutput_map_mul
      ((ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1)
      (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
        (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)))
      (fun z => (z.2.1.1.2.length : ℝ≥0∞))) ?_
    calc _
        = ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              ((s.1.1.2.length : ℝ≥0∞) + (alc.1.2.length : ℝ≥0∞)) := by
          refine tsum_congr fun alc => ?_
          simp only [List.length_append]
          push_cast
          ring
      _ = (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              (s.1.1.2.length : ℝ≥0∞)) +
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              (alc.1.2.length : ℝ≥0∞) := by
          rw [← ENNReal.tsum_add]; exact tsum_congr fun alc => by rw [mul_add]
      _ ≤ (s.1.1.2.length : ℝ≥0∞) + ENNReal.ofReal (1 / (1 - p_abort)) := by
          refine add_le_add ?_ ?_
          · rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]
          · exact le_trans (tsum_probOutput_run_ghostSignDrawBody_mul_length_le ids M pk sk msg
              hAbort maxAttempts s.1.1.1.1) (geomAttemptSum_le maxAttempts hp₀ hp)

omit [SampleableType Stmt] in
/-- **Run-level expected drawn-list length of the read-recording run.** By induction on `oa`, the
expected final drawn-list length of the read-recording run from a start state `s` is at most
`s.drawnlist.length + qSrem · (1/(1-p))`, where `qSrem` bounds the number of signing queries. The
read-recording counterpart of `deferredDraw_run_expected_length_le`: the drawn list evolves
identically (the recorded read-commit list never affects it), so the per-step charge
`deferredDrawReadImpl_step_expected_drawnlist_length_le` telescopes against the signing-query budget
exactly as before. -/
theorem deferredDrawRead_run_expected_drawnlist_length_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (qSrem : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) qSrem →
      ∀ (s : DeferredReadState M Commit Chal),
        (∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] *
            (z.2.1.1.2.length : ℝ≥0∞))
          ≤ (s.1.1.2.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qSrem _ s
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      exact le_self_add
  | query_bind t ob ih =>
      intro qSrem hQ s
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rw [simulateQ_query_bind, StateT.run_bind, tsum_probOutput_bind_mul]
      set c : ℝ≥0∞ := ENNReal.ofReal (1 / (1 - p_abort)) with hc
      have hmass : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
            (M →ₒ Option (Commit × Resp))).Range t) × DeferredReadState M Commit Chal,
          Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s]) = 1 :=
        tsum_probOutput_eq_one' (by
          rcases t with (n | mc) | msg
          · simp [deferredDrawReadImpl]
          · simp only [deferredDrawReadImpl, StateT.run_mk]
            rcases hg : s.1.1.1.1 mc with _ | v <;> simp [roStep, hg]
          · simp [deferredDrawReadImpl])
      have hfold : ∀ (b : ℕ) (extra : ℝ≥0∞),
          (∀ x : (((unifSpec + (M × Commit →ₒ Chal)) +
              (M →ₒ Option (Commit × Resp))).Range t) × DeferredReadState M Commit Chal,
            (∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                  (ob x.1)).run x.2] * (z.2.1.1.2.length : ℝ≥0∞))
              ≤ (x.2.1.1.2.length : ℝ≥0∞) + (b : ℝ≥0∞) * c) →
          (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
            (x.2.1.1.2.length : ℝ≥0∞)) ≤ (s.1.1.2.length : ℝ≥0∞) + extra →
          extra + (b : ℝ≥0∞) * c ≤ (qSrem : ℝ≥0∞) * c →
          (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob x.1)).run x.2] * (z.2.1.1.2.length : ℝ≥0∞))
            ≤ (s.1.1.2.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by
        intro b extra hcont hstep hbudget
        calc (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                ∑' z : γ × DeferredReadState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                      (ob x.1)).run x.2] * (z.2.1.1.2.length : ℝ≥0∞))
            ≤ ∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                ((x.2.1.1.2.length : ℝ≥0∞) + (b : ℝ≥0∞) * c) :=
              ENNReal.tsum_le_tsum fun x => by gcongr; exact hcont x
          _ = (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                  (x.2.1.1.2.length : ℝ≥0∞)) + (b : ℝ≥0∞) * c := by
              rw [show (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                    ((x.2.1.1.2.length : ℝ≥0∞) + (b : ℝ≥0∞) * c))
                  = ∑' x, (Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                      (x.2.1.1.2.length : ℝ≥0∞) +
                    Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                      ((b : ℝ≥0∞) * c)) from tsum_congr fun x => by rw [mul_add]]
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
          _ ≤ ((s.1.1.2.length : ℝ≥0∞) + extra) + (b : ℝ≥0∞) * c := by gcongr
          _ ≤ (s.1.1.2.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by rw [add_assoc]; gcongr
      rcases t with (n | mc) | msg
      · refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawReadImpl_step_expected_drawnlist_length_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inl n)) s
      · refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawReadImpl_step_expected_drawnlist_length_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inr mc)) s
      · have hpos : 0 < qSrem := by
          rcases hQ1 with hno | hpos
          · exact absurd (by simp) hno
          · exact hpos
        refine hfold (qSrem - 1) c (fun x => ih x.1 (qSrem - 1) (by simpa using hQ2 x.1) x.2) ?_ ?_
        · have hstep := deferredDrawReadImpl_step_expected_drawnlist_length_le ids M maxAttempts
            pk sk hp₀ hp hAbort (.inr msg) s
          rwa [ite_eq_left (by rfl), ← hc] at hstep
        · rw [add_comm, ← add_one_mul,
            show ((qSrem - 1 : ℕ) : ℝ≥0∞) + 1 = (qSrem : ℝ≥0∞) by
              have : qSrem - 1 + 1 = qSrem := by omega
              rw [← this]; push_cast; ring]

omit [SampleableType Stmt] in
/-- **Per-step expected attempt-count growth of the read-recording handler.** One step of
`deferredDrawReadImpl` grows the expected combined size `drawnlist.length + signedlist.length` by at
most `1/(1-p)` on a signing query and by `0` on a uniform or random-oracle-read query (which leave
both lists untouched). The read-recording counterpart of
`deferredDrawImpl_step_expected_attemptCount_le`; the recorded read-commit list never affects the
drawn or signed lists, so the charge is identical. -/
lemma deferredDrawReadImpl_step_expected_attemptCount_le (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : DeferredReadState M Commit Chal) :
    (∑' z : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t) ×
        DeferredReadState M Commit Chal,
      Pr[= z | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
        ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
      ≤ ((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) +
          (if (t matches Sum.inr _) then ENNReal.ofReal (1 / (1 - p_abort)) else 0) := by
  classical
  rcases t with (n | mc) | msg
  · rw [ite_eq_right (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ (by simp [deferredDrawReadImpl]))
    intro z hz
    have hzs : z ∈ support ((fun u => (u, s)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hz
    rw [support_map] at hzs
    obtain ⟨u, _, rfl⟩ := hzs; rfl
  · rw [ite_eq_right (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ ?_)
    · intro z hz
      have hzs : z ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
              mc.2 :: s.2))) <$>
            roStep M s.1.1.1.1 mc) := hz
      rw [support_map] at hzs
      obtain ⟨cu, _, rfl⟩ := hzs; rfl
    · simp only [deferredDrawReadImpl, StateT.run_mk]
      rcases hg : s.1.1.1.1 mc with _ | v <;> simp [roStep, hg]
  · rw [ite_eq_left (by simp)]
    have hrun : (deferredDrawReadImpl ids M maxAttempts pk sk (.inr msg)).run s =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1 := rfl
    rw [hrun]
    refine le_of_eq_of_le (tsum_probOutput_map_mul
      ((ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1)
      (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
        (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)))
      (fun z => ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))) ?_
    calc _
        = ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              (((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) + (1 : ℝ≥0∞) +
                (alc.1.2.length : ℝ≥0∞)) := by
          refine tsum_congr fun alc => ?_
          simp only [List.length_append, List.length_cons]
          push_cast
          ring
      _ = ((∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              (((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) + (1 : ℝ≥0∞))) +
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              (alc.1.2.length : ℝ≥0∞)) := by
          rw [← ENNReal.tsum_add]; exact tsum_congr fun alc => by rw [mul_add]
      _ ≤ ((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) +
            ENNReal.ofReal (1 / (1 - p_abort)) := by
          rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]
          rw [add_assoc]
          gcongr
          refine le_trans (add_le_add_right
            (tsum_probOutput_run_ghostSignDrawBody_mul_length_le_tight ids M pk sk msg
              hAbort maxAttempts s.1.1.1.1) _) ?_
          rw [add_comm]
          refine le_trans (le_of_eq ?_) (geomSum_le hp₀ hp (maxAttempts + 1))
          rw [Finset.sum_range_succ']
          simp only [pow_zero]

omit [SampleableType Stmt] in
/-- **Run-level expected attempt count of the read-recording run.** By induction on `oa`, the
expected combined size `drawnlist.length + signedlist.length` of the read-recording run from a start
state `s` is at most `(s.drawnlist.length + s.signedlist.length) + qSrem · (1/(1-p))`, where `qSrem`
bounds the number of signing queries. The read-recording counterpart of
`deferredDraw_run_expected_attemptCount_le`. Subtracting the start signed-list length `l.length`
gives the attempt-count mean `≤ qSrem/(1-p)` used by the sound `#attempts`-form coincidence
bound. -/
theorem deferredDrawRead_run_expected_attemptCount_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (qSrem : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) qSrem →
      ∀ (s : DeferredReadState M Commit Chal),
        (∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] *
            ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
          ≤ ((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) +
              (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qSrem _ s
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      exact le_self_add
  | query_bind t ob ih =>
      intro qSrem hQ s
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rw [simulateQ_query_bind, StateT.run_bind, tsum_probOutput_bind_mul]
      set c : ℝ≥0∞ := ENNReal.ofReal (1 / (1 - p_abort)) with hc
      have hmass : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
            (M →ₒ Option (Commit × Resp))).Range t) × DeferredReadState M Commit Chal,
          Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s]) = 1 :=
        tsum_probOutput_eq_one' (by
          rcases t with (n | mc) | msg
          · simp [deferredDrawReadImpl]
          · simp only [deferredDrawReadImpl, StateT.run_mk]
            rcases hg : s.1.1.1.1 mc with _ | v <;> simp [roStep, hg]
          · simp [deferredDrawReadImpl])
      have hfold : ∀ (b : ℕ) (extra : ℝ≥0∞),
          (∀ x : (((unifSpec + (M × Commit →ₒ Chal)) +
              (M →ₒ Option (Commit × Resp))).Range t) × DeferredReadState M Commit Chal,
            (∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                  (ob x.1)).run x.2] * ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
              ≤ ((x.2.1.1.2.length + x.2.1.1.1.2.length : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) * c) →
          (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
            ((x.2.1.1.2.length + x.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
              ≤ ((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) + extra →
          extra + (b : ℝ≥0∞) * c ≤ (qSrem : ℝ≥0∞) * c →
          (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob x.1)).run x.2] * ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
            ≤ ((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by
        intro b extra hcont hstep hbudget
        calc (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                ∑' z : γ × DeferredReadState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                      (ob x.1)).run x.2] * ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
            ≤ ∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                (((x.2.1.1.2.length + x.2.1.1.1.2.length : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) * c) :=
              ENNReal.tsum_le_tsum fun x => by gcongr; exact hcont x
          _ = (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                  ((x.2.1.1.2.length + x.2.1.1.1.2.length : ℕ) : ℝ≥0∞)) + (b : ℝ≥0∞) * c := by
              rw [show (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                    (((x.2.1.1.2.length + x.2.1.1.1.2.length : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) * c))
                  = ∑' x, (Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                      ((x.2.1.1.2.length + x.2.1.1.1.2.length : ℕ) : ℝ≥0∞) +
                    Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                      ((b : ℝ≥0∞) * c)) from tsum_congr fun x => by rw [mul_add]]
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
          _ ≤ (((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) + extra) + (b : ℝ≥0∞) * c := by
              gcongr
          _ ≤ ((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by
              rw [add_assoc]; gcongr
      rcases t with (n | mc) | msg
      · refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawReadImpl_step_expected_attemptCount_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inl n)) s
      · refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawReadImpl_step_expected_attemptCount_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inr mc)) s
      · have hpos : 0 < qSrem := by
          rcases hQ1 with hno | hpos
          · exact absurd (by simp) hno
          · exact hpos
        refine hfold (qSrem - 1) c (fun x => ih x.1 (qSrem - 1) (by simpa using hQ2 x.1) x.2) ?_ ?_
        · have hstep := deferredDrawReadImpl_step_expected_attemptCount_le ids M maxAttempts
            pk sk hp₀ hp hAbort (.inr msg) s
          rwa [ite_eq_left (by rfl), ← hc] at hstep
        · rw [add_comm, ← add_one_mul,
            show ((qSrem - 1 : ℕ) : ℝ≥0∞) + 1 = (qSrem : ℝ≥0∞) by
              have : qSrem - 1 + 1 = qSrem := by omega
              rw [← this]; push_cast; ring]

omit [SampleableType Stmt] in
/-- **The read-recording run never fails.** Every step of `deferredDrawReadImpl` pushes forward a
non-failing `ProbComp`, so the whole fold has zero failure mass. -/
theorem deferredDrawRead_run_neverFail {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s : DeferredReadState M Commit Chal),
      Pr[⊥ | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] = 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s; simp [simulateQ_pure, StateT.run_pure]
  | query_bind t ob ih =>
      intro s
      rw [simulateQ_query_bind, StateT.run_bind, probFailure_bind_eq_zero_iff]
      refine ⟨?_, fun x _ => ih x.1 x.2⟩
      rcases t with (n | mc) | msg
      · simp [deferredDrawReadImpl]
      · simp only [deferredDrawReadImpl]
        rcases hg : s.1.1.1.1 mc with _ | v <;> simp [roStep, hg]
      · simp [deferredDrawReadImpl]

omit [SampleableType Stmt] in
/-- **The signed-message list of the read-recording run grows.** From any start state the recorded
signed-message list only ever gets longer, so its start length `l.length` is a lower bound on every
reachable final length. -/
theorem deferredDrawRead_run_signed_prefix {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s : DeferredReadState M Commit Chal)
      (z : γ × DeferredReadState M Commit Chal),
      z ∈ support ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s) →
      s.1.1.1.2.length ≤ z.2.1.1.1.2.length := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact le_rfl
  | query_bind t ob ih =>
      intro s z hz
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      refine le_trans ?_ (ih x.1 x.2 z hzx)
      rcases t with (n | mc) | msg
      · have hxs : x ∈ support ((fun u => (u, s)) <$>
            (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hx
        rw [support_map] at hxs
        obtain ⟨u, _, rfl⟩ := hxs; exact le_rfl
      · have hxs : x ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                mc.2 :: s.2))) <$> roStep M s.1.1.1.1 mc) := hx
        rw [support_map] at hxs
        obtain ⟨cu, _, rfl⟩ := hxs; exact le_rfl
      · have hxs : x ∈ support ((fun alc : (Option (Commit × Resp) × List Commit) ×
            (M × Commit →ₒ Chal).QueryCache =>
            (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1) := hx
        rw [support_map] at hxs
        obtain ⟨alc, _, rfl⟩ := hxs; simp

omit [SampleableType Stmt] in
/-- **The drawn-list of the read-recording run grows.** From any start state the recorded drawn
(rejected-commit) list only ever gets longer: uniform and read steps leave it untouched, signing
steps append the body's rejected draws. So the start length is a lower bound on every reachable
final length. -/
theorem deferredDrawRead_run_drawn_prefix {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s : DeferredReadState M Commit Chal)
      (z : γ × DeferredReadState M Commit Chal),
      z ∈ support ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s) →
      s.1.1.2.length ≤ z.2.1.1.2.length := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact le_rfl
  | query_bind t ob ih =>
      intro s z hz
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      refine le_trans ?_ (ih x.1 x.2 z hzx)
      rcases t with (n | mc) | msg
      · have hxs : x ∈ support ((fun u => (u, s)) <$>
            (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hx
        rw [support_map] at hxs
        obtain ⟨u, _, rfl⟩ := hxs; exact le_rfl
      · have hxs : x ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                mc.2 :: s.2))) <$> roStep M s.1.1.1.1 mc) := hx
        rw [support_map] at hxs
        obtain ⟨cu, _, rfl⟩ := hxs; exact le_rfl
      · have hxs : x ∈ support ((fun alc : (Option (Commit × Resp) × List Commit) ×
            (M × Commit →ₒ Chal).QueryCache =>
            (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1) := hx
        rw [support_map] at hxs
        obtain ⟨alc, _, rfl⟩ := hxs; simp

omit [SampleableType Stmt] in
/-- **Read-recording attempt-count mean.** The constructed attempt count
`(drawnlist.length) + (signedlist.length - l.length)` (= #rejects + #signing-queries, the count that
soundly dominates the consumed-attempt positions) of the read-recording run from the empty-draw
start `((((re, l), []), false), [])` has mean at most `qSrem/(1-p)`. Mirrors
`deferredDraw_attemptKn_mean_le`: recover the total combined size by adding back `l.length`, valid
because `l` is a signed-list prefix (`deferredDrawRead_run_signed_prefix`); bound by the run-level
attempt-count fold `deferredDrawRead_run_expected_attemptCount_le`, then cancel `l.length` (run mass
`1`, `deferredDrawRead_run_neverFail`). -/
theorem deferredDrawRead_attemptKn_mean_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (qSrem : ℕ) (hQ : oa.IsQueryBoundP (· matches Sum.inr _) qSrem)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, l), []), false), [])] *
          ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞))
      ≤ (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
  classical
  set run : ProbComp (γ × DeferredReadState M Commit Chal) :=
    (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run ((((re, l), []), false), [])
    with hrun
  have hmass : (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run]) = 1 := by
    rw [hrun]
    exact tsum_probOutput_eq_one'
      (deferredDrawRead_run_neverFail ids M maxAttempts pk sk oa ((((re, l), []), false), []))
  -- Recover the total combined size by adding back `l.length`; the start drawn list is empty.
  have hsplit : (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
        ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)) +
        ((l.length : ℕ) : ℝ≥0∞)
      = ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
          ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞) := by
    rw [show ((l.length : ℕ) : ℝ≥0∞)
          = ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] * ((l.length : ℕ) : ℝ≥0∞) by
        rw [ENNReal.tsum_mul_right, hmass, one_mul]]
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun z => ?_
    rw [← mul_add]
    by_cases hz : z ∈ support run
    · have hpre : l.length ≤ z.2.1.1.1.2.length := by
        have := deferredDrawRead_run_signed_prefix ids M maxAttempts pk sk oa
          ((((re, l), []), false), []) z (by rwa [hrun] at hz)
        simpa using this
      congr 1
      rw [← Nat.cast_add]
      congr 1
      omega
    · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
  -- The total combined size is bounded by `l.length + qSrem/(1-p)`; cancel `l.length`.
  have htot : (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
        ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
      ≤ ((l.length : ℕ) : ℝ≥0∞) + (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
    rw [hrun]
    have := deferredDrawRead_run_expected_attemptCount_le ids M maxAttempts pk sk hp₀ hp hAbort
      oa qSrem hQ ((((re, l), []), false), [])
    simpa using this
  -- Subtract `l.length` from both sides of `hsplit ≤ htot` (it is a finite quantity ≤ both).
  have hle : (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
        ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)) +
        ((l.length : ℕ) : ℝ≥0∞)
      ≤ ((qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort))) + ((l.length : ℕ) : ℝ≥0∞) := by
    rw [hsplit, add_comm ((qSrem : ℝ≥0∞) * _)]; exact htot
  exact ENNReal.le_of_add_le_add_right (by simp) hle

omit [SampleableType Stmt] [SampleableType Chal] [DecidableEq Commit] in
/-- **Splitting an i.i.d. front draw block.** Drawing `n + m` independent commitment draws into a
list is the same computation as drawing the first `n` and then the last `m` and concatenating: the
front block factors into independent sub-blocks. This is the structural identity that, with the
i.i.d. resampling commute, lets the per-query draw blocks accumulate into one front tape. -/
lemma drawList_commit_add (pk : Stmt) (sk : Wit) (n m : ℕ) :
    OracleComp.drawList (ids.commit pk sk) (n + m) =
      OracleComp.drawList (ids.commit pk sk) n >>= fun a =>
        OracleComp.drawList (ids.commit pk sk) m >>= fun b => pure (a ++ b) := by
  classical
  induction n with
  | zero => simp [OracleComp.drawList]
  | succ n ih =>
      rw [Nat.succ_add, OracleComp.drawList, OracleComp.drawList, ih]
      simp only [bind_assoc, pure_bind, List.cons_append]

omit [SampleableType Stmt] [SampleableType Chal] [DecidableEq Commit] in
/-- **Front draw blocks have a deterministic length.** Every list in the support of
`drawList (ids.commit pk sk) n` has length exactly `n`: the block always draws `n` keys. This lets
the `take`/`drop` split of an over-provisioned tape resolve to the per-query block and its
remainder. -/
lemma length_mem_support_drawList_commit (pk : Stmt) (sk : Wit) (n : ℕ)
    (ws : List (Commit × PrvState))
    (hws : ws ∈ support (OracleComp.drawList (ids.commit pk sk) n)) :
    ws.length = n := by
  classical
  induction n generalizing ws with
  | zero =>
      simp only [OracleComp.drawList, support_pure, Set.mem_singleton_iff] at hws
      subst hws; rfl
  | succ n ih =>
      rw [OracleComp.drawList] at hws
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hws
      obtain ⟨w, hw, ws', hws', rfl⟩ := hws
      simp [ih ws' hws']

end scaffold

end EUF_CMA

end FiatShamirWithAbort
