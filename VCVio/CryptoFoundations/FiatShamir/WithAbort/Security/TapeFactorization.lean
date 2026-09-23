/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.FirstMoment

/-!
# EUF-CMA for Fiat-Shamir with aborts: TapeFactorization

The fold-level tape factorization: every interleaved signing query's attempt-draw
block commutes to the front of the opaque adversary fold, so the run distributes as
a pre-drawn tape followed by a tape-consuming run. Also the count invariants of the
deferred draw-and-read run.

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

/-! ### Fold-level tape factorization (reusable front-loading infrastructure)

The body-level half of the tape factorization
(`evalSPMF_ghostSignDrawBody_eq_drawList_tapeSignBody`)
recasts *one* signing body's inline attempt draws as consumption from a pre-drawn tape. The
*fold-level* half — built here — lifts that across the opaque adversary `simulateQ (oa)` fold: every
interleaved signing query's draw block commutes to the very front, so the whole run distributes as

  `drawList (ids.commit pk sk) L >>= fun tape => (simulateQ tapeDrawReadImpl oa).run (s, tape)`,

a single independent front draw block of `L := maxAttempts · #signing-queries` commitments followed
by a tape-*consuming* run. Once the draws are front-loaded, the recorded drawn list is a function of
the tape and the value-free read list is a function of the non-tape randomness, so the read list is
independent of the tape.

The tape-consuming handler `tapeDrawReadImpl` carries a draw tape in its state; a signing query
consumes the first `maxAttempts` tape entries (running `tapeSignBody` on them and dropping them)
instead of drawing inline, while reads/uniform behave exactly as `deferredDrawReadImpl`. The
fold equality is proved by `inductionOn oa`: at a read/uniform step the answer is independent of the
tape so the front draw block commutes trivially; at a signing step the per-body factorization
splices in the body's `drawList maxAttempts` block, which then commutes to the front of the
remaining tape via the i.i.d. resampling commute `evalSPMF_bind_comm_probComp`.

This representation is an alternative to the inline (non-tape) charge that the headline uses; see
`readRecord_expected_pairs_tape_le` and `readRecord_expected_pairs_le`. -/

/-- The tape-consuming read-recording handler. Its state extends `DeferredReadState` with a *draw
tape* `List (Commit × PrvState)`: a signing query consumes the first `maxAttempts` entries of the
tape (running the tape-consuming body `tapeSignBody` on them and dropping them from the tape)
instead of drawing each attempt's commitment inline; uniform and random-oracle-read queries behave
exactly as `deferredDrawReadImpl` and leave the tape untouched. Over-provisioning the tape (length
`maxAttempts · #signing-queries`) makes the front-loaded draw block independent of the value-free
read list. -/
@[expose] noncomputable def tapeDrawReadImpl (pk : Stmt) (sk : Wit) :
    QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT (DeferredReadState M Commit Chal × List (Commit × PrvState)) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n
  | .inl (.inr mc) => StateT.mk fun s =>
      (fun cu => (cu.1, (((((cu.2, s.1.1.1.1.2), s.1.1.1.2), s.1.1.2 || decide (mc.2 ∈ s.1.1.1.2)),
          mc.2 :: s.1.2), s.2))) <$>
        roStep M s.1.1.1.1.1 mc
  | .inr msg => StateT.mk fun s =>
      (fun alc => (alc.1.1, (((((alc.2, msg :: s.1.1.1.1.2), s.1.1.1.2 ++ alc.1.2), s.1.1.2),
          s.1.2), s.2.drop maxAttempts))) <$>
        (tapeSignBody ids M pk sk msg (s.2.take maxAttempts)).run s.1.1.1.1.1

omit [SampleableType Stmt] in
/-- **One-step unfolding of `tapeDrawReadImpl` on a uniform query.** -/
lemma tapeDrawReadImpl_run_unif (pk : Stmt) (sk : Wit) (n : unifSpec.Domain)
    (s : DeferredReadState M Commit Chal × List (Commit × PrvState)) :
    (tapeDrawReadImpl ids M maxAttempts pk sk (.inl (.inl n))).run s =
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl

omit [SampleableType Stmt] in
/-- **One-step unfolding of `tapeDrawReadImpl` on a random-oracle read query.** -/
lemma tapeDrawReadImpl_run_read (pk : Stmt) (sk : Wit) (mc : M × Commit)
    (s : DeferredReadState M Commit Chal × List (Commit × PrvState)) :
    (tapeDrawReadImpl ids M maxAttempts pk sk (.inl (.inr mc))).run s =
      (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
        (cu.1, (((((cu.2, s.1.1.1.1.2), s.1.1.1.2), s.1.1.2 || decide (mc.2 ∈ s.1.1.1.2)),
            mc.2 :: s.1.2), s.2))) <$>
        roStep M s.1.1.1.1.1 mc := rfl

omit [SampleableType Stmt] in
/-- **One-step unfolding of `tapeDrawReadImpl` on a signing query.** The body consumes the first
`maxAttempts` tape entries (via `tapeSignBody`), the drawn list is extended by the recorded rejected
commitments, and the tape advances by `maxAttempts`. -/
lemma tapeDrawReadImpl_run_sign (pk : Stmt) (sk : Wit) (msg : M)
    (s : DeferredReadState M Commit Chal × List (Commit × PrvState)) :
    (tapeDrawReadImpl ids M maxAttempts pk sk (.inr msg)).run s =
      (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
        (alc.1.1, (((((alc.2, msg :: s.1.1.1.1.2), s.1.1.1.2 ++ alc.1.2), s.1.1.2),
            s.1.2), s.2.drop maxAttempts))) <$>
        (tapeSignBody ids M pk sk msg (s.2.take maxAttempts)).run s.1.1.1.1.1 := rfl

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
/-- **Answer-irrelevant cross-step commute (the read/uniform inductive step).** A query step whose
answer and new non-tape state are produced by a tape-*preserving* `ProbComp` `step` (the uniform and
random-oracle-read steps both leave the tape untouched) commutes with the front draw block: pushing
the per-continuation front block to the very front past the answer is the i.i.d. resampling commute
`evalSPMF_bind_comm_probComp`. Given the inductive hypothesis `hcont` (the continuation run factors
as a front block followed by the tape-consuming continuation), the whole step factors likewise. -/
theorem evalSPMF_tapePreserving_step_commute {γ Ans : Type}
    (step : ProbComp (Ans × DeferredReadState M Commit Chal))
    (L : ℕ)
    (defCont : Ans → DeferredReadState M Commit Chal →
      ProbComp (γ × DeferredReadState M Commit Chal))
    (tapeCont : Ans → DeferredReadState M Commit Chal × List (Commit × PrvState) →
      ProbComp (γ × (DeferredReadState M Commit Chal × List (Commit × PrvState))))
    (pk : Stmt) (sk : Wit)
    (hcont : ∀ (a : Ans) (s' : DeferredReadState M Commit Chal),
      𝒮[defCont a s'] =
        𝒮[OracleComp.drawList (ids.commit pk sk) L >>= fun tape =>
            (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$> tapeCont a (s', tape)]) :
    𝒮[step >>= fun p => defCont p.1 p.2] =
      𝒮[OracleComp.drawList (ids.commit pk sk) L >>= fun tape =>
          (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
              (p.1, p.2.1)) <$>
            (((fun p : Ans × DeferredReadState M Commit Chal => (p.1, (p.2, tape))) <$> step)
              >>= fun p => tapeCont p.1 p.2)] :=
  -- A direct instance of the generic answer-irrelevant tape commute: the front draw block is the
  -- `drawList (ids.commit pk sk) L` tape and `proj` discards the spent suffix.
  OracleComp.DeferredSampling.evalSPMF_step_commute_tape step
    (OracleComp.drawList (ids.commit pk sk) L)
    (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) => (p.1, p.2.1))
    defCont tapeCont hcont

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] in
/-- **Tape-combine reconciliation.** A front block drawn in two pieces — `maxAttempts` then
`maxAttempts · q'` — feeding a continuation `g blk rest` is the same computation as drawing the
whole `maxAttempts · (q'+1)` block at once and splitting it with `take`/`drop`: the first
`maxAttempts` entries are the body block, the remainder is the leftover tape. Uses
`drawList_commit_add` to split and the deterministic block length
`length_mem_support_drawList_commit` to resolve `take`/`drop`. -/
theorem drawList_combine_take_drop {δ : Type} (pk : Stmt) (sk : Wit) (q' : ℕ)
    (g : List (Commit × PrvState) → List (Commit × PrvState) → ProbComp δ) :
    𝒮[OracleComp.drawList (ids.commit pk sk) maxAttempts >>= fun blk =>
        OracleComp.drawList (ids.commit pk sk) (maxAttempts * q') >>= fun rest => g blk rest]
      = 𝒮[OracleComp.drawList (ids.commit pk sk) (maxAttempts * (q' + 1)) >>= fun tape =>
          g (tape.take maxAttempts) (tape.drop maxAttempts)] := by
  classical
  rw [show maxAttempts * (q' + 1) = maxAttempts + maxAttempts * q' by ring,
    drawList_commit_add ids pk sk maxAttempts (maxAttempts * q'), bind_assoc]
  -- On the support of the first block, its length is `maxAttempts`, so `take`/`drop` resolve.
  refine evalSPMF_bind_congr (fun blk hblk => ?_)
  have hlen : blk.length = maxAttempts := length_mem_support_drawList_commit ids pk sk _ blk hblk
  rw [bind_assoc]
  refine evalSPMF_bind_congr_left _ _ _ (fun rest => ?_)
  rw [pure_bind, List.take_left' hlen, List.drop_left' hlen]

omit [SampleableType Stmt] in
theorem evalSPMF_defSignStep_splice {δ : Type} (pk : Stmt) (sk : Wit) (msg : M)
    (s : DeferredReadState M Commit Chal)
    (k : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache →
      ProbComp δ) :
    𝒮[(ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1 >>= k] =
      𝒮[OracleComp.drawList (ids.commit pk sk) maxAttempts >>= fun blk =>
          (tapeSignBody ids M pk sk msg blk).run s.1.1.1.1 >>= k] := by
  rw [show (OracleComp.drawList (ids.commit pk sk) maxAttempts >>= fun blk =>
        (tapeSignBody ids M pk sk msg blk).run s.1.1.1.1 >>= k)
      = (OracleComp.drawList (ids.commit pk sk) maxAttempts >>= fun blk =>
          (tapeSignBody ids M pk sk msg blk).run s.1.1.1.1) >>= k from by rw [bind_assoc]]
  rw [evalSPMF_bind,
    evalSPMF_ghostSignDrawBody_eq_drawList_tapeSignBody ids M pk sk msg maxAttempts s.1.1.1.1,
    ← evalSPMF_bind]

omit [SampleableType Stmt] in
/-- **Sign-step cross-step commute (the crux inductive step).** The deferred-draw sign step,
composed with the deferred continuation, factors as a single front draw block of
`maxAttempts·(q'+1)` commitments followed by the tape-consuming sign step + tape continuation. The
genuine framework content: the body's `maxAttempts` draw block splices to the front via the per-body
factorization (`evalSPMF_defSignStep_splice`); the continuation's `maxAttempts·q'` block (supplied
by the inductive hypothesis `hcont`) commutes past the body via the i.i.d. resampling commute
(`evalSPMF_bind_comm_probComp`); the two blocks combine into one `maxAttempts·(q'+1)` block split by
`take`/`drop` (`drawList_combine_take_drop`), exactly the tape the tape-consuming sign step
consumes. -/
theorem evalSPMF_signStep_commute {γ : Type} (pk : Stmt) (sk : Wit) (msg : M)
    (s : DeferredReadState M Commit Chal) (q' : ℕ)
    (ob : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
        (Sum.inr msg) →
      OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (hcont : ∀ (a : ((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg))
        (s' : DeferredReadState M Commit Chal),
      𝒮[(simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob a)).run s'] =
        𝒮[OracleComp.drawList (ids.commit pk sk) (maxAttempts * q') >>= fun tape =>
            (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob a)).run (s', tape)]) :
    𝒮[(deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s >>= fun p =>
        (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2] =
      𝒮[OracleComp.drawList (ids.commit pk sk) (maxAttempts * (q' + 1)) >>= fun tape =>
          (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
              (p.1, p.2.1)) <$>
            ((tapeDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run (s, tape) >>= fun p =>
              (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2)] := by
  classical
  -- LHS: fold the deferred sign step's map into the body bind, then splice the front block.
  rw [show (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s >>= (fun p =>
        (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2)
      = (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1 >>= fun alc =>
          (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
            (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)
      from by
        rw [show (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s
              = (fun alc : (Option (Commit × Resp) × List Commit) ×
                  (M × Commit →ₒ Chal).QueryCache =>
                  (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
                (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1 from rfl]
        simp [bind_map_left]]
  rw [evalSPMF_defSignStep_splice ids M maxAttempts pk sk msg s
    (fun alc => (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
      (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))]
  -- Rewrite the continuation by `hcont`, under the leading `drawList maxAttempts` and body binds.
  rw [evalSPMF_bind_congr (mx := OracleComp.drawList (ids.commit pk sk) maxAttempts)
    (fun blk _ => evalSPMF_bind_congr (mx := (tapeSignBody ids M pk sk msg blk).run s.1.1.1.1)
      (fun alc _ => hcont alc.1.1 ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)))]
  -- Commute the continuation's `maxAttempts·q'` block to the front past the body.
  rw [evalSPMF_bind_congr (mx := OracleComp.drawList (ids.commit pk sk) maxAttempts)
    (fun blk _ => evalSPMF_bind_comm_probComp ((tapeSignBody ids M pk sk msg blk).run s.1.1.1.1)
      (OracleComp.drawList (ids.commit pk sk) (maxAttempts * q'))
      (fun alc tape => (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
          (p.1, p.2.1)) <$>
        (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk)
          (ob alc.1.1)).run
            (((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2), tape)))]
  -- Combine the two front blocks into one `maxAttempts·(q'+1)` block split by `take`/`drop`.
  rw [drawList_combine_take_drop ids maxAttempts pk sk q'
    (fun blk rest => (tapeSignBody ids M pk sk msg blk).run s.1.1.1.1 >>= fun alc =>
      (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
          (p.1, p.2.1)) <$>
        (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk)
          (ob alc.1.1)).run
            (((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2), rest))]
  -- Match the RHS: the tape sign step consumes `take maxAttempts` and threads `drop maxAttempts`.
  refine evalSPMF_bind_congr_left _ _ _ (fun tape => ?_)
  rw [show (tapeDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run (s, tape)
        = (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
            (alc.1.1, (((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2),
              tape.drop maxAttempts))) <$>
          (tapeSignBody ids M pk sk msg (tape.take maxAttempts)).run s.1.1.1.1 from rfl]
  simp [bind_map_left, map_bind]

omit [SampleableType Stmt] in
/-- **The fold-level tape factorization (the framework lemma).** By induction on the adversary
computation `oa`, the read-recording deferred-draw run distributes as a single front draw block of
`maxAttempts · qSrem` commitments followed by a tape-consuming run:

`𝒮[(simulateQ deferredDrawReadImpl oa).run s]`
`  = 𝒮[drawList (ids.commit pk sk) (maxAttempts · qSrem) >>= fun tape =>`
`        (simulateQ tapeDrawReadImpl oa).run (s, tape)]`,

where `qSrem` bounds the number of signing queries of `oa` (the `(· matches .inr _)` component of
`signHashQueryBound`). The tape is over-provisioned (length `maxAttempts · qSrem`); each signing
query consumes its `maxAttempts`-prefix and the unused suffix is discarded on early accept.

The proof inducts on `oa`. At a **read/uniform** step the query answer is independent of the tape,
so the front draw block commutes past it (the i.i.d. resampling commute
`evalSPMF_bind_comm_probComp`),
matching the inductive hypothesis for the continuation. At a **signing** step the per-body
factorization `evalSPMF_ghostSignDrawBody_eq_drawList_tapeSignBody` recasts the body's inline draws
as a `drawList maxAttempts` block; that block is split off the front via `drawList_commit_add` (the
remaining `maxAttempts · (qSrem-1)` block feeding the continuation by the inductive hypothesis) and
commuted to the front past the answer-irrelevant continuation. The general principle it instantiates
is that answer-irrelevant per-step draws factor to a front tape in `simulateQ`. -/
theorem evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (qSrem : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) qSrem →
      ∀ (s : DeferredReadState M Commit Chal),
        𝒮[(simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] =
          𝒮[OracleComp.drawList (ids.commit pk sk) (maxAttempts * qSrem) >>= fun tape =>
              (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                  (p.1, p.2.1)) <$>
                (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) oa).run (s, tape)] := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qSrem _ s
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rw [evalSPMF_bind_const_neverFails _ (OracleComp.probFailure_drawList _ _)]
  | query_bind t ob ih =>
      intro qSrem hQ s
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rcases t with (n | mc) | msg
      · -- UNIFORM: the answer is independent of the tape; commute the front block past the draw.
        have hqs : (if (match (Sum.inl (Sum.inl n) :
              ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind]
        rw [show (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inl n))).run s
              = (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n
            from rfl]
        -- The tape uniform step is the deferred step with the tape inserted (`Functor.map_map`).
        rw [show (fun tape => (fun p :
                γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              ((tapeDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inl n))).run (s, tape)
                >>= fun p =>
                  (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2))
            = (fun tape => (fun p :
                γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              (((fun p : (((unifSpec + (M × Commit →ₒ Chal)) +
                  (M →ₒ Option (Commit × Resp))).Range (Sum.inl (Sum.inl n))) ×
                    DeferredReadState M Commit Chal => (p.1, (p.2, tape))) <$>
                  ((fun u => (u, s)) <$>
                    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n))
                >>= fun p =>
                  (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2))
            from by funext tape; rw [tapeDrawReadImpl_run_unif, Functor.map_map]; rfl]
        exact evalSPMF_tapePreserving_step_commute ids M
          ((fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n)
          (maxAttempts * qSrem)
          (fun a s' => (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob a)).run s')
          (fun a st => (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob a)).run st)
          pk sk (fun a s' => ih a qSrem (hQ2 a) s')
      · -- READ: the answer is `roStep` (real layer), independent of the tape; same commute.
        have hqs : (if (match (Sum.inl (Sum.inr mc) :
              ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind]
        rw [show (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inr mc))).run s
              = (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
                  (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                    mc.2 :: s.2))) <$> roStep M s.1.1.1.1 mc
            from rfl]
        rw [show (fun tape => (fun p :
                γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              ((tapeDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inr mc))).run (s, tape)
                >>= fun p =>
                  (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2))
            = (fun tape => (fun p :
                γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              (((fun p : Chal × DeferredReadState M Commit Chal => (p.1, (p.2, tape))) <$>
                  ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
                    (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                      mc.2 :: s.2))) <$> roStep M s.1.1.1.1 mc))
                >>= fun p =>
                  (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2))
            from by funext tape; rw [tapeDrawReadImpl_run_read, Functor.map_map]; rfl]
        exact evalSPMF_tapePreserving_step_commute ids M
          ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                mc.2 :: s.2))) <$> roStep M s.1.1.1.1 mc)
          (maxAttempts * qSrem)
          (fun a s' => (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob a)).run s')
          (fun a st => (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob a)).run st)
          pk sk (fun a s' => ih a qSrem (hQ2 a) s')
      · -- SIGN: the crux. Splice the per-body draw block to the front past the continuation.
        have hpos : 0 < qSrem := by
          rcases hQ1 with h | h
          · exact absurd rfl h
          · exact h
        clear hQ1
        have hqs : (if (match (Sum.inr msg :
              ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem - 1 := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind]
        rw [show qSrem = (qSrem - 1) + 1 from by omega]
        exact evalSPMF_signStep_commute ids M maxAttempts pk sk msg s (qSrem - 1) ob
          (fun a s' => ih a (qSrem - 1) (hQ2 a) s')

omit [SampleableType Stmt] in
/-- **The atomic value-free charge (the irreducible probabilistic kernel).** One fresh raw
commitment draw `w ← ids.commit pk sk`, *independent of* a value-free list `rl`, contributes
expected multiplicity `E[rl.count w.1] ≤ ε · rl.length`: each of the `rl.length` slots of `rl` is
hit by the fresh draw with probability `Pr[= slot | Prod.fst <$> ids.commit pk sk] ≤ ε` (`hGuess`).

This is the single source of the `ε` in the ghost-read bound. It is purely the per-draw mass bound
combined with the independence of the draw from the (value-free) read list; the structural content
of the full charge is to exhibit each recorded rejected draw of the tape run in exactly this
independent-of-the-readlist position (the value-substitution at rejected tape positions). -/
lemma tsum_probOutput_commit_mul_count_le {C P : Type} [DecidableEq C]
    (commit : ProbComp (C × P)) (rl : List C) (ε : ℝ)
    (hGuess : ∀ cm : C, Pr[= cm | Prod.fst <$> commit] ≤ ENNReal.ofReal ε) :
    (∑' w : C × P, Pr[= w | commit] * (rl.count w.1 : ℝ≥0∞))
      ≤ ENNReal.ofReal ε * (rl.length : ℝ≥0∞) :=
  OracleComp.DeferredSampling.tsum_probOutput_fresh_mul_count_le commit rl ε hGuess

omit [SampleableType Stmt] in
/-- **Value-substitution: the recorded read list is independent of the drawn-list content.** The
expected multiplicity `E[readlist.count w]` of any fixed commitment `w` in the recorded read list of
the read-recording run depends only on the start *real cache*, *signed list*, and *read list* — not
on the start *drawn list* `D` nor the start *bad flag* `b`. This is the structural value-freeness at
the heart of the ghost-read bound: the recorded reads answer via `roStep` on the real layer and
never the drawn (rejected) values, so changing the drawn list (or the bad flag, which is write-only
and never gates control flow) leaves the read-list marginal unchanged.

Formally the expectation is invariant under both drawn-list and bad-flag start values. Proved by
induction on `oa`:
* **pure** — the read list is the start one (independent of `D`, `b`).
* **uniform** — the draw is forwarded and the drawn list / bad flag / read list are untouched; the
  inductive hypothesis applies to the unchanged-`D` continuation.
* **read** — the read list grows by exactly `mc.2` (the same regardless of `D`); the bad flag
  updates to `b || (mc.2 ∈ D)` (which *does* depend on `D`), but since the inductive hypothesis is
  quantified over *all* bad-flag values, the two `D`-runs still agree.
* **sign** — the body draws are the same regardless of `D`, `b`; the drawn list grows by the body's
  rejected commitments and the bad flag is preserved, and the inductive hypothesis (quantified over
  all `D`) closes the differing-drawn-list continuations. -/
theorem deferredDrawRead_run_count_dl_invariant {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (w : Commit) (re : (M × Commit →ₒ Chal).QueryCache) (sgn : List M)
    (rl : List Commit) :
    ∀ (D₁ : List Commit) (b₁ : Bool) (D₂ : List Commit) (b₂ : Bool),
      (∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
              ((((re, sgn), D₁), b₁), rl)] * (z.2.2.count w : ℝ≥0∞))
        = ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
                ((((re, sgn), D₂), b₂), rl)] * (z.2.2.count w : ℝ≥0∞) := by
  induction oa using OracleComp.inductionOn generalizing re sgn rl with
  | pure a =>
      intro D₁ b₁ D₂ b₂
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
  | query_bind t ob ih =>
      intro D₁ b₁ D₂ b₂
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, tsum_probOutput_bind_mul]
      rcases t with (n | mc) | msg
      · -- UNIFORM: drawn list / bad flag / read list untouched; forward draw.
        set G : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
            (Sum.inl (Sum.inl n))) × DeferredReadState M Commit Chal → ℝ≥0∞ :=
          fun x => ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              (z.2.2.count w : ℝ≥0∞) with hG
        have hx₁ : ((deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inl n))).run
              ((((re, sgn), D₁), b₁), rl)) =
            (fun u => (u, ((((re, sgn), D₁), b₁), rl))) <$>
              (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl
        have hx₂ : ((deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inl n))).run
              ((((re, sgn), D₂), b₂), rl)) =
            (fun u => (u, ((((re, sgn), D₂), b₂), rl))) <$>
              (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl
        rw [hx₁, hx₂]
        refine (tsum_probOutput_map_mul _ _ G).trans
          ((tsum_congr fun u => ?_).trans (tsum_probOutput_map_mul _ _ G).symm)
        exact congrArg _ (ih u re sgn rl D₁ b₁ D₂ b₂)
      · -- READ: read list grows by `mc.2` (independent of `D`); the bad flag updates to
        -- `b || (mc.2 ∈ D)` (D-dependent), but `ih` is quantified over *all* bad flags.
        set G : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
            (Sum.inl (Sum.inr mc))) × DeferredReadState M Commit Chal → ℝ≥0∞ :=
          fun x => ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              (z.2.2.count w : ℝ≥0∞) with hG
        have hx₁ : ((deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inr mc))).run
              ((((re, sgn), D₁), b₁), rl)) =
            (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, ((((cu.2, sgn), D₁), b₁ || decide (mc.2 ∈ D₁)), mc.2 :: rl))) <$>
              roStep M re mc := rfl
        have hx₂ : ((deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inr mc))).run
              ((((re, sgn), D₂), b₂), rl)) =
            (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, ((((cu.2, sgn), D₂), b₂ || decide (mc.2 ∈ D₂)), mc.2 :: rl))) <$>
              roStep M re mc := rfl
        rw [hx₁, hx₂]
        refine (tsum_probOutput_map_mul _ _ G).trans
          ((tsum_congr fun cu => ?_).trans (tsum_probOutput_map_mul _ _ G).symm)
        exact congrArg _
          (ih cu.1 cu.2 sgn (mc.2 :: rl) D₁ (b₁ || decide (mc.2 ∈ D₁)) D₂
            (b₂ || decide (mc.2 ∈ D₂)))
      · -- SIGN: the body draws are `D`-independent; drawn list grows by the body's rejected
        -- commitments and the bad flag is preserved; `ih` (over all `D`) closes the continuations.
        set G : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
            (Sum.inr msg)) × DeferredReadState M Commit Chal → ℝ≥0∞ :=
          fun x => ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              (z.2.2.count w : ℝ≥0∞) with hG
        have hx₁ : ((deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run
              ((((re, sgn), D₁), b₁), rl)) =
            (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
              (alc.1.1, ((((alc.2, msg :: sgn), D₁ ++ alc.1.2), b₁), rl))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run re := rfl
        have hx₂ : ((deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run
              ((((re, sgn), D₂), b₂), rl)) =
            (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
              (alc.1.1, ((((alc.2, msg :: sgn), D₂ ++ alc.1.2), b₂), rl))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run re := rfl
        rw [hx₁, hx₂]
        refine (tsum_probOutput_map_mul _ _ G).trans
          ((tsum_congr fun alc => ?_).trans (tsum_probOutput_map_mul _ _ G).symm)
        exact congrArg _
          (ih alc.1.1 alc.2 (msg :: sgn) rl (D₁ ++ alc.1.2) b₁ (D₂ ++ alc.1.2) b₂)

omit [SampleableType Stmt] in
/-- **The value-substituted continuation read-multiplicity functional is drawn-invariant.** A
restatement of `deferredDrawRead_run_count_dl_invariant` reorganised for the body charge: the
expected read-multiplicity `E[Σ_{rc ∈ readlist} R.count rc]` of a *fixed* commit list `R` against
the continuation's recorded read list is invariant under the continuation's start drawn list (and
bad flag). The reads answer via `roStep` on the real layer, never the drawn (rejected) values, so
adding `R` (or any list) to the start drawn list does not change the read-list marginal. -/
theorem deferredDrawRead_run_sum_count_dl_invariant {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (R : List Commit) (re : (M × Commit →ₒ Chal).QueryCache) (sgn : List M)
    (rl : List Commit) (D₁ : List Commit) (b₁ : Bool) (D₂ : List Commit) (b₂ : Bool) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, sgn), D₁), b₁), rl)] * ((R.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
      = ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
              ((((re, sgn), D₂), b₂), rl)] * ((R.map (fun w => z.2.2.count w)).sum : ℝ≥0∞) := by
  classical
  induction R with
  | nil => simp
  | cons w R ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      rw [show ∀ (D : List Commit) (b : Bool),
            (∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
                  ((((re, sgn), D), b), rl)] *
                (((z.2.2.count w : ℕ) : ℝ≥0∞) + ((R.map (fun w => z.2.2.count w)).sum : ℝ≥0∞)))
              = (∑' z : γ × DeferredReadState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
                      ((((re, sgn), D), b), rl)] * ((z.2.2.count w : ℕ) : ℝ≥0∞))
                + ∑' z : γ × DeferredReadState M Commit Chal,
                    Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
                        ((((re, sgn), D), b), rl)] *
                      ((R.map (fun w => z.2.2.count w)).sum : ℝ≥0∞) from
          fun D b => by rw [← ENNReal.tsum_add]; exact tsum_congr fun z => by rw [mul_add]]
      rw [deferredDrawRead_run_count_dl_invariant ids M maxAttempts pk sk oa w re sgn rl
            D₁ b₁ D₂ b₂, ih, ← ENNReal.tsum_add]
      exact tsum_congr fun z => by rw [mul_add]

end scaffold

end EUF_CMA

end FiatShamirWithAbort
