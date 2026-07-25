/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.BodyHops

/-!
# EUF-CMA for Fiat-Shamir with aborts: CouplingEngine

The deferred-draw layer of the ghost-read bound: the identical-until-bad reduction
from the eager ghost handler to the ghost-blind handler
(`probEvent_ghostHybridImpl_bad_le_ghostBlind`), the deferred-draw handler
`deferredDrawImpl` with its draw-collecting signing body `ghostSignDrawBody`, the
pointwise coupling of the two runs (`ghostBlind_bad_le_deferredDraw`), and the
per-body half of the tape factorization
(`evalDist_ghostSignDrawBody_eq_drawList_tapeSignBody`, recasting one signing body's
inline attempt draws as consumption from a pre-drawn tape `tapeSignBody`).

Part of the CMA-to-NMA security development for the Fiat-Shamir-with-aborts
transform; `VCVio.CryptoFoundations.FiatShamir.WithAbort.Security` re-exports
all of its modules and holds the overview docstring.
-/

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
variable (adv : SignatureAlg.unforgeableAdv
  (FiatShamirWithAbort
    (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) ids hr M maxAttempts))

omit [SampleableType Stmt] in
/-- **The identical-until-bad / ghost-blind reduction.** The eager hybrid handler
`ghostHybridImpl … true` and the ghost-blind handler `ghostBlindImpl` flip the adversarial-read
bad flag with *exactly the same*
probability at the empty-cache Dirac start:

`Pr[bad | (simulateQ (ghostHybridImpl … true) (adv.main pk)).run δ_∅]`
`  = Pr[bad | (simulateQ ghostBlindImpl (adv.main pk)).run δ_∅]`.

The two handlers are *identical until bad*: they coincide on uniform queries, on signing
queries, and on ghost-*miss* reads (all run the same `roStep` / `ghostSignBody`), and on a
ghost-*hit* read both flip the bad flag (`ghostBlindImpl_agree_good`), while neither ever
unsets it (`ghostHybridImpl_bad_mono` / `ghostBlindImpl_bad_mono`). The blind handler answers
a hit from the real layer instead of returning the ghost value, so the ghost-key values never
influence the run — they are consulted only to record the would-hit. Because the runs differ
only on the already-bad trajectory (where both flags read `true`), the bad marginals coincide,
by the exact identical-until-bad bad-event equality `probEvent_output_bad_eq'`. -/
lemma probEvent_ghostHybridImpl_bad_eq_ghostBlind (pk : Stmt) (sk : Wit) :
    Pr[ fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      = Pr[ fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)] :=
  OracleComp.ProgramLogic.Relational.probEvent_output_bad_eq'
    (ghostHybridImpl ids M maxAttempts true pk sk)
    (ghostBlindImpl ids M maxAttempts pk sk)
    (ghostBlindImpl_agree_good ids M maxAttempts pk sk)
    (ghostHybridImpl_bad_mono ids M maxAttempts true pk sk)
    (ghostBlindImpl_bad_mono ids M maxAttempts pk sk)
    (adv.main pk) (((∅, ∅), []) : _)

omit [SampleableType Stmt] in
/-- **The ghost-blind reduction, `≤` form.** The eager ghost-read bad mass is bounded by the
ghost-blind handler's bad mass at the empty-cache Dirac start; immediate from the equality
`probEvent_ghostHybridImpl_bad_eq_ghostBlind`. This is the first step of the ghost-read bound,
chained with the value-freeness of the reads and the deferred-draw coincidence charge. -/
lemma probEvent_ghostHybridImpl_bad_le_ghostBlind (pk : Stmt) (sk : Wit) :
    Pr[ fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      ≤ Pr[ fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)] :=
  (probEvent_ghostHybridImpl_bad_eq_ghostBlind ids hr M maxAttempts adv pk sk).le

/-! ### The deferred-sampling factorization

The ghost-blind run's adversarial-read bad marginal factors as a *value-free deferred-draw game*,
and that factorization is what the ghost-read bound is charged through: the headline goes via the
σ-free first-moment quantity `readRecord_expected_coincidences_le`, the expected number of
coincidences between the value-free recorded read-commit list and the recorded rejected draws.

Why it factors. In `ghostBlindImpl` an adversarial random-oracle read at a ghost-cache hit answers
from the *real* layer via `roStep` — identically to a miss — and only *records* the would-hit by
flipping the bad flag (`ghostBlindImpl_eq_ghostHybridImpl_false`, `ghostBlindImpl_agree_good`). The
ghost-cache *values* are therefore write-only side-data: they never influence the run's outputs or
its continuation. Consequently the run's joint law of (adversary read points, reject pattern / loop
lengths, real cache) is produced by a value-free run that is independent of the stored commitment
values; those values are drawn `~ Prod.fst <$> ids.commit` per *rejected* attempt and gated into the
ghost cache by the reject decision.

The factorization is realized by pulling every rejected attempt's commitment draw into the recorded
drawn list of the deferred handler `deferredDrawImpl` (and its read-recording refinement
`deferredDrawReadImpl`), independent of the value-free recorded read-commit list. The expected
coincidence count is then bounded by `(#reads) · (#draws) · (max draw mass) ≤ (qH+1) · ε ·
E[#attempts]`, with `E[#attempts] ≤ qS/(1-p)` the aggregate of `tsum_probOutput_commit_mul_abort_le`
over the `qS` signing queries (each attempt is reached with geometric probability, summed by
`geomAttemptSum_le`). Lifting the value-freeness through the `simulateQ` fold — so that the
per-rejected-attempt draws commute to the front of the whole run — is carried out by the tape
factorization `evalDist_deferredDrawRead_eq_drawList_tapeDrawRead`, whose per-body half
(`evalDist_ghostSignDrawBody_eq_drawList_tapeSignBody`) is proved in this module. -/

/-! ### Deferred-handler ingredients

The first-moment route couples the eager ghost-blind run to a *deferred* handler (a genuine
`QueryImpl`) via a per-step coupling relation on the two run distributions and their two bad
predicates. This block constructs those ingredients.

The deferred handler `deferredDrawImpl` carries, instead of eager-committed ghost keys, the
*accumulated list of drawn rejected-attempt commitments* (the front block, grown lazily as sign
steps draw) together with the real cache, the signed list, and the "some recorded read hit a drawn
commitment" flag. Its state is

  `DeferredState M Commit Chal :=
    (((M × Commit →ₒ Chal).QueryCache × List M) × List Commit) × Bool`.

Branch behaviour, designed so that the *observable* component (output, real cache, signed list)
coincides value-free with the ghost-blind handler:
* a **uniform** query forwards exactly as `ghostBlindImpl` does, touching neither the drawn list nor
  the bad flag;
* a **random-oracle read** answers from the real layer via `roStep` (identical read point and answer
  to `ghostBlindImpl`'s value-free hit/miss branches) and sets the bad flag iff the read point's
  commitment `mc.2` is among the accumulated drawn list — the deferred counterpart of the eager
  membership test against the ghost domain;
* a **signing** query runs the value-free signing body (`run_ghostSignBody_fst` recovers
  `transSignBody`, the accepted-only loop) for the output and real cache, and appends to the drawn
  list one i.i.d. raw `Prod.fst <$> ids.commit pk sk` draw per rejected attempt, mirroring the eager
  ghost writes. -/

/-- State of the deferred-draw handler: real cache, signed-message list, the accumulated list of
drawn rejected-attempt commitments (the deferral front block), and the monotone "some recorded read
hit a drawn commitment" flag. The drawn list replaces the eager ghost cache: where `ghostBlindImpl`
commits sampled keys into its ghost layer, `deferredDrawImpl` only records the *list* of drawn
commitments, which is later read off as the front `drawList` block. -/
abbrev DeferredState (M Commit Chal : Type) : Type :=
  (((M × Commit →ₒ Chal).QueryCache × List M) × List Commit) × Bool

/-- Draw-collecting signing body: mirrors `ghostSignBody` but threads only the *real* cache and
accumulates the list of drawn *rejected*-attempt commitments instead of writing them to a ghost
layer. Returns `(output, drawn commits this query)`. Only the rejected-attempt commitments are
recorded, in attempt order; the accepted attempt (whose commitment is returned to the caller and
cached in the real layer) records nothing, exactly mirroring `ghostSignBody`, whose ghost layer
holds the rejected commitments and `uncacheQuery`-s the accepted one. Forgetting the drawn list
recovers `transSignBody` (the value-free output and real cache), and the drawn list is exactly the
list of i.i.d. raw `Prod.fst <$> ids.commit pk sk` samples taken on the *rejected* attempts — the
value-free side-data that never feeds back into the run's outputs. -/
noncomputable def ghostSignDrawBody (pk : Stmt) (sk : Wit) (msg : M) :
    ℕ → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
      (Option (Commit × Resp) × List Commit)
  | 0 => pure (none, [])
  | n + 1 => do
    let (w, st) ← liftM (ids.commit pk sk)
    let c ← (liftM (uniformSample Chal) :
      StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp Chal)
    let oz ← liftM (ids.respond pk sk st c)
    match oz with
    | some z =>
        modify fun cache => cache.cacheQuery (msg, w) c
        pure (some (w, z), [])
    | none =>
        let (res, ws) ← ghostSignDrawBody pk sk msg n
        pure (res, w :: ws)

omit [SampleableType Stmt] in
/-- One-step unfolding of the draw-collecting signing body. The body draws a commitment `w`,
samples a challenge `ch`, responds, and on accept records *no* drawn commitment (the accepted
commit is returned, not deferred) while on reject prepends `w` to the recursively collected list
of rejected commitments. -/
lemma run_ghostSignDrawBody_succ (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ)
    (re : (M × Commit →ₒ Chal).QueryCache) :
    (ghostSignDrawBody ids M pk sk msg (n + 1)).run re =
      ids.commit pk sk >>= fun ws =>
        uniformSample Chal >>= fun ch =>
          ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
            | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                (ghostSignDrawBody ids M pk sk msg n).run re := by
  simp only [ghostSignDrawBody, bind_assoc, StateT.run_bind, OracleComp.liftM_run_StateT,
    pure_bind]
  refine congrArg (ids.commit pk sk >>= ·) (funext fun ws => ?_)
  obtain ⟨w, st⟩ := ws
  refine congrArg (uniformSample Chal >>= ·) (funext fun ch => ?_)
  refine congrArg (ids.respond pk sk st ch >>= ·) (funext fun oz => ?_)
  cases oz with
  | some z => simp [StateT.run_modify]
  | none => simp [StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp]

/-! ### Body-level tape resampling (the per-body half of the tape factorization)

The draw-collecting signing body `ghostSignDrawBody` draws each attempt's commitment *inline*. The
genuine fold-lift content of the ghost-read bound is to front-load every interleaved per-attempt
draw into one independent block, so the drawn *values* factor away from the value-free adversarial
read points. The body-level half of that program — recasting one signing body's inline draws as
consumption from a *pre-drawn* tape — is proved here as a distributional equality
`evalDist_ghostSignDrawBody_eq_drawList_tapeSignBody`:

`𝒟[(ghostSignDrawBody … n).run re] = 𝒟[drawList (ids.commit pk sk) n >>= tapeSignBody … tape]`.

Pre-drawing the `n`-block of full `(Commit × PrvState)` commitment draws and consuming them
head-first (`tapeSignBody`) is distributionally identical to drawing them inline: the control flow
(accept/reject, via the inline `uniformSample`/`respond`) reads the *same* tape values, and the
unused suffix on an early accept is discarded. The proof is a structural induction on `n` that, at
each attempt, commutes the recursive front block `drawList n` past the inline
`uniformSample`/`respond` draws (`evalDist_bind_comm_probComp`, the i.i.d. resampling step) and
matches the reject-branch recursion to the inductive hypothesis.

This is the local, tractable `bind`-commutation; the remaining open content of
`readRecord_expected_pairs_le` is to lift it across the *opaque adversary* `simulateQ (oa)` fold:
the interleaved per-query draw blocks all commuting to the front, past the adaptive read points. -/

/-- **i.i.d. bind-commutation at the distribution level for `ProbComp`.** Two independent draws
`oa`, `ob` feeding a common continuation `k` may be drawn in either order without changing the
output distribution. The `OracleComp` monad is *not* commutative as a free monad (its `bind` is
syntactic), but its `evalDist` image into `SPMF` is: the two iterated sums over the independent
draws exchange by `ENNReal.tsum_comm`. This is the local resampling step that front-loads an
output-irrelevant draw past its continuation. -/
theorem evalDist_bind_comm_probComp {α β γ : Type} (oa : ProbComp α) (ob : ProbComp β)
    (k : α → β → ProbComp γ) :
    𝒟[oa >>= fun a => ob >>= fun b => k a b] = 𝒟[ob >>= fun b => oa >>= fun a => k a b] := by
  refine SPMF.ext fun x => ?_
  rw [show 𝒟[oa >>= fun a => ob >>= fun b => k a b] x
        = Pr[= x | oa >>= fun a => ob >>= fun b => k a b] from (probOutput_def _ _).symm,
    show 𝒟[ob >>= fun b => oa >>= fun a => k a b] x
        = Pr[= x | ob >>= fun b => oa >>= fun a => k a b] from (probOutput_def _ _).symm]
  rw [probOutput_bind_eq_tsum]
  rw [show (∑' a : α, Pr[= a | oa] * Pr[= x | ob >>= fun b => k a b])
      = ∑' (a : α) (b : β), Pr[= a | oa] * (Pr[= b | ob] * Pr[= x | k a b]) from
    tsum_congr fun a => by rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_left]]
  rw [probOutput_bind_eq_tsum]
  rw [show (∑' b : β, Pr[= b | ob] * Pr[= x | oa >>= fun a => k a b])
      = ∑' (b : β) (a : α), Pr[= b | ob] * (Pr[= a | oa] * Pr[= x | k a b]) from
    tsum_congr fun b => by rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_left]]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun a => tsum_congr fun b => by ring

/-- **Dropping a never-failing prefix at the distribution level.** A leading draw `od` whose
continuation ignores its value contributes only its total mass; when `od` never fails (mass `1`,
e.g. a `drawList` front block) it can be discarded from the output distribution. -/
theorem evalDist_bind_const_neverFails {α γ : Type} (od : ProbComp α) (hmass : Pr[⊥ | od] = 0)
    (k : ProbComp γ) : 𝒟[od >>= fun _ => k] = 𝒟[k] := by
  refine SPMF.ext fun x => ?_
  rw [show 𝒟[od >>= fun _ => k] x = Pr[= x | od >>= fun _ => k] from (probOutput_def _ _).symm,
    show 𝒟[k] x = Pr[= x | k] from (probOutput_def _ _).symm]
  rw [probOutput_bind_const, hmass]; simp

/-- **Distribution-level congruence under a leading bind.** If two continuations agree as
distributions pointwise then the bound computations agree as distributions. -/
theorem evalDist_bind_congr_left {α β : Type} (oa : ProbComp α) (f g : α → ProbComp β)
    (h : ∀ a, 𝒟[f a] = 𝒟[g a]) : 𝒟[oa >>= f] = 𝒟[oa >>= g] := by
  rw [evalDist_bind, evalDist_bind]; exact congrArg _ (funext h)

/-- **Tape-consuming signing body.** Identical to `ghostSignDrawBody` except that each attempt's
commitment draw `(Commit × PrvState)` is *consumed* from a pre-drawn tape (head-first) instead of
drawn inline. The challenge sampling and response stay inline. On accept the remaining tape suffix
is discarded; an empty tape ends the loop (mirroring budget exhaustion). The recorded
rejected-commit list is built exactly as in `ghostSignDrawBody`. -/
noncomputable def tapeSignBody (pk : Stmt) (sk : Wit) (msg : M) :
    List (Commit × PrvState) → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
      (Option (Commit × Resp) × List Commit)
  | [] => pure (none, [])
  | (w, st) :: rest => do
    let c ← (liftM (uniformSample Chal) :
      StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp Chal)
    let oz ← liftM (ids.respond pk sk st c)
    match oz with
    | some z =>
        modify fun cache => cache.cacheQuery (msg, w) c
        pure (some (w, z), [])
    | none =>
        let (res, ws) ← tapeSignBody pk sk msg rest
        pure (res, w :: ws)

omit [SampleableType Stmt] in
/-- One-step unfolding of the tape-consuming signing body on a non-empty tape, mirroring
`run_ghostSignDrawBody_succ`: the head `(w, st)` is consumed, a challenge sampled and a response
computed; on accept the body records no commitment, on reject it prepends `w` to the recursively
collected list and continues on the tape tail. -/
lemma run_tapeSignBody_cons (pk : Stmt) (sk : Wit) (msg : M) (w : Commit) (st : PrvState)
    (rest : List (Commit × PrvState)) (re : (M × Commit →ₒ Chal).QueryCache) :
    (tapeSignBody ids M pk sk msg ((w, st) :: rest)).run re =
      uniformSample Chal >>= fun ch =>
        ids.respond pk sk st ch >>= fun oz =>
          match oz with
          | some z => pure ((some (w, z), []), re.cacheQuery (msg, w) ch)
          | none => (fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
              (tapeSignBody ids M pk sk msg rest).run re := by
  simp only [tapeSignBody, bind_assoc, StateT.run_bind, OracleComp.liftM_run_StateT, pure_bind]
  refine congrArg (uniformSample Chal >>= ·) (funext fun ch => ?_)
  refine congrArg (ids.respond pk sk st ch >>= ·) (funext fun oz => ?_)
  cases oz with
  | some z => simp [StateT.run_modify]
  | none => simp [StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp]

omit [SampleableType Stmt] in
/-- **The body-level tape resampling equality.** Drawing one signing body's `n` attempt
commitments inline (`ghostSignDrawBody`) is distributionally identical to pre-drawing the `n`-block
of full commitment draws into a tape and consuming it head-first (`tapeSignBody`):

`𝒟[(ghostSignDrawBody … n).run re] = 𝒟[drawList (ids.commit pk sk) n >>= tapeSignBody … tape]`.

The proof inducts on `n`: at each attempt, the recursive front block `drawList n` is commuted past
the inline `uniformSample`/`respond` draws (the i.i.d. resampling step
`evalDist_bind_comm_probComp`), the accepting branch discards the unused suffix
(`evalDist_bind_const_neverFails`, `drawList` never
fails), and the rejecting branch matches the inductive hypothesis. This is the per-body half of the
tape factorization; lifting it across the opaque adversary fold is the remaining content of
`readRecord_expected_pairs_le`. -/
theorem evalDist_ghostSignDrawBody_eq_drawList_tapeSignBody (pk : Stmt) (sk : Wit) (msg : M)
    (n : ℕ) (re : (M × Commit →ₒ Chal).QueryCache) :
    𝒟[(ghostSignDrawBody ids M pk sk msg n).run re] =
      𝒟[OracleComp.drawList (ids.commit pk sk) n >>= fun tape =>
          (tapeSignBody ids M pk sk msg tape).run re] := by
  induction n generalizing re with
  | zero => simp [ghostSignDrawBody, tapeSignBody, OracleComp.drawList]
  | succ n ih =>
      rw [run_ghostSignDrawBody_succ, OracleComp.drawList]
      simp only [bind_assoc, pure_bind]
      rw [evalDist_bind, evalDist_bind]
      refine congrArg (𝒟[ids.commit pk sk] >>= ·) (funext fun ws => ?_)
      obtain ⟨w, st⟩ := ws
      simp only [run_tapeSignBody_cons]
      set dl := OracleComp.drawList (ids.commit pk sk) n with hdl
      have hdlmass : Pr[⊥ | dl] = 0 := by rw [hdl]; exact OracleComp.probFailure_drawList _ _
      rw [show (𝒟[dl >>= fun rest => uniformSample Chal >>= fun ch =>
            ids.respond pk sk st ch >>= fun oz =>
              (match oz with
              | some z => pure ((some (w, z), []), re.cacheQuery (msg, w) ch)
              | none => (fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
                  (tapeSignBody ids M pk sk msg rest).run re : ProbComp _)])
          = 𝒟[uniformSample Chal >>= fun ch => dl >>= fun rest =>
              ids.respond pk sk st ch >>= fun oz =>
                (match oz with
                | some z => pure ((some (w, z), []), re.cacheQuery (msg, w) ch)
                | none => (fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
                    (tapeSignBody ids M pk sk msg rest).run re : ProbComp _)] from
        evalDist_bind_comm_probComp dl (uniformSample Chal) _]
      refine evalDist_bind_congr_left (uniformSample Chal) _ _ (fun ch => ?_)
      rw [show (𝒟[dl >>= fun rest => ids.respond pk sk st ch >>= fun oz =>
            (match oz with
            | some z => pure ((some (w, z), []), re.cacheQuery (msg, w) ch)
            | none => (fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
                (tapeSignBody ids M pk sk msg rest).run re : ProbComp _)])
          = 𝒟[ids.respond pk sk st ch >>= fun oz => dl >>= fun rest =>
              (match oz with
              | some z => pure ((some (w, z), []), re.cacheQuery (msg, w) ch)
              | none => (fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
                  (tapeSignBody ids M pk sk msg rest).run re : ProbComp _)] from
        evalDist_bind_comm_probComp dl (ids.respond pk sk st ch) _]
      refine evalDist_bind_congr_left (ids.respond pk sk st ch) _ _ (fun oz => ?_)
      cases oz with
      | some z => rw [evalDist_bind_const_neverFails dl hdlmass]
      | none =>
          change 𝒟[(fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
            (ghostSignDrawBody ids M pk sk msg n).run re] = _
          rw [evalDist_map_eq_of_evalDist_eq (ih re)]
          rw [map_eq_bind_pure_comp, bind_assoc]
          refine evalDist_bind_congr_left dl _ _ (fun rest => ?_)
          rw [map_eq_bind_pure_comp]

omit [SampleableType Stmt] in
/-- **Expected drawn-list length of the draw-collecting signing body.** Each attempt of
`ghostSignDrawBody` records exactly one i.i.d. raw `Prod.fst <$> ids.commit pk sk` commitment;
the loop continues only on a fresh-challenge rejection (probability `≤ p` per attempt), so the
expected length of the collected list is at most `∑_{a<n} p ^ a`, the geometric attempt-count fold
that bounds the per-signing-query draw count. The drawn list plays, for the deferred handler, the
role the ghost-cache size plays for the eager one. -/
lemma tsum_probOutput_run_ghostSignDrawBody_mul_length_le (pk : Stmt) (sk : Wit) (msg : M)
    {p_abort : ℝ}
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    ∀ (n : ℕ) (re : (M × Commit →ₒ Chal).QueryCache),
      ∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] * (z.1.2.length : ℝ≥0∞)
        ≤ ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a := by
  intro n
  induction n with
  | zero =>
      intro re
      simp only [ghostSignDrawBody, StateT.run_pure, tsum_probOutput_pure_mul]
      simp
  | succ n ih =>
      intro re
      classical
      set S : ℝ≥0∞ := ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a with hS
      have hSucc : ∑ a ∈ Finset.range (n + 1), ENNReal.ofReal p_abort ^ a =
          1 + ENNReal.ofReal p_abort * S := by
        rw [Finset.sum_range_succ', pow_zero, add_comm]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => pow_succ' _ _
      rw [run_ghostSignDrawBody_succ, tsum_probOutput_bind_mul]
      have h_ws : ∀ ws : Commit × PrvState,
          (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= z | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] * (z.1.2.length : ℝ≥0∞))
          ≤ 1 + Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] * S := by
        intro ws
        rw [tsum_probOutput_bind_mul]
        have h_ch : ∀ ch : Chal,
            (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
              Pr[= z | ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] * (z.1.2.length : ℝ≥0∞))
            ≤ 1 + Pr[= none | ids.respond pk sk ws.2 ch] * S := by
          intro ch
          rw [tsum_probOutput_bind_mul]
          have h_oz : ∀ oz : Option Resp,
              (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
                Pr[= z | (match oz with
                  | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                  | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                      (ghostSignDrawBody ids M pk sk msg n).run re :
                  ProbComp ((Option (Commit × Resp) × List Commit) ×
                    (M × Commit →ₒ Chal).QueryCache))] * (z.1.2.length : ℝ≥0∞))
              ≤ 1 + (if oz = none then S else 0) := by
            intro oz
            cases oz with
            | some z =>
                rw [if_neg (by simp), add_zero, tsum_probOutput_pure_mul]
                simp
            | none =>
                rw [if_pos rfl]
                -- length of `ws.1 :: rws.1.2` is `1 + rws.1.2.length`; rewrite map as bind+pure.
                rw [map_eq_bind_pure_comp, tsum_probOutput_bind_mul]
                calc (∑' z : (Option (Commit × Resp) × List Commit) ×
                      (M × Commit →ₒ Chal).QueryCache,
                    Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] *
                      (∑' y : (Option (Commit × Resp) × List Commit) ×
                          (M × Commit →ₒ Chal).QueryCache,
                        Pr[= y | (pure ((fun rws : (Option (Commit × Resp) × List Commit) ×
                            (M × Commit →ₒ Chal).QueryCache =>
                          ((rws.1.1, ws.1 :: rws.1.2), rws.2)) z) :
                          ProbComp ((Option (Commit × Resp) × List Commit) ×
                            (M × Commit →ₒ Chal).QueryCache))] * (y.1.2.length : ℝ≥0∞)))
                    = ∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] *
                        (1 + (z.1.2.length : ℝ≥0∞)) := by
                      refine tsum_congr fun z => ?_
                      rw [tsum_probOutput_pure_mul]
                      simp only [List.length_cons]
                      push_cast
                      ring_nf
                  _ = (∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re]) +
                      ∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] *
                        (z.1.2.length : ℝ≥0∞) := by
                      rw [← ENNReal.tsum_add]
                      exact tsum_congr fun z => by rw [mul_add, mul_one]
                  _ ≤ 1 + S := add_le_add tsum_probOutput_le_one (ih re)
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
      gcongr
      calc ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
            (Pr[= none | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch] * S)
          = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch]) * S := by
            rw [← ENNReal.tsum_mul_right]
            exact tsum_congr fun ws => (mul_assoc _ _ _).symm
        _ ≤ ENNReal.ofReal p_abort * S :=
            mul_le_mul_left (tsum_probOutput_commit_mul_abort_le ids pk sk hAbort) _

omit [SampleableType Stmt] in
/-- **Tight expected drawn-list length of the draw-collecting signing body.** Sharper companion to
`tsum_probOutput_run_ghostSignDrawBody_mul_length_le`: the expected number of *recorded* (rejected)
commitments of one `ghostSignDrawBody` run is at most the *reject-gated* geometric sum
`∑_{a<n} ofReal p^(a+1)` (each summand starts at `p^1`, not `p^0`). The first attempt's commitment
is recorded only on a *rejection* (probability `≤ p`); the accepting attempt records nothing. This
is the tight reject-count bound — `∑_{a<n} p^(a+1) ≤ p/(1-p)` — that the attempt-count law of the
redrafted residual needs: combined with the unconditional `+1` per signing query (the signed-message
list always grows by one), it gives the clean per-query charge `∑_{a≤n} p^a ≤ 1/(1-p)`, whereas the
loose bound `∑_{a<n} p^a` already saturates `1/(1-p)` for the rejects alone and cannot absorb the
extra `+1`. -/
lemma tsum_probOutput_run_ghostSignDrawBody_mul_length_le_tight (pk : Stmt) (sk : Wit) (msg : M)
    {p_abort : ℝ}
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    ∀ (n : ℕ) (re : (M × Commit →ₒ Chal).QueryCache),
      ∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] * (z.1.2.length : ℝ≥0∞)
        ≤ ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ (a + 1) := by
  intro n
  induction n with
  | zero =>
      intro re
      simp only [ghostSignDrawBody, StateT.run_pure, tsum_probOutput_pure_mul]
      simp
  | succ n ih =>
      intro re
      classical
      set S : ℝ≥0∞ := ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ (a + 1) with hS
      -- Target: the `(n+1)`-attempt reject-count expectation is `≤ ofReal p * (1 + S)`, which
      -- equals `∑_{a<n+1} ofReal p^(a+1)`.
      have hSucc : ∑ a ∈ Finset.range (n + 1), ENNReal.ofReal p_abort ^ (a + 1)
          = ENNReal.ofReal p_abort * (1 + S) := by
        rw [mul_add, mul_one, hS, Finset.mul_sum, Finset.sum_range_succ', pow_succ, pow_zero,
          one_mul, add_comm]
        congr 1
        exact Finset.sum_congr rfl fun a _ => by rw [← pow_succ']
      rw [hSucc, run_ghostSignDrawBody_succ, tsum_probOutput_bind_mul]
      -- Per-commit-draw `ws`: the recorded list is empty on accept and `ws.1 :: recursive` on
      -- reject; reject happens with probability `Pr[= none | uniformSample >>= respond]`.
      have h_ws : ∀ ws : Commit × PrvState,
          (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= z | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] * (z.1.2.length : ℝ≥0∞))
          ≤ Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] * (1 + S) := by
        intro ws
        rw [tsum_probOutput_bind_mul]
        have h_ch : ∀ ch : Chal,
            (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
              Pr[= z | ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] * (z.1.2.length : ℝ≥0∞))
            ≤ Pr[= none | ids.respond pk sk ws.2 ch] * (1 + S) := by
          intro ch
          rw [tsum_probOutput_bind_mul]
          -- Per response `oz`: accept contributes `0`, reject contributes `1 + S`.
          have h_oz : ∀ oz : Option Resp,
              (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
                Pr[= z | (match oz with
                  | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                  | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                      (ghostSignDrawBody ids M pk sk msg n).run re :
                  ProbComp ((Option (Commit × Resp) × List Commit) ×
                    (M × Commit →ₒ Chal).QueryCache))] * (z.1.2.length : ℝ≥0∞))
              ≤ (if oz = none then (1 : ℝ≥0∞) + S else 0) := by
            intro oz
            cases oz with
            | some z =>
                rw [if_neg (by simp), tsum_probOutput_pure_mul]
                simp [List.length]
            | none =>
                rw [if_pos rfl, map_eq_bind_pure_comp, tsum_probOutput_bind_mul]
                calc (∑' z : (Option (Commit × Resp) × List Commit) ×
                      (M × Commit →ₒ Chal).QueryCache,
                    Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] *
                      (∑' y : (Option (Commit × Resp) × List Commit) ×
                          (M × Commit →ₒ Chal).QueryCache,
                        Pr[= y | (pure ((fun rws : (Option (Commit × Resp) × List Commit) ×
                            (M × Commit →ₒ Chal).QueryCache =>
                          ((rws.1.1, ws.1 :: rws.1.2), rws.2)) z) :
                          ProbComp ((Option (Commit × Resp) × List Commit) ×
                            (M × Commit →ₒ Chal).QueryCache))] * (y.1.2.length : ℝ≥0∞)))
                    = ∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] *
                        (1 + (z.1.2.length : ℝ≥0∞)) := by
                      refine tsum_congr fun z => ?_
                      rw [tsum_probOutput_pure_mul]
                      simp only [List.length_cons]
                      push_cast
                      ring_nf
                  _ = (∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re]) +
                      ∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] *
                        (z.1.2.length : ℝ≥0∞) := by
                      rw [← ENNReal.tsum_add]
                      exact tsum_congr fun z => by rw [mul_add, mul_one]
                  _ ≤ 1 + S := add_le_add tsum_probOutput_le_one (ih re)
          refine le_trans (ENNReal.tsum_le_tsum fun oz =>
            mul_le_mul_right (h_oz oz) _) ?_
          rw [tsum_eq_single (none : Option Resp) fun oz hoz => by
            rw [if_neg hoz, mul_zero]]
          rw [if_pos rfl, mul_comm]
        refine le_trans (ENNReal.tsum_le_tsum fun ch =>
          mul_le_mul_right (h_ch ch) _) ?_
        rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
        exact le_of_eq (tsum_congr fun ch => (mul_assoc _ _ _).symm)
      refine le_trans (ENNReal.tsum_le_tsum fun ws => mul_le_mul_right (h_ws ws) _) ?_
      calc ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
            (Pr[= none | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch] * (1 + S))
          = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch]) * (1 + S) := by
            rw [← ENNReal.tsum_mul_right]
            exact tsum_congr fun ws => (mul_assoc _ _ _).symm
        _ ≤ ENNReal.ofReal p_abort * (1 + S) :=
            mul_le_mul_left (tsum_probOutput_commit_mul_abort_le ids pk sk hAbort) _

/-- The deferred-draw handler for the adversary's oracles, driving the distribution-level mono
skeleton against `ghostBlindImpl`. Carries the accumulated drawn-commitment list and a monotone
read-hit flag in place of the eager ghost cache (see `DeferredState`). -/
noncomputable def deferredDrawImpl (pk : Stmt) (sk : Wit) :
    QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT (DeferredState M Commit Chal) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n
  | .inl (.inr mc) => StateT.mk fun s =>
      (fun cu => (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2 || decide (mc.2 ∈ s.1.2)))) <$>
        roStep M s.1.1.1 mc
  | .inr msg => StateT.mk fun s =>
      (fun alc => (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2))) <$>
        (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1

omit [SampleableType Stmt] in
/-- **Sign-step coupling.** The eager ghost signing body `ghostSignBody` and the deferred draw-
collecting body `ghostSignDrawBody` are coupled, with their `ids.commit`/`uniformSample`/`respond`
draws matched, so that the outputs and real caches agree and the eager ghost layer's key domain is
covered by the front drawn list `drawn` extended with the body's collected commitments. Proved by
induction on the attempt budget: the accept branch writes the accepted commitment to both real
caches and leaves the ghost layer covered by `drawn`; the reject branch records the commitment in
the ghost layer and prepends it to the deferred collected list, recursing with a wider cover. -/
theorem signBody_couple (pk : Stmt) (sk : Wit) (msg : M) :
    ∀ (n : ℕ) (re gh : (M × Commit →ₒ Chal).QueryCache) (drawn : List Commit),
      (∀ mc : M × Commit, gh mc ≠ none → mc.2 ∈ drawn) →
      OracleComp.ProgramLogic.Relational.RelTriple
        ((ghostSignBody ids M pk sk msg n).run (re, gh))
        ((ghostSignDrawBody ids M pk sk msg n).run re)
        (fun p₁ p₂ => p₁.1 = p₂.1.1 ∧ p₁.2.1 = p₂.2 ∧
          (∀ mc : M × Commit, p₁.2.2 mc ≠ none → mc.2 ∈ drawn ++ p₂.1.2))
  | 0, re, gh, drawn, hcov => by
      simp only [ghostSignBody, ghostSignDrawBody, StateT.run_pure]
      exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure
        ⟨rfl, rfl, fun mc hmc => List.mem_append.2 (Or.inl (hcov mc hmc))⟩
  | (n+1), re, gh, drawn, hcov => by
      have hrun₁ : (ghostSignBody ids M pk sk msg (n+1)).run (re, gh) =
          (ids.commit pk sk >>= fun wst => uniformSample Chal >>= fun c =>
            ids.respond pk sk wst.2 c >>= fun oz =>
              match oz with
              | some z => pure (some (wst.1, z),
                  (re.cacheQuery (msg, wst.1) c, uncacheQuery M gh (msg, wst.1)))
              | none => (ghostSignBody ids M pk sk msg n).run
                  (re, gh.cacheQuery (msg, wst.1) c)) := by
        simp only [ghostSignBody, bind_assoc, StateT.run_bind, OracleComp.liftM_run_StateT,
          pure_bind]
        refine congrArg (ids.commit pk sk >>= ·) (funext fun wst => ?_)
        refine congrArg (uniformSample Chal >>= ·) (funext fun c => ?_)
        refine congrArg (ids.respond pk sk wst.2 c >>= ·) (funext fun oz => ?_)
        cases oz with
        | some z => simp [StateT.run_modify]
        | none => simp [StateT.run_bind, StateT.run_modify]
      have hrun₂ : (ghostSignDrawBody ids M pk sk msg (n+1)).run re =
          (ids.commit pk sk >>= fun wst => uniformSample Chal >>= fun c =>
            ids.respond pk sk wst.2 c >>= fun oz =>
              match oz with
              | some z => pure ((some (wst.1, z), []), re.cacheQuery (msg, wst.1) c)
              | none => (fun rws => ((rws.1.1, wst.1 :: rws.1.2), rws.2)) <$>
                  (ghostSignDrawBody ids M pk sk msg n).run re) := by
        simp only [ghostSignDrawBody, bind_assoc, StateT.run_bind, OracleComp.liftM_run_StateT,
          pure_bind]
        refine congrArg (ids.commit pk sk >>= ·) (funext fun wst => ?_)
        refine congrArg (uniformSample Chal >>= ·) (funext fun c => ?_)
        refine congrArg (ids.respond pk sk wst.2 c >>= ·) (funext fun oz => ?_)
        cases oz with
        | some z => simp [StateT.run_modify]
        | none => simp [StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp]
      rw [hrun₁, hrun₂]
      refine OracleComp.ProgramLogic.Relational.relTriple_bind
        (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_
      rintro wst _ (rfl : wst = _)
      refine OracleComp.ProgramLogic.Relational.relTriple_bind
        (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_
      rintro c _ (rfl : c = _)
      refine OracleComp.ProgramLogic.Relational.relTriple_bind
        (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_
      rintro oz _ (rfl : oz = _)
      cases oz with
      | some z =>
          refine OracleComp.ProgramLogic.Relational.relTriple_pure_pure ⟨rfl, rfl, ?_⟩
          intro mc hmc
          -- accept branch: ghost layer is `uncacheQuery M gh (msg, wst.1)`, whose domain ⊆ dom gh
          refine List.mem_append.2 (Or.inl (hcov mc ?_))
          by_cases hmceq : mc = (msg, wst.1)
          · exact absurd (by simp [uncacheQuery, hmceq]) hmc
          · simpa [uncacheQuery, hmceq] using hmc
      | none =>
          have hcov' : ∀ mc : M × Commit, (gh.cacheQuery (msg, wst.1) c) mc ≠ none →
              mc.2 ∈ drawn ++ [wst.1] := by
            intro mc hmc
            by_cases hmceq : mc = (msg, wst.1)
            · subst hmceq; exact List.mem_append.2 (Or.inr (by simp))
            · rw [QueryCache.cacheQuery_of_ne _ _ hmceq] at hmc
              exact List.mem_append.2 (Or.inl (hcov mc hmc))
          have hih := signBody_couple pk sk msg n re (gh.cacheQuery (msg, wst.1) c)
            (drawn ++ [wst.1]) hcov'
          rw [show ((fun rws : (Option (Commit × Resp) × List Commit) ×
                (M × Commit →ₒ Chal).QueryCache => ((rws.1.1, wst.1 :: rws.1.2), rws.2)) <$>
              (ghostSignDrawBody ids M pk sk msg n).run re)
              = ((ghostSignDrawBody ids M pk sk msg n).run re >>= fun rws =>
                pure ((rws.1.1, wst.1 :: rws.1.2), rws.2)) from by rw [map_eq_bind_pure_comp]; rfl]
          rw [show ((ghostSignBody ids M pk sk msg n).run (re, gh.cacheQuery (msg, wst.1) c))
              = ((ghostSignBody ids M pk sk msg n).run (re, gh.cacheQuery (msg, wst.1) c) >>= pure)
              from by rw [bind_pure]]
          refine OracleComp.ProgramLogic.Relational.relTriple_bind hih ?_
          rintro p₁ p₂ ⟨hout, hcache, hghcov⟩
          refine OracleComp.ProgramLogic.Relational.relTriple_pure_pure ⟨hout, hcache, ?_⟩
          intro mc hmc
          have hmem := hghcov mc hmc
          rw [List.append_assoc] at hmem
          simpa using hmem

/-! ### The deferred-coupling reduction

The eager ghost-blind bad marginal reduces, through the deferred-draw handler `deferredDrawImpl`,
to the deferred run's bad marginal. `ghostBlind_bad_le_deferredDraw` is a *pointwise coupling* of
the eager ghost-blind run with the deferred-draw run, established on the pointwise mono skeleton
`relTriple_simulateQ_run_mono` carrying the state invariant `deferredCoupleInv` (real cache and
signed list equal; ghost domain covered by the drawn-commitment list; bad-flag ordered). The read
step is an output-equal coupling (both answer from the real layer via `roStep`, and the membership
flag fires more readily on the deferred side because it ignores the message component); the sign
step couples the two bodies' `ids.commit` draws so the eager ghost writes and the deferred draws
stay in lockstep. `probEvent_le_of_relTriple_imp` then reads off the ordered bad marginals.

The pointwise route applies here precisely because the bad flags *are* pointwise linkable: eager
ghost-membership ⟹ deferred commitment-membership, since the drawn list grows in lockstep with the
ghost cache.

The deferred run's bad marginal is then carried — through the read-recording reduction
(`deferredDraw_bad_le_readRecord`) and the first-moment Markov step
(`readRecord_pred_le_expected_coincidences`) — to the expected coincidence count bounded by
`readRecord_expected_coincidences_le`.

The state invariant linking the eager `GhostState` and the deferred `DeferredState`: real cache and
signed-message list agree, every key in the ghost cache has its commitment recorded in the drawn
list, and the bad flag is ordered (eager-bad ⟹ deferred-bad). The read points coincide because both
sides answer from the (shared) real layer. -/
omit [SampleableType Stmt] in
/-- The coupling invariant between the eager ghost-blind state and the deferred-draw state: real
cache and signed list agree, every ghost-cache key's commitment is in the drawn list, and the bad
flag is ordered. -/
def deferredCoupleInv
    (s₁ : GhostState M Commit Chal) (s₂ : DeferredState M Commit Chal) : Prop :=
  s₁.1.1.1 = s₂.1.1.1 ∧ s₁.1.2 = s₂.1.1.2 ∧
    (∀ mc : M × Commit, s₁.1.1.2 mc ≠ none → mc.2 ∈ s₂.1.2) ∧
    (s₁.2 = true → s₂.2 = true)

omit [SampleableType Stmt] in
/-- **Per-query coupling step for the ghost-blind → deferred coupling.** From any pair of
`deferredCoupleInv`-related states, one step of the eager ghost-blind handler couples with one step
of the deferred-draw handler with equal output and the invariant preserved.

* **Uniform** steps forward the same draw; the state is untouched, so the invariant is inherited.
* **Read** steps answer from the shared real layer via `roStep` (same answer, same cache update);
  the eager bad flag fires on ghost-domain membership and the deferred one on drawn-list membership;
  the domain-coverage invariant makes the eager fire imply the deferred fire (it ignores the message
  component), preserving the bad ordering.
* **Sign** steps invoke `signBody_couple`: the matched `ids.commit` draws keep the outputs and real
  caches equal and extend the drawn list to cover the new ghost writes; the bad flag is intact. -/
theorem deferredCouple_step (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (u₁ : GhostState M Commit Chal) (u₂ : DeferredState M Commit Chal)
    (hu : deferredCoupleInv M u₁ u₂) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((ghostBlindImpl ids M maxAttempts pk sk t).run u₁)
      ((deferredDrawImpl ids M maxAttempts pk sk t).run u₂)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ deferredCoupleInv M p₁.2 p₂.2) := by
  obtain ⟨hre, hl, hdom, hbad⟩ := hu
  rcases t with (n | mc) | msg
  · -- UNIFORM: both forward the same draw; state untouched.
    have hrun₁ : (ghostBlindImpl ids M maxAttempts pk sk (.inl (.inl n))).run u₁ =
        (fun u => (u, u₁)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl
    have hrun₂ : (deferredDrawImpl ids M maxAttempts pk sk (.inl (.inl n))).run u₂ =
        (fun u => (u, u₂)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl
    rw [hrun₁, hrun₂]
    refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
      (OracleComp.ProgramLogic.Relational.relTriple_post_mono
        (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_)
    rintro a b (rfl : a = b)
    exact ⟨rfl, hre, hl, hdom, hbad⟩
  · -- READ: answer from the shared real layer; bad flag dominated under domain coverage.
    have hrun₂ : (deferredDrawImpl ids M maxAttempts pk sk (.inl (.inr mc))).run u₂ =
        (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, (((cu.2, u₂.1.1.2), u₂.1.2), u₂.2 || decide (mc.2 ∈ u₂.1.2)))) <$>
          roStep M u₂.1.1.1 mc := rfl
    cases hgh : u₁.1.1.2 mc with
    | none =>
        have hrun₁ : (ghostBlindImpl ids M maxAttempts pk sk (.inl (.inr mc))).run u₁ =
            (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, (((cu.2, u₁.1.1.2), u₁.1.2), u₁.2))) <$> roStep M u₁.1.1.1 mc := by
          rw [ghostBlindImpl_eq_ghostHybridImpl_false]
          exact ghostHybridImpl_run_ro_ghost_none ids M maxAttempts false pk sk hgh
        rw [hrun₁, hrun₂, hre]
        refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
          (OracleComp.ProgramLogic.Relational.relTriple_post_mono
            (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_)
        rintro a b (rfl : a = b)
        exact ⟨rfl, rfl, hl, hdom, fun hb => by rw [hbad hb]; rfl⟩
    | some v =>
        have hgh2 : u₁.1.1.2 mc ≠ none := by rw [hgh]; exact Option.some_ne_none v
        have hrun₁ : (ghostBlindImpl ids M maxAttempts pk sk (.inl (.inr mc))).run u₁ =
            (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, (((cu.2, u₁.1.1.2), u₁.1.2), true))) <$> roStep M u₁.1.1.1 mc := by
          rw [ghostBlindImpl_eq_ghostHybridImpl_false,
            ghostHybridImpl_run_ro_ghost_some ids M maxAttempts false pk sk hgh,
            if_neg Bool.false_ne_true]
        rw [hrun₁, hrun₂, hre]
        refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
          (OracleComp.ProgramLogic.Relational.relTriple_post_mono
            (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_)
        rintro a b (rfl : a = b)
        have hdef : (u₂.2 || decide (mc.2 ∈ u₂.1.2)) = true := by simp [hdom mc hgh2]
        exact ⟨rfl, rfl, hl, hdom, fun _ => hdef⟩
  · -- SIGN: couple the two signing bodies via `signBody_couple`; bad flag untouched.
    have hrun₁ : (ghostBlindImpl ids M maxAttempts pk sk (.inr msg)).run u₁ =
        (fun alc : Option (Commit × Resp) ×
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
          (alc.1, ((alc.2, msg :: u₁.1.2), u₁.2))) <$>
          (ghostSignBody ids M pk sk msg maxAttempts).run u₁.1.1 := by
      rw [ghostBlindImpl_eq_ghostHybridImpl_false]
      exact ghostHybridImpl_run_sign ids M maxAttempts false pk sk msg u₁
    have hrun₂ : (deferredDrawImpl ids M maxAttempts pk sk (.inr msg)).run u₂ =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, (((alc.2, msg :: u₂.1.1.2), u₂.1.2 ++ alc.1.2), u₂.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run u₂.1.1.1 := rfl
    rw [hrun₁, hrun₂]
    have hu11 : u₁.1.1 = (u₂.1.1.1, u₁.1.1.2) := by rw [← hre]
    rw [hu11]
    refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
      (OracleComp.ProgramLogic.Relational.relTriple_post_mono
        (signBody_couple ids M pk sk msg maxAttempts u₂.1.1.1 u₁.1.1.2 u₂.1.2 hdom) ?_)
    rintro p₁ p₂ ⟨hout, hcache, hghcov⟩
    exact ⟨hout, hcache, by rw [hl], hghcov, hbad⟩

omit [SampleableType Stmt] in
/-- **The ghost-blind → deferred run coupling.** By induction on the adversary computation `oa`,
the eager ghost-blind run and the deferred-draw run are coupled with the invariant
`deferredCoupleInv` preserved at every leaf, using `deferredCouple_step` at each query and the
inductive hypothesis for the continuation. -/
theorem deferredCouple_run {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s₁ : GhostState M Commit Chal) (s₂ : DeferredState M Commit Chal),
      deferredCoupleInv M s₁ s₂ →
      OracleComp.ProgramLogic.Relational.RelTriple
        ((simulateQ (ghostBlindImpl ids M maxAttempts pk sk) oa).run s₁)
        ((simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s₂)
        (fun q₁ q₂ => deferredCoupleInv M q₁.2 q₂.2) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s₁ s₂ hinv
      simp only [simulateQ_pure, StateT.run_pure]
      exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure hinv
  | query_bind t ob ih =>
      intro s₁ s₂ hinv
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      refine OracleComp.ProgramLogic.Relational.relTriple_bind
        (deferredCouple_step ids M maxAttempts pk sk t s₁ s₂ hinv) ?_
      rintro p₁ p₂ ⟨hout, hinv'⟩
      rw [show p₁.1 = p₂.1 from hout]
      exact ih p₂.1 p₁.2 p₂.2 hinv'

omit [SampleableType Stmt] in
/-- **The ghost-blind → deferred coupling.** The ghost-blind run's bad marginal is at most
the deferred-draw run's bad marginal, from any pair of `deferredCoupleInv`-related start states.

Reads off the bad-flag ordering component of the invariant from the run coupling
`deferredCouple_run` via `probEvent_le_of_relTriple_imp`. -/
theorem ghostBlind_bad_le_deferredDraw {γ : Type}
    (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (s₁ : GhostState M Commit Chal) (s₂ : DeferredState M Commit Chal)
    (hinv : deferredCoupleInv M s₁ s₂) :
    Pr[fun z : γ × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) oa).run s₁]
      ≤ Pr[fun z : γ × DeferredState M Commit Chal => z.2.2 = true |
          (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s₂] :=
  OracleComp.ProgramLogic.Relational.probEvent_le_of_relTriple_imp
    (deferredCouple_run ids M maxAttempts pk sk oa s₁ s₂ hinv)
    (fun _ _ hp => hp.2.2.2)

end scaffold

end EUF_CMA

end FiatShamirWithAbort
