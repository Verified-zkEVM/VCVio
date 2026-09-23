/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.HiddenReadFold

/-!
# EUF-CMA for Fiat-Shamir with aborts: CouplingEngine

`avgBadM_eager_le_lazy_joint`, a reusable free-monad telescoping engine for
dominating averaged bad masses under a two-measure coupling invariant, with the
geometric first-fire charge, the single-query deferral primitives and the
deferred-handler ingredients. Not on the live path of the ghost-read bound;
retained as general infrastructure.

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

/-! ## Measure-level eager↔lazy coupling engine

`avgBadM_eager_le_lazy_joint` is a reusable free-monad telescoping engine for dominating
averaged bad masses under a two-measure coupling invariant. It is not on the live path of
the ghost-read bound, which goes through the ghost-blind first-moment route
(`probEvent_ghostHybridImpl_bad_le_ghostBlind` into `probEvent_ghostBlindImpl_bad_le`). It
is retained here as general infrastructure for a joint-law approach to the eager↔lazy
comparison.

The engine carries a **two-measure coupling invariant** `Inv νe νl` through the free-monad
induction on `oa`: the uniform and signing steps preserve `Inv` on the per-output post-step
measures (the handlers are definitionally identical on those steps, so `postStepOutM` agrees
and `Inv` is threaded unchanged), the pure leaf compares the carried bad mass under `Inv`, and
the read step supplies the genuine deferred-sampling inequality — the eager read's averaged
ghost-hit marginal over `νe` dominated by the lazy read's deferred-fire marginal over `νl`.

A per-state (single-measure, `νe = νl`) version of the read inequality is **false** — at a
committed ghost-hit state the eager read flips the bad flag with mass `1` while the lazy read
fires with sub-unit mass — so the two-measure coupling is essential for any future application. -/

omit [SampleableType Stmt] in
/-- **Two-measure eager↔lazy averaged-bad coupling engine.** Threads a coupling invariant
`Inv : (state-measure) → (state-measure) → Prop` through the free-monad induction on `oa`:

* `h_step_eq`: a non-read step (uniform forward or signing query) preserves `Inv` on the
  per-output post-step measures. The eager and lazy handlers are definitionally identical on
  these steps, so the two `postStepOutM` measures are produced by the same map and `Inv` is
  threaded across them.
* `h_pure`: at a pure leaf the carried bad mass of `νe` is dominated by that of `νl` (under
  `Inv`).
* `h_read`: at a random-oracle read step, the eager read's averaged ghost-hit bad marginal
  over `νe` is dominated by the lazy read's deferred-fire marginal over `νl` (under `Inv`),
  with the invariant-conditional inductive hypothesis on the continuations available.

Given these, `avgBadM eager νe oa ≤ avgBadM lazy νl oa` for every `Inv`-related pair. This is
the measure-level coupling vehicle: the read-step averaging (signing-time draw into `νe`
versus read-time redraw of `νl`) is exactly what the per-output post-step *measures* (not
per-state Diracs) carry, which is why a per-state comparison cannot replace it. -/
lemma avgBadM_eager_le_lazy_joint (pk : Stmt) (sk : Wit)
    (Inv : (GhostState M Commit Chal → ℝ≥0∞) → (GhostState M Commit Chal → ℝ≥0∞) → Prop)
    (h_step_eq : ∀ (νe νl : GhostState M Commit Chal → ℝ≥0∞), Inv νe νl →
      ∀ (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain),
        (¬ t matches Sum.inl (Sum.inr _)) →
        ∀ u, Inv (OracleComp.ProgramLogic.Relational.postStepOutM
                (ghostHybridImpl ids M maxAttempts true pk sk) νe t u)
              (OracleComp.ProgramLogic.Relational.postStepOutM
                (lazyGhostHybridImpl ids M maxAttempts pk sk) νl t u))
    (h_read : ∀ (νe νl : GhostState M Commit Chal → ℝ≥0∞), Inv νe νl →
      ∀ (mc : M × Commit)
        (cont : Chal → OracleComp ((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))) (M × Option (Commit × Resp))),
        (∀ u νe' νl', Inv νe' νl' →
          OracleComp.ProgramLogic.Relational.avgBadM
              (ghostHybridImpl ids M maxAttempts true pk sk) νe' (cont u)
            ≤ OracleComp.ProgramLogic.Relational.avgBadM
              (lazyGhostHybridImpl ids M maxAttempts pk sk) νl' (cont u)) →
        (∑' p : GhostState M Commit Chal, νe p *
            ∑' z : Chal × GhostState M Commit Chal,
              Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk
                  (Sum.inl (Sum.inr mc))).run p] *
                Pr[ fun w : (M × Option (Commit × Resp)) × GhostState M Commit Chal =>
                    w.2.2 = true |
                  (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (cont z.1)).run z.2])
          ≤ ∑' p : GhostState M Commit Chal, νl p *
            ∑' z : Chal × GhostState M Commit Chal,
              Pr[= z | (lazyGhostHybridImpl ids M maxAttempts pk sk
                  (Sum.inl (Sum.inr mc))).run p] *
                Pr[ fun w : (M × Option (Commit × Resp)) × GhostState M Commit Chal =>
                    w.2.2 = true |
                  (simulateQ (lazyGhostHybridImpl ids M maxAttempts pk sk) (cont z.1)).run z.2])
    (h_pure : ∀ (νe νl : GhostState M Commit Chal → ℝ≥0∞), Inv νe νl →
      ∀ _x : M × Option (Commit × Resp),
        (∑' p : GhostState M Commit Chal, νe p * (if p.2 = true then 1 else 0))
            ≤ ∑' p : GhostState M Commit Chal, νl p * (if p.2 = true then 1 else 0))
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (M × Option (Commit × Resp))) :
    ∀ νe νl : GhostState M Commit Chal → ℝ≥0∞, Inv νe νl →
      OracleComp.ProgramLogic.Relational.avgBadM
          (ghostHybridImpl ids M maxAttempts true pk sk) νe oa
        ≤ OracleComp.ProgramLogic.Relational.avgBadM
          (lazyGhostHybridImpl ids M maxAttempts pk sk) νl oa := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro νe νl hInv
      rw [OracleComp.ProgramLogic.Relational.avgBadM_pure,
        OracleComp.ProgramLogic.Relational.avgBadM_pure]
      exact h_pure νe νl hInv x
  | @query_bind t cont ih =>
      intro νe νl hInv
      rcases t with (n | mc) | msg
      · rw [OracleComp.ProgramLogic.Relational.avgBadM_query_bind_eq_tsum_output,
          OracleComp.ProgramLogic.Relational.avgBadM_query_bind_eq_tsum_output]
        refine ENNReal.tsum_le_tsum fun u => ?_
        exact ih u _ _ (h_step_eq νe νl hInv (Sum.inl (Sum.inl n)) (by simp) u)
      · rw [OracleComp.ProgramLogic.Relational.avgBadM_query_bind_eq,
          OracleComp.ProgramLogic.Relational.avgBadM_query_bind_eq]
        exact h_read νe νl hInv mc cont (fun u νe' νl' h => ih u νe' νl' h)
      · rw [OracleComp.ProgramLogic.Relational.avgBadM_query_bind_eq_tsum_output,
          OracleComp.ProgramLogic.Relational.avgBadM_query_bind_eq_tsum_output]
        refine ENNReal.tsum_le_tsum fun u => ?_
        exact ih u _ _ (h_step_eq νe νl hInv (Sum.inr msg) (by simp) u)

omit [SampleableType Stmt] in
/-- **M1: the identical-until-bad / ghost-blind reduction** (foundational step of the
ghost-read bound). The eager hybrid handler `ghostHybridImpl … true` and the ghost-blind
handler `ghostBlindImpl` flip the adversarial-read bad flag with *exactly the same*
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
by the exact identical-until-bad bad-event equality
`probEvent_output_bad_eq'`. -/
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
/-- **M1 (≤ form).** The eager ghost-read bad mass is bounded by the ghost-blind handler's
bad mass at the empty-cache Dirac start; immediate from the equality
`probEvent_ghostHybridImpl_bad_eq_ghostBlind`. This is the reduction the read-bound spine
chains with M2 (reads ⊥ ghost-key values) and M3 (geometric first-fire charge). -/
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

/-! ### M3: the geometric first-fire charge (assembly)

`probEvent_ghostBlind_bad_le_of_fac` is the **M3** charge: given the **M2** deferred-sampling
factorization `hfac` — the ghost-blind run's bad marginal exhibited as the value-free
multi-key hidden-target game `kn >>= hiddenReadList (Prod.fst <$> ids.commit pk sk) (qH+1) σ`
(rejected commitment values deferred to a front block, read off by the adversary's adaptive
all-miss strategy `σ`) — the target bound `qS·(qH+1)·ε/(1-p)` follows by the
union-bound + geometric-fold pipeline:

* per-target guessing bound `hGuess` (raw `Pr[= w | commit] ≤ ε`) feeds the multi-key
  first-fire union bound `OracleComp.probEvent_bind_hiddenReadList_le`, giving
  `E[n]·((qH+1)·ε)` where `E[n] = ∑' n, Pr[= n | kn]·n` is the expected ghost-key count;
* the expected-count mean bound `hmean` (`E[n] ≤ qS/(1-p)`, the aggregate of
  `tsum_probOutput_commit_mul_abort_le` over the `qS` signing queries) folds into the target
  via `hiddenReadList_fold_le_target`.

The `Pr[reject|mc] ≤ 1` skew-drop is already baked into the raw-`commit` per-target bound
`hGuess` (the hidden targets are drawn from the *raw* commit law, not the rejection-conditioned
law), so no skew survives into this charge. The accepting attempt contributes `0` because it
is not a rejected draw and so is absent from `kn`'s key count. -/
omit [SampleableType Stmt] in
theorem probEvent_ghostBlind_bad_le_of_fac
    (qS qH : ℕ) (ε p_abort : ℝ) (hp : p_abort < 1)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (σ : List Bool → Commit) (kn : ProbComp ℕ)
    (hmean : ∑' n : ℕ, Pr[= n | kn] * (n : ℝ≥0∞)
      ≤ ENNReal.ofReal ((qS : ℝ) / (1 - p_abort)))
    (hfac : Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      ≤ Pr[(fun b : Bool => b = true) |
        kn >>= fun n => OracleComp.hiddenReadList (Prod.fst <$> ids.commit pk sk) (qH + 1) σ n]) :
    Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      ≤ ENNReal.ofReal (qS * ((qH : ℝ) + 1) * ε / (1 - p_abort)) := by
  refine (OracleComp.probEvent_le_of_eq_bind_hiddenReadList (oa := Prod.fst <$> ids.commit pk sk)
    (ε := ENNReal.ofReal ε) hGuess (qH + 1) σ kn hfac).trans ?_
  -- The averaged union bound `E[n]·((qH+1)·ε)` folds into the target via the geometric fold.
  refine le_trans (le_of_eq ?_)
    (hiddenReadList_fold_le_target qS qH ε p_abort hp (fun n => Pr[= n | kn]) hmean)
  -- Reconcile the `((qH+1)·ofReal ε)` factor shapes: `((qH:ℝ≥0∞)+1)` vs `↑(qH+1)`.
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [mul_assoc]
  congr 2
  push_cast
  ring

omit [SampleableType Stmt] in
/-- **Ghost-blind read-step bad indicator** (an M2 structural building block). Starting from a
state with the bad flag unset, the ghost-blind handler's adversarial random-oracle read at `mc`
sets the bad flag with mass exactly `1` if `mc` lies in the ghost-cache domain and `0`
otherwise. Identical indicator to the eager handler's `probOutput_ghostHybridImpl_read_bad`, but
here the *answer* is `roStep` on the real layer in **both** branches (hit and miss): the ghost
value never reaches the output, only the bad flag records the structural hit. This is the
manifest output-irrelevance of `ghostBlindImpl` at the read step — the per-read membership test
the M2 factorization reads off as a `hiddenReadList` probe. -/
lemma probEvent_ghostBlindImpl_read_bad (pk : Stmt) (sk : Wit) (mc : M × Commit)
    (s : ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M) :
    Pr[fun z : Chal × GhostState M Commit Chal => z.2.2 = true |
        (ghostBlindImpl ids M maxAttempts pk sk (.inl (.inr mc))).run (s, false)] =
      if s.1.2 mc = none then 0 else 1 := by
  rw [ghostBlindImpl_eq_ghostHybridImpl_false]
  cases hgh : s.1.2 mc with
  | some v =>
      rw [ghostHybridImpl_run_ro_ghost_some ids M maxAttempts false pk sk hgh]
      simp
  | none =>
      rw [ghostHybridImpl_run_ro_ghost_none ids M maxAttempts false pk sk hgh, ite_eq_left rfl]
      simp [probEvent_eq_zero]

/-! ### Stage 2: single-query deferral primitives

The value-free foundation (`blindStepProj_map_ghostBlindImpl_indep`, Stage 1) shows the stored
ghost commitment values never feed back into the ghost-blind run. The two lemmas here are the
*single-query* deferral atoms that Stage 3 instantiates once per rejected signing attempt:

* `ghostBlindImpl_read_singletonGhost_bad` connects the ghost-blind read handler to the
  membership predicate. With the ghost cache holding a single rejected-attempt key `(msg, w) ↦ c`,
  an adversarial read at `mc` fires the bad flag *exactly* when `mc = (msg, w)` — the structural
  read-hit test that `OracleComp.readMany` models for one hidden target.
* `ghostBlind_singleDraw_fire_le` is the commit-sampler instance of the deferral primitive
  `OracleComp.probEvent_bind_fire_le_of_gen`: a run that draws one ghost commitment up front and
  feeds it *only* through the fixed `q`-read game of a value-free generator fires with probability
  at most `q · ε`. This is the "front-loaded one draw" charge; Stage 3 supplies the value-free
  generator `gen` from `blindStepProj_map_ghostBlindImpl_indep` and folds the `qS` per-query
  charges into the aggregate `kn >>= drawList` block. -/

omit [SampleableType Stmt] in
/-- **Stage 2 read-membership atom.** With the ghost cache holding exactly the single
rejected-attempt key `(msg, w) ↦ c`, an adversarial random-oracle read at `mc` in the ghost-blind
run fires the bad flag with mass `1` when `mc = (msg, w)` and `0` otherwise. This is the structural
single-target read-hit indicator (`OracleComp.readMany`'s per-read test) realised by the
ghost-blind handler: the value `w` enters the run *only* through this membership test, never through
the read's answer (which is `roStep` on the real layer — `probEvent_ghostBlindImpl_read_bad`). -/
lemma ghostBlindImpl_read_singletonGhost_bad (pk : Stmt) (sk : Wit) (mc : M × Commit) (msg : M)
    (w : Commit) (c : Chal) (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    Pr[fun z : Chal × GhostState M Commit Chal => z.2.2 = true |
        (ghostBlindImpl ids M maxAttempts pk sk (.inl (.inr mc))).run
          (((re, (∅ : (M × Commit →ₒ Chal).QueryCache).cacheQuery (msg, w) c), l), false)] =
      if mc = (msg, w) then 1 else 0 := by
  rw [probEvent_ghostBlindImpl_read_bad ids M maxAttempts pk sk mc
    ((re, (∅ : (M × Commit →ₒ Chal).QueryCache).cacheQuery (msg, w) c), l)]
  by_cases h : mc = (msg, w)
  · subst h
    rw [ite_eq_right (by simp), ite_eq_left rfl]
  · rw [ite_eq_left (by simp [QueryCache.cacheQuery_of_ne _ _ h]), ite_eq_right h]

omit [SampleableType Stmt] [SampleableType Chal] in
/-- **Stage 2 single-query deferral.** A run that draws one ghost commitment
`w ← Prod.fst <$> ids.commit pk sk` (each outcome of mass at most `ε`) and feeds it to a
*value-free* continuation `k w = gen >>= fun p => pure (p.1, readMany w q p.2)` — a `w`-free
generator `gen` producing the visible output `p.1` and the `q`-read strategy `p.2`, with the drawn
commitment entering *only* through the fixed read game `readMany w q p.2` — fires with probability
at most `q · ε`.

This is the commit-sampler instance of `OracleComp.probEvent_bind_fire_le_of_gen`. The hypothesis
`hk` is exactly the value-freeness supplied by `blindStepProj_map_ghostBlindImpl_indep` (Stage 1):
because the ghost value never influences the run, the continuation's fire-marginal factors through
a `w`-free generator with the draw confined to the read-membership test
(`ghostBlindImpl_read_singletonGhost_bad`). Stage 3 instantiates this once per rejected attempt. -/
lemma ghostBlind_singleDraw_fire_le {α : Type} (pk : Stmt) (sk : Wit) {ε : ℝ≥0∞}
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ε)
    (q : ℕ) (gen : ProbComp (α × (List Bool → Commit))) (k : Commit → ProbComp (α × Bool))
    (hk : ∀ w : Commit, k w = gen >>= fun p => pure (p.1, OracleComp.readMany w q p.2)) :
    Pr[(fun z : α × Bool => z.2 = true) | (Prod.fst <$> ids.commit pk sk) >>= k]
      ≤ (q : ℝ≥0∞) * ε :=
  OracleComp.probEvent_bind_fire_le_of_gen hGuess q gen k hk

/-! ### M2: the deferred-sampling factorization

The **M2** content is the ghost-blind run's bad marginal *factoring* as a value-free deferred-draw
game. In this module it appears as the hypothesis `hfac` of `probEvent_ghostBlind_bad_le_of_fac`,
which is the σ-indexed (front-loaded hidden-target) form of the factorization. The headline takes
the σ-free route instead, charging the ghost-read bound through the first-moment residual
`readRecord_expected_coincidences_le` (the expected coincidence count of the value-free recorded
read-commit list with the recorded rejected draws).

Why it factors (the sound argument). In `ghostBlindImpl` an adversarial random-oracle read at a
ghost-cache hit answers from the *real* layer via `roStep` — identically to a miss — and only
*records* the would-hit by flipping the bad flag (`ghostBlindImpl_eq_ghostHybridImpl_false`,
`ghostBlindImpl_agree_good`). So the ghost-cache *values* are write-only side-data: they never
influence the run's outputs or continuation. Consequently the run's joint law of (adversary read
points, reject pattern / loop lengths, real cache) is produced by a value-free run that is
*independent of the stored commitment values*; those values are drawn `~ Prod.fst <$> ids.commit`
per *rejected* attempt and gated into the ghost cache by the reject decision.

Formalize as a deferred-sampling factorization: pull every rejected attempt's commitment draw
into the recorded drawn-list of the deferred handler `deferredDrawReadImpl`, independent of the
value-free recorded read-commit list. The expected coincidence count is then bounded by
`(#reads) · (#draws) · (max draw mass) ≤ (qH+1) · ε · E[#attempts]`, with `E[#attempts] ≤
qS/(1-p)` the aggregate of `tsum_probOutput_commit_mul_abort_le` over the `qS` signing queries
(each rejected attempt is reached with geometric probability, summed by `geomAttemptSum_le`).

Supporting tools for the σ-indexed form: the read-marginal equalities
`probEvent_ghostHybridImpl_read_bad_single_eq_lazyFire` /
`probOutput_eagerMultiReadBad_eq_lazyFire_or` (the signing-time→read-time draw commutation, here
applied to the value-free `ghostBlindImpl` continuation rather than the eager one whose
continuation depends on the read value), `probOutput_lazyGhostFire_one`, and the value-free
read-answer agreement (`ghostBlindImpl`'s hit branch is `roStep`, the same `map`-of-`roStep` as a
miss and as the lazy handler). Lifting the output-irrelevance through the `simulateQ` fold, so that
the per-rejected-attempt draws commute to the front independently of the intervening adversary
computation, is carried out on the σ-free route by
`evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead` in `Security/TapeFactorization.lean`.

This factorization route is sound precisely because `ghostBlindImpl` reads never feed the ghost
value into the run, so the draws are genuinely deferrable. -/

/-! ### Stage 3a: deferred-handler ingredients

The sound first-moment route couples the eager ghost-blind run to a *deferred* handler `impl₂` (a
genuine `QueryImpl`) via a per-step coupling relation `Rrun` on the two run distributions and the
two bad predicates `bad₁ / bad₂`. This block constructs those ingredients.

The deferred handler `deferredDrawImpl` carries, instead of eager-committed ghost keys, the
*accumulated list of drawn rejected-attempt commitments* (the front block, grown lazily as sign
steps draw) together with the real cache, the signed list, and the "some recorded read hit a drawn
commitment" flag. Its state is

  `DeferredState M Commit Chal :=
    (((M × Commit →ₒ Chal).QueryCache × List M) × List Commit) × Bool`.

Branch behaviour, designed so that the *observable* component (output, real cache, signed list)
coincides with the ghost-blind handler value-free (Stage 1):
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
@[expose] noncomputable def ghostSignDrawBody (pk : Stmt) (sk : Wit) (msg : M) :
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
/-- One-step unfolding of the draw-collecting signing body, mirroring `run_ghostSignBody_succ`.
The body draws a commitment `w`, samples a challenge `ch`, responds, and on accept records *no*
drawn commitment (the accepted commit is returned, not deferred) while on reject prepends `w` to
the recursively collected list of rejected commitments. -/
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

end scaffold

end EUF_CMA

end FiatShamirWithAbort
