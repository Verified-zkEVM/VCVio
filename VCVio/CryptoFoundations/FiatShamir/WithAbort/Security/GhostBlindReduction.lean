/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.BodyHops
public import VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies.BodyBounds

/-!
# EUF-CMA for Fiat-Shamir with aborts: GhostBlindReduction

The first link of the ghost-read bound and the draw-collecting signing body it is coupled
with. The eager ghost-read bad event equals the bad event of the ghost-blind handler
(`prEvent_ghostHybridImpl_bad_eq_ghostBlind`), whose reads never consult the ghost values;
`ghostSignDrawBody` is the signing body of the deferred handler that
`Security/DeferredCoupling.lean` couples to the ghost-blind run.

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

/-! ## Ghost-blind reduction

The ghost-read bound goes through the ghost-blind handler: the eager bad event is replaced by
the ghost-blind one (`prEvent_ghostHybridImpl_bad_le_ghostBlind`), which
`prEvent_ghostBlindImpl_bad_le` then charges through the deferred-draw coupling and the
first-moment bound. -/

omit [SampleableType Stmt] in
/-- **Identical-until-bad / ghost-blind reduction** (the first step of the ghost-read
bound). The eager hybrid handler `ghostHybridImpl … true` and the ghost-blind
handler `ghostBlindImpl` flip the adversarial-read bad flag with *exactly the same*
probability at the empty-cache Dirac start:

`Pr{let z ← (simulateQ (ghostHybridImpl … true) (adv.main pk)).run δ_∅}[z.2.2 = true]`
`  = Pr{let z ← (simulateQ ghostBlindImpl (adv.main pk)).run δ_∅}[z.2.2 = true]`.

The two handlers are *identical until bad*: they coincide on uniform queries, on signing
queries, and on ghost-*miss* reads (all run the same `roStep` / `ghostSignBody`), and on a
ghost-*hit* read both flip the bad flag (`ghostBlindImpl_agree_good`), while neither ever
unsets it (`ghostHybridImpl_bad_mono` / `ghostBlindImpl_bad_mono`). The blind handler answers
a hit from the real layer instead of returning the ghost value, so the ghost-key values never
influence the run — they are consulted only to record the would-hit. Because the runs differ
only on the already-bad trajectory (where both flags read `true`), the bad marginals coincide,
by the exact identical-until-bad bad-event equality
`prEvent_simulateQ_run_bad_eq`. -/
lemma prEvent_ghostHybridImpl_bad_eq_ghostBlind (pk : Stmt) (sk : Wit) :
    Pr{let z ← ((simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false))}[z.2.2 = true]
      = Pr{let z ← ((simulateQ (ghostBlindImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false))}[z.2.2 = true] :=
  OracleComp.ProgramLogic.Relational.prEvent_simulateQ_run_bad_eq
    (ghostHybridImpl ids M maxAttempts true pk sk)
    (ghostBlindImpl ids M maxAttempts pk sk) (fun p => p.2 = true)
    (fun t s hs q => by
      obtain ⟨s, b⟩ := s
      obtain rfl : b = false := by simpa using hs
      exact OracleComp.ProgramLogic.Relational.prEvent_and_not_flag_eq_of_forall_prEvent_eq
        (fun u s' => ghostBlindImpl_agree_good ids M maxAttempts pk sk t s u s') q)
    (ghostHybridImpl_bad_mono ids M maxAttempts true pk sk)
    (ghostBlindImpl_bad_mono ids M maxAttempts pk sk)
    (adv.main pk) ((((∅, ∅), []) : _), false)

omit [SampleableType Stmt] in
/-- The eager ghost-read bad mass is bounded by the ghost-blind handler's bad mass at the
empty-cache Dirac start; immediate from the equality
`prEvent_ghostHybridImpl_bad_eq_ghostBlind`. -/
lemma prEvent_ghostHybridImpl_bad_le_ghostBlind (pk : Stmt) (sk : Wit) :
    Pr{let z ← ((simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false))}[z.2.2 = true]
      ≤ Pr{let z ← ((simulateQ (ghostBlindImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false))}[z.2.2 = true] :=
  (prEvent_ghostHybridImpl_bad_eq_ghostBlind ids hr M maxAttempts adv pk sk).le

/-! ## Deferred-handler ingredients

In `ghostBlindImpl` an adversarial random-oracle read at a ghost-cache hit answers from the
real layer via `roStep`, identically to a miss, and only records the would-hit by flipping the
bad flag (`ghostBlindImpl_agree_good`). The ghost-cache values are therefore write-only side
data: the run's outputs and continuation do not depend on them. The deferred handler
`deferredDrawImpl` (`Security/DrawCollectingBody.lean`) exploits this: instead of eager-committed
ghost keys it carries the accumulated list of drawn rejected-attempt commitments, together
with the real cache, the signed list and the "some recorded read hit a drawn commitment" flag.
Its state is

  `DeferredState M Commit Chal :=
    (((M × Commit →ₒ Chal).QueryCache × List M) × List Commit) × Bool`.

On uniform queries and random-oracle reads it behaves as `ghostBlindImpl` on the observable
component (output, real cache, signed list); a read sets the bad flag iff its commitment is
among the drawn list. On a signing query it runs `ghostSignDrawBody` below, which appends one
i.i.d. raw `Prod.fst <$> ids.commit pk sk` draw per rejected attempt. -/

/-- State of the deferred-draw handler: real cache, signed-message list, the accumulated list of
drawn rejected-attempt commitments, and the monotone "some recorded read hit a drawn commitment"
flag. The drawn list replaces the eager ghost cache: where `ghostBlindImpl` commits sampled keys
into its ghost layer, `deferredDrawImpl` only records the *list* of drawn commitments. Random-oracle
reads are recorded against that list (module `ReadRecording`), and each drawn commitment is
charged as a fresh raw commitment independent of the recorded reads
(`tsum_prEvent_commit_mul_count_le`). -/
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
/-- One-step unfolding of the draw-collecting signing body.
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
