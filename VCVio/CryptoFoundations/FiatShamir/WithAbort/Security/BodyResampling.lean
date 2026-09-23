/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.CouplingEngine

/-!
# EUF-CMA for Fiat-Shamir with aborts: BodyResampling

The per-body half of the tape factorization: a signing body's attempt draws
resample as a pre-drawn list consumed by `tapeSignBody`, with the expected-length
bounds of the ghost draw body and the body-level coupling `signBody_couple`.

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

/-! ### Body-level tape resampling (the per-body half of the tape factorization)

The draw-collecting signing body `ghostSignDrawBody` draws each attempt's commitment *inline*. The
genuine fold-lift content of the ghost-read bound is to front-load every interleaved per-attempt
draw into one independent block, so the drawn *values* factor away from the value-free adversarial
read points. The body-level half of that program — recasting one signing body's inline draws as
consumption from a *pre-drawn* tape — is proved here as a distributional equality
`evalSPMF_ghostSignDrawBody_eq_drawList_tapeSignBody`:

`𝒮[(ghostSignDrawBody … n).run re] = 𝒮[drawList (ids.commit pk sk) n >>= tapeSignBody … tape]`.

Pre-drawing the `n`-block of full `(Commit × PrvState)` commitment draws and consuming them
head-first (`tapeSignBody`) is distributionally identical to drawing them inline: the control flow
(accept/reject, via the inline `uniformSample`/`respond`) reads the *same* tape values, and the
unused suffix on an early accept is discarded. The proof is a structural induction on `n` that, at
each attempt, commutes the recursive front block `drawList n` past the inline
`uniformSample`/`respond` draws (`evalSPMF_bind_comm_probComp`, the i.i.d. resampling step) and
matches the reject-branch recursion to the inductive hypothesis.

This is the local, per-body `bind`-commutation. Its lift across the *opaque adversary*
`simulateQ (oa)` fold — the interleaved per-query draw blocks all commuting to the front, past the
adaptive read points — is `evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead` in
`Security/TapeFactorization.lean`. -/

/-- **i.i.d. bind-commutation at the distribution level for `ProbComp`.** Two independent draws
`oa`, `ob` feeding a common continuation `k` may be drawn in either order without changing the
output distribution. The `OracleComp` monad is *not* commutative as a free monad (its `bind` is
syntactic), but its `evalSPMF` image into `SPMF` is: the two iterated sums over the independent
draws exchange by `ENNReal.tsum_comm`. This is the local resampling step that front-loads an
output-irrelevant draw past its continuation. -/
theorem evalSPMF_bind_comm_probComp {α β γ : Type} (oa : ProbComp α) (ob : ProbComp β)
    (k : α → β → ProbComp γ) :
    𝒮[oa >>= fun a => ob >>= fun b => k a b] = 𝒮[ob >>= fun b => oa >>= fun a => k a b] := by
  refine SPMF.ext fun x => ?_
  rw [show 𝒮[oa >>= fun a => ob >>= fun b => k a b] x
        = Pr[= x | oa >>= fun a => ob >>= fun b => k a b] from (probOutput_def _ _).symm,
    show 𝒮[ob >>= fun b => oa >>= fun a => k a b] x
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
theorem evalSPMF_bind_const_neverFails {α γ : Type} (od : ProbComp α) (hmass : Pr[⊥ | od] = 0)
    (k : ProbComp γ) : 𝒮[od >>= fun _ => k] = 𝒮[k] := by
  refine SPMF.ext fun x => ?_
  rw [show 𝒮[od >>= fun _ => k] x = Pr[= x | od >>= fun _ => k] from (probOutput_def _ _).symm,
    show 𝒮[k] x = Pr[= x | k] from (probOutput_def _ _).symm]
  rw [probOutput_bind_const, hmass]; simp

/-- **Distribution-level congruence under a leading bind.** If two continuations agree as
distributions pointwise then the bound computations agree as distributions. -/
theorem evalSPMF_bind_congr_left {α β : Type} (oa : ProbComp α) (f g : α → ProbComp β)
    (h : ∀ a, 𝒮[f a] = 𝒮[g a]) : 𝒮[oa >>= f] = 𝒮[oa >>= g] := by
  rw [evalSPMF_bind, evalSPMF_bind]; exact congrArg _ (funext h)

/-- **Tape-consuming signing body.** Identical to `ghostSignDrawBody` except that each attempt's
commitment draw `(Commit × PrvState)` is *consumed* from a pre-drawn tape (head-first) instead of
drawn inline. The challenge sampling and response stay inline. On accept the remaining tape suffix
is discarded; an empty tape ends the loop (mirroring budget exhaustion). The recorded
rejected-commit list is built exactly as in `ghostSignDrawBody`. -/
@[expose] noncomputable def tapeSignBody (pk : Stmt) (sk : Wit) (msg : M) :
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

`𝒮[(ghostSignDrawBody … n).run re] = 𝒮[drawList (ids.commit pk sk) n >>= tapeSignBody … tape]`.

The proof inducts on `n`: at each attempt, the recursive front block `drawList n` is commuted past
the inline `uniformSample`/`respond` draws (the i.i.d. resampling step
`evalSPMF_bind_comm_probComp`), the accepting branch discards the unused suffix
(`evalSPMF_bind_const_neverFails`, `drawList` never
fails), and the rejecting branch matches the inductive hypothesis. This is the per-body half of the
tape factorization; its lift across the opaque adversary fold is
`evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead`. -/
theorem evalSPMF_ghostSignDrawBody_eq_drawList_tapeSignBody (pk : Stmt) (sk : Wit) (msg : M)
    (n : ℕ) (re : (M × Commit →ₒ Chal).QueryCache) :
    𝒮[(ghostSignDrawBody ids M pk sk msg n).run re] =
      𝒮[OracleComp.drawList (ids.commit pk sk) n >>= fun tape =>
          (tapeSignBody ids M pk sk msg tape).run re] := by
  induction n generalizing re with
  | zero => simp [ghostSignDrawBody, tapeSignBody, OracleComp.drawList]
  | succ n ih =>
      rw [run_ghostSignDrawBody_succ, OracleComp.drawList]
      simp only [bind_assoc, pure_bind]
      rw [evalSPMF_bind, evalSPMF_bind]
      refine congrArg (𝒮[ids.commit pk sk] >>= ·) (funext fun ws => ?_)
      obtain ⟨w, st⟩ := ws
      simp only [run_tapeSignBody_cons]
      set dl := OracleComp.drawList (ids.commit pk sk) n with hdl
      have hdlmass : Pr[⊥ | dl] = 0 := by rw [hdl]; exact OracleComp.probFailure_drawList _ _
      rw [show (𝒮[dl >>= fun rest => uniformSample Chal >>= fun ch =>
            ids.respond pk sk st ch >>= fun oz =>
              (match oz with
              | some z => pure ((some (w, z), []), re.cacheQuery (msg, w) ch)
              | none => (fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
                  (tapeSignBody ids M pk sk msg rest).run re : ProbComp _)])
          = 𝒮[uniformSample Chal >>= fun ch => dl >>= fun rest =>
              ids.respond pk sk st ch >>= fun oz =>
                (match oz with
                | some z => pure ((some (w, z), []), re.cacheQuery (msg, w) ch)
                | none => (fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
                    (tapeSignBody ids M pk sk msg rest).run re : ProbComp _)] from
        evalSPMF_bind_comm_probComp dl (uniformSample Chal) _]
      refine evalSPMF_bind_congr_left (uniformSample Chal) _ _ (fun ch => ?_)
      rw [show (𝒮[dl >>= fun rest => ids.respond pk sk st ch >>= fun oz =>
            (match oz with
            | some z => pure ((some (w, z), []), re.cacheQuery (msg, w) ch)
            | none => (fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
                (tapeSignBody ids M pk sk msg rest).run re : ProbComp _)])
          = 𝒮[ids.respond pk sk st ch >>= fun oz => dl >>= fun rest =>
              (match oz with
              | some z => pure ((some (w, z), []), re.cacheQuery (msg, w) ch)
              | none => (fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
                  (tapeSignBody ids M pk sk msg rest).run re : ProbComp _)] from
        evalSPMF_bind_comm_probComp dl (ids.respond pk sk st ch) _]
      refine evalSPMF_bind_congr_left (ids.respond pk sk st ch) _ _ (fun oz => ?_)
      cases oz with
      | some z => rw [evalSPMF_bind_const_neverFails dl hdlmass]
      | none =>
          change 𝒮[(fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
            (ghostSignDrawBody ids M pk sk msg n).run re] = _
          rw [evalSPMF_map_eq_of_evalSPMF_eq (ih re)]
          rw [map_eq_bind_pure_comp, bind_assoc]
          refine evalSPMF_bind_congr_left dl _ _ (fun rest => ?_)
          rw [map_eq_bind_pure_comp]

omit [SampleableType Stmt] in
/-- **Expected drawn-list length of the draw-collecting signing body.** Each attempt of
`ghostSignDrawBody` records exactly one i.i.d. raw `Prod.fst <$> ids.commit pk sk` commitment;
the loop continues only on a fresh-challenge rejection (probability `≤ p` per attempt), so the
expected length of the collected list is at most `∑_{a<n} p ^ a`, the geometric attempt-count
fold (`geomAttemptSum_le`) that bounds the per-signing-query draw count. This is the deferred-draw
counterpart of `tsum_probOutput_run_ghostSignBody_mul_ghost_enncard_le`: the drawn list replaces
the eager ghost layer, so its length plays the role of the ghost-cache size. -/
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
                rw [ite_eq_right (by simp), add_zero, tsum_probOutput_pure_mul]
                simp
            | none =>
                rw [ite_eq_left rfl]
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
                rw [ite_eq_right (by simp), tsum_probOutput_pure_mul]
                simp [List.length]
            | none =>
                rw [ite_eq_left rfl, map_eq_bind_pure_comp, tsum_probOutput_bind_mul]
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
            rw [ite_eq_right hoz, mul_zero]]
          rw [ite_eq_left rfl, mul_comm]
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

omit [SampleableType Stmt] in
/-- **Single-signing-body resampling over-count.** Testing the *drawn list* produced by one
`ghostSignDrawBody` run (the rejected-attempt commitments, write-only side-data) against any *fixed*
read strategy `σ` with `q` reads fires with probability at most testing `n` *fresh* i.i.d. raw
`Prod.fst <$> ids.commit pk sk` draws against the same strategy (`drawList … n`, where `n` is the
attempt budget `maxAttempts`).

This is the genuine per-query resampling content, isolated to one signing body. The drawn list of
the body is *not* equal in law to `n` fresh raw draws (the rejected draws are skewed by the
rejection-conditioning `commit | reject`), but the firing event over-counts to the fresh game: on
the accept branch the body records *no* commitment (so its read-game fires with probability `0`,
dominated by the fresh side, which still draws and tests one value); on the reject branch the body's
recorded commitment is a raw `Prod.fst <$> ids.commit pk sk` draw — distributed exactly as the fresh
head — and its `readMany` test matches the fresh head's, while the recursive rejected list is
dominated by the recursive fresh list (induction). The read strategy `σ` is *fixed* (the read points
are determined by the all-miss reply history; the drawn values never feed them — value-freeness),
which is what lets a single `σ` dominate both sides. The corresponding fold-level statement —
front-loading every signing query's interleaved draws into one aggregate `drawList` block — is
`evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead`, which the headline uses on the σ-free
first-moment route. This lemma is the single-body over-count in σ-indexed form; it is not on the
live headline path (which charges the expected coincidence count directly). -/
lemma ghostSignDrawBody_readManyList_le_drawList (pk : Stmt) (sk : Wit) (msg : M)
    (q : ℕ) (σ : List Bool → Commit) :
    ∀ (n : ℕ) (re : (M × Commit →ₒ Chal).QueryCache),
      Pr[(fun b : Bool => b = true) |
          (ghostSignDrawBody ids M pk sk msg n).run re >>= fun rws =>
            pure (OracleComp.readManyList rws.1.2 q σ)]
        ≤ Pr[(fun b : Bool => b = true) |
            OracleComp.drawList (Prod.fst <$> ids.commit pk sk) n >>= fun ws =>
              pure (OracleComp.readManyList ws q σ)] := by
  intro n
  induction n with
  | zero =>
      intro re
      simp [ghostSignDrawBody, OracleComp.drawList, OracleComp.readManyList]
  | succ n ih =>
      intro re
      -- Unfold one attempt on the left and one fresh draw on the right; both bind over the same
      -- raw `ids.commit pk sk` draw, so compare the per-draw fire-marginals termwise.
      rw [run_ghostSignDrawBody_succ]
      rw [OracleComp.drawList, bind_assoc, bind_map_left]
      simp only [bind_assoc, pure_bind]
      rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      refine ENNReal.tsum_le_tsum fun ws => ?_
      gcongr
      -- Per commit draw `ws`: name the recursive fresh `n`-draw game and the recursive body-`n`
      -- game; the latter is `≤` the former by the inductive hypothesis (`ih`).
      set RHSinner : ℝ≥0∞ := Pr[(fun b : Bool => b = true) |
        OracleComp.drawList (Prod.fst <$> ids.commit pk sk) n >>= fun rest =>
          pure (OracleComp.readManyList rest q σ)] with hRHSinner
      by_cases hhead : OracleComp.readMany ws.1 q σ = true
      · -- The head already fires: the RHS `readManyList (ws.1 :: rest)` is always `true`, so the
        -- RHS per-draw marginal is the full mass of `drawList n` = 1 ≥ the LHS.
        refine le_trans probEvent_le_one (le_of_eq ?_)
        symm
        have hcongr : (OracleComp.drawList (Prod.fst <$> ids.commit pk sk) n >>= fun rest =>
              pure (OracleComp.readManyList (ws.1 :: rest) q σ))
            = (OracleComp.drawList (Prod.fst <$> ids.commit pk sk) n >>= fun _ =>
              (pure true : ProbComp Bool)) := by
          refine bind_congr fun rest => ?_
          rw [OracleComp.readManyList, List.any_cons, hhead, Bool.true_or]
        rw [hcongr, probEvent_bind_eq_tsum]
        simp only [probEvent_pure, ite_eq_left]
        rw [ENNReal.tsum_mul_right, OracleComp.tsum_probOutput_drawList_eq_one, one_mul]
      · -- The head misses: the RHS reduces to the recursive fresh game `RHSinner`, and the LHS is
        -- dominated by the recursive body-`n` game, which is `≤ RHSinner` by `ih`.
        rw [Bool.not_eq_true] at hhead
        have hRHS : Pr[(fun b : Bool => b = true) |
              OracleComp.drawList (Prod.fst <$> ids.commit pk sk) n >>= fun rest =>
                pure (OracleComp.readManyList (ws.1 :: rest) q σ)] = RHSinner := by
          rw [hRHSinner]
          refine probEvent_bind_congr fun rest _ => ?_
          rw [OracleComp.readManyList, List.any_cons, hhead, Bool.false_or, OracleComp.readManyList]
        rw [hRHS]
        -- The LHS per-draw game is dominated by the recursive body-`n` game: drop the
        -- `uniformSample`/`respond` draws (mass `≤ 1`); the accept branch records `[]`
        -- (`readManyList [] = false`, fires with probability `0`) and the reject branch's head
        -- test `readMany ws.1 q σ` misses (`hhead`), so its `readManyList (ws.1 :: inner)` reduces
        -- to the body-`n` game's `readManyList inner`.
        refine le_trans ?_ (ih re)
        refine probEvent_bind_le_of_forall_le fun ch _ => ?_
        refine probEvent_bind_le_of_forall_le fun oz _ => ?_
        cases oz with
        | some z => simp [OracleComp.readManyList]
        | none =>
            rw [bind_map_left]
            refine le_of_eq ?_
            refine probEvent_bind_congr fun rws _ => ?_
            rw [OracleComp.readManyList, List.any_cons, hhead, Bool.false_or,
              OracleComp.readManyList]

/-- The deferred-draw handler for the adversary's oracles, driving the distribution-level mono
skeleton against `ghostBlindImpl`. Carries the accumulated drawn-commitment list and a monotone
read-hit flag in place of the eager ghost cache (see `DeferredState`). -/
@[expose] noncomputable def deferredDrawImpl (pk : Stmt) (sk : Wit) :
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
/-- **Per-step expected drawn-list length growth of the deferred-draw handler.** One step of
`deferredDrawImpl` grows the expected drawn-list length by at most `1/(1-p)` on a signing query and
by `0` on a uniform or random-oracle-read query (which leave the drawn list untouched). The
signing-step bound is the per-query draw count `tsum_probOutput_run_ghostSignDrawBody_mul_length_le`
folded with `geomAttemptSum_le`. This is the per-step charge that the run-level mean fold
`deferredDraw_run_expected_length_le` telescopes against `signHashQueryBound`. -/
lemma deferredDrawImpl_step_expected_length_le (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : DeferredState M Commit Chal) :
    (∑' z : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t) ×
        DeferredState M Commit Chal,
      Pr[= z | (deferredDrawImpl ids M maxAttempts pk sk t).run s] * (z.2.1.2.length : ℝ≥0∞))
      ≤ (s.1.2.length : ℝ≥0∞) +
          (if (t matches Sum.inr _) then ENNReal.ofReal (1 / (1 - p_abort)) else 0) := by
  classical
  rcases t with (n | mc) | msg
  · -- UNIFORM: state untouched, drawn list `s.1.2` preserved.
    rw [ite_eq_right (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ (by simp [deferredDrawImpl]))
    intro z hz
    have hzs : z ∈ support ((fun u => (u, s)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hz
    rw [support_map] at hzs
    obtain ⟨u, _, rfl⟩ := hzs; rfl
  · -- READ: writes only the base cache / bad flag; drawn list `s.1.2` preserved.
    rw [ite_eq_right (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ ?_)
    · intro z hz
      have hzs : z ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2 || decide (mc.2 ∈ s.1.2)))) <$>
            roStep M s.1.1.1 mc) := hz
      rw [support_map] at hzs
      obtain ⟨cu, _, rfl⟩ := hzs; rfl
    · simp only [deferredDrawImpl, StateT.run_mk]
      rcases hg : s.1.1.1 mc with _ | v <;> simp [roStep, hg]
  · -- SIGN: drawn list becomes `s.1.2 ++ alc.1.2`; expected new length ≤ 1/(1-p).
    rw [ite_eq_left (by simp)]
    have hrun : (deferredDrawImpl ids M maxAttempts pk sk (.inr msg)).run s =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1 := rfl
    rw [hrun]
    refine le_of_eq_of_le (tsum_probOutput_map_mul
      ((ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1)
      (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
        (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2)))
      (fun z => (z.2.1.2.length : ℝ≥0∞))) ?_
    calc _
        = ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1] *
              ((s.1.2.length : ℝ≥0∞) + (alc.1.2.length : ℝ≥0∞)) := by
          refine tsum_congr fun alc => ?_
          simp only [List.length_append]
          push_cast
          ring
      _ = (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1] *
              (s.1.2.length : ℝ≥0∞)) +
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1] *
              (alc.1.2.length : ℝ≥0∞) := by
          rw [← ENNReal.tsum_add]; exact tsum_congr fun alc => by rw [mul_add]
      _ ≤ (s.1.2.length : ℝ≥0∞) + ENNReal.ofReal (1 / (1 - p_abort)) := by
          refine add_le_add ?_ ?_
          · rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]
          · exact le_trans (tsum_probOutput_run_ghostSignDrawBody_mul_length_le ids M pk sk msg
              hAbort maxAttempts s.1.1.1) (geomAttemptSum_le maxAttempts hp₀ hp)

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

end scaffold

end EUF_CMA

end FiatShamirWithAbort
