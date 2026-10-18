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
`evalDistEq_ghostSignDrawBody_eq_drawList_tapeSignBody`:

`((ghostSignDrawBody … n).run re) =ᵈ (drawList (ids.commit pk sk) n >>= tapeSignBody … tape)`.

Pre-drawing the `n`-block of full `(Commit × PrvState)` commitment draws and consuming them
head-first (`tapeSignBody`) is distributionally identical to drawing them inline: the control flow
(accept/reject, via the inline `uniformSample`/`respond`) reads the *same* tape values, and the
unused suffix on an early accept is discarded. The proof is a structural induction on `n` that, at
each attempt, commutes the recursive front block `drawList n` past the inline
`uniformSample`/`respond` draws (`OracleComp.EvalDistEq.bind_bind_swap`, the i.i.d. resampling
step) and matches the reject-branch recursion to the inductive hypothesis.

This is the local, per-body `bind`-commutation. Its lift across the *opaque adversary*
`simulateQ (oa)` fold — the interleaved per-query draw blocks all commuting to the front, past the
adaptive read points — is `evalDistEq_deferredDrawRead_eq_drawList_tapeDrawRead` in
`Security/TapeFactorization.lean`. -/

omit [SampleableType Stmt] in
/-- **Tight expected drawn-list length of the draw-collecting signing body.** Sharper companion to
`tsum_prEvent_run_ghostSignDrawBody_mul_length_le`: the expected number of *recorded* (rejected)
commitments of one `ghostSignDrawBody` run is at most the *reject-gated* geometric sum
`∑_{a<n} ofReal p^(a+1)` (each summand starts at `p^1`, not `p^0`). The first attempt's commitment
is recorded only on a *rejection* (probability `≤ p`); the accepting attempt records nothing. This
is the tight reject-count bound — `∑_{a<n} p^(a+1) ≤ p/(1-p)` — that the attempt-count law of the
redrafted residual needs: combined with the unconditional `+1` per signing query (the signed-message
list always grows by one), it gives the clean per-query charge `∑_{a≤n} p^a ≤ 1/(1-p)`, whereas the
loose bound `∑_{a<n} p^a` already saturates `1/(1-p)` for the rejects alone and cannot absorb the
extra `+1`. -/
lemma tsum_prEvent_run_ghostSignDrawBody_mul_length_le_tight (pk : Stmt) (sk : Wit) (msg : M)
    {p_abort : ℝ}
    (hAbort : Pr{let x ← ids.honestExecution pk sk}[x = none] ≤ ENNReal.ofReal p_abort) :
    ∀ (n : ℕ) (re : (M × Commit →ₒ Chal).QueryCache),
      ∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr{let x ← (ghostSignDrawBody ids M pk sk msg n).run re}[x = z] * (z.1.2.length : ℝ≥0∞)
        ≤ ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ (a + 1) := by
  intro n
  induction n with
  | zero =>
      intro re
      simp only [ghostSignDrawBody, StateT.run_pure, OracleComp.tsum_prEvent_pure_mul]
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
      rw [hSucc, run_ghostSignDrawBody_succ, OracleComp.tsum_prEvent_bind_mul]
      -- Per-commit-draw `ws`: the recorded list is empty on accept and `ws.1 :: recursive` on
      -- reject; reject happens with probability `Pr{let x ← uniformSample >>= respond}[x = none]`.
      have h_ws : ∀ ws : Commit × PrvState,
          (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr{let x ← (uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re)}[x = z] * (z.1.2.length : ℝ≥0∞))
          ≤ Pr{let x ← uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch}[x = none]
              * (1 + S) := by
        intro ws
        rw [OracleComp.tsum_prEvent_bind_mul]
        have h_ch : ∀ ch : Chal,
            (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
              Pr{let x ← (ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re)}[x = z] * (z.1.2.length : ℝ≥0∞))
            ≤ Pr{let x ← ids.respond pk sk ws.2 ch}[x = none] * (1 + S) := by
          intro ch
          rw [OracleComp.tsum_prEvent_bind_mul]
          -- Per response `oz`: accept contributes `0`, reject contributes `1 + S`.
          have h_oz : ∀ oz : Option Resp,
              (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
                Pr{let x ← (match oz with
                  | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                  | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                      (ghostSignDrawBody ids M pk sk msg n).run re :
                  ProbComp ((Option (Commit × Resp) × List Commit) ×
                    (M × Commit →ₒ Chal).QueryCache))}[x = z] * (z.1.2.length : ℝ≥0∞))
              ≤ (if oz = none then (1 : ℝ≥0∞) + S else 0) := by
            intro oz
            cases oz with
            | some z =>
                rw [ite_eq_right (by simp), OracleComp.tsum_prEvent_pure_mul]
                simp [List.length]
            | none =>
                rw [ite_eq_left rfl, map_eq_bind_pure_comp, OracleComp.tsum_prEvent_bind_mul]
                calc (∑' z : (Option (Commit × Resp) × List Commit) ×
                      (M × Commit →ₒ Chal).QueryCache,
                    Pr{let x ← (ghostSignDrawBody ids M pk sk msg n).run re}[x = z] *
                      (∑' y : (Option (Commit × Resp) × List Commit) ×
                          (M × Commit →ₒ Chal).QueryCache,
                        Pr{let x ← (pure ((fun rws : (Option (Commit × Resp) × List Commit) ×
                            (M × Commit →ₒ Chal).QueryCache =>
                          ((rws.1.1, ws.1 :: rws.1.2), rws.2)) z) :
                          ProbComp ((Option (Commit × Resp) × List Commit) ×
                            (M × Commit →ₒ Chal).QueryCache))}[x = y] * (y.1.2.length : ℝ≥0∞)))
                    = ∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr{let x ← (ghostSignDrawBody ids M pk sk msg n).run re}[x = z] *
                        (1 + (z.1.2.length : ℝ≥0∞)) := by
                      refine tsum_congr fun z => ?_
                      rw [OracleComp.tsum_prEvent_pure_mul]
                      simp only [List.length_cons]
                      push_cast
                      ring_nf
                  _ = (∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr{let x ← (ghostSignDrawBody ids M pk sk msg n).run re}[x = z]) +
                      ∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr{let x ← (ghostSignDrawBody ids M pk sk msg n).run re}[x = z] *
                        (z.1.2.length : ℝ≥0∞) := by
                      rw [← ENNReal.tsum_add]
                      exact tsum_congr fun z => by rw [mul_add, mul_one]
                  _ ≤ 1 + S := add_le_add (OracleComp.tsum_prEvent_le_one _) (ih re)
          refine le_trans (ENNReal.tsum_le_tsum fun oz =>
            mul_le_mul_right (h_oz oz) _) ?_
          rw [tsum_eq_single (none : Option Resp) fun oz hoz => by
            rw [ite_eq_right hoz, mul_zero]]
          rw [ite_eq_left rfl, mul_comm]
        refine le_trans (ENNReal.tsum_le_tsum fun ch =>
          mul_le_mul_right (h_ch ch) _) ?_
        rw [OracleComp.prEvent_bind_eq_tsum, ← ENNReal.tsum_mul_right]
        exact le_of_eq (tsum_congr fun ch => (mul_assoc _ _ _).symm)
      refine le_trans (ENNReal.tsum_le_tsum fun ws => mul_le_mul_right (h_ws ws) _) ?_
      calc ∑' ws : Commit × PrvState, Pr{let x ← ids.commit pk sk}[x = ws] *
            (Pr{let x ← (uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch)}[x = none] * (1 + S))
          = (∑' ws : Commit × PrvState, Pr{let x ← ids.commit pk sk}[x = ws] *
              Pr{let x ← (uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch)}[x = none]) * (1 + S) := by
            rw [← ENNReal.tsum_mul_right]
            exact tsum_congr fun ws => (mul_assoc _ _ _).symm
        _ ≤ ENNReal.ofReal p_abort * (1 + S) :=
            mul_le_mul_left (tsum_prEvent_commit_mul_abort_le ids pk sk hAbort) _

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
