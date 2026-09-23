/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.TapeFactorization

/-!
# EUF-CMA for Fiat-Shamir with aborts: SignStepCharge

The per-signing-step coincidence charges: the constant-length body charge of
`ghostSignDrawBody` (its `succ` step and the continuation form), and the charge of a
non-tape signing step against the read multiplicity of its rejected draws.

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
/-- **One step of the constant-length body charge (the genuine per-attempt induction step).** The
`succ` case of `ghostSignDrawBody_continuation_charge`: peel the head commit draw `ws` (kept
*averaged* — the head `ε`-kernel needs the full `ids.commit` marginal, a per-`ws` bound is false),
the challenge and the response, and case on the accept/reject branch. On *accept* the body records
nothing (charge `0`). On *reject* the recorded rejects are `ws.1 :: rec-rejects`; the
read-multiplicity splits into the head `z.readlist.count ws.1` (paid by the unconditional `+1` via
the value-substituted, gate-dropped marginal `ε`-kernel) and the recursive body charge (the
inductive hypothesis `ih` at the extended start drawn list `dr ++ [ws.1]`). The body never fails, so
the full-mass identities make the head `≤ L₀` match the RHS `+1`. -/
theorem ghostSignDrawBody_succ_charge {γ : Type}
    (qH : ℕ) (ε : ℝ) (_hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (msg : M)
    (ob : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg) →
      OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (hob : ∀ u, (ob u).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH)
    (sgn : List M) (rl : List Commit) (bad : Bool) (n : ℕ)
    (re : (M × Commit →ₒ Chal).QueryCache) (dr : List Commit)
    (ih : ∀ (re : (M × Commit →ₒ Chal).QueryCache) (dr : List Commit),
      (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg n).run re] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                  ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
        ≤ ENNReal.ofReal ε * ((rl.length + qH : ℕ) : ℝ≥0∞) *
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg n).run re] *
              ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞)) :
    (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= alc | (ghostSignDrawBody ids M pk sk msg (n + 1)).run re] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
              ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
      ≤ ENNReal.ofReal ε * ((rl.length + qH : ℕ) : ℝ≥0∞) *
        ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg (n + 1)).run re] *
            ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞) := by
  classical
  set L₀ : ℝ≥0∞ := ENNReal.ofReal ε * ((rl.length + qH : ℕ) : ℝ≥0∞) with hL₀
  -- The continuation run never fails, so its output mass is `1`.
  have hcontMass : ∀ (u : ((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg))
      (cache : (M × Commit →ₒ Chal).QueryCache) (D : List Commit),
      (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob u)).run
            ((((cache, sgn), D), bad), rl)]) = 1 := fun u cache D =>
    tsum_probOutput_eq_one'
      (deferredDrawRead_run_neverFail ids M maxAttempts pk sk (ob u) _)
  -- The signing body never fails, so its output mass is `1`.
  have hbodyMass : ∀ (re' : (M × Commit →ₒ Chal).QueryCache),
      (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= alc | (ghostSignDrawBody ids M pk sk msg n).run re']) = 1 := by
    intro re'
    exact tsum_probOutput_eq_one' (by simp)
  -- Deterministic continuation-readlist bound: every continuation run started at read list `rl`
  -- with read budget `qH` records `≤ rl.length + qH` reads.
  have hlen : ∀ (u : ((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg))
      (cache : (M × Commit →ₒ Chal).QueryCache) (D : List Commit)
      (z' : γ × DeferredReadState M Commit Chal),
      z' ∈ support ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob u)).run
          ((((cache, sgn), D), bad), rl)) →
      (z'.2.2.length : ℝ≥0∞) ≤ ((rl.length + qH : ℕ) : ℝ≥0∞) := by
    intro u cache D z' hz'
    have := deferredDrawReadImpl_run_readlist_length_le ids M maxAttempts pk sk (ob u) qH
      (hob u) ((((cache, sgn), D), bad), rl) z' hz'
    exact_mod_cast this
  -- Per-`ws` value-substituted ungated head charge.
  set H : Commit × PrvState → ℝ≥0∞ := fun ws =>
    ∑' rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
      Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
        ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob rws.1.1)).run
              ((((rws.2, sgn), dr), bad), rl)] * ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞) with hH
  -- Per-`ws` recorded-length factor of the one-attempt body (RHS length factor minus the `+1`).
  set R : Commit × PrvState → ℝ≥0∞ := fun ws =>
    ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
      Pr[= alc | uniformSample Chal >>= fun ch =>
        ids.respond pk sk ws.2 ch >>= fun oz =>
          match oz with
          | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
          | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
              (ghostSignDrawBody ids M pk sk msg n).run re] *
        ((alc.1.2.length : ℕ) : ℝ≥0∞) with hR
  -- The per-`ws` head bound, summed over `ws` (gate dropped, value-substituted, `ε`-kernel).
  have hHead : (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * H ws) ≤ L₀ := by
    rw [hH]
    -- Per `(rws, z)` the inner `ws`-marginal of `z.count ws.1` is `≤ L₀`; the body and continuation
    -- have full mass, so the whole head expectation is `≤ L₀`.
    have hinner : ∀ (rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache)
        (z : γ × DeferredReadState M Commit Chal),
        z ∈ support ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob rws.1.1)).run
            ((((rws.2, sgn), dr), bad), rl)) →
        (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞))
          ≤ L₀ := by
      intro rws z hz
      calc (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
            ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞))
          ≤ ENNReal.ofReal ε * ((z.2.2.length : ℕ) : ℝ≥0∞) :=
            tsum_probOutput_commit_mul_count_le (ids.commit pk sk) z.2.2 ε (fun cm => hGuess cm)
        _ ≤ L₀ := by rw [hL₀]; gcongr; exact_mod_cast hlen rws.1.1 rws.2 dr z hz
    -- Rewrite the head as a single average over `(ws, rws, z)`, reorder, bound, and recombine.
    calc (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
            ∑' rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
              Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
                ∑' z : γ × DeferredReadState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                      (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)] *
                    ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞))
        = ∑' rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)] *
                  (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
                    ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞)) := by
          -- Fully distribute the probability weights, reorder `ws` innermost, recombine.
          simp_rw [← ENNReal.tsum_mul_left]
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun rws => ?_
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun z => ?_
          refine tsum_congr fun ws => by ring
      _ ≤ ∑' rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)] * L₀ := by
          refine ENNReal.tsum_le_tsum fun rws => ?_
          refine mul_le_mul' le_rfl ?_
          refine ENNReal.tsum_le_tsum fun z => ?_
          rcases eq_or_ne Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
              (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)] 0 with hz | hz
          · rw [hz]; simp
          · gcongr
            exact hinner rws z ((mem_support_iff _ _).mpr hz)
      _ = L₀ * ∑' rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)] := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun rws => ?_
          rw [ENNReal.tsum_mul_right, ← mul_assoc, mul_comm _ L₀, mul_assoc]
      _ = L₀ := by
          have hone : (∑' rws : (Option (Commit × Resp) × List Commit) ×
              (M × Commit →ₒ Chal).QueryCache,
              Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
                ∑' z : γ × DeferredReadState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                      (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)]) = 1 := by
            rw [← hbodyMass re]
            exact tsum_congr fun rws => by rw [hcontMass rws.1.1 rws.2 dr, mul_one]
          rw [hone, mul_one]
  -- The per-`ws` LHS inner bound: head + recursive (the inductive hypothesis).
  have h_ws : ∀ ws : Commit × PrvState,
      (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= alc | uniformSample Chal >>= fun ch =>
          ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
            | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                (ghostSignDrawBody ids M pk sk msg n).run re] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
              ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
        ≤ H ws + L₀ * R ws := by
    intro ws
    -- Body-`n` expected `length + 1` (the reject-branch length factor; `+1` is the head commit).
    set Rr : ℝ≥0∞ :=
      ∑' rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
      Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
        ((rws.1.2.length + 1 : ℕ) : ℝ≥0∞) with hRr
    -- `R ws = Pr[reject ws] · Rr` (accept records length `0`; reject records `ws.1 :: rws`).
    have hR_eq : R ws = Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] *
        Rr := by
      rw [hR, probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
      simp only []
      rw [tsum_probOutput_bind_mul]
      refine tsum_congr fun ch => ?_
      rw [tsum_probOutput_bind_mul]
      -- Per response `oz`: accept records length `0`; reject records `(ws.1 :: rws).length`.
      have h_oz : ∀ oz : Option Resp,
          (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (match oz with
              | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
              | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                  (ghostSignDrawBody ids M pk sk msg n).run re :
              ProbComp ((Option (Commit × Resp) × List Commit) ×
                (M × Commit →ₒ Chal).QueryCache))] * ((alc.1.2.length : ℕ) : ℝ≥0∞))
            = (if oz = none then Rr else 0) := by
        intro oz
        cases oz with
        | some z => rw [ite_eq_right (by simp), tsum_probOutput_pure_mul]; simp
        | none =>
            rw [ite_eq_left rfl, hRr, map_eq_bind_pure_comp, tsum_probOutput_bind_mul]
            refine tsum_congr fun rws => ?_
            simp only [Function.comp]
            rw [tsum_probOutput_pure_mul]
            simp [List.length_cons]
      rw [tsum_eq_single (none : Option Resp) fun oz hoz => by
        rw [h_oz oz, ite_eq_right hoz, mul_zero]]
      rw [h_oz none, ite_eq_left rfl]; ring
    -- Peel the challenge `ch`. On *accept* the recorded list is empty (charge `0`); only the
    -- *reject* branch contributes, gated by `Pr[none | respond]`.
    rw [tsum_probOutput_bind_mul]
    -- Per-challenge: peel the response, then case on accept/reject.
    have h_ch : ∀ ch : Chal,
        (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
            | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                (ghostSignDrawBody ids M pk sk msg n).run re] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                  ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
          ≤ Pr[= none | ids.respond pk sk ws.2 ch] * (H ws + L₀ * Rr) := by
      intro ch
      rw [tsum_probOutput_bind_mul]
      -- Per response `oz`: accept records nothing (charge `0`); reject = head + recursion.
      have h_oz : ∀ oz : Option Resp,
          (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (match oz with
              | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
              | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                  (ghostSignDrawBody ids M pk sk msg n).run re :
              ProbComp ((Option (Commit × Resp) × List Commit) ×
                (M × Commit →ₒ Chal).QueryCache))] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                    ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                  ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
            ≤ (if oz = none then H ws + L₀ * Rr else 0) := by
        intro oz
        cases oz with
        | some z =>
            rw [ite_eq_right (by simp), tsum_probOutput_pure_mul]
            simp
        | none =>
            rw [ite_eq_left rfl, map_eq_bind_pure_comp, tsum_probOutput_bind_mul]
            -- The reject branch: split the recorded count list `ws.1 :: rws.1.2` into head + tail.
            have hsplit : ∀ rws : (Option (Commit × Resp) × List Commit) ×
                (M × Commit →ₒ Chal).QueryCache,
                (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
                  Pr[= alc | (pure ((rws.1.1, ws.1 :: rws.1.2), rws.2) :
                    ProbComp ((Option (Commit × Resp) × List Commit) ×
                      (M × Commit →ₒ Chal).QueryCache))] *
                    ∑' z : γ × DeferredReadState M Commit Chal,
                      Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                          (ob alc.1.1)).run ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                        ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
                  = (∑' z : γ × DeferredReadState M Commit Chal,
                        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                            (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)] *
                          ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞))
                    + ∑' z : γ × DeferredReadState M Commit Chal,
                        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                            (ob rws.1.1)).run
                            ((((rws.2, sgn), (dr ++ [ws.1]) ++ rws.1.2), bad), rl)] *
                          ((rws.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞) := by
              intro rws
              rw [tsum_probOutput_pure_mul]
              simp only [List.map_cons, List.sum_cons, Nat.cast_add]
              rw [show dr ++ ws.1 :: rws.1.2 = (dr ++ [ws.1]) ++ rws.1.2 from by simp]
              rw [show (∑' z : γ × DeferredReadState M Commit Chal,
                    Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                        (ob rws.1.1)).run ((((rws.2, sgn), (dr ++ [ws.1]) ++ rws.1.2), bad), rl)] *
                      ((z.2.2.count ws.1 : ℝ≥0∞) +
                        ((rws.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞)))
                  = (∑' z : γ × DeferredReadState M Commit Chal,
                        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                            (ob rws.1.1)).run
                            ((((rws.2, sgn), (dr ++ [ws.1]) ++ rws.1.2), bad), rl)] *
                          ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞))
                    + ∑' z : γ × DeferredReadState M Commit Chal,
                        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                            (ob rws.1.1)).run
                            ((((rws.2, sgn), (dr ++ [ws.1]) ++ rws.1.2), bad), rl)] *
                          ((rws.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞) from by
                rw [← ENNReal.tsum_add]; exact tsum_congr fun z => by rw [mul_add]]
              -- Head: value-substitute the drawn list from `(dr ++ [ws.1]) ++ rws.1.2` to `dr`.
              congr 1
              exact deferredDrawRead_run_count_dl_invariant ids M maxAttempts pk sk (ob rws.1.1)
                ws.1 rws.2 sgn rl ((dr ++ [ws.1]) ++ rws.1.2) bad dr bad
            -- Now `h_oz none` reduces to: `∑'rws Pr[rws]·(head + rec) ≤ H ws + L₀·Rr`.
            simp only [Function.comp]
            simp_rw [hsplit, mul_add]
            rw [ENNReal.tsum_add]
            -- The head sum *is* `H ws`; the recursive sum is bounded by the inductive hypothesis.
            refine add_le_add (le_of_eq ?_) ?_
            · rw [hH]
            · -- `dr ++ [ws.1]` form matches the inductive hypothesis at the extended prefix.
              rw [hRr]
              refine le_trans ?_ (ih re (dr ++ [ws.1]))
              exact le_of_eq (tsum_congr fun x => by rw [List.append_assoc])
      -- Sum over `oz`: only the reject (`none`) term survives, gated by `Pr[none | respond]`.
      calc (∑' oz : Option Resp, Pr[= oz | ids.respond pk sk ws.2 ch] *
              ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
                Pr[= alc | (match oz with
                  | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                  | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                      (ghostSignDrawBody ids M pk sk msg n).run re :
                  ProbComp ((Option (Commit × Resp) × List Commit) ×
                    (M × Commit →ₒ Chal).QueryCache))] *
                  ∑' z : γ × DeferredReadState M Commit Chal,
                    Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                        (ob alc.1.1)).run ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                      ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
          ≤ ∑' oz : Option Resp, Pr[= oz | ids.respond pk sk ws.2 ch] *
              (if oz = none then H ws + L₀ * Rr else 0) :=
            ENNReal.tsum_le_tsum fun oz => by gcongr; exact h_oz oz
        _ = Pr[= none | ids.respond pk sk ws.2 ch] * (H ws + L₀ * Rr) := by
            rw [tsum_eq_single (none : Option Resp) fun oz hoz => by
              rw [ite_eq_right hoz, mul_zero]]
            rw [ite_eq_left rfl]
    -- Sum over `ch`: factor out the reject probability and fold via `hR_eq`.
    calc (∑' ch : Chal, Pr[= ch | uniformSample Chal] *
            ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
              Pr[= alc | ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] *
                ∑' z : γ × DeferredReadState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                      (ob alc.1.1)).run ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                    ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
        ≤ ∑' ch : Chal, Pr[= ch | uniformSample Chal] *
            (Pr[= none | ids.respond pk sk ws.2 ch] * (H ws + L₀ * Rr)) :=
          ENNReal.tsum_le_tsum fun ch => by gcongr; exact h_ch ch
      _ = (∑' ch : Chal, Pr[= ch | uniformSample Chal] *
            Pr[= none | ids.respond pk sk ws.2 ch]) * (H ws + L₀ * Rr) := by
          rw [← ENNReal.tsum_mul_right]; exact tsum_congr fun ch => (mul_assoc _ _ _).symm
      _ = Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] *
            (H ws + L₀ * Rr) := by rw [probOutput_bind_eq_tsum]
      _ ≤ H ws + L₀ * R ws := by
          rw [mul_add, hR_eq]
          refine add_le_add (mul_le_of_le_one_left zero_le probOutput_le_one) ?_
          rw [← mul_assoc, mul_comm
            Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] L₀, mul_assoc]
  -- Assemble: unfold the `succ` body, peel the commit draw, apply `h_ws`, and split the sums.
  rw [run_ghostSignDrawBody_succ, tsum_probOutput_bind_mul]
  rw [tsum_probOutput_bind_mul]
  -- RHS inner equals `R ws + 1` (the body never fails, so the `+1` carries full mass).
  have hRinner : ∀ ws : Commit × PrvState,
      (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= alc | uniformSample Chal >>= fun ch =>
          ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
            | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                (ghostSignDrawBody ids M pk sk msg n).run re] *
          ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞))
        = R ws + 1 := by
    intro ws
    have hmass : (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= alc | uniformSample Chal >>= fun ch =>
          ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
            | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                (ghostSignDrawBody ids M pk sk msg n).run re]) = 1 :=
      tsum_probOutput_eq_one' (by simp)
    rw [hR]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | uniformSample Chal >>= fun ch =>
            ids.respond pk sk ws.2 ch >>= fun oz =>
              match oz with
              | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
              | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                  (ghostSignDrawBody ids M pk sk msg n).run re] *
            ((alc.1.2.length : ℝ≥0∞) + 1))
        = (∑' alc, Pr[= alc | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] * (alc.1.2.length : ℝ≥0∞))
          + ∑' alc, Pr[= alc | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] from by
      rw [← ENNReal.tsum_add]; exact tsum_congr fun alc => by rw [mul_add, mul_one]]
    rw [hmass]
  calc (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob alc.1.1)).run ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                  ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
        ≤ ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * (H ws + L₀ * R ws) :=
          ENNReal.tsum_le_tsum fun ws => by gcongr; exact h_ws ws
      _ = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * H ws)
            + ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * (L₀ * R ws) := by
          rw [← ENNReal.tsum_add]; exact tsum_congr fun ws => by rw [mul_add]
      _ ≤ L₀ + ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * (L₀ * R ws) := by
          gcongr
      _ = L₀ * ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
            ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
              Pr[= alc | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch >>= fun oz =>
                  match oz with
                  | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                  | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                      (ghostSignDrawBody ids M pk sk msg n).run re] *
                ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞) := by
          have hcommitMass : (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk]) = 1 :=
            tsum_probOutput_eq_one' (by simp)
          simp_rw [hRinner, mul_add, mul_one]
          rw [ENNReal.tsum_add, hcommitMass, mul_add, mul_one]
          rw [show (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * (L₀ * R ws))
              = L₀ * ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * R ws from by
            rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun ws => by ring]
          rw [add_comm]

omit [SampleableType Stmt] in
/-- **The constant-length body charge (the genuine per-attempt induction).** Over one signing body
`ghostSignDrawBody n`, the expected continuation read-multiplicity of the body's *rejected* draws —
`E[Σ_{w ∈ body-rejects} continuation.readlist.count w]` — is at most `ε · (rl.length + qH) ·
E[#body-rejects + 1]`, where `rl` is the continuation's start read list and `qH` the continuation's
read-query budget (so the continuation's recorded read list has length `≤ rl.length + qH`
deterministically). The `+1` is the body's single unconditional signing query; it is *not* slack —
it pays the reject-gate skew of the head charge (see below).

Proved by induction on `n`:
* **0** — the body rejects nothing, the read-multiplicity is `0 ≤ ε · (rl.length + qH) · 1`.
* **n+1** — peel the head commit draw `ws` (kept *averaged*: the `ε`-kernel needs the full
  `ids.commit` marginal — a per-`ws` bound is false, the adversary could target a fixed `ws.1`),
  the challenge, the response, and case on the accept/reject branch. On *accept* the body records
  nothing (`rej = []`, charge `0`). On *reject* the recorded rejects are `ws.1 :: rec-rejects`; the
  read-multiplicity `Σ_{w ∈ ws.1 :: rec-rejects} z'.readlist.count w` splits as
  `z'.readlist.count ws.1` (head) plus the recursive body charge (recurses to the inductive
  hypothesis at the extended start drawn list `dr ++ [ws.1]`).

  Crucially the two halves treat the reject gate `1[respond = none]` differently:
  * the **head** charge `Σ_{ws} commit(ws) · 1[reject(ws.2)] · z'.readlist.count ws.1` drops the
    gate (`1[reject] ≤ 1`) — necessary because `ws.1` and the reject decision `f(ws.2, c)` are
    *correlated* (the prover state `ws.2` determines both the commit and the accept decision), so a
    gated kernel would skew the `ws.1` marginal. After value-substitution
    (`deferredDrawRead_run_sum_count_dl_invariant` moves `ws.1` out of the continuation's drawn
    list) and the marginal `ε`-kernel `tsum_probOutput_commit_mul_count_le`, the ungated head is
    `≤ ε · z'.readlist.length ≤ ε · (rl.length + qH)`, paid by the unconditional `+1`;
  * the **recursive** charge `Σ_{ws} commit(ws) · 1[reject(ws.2)] · (rec body charge)` *keeps* the
    gate, so it is `Pr[reject] · ε · (rl.length + qH) · E[#rec-rejects + 1]` (inductive hypothesis),
    which the reject paths of `#body-rejects` in the right-hand side exactly cover. Dropping the
    recursive gate would be unsound (it over-charges by the accept mass). -/
theorem ghostSignDrawBody_continuation_charge {γ : Type}
    (qH : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (msg : M)
    (ob : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg) →
      OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (hob : ∀ u, (ob u).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH)
    (sgn : List M) (rl : List Commit) (bad : Bool) :
    ∀ (n : ℕ) (re : (M × Commit →ₒ Chal).QueryCache) (dr : List Commit),
      (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg n).run re] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                  ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
        ≤ ENNReal.ofReal ε * ((rl.length + qH : ℕ) : ℝ≥0∞) *
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg n).run re] *
              ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞) := by
  classical
  intro n
  induction n with
  | zero =>
      intro re dr
      simp only [ghostSignDrawBody, StateT.run_pure, tsum_probOutput_pure_mul, List.map_nil,
        List.sum_nil, Nat.cast_zero, mul_zero, tsum_zero]
      exact zero_le
  | succ n ih =>
      intro re dr
      -- The genuine per-attempt step; see `ghostSignDrawBody_succ_charge`.
      exact ghostSignDrawBody_succ_charge ids M maxAttempts qH ε hε pk sk hGuess msg ob hob sgn rl
        bad n re dr ih


omit [SampleableType Stmt] in
/-- **The sign-step value-free charge — the probabilistic core of the ghost-read bound.**
This is the single-query step of the inline-run induction
`readRecord_expected_pairs_nontape_general` at a *signing* query `Sum.inr msg`. The signing body
`ghostSignDrawBody` draws `maxAttempts` fresh commitments inline, records the *rejected* ones into
the drawn list, and runs the continuation `ob` from the post-body state; the goal bounds the
resulting expected pair count by the `s`-based pre-existing term plus `ε` times the `s`-based
new-attempt count.

The genuine content is concentrated here. Expanding the inductive hypothesis at the post-body state,
the only term not covered by the `s`-based pre-existing term and the slack of the `#attempt` count
is the **body charge** `E[Σ_{rc ∈ readlist} body-rejects.count rc]`, which must be bounded by
`ε · E[readlist.length · #body-attempts]` (where `#body-attempts = #body-rejects + 1`, the body's
single unconditional signing query providing the `+1`). Crucially the body's draws must remain
**averaged** (the sum over body outputs is retained, not factored): for a *fixed* body output the
recorded rejected commitment is a determined value, and a continuation adversary could read the
random oracle at exactly that value, so the per-output charge is not `≤ ε`. The `ε` arises only by
averaging each rejected commitment over the fresh `ids.commit pk sk` draw
(`tsum_probOutput_commit_mul_count_le`).

The charge is sound because the recorded read list is *value-free*: the continuation's
reads answer via `roStep` on the real layer and never the drawn (rejected) values, and the rejected
commitments are write-only (never cached; only accepted commitments are, via `cacheQuery`). The
value-substitution lemma `deferredDrawRead_run_count_dl_invariant` makes this precise: the
continuation's expected `readlist.count w` is invariant under the start drawn list, so the read list
is independent of every rejected draw's *value*. Combined with the body's draws being independent of
*reach* (a position is reached iff the earlier attempts rejected, which is determined by the earlier
draws — the body tape factorization `evalSPMF_ghostSignDrawBody_eq_drawList_tapeSignBody` exhibits
this), each rejected draw charges its continuation read-multiplicity at the full marginal
`Pr[· | Prod.fst <$> commit] ≤ ε` (drop the reject indicator `≤ 1` on the value-substituted, hence
fixed, read list — no rejection-conditioning skew). The body's single unconditional signing query
(`+1`) pays the full-marginal head charge, and the read list `⊥` the attempt count factors
`E[readlist.length · #attempts] = E[readlist.length] · E[#attempts]`.

**Proof.** Unfold the sign step (`deferredDrawReadImpl … (Sum.inr msg)`), which maps each
signing-body output `alc` to the post-state with drawn list `s.drawn ++ alc.1.2` and signed list
`msg :: s.signed`. The continuation charge from the post-body state is bounded per `alc` by the
inductive hypothesis `ih`; its pre-existing drawn count splits via `List.count_append` into the
start drawn count (matched against the right-hand side) and the *body coincidence*
`E[Σ_{rc ∈ readlist} alc.1.2.count rc]`, which the bilinear count swap `sum_map_count_comm` recasts
as `E[Σ_{w ∈ alc.1.2} readlist.count w]` and `ghostSignDrawBody_continuation_charge` bounds by
`ε · (rl.length + qH) · E[#attempts + 1]`. The slack length factor recombines via the deterministic
prefix monotonicities `deferredDrawRead_run_drawn_prefix` / `deferredDrawRead_run_signed_prefix`:
the gap between the start slack and the post-body slack is exactly `alc.1.2.length + 1` (the body's
rejected draws plus the single signing query), which the body's `+1` term covers. The continuation
run's full mass (`deferredDrawRead_run_neverFail`) makes the constant-length factor `L₀` exact. -/
theorem nontape_signStep_charge {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (_hp₀ : 0 ≤ p_abort) (_hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (_hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (msg : M)
    (ob : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg) →
      OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (s : DeferredReadState M Commit Chal)
    (hob : ∀ u, (ob u).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH)
    (ih : ∀ (u : ((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg))
        (s' : DeferredReadState M Commit Chal),
        (ob u).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH →
        (∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob u)).run s'] *
              ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
          ≤ (∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob u)).run s'] *
                ((z.2.2.map (fun rc => s'.1.1.2.count rc)).sum : ℝ≥0∞))
            + ENNReal.ofReal ε * ((s'.2.length + qH : ℕ) : ℝ≥0∞) *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob u)).run s'] *
                  (((z.2.1.1.2.length - s'.1.1.2.length)
                    + (z.2.1.1.1.2.length - s'.1.1.1.2.length) : ℕ) : ℝ≥0∞)) :
    (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ ∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        ((Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z |
                  (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                ((z.2.2.map (fun rc => s.1.1.2.count rc)).sum : ℝ≥0∞))
          + ENNReal.ofReal ε * ((s.2.length + qH : ℕ) : ℝ≥0∞) *
            (Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z |
                    (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                  (((z.2.1.1.2.length - s.1.1.2.length)
                    + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞))) := by
  classical
  set L₀ : ℝ≥0∞ := ENNReal.ofReal ε * ((s.2.length + qH : ℕ) : ℝ≥0∞) with hL₀
  -- Unfold the sign step: it maps each signing-body output `alc` to the post-state with drawn list
  -- `s.drawn ++ alc.1.2` and signed list `msg :: s.signed`. Convert all three sign-step averages to
  -- averages over the signing-body output `alc`.
  have hLHS : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      = ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                  (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2),
                    s.2)] *
                ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞) :=
    tsum_probOutput_map_mul _ _ _
  have hRHS1 : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              ((z.2.2.map (fun rc => s.1.1.2.count rc)).sum : ℝ≥0∞))
      = ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                  (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2),
                    s.2)] *
                ((z.2.2.map (fun rc => s.1.1.2.count rc)).sum : ℝ≥0∞) :=
    tsum_probOutput_map_mul _ _ _
  have hRHS2 : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        L₀ * (Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              (((z.2.1.1.2.length - s.1.1.2.length)
                + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞)))
      = L₀ * ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                  (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2),
                    s.2)] *
                (((z.2.1.1.2.length - s.1.1.2.length)
                  + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞) := by
    rw [ENNReal.tsum_mul_left]; exact congrArg (L₀ * ·) (tsum_probOutput_map_mul _ _ _)
  -- Rewrite all three sums to body averages; the RHS is `(pre-existing) + L₀ · (slack)`.
  rw [hLHS]
  rw [ENNReal.tsum_add]
  conv_rhs => rw [show (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        ENNReal.ofReal ε * ((s.2.length + qH : ℕ) : ℝ≥0∞) *
          (Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z |
                  (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                (((z.2.1.1.2.length - s.1.1.2.length)
                  + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞)))
      = ∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        L₀ * (Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z |
                (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              (((z.2.1.1.2.length - s.1.1.2.length)
                + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞)) from
    tsum_congr fun x => by rw [hL₀]]
  rw [hRHS1, hRHS2]
  -- Both sides are now body averages; bound the LHS per `alc` by the inductive hypothesis at the
  -- post-body state, splitting the pre-existing drawn count and applying induction (1) to the body
  -- coincidence and the slack length identities.
  -- The body-coincidence charge `E_alc[E_z[Σ_{rc∈readlist} alc.1.2.count rc]]` is bounded by
  -- induction (1) (after the bilinear count swap `sum_map_count_comm`).
  have hbody : (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
      Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
        ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
              ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
            ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
      ≤ L₀ * ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
            ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞) := by
    rw [hL₀]
    exact ghostSignDrawBody_continuation_charge ids M maxAttempts qH ε hε pk sk hGuess msg ob
      (fun u => hob u) (msg :: s.1.1.1.2) s.2 s.1.2 maxAttempts s.1.1.1.1 s.1.1.2
  -- The continuation runs never fail, so their mass is `1`.
  have hcontMass : ∀ alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
      (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
            ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)]) = 1 := fun alc =>
    tsum_probOutput_eq_one' (deferredDrawRead_run_neverFail ids M maxAttempts pk sk (ob alc.1.1) _)
  -- Per `alc`: split the pre-existing drawn count and rewrite the slack via the prefix lemmas.
  -- The slack inner sum splits as the post-body inductive slack plus the body's `#attempts + 1`.
  have hslack : ∀ (alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache),
      (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
            ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
          (((z.2.1.1.2.length - s.1.1.2.length)
            + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞))
      = (∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
              ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
            (((z.2.1.1.2.length - (s.1.1.2 ++ alc.1.2).length)
              + (z.2.1.1.1.2.length - (msg :: s.1.1.1.2).length) : ℕ) : ℝ≥0∞))
        + ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞) := by
    intro alc
    rw [show ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞)
        = (∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)]) *
            ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞) from by rw [hcontMass alc, one_mul]]
    rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
    refine tsum_congr fun z => ?_
    by_cases hz : z ∈ support ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
        (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))
    · have hdr := deferredDrawRead_run_drawn_prefix ids M maxAttempts pk sk (ob alc.1.1)
        ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2) z hz
      have hsg := deferredDrawRead_run_signed_prefix ids M maxAttempts pk sk (ob alc.1.1)
        ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2) z hz
      simp only at hdr hsg
      rw [← mul_add]
      congr 1
      rw [← Nat.cast_add]
      congr 1
      simp only [List.length_append, List.length_cons] at hdr hsg ⊢
      omega
    · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul, zero_mul, add_zero]
  -- Per `alc`: the inductive hypothesis at the post-body state, with the pre-existing drawn count
  -- split into the start drawn count and the body coincidence (the bilinear count swap).
  have h_alc : ∀ (alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache),
      (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
            ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ (∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
              ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
            ((z.2.2.map (fun rc => s.1.1.2.count rc)).sum : ℝ≥0∞))
        + (∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
              ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
          + L₀ * ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                  ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
                (((z.2.1.1.2.length - (s.1.1.2 ++ alc.1.2).length)
                  + (z.2.1.1.1.2.length - (msg :: s.1.1.1.2).length) : ℕ) : ℝ≥0∞) := by
    intro alc
    have hih := ih alc.1.1 ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)
      (hob alc.1.1)
    -- The post-state read list is `s.2`, so the read-length factor is `L₀`.
    simp only [hL₀.symm] at hih ⊢
    refine le_trans hih (le_of_eq ?_)
    congr 1
    -- Pre-existing drawn count `(s.drawn ++ alc.1.2).count` splits into `s.drawn.count` plus the
    -- body coincidence (via the bilinear count swap).
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun z => ?_
    rw [← mul_add]
    congr 1
    rw [← Nat.cast_add]
    congr 1
    rw [show (z.2.2.map (fun rc => (s.1.1.2 ++ alc.1.2).count rc))
        = z.2.2.map (fun rc => s.1.1.2.count rc + alc.1.2.count rc) from
      List.map_congr_left fun rc _ => by rw [List.count_append]]
    rw [List.sum_map_add, sum_map_count_comm alc.1.2 z.2.2]
  -- Assemble: sum the per-`alc` bound, split into pre-existing + body-coincidence + ih-slack, then
  -- recombine the slack via `hslack` (the `#attempts + 1` gap) and the coincidence via `hbody`.
  refine le_trans (ENNReal.tsum_le_tsum fun alc => mul_le_mul' le_rfl (h_alc alc)) ?_
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_add, add_assoc]
  refine add_le_add le_rfl ?_
  -- The body coincidence plus the post-body inductive slack equal `L₀ · (the full RHS slack)`.
  have hslackSum :
      L₀ * ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
            ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞)
        + (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              (L₀ * ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2),
                      s.2)] *
                  (((z.2.1.1.2.length - (s.1.1.2 ++ alc.1.2).length)
                    + (z.2.1.1.1.2.length - (msg :: s.1.1.1.2).length) : ℕ) : ℝ≥0∞)))
      = L₀ * ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                  (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2),
                    s.2)] *
                (((z.2.1.1.2.length - s.1.1.2.length)
                  + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    refine tsum_congr fun alc => ?_
    rw [hslack alc, mul_add, add_comm]
    ring
  rw [← hslackSum]
  exact add_le_add hbody le_rfl

end scaffold

end EUF_CMA

end FiatShamirWithAbort
