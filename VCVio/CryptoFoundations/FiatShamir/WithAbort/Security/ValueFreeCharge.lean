/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.FirstMoment

/-!
# EUF-CMA for Fiat-Shamir with aborts: ValueFreeCharge

The two value-free ingredients of the per-pair charge: the atomic charge of one fresh
commitment draw against a list independent of it (`tsum_prEvent_commit_mul_count_le`),
and the invariance of the recorded read list of the deferred draw-and-read run under its
start drawn list (`deferredDrawRead_run_count_dl_invariant`).

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

/-! ### Value-free charge ingredients

A fresh commitment draw contributes at most `ε` per slot of any list independent of it. The
recorded read list of the read-recording run is such a list: its reads answer via `roStep` on
the real layer and never from the drawn (rejected) values, so its law does not depend on the
drawn list. -/

omit [SampleableType Stmt] in
/-- **The atomic value-free charge.** One fresh raw
commitment draw `w ← ids.commit pk sk`, *independent of* a value-free list `rl`, contributes
expected multiplicity `E[rl.count w.1] ≤ ε · rl.length`: each of the `rl.length` slots of `rl` is
hit by the fresh draw with probability `Pr{let x ← Prod.fst <$> ids.commit pk sk}[x = slot] ≤ ε`
(`hGuess`).

This is the single source of the `ε` in the ghost-read bound. It is purely the per-draw mass bound
combined with the independence of the draw from the (value-free) read list; the structural content
of the full charge is to exhibit each recorded rejected draw in exactly this
independent-of-the-read-list position. -/
lemma tsum_prEvent_commit_mul_count_le {C P : Type} [DecidableEq C]
    (commit : ProbComp (C × P)) (rl : List C) (ε : ℝ)
    (hGuess : ∀ cm : C, Pr{let x ← Prod.fst <$> commit}[x = cm] ≤ ENNReal.ofReal ε) :
    (∑' w : C × P, Pr{let x ← commit}[x = w] * (rl.count w.1 : ℝ≥0∞))
      ≤ ENNReal.ofReal ε * (rl.length : ℝ≥0∞) := by
  let : MeasurableSpace C := ⊤
  have h := OracleComp.DeferredSampling.lintegral_count_le commit rl (ENNReal.ofReal ε)
    fun cm => by simpa only [prEvent_map] using hGuess cm
  rwa [lintegral_evalDist_eq_tsum, OracleComp.tsum_prEvent_map_mul] at h

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
          Pr{let x ← ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
              ((((re, sgn), D₁), b₁), rl))}[x = z] * (z.2.2.count w : ℝ≥0∞))
        = ∑' z : γ × DeferredReadState M Commit Chal,
            Pr{let x ← ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
                ((((re, sgn), D₂), b₂), rl))}[x = z] * (z.2.2.count w : ℝ≥0∞) := by
  induction oa using OracleComp.inductionOn generalizing re sgn rl with
  | pure a =>
      intro D₁ b₁ D₂ b₂
      simp only [simulateQ_pure, StateT.run_pure, OracleComp.tsum_prEvent_pure_mul]
  | query_bind t ob ih =>
      intro D₁ b₁ D₂ b₂
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, OracleComp.tsum_prEvent_bind_mul]
      rcases t with (n | mc) | msg
      · -- UNIFORM: drawn list / bad flag / read list untouched; forward draw.
        set G : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
            (Sum.inl (Sum.inl n))) × DeferredReadState M Commit Chal → ℝ≥0∞ :=
          fun x => ∑' z : γ × DeferredReadState M Commit Chal,
            Pr{let y ← (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run
                 x.2}[y = z] *
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
        refine (OracleComp.tsum_prEvent_map_mul _ _ G).trans
          ((tsum_congr fun u => ?_).trans (OracleComp.tsum_prEvent_map_mul _ _ G).symm)
        exact congrArg _ (ih u re sgn rl D₁ b₁ D₂ b₂)
      · -- READ: read list grows by `mc.2` (independent of `D`); the bad flag updates to
        -- `b || (mc.2 ∈ D)` (D-dependent), but `ih` is quantified over *all* bad flags.
        set G : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
            (Sum.inl (Sum.inr mc))) × DeferredReadState M Commit Chal → ℝ≥0∞ :=
          fun x => ∑' z : γ × DeferredReadState M Commit Chal,
            Pr{let y ← (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run
                 x.2}[y = z] *
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
        refine (OracleComp.tsum_prEvent_map_mul _ _ G).trans
          ((tsum_congr fun cu => ?_).trans (OracleComp.tsum_prEvent_map_mul _ _ G).symm)
        exact congrArg _
          (ih cu.1 cu.2 sgn (mc.2 :: rl) D₁ (b₁ || decide (mc.2 ∈ D₁)) D₂
            (b₂ || decide (mc.2 ∈ D₂)))
      · -- SIGN: the body draws are `D`-independent; drawn list grows by the body's rejected
        -- commitments and the bad flag is preserved; `ih` (over all `D`) closes the continuations.
        set G : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
            (Sum.inr msg)) × DeferredReadState M Commit Chal → ℝ≥0∞ :=
          fun x => ∑' z : γ × DeferredReadState M Commit Chal,
            Pr{let y ← (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run
                 x.2}[y = z] *
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
        refine (OracleComp.tsum_prEvent_map_mul _ _ G).trans
          ((tsum_congr fun alc => ?_).trans (OracleComp.tsum_prEvent_map_mul _ _ G).symm)
        exact congrArg _
          (ih alc.1.1 alc.2 (msg :: sgn) rl (D₁ ++ alc.1.2) b₁ (D₂ ++ alc.1.2) b₂)

end scaffold

end EUF_CMA

end FiatShamirWithAbort
