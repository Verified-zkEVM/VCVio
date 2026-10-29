/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.Bad
public import VCVio.CryptoFoundations.TimeLockPuzzle.Truncate

/-!
# The delay theorem of the pointer-chain puzzle

This file proves the delay theorem of the pointer-chain puzzle (`scheme`) over independent typed
random oracles: the leanSeal paper's Theorem `thm:delay`. Write
`P = solvePoints n m = n (m + 3) + 1` and `T_key = keyRound n m = n (m + 2) + 1`. For injective
`mkCtx`, finite `Ctx`, and an adversary with at most `Q_pre` preprocessing queries and at most
`Q_on` online point queries, the probability that the online phase outputs the key within fewer
than `T_key` completed rounds is at most

```
[n ≥ 2] Q_on / |L| + Q_pre / (|Salt| |L|) + ((Q_pre + Q_on) P + P² + 1) / |S|
```

(`delayAdvantageWithin_scheme_le`, with no bound on the rounds of the adversary;
`delayAdvantage_scheme_le` and `delaySecure_scheme` for an adversary within `T_key - 1` rounds).
With the paper's sizes `|S| = 2^256`, `|L| = 2^(8b)` and `|Salt| = 2^128` this is
`[n ≥ 2] Q_on / 2^(8b) + Q_pre / 2^(128 + 8b) + (Q P + P² + 1) / 2^256` with `Q = Q_pre + Q_on`
(`bound_eq_paper_of_card`, `delayAdvantageWithin_scheme_le_paper`, `delaySecure_scheme_paper`).

## The final guess

The step proved here is the conclusion of the paper's proof: in the ideal experiment
(`idealExperiment`), an online phase within fewer than `T_key` rounds outputs the key label with
probability at most `1 / |S|` (`prEvent_idealExperiment_win_le`). The proof follows the resampling
route of `Bad.lean` rather than a lazy-label experiment. The ideal handler reads the label of a
path value only when it answers a legitimate point for it, and it reads the labels of the
predecessors of a path value only to test legitimacy for it against the reached set. The key is a
predecessor only of the commitment, which is never legitimate while the key is unreached, and by
Claim 1 the key is never reached, nor a candidate for being reached, within fewer than `T_key`
rounds. So the run of the online phase does not depend on the key label
(`simulateQ_idealImpl_run_congr_of_ne_key`), and neither does the puzzle, which carries only the
commitment label. Redrawing the key label alone (`prEvent_uniform_bind_le_of_update`) then
leaves the output of the online phase fixed while the key label is uniform.

## Any output, several guesses

The final guess and the delay theorem hold for an online phase with outputs of any type and any
event `E` of the output and the key (`prEvent_idealOutcomeExperiment_le_of_forall`,
`prEvent_guessExperiment_scheme_le_of_forall`), with the last term `1 / |S|` replaced by any `ε`
bounding the probability of `E out u` for each output `out` and a uniform `u`. For an online phase
that outputs `q` guesses (`Fin q → S`) and the event that one of them is the key, the union bound
gives `ε = q / |S|` (`prEvent_idealOutcomeExperiment_mem_le`, `prEvent_guessExperiment_scheme_le`).
The delay statements of the table are the cases of these for the event that the output is the key.

## Paper citation table

The leanSeal paper's statement and the steps of its proof (Appendix A), with the declarations that
formalize them.

| Paper | Declaration |
| --- | --- |
| `thm:delay` | `delayAdvantageWithin_scheme_le` |
| `thm:delay`, paper's constants | `delayAdvantageWithin_scheme_le_paper` |
| `thm:delay`, paper's constants, within the rounds | `delaySecure_scheme_paper` |
| `thm:delay`, within the rounds | `delayAdvantage_scheme_le`, `delaySecure_scheme` |
| `thm:delay`, leanSeal's bytes (SPEC §8) | `LeanSeal.delayAdvantageWithin_byteScheme_le` |
| Claim 1 (`claim:sequential`) | `rho_le_round_of_mem_support` |
| Claim 1, the key | `key_not_mem_reached_of_isOnlineQueryBound` |
| Claim 2 (`claim:hybrid`), links | `delayAdvantage_maskedScheme` |
| Claim 2, programming (path-input) | `delayAdvantage_maskedScheme_le`, `realRest_eq_of_not_bad` |
| Claim 2, until Bad (path-input) | `dominatedUntilBad_idealImpl` |
| Claim 2, the comparison (path-input) | `delayAdvantage_scheme_le_idealExperiment` |
| Claim 3 (`claim:bad`) (path-input) | `prEvent_idealExperiment_bad_le` |
| Conclusion | `prEvent_idealExperiment_win_le` |

The formal generator's `Bad` (`Bad`) is not the paper's Bad: its collision case asks for two
distinct path values with equal path inputs, while the paper's Bad (a) asks for two path values
with equal labels. Equal labels need not give equal path inputs (with `n = m = 1`, the key and the
commitment may share a label without `Bad`), so `prEvent_idealExperiment_bad_le` does not bound the
paper's event. The rows marked "path-input" state Claims 2 and 3 for the formal event. The
comparison of Claim 2 needs only that distinct path values are programmed at distinct oracle
inputs, so the formal proof bounds this event directly, and the final bound is the paper's.

Claim 3 splits into the generator's `Bad` (`prEvent_seed_bad_le`) and online Bad
(`prEvent_idealExperiment_onlineBad_le`). The per-run event of `thm:delay`, with no bound on the
rounds, reduces to delay security at `keyRound n m - 1` rounds through the truncated adversary
(`TimeLockPuzzle.delayAdvantageWithin_le_of_delaySecure`).
-/

public section

open OracleSpec OracleComp
open scoped ENNReal

namespace PointerChainPuzzle

variable {n m : ℕ} {S L Salt Ctx : Type}

/-! ## Redrawing one label -/

/-- **One label, after a computation.** An event of a computation run on a uniform labelling has
probability at most `ε` if, for every labelling, redrawing the label of `a` alone gives it
probability at most `ε`. -/
lemma prEvent_uniform_bind_le_of_update [SampleableType S] [SampleableType L] (a : PathValue n m)
    (f : Labels n m S L → ProbComp Prop) {ε : ℝ≥0∞}
    (h : ∀ ℓ, prEvent ($ᵗ (a.Val S L) >>= fun u => f (Function.update ℓ a u)) ≤ ε) :
    prEvent ($ᵗ Labels n m S L >>= f) ≤ ε := by
  let : ∀ v : PathValue n m, MeasurableSpace (v.Val S L) := fun _ => ⊤
  have h₁ := evalDist_bind_bind_update_dependent a ($ᵗ (a.Val S L)) ($ᵗ Labels n m S L)
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample f
  rw [prEvent_def, ← h₁, ← prEvent_def, prEvent_bind_swap]
  exact prEvent_bind_le h

/-! ## The online phase does not read the key label -/

section Key

variable {mkCtx : Salt → Ctx} {initAcc : Ctx → S} [NeZero n] [AddCommGroup L]
  [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx] {P : Puzzle n S L Salt}

/-- A round submitted from a state satisfying the invariant of Claim 1 with the round counter at
most `keyRound n m - 2` neither starts with the key reached nor reaches it. -/
lemma key_not_mem_reached_union_newlyReached {s : IdealState n m S L Salt Ctx}
    (hs : s.RhoBounded) (hr : s.round + 1 < keyRound n m) (ℓ : Labels n m S L)
    (ts : List (Point n S L Salt Ctx)) :
    PathValue.key ∉ s.reached ∪ newlyReached m mkCtx initAcc P ℓ s.reached ts := by
  intro hv
  rcases Finset.mem_union.mp hv with hv | hv
  · have := hs _ hv
    rw [PathValue.rho_key] at this
    omega
  · rw [mem_newlyReached] at hv
    have := PathValue.rho_le_succ_of_preds (k := s.round) fun w hw => hs w (hv.1 hw)
    rw [PathValue.rho_key] at this
    omega

/-- **The key label is not read.** An online phase with at most `r` rounds, run under the ideal
handler from a state satisfying the invariant of Claim 1 whose round counter plus `r` is below
`keyRound n m`, runs alike under two labellings that differ only at the key. Each round reads only
the labels of the reached set and of the path values it reaches (`idealImpl_inr_run_congr`), and
by Claim 1 the key is neither. -/
theorem simulateQ_idealImpl_run_congr_of_ne_key [SampleableType S] [SampleableType L] {α : Type}
    {oa : OracleComp (unifSpec + (oracleSpec n S L Salt Ctx).batch) α} {r q : ℕ}
    (h : IsOnlineQueryBound oa (r, q)) {ℓ₁ ℓ₂ : Labels n m S L}
    (hℓ : ∀ v, v ≠ .key → ℓ₁ v = ℓ₂ v) {s : IdealState n m S L Salt Ctx}
    (hs : s.RhoBounded) (hr : s.round + r < keyRound n m) :
    (simulateQ (idealImpl m mkCtx initAcc P ℓ₁) oa).run s =
      (simulateQ (idealImpl m mkCtx initAcc P ℓ₂) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing r q s with
  | pure a => simp
  | query_bind t f ih =>
      obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).mp h
      rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
      rcases t with k | ts
      · simp only [idealImpl_inl_run, bind_map_left]
        exact bind_congr fun u => ih u (by simpa using hk u) hs hr
      · obtain ⟨hr₁, -⟩ := ht
        have hkey : ∀ v ∈ s.reached ∪ newlyReached m mkCtx initAcc P ℓ₁ s.reached ts,
            ℓ₁ v = ℓ₂ v := by
          refine fun v hv => hℓ v ?_
          rintro rfl
          exact key_not_mem_reached_union_newlyReached hs (by omega) ℓ₁ ts hv
        rw [← idealImpl_inr_run_congr hkey, idealImpl_inr_run]
        simp only [bind_map_left]
        refine bind_congr fun z => ih _ (hk z.1) (hs.afterRound ts z.2) ?_
        simp only [IdealState.afterRound_round]
        omega

end Key

/-! ## The final guess -/

section OutcomeExperiment

variable [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
  [SampleableType S] [SampleableType L] [SampleableType Salt]
  {m : ℕ} {mkCtx : Salt → Ctx} {initAcc : Ctx → S} [NeZero n] [AddCommGroup L]

/-- **The final guess, for any event.** If the online phase of the adversary, with outputs of any
type, submits at most `r < keyRound n m` rounds, then an event `E` of its output and the key label
holds in the ideal experiment with probability at most `ε`, for every `ε` bounding the probability
of `E out u` for each output `out` and a uniform `u`. The key is never reached (Claim 1), so the
run of the online phase and the puzzle do not depend on the key label
(`simulateQ_idealImpl_run_congr_of_ne_key`), and redrawing the key label alone
(`prEvent_uniform_bind_le_of_update`) leaves the output fixed while the key label is uniform. -/
theorem prEvent_idealOutcomeExperiment_le_of_forall {Out : Type}
    {adv : TimeLockPuzzle.TwoPhaseAdversary unifSpec (oracleSpec n S L Salt Ctx)
      (Puzzle n S L Salt) Out} {E : Out → S → Prop} {ε : ℝ≥0∞} {r q : ℕ}
    (hbound : ∀ σ P, IsOnlineQueryBound (adv.online σ P) (r, q)) (hr : r < keyRound n m)
    (hE : ∀ out, Pr{let u ← $ᵗ S}[E out u] ≤ ε) :
    Pr{let res ← idealOutcomeExperiment adv m mkCtx initAcc}[E res.out res.key] ≤ ε := by
  rw [idealOutcomeExperiment, map_bind]
  refine prEvent_seedOf_bind_le fun z _ => prEvent_bind_le fun salt => prEvent_bind_le fun p => ?_
  simp only [idealOutcomeRest, Functor.map_map, Seed.puzzle]
  refine prEvent_uniform_bind_le_of_update .key _ fun ℓ => ?_
  have hP : ∀ u : S, labelPuzzle salt p.1 p.2 (Function.update ℓ .key u) =
      labelPuzzle salt p.1 p.2 ℓ := fun u => by
    simp [labelPuzzle]
  have hrun : ∀ u : S, (simulateQ (idealImpl m mkCtx initAcc (labelPuzzle salt p.1 p.2 ℓ)
      (Function.update ℓ .key u)) (adv.online z.1 (labelPuzzle salt p.1 p.2 ℓ))).run
        (IdealState.init z.2) =
      (simulateQ (idealImpl m mkCtx initAcc (labelPuzzle salt p.1 p.2 ℓ) ℓ)
        (adv.online z.1 (labelPuzzle salt p.1 p.2 ℓ))).run (IdealState.init z.2) := fun u =>
    simulateQ_idealImpl_run_congr_of_ne_key (hbound _ _)
      (fun v hv => Function.update_of_ne hv _ _) (IdealState.rhoBounded_init _) (by simpa using hr)
  simp only [hP, hrun, Function.update_self]
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  rw [prEvent_bind_swap]
  refine prEvent_bind_le fun w => le_of_eq_of_le ?_ (hE w.1)
  simp only [map_eq_bind_pure_comp, Function.comp_def]

/-- **The final guess with `q` guesses.** If the online phase of the adversary outputs `q` guesses
within at most `r < keyRound n m` rounds, one of them is the key label in the ideal experiment with
probability at most `q / |S|`. -/
theorem prEvent_idealOutcomeExperiment_mem_le [Fintype S] {q r b : ℕ}
    {adv : TimeLockPuzzle.TwoPhaseAdversary unifSpec (oracleSpec n S L Salt Ctx)
      (Puzzle n S L Salt) (Fin q → S)}
    (hbound : ∀ σ P, IsOnlineQueryBound (adv.online σ P) (r, b)) (hr : r < keyRound n m) :
    Pr{let res ← idealOutcomeExperiment adv m mkCtx initAcc}[∃ i, res.out i = res.key] ≤
      q / Fintype.card S :=
  prEvent_idealOutcomeExperiment_le_of_forall hbound hr
    SampleableType.prEvent_uniformSample_exists_eq_le

/-- **The delay theorem for any event.** For injective `mkCtx` and an adversary with outputs of
any type, at most `Q_pre` preprocessing queries and an online phase within `keyRound n m - 1`
rounds holding at most `Q_on` points, an event `E` of the output and the key in the delay
experiment (`TimeLockPuzzle.guessExperiment`) has probability at most
`[n ≥ 2] Q_on / |L| + Q_pre / (|Salt| |L|) + ((Q_pre + Q_on) P + P²) / |S| + ε`, with
`P = solvePoints n m`, for every `ε` bounding the probability of `E out u` for each output `out`
and a uniform `u`. The proof adds the final guess
(`prEvent_idealOutcomeExperiment_le_of_forall`) to Claim 3
(`prEvent_idealOutcomeExperiment_bad_le`) through the comparison with the ideal experiment
(`prEvent_guessExperiment_scheme_le_idealOutcomeExperiment`). -/
theorem prEvent_guessExperiment_scheme_le_of_forall [Finite Ctx] [Fintype S] [Fintype L]
    [Fintype Salt] (hctx : Function.Injective mkCtx) {Out : Type}
    {adv : TimeLockPuzzle.TwoPhaseAdversary unifSpec (oracleSpec n S L Salt Ctx)
      (Puzzle n S L Salt) Out} {Qpre Qon : ℕ}
    (hadv : adv.IsQueryBound Qpre (keyRound n m - 1, Qon)) {E : Out → S → Prop} {ε : ℝ≥0∞}
    (hE : ∀ out, Pr{let u ← $ᵗ S}[E out u] ≤ ε) :
    Pr{let z ← (simulateQ (oracleSpec n S L Salt Ctx).romImpl
        ((scheme n m mkCtx initAcc).guessExperiment adv)).run' ∅}[E z.1 z.2] ≤
      (if 2 ≤ n then (Qon : ℝ≥0∞) / Fintype.card L else 0) +
        Qpre / (Fintype.card Salt * Fintype.card L) +
          ((Qpre + Qon) * solvePoints n m + (solvePoints n m : ℝ≥0∞) ^ 2) / Fintype.card S +
        ε := by
  have hr : keyRound n m - 1 < keyRound n m := by
    simp only [keyRound]
    omega
  refine (prEvent_guessExperiment_scheme_le_idealOutcomeExperiment adv m mkCtx initAcc E).trans ?_
  rw [add_comm]
  exact add_le_add (prEvent_idealOutcomeExperiment_bad_le hctx hadv)
    (prEvent_idealOutcomeExperiment_le_of_forall hadv.2 hr hE)

/-- **The delay theorem with `q` guesses.** For injective `mkCtx` and an adversary whose online
phase outputs `q` guesses, with at most `Q_pre` preprocessing queries and an online phase within
`keyRound n m - 1` rounds holding at most `Q_on` points, the probability that one of the guesses is
the key is at most
`[n ≥ 2] Q_on / |L| + Q_pre / (|Salt| |L|) + ((Q_pre + Q_on) P + P² + q) / |S|`, with
`P = solvePoints n m`: the bound of `delayAdvantage_scheme_le` with its last term `1` replaced by
`q`. -/
theorem prEvent_guessExperiment_scheme_le [Finite Ctx] [Fintype S] [Fintype L] [Fintype Salt]
    (hctx : Function.Injective mkCtx) {Qpre Qon q : ℕ}
    {adv : TimeLockPuzzle.TwoPhaseAdversary unifSpec (oracleSpec n S L Salt Ctx)
      (Puzzle n S L Salt) (Fin q → S)}
    (hadv : adv.IsQueryBound Qpre (keyRound n m - 1, Qon)) :
    Pr{let z ← (simulateQ (oracleSpec n S L Salt Ctx).romImpl
        ((scheme n m mkCtx initAcc).guessExperiment adv)).run' ∅}[∃ i, z.1 i = z.2] ≤
      (if 2 ≤ n then (Qon : ℝ≥0∞) / Fintype.card L else 0) +
        Qpre / (Fintype.card Salt * Fintype.card L) +
          ((Qpre + Qon) * solvePoints n m + (solvePoints n m : ℝ≥0∞) ^ 2 + q) /
            Fintype.card S := by
  refine (prEvent_guessExperiment_scheme_le_of_forall hctx hadv
    SampleableType.prEvent_uniformSample_exists_eq_le).trans (le_of_eq ?_)
  simp only [div_eq_mul_inv]
  ring

end OutcomeExperiment

section Experiment

variable [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
  [SampleableType S] [SampleableType L] [SampleableType Salt]
  {adv : TimeLockPuzzle.Adversary (oracleSpec n S L Salt Ctx) (Puzzle n S L Salt) S}
  {m : ℕ} {mkCtx : Salt → Ctx} {initAcc : Ctx → S} [NeZero n] [AddCommGroup L]

/-- **The conclusion of the delay proof (the final guess).** If the online phase of the adversary
submits at most `r < keyRound n m` rounds, it returns the key label in the ideal experiment with
probability at most `1 / |S|`: the case of `prEvent_idealOutcomeExperiment_le_of_forall` for the
event that the output is the key label. -/
theorem prEvent_idealExperiment_win_le [Fintype S] {r q : ℕ}
    (hbound : ∀ σ P, IsOnlineQueryBound (adv.online σ P) (r, q)) (hr : r < keyRound n m) :
    Pr{let res ← idealExperiment adv m mkCtx initAcc}[res.win = true] ≤
      (Fintype.card S : ℝ≥0∞)⁻¹ := by
  rw [idealExperiment_eq_map_toResult, prEvent_map]
  simpa only [IdealOutcome.toResult, decide_eq_true_eq] using
    prEvent_idealOutcomeExperiment_le_of_forall (E := (· = ·)) hbound hr fun out =>
      (SampleableType.prEvent_uniformSample_eq_singleton' out).le

/-! ## The delay theorem -/

/-- **The delay theorem (`thm:delay`), for adversaries within `keyRound n m - 1` rounds.** For
injective `mkCtx` and an adversary with at most `Q_pre` preprocessing queries whose online phase
submits at most `keyRound n m - 1` rounds holding at most `Q_on` points, the delay advantage
against the pointer-chain puzzle is at most
`[n ≥ 2] Q_on / |L| + Q_pre / (|Salt| |L|) + ((Q_pre + Q_on) P + P² + 1) / |S|`, with
`P = solvePoints n m`. The first term is absent when `n = 1`. The proof adds the final guess
(`prEvent_idealExperiment_win_le`) to Claim 3 (`prEvent_idealExperiment_bad_le`) through the
comparison with the ideal experiment (`delayAdvantage_scheme_le_idealExperiment`); these are the
cases of the statements for outputs of any type (`prEvent_guessExperiment_scheme_le_of_forall`)
for the event that the output is the key. -/
theorem delayAdvantage_scheme_le [Finite Ctx] [Fintype S] [Fintype L] [Fintype Salt]
    (hctx : Function.Injective mkCtx) {Qpre Qon : ℕ}
    (hadv : adv.IsQueryBound Qpre (keyRound n m - 1, Qon)) :
    (scheme n m mkCtx initAcc).delayAdvantage adv ≤
      (if 2 ≤ n then (Qon : ℝ≥0∞) / Fintype.card L else 0) +
        Qpre / (Fintype.card Salt * Fintype.card L) +
          ((Qpre + Qon) * solvePoints n m + (solvePoints n m : ℝ≥0∞) ^ 2 + 1) /
            Fintype.card S := by
  rw [TimeLockPuzzle.delayAdvantage_eq_prEvent_guessExperiment]
  refine (prEvent_guessExperiment_scheme_le_of_forall (E := (· = ·)) hctx hadv fun out =>
    (SampleableType.prEvent_uniformSample_eq_singleton' out).le).trans (le_of_eq ?_)
  simp only [div_eq_mul_inv]
  ring

/-- **The delay theorem (`thm:delay`) as delay security.** For injective `mkCtx`, the
pointer-chain puzzle is delay secure against adversaries with at most `Q_pre` preprocessing
queries and at most `keyRound n m - 1` online rounds holding at most `Q_on` points, with the bound
of `delayAdvantage_scheme_le`. -/
theorem delaySecure_scheme [Finite Ctx] [Fintype S] [Fintype L] [Fintype Salt]
    (hctx : Function.Injective mkCtx) (Qpre Qon : ℕ) :
    TimeLockPuzzle.DelaySecure (scheme n m mkCtx initAcc (L := L)) Qpre (keyRound n m - 1, Qon)
      ((if 2 ≤ n then (Qon : ℝ≥0∞) / Fintype.card L else 0) +
        Qpre / (Fintype.card Salt * Fintype.card L) +
          ((Qpre + Qon) * solvePoints n m + (solvePoints n m : ℝ≥0∞) ^ 2 + 1) /
            Fintype.card S) :=
  fun _ hadv => delayAdvantage_scheme_le hctx hadv

/-- **The delay theorem (`thm:delay`), the paper's form.** For injective `mkCtx` and an adversary
with at most `Q_pre` preprocessing queries whose online phase holds at most `Q_on` points on every
path, with no bound on its rounds, the probability that the online phase outputs the key within
fewer than `T_key = keyRound n m` completed rounds is at most
`[n ≥ 2] Q_on / |L| + Q_pre / (|Salt| |L|) + ((Q_pre + Q_on) P + P² + 1) / |S|`, with
`P = solvePoints n m`. -/
theorem delayAdvantageWithin_scheme_le [Finite Ctx] [Fintype S] [Fintype L] [Fintype Salt]
    (hctx : Function.Injective mkCtx) {Qpre Qon : ℕ}
    (hpre : IsPreprocessingQueryBound adv.preprocess Qpre)
    (honline : ∀ σ P, IsPointQueryBound (adv.online σ P) Qon) :
    TimeLockPuzzle.delayAdvantageWithin (scheme n m mkCtx initAcc) adv (keyRound n m - 1) ≤
      (if 2 ≤ n then (Qon : ℝ≥0∞) / Fintype.card L else 0) +
        Qpre / (Fintype.card Salt * Fintype.card L) +
          ((Qpre + Qon) * solvePoints n m + (solvePoints n m : ℝ≥0∞) ^ 2 + 1) /
            Fintype.card S :=
  have : Inhabited S := ⟨(support_uniformSample_nonempty (α := S)).some⟩
  TimeLockPuzzle.delayAdvantageWithin_le_of_delaySecure (delaySecure_scheme hctx Qpre Qon) hpre
    honline

/-! ## The paper's constants -/

omit [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx] [SampleableType S]
  [SampleableType L] [SampleableType Salt] [NeZero n] [AddCommGroup L] in
/-- With the paper's sizes `|S| = 2^256`, `|L| = 2^(8b)` and `|Salt| = 2^128`, the bound of the
delay theorem is `[n ≥ 2] Q_on / 2^(8b) + Q_pre / 2^(128 + 8b) + (Q P + P² + 1) / 2^256` with
`Q = Q_pre + Q_on` and `P = solvePoints n m`. -/
lemma bound_eq_paper_of_card [Fintype S] [Fintype L] [Fintype Salt] {b : ℕ}
    (hS : Fintype.card S = 2 ^ 256) (hL : Fintype.card L = 2 ^ (8 * b))
    (hSalt : Fintype.card Salt = 2 ^ 128) (Qpre Qon : ℕ) :
    (if 2 ≤ n then (Qon : ℝ≥0∞) / Fintype.card L else 0) +
        Qpre / (Fintype.card Salt * Fintype.card L) +
          ((Qpre + Qon) * solvePoints n m + (solvePoints n m : ℝ≥0∞) ^ 2 + 1) /
            Fintype.card S =
      (if 2 ≤ n then (Qon : ℝ≥0∞) / 2 ^ (8 * b) else 0) + Qpre / 2 ^ (128 + 8 * b) +
        ((Qpre + Qon) * solvePoints n m + (solvePoints n m : ℝ≥0∞) ^ 2 + 1) / 2 ^ 256 := by
  rw [hS, hL, hSalt, pow_add]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

/-- **The delay theorem (`thm:delay`) with the paper's constants, as delay security.** With
`|S| = 2^256`, `|L| = 2^(8b)` and `|Salt| = 2^128`, against adversaries within `Q_pre`
preprocessing queries and `keyRound n m - 1` online rounds holding at most `Q_on` points, the
bound is `[n ≥ 2] Q_on / 2^(8b) + Q_pre / 2^(128 + 8b) + (Q P + P² + 1) / 2^256`. -/
theorem delaySecure_scheme_paper [Finite Ctx] [Fintype S] [Fintype L] [Fintype Salt]
    (hctx : Function.Injective mkCtx) {b : ℕ} (hS : Fintype.card S = 2 ^ 256)
    (hL : Fintype.card L = 2 ^ (8 * b)) (hSalt : Fintype.card Salt = 2 ^ 128) (Qpre Qon : ℕ) :
    TimeLockPuzzle.DelaySecure (scheme n m mkCtx initAcc (L := L)) Qpre (keyRound n m - 1, Qon)
      ((if 2 ≤ n then (Qon : ℝ≥0∞) / 2 ^ (8 * b) else 0) + Qpre / 2 ^ (128 + 8 * b) +
        ((Qpre + Qon) * solvePoints n m + (solvePoints n m : ℝ≥0∞) ^ 2 + 1) / 2 ^ 256) := by
  rw [← bound_eq_paper_of_card (m := m) hS hL hSalt]
  exact delaySecure_scheme hctx Qpre Qon

/-- **The delay theorem (`thm:delay`) with the paper's constants.** With `|S| = 2^256`,
`|L| = 2^(8b)` and `|Salt| = 2^128`, for an adversary with at most `Q_pre` preprocessing queries
whose online phase holds at most `Q_on` points, the probability that it outputs the key within
fewer than `T_key = n (m + 2) + 1` completed rounds is at most
`[n ≥ 2] Q_on / 2^(8b) + Q_pre / 2^(128 + 8b) + (Q P + P² + 1) / 2^256`, with
`Q = Q_pre + Q_on` and `P = n (m + 3) + 1`. -/
theorem delayAdvantageWithin_scheme_le_paper [Finite Ctx] [Fintype S] [Fintype L] [Fintype Salt]
    (hctx : Function.Injective mkCtx) {b : ℕ} (hS : Fintype.card S = 2 ^ 256)
    (hL : Fintype.card L = 2 ^ (8 * b)) (hSalt : Fintype.card Salt = 2 ^ 128) {Qpre Qon : ℕ}
    (hpre : IsPreprocessingQueryBound adv.preprocess Qpre)
    (honline : ∀ σ P, IsPointQueryBound (adv.online σ P) Qon) :
    TimeLockPuzzle.delayAdvantageWithin (scheme n m mkCtx initAcc) adv (keyRound n m - 1) ≤
      (if 2 ≤ n then (Qon : ℝ≥0∞) / 2 ^ (8 * b) else 0) + Qpre / 2 ^ (128 + 8 * b) +
        ((Qpre + Qon) * solvePoints n m + (solvePoints n m : ℝ≥0∞) ^ 2 + 1) / 2 ^ 256 := by
  rw [← bound_eq_paper_of_card (m := m) hS hL hSalt]
  exact delayAdvantageWithin_scheme_le hctx hpre honline

end Experiment

end PointerChainPuzzle
