/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.EvalDist.Measure

/-!
# ε-Cell First-Fire Bound

This file develops the *first-fire bound* for a hidden value drawn from an arbitrary sampler
`oa : ProbComp R` whose every outcome has probability at most `ε`. Where the uniform development
(`FirstFire.lean`) charges a state-dependent `1 / (|R| - S.card)` per genuine read and needs an
exact telescope to fold the growing exclusion sets, the ε-development charges a single uniform `ε`
per read, valid in *every* state. The first-fire telescope collapses to a plain union bound: an
adaptive `q`-read strategy fires with probability at most `q · ε`.

## The model

A hidden target `w ← oa` is drawn **once** and committed into the run's state; an adaptive
`q`-read strategy `σ : List Bool → R`, mapping the boolean reply history (hit/miss) to the next
read point, then probes that fixed `w`, firing as soon as some read equals `w`. Up to the first
hit the read points are fixed by the all-miss history and independent of `w`, so averaging over
the single hidden draw — without ever conditioning on the drawn value — bounds the firing
probability by the union of `q` fixed singletons, each of mass at most `ε`. This models an eager
run that commits a sampled key at draw time and exposes it only through later membership tests.
Because the per-outcome bound `∀ r, Pr{let w ← oa}[w = r] ≤ ε` holds unconditionally, the bound
is valid in every state.

## Main results

* `hiddenReadMany` / `prEvent_hiddenReadMany_le` : the single-target adaptive read game and its
  first-fire union bound `Pr[fire] ≤ q · ε`.
* `hiddenReadList` / `prEvent_hiddenReadList_le` : the per-attempt-fresh-target list game and
  its union bound.
* `prEvent_bind_fire_le_of_gen` : the deferred-sampling fire bound whose marginal is a
  hidden-target read, against an opaque continuation.
* `drawList` : the explicit i.i.d. front-tape form of the per-attempt draws.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace OracleComp

variable {R : Type}

/-! ## Iterated draws: the explicit front-block key list

Stage A defers a *single* output-irrelevant draw. `drawList` lifts this to `n` interleaved draws
by collecting them into an explicit front block: draw a list of `n` independent keys up front,
against which a run's hidden draws can be exhibited and then charged by the abstract
`hiddenReadList` union bound. -/

/-- Draw a list of `n` independent keys from `oa` (the front block of the deferred-sampling
factorization). The keys are the hidden targets; the list length is the key count `n`. -/
noncomputable def drawList (oa : ProbComp R) : ℕ → ProbComp (List R)
  | 0 => pure []
  | n + 1 => do
      let w ← oa
      let ws ← drawList oa n
      pure (w :: ws)

variable [DecidableEq R]

/-! ## Hidden-target adaptive first-fire bound

`hiddenReadMany` draws a single hidden target `w ← oa` **once** and lets an adaptive `q`-read
strategy probe that *fixed* `w` repeatedly. This is the structure of an eager run that commits a
sampled key into its state at draw time and then exposes it only through later membership tests:
the key's value is hidden until the first hit, so up to the first hit the read points are fixed
(determined by the all-miss reply history) and independent of `w`. Averaging over the single hidden
draw — without ever conditioning on the drawn value — gives the union bound `q · ε`. -/

/-- Adaptive `q`-read game against a FIXED hidden target `w`: the strategy `σ` maps the list of
boolean replies (hit/miss) seen so far to the next read point, and the game fires (returns `true`)
iff some read equals `w`. The target `w` is reused across all reads; it is drawn once, outside this
program (see `hiddenReadMany`). -/
noncomputable def readMany (w : R) : ℕ → (List Bool → R) → Bool
  | 0, _ => false
  | q + 1, σ =>
    let b := decide (σ [] = w)
    b || readMany w q (fun h => σ (b :: h))

/-- The hidden-target game: draw the target `w ← oa` **once**, then run `q` adaptive reads against
that fixed `w`. -/
noncomputable def hiddenReadMany (oa : ProbComp R) (q : ℕ) (σ : List Bool → R) : ProbComp Bool :=
  oa >>= fun w => pure (readMany w q σ)

/-- **Fixed read points before the first hit.** A FIXED-target adaptive read game fires iff the
hidden target `w` equals one of the `q` read points reached along the all-miss history
`σ (List.replicate j false)`. The point: those read points do **not** depend on `w` (until a hit,
every reply is a miss, so the history is `replicate j false`), which is exactly what turns the
averaged firing probability into a plain union bound. -/
theorem readMany_true_iff (w : R) (q : ℕ) (σ : List Bool → R) :
    readMany w q σ = true ↔ ∃ j < q, w = σ (List.replicate j false) := by
  induction q generalizing σ with
  | zero => simp [readMany]
  | succ q ih =>
    rw [readMany]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (h | h)
      · exact ⟨0, Nat.succ_pos q, by simpa using h.symm⟩
      · by_cases hhead : σ [] = w
        · exact ⟨0, Nat.succ_pos q, hhead.symm⟩
        · rw [decide_eq_false (by simpa using hhead)] at h
          obtain ⟨j, hj, hwj⟩ := (ih (fun h => σ (false :: h))).1 h
          exact ⟨j + 1, Nat.succ_lt_succ hj, by simpa [List.replicate_succ] using hwj⟩
    · rintro ⟨j, hj, hwj⟩
      cases j with
      | zero => left; simpa using hwj.symm
      | succ j =>
        by_cases hhead : σ [] = w
        · exact Or.inl hhead
        · refine Or.inr ?_
          rw [decide_eq_false (by simpa using hhead)]
          exact (ih (fun h => σ (false :: h))).2
            ⟨j, Nat.lt_of_succ_lt_succ hj, by simpa [List.replicate_succ] using hwj⟩

/-- **Hidden-target adaptive first-fire bound.** A FIXED target `w ← oa` drawn **once** and probed
by `q` adaptive reads fires with probability at most `q · ε`, whenever every outcome of `oa` has
mass at most `ε`. The averaging is over the single hidden draw; we never condition on `w`. Because
the read points are fixed by the all-miss history (`readMany_true_iff`), the firing event is the
union of the `q` fixed singletons `{w = σ (replicate j false)}`, each of mass at most `ε`. -/
theorem prEvent_hiddenReadMany_le {oa : ProbComp R} {ε : ℝ≥0∞}
    (hε : ∀ r : R, Pr{let w ← oa}[w = r] ≤ ε) (q : ℕ) (σ : List Bool → R) :
    Pr{let b ← hiddenReadMany oa q σ}[b = true] ≤ (q : ℝ≥0∞) * ε := by
  calc Pr{let b ← hiddenReadMany oa q σ}[b = true]
      = Pr{let w ← oa}[∃ j ∈ Finset.range q, w = σ (List.replicate j false)] := by
        simp only [hiddenReadMany, prEvent_norm]
        exact prEvent_congr _ _ _ fun w => by simp [readMany_true_iff]
    _ ≤ ∑ j ∈ Finset.range q, Pr{let w ← oa}[w = σ (List.replicate j false)] :=
        prEvent_exists_finset_le _ _ _
    _ ≤ ∑ _j ∈ Finset.range q, ε := Finset.sum_le_sum fun j _ => hε _
    _ = (q : ℝ≥0∞) * ε := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The multi-key fixed-target game: a list `ws` of hidden keys, each probed by the same `q`
adaptive reads; fires iff some read hits some key. Used to model the eager ghost run, whose ghost
cache accumulates one sampled key per rejected signing attempt. -/
noncomputable def readManyList (ws : List R) (q : ℕ) (σ : List Bool → R) : Bool :=
  ws.any (fun w => readMany w q σ)

/-- The list game fires iff some individual key's game fires. -/
theorem readManyList_true_iff (ws : List R) (q : ℕ) (σ : List Bool → R) :
    readManyList ws q σ = true ↔ ∃ w ∈ ws, readMany w q σ = true := by
  simp [readManyList, List.any_eq_true]

/-- The probabilistic multi-key game: draw `n` hidden targets independently from `oa`, one per
rejected signing attempt, and probe each by the same `q` adaptive reads; fire iff some read hits
some target. This is the accumulating-ghost-cache form of `hiddenReadMany`. -/
noncomputable def hiddenReadList (oa : ProbComp R) (q : ℕ) (σ : List Bool → R) :
    ℕ → ProbComp Bool
  | 0 => pure false
  | n + 1 => do
    let w ← oa
    let b ← hiddenReadList oa q σ n
    pure (readMany w q σ || b)

/-- **Multi-key hidden-target first-fire bound.** Drawing `n` independent hidden targets from `oa`
(each outcome of mass at most `ε`) and probing each by `q` adaptive reads fires with probability at
most `n · q · ε`. Proved by induction on `n`: the head key fires with probability at most `q · ε`
(`prEvent_hiddenReadMany_le`), and when it misses, the game is the game on the remaining keys.
This is the form that bounds the eager ghost run's bad probability once the run is factored so that
each rejected signing attempt's key draw is read off as an independent `hiddenReadMany` target. -/
theorem prEvent_hiddenReadList_le {oa : ProbComp R} {ε : ℝ≥0∞}
    (hε : ∀ r : R, Pr{let w ← oa}[w = r] ≤ ε) (q : ℕ) (σ : List Bool → R) (n : ℕ) :
    Pr{let b ← hiddenReadList oa q σ n}[b = true] ≤ (n : ℝ≥0∞) * ((q : ℝ≥0∞) * ε) := by
  induction n with
  | zero => simp [hiddenReadList]
  | succ n ih =>
    have hhead : Pr{let w ← oa}[readMany w q σ = true] ≤ (q : ℝ≥0∞) * ε := by
      simpa only [hiddenReadMany, prEvent_norm] using prEvent_hiddenReadMany_le hε q σ
    rw [hiddenReadList]
    calc Pr{let c ← oa >>= fun w => hiddenReadList oa q σ n >>= fun b =>
            (pure (readMany w q σ || b) : ProbComp Bool)}[c = true]
        ≤ Pr{let w ← oa}[readMany w q σ = true] + (n : ℝ≥0∞) * ((q : ℝ≥0∞) * ε) :=
          prEvent_bind_le_prEvent_add _ _ (fun w => readMany w q σ = true) _ fun w hw => by
            rw [Bool.not_eq_true] at hw
            simpa only [hw, Bool.false_or, bind_pure] using ih
      _ ≤ (q : ℝ≥0∞) * ε + (n : ℝ≥0∞) * ((q : ℝ≥0∞) * ε) := add_le_add hhead le_rfl
      _ = (↑(n + 1) : ℝ≥0∞) * ((q : ℝ≥0∞) * ε) := by push_cast; ring

/-! ## Averaging the key count and the run-factorization bridge

The multi-key bound `prEvent_hiddenReadList_le` is stated for a *fixed* number of keys `n`. In
the intended application the key count is itself random (one ghost key is drawn per *rejected*
signing attempt), so the closing step averages the bound over a key-count distribution
`kn : ProbComp ℕ`, yielding `E[n] · q · ε`. The final bridge
`prEvent_le_of_eq_bind_hiddenReadList`
packages the union-bound side of the *direct route*: once a run's bad marginal is exhibited as a
`kn >>= hiddenReadList oa q σ` game (the deferred-sampling factorization), the bound is immediate.
-/

/-- **Averaged multi-key hidden-target bound.** When the number of independently drawn hidden keys
is itself sampled from `kn : ProbComp ℕ`, the firing probability of the multi-key game is at most
`E[n] · q · ε`, where `E[n] = ∫⁻ n, n ∂𝒟[kn]` is the expected key count. This is the averaging
step of the direct route: it folds the fixed-`n` bound `prEvent_hiddenReadList_le` against the
key-count distribution. Combined with an expected-count bound `E[n] ≤ qS / (1 - p)` it gives the
target `qS · q · ε / (1 - p)`. -/
theorem prEvent_bind_hiddenReadList_le {oa : ProbComp R} {ε : ℝ≥0∞}
    (hε : ∀ r : R, Pr{let w ← oa}[w = r] ≤ ε) (q : ℕ) (σ : List Bool → R) (kn : ProbComp ℕ) :
    Pr{let b ← kn >>= fun n => hiddenReadList oa q σ n}[b = true]
      ≤ (∫⁻ n, (n : ℝ≥0∞) ∂𝒟[kn]) * ((q : ℝ≥0∞) * ε) := by
  rw [prEvent_bind_eq_lintegral_of_discrete,
    ← MeasureTheory.lintegral_mul_const _ Measurable.of_discrete]
  exact MeasureTheory.lintegral_mono fun n => prEvent_hiddenReadList_le hε q σ n

/-- **Direct-route union-bound bridge.** If an arbitrary run `run : ProbComp β` with a bad
event `bad : β → Prop` has its bad marginal bounded by the averaged multi-key hidden-target game
`kn >>= hiddenReadList oa q σ` — the deferred-sampling factorization that pulls the run's hidden key
draws into an independent front block, reading each off as a `hiddenReadMany` target probed by the
`q` subsequent adaptive reads — then the run's bad probability is bounded by the expected-count
union bound `E[n] · q · ε`.

The remaining content is supplied as the hypothesis `hfac`; establishing it is the
deferred-sampling commutation (factoring the run's per-key draws to the front so the pre-first-hit
reads become the deterministic strategy `σ`). -/
theorem prEvent_le_of_eq_bind_hiddenReadList {β : Type} {run : ProbComp β} {bad : β → Prop}
    {oa : ProbComp R} {ε : ℝ≥0∞} (hε : ∀ r : R, Pr{let w ← oa}[w = r] ≤ ε)
    (q : ℕ) (σ : List Bool → R) (kn : ProbComp ℕ)
    (hfac : Pr{let x ← run}[bad x]
      ≤ Pr{let b ← kn >>= fun n => hiddenReadList oa q σ n}[b = true]) :
    Pr{let x ← run}[bad x] ≤ (∫⁻ n, (n : ℝ≥0∞) ∂𝒟[kn]) * ((q : ℝ≥0∞) * ε) :=
  hfac.trans (prEvent_bind_hiddenReadList_le hε q σ kn)

/-! ## Single output-irrelevant draw deferral

The lemmas above take the read strategy `σ` (and, in `hiddenReadList`, the key count) as already
*extracted* data. The genuine new content of the sound route is the **deferral primitive**: lifting
a single hidden draw out of an arbitrary run when that draw is used *only output-irrelevantly* —
i.e. it influences neither the run's visible output nor the read points, only the boolean "fire"
flag computed by membership tests against an adaptive read sequence.

The key observation (cf. `ghostHybridImpl_proj_trans`: the ghost cache is a per-step deterministic
projection of the single ghost-blind run, and the read answer is independent of the ghost value) is
that such a draw can be *deferred* past its continuation. Concretely, a run `oa >>= k` whose
continuation `k w` is built from a `w`-free generator `gen` (producing both the visible output and
the read strategy) with `w` entering only through `readMany w q σ`, has its fire-marginal equal to
that of the deferred game `gen >>= fun p => oa >>= fun w => …`. Each generated branch is then a
`hiddenReadMany` game on a *fixed* strategy `p.2`, charged `q · ε` by
`prEvent_hiddenReadMany_le`. This converts "front-load the draw across the opaque continuation"
into a local `bind`-commutation, the tractable route. -/

/-- **Bind-commutation for an output-irrelevant draw.** When the continuation `k w` is `gen >>= fun
p => pure (p.1, readMany w q p.2)` — a `w`-free generator `gen` producing both the visible output
`p.1` and the read strategy `p.2`, with the hidden draw `w` entering only through the fixed read
game `readMany w q p.2` — the fire-marginal of the run `oa >>= k` is unchanged by deferring the
draw of `w` to *after* `gen`. This is the local deferral step, an instance of the bind-swap law
for independent draws. -/
theorem prEvent_bind_fire_eq_defer {α : Type} (oa : ProbComp R)
    (q : ℕ) (gen : ProbComp (α × (List Bool → R))) (k : R → ProbComp (α × Bool))
    (hk : ∀ w : R, k w = gen >>= fun p => pure (p.1, readMany w q p.2)) :
    Pr{let z ← oa >>= k}[z.2 = true]
      = Pr{let z ← gen >>= fun p => oa >>= fun w =>
          (pure (p.1, readMany w q p.2) : ProbComp (α × Bool))}[z.2 = true] := by
  rw [show k = fun w => gen >>= fun p => pure (p.1, readMany w q p.2) from funext hk]
  refine prEvent_congr_of_evalDist_eq _ _ ?_ _
  let : MeasurableSpace (α × Bool) := ⊤
  exact OracleComp.evalDist_bind_bind_swap _ _ _

/-- **Single output-irrelevant draw first-fire bound (structural form).** A run `oa >>= k` that
draws one hidden value `w ← oa` (each outcome of mass at most `ε`) and feeds it to a continuation
`k w = gen >>= fun p => pure (p.1, readMany w q p.2)` — a `w`-free generator `gen` producing the
visible output and the read strategy, with `w` entering *only* through the fixed read game — fires
with probability at most `q · ε`.

This is the reusable single-draw deferral primitive of the sound route. The proof defers the draw
past `gen` (`prEvent_bind_fire_eq_defer`), so each generated branch becomes a `hiddenReadMany`
game on a fixed strategy `p.2`, charged `q · ε` by `prEvent_hiddenReadMany_le`. -/
theorem prEvent_bind_fire_le_of_gen {α : Type} {oa : ProbComp R} {ε : ℝ≥0∞}
    (hε : ∀ r : R, Pr{let w ← oa}[w = r] ≤ ε) (q : ℕ) (gen : ProbComp (α × (List Bool → R)))
    (k : R → ProbComp (α × Bool))
    (hk : ∀ w : R, k w = gen >>= fun p => pure (p.1, readMany w q p.2)) :
    Pr{let z ← oa >>= k}[z.2 = true] ≤ (q : ℝ≥0∞) * ε := by
  rw [prEvent_bind_fire_eq_defer oa q gen k hk]
  refine prEvent_bind_le_of_forall_le _ _ _ fun p => ?_
  simpa only [hiddenReadMany, prEvent_norm] using prEvent_hiddenReadMany_le hε q p.2

/-- **Single output-irrelevant draw first-fire bound (marginal form).** The convenience special
case of `prEvent_bind_fire_le_of_gen` for a run `oa >>= k` whose continuation's fire-marginal is,
for *every* hidden value `w`, exactly that of the fixed read game `readMany w q σ` against a single
strategy `σ` independent of `w`. Whenever every outcome of `oa` has mass at most `ε`, the run fires
with probability at most `q · ε`. -/
theorem prEvent_bind_fire_le_of_marginal_eq_readMany {α : Type} {oa : ProbComp R} {ε : ℝ≥0∞}
    (hε : ∀ r : R, Pr{let w ← oa}[w = r] ≤ ε) (q : ℕ) (σ : List Bool → R)
    (k : R → ProbComp (α × Bool))
    (hmarg : ∀ w : R, Pr{let z ← k w}[z.2 = true]
      = Pr{let b ← (pure (readMany w q σ) : ProbComp Bool)}[b = true]) :
    Pr{let z ← oa >>= k}[z.2 = true] ≤ (q : ℝ≥0∞) * ε := by
  rw [prEvent_bind_congr oa k (fun w => (pure (readMany w q σ) : ProbComp Bool)) _ _ hmarg]
  exact prEvent_hiddenReadMany_le hε q σ

end OracleComp
