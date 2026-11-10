/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.Sequential
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer

/-!
# Bad events of the ideal experiment (Claim 3)

This file bounds the probability that the generator's `Bad` or online Bad occurs in the ideal
experiment `idealExperiment` (Claim 3 of the pointer-chain delay proof). Write
`P = solvePoints n m`. For injective `mkCtx` and an adversary making at most `Q_pre`
preprocessing queries and at most `Q_on` online point queries,
`prEvent_idealExperiment_bad_le` gives

```
Pr[genBad ∨ onlineBad] ≤ [n ≥ 2] Q_on / |L| + Q_pre / (|Salt| |L|) + ((Q_pre + Q_on) P + P²) / |S|
```

The proof splits into the four cases of the paper's Claim 3:

* `prEvent_collision_le` (case 1, the generator's `Bad` (a)): two distinct path values share
  their path input with probability at most `P² / |S|`;
* `prEvent_eq_pathInput_seed_le` (case 2, the generator's `Bad` (b)): a fixed point, such as one
  cached by the preprocessing phase, is a path input with probability at most
  `1 / (|Salt| |L|) + P / |S|`;
* `prEvent_hitAt_start_le` (case 3): an online start point hits an unreached path value with
  probability at most `1 / |L|`, and never when `n = 1`;
* `prEvent_hitAt_le_of_ne_start` (case 4): any other online point hits with probability at most
  `P / |S|`.

The bridge `prEvent_newHit_le` turns the per-point bounds of cases 3 and 4 into a bound on all the
points logged by the online phase, and `prEvent_idealExperiment_onlineBad_le` and
`prEvent_seed_bad_le` bound the two bad events.

## Route: resampling unreached labels

The paper argues that a label that is not reached when a query is submitted is independent of the
query. Rather than a lazy-label variant of the ideal experiment, this file states that
independence with eager labels, by resampling. `mixLabels R ℓ₀ ℓ'` takes the labels of the
reached set `R` and of the commitment from `ℓ₀` and every other label from `ℓ'`. Drawing `ℓ₀` and
`ℓ'` uniformly gives a uniform labelling (`prEvent_uniform_bind_mixLabels`), so an event of a
uniform labelling may be bounded, for each fixed `ℓ₀`, over the resampled labels `ℓ'` alone.

* The online Bad test compares each logged point with path inputs under the full labelling, and a
  logged point records its reached set (`HitAt`). Against a labelling resampled outside `R`, a
  point hits through some path value with a predecessor `w ∉ R`. Redrawing the label of `w` alone
  (`prEvent_uniform_le_of_update`, the case for an event of
  `prEvent_uniform_bind_le_of_update`) changes that path input injectively
  (`pathInput_update_injective`), which gives cases 3 and 4.
* A round of the ideal handler reads only the labels of the reached set and the labels it newly
  reaches (`idealImpl_inr_run_congr`). After each round, the bridge resamples again outside the
  enlarged reached set, so the next round faces fresh unreached labels. This is the induction in
  `prEvent_newHit_le`.
* Resampling outside the empty set keeps only the commitment's label, and so fixes the puzzle
  (`labelPuzzle_mixLabels`, `prEvent_labelPuzzle_le`). This lets the online phase depend on the
  puzzle while every other label is redrawn, and it gives the non-start half of case 2.

Because the labelling stays eager, the experiment and the bad events are used exactly as
`Handler.lean` defines them, and no equality of distributions between two experiments is needed.
-/

public section

open OracleSpec OracleComp
open scoped ENNReal

namespace PointerChainPuzzle

variable {n m : ℕ} {S L Salt Ctx : Type}

/-! ## Path inputs as functions of single labels -/

namespace PathValue

/-- The values of a path value form a finite type. -/
instance instFintypeVal [Fintype S] [Fintype L] : (v : PathValue n m) → Fintype (v.Val S L)
  | .state .. => inferInstanceAs (Fintype S)
  | .mask _ => inferInstanceAs (Fintype L)
  | .acc _ => inferInstanceAs (Fintype S)
  | .key => inferInstanceAs (Fintype S)
  | .commit => inferInstanceAs (Fintype S)

/-- Every path value other than a mask takes values in `S`. -/
lemma card_val_of_ne_mask [Fintype S] [Fintype L] {v : PathValue n m} (hv : ∀ i, v ≠ .mask i) :
    Fintype.card (v.Val S L) = Fintype.card S := by
  cases v with
  | mask i => exact absurd rfl (hv i)
  | _ => rfl

variable [NeZero n]

/-- The commitment is the predecessor of no path value. -/
lemma commit_not_mem_preds (v : PathValue n m) : PathValue.commit ∉ v.preds := by
  rcases v with ⟨⟨_ | i, hi⟩, ⟨_ | k, hk⟩⟩ | i | ⟨_ | i, hi⟩ | _ | _ <;> simp [preds]

/-- A mask is a predecessor only of the start of the next chain. -/
lemma eq_of_mask_mem_preds {v : PathValue n m} {i : Fin (n - 1)} (h : PathValue.mask i ∈ v.preds) :
    v = .state (nextChain i) ⟨0, m.succ_pos⟩ := by
  rcases v with ⟨⟨_ | j, hj⟩, ⟨_ | k, hk⟩⟩ | j | ⟨_ | j, hj⟩ | _ | _ <;>
    simp only [preds, Fin.mk_zero', Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      reduceCtorEq, or_self, mask.injEq] at h
  subst h
  rfl

end PathValue

section PathInput

variable {m : ℕ} {mkCtx : Salt → Ctx} {initAcc : Ctx → S} [NeZero n] [AddCommGroup L]

/-- A path input determines the label of each of its predecessors: changing the label of a
predecessor `w` of `v` changes the path input of `v` injectively. -/
lemma pathInput_update_injective (P : Puzzle n S L Salt) (ℓ : Labels n m S L)
    {v w : PathValue n m} (hw : w ∈ v.preds) :
    Function.Injective fun u : w.Val S L =>
      pathInput m mkCtx initAcc P (Function.update ℓ w u) v := by
  intro u₁ u₂ h
  rcases v with ⟨⟨_ | i, hi⟩, ⟨_ | k, hk⟩⟩ | i | ⟨_ | i, hi⟩ | _ | _ <;>
    simp only [PathValue.preds, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty] at hw
  all_goals first
    | (subst hw; simpa [pathInput] using h)
    | (rcases hw with rfl | rfl <;> simpa [pathInput] using h)

/-- Only the start of chain `i` has a start point of chain `i` as its path input. -/
lemma eq_of_pathInput_eq_start {P : Puzzle n S L Salt} {ℓ : Labels n m S L} {v : PathValue n m}
    {ctx : Ctx} {i : Fin n} {x : L} (h : pathInput m mkCtx initAcc P ℓ v = .start ctx i x) :
    v = .state i ⟨0, m.succ_pos⟩ := by
  rcases v with ⟨⟨_ | j, hj⟩, ⟨_ | k, hk⟩⟩ | j | ⟨_ | j, hj⟩ | _ | _ <;>
    simp only [pathInput, Fin.mk_zero', Point.start.injEq, reduceCtorEq] at h
  all_goals (obtain ⟨-, rfl, -⟩ := h; rfl)

/-- Two distinct path values have distinct path inputs under every labelling, or one of them has a
state-valued predecessor that is not a predecessor of the other. -/
lemma pathInput_ne_or_exists_pred {v w : PathValue n m} (hvw : v ≠ w) :
    (∀ (P : Puzzle n S L Salt) (ℓ : Labels n m S L),
      pathInput m mkCtx initAcc P ℓ v ≠ pathInput m mkCtx initAcc P ℓ w) ∨
      ∃ a ∈ v.preds, a ∉ w.preds ∧ ∀ i, a ≠ .mask i := by
  rcases v with ⟨⟨_ | i, hi⟩, ⟨_ | k, hk⟩⟩ | i | ⟨_ | i, hi⟩ | _ | _ <;>
    rcases w with ⟨⟨_ | j, hj⟩, ⟨_ | l, hl⟩⟩ | j | ⟨_ | j, hj⟩ | _ | _
  all_goals first
    | exact absurd rfl hvw
    | (left; intro P ℓ h; simp_all [pathInput]; done)
    | (left; intro P ℓ h; simp [pathInput] at h; simp_all [Fin.ext_iff]; done)
    | (right; exact ⟨_, Finset.mem_singleton_self _,
        by simp_all [PathValue.preds, chainOf, Fin.ext_iff], by simp⟩)
    | (right; exact ⟨_, Finset.mem_insert_self _ _,
        by simp_all [PathValue.preds, Fin.ext_iff], by simp⟩)

end PathInput

/-! ## Event bounds after a common draw -/

section Draw

variable {α : Type}

/-- A bound on an event after every draw bounds it after the draw. -/
lemma prEvent_bind_le {mx : ProbComp α} {f : α → ProbComp Prop} {ε : ℝ≥0∞}
    (h : ∀ a, prEvent (f a) ≤ ε) : prEvent (mx >>= f) ≤ ε := by
  simpa using prEvent_bind_le_of_forall_le mx f (fun p => p) (by simpa using h)

/-- A bound on an event after every possible draw bounds it after the draw. -/
lemma prEvent_bind_le_of_support {mx : ProbComp α} {f : α → ProbComp Prop} {ε : ℝ≥0∞}
    (h : ∀ a ∈ support mx, prEvent (f a) ≤ ε) : prEvent (mx >>= f) ≤ ε := by
  simpa using prEvent_bind_le_of_forall_le_of_support mx f (fun p => p) (by simpa using h)

/-- A union bound after every draw gives a union bound after the draw. -/
lemma prEvent_bind_le_add {mx : ProbComp α} {f g k : α → ProbComp Prop}
    (h : ∀ a, prEvent (f a) ≤ prEvent (g a) + prEvent (k a)) :
    prEvent (mx >>= f) ≤ prEvent (mx >>= g) + prEvent (mx >>= k) := by
  simpa using prEvent_bind_le_add_of_forall_le mx f g k (fun p => p) (fun p => p) (fun p => p)
    (by simpa using h)

/-- An event that has probability at most `ε` after a draw satisfying `p` and probability `0`
after any other draw has probability at most `Pr[p] ε`. -/
lemma prEvent_bind_le_mul {mx : ProbComp α} {f : α → ProbComp Prop} (p : α → Prop)
    {ε : ℝ≥0∞} (h₁ : ∀ a, p a → prEvent (f a) ≤ ε) (h₂ : ∀ a, ¬p a → prEvent (f a) = 0) :
    prEvent (mx >>= f) ≤ Pr{let a ← mx}[p a] * ε := by
  simpa using prEvent_bind_le_prEvent_mul_of_forall_le mx f p (fun p => p) (by simpa using h₁)
    (by simpa using h₂)

end Draw

/-! ## Resampling labels -/

section Mix

/-- The labelling that takes the labels of `R` and of the commitment from `ℓ₀` and every other
label from `ℓ'`. -/
@[expose]
def mixLabels (R : Finset (PathValue n m)) (ℓ₀ ℓ' : Labels n m S L) : Labels n m S L :=
  fun v => if v ∈ R ∨ v = .commit then ℓ₀ v else ℓ' v

/-- `mixLabels R ℓ₀ ℓ'` keeps the labels of `R` from `ℓ₀`. -/
lemma mixLabels_of_mem {R : Finset (PathValue n m)} {ℓ₀ ℓ' : Labels n m S L} {v : PathValue n m}
    (hv : v ∈ R) : mixLabels R ℓ₀ ℓ' v = ℓ₀ v := by
  simp [mixLabels, hv]

/-- `mixLabels R ℓ₀ ℓ'` keeps the commitment's label from `ℓ₀`. -/
@[simp] lemma mixLabels_commit (R : Finset (PathValue n m)) (ℓ₀ ℓ' : Labels n m S L) :
    mixLabels R ℓ₀ ℓ' .commit = ℓ₀ .commit := by
  simp [mixLabels]

/-- `mixLabels R ℓ₀ ℓ'` takes the labels outside `R` other than the commitment from `ℓ'`. -/
lemma mixLabels_of_not_mem {R : Finset (PathValue n m)} {ℓ₀ ℓ' : Labels n m S L}
    {v : PathValue n m} (hv : v ∉ R) (hc : v ≠ .commit) : mixLabels R ℓ₀ ℓ' v = ℓ' v := by
  simp [mixLabels, hv, hc]

/-- Resampling inside a larger set: for `R ⊆ R₁`, resampling outside `R` and then outside `R₁` is
resampling outside `R₁` from the labelling resampled outside `R`. -/
lemma mixLabels_mixLabels {R R₁ : Finset (PathValue n m)} (h : R ⊆ R₁)
    (ℓ₀ ℓ' ℓ'' : Labels n m S L) :
    mixLabels R ℓ₀ (mixLabels R₁ ℓ' ℓ'') = mixLabels R₁ (mixLabels R ℓ₀ ℓ') ℓ'' := by
  funext v
  by_cases hv : v ∈ R ∨ v = .commit
  · have hv₁ : v ∈ R₁ ∨ v = .commit := hv.imp_left fun hv => h hv
    simp [mixLabels, hv, hv₁]
  · by_cases hv₁ : v ∈ R₁ ∨ v = .commit <;> simp [mixLabels, hv, hv₁]

/-- Updating the second labelling at a label outside `R` other than the commitment updates the
mixed labelling there. -/
lemma mixLabels_update {R : Finset (PathValue n m)} (ℓ₀ ℓ' : Labels n m S L) {w : PathValue n m}
    (hw : w ∉ R) (hc : w ≠ .commit) (u : w.Val S L) :
    mixLabels R ℓ₀ (Function.update ℓ' w u) = Function.update (mixLabels R ℓ₀ ℓ') w u := by
  funext v
  by_cases hv : v = w
  · subst hv
    simp [mixLabels, hw, hc]
  · simp [mixLabels, hv]

/-- The puzzle committing to a labelling depends only on its commitment label, which `mixLabels`
keeps. -/
lemma labelPuzzle_mixLabels (salt : Salt) (x : L) (z : Fin (n - 1) → L)
    (R : Finset (PathValue n m)) (ℓ₀ ℓ' : Labels n m S L) :
    labelPuzzle salt x z (mixLabels R ℓ₀ ℓ') = labelPuzzle salt x z ℓ₀ := by
  simp [labelPuzzle]

variable [SampleableType S] [SampleableType L]

/-- **Resampling.** Drawing the labels outside `B` (other than the commitment) afresh from a
second uniform labelling keeps the labelling uniform. -/
lemma prEvent_uniform_bind_mixLabels (B : Finset (PathValue n m))
    (f : Labels n m S L → ProbComp Prop) :
    prEvent ($ᵗ Labels n m S L >>= fun ℓ' => $ᵗ Labels n m S L >>= fun ℓ'' =>
      f (mixLabels B ℓ' ℓ'')) = prEvent ($ᵗ Labels n m S L >>= f) := by
  let : MeasurableSpace (Labels n m S L × Labels n m S L) := ⊤
  let : MeasurableSpace (Labels n m S L) := ⊤
  let e : Labels n m S L × Labels n m S L → Labels n m S L × Labels n m S L :=
    fun p => (mixLabels B p.1 p.2, mixLabels B p.2 p.1)
  have he : Function.Involutive e := by
    rintro ⟨a, b⟩
    simp only [e, Prod.mk.injEq]
    constructor <;> funext v <;> by_cases hv : v ∈ B ∨ v = .commit <;> simp [mixLabels, hv]
  have h₁ := evalDist_bind_bijective_uniform_cross ($ᵗ (Labels n m S L × Labels n m S L))
    ($ᵗ (Labels n m S L × Labels n m S L)) SampleableType.evalDist_uniformSample
    SampleableType.evalDist_uniformSample e he.bijective (fun p => f p.1)
  have h₂ : ($ᵗ Labels n m S L >>= fun ℓ' => $ᵗ Labels n m S L >>= fun ℓ'' =>
      f (mixLabels B ℓ' ℓ'')) = ($ᵗ (Labels n m S L × Labels n m S L) >>= fun p => f (e p).1) := by
    rw [SampleableType.uniformSample_prod_eq_bind]
    simp [e]
  rw [prEvent_def, prEvent_def, h₂, h₁, SampleableType.evalDist_uniformSample_prod_bind_fst]

end Mix

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
  rw [prEvent_def, ← h₁, ← prEvent_def, prEvent_bind_bind_swap]
  exact prEvent_bind_le h

/-- **One label.** An event of a uniform labelling has probability at most `ε` if, for every
labelling, redrawing the label of `a` alone gives it probability at most `ε`. -/
lemma prEvent_uniform_le_of_update [SampleableType S] [SampleableType L] (a : PathValue n m)
    (E : Labels n m S L → Prop) {ε : ℝ≥0∞}
    (h : ∀ ℓ, Pr{let u ← $ᵗ (a.Val S L)}[E (Function.update ℓ a u)] ≤ ε) :
    Pr{let ℓ ← $ᵗ Labels n m S L}[E ℓ] ≤ ε := by
  simpa [bind_pure_comp] using prEvent_uniform_bind_le_of_update a (fun ℓ => pure (E ℓ))
    fun ℓ => by simpa [bind_pure_comp] using h ℓ

/-! ## Hits on unreached path values -/

section Hit

variable (m : ℕ) (mkCtx : Salt → Ctx) (initAcc : Ctx → S) [NeZero n] [AddCommGroup L]

/-- The point `t`, submitted against the reached set `R`, *hits* an unreached path value: it is the
path input of some path value with a predecessor outside `R`. An online-bad point hits. -/
@[expose]
def HitAt (P : Puzzle n S L Salt) (ℓ : Labels n m S L) (R : Finset (PathValue n m))
    (t : Point n S L Salt Ctx) : Prop :=
  ∃ v, t = pathInput m mkCtx initAcc P ℓ v ∧ ¬v.preds ⊆ R

variable {m mkCtx initAcc}

/-- An online-bad point hits an unreached path value. -/
lemma OnlineBadAt.hitAt {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {R : Finset (PathValue n m)} {t : Point n S L Salt Ctx}
    (h : OnlineBadAt m mkCtx initAcc P ℓ R t) : HitAt m mkCtx initAcc P ℓ R t := by
  obtain ⟨⟨v, hv⟩, hl⟩ := h
  exact ⟨v, hv, fun hR => hl v ⟨hR, hv⟩⟩

variable [SampleableType S] [SampleableType L]

/-- A point equals the path input of `v` under a labelling resampled outside `R` with probability
at most `1 / |V|`, where `V` is the type of a predecessor `w ∉ R` of `v`. -/
lemma prEvent_eq_pathInput_mixLabels_le [Fintype S] [Fintype L] (P : Puzzle n S L Salt)
    (R : Finset (PathValue n m)) (ℓ₀ : Labels n m S L) (t : Point n S L Salt Ctx)
    {v w : PathValue n m} (hw : w ∈ v.preds) (hwR : w ∉ R) :
    Pr{let ℓ' ← $ᵗ Labels n m S L}[t = pathInput m mkCtx initAcc P (mixLabels R ℓ₀ ℓ') v] ≤
      (Fintype.card (w.Val S L) : ℝ≥0∞)⁻¹ := by
  have hc : w ≠ .commit := fun h => PathValue.commit_not_mem_preds v (h ▸ hw)
  refine prEvent_uniform_le_of_update w _ fun ℓ' => ?_
  simp_rw [mixLabels_update ℓ₀ ℓ' hwR hc, eq_comm (a := t)]
  rw [← Nat.card_eq_fintype_card]
  exact SampleableType.prEvent_uniformSample_apply_eq_le (pathInput_update_injective P _ hw) t

/-- **Claim 3, case 3 (online start points).** A start point of chain `i`, submitted against `R`,
hits an unreached path value under a labelling resampled outside `R` with probability at most
`1 / |L|`, and never when `n = 1`: it can only be the path input of `s_i`, which for `i ≥ 1` has
the unreached mask `μ_{i-1}` as its only predecessor, and `x_i = z_{i-1} - μ_{i-1}` is then
uniform. -/
theorem prEvent_hitAt_start_le [Fintype L] (P : Puzzle n S L Salt) (R : Finset (PathValue n m))
    (ℓ₀ : Labels n m S L) (ctx : Ctx) (i : Fin n) (x : L) :
    Pr{let ℓ' ← $ᵗ Labels n m S L}[
      HitAt m mkCtx initAcc P (mixLabels R ℓ₀ ℓ') R (.start ctx i x)] ≤
      if 2 ≤ n then (Fintype.card L : ℝ≥0∞)⁻¹ else 0 := by
  let := Fintype.ofFinite S
  have hmono : Pr{let ℓ' ← $ᵗ Labels n m S L}[
      HitAt m mkCtx initAcc P (mixLabels R ℓ₀ ℓ') R (.start ctx i x)] ≤
      Pr{let ℓ' ← $ᵗ Labels n m S L}[.start ctx i x =
        pathInput m mkCtx initAcc P (mixLabels R ℓ₀ ℓ') (.state i ⟨0, m.succ_pos⟩) ∧
          ¬(PathValue.state i ⟨0, m.succ_pos⟩ : PathValue n m).preds ⊆ R] := by
    refine prEvent_mono _ _ _ fun ℓ' ⟨v, hv, hR⟩ => ?_
    obtain rfl := eq_of_pathInput_eq_start hv.symm
    exact ⟨hv, hR⟩
  refine hmono.trans ?_
  obtain ⟨_ | j, hi⟩ := i
  · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun ℓ' h => h.2 ?_) zero_le
    simp [PathValue.preds]
  · have hn : 2 ≤ n := by omega
    simp only [hn, ↓reduceIte]
    by_cases hR : (PathValue.mask ⟨j, by omega⟩ : PathValue n m) ∈ R
    · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun ℓ' h => h.2 ?_) zero_le
      simpa [PathValue.preds] using hR
    · refine (prEvent_mono _ _ _ fun ℓ' h => h.1).trans ?_
      have := prEvent_eq_pathInput_mixLabels_le (mkCtx := mkCtx) (initAcc := initAcc) P R ℓ₀
        (.start ctx ⟨j + 1, hi⟩ x) (v := .state ⟨j + 1, hi⟩ ⟨0, m.succ_pos⟩)
        (by simp [PathValue.preds]) hR
      simpa using this

/-- **Claim 3, case 4 (other online points).** A point that is not a start point, submitted
against `R`, hits an unreached path value under a labelling resampled outside `R` with probability
at most `P / |S|`: for each of the `P` path values `v` it may be the path input of, `v` has a
predecessor outside `R`, which is not a mask (masks precede only starts), and its uniform label
determines the path input of `v`. This covers `key(ctx, a_n)` and `commit(ctx, K)`. -/
theorem prEvent_hitAt_le_of_ne_start [Fintype S] (P : Puzzle n S L Salt)
    (R : Finset (PathValue n m)) (ℓ₀ : Labels n m S L) {t : Point n S L Salt Ctx}
    (ht : ∀ ctx i x, t ≠ .start ctx i x) :
    Pr{let ℓ' ← $ᵗ Labels n m S L}[HitAt m mkCtx initAcc P (mixLabels R ℓ₀ ℓ') R t] ≤
      solvePoints n m / Fintype.card S := by
  let := Fintype.ofFinite L
  rw [div_eq_mul_inv, ← PathValue.card_eq (m := m)]
  refine prEvent_exists_le_card_mul _ _ fun v => ?_
  by_cases hR : v.preds ⊆ R
  · exact le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun _ h => h.2 hR) zero_le
  obtain ⟨w, hw, hwR⟩ := Finset.not_subset.mp hR
  by_cases hmask : ∃ j, w = .mask j
  · obtain ⟨j, rfl⟩ := hmask
    obtain rfl := PathValue.eq_of_mask_mem_preds hw
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun ℓ' h => ?_) zero_le
    exact ht _ _ _ h.1
  · simp only [not_exists] at hmask
    refine (prEvent_mono _ _ _ fun ℓ' h => h.1).trans ?_
    rw [← PathValue.card_val_of_ne_mask (L := L) hmask]
    exact prEvent_eq_pathInput_mixLabels_le P R ℓ₀ t hw hwR

/-- The probability that a point hits, `[n ≥ 2] / |L| + P / |S|`. -/
@[expose, reducible]
noncomputable def hitBound (n m : ℕ) (S L : Type) [Fintype S] [Fintype L] : ℝ≥0∞ :=
  (if 2 ≤ n then (Fintype.card L : ℝ≥0∞)⁻¹ else 0) + solvePoints n m / Fintype.card S

/-- Any point, submitted against `R`, hits an unreached path value under a labelling resampled
outside `R` with probability at most `hitBound`. -/
theorem prEvent_hitAt_le [Fintype S] [Fintype L] (P : Puzzle n S L Salt)
    (R : Finset (PathValue n m)) (ℓ₀ : Labels n m S L) (t : Point n S L Salt Ctx) :
    Pr{let ℓ' ← $ᵗ Labels n m S L}[HitAt m mkCtx initAcc P (mixLabels R ℓ₀ ℓ') R t] ≤
      hitBound n m S L := by
  by_cases ht : ∃ ctx i x, t = .start ctx i x
  · obtain ⟨ctx, i, x, rfl⟩ := ht
    exact (prEvent_hitAt_start_le P R ℓ₀ ctx i x).trans le_self_add
  · simp only [not_exists] at ht
    exact (prEvent_hitAt_le_of_ne_start P R ℓ₀ ht).trans le_add_self

/-- A round of points, submitted against `R`, hits an unreached path value under a labelling
resampled outside `R` with probability at most its number of points times `hitBound`. -/
theorem prEvent_exists_hitAt_le [Fintype S] [Fintype L] (P : Puzzle n S L Salt)
    (R : Finset (PathValue n m)) (ℓ₀ : Labels n m S L) (ts : List (Point n S L Salt Ctx)) :
    Pr{let ℓ' ← $ᵗ Labels n m S L}[∃ t ∈ ts, HitAt m mkCtx initAcc P (mixLabels R ℓ₀ ℓ') R t] ≤
      ts.length * hitBound n m S L := by
  classical
  calc _ = Pr{let ℓ' ← $ᵗ Labels n m S L}[
        ∃ t ∈ ts.toFinset, HitAt m mkCtx initAcc P (mixLabels R ℓ₀ ℓ') R t] := by
          simp only [List.mem_toFinset]
    _ ≤ ts.toFinset.card * hitBound n m S L :=
          prEvent_exists_finset_le_card_mul _ _ _ fun t _ => prEvent_hitAt_le P R ℓ₀ t
    _ ≤ ts.length * hitBound n m S L := by
          gcongr
          exact List.toFinset_card_le ts

end Hit

/-! ## Collisions -/

section Collision

variable {m : ℕ} {mkCtx : Salt → Ctx} {initAcc : Ctx → S} [NeZero n] [AddCommGroup L]
  [Fintype S] [SampleableType S] [SampleableType L]

/-- Two distinct path values share their path input under a uniform labelling with probability at
most `1 / |S|`. -/
lemma prEvent_pathInput_eq_le (salt : Salt) (x : L) (z : Fin (n - 1) → L) (v w : PathValue n m) :
    Pr{let ℓ ← $ᵗ Labels n m S L}[v ≠ w ∧
      pathInput m mkCtx initAcc (labelPuzzle salt x z ℓ) ℓ v =
        pathInput m mkCtx initAcc (labelPuzzle salt x z ℓ) ℓ w] ≤ (Fintype.card S : ℝ≥0∞)⁻¹ := by
  let := Fintype.ofFinite L
  by_cases hvw : v = w
  · exact le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun _ h => h.1 hvw) zero_le
  rcases pathInput_ne_or_exists_pred (S := S) (L := L) (mkCtx := mkCtx) (initAcc := initAcc)
    hvw with hne | ⟨a, ha, haw, hmask⟩
  · exact le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun _ h => hne _ _ h.2) zero_le
  refine prEvent_uniform_le_of_update a _ fun ℓ => ?_
  have hw : ∀ u, pathInput m mkCtx initAcc (labelPuzzle salt x z ℓ) (Function.update ℓ a u) w =
      pathInput m mkCtx initAcc (labelPuzzle salt x z ℓ) ℓ w := fun u =>
    pathInput_congr m mkCtx initAcc _ w fun b hb =>
      Function.update_of_ne (fun (h : b = a) => haw (h ▸ hb)) _ _
  simp_rw [pathInput_labelPuzzle m mkCtx initAcc salt x z _ ℓ, hw]
  refine (prEvent_mono _ _ _ fun u h => h.2).trans ?_
  rw [← PathValue.card_val_of_ne_mask (L := L) hmask, ← Nat.card_eq_fintype_card]
  exact SampleableType.prEvent_uniformSample_apply_eq_le
    (pathInput_update_injective (labelPuzzle salt x z ℓ) ℓ ha) _

/-- **Claim 3, case 1 (collisions, the generator's `Bad` (a)).** Under a uniform labelling, two
distinct path values share their path input with probability at most `P² / |S|`: equal inputs to
one oracle force a state-valued predecessor of one of them that is not a predecessor of the
other to take one value, and starts carry their chain index. -/
theorem prEvent_collision_le (salt : Salt) (x : L) (z : Fin (n - 1) → L) :
    Pr{let ℓ ← $ᵗ Labels n m S L}[∃ v w, v ≠ w ∧
      pathInput m mkCtx initAcc (labelPuzzle salt x z ℓ) ℓ v =
        pathInput m mkCtx initAcc (labelPuzzle salt x z ℓ) ℓ w] ≤
      (solvePoints n m : ℝ≥0∞) ^ 2 / Fintype.card S := by
  have h := prEvent_exists_le_card_mul _ _ fun v =>
    prEvent_exists_le_card_mul _ _ fun w => prEvent_pathInput_eq_le (S := S) (m := m)
      (mkCtx := mkCtx) (initAcc := initAcc) salt x z v w
  refine h.trans (le_of_eq ?_)
  rw [PathValue.card_eq, div_eq_mul_inv, sq, mul_assoc]

end Collision

/-! ## The ideal handler reads only reached labels -/

section Reads

variable {m : ℕ} {mkCtx : Salt → Ctx} {initAcc : Ctx → S} [NeZero n] [AddCommGroup L]
  [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
  {P : Puzzle n S L Salt} {ℓ₁ ℓ₂ : Labels n m S L} {R : Finset (PathValue n m)}

omit [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx] in
/-- Whether a point is the legitimate query of a path value depends only on the labels of the
reached set. -/
lemma isLegit_congr (hR : ∀ v ∈ R, ℓ₁ v = ℓ₂ v) (t : Point n S L Salt Ctx) (v : PathValue n m) :
    IsLegit m mkCtx initAcc P ℓ₁ R t v ↔ IsLegit m mkCtx initAcc P ℓ₂ R t v := by
  refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
  · rw [h.2]
    exact pathInput_congr m mkCtx initAcc P v fun w hw => hR w (h.1 hw)
  · rw [h.2]
    exact (pathInput_congr m mkCtx initAcc P v fun w hw => hR w (h.1 hw)).symm

/-- The path values a round newly reaches depend only on the labels of the reached set. -/
lemma newlyReached_congr (hR : ∀ v ∈ R, ℓ₁ v = ℓ₂ v) (ts : List (Point n S L Salt Ctx)) :
    newlyReached m mkCtx initAcc P ℓ₁ R ts = newlyReached m mkCtx initAcc P ℓ₂ R ts := by
  ext v
  simp only [mem_newlyReached_iff_exists, isLegit_congr hR]

/-- The label a legitimate point returns is the same under two labellings that agree on the
reached set and on the path values the point legitimately queries. -/
lemma legitLabelFrom_congr (hR : ∀ v ∈ R, ℓ₁ v = ℓ₂ v) {t : Point n S L Salt Ctx}
    (hl : ∀ v, IsLegit m mkCtx initAcc P ℓ₁ R t v → ℓ₁ v = ℓ₂ v) (vs : List (PathValue n m)) :
    legitLabelFrom m mkCtx initAcc P ℓ₁ R t vs = legitLabelFrom m mkCtx initAcc P ℓ₂ R t vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      by_cases h₁ : IsLegit m mkCtx initAcc P ℓ₁ R t v
      · have h₂ := (isLegit_congr hR t v).mp h₁
        simp only [legitLabelFrom, h₁, h₂, ↓reduceDIte, labelAt, hl v h₁]
      · have h₂ : ¬IsLegit m mkCtx initAcc P ℓ₂ R t v := fun h => h₁ ((isLegit_congr hR t v).mpr h)
        simp only [legitLabelFrom, h₁, h₂, ↓reduceDIte, ih]

variable [SampleableType S] [SampleableType L]

/-- A round of the ideal handler reads the labels only on the reached set and on the path values
it reaches: two labellings that agree there handle the round alike. -/
lemma idealImpl_inr_run_congr {s : IdealState n m S L Salt Ctx} {ts : List (Point n S L Salt Ctx)}
    (h : ∀ v ∈ s.reached ∪ newlyReached m mkCtx initAcc P ℓ₁ s.reached ts, ℓ₁ v = ℓ₂ v) :
    (idealImpl m mkCtx initAcc P ℓ₁ (.inr ts)).run s =
      (idealImpl m mkCtx initAcc P ℓ₂ (.inr ts)).run s := by
  have hR : ∀ v ∈ s.reached, ℓ₁ v = ℓ₂ v := fun v hv => h v (Finset.mem_union_left _ hv)
  have hpoint : ∀ t ∈ ts, idealPoint m mkCtx initAcc P ℓ₁ s.reached t =
      idealPoint m mkCtx initAcc P ℓ₂ s.reached t := by
    intro t ht
    have hl : legitLabel m mkCtx initAcc P ℓ₁ s.reached t =
        legitLabel m mkCtx initAcc P ℓ₂ s.reached t :=
      legitLabelFrom_congr hR (fun v hv => h v (Finset.mem_union_right _
        (mem_newlyReached_iff_exists.mpr ⟨t, ht, hv⟩))) _
    simp only [idealPoint, hl]
  have hafter : ∀ c, s.afterRound m mkCtx initAcc P ℓ₁ ts c =
      s.afterRound m mkCtx initAcc P ℓ₂ ts c := fun c => by
    simp only [IdealState.afterRound, newlyReached_congr hR ts]
  rw [idealImpl_inr_run, idealImpl_inr_run, QueryImpl.batch_congr hpoint]
  simp only [hafter]

/-- The log of the ideal handler only grows. -/
lemma log_prefix_of_mem_support {ℓ : Labels n m S L} {α : Type}
    (oa : OracleComp (unifSpec + (oracleSpec n S L Salt Ctx).batch) α)
    (s : IdealState n m S L Salt Ctx) {z : α × IdealState n m S L Salt Ctx}
    (hz : z ∈ support ((simulateQ (idealImpl m mkCtx initAcc P ℓ) oa).run s)) :
    s.log <+: z.2.log := by
  refine simulateQ_run_preservesInv _ (fun s' => s.log <+: s'.log) ?_ oa s
    (List.prefix_refl _) z hz
  rintro (k | ts) s' hs' z' hz'
  · rwa [eq_of_mem_support_idealImpl_inl hz']
  · obtain ⟨c, hc⟩ := exists_of_mem_support_idealImpl_inr hz'
    rw [hc, IdealState.afterRound_log]
    exact hs'.trans (List.prefix_append _ _)

end Reads

/-! ## The bridge -/

section Bridge

variable (m : ℕ) (mkCtx : Salt → Ctx) (initAcc : Ctx → S) [NeZero n] [AddCommGroup L]

/-- Some point logged after the state `s` hit an unreached path value at its submission. -/
@[expose]
def NewHit (P : Puzzle n S L Salt) (ℓ : Labels n m S L) (s s' : IdealState n m S L Salt Ctx) :
    Prop :=
  ∃ e ∈ s'.log.drop s.log.length, HitAt m mkCtx initAcc P ℓ e.reached e.point

variable {m mkCtx initAcc} [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
  [SampleableType S] [SampleableType L]

/-- Running the ideal handler on a query followed by a continuation runs the query, then the
continuation from the resulting state. -/
lemma run_simulateQ_query_bind {ℓ : Labels n m S L} {P : Puzzle n S L Salt} {α : Type}
    (t : (unifSpec + (oracleSpec n S L Salt Ctx).batch).Domain)
    (f : (unifSpec + (oracleSpec n S L Salt Ctx).batch).Range t →
      OracleComp (unifSpec + (oracleSpec n S L Salt Ctx).batch) α)
    (s : IdealState n m S L Salt Ctx) :
    (simulateQ (idealImpl m mkCtx initAcc P ℓ)
      ((liftM (OracleSpec.query t) :
        OracleComp (unifSpec + (oracleSpec n S L Salt Ctx).batch) _) >>= f)).run s =
      (idealImpl m mkCtx initAcc P ℓ t).run s >>= fun p =>
        (simulateQ (idealImpl m mkCtx initAcc P ℓ) (f p.1)).run p.2 := by
  simp [simulateQ_bind]

/-- A point logged after a round was logged in that round, against the reached set at its
submission, or after it. -/
lemma newHit_of_mem_support_inr {P : Puzzle n S L Salt} {ℓ : Labels n m S L} {α : Type}
    {ts : List (Point n S L Salt Ctx)}
    {f : (oracleSpec n S L Salt Ctx).batch.Range ts →
      OracleComp (unifSpec + (oracleSpec n S L Salt Ctx).batch) α}
    {s : IdealState n m S L Salt Ctx}
    {p : (oracleSpec n S L Salt Ctx).batch.Range ts × IdealState n m S L Salt Ctx}
    (hp : p ∈ support ((idealImpl m mkCtx initAcc P ℓ (.inr ts)).run s))
    {z : α × IdealState n m S L Salt Ctx}
    (hz : z ∈ support ((simulateQ (idealImpl m mkCtx initAcc P ℓ) (f p.1)).run p.2))
    (h : NewHit m mkCtx initAcc P ℓ s z.2) :
    (∃ t ∈ ts, HitAt m mkCtx initAcc P ℓ s.reached t) ∨ NewHit m mkCtx initAcc P ℓ p.2 z.2 := by
  obtain ⟨c, hc⟩ := exists_of_mem_support_idealImpl_inr hp
  obtain ⟨D, hD⟩ := log_prefix_of_mem_support (f p.1) p.2 hz
  obtain ⟨e, he, hhit⟩ := h
  rw [hc, IdealState.afterRound_log] at hD
  rw [← hD, List.append_assoc, List.drop_left, List.mem_append] at he
  rcases he with he | he
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
    exact Or.inl ⟨t, ht, hhit⟩
  · refine Or.inr ⟨e, ?_, hhit⟩
    rw [← hD, hc, IdealState.afterRound_log, List.drop_left]
    exact he

/-- After a round, the reached set is the reached set before it with the newly reached path
values. -/
lemma reached_of_mem_support_inr {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {ts : List (Point n S L Salt Ctx)} {s : IdealState n m S L Salt Ctx}
    {p : (oracleSpec n S L Salt Ctx).batch.Range ts × IdealState n m S L Salt Ctx}
    (hp : p ∈ support ((idealImpl m mkCtx initAcc P ℓ (.inr ts)).run s)) :
    p.2.reached = s.reached ∪ newlyReached m mkCtx initAcc P ℓ s.reached ts := by
  obtain ⟨c, hc⟩ := exists_of_mem_support_idealImpl_inr hp
  rw [hc, IdealState.afterRound_reached]

variable [Fintype S] [Fintype L]

/-- **The bridge.** Run the ideal handler from the state `s` on a computation making at most `q`
point queries, with the labels outside the reached set of `s` (other than the commitment)
resampled. Then some point logged during the run hits an unreached path value at its submission
with probability at most `q ([n ≥ 2] / |L| + P / |S|)`.

The proof inducts on the computation. A round of points reads only the reached labels and the
labels it newly reaches (`idealImpl_inr_run_congr`), so the labels outside the enlarged reached
set can be resampled again after the round (`prEvent_uniform_bind_mixLabels`), and the
continuation starts in the same situation. Each point of the round hits with probability at most
`hitBound` (`prEvent_exists_hitAt_le`). -/
theorem prEvent_newHit_le (P : Puzzle n S L Salt) {α : Type}
    (oa : OracleComp (unifSpec + (oracleSpec n S L Salt Ctx).batch) α) {q : ℕ}
    (hq : IsPointQueryBound oa q) (s : IdealState n m S L Salt Ctx) (ℓ₀ : Labels n m S L) :
    Pr{let ℓ' ← $ᵗ Labels n m S L;
       let z ← (simulateQ (idealImpl m mkCtx initAcc P (mixLabels s.reached ℓ₀ ℓ')) oa).run s}[
        NewHit m mkCtx initAcc P (mixLabels s.reached ℓ₀ ℓ') s z.2] ≤ q * hitBound n m S L := by
  induction oa using OracleComp.inductionOn generalizing q s ℓ₀ with
  | pure a =>
      refine le_of_eq_of_le ?_ zero_le
      simp [NewHit]
  | query_bind t f ih =>
      obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).mp hq
      simp only [run_simulateQ_query_bind, map_bind]
      rcases t with k | ts
      · simp only [idealImpl_inl_run, bind_map_left]
        rw [prEvent_bind_bind_swap]
        exact prEvent_bind_le fun u => by simpa using ih u (by simpa using hk u) s ℓ₀
      · simp only [pointCount_inr] at ht
        simp only [pointCount_inr] at hk
        obtain ⟨R₁, hR₁⟩ : ∃ R₁, R₁ = s.reached ∪ newlyReached m mkCtx initAcc P ℓ₀ s.reached ts :=
          ⟨_, rfl⟩
        have hRR₁ : s.reached ⊆ R₁ := hR₁ ▸ Finset.subset_union_left
        -- Split off the hits of this round, which depend only on the labels.
        refine (prEvent_bind_le_add (g := fun ℓ' => pure (∃ t ∈ ts,
            HitAt m mkCtx initAcc P (mixLabels s.reached ℓ₀ ℓ') s.reached t))
          (k := fun ℓ' => (idealImpl m mkCtx initAcc P (mixLabels s.reached ℓ₀ ℓ') (.inr ts)).run s
            >>= fun p => (fun z => NewHit m mkCtx initAcc P (mixLabels s.reached ℓ₀ ℓ') p.2 z.2) <$>
              (simulateQ (idealImpl m mkCtx initAcc P (mixLabels s.reached ℓ₀ ℓ')) (f p.1)).run p.2)
          fun ℓ' => ?_).trans ?_
        · by_cases hE : ∃ t ∈ ts, HitAt m mkCtx initAcc P (mixLabels s.reached ℓ₀ ℓ') s.reached t
          · refine (prEvent_le_one _).trans (le_trans (le_of_eq ?_) le_self_add)
            simp [hE]
          · refine le_trans ?_ le_add_self
            exact prEvent_bind_mono_of_support _ _ _ fun p hp =>
              prEvent_mono_of_support _ _ _ fun z hz hn =>
                (newHit_of_mem_support_inr hp hz hn).resolve_left hE
        refine (add_le_add (b := (ts.length : ℝ≥0∞) * hitBound n m S L)
          (d := ((q - ts.length : ℕ) : ℝ≥0∞) * hitBound n m S L) ?_ ?_).trans (le_of_eq ?_)
        · simpa [bind_pure_comp] using prEvent_exists_hitAt_le P s.reached ℓ₀ ts
        · -- Resample the labels outside the reached set after the round.
          rw [← prEvent_uniform_bind_mixLabels R₁]
          refine prEvent_bind_le fun ℓ₁ => ?_
          simp only [mixLabels_mixLabels hRR₁]
          have hNR : newlyReached m mkCtx initAcc P (mixLabels s.reached ℓ₀ ℓ₁) s.reached ts =
              newlyReached m mkCtx initAcc P ℓ₀ s.reached ts :=
            newlyReached_congr (fun w hw => mixLabels_of_mem hw) ts
          have hstep : ∀ ℓ₂, (idealImpl m mkCtx initAcc P
              (mixLabels R₁ (mixLabels s.reached ℓ₀ ℓ₁) ℓ₂) (.inr ts)).run s =
              (idealImpl m mkCtx initAcc P (mixLabels s.reached ℓ₀ ℓ₁) (.inr ts)).run s :=
            fun ℓ₂ => (idealImpl_inr_run_congr fun v hv => by
              rw [hNR, ← hR₁] at hv
              exact (mixLabels_of_mem hv).symm).symm
          simp only [hstep]
          rw [prEvent_bind_bind_swap]
          refine prEvent_bind_le_of_support fun p hp => ?_
          have hreached : p.2.reached = R₁ := by
            rw [reached_of_mem_support_inr hp, hNR, hR₁]
          rw [← hreached]
          exact ih p.1 (hk p.1) p.2 _
        · rw [← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' ht]

end Bridge

/-! ## Preprocessing queries -/

section Preprocessing

variable {m : ℕ} {mkCtx : Salt → Ctx} {initAcc : Ctx → S} [NeZero n] [AddCommGroup L]

/-- A path input that is not the start of the first chain hits against the empty reached set. -/
lemma hitAt_empty_of_eq {P : Puzzle n S L Salt} {ℓ : Labels n m S L} {t : Point n S L Salt Ctx}
    {v : PathValue n m} (hv : t = pathInput m mkCtx initAcc P ℓ v)
    (ht : ∀ ctx x, t ≠ .start ctx ⟨0, Nat.pos_of_neZero n⟩ x) :
    HitAt m mkCtx initAcc P ℓ ∅ t := by
  refine ⟨v, hv, fun hR => ?_⟩
  rw [Finset.subset_empty, PathValue.preds_eq_empty_iff] at hR
  subst hR
  exact ht _ _ hv

variable [Fintype S] [Fintype L] [SampleableType S] [SampleableType L]

omit [NeZero n] [AddCommGroup L] [Fintype S] [Fintype L] in
/-- Resampling every label but the commitment fixes the puzzle: an event of the puzzle committing
to a uniform labelling and of that labelling is bounded by bounding it, for each labelling `ℓ₀`,
on the puzzle of `ℓ₀` and the labelling resampled outside the commitment. -/
lemma prEvent_labelPuzzle_le (salt : Salt) (x : L) (z : Fin (n - 1) → L)
    (E : Puzzle n S L Salt → Labels n m S L → Prop) {ε : ℝ≥0∞}
    (h : ∀ ℓ₀, Pr{let ℓ' ← $ᵗ Labels n m S L}[E (labelPuzzle salt x z ℓ₀) (mixLabels ∅ ℓ₀ ℓ')] ≤
      ε) :
    Pr{let ℓ ← $ᵗ Labels n m S L}[E (labelPuzzle salt x z ℓ) ℓ] ≤ ε := by
  have h₁ := prEvent_uniform_bind_mixLabels (∅ : Finset (PathValue n m))
    (fun ℓ => (pure (E (labelPuzzle salt x z ℓ) ℓ) : ProbComp Prop))
  simp only [labelPuzzle_mixLabels] at h₁
  rw [map_eq_bind_pure_comp]
  refine le_of_eq_of_le h₁.symm (prEvent_bind_le fun ℓ₀ => ?_)
  simpa [bind_pure_comp] using h ℓ₀

/-- **Claim 3, case 2 (preprocessing queries, the generator's `Bad` (b)).** A fixed point, such as
one cached by the preprocessing phase, is a path input of the puzzle drawn afterwards with
probability at most `1 / (|Salt| |L|) + P / |S|`: a start point names one chain index and is the
path input of that chain's start only if its context is that of the fresh salt (through injective
`mkCtx`) and its link is `x_i` (uniform: `x_0` directly, `x_i = z_{i-1} - μ_{i-1}` through the
mask); every other point is as in case 4 against the empty reached set. -/
theorem prEvent_eq_pathInput_seed_le (hctx : Function.Injective mkCtx)
    (t : Point n S L Salt Ctx) [SampleableType Salt] [Fintype Salt] :
    Pr{let salt ← $ᵗ Salt; let p ← $ᵗ (L × (Fin (n - 1) → L)); let ℓ ← $ᵗ Labels n m S L}[
      ∃ v, t = pathInput m mkCtx initAcc (labelPuzzle salt p.1 p.2 ℓ) ℓ v] ≤
      (Fintype.card Salt * Fintype.card L : ℝ≥0∞)⁻¹ + solvePoints n m / Fintype.card S := by
  by_cases hst : ∃ ctx i x, t = .start ctx i x
  · obtain ⟨ctx, i, x, rfl⟩ := hst
    refine le_add_right ?_
    have h₁ : ∀ salt, mkCtx salt = ctx →
        Pr{let p ← $ᵗ (L × (Fin (n - 1) → L)); let ℓ ← $ᵗ Labels n m S L}[
          ∃ v, Point.start ctx i x = pathInput m mkCtx initAcc (labelPuzzle salt p.1 p.2 ℓ) ℓ v] ≤
          (Fintype.card L : ℝ≥0∞)⁻¹ := by
      intro salt hsalt
      obtain ⟨_ | j, hi⟩ := i
      · have h₀ : ∀ p : L × (Fin (n - 1) → L), ¬p.1 = x →
            Pr{let ℓ ← $ᵗ Labels n m S L}[∃ v, Point.start ctx ⟨0, hi⟩ x =
              pathInput m mkCtx initAcc (labelPuzzle salt p.1 p.2 ℓ) ℓ v] = 0 := by
          intro p hp
          refine prEvent_eq_zero_of_forall_not _ _ fun ℓ ⟨v, hv⟩ => hp ?_
          obtain rfl := eq_of_pathInput_eq_start hv.symm
          simp only [pathInput, labelPuzzle, Point.start.injEq] at hv
          exact hv.2.2.symm
        refine (prEvent_bind_le_mul (fun p => p.1 = x) (ε := 1) (fun _ _ => prEvent_le_one _)
          h₀).trans ?_
        have hfst := SampleableType.evalDist_uniformSample_prod_bind_fst (β := Fin (n - 1) → L)
          (fun a : L => (pure (a = x) : ProbComp Prop))
        calc Pr{let p ← $ᵗ (L × (Fin (n - 1) → L))}[p.1 = x] * 1 = Pr{let a ← $ᵗ L}[a = x] := by
              rw [mul_one, prEvent_def, prEvent_def, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
              exact congrArg (· {True}) hfst
          _ ≤ _ := (SampleableType.prEvent_uniformSample_eq_singleton x).le
      · refine prEvent_bind_le fun p => prEvent_labelPuzzle_le salt p.1 p.2
          (fun P ℓ => ∃ v, Point.start ctx ⟨j + 1, hi⟩ x = pathInput m mkCtx initAcc P ℓ v)
          fun ℓ₀ => ?_
        have hne : ∀ ctx' x', (Point.start ctx ⟨j + 1, hi⟩ x : Point n S L Salt Ctx) ≠
            .start ctx' ⟨0, Nat.pos_of_neZero n⟩ x' := by
          intro ctx' x' h
          simp only [Point.start.injEq, Fin.mk.injEq] at h
          omega
        refine (prEvent_mono _ _ _ fun ℓ' ⟨v, hv⟩ => hitAt_empty_of_eq hv hne).trans
          ((prEvent_hitAt_start_le _ ∅ ℓ₀ ctx ⟨j + 1, hi⟩ x).trans ?_)
        split_ifs <;> simp
    have h₂ : ∀ salt, ¬mkCtx salt = ctx →
        Pr{let p ← $ᵗ (L × (Fin (n - 1) → L)); let ℓ ← $ᵗ Labels n m S L}[
          ∃ v, Point.start ctx i x = pathInput m mkCtx initAcc (labelPuzzle salt p.1 p.2 ℓ) ℓ v] =
          0 := by
      intro salt hsalt
      refine le_antisymm (prEvent_bind_le fun p => le_of_eq
        (prEvent_eq_zero_of_forall_not _ _ fun ℓ ⟨v, hv⟩ => hsalt ?_)) zero_le
      obtain rfl := eq_of_pathInput_eq_start hv.symm
      obtain ⟨_ | j, hj⟩ := i <;>
        simp only [Fin.mk_zero', pathInput, labelPuzzle, Point.start.injEq, true_and] at hv <;>
        exact hv.1.symm
    refine (prEvent_bind_le_mul (fun salt => mkCtx salt = ctx) h₁ h₂).trans ?_
    have hsalt : Pr{let salt ← $ᵗ Salt}[mkCtx salt = ctx] ≤ (Fintype.card Salt : ℝ≥0∞)⁻¹ := by
      rw [← Nat.card_eq_fintype_card]
      exact SampleableType.prEvent_uniformSample_apply_eq_le hctx ctx
    rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
    gcongr
  · simp only [not_exists] at hst
    refine le_add_left (prEvent_bind_le fun salt => prEvent_bind_le fun p =>
      prEvent_labelPuzzle_le salt p.1 p.2
        (fun P ℓ => ∃ v, t = pathInput m mkCtx initAcc P ℓ v) fun ℓ₀ => ?_)
    exact (prEvent_mono _ _ _ fun ℓ' ⟨v, hv⟩ => hitAt_empty_of_eq hv fun ctx x => hst ctx _ x).trans
      (prEvent_hitAt_le_of_ne_start _ ∅ ℓ₀ hst)

end Preprocessing

/-! ## Claim 3 -/

section OutcomeExperiment

variable [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
  [SampleableType S] [SampleableType L] [SampleableType Salt]
  {m : ℕ} {mkCtx : Salt → Ctx} {initAcc : Ctx → S} [NeZero n] [AddCommGroup L]

omit [NeZero n] [AddCommGroup L] in
/-- A bound on an event after each run of the preprocessing computation, for the salt, links and
labels drawn after it, bounds the event after the seed. -/
lemma prEvent_seedOf_bind_le {State : Type}
    {pre : OracleComp (unifSpec + oracleSpec n S L Salt Ctx) State}
    {g : Seed n m S L Salt Ctx State → ProbComp Prop} {ε : ℝ≥0∞}
    (h : ∀ z ∈ support ((simulateQ (oracleSpec n S L Salt Ctx).romImpl pre).run ∅),
      prEvent ($ᵗ Salt >>= fun salt => $ᵗ (L × (Fin (n - 1) → L)) >>= fun p =>
        $ᵗ Labels n m S L >>= fun ℓ => g ⟨z.1, z.2, salt, p.1, p.2, ℓ⟩) ≤ ε) :
    prEvent (seedOf pre m >>= g) ≤ ε := by
  simp only [seedOf, bind_assoc, pure_bind]
  exact prEvent_bind_le_of_support h

/-- **The generator's `Bad`.** For a preprocessing computation making at most `Q_pre` queries,
the generator's `Bad` holds on the seed with probability at most
`P² / |S| + Q_pre (1 / (|Salt| |L|) + P / |S|)`: collisions (case 1), and a path input among the
at most `Q_pre` points cached by the preprocessing computation (case 2). -/
theorem prEvent_seedOf_bad_le [Fintype S] [Fintype L] [Fintype Salt]
    (hctx : Function.Injective mkCtx) {State : Type}
    {pre : OracleComp (unifSpec + oracleSpec n S L Salt Ctx) State} {Qpre : ℕ}
    (hpre : IsPreprocessingQueryBound pre Qpre) :
    Pr{let s ← seedOf pre m}[Bad m mkCtx initAcc s.cache s.puzzle s.labels] ≤
      (solvePoints n m : ℝ≥0∞) ^ 2 / Fintype.card S +
        Qpre * ((Fintype.card Salt * Fintype.card L : ℝ≥0∞)⁻¹ +
          solvePoints n m / Fintype.card S) := by
  simp only [Bad]
  refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
  · rw [map_eq_bind_pure_comp]
    refine prEvent_seedOf_bind_le fun z _ => prEvent_bind_le fun salt => prEvent_bind_le fun p => ?_
    simpa [Seed.puzzle, bind_pure_comp] using prEvent_collision_le (m := m) (mkCtx := mkCtx)
      (initAcc := initAcc) (S := S) salt p.1 p.2
  · rw [map_eq_bind_pure_comp]
    refine prEvent_seedOf_bind_le fun z hz => ?_
    let J : ProbComp (Salt × (L × (Fin (n - 1) → L)) × Labels n m S L) :=
      $ᵗ Salt >>= fun salt => $ᵗ (L × (Fin (n - 1) → L)) >>= fun p =>
        $ᵗ Labels n m S L >>= fun ℓ => pure (salt, p, ℓ)
    let T : Set (Point n S L Salt Ctx) := {t | (z.2 t).isSome}
    have hT : (T.encard : ℝ≥0∞) ≤ Qpre :=
      (QueryCache.encard_le_enncard T fun _ ht => ht).trans
        (enncard_le_of_mem_support_run_unifFwdImpl_add_randomOracle hpre hz)
    calc _ = Pr{let w ← J}[∃ v, (z.2 (pathInput m mkCtx initAcc
            (labelPuzzle w.1 w.2.1.1 w.2.1.2 w.2.2) w.2.2 v)).isSome] := by
          simp [J, Seed.puzzle, map_bind, bind_pure_comp]
      _ ≤ Pr{let w ← J}[∃ t ∈ T, ∃ v, t = pathInput m mkCtx initAcc
            (labelPuzzle w.1 w.2.1.1 w.2.1.2 w.2.2) w.2.2 v] :=
          prEvent_mono _ _ _ fun w ⟨v, hv⟩ => ⟨_, hv, v, rfl⟩
      _ ≤ ((Fintype.card Salt * Fintype.card L : ℝ≥0∞)⁻¹ + solvePoints n m / Fintype.card S) *
            T.encard := by
          refine prEvent_exists_mem_le_encard_mul J T _ fun t _ => ?_
          have h := prEvent_eq_pathInput_seed_le (m := m) (initAcc := initAcc) (S := S) hctx t
          simpa [J, map_bind, bind_pure_comp] using h
      _ ≤ _ := by
          rw [mul_comm]
          gcongr

variable {Out : Type}
  {adv : TimeLockPuzzle.TwoPhaseAdversary unifSpec (oracleSpec n S L Salt Ctx) (Puzzle n S L Salt)
    Out}

/-- **Online Bad.** In the ideal experiment for an online phase with outputs of any type, under an
online budget of `Q_on` points, online Bad occurs with probability at most
`Q_on ([n ≥ 2] / |L| + P / |S|)`: resampling every label but the commitment fixes the puzzle, and
the bridge (`prEvent_newHit_le`) applies from the initial state. -/
theorem prEvent_idealOutcomeExperiment_onlineBad_le [Fintype S] [Fintype L] {r Qon : ℕ}
    (hadv : ∀ σ P, IsOnlineQueryBound (adv.online σ P) (r, Qon)) :
    Pr{let res ← idealOutcomeExperiment adv m mkCtx initAcc}[res.onlineBad = true] ≤
      Qon * hitBound n m S L := by
  rw [idealOutcomeExperiment, map_bind]
  refine prEvent_seedOf_bind_le fun z _ => prEvent_bind_le fun salt => prEvent_bind_le fun p => ?_
  simp only [idealOutcomeRest, Functor.map_map, Seed.puzzle]
  rw [← prEvent_uniform_bind_mixLabels ∅]
  refine prEvent_bind_le fun ℓ₀ => ?_
  simp only [labelPuzzle_mixLabels]
  have h := prEvent_newHit_le (mkCtx := mkCtx) (initAcc := initAcc) (labelPuzzle salt p.1 p.2 ℓ₀)
    (adv.online z.1 (labelPuzzle salt p.1 p.2 ℓ₀)) (hadv _ _).isPointQueryBound
    (IdealState.init z.2) ℓ₀
  refine le_trans (prEvent_bind_mono_of_support _ _ _ fun ℓ' _ =>
    prEvent_mono_of_support _ _ _ fun w _ hw => ?_) h
  obtain ⟨e, he, hb⟩ := of_decide_eq_true hw
  exact ⟨e, by simpa using he, hb.hitAt⟩

/-- **Claim 3, for any output.** In the ideal experiment for an online phase with outputs of any
type, for injective `mkCtx` and an adversary making at most `Q_pre` preprocessing queries and at
most `Q_on` online point queries, the generator's `Bad` or online Bad occurs with probability at
most `[n ≥ 2] Q_on / |L| + Q_pre / (|Salt| |L|) + ((Q_pre + Q_on) P + P²) / |S|`, with
`P = solvePoints n m`. The first term is absent when `n = 1`. -/
theorem prEvent_idealOutcomeExperiment_bad_le [Fintype S] [Fintype L] [Fintype Salt]
    (hctx : Function.Injective mkCtx) {Qpre r Qon : ℕ} (hadv : adv.IsQueryBound Qpre (r, Qon)) :
    Pr{let res ← idealOutcomeExperiment adv m mkCtx initAcc}[
        res.genBad = true ∨ res.onlineBad = true] ≤
      (if 2 ≤ n then (Qon : ℝ≥0∞) / Fintype.card L else 0) +
        Qpre / (Fintype.card Salt * Fintype.card L) +
          ((Qpre + Qon) * solvePoints n m + (solvePoints n m : ℝ≥0∞) ^ 2) / Fintype.card S := by
  refine (prEvent_or_le _ _ _).trans ?_
  rw [prEvent_idealOutcomeExperiment_genBad]
  refine (add_le_add (prEvent_seedOf_bad_le hctx hadv.1)
    (prEvent_idealOutcomeExperiment_onlineBad_le hadv.2)).trans (le_of_eq ?_)
  simp only [hitBound, div_eq_mul_inv]
  split_ifs <;> ring

end OutcomeExperiment

section Experiment

variable [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
  [SampleableType S] [SampleableType L] [SampleableType Salt]
  {adv : TimeLockPuzzle.Adversary (oracleSpec n S L Salt Ctx) (Puzzle n S L Salt) S}
  {m : ℕ} {mkCtx : Salt → Ctx} {initAcc : Ctx → S} [NeZero n] [AddCommGroup L]

omit [NeZero n] [AddCommGroup L] in
/-- A bound on an event after each preprocessing run, for the salt, links and labels drawn
after it, bounds the event after the seed. -/
lemma prEvent_seed_bind_le {g : Seed n m S L Salt Ctx adv.State → ProbComp Prop} {ε : ℝ≥0∞}
    (h : ∀ z ∈ support ((simulateQ (oracleSpec n S L Salt Ctx).romImpl adv.preprocess).run ∅),
      prEvent ($ᵗ Salt >>= fun salt => $ᵗ (L × (Fin (n - 1) → L)) >>= fun p =>
        $ᵗ Labels n m S L >>= fun ℓ => g ⟨z.1, z.2, salt, p.1, p.2, ℓ⟩) ≤ ε) :
    prEvent (seed adv m >>= g) ≤ ε :=
  prEvent_seedOf_bind_le h

/-- **Online Bad.** In the ideal experiment, under an online budget of `Q_on` points, online Bad
occurs with probability at most `Q_on ([n ≥ 2] / |L| + P / |S|)`: resampling every label but the
commitment fixes the puzzle, and the bridge (`prEvent_newHit_le`) applies from the initial state. -/
theorem prEvent_idealExperiment_onlineBad_le [Fintype S] [Fintype L] {r Qon : ℕ}
    (hadv : ∀ σ P, IsOnlineQueryBound (adv.online σ P) (r, Qon)) :
    Pr{let res ← idealExperiment adv m mkCtx initAcc}[res.onlineBad = true] ≤
      Qon * hitBound n m S L := by
  rw [idealExperiment_eq_map_toResult, prEvent_map]
  exact prEvent_idealOutcomeExperiment_onlineBad_le hadv

/-- **The generator's `Bad`.** For a preprocessing phase making at most `Q_pre` queries, the
generator's `Bad` holds on the seed with probability at most
`P² / |S| + Q_pre (1 / (|Salt| |L|) + P / |S|)`: collisions (case 1), and a path input among the
at most `Q_pre` points cached by the preprocessing phase (case 2). -/
theorem prEvent_seed_bad_le [Fintype S] [Fintype L] [Fintype Salt]
    (hctx : Function.Injective mkCtx) {Qpre : ℕ}
    (hpre : IsPreprocessingQueryBound adv.preprocess Qpre) :
    Pr{let s ← seed adv m}[Bad m mkCtx initAcc s.cache s.puzzle s.labels] ≤
      (solvePoints n m : ℝ≥0∞) ^ 2 / Fintype.card S +
        Qpre * ((Fintype.card Salt * Fintype.card L : ℝ≥0∞)⁻¹ +
          solvePoints n m / Fintype.card S) :=
  prEvent_seedOf_bad_le hctx hpre

/-- **Claim 3.** In the ideal experiment, for injective `mkCtx` and an adversary making at most
`Q_pre` preprocessing queries and at most `Q_on` online point queries, the generator's `Bad` or
online Bad occurs with probability at most
`[n ≥ 2] Q_on / |L| + Q_pre / (|Salt| |L|) + ((Q_pre + Q_on) P + P²) / |S|`, with
`P = solvePoints n m`. The first term is absent when `n = 1`. -/
theorem prEvent_idealExperiment_bad_le [Fintype S] [Fintype L] [Fintype Salt]
    (hctx : Function.Injective mkCtx) {Qpre r Qon : ℕ} (hadv : adv.IsQueryBound Qpre (r, Qon)) :
    Pr{let res ← idealExperiment adv m mkCtx initAcc}[res.genBad = true ∨ res.onlineBad = true] ≤
      (if 2 ≤ n then (Qon : ℝ≥0∞) / Fintype.card L else 0) +
        Qpre / (Fintype.card Salt * Fintype.card L) +
          ((Qpre + Qon) * solvePoints n m + (solvePoints n m : ℝ≥0∞) ^ 2) / Fintype.card S := by
  rw [idealExperiment_eq_map_toResult, prEvent_map]
  exact prEvent_idealOutcomeExperiment_bad_le hctx hadv

end Experiment

end PointerChainPuzzle
