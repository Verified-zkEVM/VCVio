/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.Ideal
public import VCVio.OracleComp.SimSemantics.StateT.UntilBad

/-!
# The atomic ideal handler of the pointer-chain puzzle

The third game hop of the delay proof of the pointer-chain puzzle: the online phase of the
programmed experiment (`programmedExperiment`), whose lazy random oracle starts from the
programmed cache, is compared with the online phase under an ideal handler that answers the
points of a round from the labels only when they are legitimate.

## The ideal handler

Fix a puzzle `P` and a labelling `ℓ`. A point `t` is *legitimate for* a path value `v` against
a set `R` of reached path values (`IsLegit`) when every predecessor of `v` is in `R` and `t` is
the path input of `v`. The state of the ideal handler (`IdealState`) is the lazy cache, the set
of reached path values, the number of online rounds so far, and the log of the submitted points
(`Submission`), each with its round and the reached set at its submission. A round `ts`
(`idealImpl`) is handled atomically:

* the reached set `R` is read once, when the round is submitted;
* each point legitimate for some path value is answered with that value's label, from the first
  such path value in `PathValue.all` (`legitLabel`); every other point is answered by the lazy
  random oracle from the cache (`idealPoint`), which samples and caches on a miss, so a repeated
  point receives one answer;
* after the whole round, the path values with a legitimate point in the round are added to the
  reached set (`newlyReached`), the round counter goes up by one, and the points are logged
  (`IdealState.afterRound`).

A value reached in a round therefore never makes another point of the same round legitimate.
Uniform queries pass through. The commitment `.commit` is public but is not reached at the start.

## Online Bad and the comparison

A point is *online-bad* (`OnlineBadAt`) when it is the path input of some path value but is
legitimate for none at its submission; `IdealState.OnlineBad` holds when some logged point is.
From a cache off the generator's `Bad`, the ideal handler and the lazy random oracle on the
programmed cache answer every point that is not online-bad alike (`idealPoint_run_bind`), so the
ideal handler is dominated by the programmed one until online Bad or the generator's `Bad`
(`dominatedUntilBad_idealImpl`). The ideal experiment (`idealExperiment`) draws the same `seed` as
the programmed experiment and runs the online phase under the ideal handler from the cache left by
the preprocessing phase, with nothing reached and the counter at `0`; it reports whether the
adversary returns the key label, whether the generator's `Bad` holds, whether online Bad occurred,
and whether the key is reached. The winning probability in the programmed experiment is at most
the winning probability in the ideal experiment plus the probability of either Bad there
(`programmedExperiment_win_le_idealExperiment`).

The log of submissions is kept for the bound on online Bad: each logged point records the round
in which it was submitted and the reached set at that time.
-/

public section

open OracleSpec OracleComp

namespace PointerChainPuzzle

variable {n m : ℕ} {S L Salt Ctx : Type}

/-! ## Legitimacy -/

section Legit

variable (m : ℕ) (mkCtx : Salt → Ctx) (initAcc : Ctx → S) [NeZero n] [AddCommGroup L]

/-- The point `t` is *legitimate for* the path value `v` against the reached set `R` when every
predecessor of `v` is in `R` and `t` is the path input of `v`. -/
@[expose]
def IsLegit (P : Puzzle n S L Salt) (ℓ : Labels n m S L) (R : Finset (PathValue n m))
    (t : Point n S L Salt Ctx) (v : PathValue n m) : Prop :=
  v.preds ⊆ R ∧ t = pathInput m mkCtx initAcc P ℓ v

/-- A point submitted against the reached set `R` is *online-bad* when it is the path input of
some path value but is legitimate for none: every path value with this path input has a
predecessor outside `R`. -/
@[expose]
def OnlineBadAt (P : Puzzle n S L Salt) (ℓ : Labels n m S L) (R : Finset (PathValue n m))
    (t : Point n S L Salt Ctx) : Prop :=
  (∃ v, t = pathInput m mkCtx initAcc P ℓ v) ∧ ∀ v, ¬IsLegit m mkCtx initAcc P ℓ R t v

/-- The label of the path value `v`, read at a point `t` equal to its path input. -/
@[expose]
def labelAt (P : Puzzle n S L Salt) (ℓ : Labels n m S L) {t : Point n S L Salt Ctx}
    {v : PathValue n m} (h : t = pathInput m mkCtx initAcc P ℓ v) :
    (oracleSpec n S L Salt Ctx).Range t :=
  cast ((congrArg (oracleSpec n S L Salt Ctx).Range h).trans
    (range_pathInput m mkCtx initAcc P ℓ v)).symm (ℓ v)

lemma not_onlineBadAt_iff {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {R : Finset (PathValue n m)} {t : Point n S L Salt Ctx} :
    ¬OnlineBadAt m mkCtx initAcc P ℓ R t ↔
      (∃ v, IsLegit m mkCtx initAcc P ℓ R t v) ∨ ∀ v, t ≠ pathInput m mkCtx initAcc P ℓ v := by
  simp only [OnlineBadAt, not_and, not_forall, not_not, ne_eq]
  constructor
  · intro h
    by_cases hv : ∃ v, t = pathInput m mkCtx initAcc P ℓ v
    · exact Or.inl (h hv)
    · exact Or.inr fun v hv' => hv ⟨v, hv'⟩
  · rintro (h | h) hv
    · exact h
    · obtain ⟨v, hv⟩ := hv
      exact absurd hv (h v)

variable [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]

instance (P : Puzzle n S L Salt) (ℓ : Labels n m S L) (R : Finset (PathValue n m))
    (t : Point n S L Salt Ctx) (v : PathValue n m) :
    Decidable (IsLegit m mkCtx initAcc P ℓ R t v) := by
  unfold IsLegit
  infer_instance

instance (P : Puzzle n S L Salt) (ℓ : Labels n m S L) (R : Finset (PathValue n m))
    (t : Point n S L Salt Ctx) : Decidable (OnlineBadAt m mkCtx initAcc P ℓ R t) := by
  unfold OnlineBadAt
  infer_instance

/-- The label answering `t` from the first path value of `vs` for which `t` is legitimate
against `R`, if any. -/
@[expose]
def legitLabelFrom (P : Puzzle n S L Salt) (ℓ : Labels n m S L) (R : Finset (PathValue n m))
    (t : Point n S L Salt Ctx) : List (PathValue n m) → Option ((oracleSpec n S L Salt Ctx).Range t)
  | [] => none
  | v :: vs =>
      if h : IsLegit m mkCtx initAcc P ℓ R t v then some (labelAt m mkCtx initAcc P ℓ h.2)
      else legitLabelFrom P ℓ R t vs

/-- The label answering a legitimate point `t` against `R`: the label of the first path value in
`PathValue.all` for which `t` is legitimate, and `none` if there is none. -/
@[expose]
def legitLabel (P : Puzzle n S L Salt) (ℓ : Labels n m S L) (R : Finset (PathValue n m))
    (t : Point n S L Salt Ctx) : Option ((oracleSpec n S L Salt Ctx).Range t) :=
  legitLabelFrom m mkCtx initAcc P ℓ R t (PathValue.all n m)

variable {m mkCtx initAcc}

lemma legitLabelFrom_eq_none_iff {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {R : Finset (PathValue n m)} {t : Point n S L Salt Ctx} {vs : List (PathValue n m)} :
    legitLabelFrom m mkCtx initAcc P ℓ R t vs = none ↔
      ∀ v ∈ vs, ¬IsLegit m mkCtx initAcc P ℓ R t v := by
  induction vs with
  | nil => simp [legitLabelFrom]
  | cons v vs ih => by_cases h : IsLegit m mkCtx initAcc P ℓ R t v <;> simp [legitLabelFrom, h, ih]

lemma exists_of_legitLabelFrom_eq_some {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {R : Finset (PathValue n m)} {t : Point n S L Salt Ctx} {vs : List (PathValue n m)}
    {a : (oracleSpec n S L Salt Ctx).Range t}
    (h : legitLabelFrom m mkCtx initAcc P ℓ R t vs = some a) :
    ∃ v, ∃ hv : IsLegit m mkCtx initAcc P ℓ R t v, a = labelAt m mkCtx initAcc P ℓ hv.2 := by
  induction vs with
  | nil => simp [legitLabelFrom] at h
  | cons v vs ih =>
      by_cases hv : IsLegit m mkCtx initAcc P ℓ R t v
      · simp only [legitLabelFrom, hv, ↓reduceDIte, Option.some.injEq] at h
        exact ⟨v, hv, h.symm⟩
      · simp only [legitLabelFrom, hv, ↓reduceDIte] at h
        exact ih h

lemma legitLabel_eq_none_iff {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {R : Finset (PathValue n m)} {t : Point n S L Salt Ctx} :
    legitLabel m mkCtx initAcc P ℓ R t = none ↔ ∀ v, ¬IsLegit m mkCtx initAcc P ℓ R t v :=
  legitLabelFrom_eq_none_iff.trans ⟨fun h v => h v (PathValue.mem_all v), fun h v _ => h v⟩

lemma exists_of_legitLabel_eq_some {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {R : Finset (PathValue n m)} {t : Point n S L Salt Ctx}
    {a : (oracleSpec n S L Salt Ctx).Range t} (h : legitLabel m mkCtx initAcc P ℓ R t = some a) :
    ∃ v, ∃ hv : IsLegit m mkCtx initAcc P ℓ R t v, a = labelAt m mkCtx initAcc P ℓ hv.2 :=
  exists_of_legitLabelFrom_eq_some h

variable (m mkCtx initAcc)

/-- The path values reached by the round `ts` submitted against the reached set `R`: those whose
predecessors are all in `R` and whose path input is a point of `ts`. -/
@[expose]
def newlyReached (P : Puzzle n S L Salt) (ℓ : Labels n m S L) (R : Finset (PathValue n m))
    (ts : List (Point n S L Salt Ctx)) : Finset (PathValue n m) :=
  Finset.univ.filter fun v => v.preds ⊆ R ∧ pathInput m mkCtx initAcc P ℓ v ∈ ts

variable {m mkCtx initAcc}

@[simp] lemma mem_newlyReached {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {R : Finset (PathValue n m)} {ts : List (Point n S L Salt Ctx)} {v : PathValue n m} :
    v ∈ newlyReached m mkCtx initAcc P ℓ R ts ↔
      v.preds ⊆ R ∧ pathInput m mkCtx initAcc P ℓ v ∈ ts := by
  simp [newlyReached]

/-- A path value is newly reached by a round exactly when some point of the round is legitimate
for it. -/
lemma mem_newlyReached_iff_exists {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {R : Finset (PathValue n m)} {ts : List (Point n S L Salt Ctx)} {v : PathValue n m} :
    v ∈ newlyReached m mkCtx initAcc P ℓ R ts ↔ ∃ t ∈ ts, IsLegit m mkCtx initAcc P ℓ R t v := by
  rw [mem_newlyReached]
  constructor
  · rintro ⟨hR, ht⟩
    exact ⟨_, ht, hR, rfl⟩
  · rintro ⟨t, ht, hR, rfl⟩
    exact ⟨hR, ht⟩

end Legit

/-! ## The state of the ideal handler -/

/-- A point of an online round, with the number of that round and the set of path values reached
when the round was submitted. -/
structure Submission (n m : ℕ) (S L Salt Ctx : Type) where
  /-- The online round in which the point was submitted, counted from `1`. -/
  round : ℕ
  /-- The path values reached when the round was submitted. -/
  reached : Finset (PathValue n m)
  /-- The submitted point. -/
  point : Point n S L Salt Ctx

/-- The state of the ideal handler: the lazy cache, the reached path values, the number of online
rounds so far, and the log of the submitted points. -/
structure IdealState (n m : ℕ) (S L Salt Ctx : Type) where
  /-- The lazy cache of the random oracle. -/
  cache : (oracleSpec n S L Salt Ctx).QueryCache
  /-- The path values reached so far. -/
  reached : Finset (PathValue n m)
  /-- The number of online rounds so far. -/
  round : ℕ
  /-- The points submitted so far, in order. -/
  log : List (Submission n m S L Salt Ctx)

namespace IdealState

/-- The state at the start of the online phase: the cache `c`, nothing reached, no round, and an
empty log. -/
@[expose]
def init (c : (oracleSpec n S L Salt Ctx).QueryCache) : IdealState n m S L Salt Ctx :=
  ⟨c, ∅, 0, []⟩

@[simp] lemma init_cache (c : (oracleSpec n S L Salt Ctx).QueryCache) :
    (init c : IdealState n m S L Salt Ctx).cache = c := rfl

@[simp] lemma init_reached (c : (oracleSpec n S L Salt Ctx).QueryCache) :
    (init c : IdealState n m S L Salt Ctx).reached = ∅ := rfl

@[simp] lemma init_round (c : (oracleSpec n S L Salt Ctx).QueryCache) :
    (init c : IdealState n m S L Salt Ctx).round = 0 := rfl

@[simp] lemma init_log (c : (oracleSpec n S L Salt Ctx).QueryCache) :
    (init c : IdealState n m S L Salt Ctx).log = [] := rfl

variable (m : ℕ) (mkCtx : Salt → Ctx) (initAcc : Ctx → S) [NeZero n] [AddCommGroup L]
  [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]

/-- The state after the round `ts`, submitted from the state `s` and leaving the cache `c`: the
path values newly reached against the reached set at submission are added, the round counter goes
up by one, and the points are logged with the new round number and the reached set at
submission. -/
@[expose]
def afterRound (P : Puzzle n S L Salt) (ℓ : Labels n m S L) (s : IdealState n m S L Salt Ctx)
    (ts : List (Point n S L Salt Ctx)) (c : (oracleSpec n S L Salt Ctx).QueryCache) :
    IdealState n m S L Salt Ctx where
  cache := c
  reached := s.reached ∪ newlyReached m mkCtx initAcc P ℓ s.reached ts
  round := s.round + 1
  log := s.log ++ ts.map fun t => ⟨s.round + 1, s.reached, t⟩

/-- Online Bad: some logged point was online-bad at its submission. -/
@[expose]
def OnlineBad (P : Puzzle n S L Salt) (ℓ : Labels n m S L) (s : IdealState n m S L Salt Ctx) :
    Prop :=
  ∃ e ∈ s.log, OnlineBadAt m mkCtx initAcc P ℓ e.reached e.point

instance (P : Puzzle n S L Salt) (ℓ : Labels n m S L) (s : IdealState n m S L Salt Ctx) :
    Decidable (s.OnlineBad m mkCtx initAcc P ℓ) := by
  unfold OnlineBad
  infer_instance

variable {m mkCtx initAcc}

@[simp] lemma afterRound_cache {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {s : IdealState n m S L Salt Ctx} {ts : List (Point n S L Salt Ctx)}
    {c : (oracleSpec n S L Salt Ctx).QueryCache} :
    (s.afterRound m mkCtx initAcc P ℓ ts c).cache = c := rfl

@[simp] lemma afterRound_reached {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {s : IdealState n m S L Salt Ctx} {ts : List (Point n S L Salt Ctx)}
    {c : (oracleSpec n S L Salt Ctx).QueryCache} :
    (s.afterRound m mkCtx initAcc P ℓ ts c).reached =
      s.reached ∪ newlyReached m mkCtx initAcc P ℓ s.reached ts := rfl

@[simp] lemma afterRound_round {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {s : IdealState n m S L Salt Ctx} {ts : List (Point n S L Salt Ctx)}
    {c : (oracleSpec n S L Salt Ctx).QueryCache} :
    (s.afterRound m mkCtx initAcc P ℓ ts c).round = s.round + 1 := rfl

@[simp] lemma afterRound_log {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {s : IdealState n m S L Salt Ctx} {ts : List (Point n S L Salt Ctx)}
    {c : (oracleSpec n S L Salt Ctx).QueryCache} :
    (s.afterRound m mkCtx initAcc P ℓ ts c).log =
      s.log ++ ts.map fun t => ⟨s.round + 1, s.reached, t⟩ := rfl

/-- Online Bad persists across a round. -/
lemma OnlineBad.afterRound {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {s : IdealState n m S L Salt Ctx} (h : s.OnlineBad m mkCtx initAcc P ℓ)
    (ts : List (Point n S L Salt Ctx)) (c : (oracleSpec n S L Salt Ctx).QueryCache) :
    (s.afterRound m mkCtx initAcc P ℓ ts c).OnlineBad m mkCtx initAcc P ℓ := by
  obtain ⟨e, he, hb⟩ := h
  exact ⟨e, List.mem_append_left _ he, hb⟩

/-- A round holding an online-bad point raises online Bad. -/
lemma onlineBad_afterRound_of_mem {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {s : IdealState n m S L Salt Ctx} {ts : List (Point n S L Salt Ctx)}
    {t : Point n S L Salt Ctx} (ht : t ∈ ts) (hb : OnlineBadAt m mkCtx initAcc P ℓ s.reached t)
    (c : (oracleSpec n S L Salt Ctx).QueryCache) :
    (s.afterRound m mkCtx initAcc P ℓ ts c).OnlineBad m mkCtx initAcc P ℓ :=
  ⟨⟨s.round + 1, s.reached, t⟩, List.mem_append_right _ (List.mem_map_of_mem ht), hb⟩

end IdealState

/-! ## The ideal handler -/

section Handler

variable (m : ℕ) (mkCtx : Salt → Ctx) (initAcc : Ctx → S) [NeZero n] [AddCommGroup L]
  [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
  [SampleableType S] [SampleableType L]

/-- One point of a round submitted against the reached set `R`, on the lazy cache: a point
legitimate for some path value is answered with that value's label (`legitLabel`) and leaves the
cache unchanged; every other point is answered by the lazy random oracle, which samples and caches
on a miss. -/
@[expose]
def idealPoint (P : Puzzle n S L Salt) (ℓ : Labels n m S L) (R : Finset (PathValue n m)) :
    QueryImpl (oracleSpec n S L Salt Ctx)
      (StateT (oracleSpec n S L Salt Ctx).QueryCache ProbComp) := fun t =>
  match legitLabel m mkCtx initAcc P ℓ R t with
  | some a => pure a
  | none => (oracleSpec n S L Salt Ctx).randomOracle t

/-- The atomic ideal handler of the online phase. Uniform queries pass through. A round `ts` reads
the reached set once, answers its points one after the other with `idealPoint` against that
reached set on the shared cache, and only then adds the newly reached path values, increments the
round counter and logs the points (`IdealState.afterRound`). -/
@[expose]
def idealImpl (P : Puzzle n S L Salt) (ℓ : Labels n m S L) :
    QueryImpl (unifSpec + (oracleSpec n S L Salt Ctx).batch)
      (StateT (IdealState n m S L Salt Ctx) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (IdealState n m S L Salt Ctx) ProbComp) +
    fun ts => StateT.mk fun s : IdealState n m S L Salt Ctx =>
      (fun z => (z.1, s.afterRound m mkCtx initAcc P ℓ ts z.2)) <$>
        (QueryImpl.batch (idealPoint m mkCtx initAcc P ℓ s.reached) ts).run s.cache

variable {m mkCtx initAcc}

lemma idealPoint_of_legitLabel_eq_some {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {R : Finset (PathValue n m)} {t : Point n S L Salt Ctx}
    {a : (oracleSpec n S L Salt Ctx).Range t} (h : legitLabel m mkCtx initAcc P ℓ R t = some a) :
    idealPoint m mkCtx initAcc P ℓ R t = pure a := by
  simp only [idealPoint, h]

lemma idealPoint_of_legitLabel_eq_none {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {R : Finset (PathValue n m)} {t : Point n S L Salt Ctx}
    (h : legitLabel m mkCtx initAcc P ℓ R t = none) :
    idealPoint m mkCtx initAcc P ℓ R t = (oracleSpec n S L Salt Ctx).randomOracle t := by
  simp only [idealPoint, h]

/-- A point already answered is answered again with the same answer, leaving the cache: a
repeated point of a round, or of a later round against the same reached set, gets one answer. -/
lemma idealPoint_run_of_mem_support {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {R : Finset (PathValue n m)} {t : Point n S L Salt Ctx}
    {c : (oracleSpec n S L Salt Ctx).QueryCache}
    {z : (oracleSpec n S L Salt Ctx).Range t × (oracleSpec n S L Salt Ctx).QueryCache}
    (hz : z ∈ support ((idealPoint m mkCtx initAcc P ℓ R t).run c)) :
    (idealPoint m mkCtx initAcc P ℓ R t).run z.2 = pure z :=
  match h : legitLabel m mkCtx initAcc P ℓ R t with
  | some a => by
      rw [idealPoint_of_legitLabel_eq_some h, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      rw [idealPoint_of_legitLabel_eq_some h, StateT.run_pure]
  | none => by
      rw [idealPoint_of_legitLabel_eq_none h] at hz ⊢
      exact QueryImpl.withCaching_run_some _ (QueryImpl.withCaching_run_caches _ _ _ z hz)

lemma idealImpl_inl_run (P : Puzzle n S L Salt) (ℓ : Labels n m S L) (k : ℕ)
    (s : IdealState n m S L Salt Ctx) :
    (idealImpl m mkCtx initAcc P ℓ (.inl k)).run s =
      (fun u => (u, s)) <$> (unifSpec.query k : ProbComp (Fin (k + 1))) := by
  simp [idealImpl, map_eq_bind_pure_comp]

lemma idealImpl_inr_run (P : Puzzle n S L Salt) (ℓ : Labels n m S L)
    (ts : List (Point n S L Salt Ctx)) (s : IdealState n m S L Salt Ctx) :
    (idealImpl m mkCtx initAcc P ℓ (.inr ts)).run s =
      (fun z => (z.1, s.afterRound m mkCtx initAcc P ℓ ts z.2)) <$>
        (QueryImpl.batch (idealPoint m mkCtx initAcc P ℓ s.reached) ts).run s.cache := rfl

/-- A uniform query leaves the state of the ideal handler unchanged. -/
lemma eq_of_mem_support_idealImpl_inl {P : Puzzle n S L Salt} {ℓ : Labels n m S L} {k : ℕ}
    {s : IdealState n m S L Salt Ctx} {z : Fin (k + 1) × IdealState n m S L Salt Ctx}
    (hz : z ∈ support ((idealImpl m mkCtx initAcc P ℓ (.inl k)).run s)) : z.2 = s := by
  rw [idealImpl_inl_run, support_map] at hz
  obtain ⟨_, _, rfl⟩ := hz
  rfl

/-- After a round, the state of the ideal handler is `IdealState.afterRound` of the state before,
for some cache. -/
lemma exists_of_mem_support_idealImpl_inr {P : Puzzle n S L Salt} {ℓ : Labels n m S L}
    {ts : List (Point n S L Salt Ctx)} {s : IdealState n m S L Salt Ctx}
    {z : (oracleSpec n S L Salt Ctx).batch.Range ts × IdealState n m S L Salt Ctx}
    (hz : z ∈ support ((idealImpl m mkCtx initAcc P ℓ (.inr ts)).run s)) :
    ∃ c, z.2 = s.afterRound m mkCtx initAcc P ℓ ts c := by
  rw [idealImpl_inr_run, support_map] at hz
  obtain ⟨w, _, rfl⟩ := hz
  exact ⟨w.2, rfl⟩

end Handler

/-! ## The ideal handler against the programmed cache

Off the generator's `Bad`, the programmed cache answers the path input of every path value with
its label and agrees with the cache it was programmed over everywhere else. A point that is not
online-bad is either legitimate, and answered with the label of its path value by both handlers,
or the path input of no path value, and answered by the lazy random oracle from caches that agree
there. -/

section Compare

variable {m : ℕ} {mkCtx : Salt → Ctx} {initAcc : Ctx → S} [NeZero n] [AddCommGroup L]
  [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
  {P : Puzzle n S L Salt} {ℓ : Labels n m S L}

/-- Programming the labels commutes with caching an answer at a point that is the path input of
none of the programmed path values. -/
lemma programCache_cacheQuery {vs : List (PathValue n m)} {t : Point n S L Salt Ctx}
    (h : ∀ w ∈ vs, pathInput m mkCtx initAcc P ℓ w ≠ t) (u : (oracleSpec n S L Salt Ctx).Range t)
    (c : (oracleSpec n S L Salt Ctx).QueryCache) :
    programCache m mkCtx initAcc P ℓ vs (c.cacheQuery t u) =
      (programCache m mkCtx initAcc P ℓ vs c).cacheQuery t u := by
  induction vs generalizing c with
  | nil => rfl
  | cons w ws ih =>
      rw [programCache, programCache, QueryCache.cacheQuery_comm c (h w List.mem_cons_self).symm,
        ih fun v hv => h v (List.mem_cons_of_mem _ hv)]

/-- The programmed cache commutes with caching an answer at a point that is the path input of no
path value. -/
lemma programmedCache_cacheQuery {t : Point n S L Salt Ctx}
    (h : ∀ w, t ≠ pathInput m mkCtx initAcc P ℓ w) (u : (oracleSpec n S L Salt Ctx).Range t)
    (c : (oracleSpec n S L Salt Ctx).QueryCache) :
    programmedCache m mkCtx initAcc (c.cacheQuery t u) P ℓ =
      (programmedCache m mkCtx initAcc c P ℓ).cacheQuery t u :=
  programCache_cacheQuery (fun w _ => (h w).symm) u c

/-- The programmed cache agrees with the cache it was programmed over at a point that is the path
input of no path value. -/
lemma programmedCache_apply_of_forall_ne {t : Point n S L Salt Ctx}
    (h : ∀ w, t ≠ pathInput m mkCtx initAcc P ℓ w) (c : (oracleSpec n S L Salt Ctx).QueryCache) :
    programmedCache m mkCtx initAcc c P ℓ t = c t :=
  programCache_apply_of_forall_ne m mkCtx initAcc P ℓ (fun w _ => (h w).symm) c

/-- Caching an answer at a point that is the path input of no path value keeps the generator's
`Bad` false. -/
lemma not_bad_cacheQuery {c : (oracleSpec n S L Salt Ctx).QueryCache}
    (hc : ¬Bad m mkCtx initAcc c P ℓ) {t : Point n S L Salt Ctx}
    (h : ∀ w, t ≠ pathInput m mkCtx initAcc P ℓ w) (u : (oracleSpec n S L Salt Ctx).Range t) :
    ¬Bad m mkCtx initAcc (c.cacheQuery t u) P ℓ := by
  rintro (hb | ⟨v, hv⟩)
  · exact hc (Or.inl hb)
  · rw [QueryCache.cacheQuery_of_ne _ _ (h v).symm] at hv
    exact hc (Or.inr ⟨v, hv⟩)

variable [SampleableType S] [SampleableType L]

/-- **One point.** From a cache `c` off the generator's `Bad`, a point that is not online-bad is
answered alike by the ideal handler on `c` and by the lazy random oracle on the programmed cache:
any two continuations that agree on caches off `Bad`, read through the programmed cache, give the
same computation. -/
lemma idealPoint_run_bind {β : Type} {R : Finset (PathValue n m)} {t : Point n S L Salt Ctx}
    (ht : ¬OnlineBadAt m mkCtx initAcc P ℓ R t) {c : (oracleSpec n S L Salt Ctx).QueryCache}
    (hc : ¬Bad m mkCtx initAcc c P ℓ)
    (k k' : (oracleSpec n S L Salt Ctx).Range t × (oracleSpec n S L Salt Ctx).QueryCache →
      ProbComp β)
    (hk : ∀ u c', ¬Bad m mkCtx initAcc c' P ℓ →
      k (u, c') = k' (u, programmedCache m mkCtx initAcc c' P ℓ)) :
    (idealPoint m mkCtx initAcc P ℓ R t).run c >>= k =
      ((oracleSpec n S L Salt Ctx).randomOracle t).run (programmedCache m mkCtx initAcc c P ℓ) >>=
        k' := by
  rcases hl : legitLabel m mkCtx initAcc P ℓ R t with _ | a
  · have hnone : ∀ w, t ≠ pathInput m mkCtx initAcc P ℓ w :=
      ((not_onlineBadAt_iff m mkCtx initAcc).mp ht).resolve_left fun ⟨v, hv⟩ =>
        legitLabel_eq_none_iff.mp hl v hv
    rw [idealPoint_of_legitLabel_eq_none hl, randomOracle.run_eq, randomOracle.run_eq,
      programmedCache_apply_of_forall_ne hnone]
    rcases hct : c t with _ | u
    · simp only [bind_assoc, pure_bind]
      refine congrArg _ (funext fun u => ?_)
      rw [← programmedCache_cacheQuery hnone]
      exact hk u _ (not_bad_cacheQuery hc hnone u)
    · simp only [pure_bind]
      exact hk u c hc
  · obtain ⟨v, ⟨_, htv⟩, rfl⟩ := exists_of_legitLabel_eq_some hl
    rw [idealPoint_of_legitLabel_eq_some hl, StateT.run_pure, pure_bind, randomOracle.run_eq]
    subst htv
    rw [programmedCache_pathInput m mkCtx initAcc hc v, pure_bind]
    exact hk _ c hc

/-- **One round.** From a cache off the generator's `Bad`, a round none of whose points is
online-bad against `R` is answered alike by the ideal handler and by the lazy random oracle on the
programmed cache. -/
lemma batch_idealPoint_run_bind {β : Type} {R : Finset (PathValue n m)}
    {ts : List (Point n S L Salt Ctx)} (hts : ∀ t ∈ ts, ¬OnlineBadAt m mkCtx initAcc P ℓ R t)
    {c : (oracleSpec n S L Salt Ctx).QueryCache} (hc : ¬Bad m mkCtx initAcc c P ℓ)
    (k k' : (oracleSpec n S L Salt Ctx).batch.Range ts × (oracleSpec n S L Salt Ctx).QueryCache →
      ProbComp β)
    (hk : ∀ us c', ¬Bad m mkCtx initAcc c' P ℓ →
      k (us, c') = k' (us, programmedCache m mkCtx initAcc c' P ℓ)) :
    (QueryImpl.batch (idealPoint m mkCtx initAcc P ℓ R) ts).run c >>= k =
      (QueryImpl.batch (oracleSpec n S L Salt Ctx).randomOracle ts).run
        (programmedCache m mkCtx initAcc c P ℓ) >>= k' := by
  induction ts generalizing c with
  | nil =>
      simp only [QueryImpl.batch_nil, StateT.run_pure, pure_bind]
      exact hk _ c hc
  | cons t ts ih =>
      simp only [QueryImpl.batch_cons, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
      exact idealPoint_run_bind (hts t List.mem_cons_self) hc _ _ fun u c' hc' =>
        ih (fun t' ht' => hts t' (List.mem_cons_of_mem _ ht')) hc' _ _ fun us c'' hc'' =>
          hk _ c'' hc''

/-- A round none of whose points is online-bad keeps the generator's `Bad` false. -/
lemma not_bad_of_mem_support_batch_idealPoint {R : Finset (PathValue n m)}
    {ts : List (Point n S L Salt Ctx)} (hts : ∀ t ∈ ts, ¬OnlineBadAt m mkCtx initAcc P ℓ R t)
    {c : (oracleSpec n S L Salt Ctx).QueryCache} (hc : ¬Bad m mkCtx initAcc c P ℓ)
    {z : (oracleSpec n S L Salt Ctx).batch.Range ts × (oracleSpec n S L Salt Ctx).QueryCache}
    (hz : z ∈ support ((QueryImpl.batch (idealPoint m mkCtx initAcc P ℓ R) ts).run c)) :
    ¬Bad m mkCtx initAcc z.2 P ℓ := by
  induction ts generalizing c with
  | nil =>
      rw [QueryImpl.batch_nil, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hc
  | cons t ts ih =>
      simp only [QueryImpl.batch_cons, StateT.run_bind, StateT.run_pure, support_bind,
        support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hz
      obtain ⟨w, hw, w', hw', rfl⟩ := hz
      refine ih (fun t' ht' => hts t' (List.mem_cons_of_mem _ ht')) ?_ hw'
      rcases hl : legitLabel m mkCtx initAcc P ℓ R t with _ | a
      · have hnone : ∀ v, t ≠ pathInput m mkCtx initAcc P ℓ v :=
          ((not_onlineBadAt_iff m mkCtx initAcc).mp (hts t List.mem_cons_self)).resolve_left
            fun ⟨v, hv⟩ => legitLabel_eq_none_iff.mp hl v hv
        rw [idealPoint_of_legitLabel_eq_none hl] at hw
        rw [QueryImpl.withCaching_run_eq_cacheQuery _ hw]
        exact not_bad_cacheQuery hc hnone _
      · rw [idealPoint_of_legitLabel_eq_some hl, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hw
        subst hw
        exact hc

/-- The handler of the programmed experiment's online phase: uniform queries pass through, and
each round is answered point by point by the lazy random oracle. -/
local notation "H" => unifFwdImpl (oracleSpec n S L Salt Ctx) +
  QueryImpl.batch (OracleSpec.randomOracle (spec := oracleSpec n S L Salt Ctx))

variable (m mkCtx initAcc P ℓ) in
/-- The invariant of the comparison, for the preprocessing cache `c₀`: online Bad, or the
generator's `Bad` for `c₀`, or the cache is off the generator's `Bad`. -/
@[expose]
def CompareInv (c₀ : (oracleSpec n S L Salt Ctx).QueryCache) (s : IdealState n m S L Salt Ctx) :
    Prop :=
  s.OnlineBad m mkCtx initAcc P ℓ ∨ Bad m mkCtx initAcc c₀ P ℓ ∨ ¬Bad m mkCtx initAcc s.cache P ℓ

variable (m mkCtx initAcc P ℓ) in
/-- The bad event of the comparison, for the preprocessing cache `c₀`: online Bad, or the
generator's `Bad` for `c₀`. -/
@[expose]
def CompareBad (c₀ : (oracleSpec n S L Salt Ctx).QueryCache) (s : IdealState n m S L Salt Ctx) :
    Prop :=
  s.OnlineBad m mkCtx initAcc P ℓ ∨ Bad m mkCtx initAcc c₀ P ℓ

lemma preservesInv_idealImpl_compareBad (c₀ : (oracleSpec n S L Salt Ctx).QueryCache) :
    QueryImpl.PreservesInv (idealImpl m mkCtx initAcc P ℓ) (CompareBad m mkCtx initAcc P ℓ c₀) := by
  rintro (k | ts) s hs z hz
  · rwa [eq_of_mem_support_idealImpl_inl hz]
  · obtain ⟨c, hc⟩ := exists_of_mem_support_idealImpl_inr hz
    rw [hc]
    exact hs.imp (fun h => h.afterRound ts c) id

lemma preservesInv_idealImpl_compareInv (c₀ : (oracleSpec n S L Salt Ctx).QueryCache) :
    QueryImpl.PreservesInv (idealImpl m mkCtx initAcc P ℓ) (CompareInv m mkCtx initAcc P ℓ c₀) := by
  rintro (k | ts) s hs z hz
  · rwa [eq_of_mem_support_idealImpl_inl hz]
  · rw [idealImpl_inr_run, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rcases hs with hs | hs | hs
    · exact Or.inl (hs.afterRound ts w.2)
    · exact Or.inr (Or.inl hs)
    · by_cases hts : ∃ t ∈ ts, OnlineBadAt m mkCtx initAcc P ℓ s.reached t
      · obtain ⟨t, ht, hb⟩ := hts
        exact Or.inl (IdealState.onlineBad_afterRound_of_mem ht hb w.2)
      · simp only [not_exists, not_and] at hts
        exact Or.inr (Or.inr (not_bad_of_mem_support_batch_idealPoint hts hs hw))

/-- **Domination until Bad.** The ideal handler is dominated by the handler of the programmed
experiment until online Bad or the generator's `Bad` for `c₀`, through the map sending a state to
the programmed cache over its cache. -/
theorem dominatedUntilBad_idealImpl (c₀ : (oracleSpec n S L Salt Ctx).QueryCache) :
    QueryImpl.DominatedUntilBad (idealImpl m mkCtx initAcc P ℓ) H
      (fun s => programmedCache m mkCtx initAcc s.cache P ℓ)
      (CompareInv m mkCtx initAcc P ℓ c₀) (CompareBad m mkCtx initAcc P ℓ c₀) := by
  rintro (k | ts) s hinv hbad Q
  · rw [idealImpl_inl_run, prEvent_map]
    have h : ((H) (.inl k)).run (programmedCache m mkCtx initAcc s.cache P ℓ) =
        (fun u => (u, programmedCache m mkCtx initAcc s.cache P ℓ)) <$>
          (unifSpec.query k : ProbComp (Fin (k + 1))) := by
      simp [unifFwdImpl, map_eq_bind_pure_comp]
    rw [h, prEvent_map]
    exact prEvent_mono _ _ _ fun _ h => h.1
  · have hc : ¬Bad m mkCtx initAcc s.cache P ℓ := by
      rcases hinv with h | h | h
      · exact absurd (Or.inl h) hbad
      · exact absurd (Or.inr h) hbad
      · exact h
    by_cases hts : ∃ t ∈ ts, OnlineBadAt m mkCtx initAcc P ℓ s.reached t
    · obtain ⟨t, ht, hb⟩ := hts
      refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => ?_) zero_le
      obtain ⟨c, hc⟩ := exists_of_mem_support_idealImpl_inr hz
      exact h.2 (Or.inl (hc ▸ IdealState.onlineBad_afterRound_of_mem ht hb c))
    · simp only [not_exists, not_and] at hts
      refine (prEvent_mono _ _ _ fun _ h => h.1).trans (le_of_eq ?_)
      have h := batch_idealPoint_run_bind hts hc
        (fun w => pure (w.1, programmedCache m mkCtx initAcc w.2 P ℓ)) pure fun _ _ _ => rfl
      rw [bind_pure, bind_pure_comp] at h
      rw [idealImpl_inr_run, prEvent_map, QueryImpl.add_apply_inr, ← h, prEvent_map]
      rfl

end Compare

/-! ## The ideal experiment -/

/-- The outcome of the ideal experiment. -/
structure IdealResult where
  /-- The online phase returned the key label. -/
  win : Bool
  /-- The generator's `Bad` holds for the preprocessing cache, the puzzle and the labels. -/
  genBad : Bool
  /-- Some point of an online round was online-bad at its submission. -/
  onlineBad : Bool
  /-- The key is reached at the end of the online phase. -/
  keyReached : Bool

section Experiment

variable [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
  [SampleableType S] [SampleableType L]
  (adv : TimeLockPuzzle.Adversary (oracleSpec n S L Salt Ctx) (Puzzle n S L Salt) S)
  (m : ℕ) (mkCtx : Salt → Ctx) (initAcc : Ctx → S) [NeZero n] [AddCommGroup L]

/-- The online phase of the ideal experiment after the seed `s`: the online phase of the adversary
runs under the ideal handler for the puzzle and the labels of `s`, from the cache left by the
preprocessing phase, with nothing reached and the round counter at `0`. -/
@[expose]
def idealRest (s : Seed n m S L Salt Ctx adv.State) : ProbComp IdealResult :=
  (fun z => ⟨decide (z.1 = s.labels .key), decide (Bad m mkCtx initAcc s.cache s.puzzle s.labels),
      decide (z.2.OnlineBad m mkCtx initAcc s.puzzle s.labels), decide (.key ∈ z.2.reached)⟩) <$>
    (simulateQ (idealImpl m mkCtx initAcc s.puzzle s.labels) (adv.online s.state s.puzzle)).run
      (IdealState.init s.cache)

/-- The ideal experiment: draw the `seed` of the programmed experiment, then run the online phase
under the ideal handler (`idealRest`). -/
@[expose]
def idealExperiment [SampleableType Salt] : ProbComp IdealResult :=
  seed adv m >>= idealRest adv m mkCtx initAcc

omit [NeZero n] [AddCommGroup L] in
/-- Winning in the online phase of the programmed experiment, from a cache `c`, is the event that
the lazy random oracle answering each round point by point leads the online phase to `key`. -/
lemma prEvent_onlineWin (σ : adv.State) (P : Puzzle n S L Salt) (key : S)
    (c : (oracleSpec n S L Salt Ctx).QueryCache) :
    Pr{let b ← onlineWin adv σ P key c}[b = true] =
      Pr{let z ← (simulateQ (unifFwdImpl (oracleSpec n S L Salt Ctx) +
          QueryImpl.batch (oracleSpec n S L Salt Ctx).randomOracle) (adv.online σ P)).run c}[
        z.1 = key] := by
  have h : onlineWin adv σ P key c = (fun z => decide (z.1 = key)) <$>
      (simulateQ (unifFwdImpl (oracleSpec n S L Salt Ctx) +
        QueryImpl.batch (oracleSpec n S L Salt Ctx).randomOracle) (adv.online σ P)).run c := by
    simp [onlineWin, OracleSpec.simulateQ_romImpl_simulateQ_unbatch, StateT.run'_eq]
  rw [h, prEvent_map]
  simp only [decide_eq_true_eq]

/-- **Until Bad, after the seed.** For a preprocessing cache `c`, a puzzle `P` and labels `ℓ`, the
online phase wins from the programmed cache with probability at most that of winning, online Bad
or the generator's `Bad` for `c` under the ideal handler from `c`. -/
theorem prEvent_onlineWin_le (σ : adv.State) (P : Puzzle n S L Salt) (ℓ : Labels n m S L)
    (c : (oracleSpec n S L Salt Ctx).QueryCache) :
    Pr{let b ← onlineWin adv σ P (ℓ .key) (programmedCache m mkCtx initAcc c P ℓ)}[b = true] ≤
      Pr{let z ← (simulateQ (idealImpl m mkCtx initAcc P ℓ) (adv.online σ P)).run
          (IdealState.init c)}[
        z.1 = ℓ .key ∨ z.2.OnlineBad m mkCtx initAcc P ℓ ∨ Bad m mkCtx initAcc c P ℓ] := by
  rw [prEvent_onlineWin]
  have hinit : CompareInv m mkCtx initAcc P ℓ c (IdealState.init c) := by
    by_cases h : Bad m mkCtx initAcc c P ℓ
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  exact (dominatedUntilBad_idealImpl c).prEvent_simulateQ_run_le_map_or_bad
    (preservesInv_idealImpl_compareInv c) (preservesInv_idealImpl_compareBad c) (adv.online σ P)
    (IdealState.init c) hinit fun z => z.1 = ℓ .key

variable [SampleableType Salt]

/-- **Until-Bad comparison.** The winning probability in the programmed experiment is at most the
winning probability in the ideal experiment plus the probability, in the ideal experiment, that the
generator's `Bad` holds or online Bad occurs. -/
theorem programmedExperiment_win_le_idealExperiment :
    Pr{let r ← programmedExperiment adv m mkCtx initAcc}[r.1 = true] ≤
      Pr{let r ← idealExperiment adv m mkCtx initAcc}[r.win = true] +
        Pr{let r ← idealExperiment adv m mkCtx initAcc}[r.genBad = true ∨ r.onlineBad = true] := by
  rw [prEvent_programmedExperiment_win]
  refine (prEvent_bind_mono_of_forall_le _ _ _ _
    (fun r : IdealResult => r.win = true ∨ (r.genBad = true ∨ r.onlineBad = true))
    fun s => ?_).trans (prEvent_or_le _ _ _)
  have hrest : Prod.fst <$> programmedRest adv m mkCtx initAcc s =
      onlineWin adv s.state s.puzzle (s.labels .key)
        (programmedCache m mkCtx initAcc s.cache s.puzzle s.labels) := by
    rw [programmedRest, Functor.map_map]
    exact id_map _
  rw [hrest, idealRest, prEvent_map]
  refine (prEvent_onlineWin_le adv m mkCtx initAcc _ _ _ _).trans (le_of_eq ?_)
  refine prEvent_congr _ _ _ fun z => ?_
  simp only [decide_eq_true_eq]
  tauto

/-- The generator's `Bad` in the ideal experiment is `Bad` on the seed. -/
lemma prEvent_idealExperiment_genBad :
    Pr{let r ← idealExperiment adv m mkCtx initAcc}[r.genBad = true] =
      Pr{let s ← seed adv m}[Bad m mkCtx initAcc s.cache s.puzzle s.labels] := by
  rw [idealExperiment, map_bind, map_eq_bind_pure_comp]
  refine prEvent_bind_congr_of_support _ _ _ fun s _ => ?_
  simp only [idealRest, Functor.map_map, Function.comp_def, prEvent_def,
    OracleComp.evalDist_map_const, evalDist_pure, decide_eq_true_eq]

/-- **Programming and until Bad.** The delay advantage of the pointer-chain puzzle is at most the
winning probability in the ideal experiment, plus the probability there of the generator's `Bad`
or online Bad, plus the probability there of the generator's `Bad`. -/
theorem delayAdvantage_scheme_le_idealExperiment [Finite Ctx] :
    (scheme n m mkCtx initAcc).delayAdvantage adv ≤
      Pr{let r ← idealExperiment adv m mkCtx initAcc}[r.win = true] +
        Pr{let r ← idealExperiment adv m mkCtx initAcc}[r.genBad = true ∨ r.onlineBad = true] +
          Pr{let r ← idealExperiment adv m mkCtx initAcc}[r.genBad = true] := by
  rw [← delayAdvantage_maskedScheme m mkCtx initAcc adv]
  refine (delayAdvantage_maskedScheme_le adv m mkCtx initAcc).trans ?_
  rw [prEvent_programmedExperiment_bad, ← prEvent_idealExperiment_genBad]
  exact add_le_add_left (programmedExperiment_win_le_idealExperiment adv m mkCtx initAcc) _

end Experiment

end PointerChainPuzzle
