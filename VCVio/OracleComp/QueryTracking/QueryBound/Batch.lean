/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.SimSemantics.Batch

/-!
# Query budgets for rounds of parallel queries

Budgets for a two-phase adversary, counted by the path-wise `IsQueryBound` and `IsQueryBoundP`.
Every budget is stated on a sum and charges only its right summand. The preprocessing phase runs
on `unifSpec + spec`, so its local coins are free. The online phase runs on `free + spec.batch`
for any oracles `free`, whose queries cost nothing: local coins `unifSpec` in a delay game, and in
a hiding game local coins together with the challenger's encryption oracle.

* Preprocessing, on `unifSpec + spec`: `IsPreprocessingQueryBound oa Q` allows at most `Q`
  queries to `spec`.
* Online, on `free + spec.batch`: `IsOnlineQueryBound oa (r, q)` allows at most `r` rounds holding
  at most `q` points in total. A round `ts` needs `0 < r` and `ts.length ≤ q`, and costs
  `(1, ts.length)`.
* Points only, on `free + spec.batch`: `IsPointQueryBound oa q` allows at most `q` points in total,
  in any number of rounds.

## Main statements

* `IsPointQueryBound.isQueryBoundP_simulateQ_unbatch`: rewriting the rounds of a program with
  point budget `q` as single queries gives a program making at most `q` queries to `spec`.
* `IsOnlineQueryBound.simulateQ_of_step`: a handler sending each query to `free` to a program with
  no rounds, and each round to a program with one round of at most as many points, preserves the
  online budget.
* `IsOnlineQueryBound.liftComp`: lifting a program through a `SubSpec` inclusion preserves the
  online budget.
* `isOnlineQueryBound_liftComp`: a program on oracles inside `free`, such as local coins, submits
  no rounds.
* `isOnlineQueryBound_queryRound₂`, `isOnlineQueryBound_queryRound`,
  `isOnlineQueryBound_queryPoint`: each of the typed rounds costs one round and one point per
  point it holds.
-/

public section

open OracleSpec

namespace OracleComp

variable {τ ι : Type} {free : OracleSpec.{0, 0} τ} {spec : OracleSpec.{0, 0} ι} {α β : Type}

/-! ## Preprocessing budget -/

/-- `oa` makes at most `Q` queries to `spec`, the queries at indices `t` with `t.isRight`; its
uniform queries are free. -/
abbrev IsPreprocessingQueryBound (oa : OracleComp (unifSpec + spec) α) (Q : ℕ) : Prop :=
  IsQueryBoundP oa (·.isRight) Q

/-! ## Online budget -/

/-- Whether a query fits the online budget `(r, q)`: queries to the free summand always fit, and a
round `ts` needs a round left and room for its `ts.length` points. -/
@[expose]
def onlineCanQuery : τ ⊕ List ι → ℕ × ℕ → Prop
  | .inl _, _ => True
  | .inr ts, b => 0 < b.1 ∧ ts.length ≤ b.2

/-- The online budget left after a query: queries to the free summand cost nothing, and a round
`ts` costs one round and `ts.length` points. -/
@[expose]
def onlineCost : τ ⊕ List ι → ℕ × ℕ → ℕ × ℕ
  | .inl _, b => b
  | .inr ts, b => (b.1 - 1, b.2 - ts.length)

/-- The online budget a single query uses: nothing for a query to the free summand, and one round
of `ts.length` points for a round `ts`. -/
@[expose]
def onlineStep : τ ⊕ List ι → ℕ × ℕ
  | .inl _ => (0, 0)
  | .inr ts => (1, ts.length)

@[simp] lemma onlineCanQuery_inl (n : τ) (b : ℕ × ℕ) :
    onlineCanQuery (ι := ι) (.inl n) b := trivial

@[simp] lemma onlineCanQuery_inr (ts : List ι) (b : ℕ × ℕ) :
    onlineCanQuery (τ := τ) (.inr ts) b ↔ 0 < b.1 ∧ ts.length ≤ b.2 := Iff.rfl

@[simp] lemma onlineCost_inl (n : τ) (b : ℕ × ℕ) : onlineCost (ι := ι) (.inl n) b = b := rfl

@[simp] lemma onlineCost_inr (ts : List ι) (b : ℕ × ℕ) :
    onlineCost (τ := τ) (.inr ts) b = (b.1 - 1, b.2 - ts.length) := rfl

@[simp] lemma onlineStep_inl (n : τ) : onlineStep (ι := ι) (.inl n) = (0, 0) := rfl

@[simp] lemma onlineStep_inr (ts : List ι) : onlineStep (τ := τ) (.inr ts) = (1, ts.length) :=
  rfl

/-- `oa` submits at most `r` rounds of parallel queries to `spec`, holding at most `q` points in
total, on every path; its queries to `free` are free. -/
abbrev IsOnlineQueryBound (oa : OracleComp (free + spec.batch) α) (b : ℕ × ℕ) : Prop :=
  IsQueryBound oa b onlineCanQuery onlineCost

/-- The number of points a single query submits: none for a query to the free summand, and
`ts.length` for a round `ts`. -/
@[expose]
def pointCount : τ ⊕ List ι → ℕ
  | .inl _ => 0
  | .inr ts => ts.length

@[simp] lemma pointCount_inl (n : τ) : pointCount (ι := ι) (.inl n) = 0 := rfl

@[simp] lemma pointCount_inr (ts : List ι) : pointCount (τ := τ) (.inr ts) = ts.length := rfl

/-- `oa` submits rounds of parallel queries to `spec` holding at most `q` points in total, on
every path; the number of rounds and its queries to `free` are free. -/
abbrev IsPointQueryBound (oa : OracleComp (free + spec.batch) α) (q : ℕ) : Prop :=
  IsQueryBound oa q (fun t q => pointCount t ≤ q) (fun t q => q - pointCount t)

lemma isOnlineQueryBound_query_bind_inl_iff (n : τ)
    (mx : (free + spec.batch).Range (.inl n) → OracleComp (free + spec.batch) α)
    (b : ℕ × ℕ) :
    IsOnlineQueryBound (liftM ((free + spec.batch).query (.inl n)) >>= mx) b ↔
      ∀ u, IsOnlineQueryBound (mx u) b := by
  simp [IsOnlineQueryBound]

lemma isOnlineQueryBound_query_bind_inr_iff (ts : List ι)
    (mx : (free + spec.batch).Range (.inr ts) → OracleComp (free + spec.batch) α)
    (b : ℕ × ℕ) :
    IsOnlineQueryBound (liftM ((free + spec.batch).query (.inr ts)) >>= mx) b ↔
      (0 < b.1 ∧ ts.length ≤ b.2) ∧ ∀ u, IsOnlineQueryBound (mx u) (b.1 - 1, b.2 - ts.length) :=
  Iff.rfl

/-- Composing online budgets: the budgets of the two halves of a `bind` add. -/
lemma isOnlineQueryBound_bind {oa : OracleComp (free + spec.batch) α}
    {ob : α → OracleComp (free + spec.batch) β} {b₁ b₂ : ℕ × ℕ}
    (h₁ : IsOnlineQueryBound oa b₁) (h₂ : ∀ x, IsOnlineQueryBound (ob x) b₂) :
    IsOnlineQueryBound (oa >>= ob) (b₁ + b₂) := by
  refine isQueryBound_bind (· + ·) (fun t b₁' b₂' b hb => ?_) (fun t b₁' b₂' b hb => ?_) h₁ h₂
  · rcases t with n | ts
    · simp
    · simp only [onlineCanQuery_inr, Prod.fst_add, Prod.snd_add] at hb ⊢
      omega
  · rcases t with n | ts
    · simp
    · simp only [onlineCanQuery_inr] at hb
      refine ⟨Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩ <;> simp <;> omega

/-- A larger online budget, coordinatewise, is still a budget. -/
lemma IsOnlineQueryBound.mono {oa : OracleComp (free + spec.batch) α} {b b' : ℕ × ℕ}
    (h : IsOnlineQueryBound oa b) (hb : b ≤ b') : IsOnlineQueryBound oa b' := by
  induction oa using OracleComp.inductionOn generalizing b b' with
  | pure _ => trivial
  | query_bind t mx ih =>
      rcases t with n | ts
      · exact ⟨trivial, fun u => ih u (h.2 u) hb⟩
      · obtain ⟨⟨h₁, h₂⟩, hk⟩ := h
        obtain ⟨hb₁, hb₂⟩ := Prod.mk_le_mk.mp hb
        refine ⟨⟨by omega, by omega⟩, fun u => ih u (hk u) ?_⟩
        exact Prod.mk_le_mk.mpr ⟨by simp; omega, by simp; omega⟩

/-- An online budget `(r, q)` bounds the points by `q`. -/
lemma IsOnlineQueryBound.isPointQueryBound {oa : OracleComp (free + spec.batch) α}
    {b : ℕ × ℕ} (h : IsOnlineQueryBound oa b) : IsPointQueryBound oa b.2 :=
  IsQueryBound.proj Prod.snd
    (fun t b' hb => by rcases t with n | ts <;> simp_all)
    (fun t b' hb => by rcases t with n | ts <;> simp) h

/-! ## Budgets of building blocks -/

/-- A pure value submits no rounds. -/
lemma isOnlineQueryBound_pure (x : α) (b : ℕ × ℕ) :
    IsOnlineQueryBound (pure x : OracleComp (free + spec.batch) α) b :=
  trivial

/-- A program on oracles `spec₀` inside the free summand, such as a `ProbComp` flipping local
coins, submits no rounds once lifted. -/
lemma isOnlineQueryBound_liftComp {κ : Type} {spec₀ : OracleSpec.{0, 0} κ}
    [MonadLiftT (OracleQuery spec₀) (OracleQuery free)] (oa : OracleComp spec₀ α) (b : ℕ × ℕ) :
    IsOnlineQueryBound (liftComp oa (free + spec.batch)) b := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact isOnlineQueryBound_pure x b
  | query_bind t k ih =>
      rw [liftComp_bind, liftComp_query]
      change IsOnlineQueryBound ((liftM ((free + spec.batch).query
        (.inl (liftM (spec₀.query t) : OracleQuery free _).input)) >>= fun u =>
          pure ((liftM (spec₀.query t) : OracleQuery free _).cont u)) >>= fun u =>
            (k u).liftComp _) b
      rw [bind_assoc]
      exact (isOnlineQueryBound_query_bind_inl_iff _ _ _).2 fun u => by simpa using ih _

/-- Composing online budgets `b₁` and `b₂` into a budget `b` that covers their sum. -/
lemma isOnlineQueryBound_bind_le {oa : OracleComp (free + spec.batch) α}
    {ob : α → OracleComp (free + spec.batch) β} (b₁ b₂ : ℕ × ℕ) {b : ℕ × ℕ}
    (h₁ : IsOnlineQueryBound oa b₁) (h₂ : ∀ x, IsOnlineQueryBound (ob x) b₂)
    (hb : b₁.1 + b₂.1 ≤ b.1 ∧ b₁.2 + b₂.2 ≤ b.2) : IsOnlineQueryBound (oa >>= ob) b :=
  (isOnlineQueryBound_bind h₁ h₂).mono (Prod.mk_le_mk.mpr hb)

/-- The round `queryRound₂ p q` costs one round of `k + l` points. -/
lemma isOnlineQueryBound_queryRound₂ {k l : ℕ} (p : Fin k → ι) (q : Fin l → ι) :
    IsOnlineQueryBound (queryRound₂ (free := free) (spec := spec) p q) (1, k + l) := by
  rw [queryRound₂, IsOnlineQueryBound, isQueryBound_map_iff, isQueryBound_query_iff]
  simp

/-- The round `queryRound p` costs one round of `k` points. -/
lemma isOnlineQueryBound_queryRound {k : ℕ} (p : Fin k → ι) :
    IsOnlineQueryBound (queryRound (free := free) (spec := spec) p) (1, k) := by
  rw [queryRound, IsOnlineQueryBound, isQueryBound_map_iff]
  exact isOnlineQueryBound_queryRound₂ p _

/-- The single-point round `queryPoint t` costs one round of one point. -/
lemma isOnlineQueryBound_queryPoint (t : ι) :
    IsOnlineQueryBound (queryPoint (free := free) (spec := spec) t) (1, 1) := by
  rw [queryPoint, IsOnlineQueryBound, isQueryBound_map_iff]
  exact isOnlineQueryBound_queryRound _

/-! ## Rewriting rounds as single queries -/

/-- Answering a round point by point makes one query to `spec` per point. -/
lemma isQueryBoundP_batch_query (ts : List ι) :
    IsQueryBoundP (QueryImpl.batch (fun t => liftM ((free + spec).query (.inr t))) ts :
        OracleComp (free + spec) _) (·.isRight) ts.length := by
  induction ts with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons t ts ih =>
      rw [QueryImpl.batch_cons, List.length_cons,
        show ts.length + 1 = 1 + (ts.length + 0) by omega]
      exact isQueryBoundP_bind (by simp) fun u _ =>
        isQueryBoundP_bind ih fun us _ => isQueryBoundP_pure _ _ _

/-- Rewriting the rounds of a program with point budget `q` as single queries gives a program
making at most `q` queries to `spec`. -/
theorem IsPointQueryBound.isQueryBoundP_simulateQ_unbatch
    {oa : OracleComp (free + spec.batch) α} {q : ℕ} (h : IsPointQueryBound oa q) :
    IsQueryBoundP (simulateQ spec.unbatch oa) (·.isRight) q := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure x => exact isQueryBoundP_pure _ _ _
  | query_bind t mx ih =>
      obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).mp h
      rw [simulateQ_bind, simulateQ_spec_query]
      rcases t with n | ts
      · rw [← Nat.zero_add q]
        refine isQueryBoundP_bind ?_ fun u _ => ih u (by simpa using hk u)
        simp
      · have hq : q = ts.length + (q - ts.length) := by simp at ht; omega
        rw [hq]
        exact isQueryBoundP_bind (isQueryBoundP_batch_query ts) fun u _ => ih u (hk u)

/-- Rewriting the rounds of a program with online budget `(r, q)` as single queries gives a
program making at most `q` queries to `spec`. -/
theorem IsOnlineQueryBound.isQueryBoundP_simulateQ_unbatch
    {oa : OracleComp (free + spec.batch) α} {r q : ℕ} (h : IsOnlineQueryBound oa (r, q)) :
    IsQueryBoundP (simulateQ spec.unbatch oa) (·.isRight) q :=
  h.isPointQueryBound.isQueryBoundP_simulateQ_unbatch

/-! ## Handlers sending rounds to rounds -/

/-- A handler that sends each query to the free summand to a program with no rounds, and each
round `ts` to a program with at most one round of at most `ts.length` points, preserves the online
budget. The free summands `free` and `free'` of the two sides may differ. -/
theorem IsOnlineQueryBound.simulateQ_of_step {τ' ι' : Type} {free' : OracleSpec.{0, 0} τ'}
    {spec' : OracleSpec.{0, 0} ι'}
    {so : QueryImpl (free + spec.batch) (OracleComp (free' + spec'.batch))}
    {oa : OracleComp (free + spec.batch) α} {b : ℕ × ℕ}
    (h : IsOnlineQueryBound oa b) (hstep : ∀ t, IsOnlineQueryBound (so t) (onlineStep t)) :
    IsOnlineQueryBound (simulateQ so oa) b := by
  induction oa using OracleComp.inductionOn generalizing b with
  | pure x => trivial
  | query_bind t mx ih =>
      obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).mp h
      rw [simulateQ_bind, simulateQ_spec_query]
      have hb : onlineStep t + onlineCost t b = b := by
        rcases t with n | ts
        · simp
        · simp only [onlineCanQuery_inr] at ht
          refine Prod.ext ?_ ?_ <;> simp <;> omega
      rw [← hb]
      exact isOnlineQueryBound_bind (hstep t) fun u => ih u (hk u)

/-- Lifting a program through a `SubSpec` inclusion `spec ⊂ₒ superSpec`, which sends each round
to the round of its translated points, preserves the online budget. -/
theorem IsOnlineQueryBound.liftComp {ι' : Type} {superSpec : OracleSpec.{0, 0} ι'}
    [spec ⊂ₒ superSpec] {oa : OracleComp (free + spec.batch) α} {b : ℕ × ℕ}
    (h : IsOnlineQueryBound oa b) :
    IsOnlineQueryBound (liftComp oa (free + superSpec.batch)) b := by
  refine h.simulateQ_of_step fun t => ?_
  rcases t with n | ts
  · exact (isQueryBound_query_iff (spec := free + superSpec.batch) (.inl n) _ _ _).mpr trivial
  · change IsOnlineQueryBound (SubSpec.batchOnResponse _ ts <$>
      liftM ((free + superSpec.batch).query (.inr (ts.map _)))) _
    rw [IsOnlineQueryBound, isQueryBound_map_iff, isQueryBound_query_iff]
    simp

end OracleComp
