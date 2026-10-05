/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.UntilBad
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure
import VCVio.OracleComp.QueryTracking.QueryBound.Counter
import VCVio.OracleComp.EvalDist.Measure

/-!
# Hidden-seed derivations from a random oracle

A program over `pub.withDerivations X R = unifSpec + pub + (X →ₒ R)` makes public random-oracle
queries and *derivation* queries `x : X`. A `SecretEncoding pub S X R` places each derivation at
a public point: under the secret `s : S`, the derivation of `x` is the public answer at
`E.enc s x`, and `E.enc s` is injective with every encoded point answered in `R`.

* The real game `SecretEncoding.realImpl E s` answers both kinds of query from one lazily sampled
  public cache, reading a derivation `x` at `E.enc s x`.
* The ideal game `SecretEncoding.idealImpl pub X R` answers public queries from the public cache
  and derivations from an independent table; the secret does not enter it.

The two agree until a public query hits an encoded point. The proof couples them on a split
state (public cache, derivation table, flag): the coupled real game
`SecretEncoding.coupledImpl E s` stores the answers at encoded points in the table, and merging
the split state (`SecretEncoding.merge`) recovers the real cache exactly
(`SecretEncoding.map_run_simulateQ_coupledImpl`). The flagged ideal game
`SecretEncoding.flaggedIdealImpl E s` adds to the ideal game a flag raised by every public query
at an encoded point. Off the flag, the two take identically distributed steps
(`SecretEncoding.agreeUntilBad_coupledImpl_flaggedIdealImpl`), so the fundamental lemma
`QueryImpl.AgreeUntilBad.prEvent_simulateQ_run_le_add_bad_right` applies.

From empty states the flag is a function of the final public cache: it is raised exactly when
that cache holds an encoded point
(`SecretEncoding.flag_eq_true_iff_of_mem_support_flaggedIdealImpl`). Without its flag the flagged
ideal game does not depend on the secret, so for a secret drawn independently of the run the flag
probability is bounded by exchanging the secret draw with the run and applying a union bound over
the cached points. The points that can be encoded under some secret,
`D = ⋃ s, Set.range (E.enc s)`, are charged by a query budget `IsQueryBoundP oa p q` whose
predicate `p` holds at every public query at a point of `D`; every other query (public queries at
points outside `D`, derivation queries and uniform draws) may be left free. Under that budget the
final public cache of the ideal game holds at most `q` points of `D`
(`SecretEncoding.encard_inter_setOf_isSome_le_of_mem_support_idealImpl`), so if every public point
is encoded under the secret with probability at most `ε`, the flag is raised with probability at
most `q * ε` (`SecretEncoding.prEvent_flaggedIdealImpl_le_mul`). The bound `q * ε` is attained: a
single public query at a point encoded under half of the secrets raises the flag with probability
`1 / 2 = q * ε`.

Bookkeeping that an event must read alongside the games, such as a log or a record of where each
answer came from, is carried through the bounds by extending the coupled real game and the ideal
game by the same passive auxiliary state (`QueryImpl.extendState`). Its update may read the
secret, the query, its answer, the split state before and after the step (including the
derivation table) and its own previous value, but not the flag. The extended forms
`SecretEncoding.prEvent_coupledImpl_extendState_le_add_mul` and
`SecretEncoding.prEvent_coupledImpl_extendState_le_add` bound an event of the extended coupled
game's output, split state and auxiliary state by the same event of the extended ideal game.

## Main statements

- `SecretEncoding.prEvent_realImpl_le_add_mul`: for a secret drawn from any distribution and
  under the budget, an event of the secret and the real game is at most the same event of the
  ideal game, read on the merged cache, plus `q * ε`.
- `SecretEncoding.prEvent_coupledImpl_le_add_mul`: the same bound for an event of the coupled
  game's split state, which exposes the derivation table that the ideal game samples
  independently.
- `SecretEncoding.prEvent_coupledImpl_extendState_le_add_mul`: the same bound for the coupled and
  ideal games extended by a shared passive auxiliary state.
- `SecretEncoding.prEvent_flaggedIdealImpl_le_mul`: the flag bound `q * ε`.
- `SecretEncoding.prEvent_realImpl_le_add`, `SecretEncoding.prEvent_coupledImpl_le_add` and
  `SecretEncoding.prEvent_coupledImpl_extendState_le_add`: the fixed-secret bounds, charging the
  flag probability of the flagged ideal game.
- `SecretEncoding.agreeUntilBad_coupledImpl_flaggedIdealImpl`: the coupled real game and the
  flagged ideal game agree until the flag.
- `SecretEncoding.deriveImpl_comp_withDerivationsLift` and
  `SecretEncoding.simulateQ_deriveImpl_liftM`: `E.deriveImpl s` undoes the lift of sampling and
  public queries into the derivation world (`OracleSpec.withDerivationsLift`) and the lift of a
  probabilistic computation.
- `SecretEncoding.map_run_simulateQ_coupledImpl` and
  `SecretEncoding.map_run_simulateQ_flaggedIdealImpl`: the coupled and flagged games project onto
  the real and ideal games.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace OracleSpec

variable {ι : Type} (pub : OracleSpec ι) (X R : Type)

/-- Programs with uniform sampling, a public random oracle `pub`, and derivation queries
`X →ₒ R`. -/
abbrev withDerivations : OracleSpec ((ℕ ⊕ ι) ⊕ X) := unifSpec + pub + (X →ₒ R)

/-- The handler forwarding each sampling and public query unchanged into
`pub.withDerivations X R`. -/
@[expose] def withDerivationsLift :
    QueryImpl (unifSpec + pub) (OracleComp (pub.withDerivations X R)) :=
  fun t => (pub.withDerivations X R).query (.inl t)

end OracleSpec

/-- An injective, secret-keyed encoding of derivation inputs as public oracle inputs, each
answered in `R`. -/
structure SecretEncoding {ι : Type} (pub : OracleSpec ι) (S X R : Type) where
  /-- The public oracle input at which the derivation of `x` under secret `s` is read. -/
  enc : S → X → ι
  /-- The public oracle answers every encoded point in `R`. -/
  range_eq : ∀ s x, pub.Range (enc s x) = R
  /-- Distinct derivation inputs have distinct encodings. -/
  injective : ∀ s, Function.Injective (enc s)

namespace SecretEncoding

variable {ι : Type} {pub : OracleSpec ι} {S X R : Type} (E : SecretEncoding pub S X R)

/-- Every point witnessed as an encoding is answered in `R`. -/
theorem range_eq_of_enc_eq {s : S} {x : X} {t : ι} (h : E.enc s x = t) : pub.Range t = R :=
  h ▸ E.range_eq s x

/-! ## Split state: public cache, derivation table, flag -/

/-- The public cache off the encoded points, paired with the derivation table. -/
abbrev SplitCache (pub : OracleSpec ι) (X R : Type) := pub.QueryCache × (X →ₒ R).QueryCache

open Classical in
/-- Rebuild the real public cache from a split state: an encoded point `E.enc s x` reads the
table at `x`, every other point reads the public cache. -/
noncomputable def merge (s : S) (st : SplitCache pub X R) : pub.QueryCache :=
  .ofFn fun t => if h : ∃ x, E.enc s x = t then
    (st.2 h.choose).map (cast (E.range_eq_of_enc_eq h.choose_spec).symm) else st.1 t

/-- The merged cache at an encoded point reads the table at any witness of the encoding. -/
theorem merge_apply_of_enc_eq (s : S) (st : SplitCache pub X R) {x : X} {t : ι}
    (hx : E.enc s x = t) :
    (E.merge s st) t = (st.2 x).map (cast (E.range_eq_of_enc_eq hx).symm) := by
  have key : ∀ y (hy : E.enc s y = t),
      (st.2 y).map (cast (E.range_eq_of_enc_eq hy).symm) =
        (st.2 x).map (cast (E.range_eq_of_enc_eq hx).symm) := by
    intro y hy
    obtain rfl := E.injective s (hy.trans hx.symm)
    rfl
  simp only [merge, QueryCache.ofFn_apply]
  split
  · rename_i h
    exact key _ h.choose_spec
  · rename_i h
    exact absurd ⟨x, hx⟩ h

/-- The merged cache at `E.enc s x` reads the table at `x`. -/
theorem merge_apply_enc (s : S) (st : SplitCache pub X R) (x : X) :
    (E.merge s st) (E.enc s x) = (st.2 x).map (cast (E.range_eq s x).symm) :=
  E.merge_apply_of_enc_eq s st rfl

/-- The merged cache at a point that encodes nothing reads the public cache. -/
theorem merge_apply_of_not_exists (s : S) (st : SplitCache pub X R) {t : ι}
    (ht : ¬∃ x, E.enc s x = t) : (E.merge s st) t = st.1 t := by
  simp only [merge, QueryCache.ofFn_apply, ht, ↓reduceDIte]

/-- Merging two empty caches gives the empty cache. -/
@[simp] theorem merge_empty (s : S) : E.merge s ((∅, ∅) : SplitCache pub X R) = ∅ := by
  refine QueryCache.ext fun t ↦ ?_
  by_cases ht : ∃ x, E.enc s x = t
  · obtain ⟨x, rfl⟩ := ht
    simp only [merge_apply_enc, QueryCache.empty_apply, Option.map_none]
  · simp only [E.merge_apply_of_not_exists s _ ht, QueryCache.empty_apply]

open Classical in
/-- Whether a query is a public query at a point `E.enc s x`. -/
@[expose] noncomputable def encodedQuery (s : S) : (pub.withDerivations X R).Domain → Bool
  | .inl (.inr t) => decide (∃ x, E.enc s x = t)
  | _ => false

/-- `E.encodedQuery s` holds exactly at the public queries at the points `E.enc s x`. -/
theorem encodedQuery_eq_true_iff (s : S) (t : (pub.withDerivations X R).Domain) :
    E.encodedQuery s t = true ↔ ∃ x, .inl (.inr (E.enc s x)) = t := by
  rcases t with (n | t) | x
  · simp only [encodedQuery, Bool.false_eq_true, Sum.inl.injEq, reduceCtorEq, exists_false]
  · simp only [encodedQuery, decide_eq_true_eq, Sum.inl.injEq, Sum.inr.injEq]
  · simp only [encodedQuery, Bool.false_eq_true, reduceCtorEq, exists_false]

variable [DecidableEq ι]

/-- Filling the table at `x` fills the merged cache at `E.enc s x`. -/
theorem merge_cacheQuery_table [DecidableEq X] (s : S) (st : SplitCache pub X R) (x : X)
    (u : pub.Range (E.enc s x)) :
    E.merge s (st.1, st.2.cacheQuery x (cast (E.range_eq s x) u)) =
      (E.merge s st).cacheQuery (E.enc s x) u := by
  refine QueryCache.ext fun t ↦ ?_
  by_cases ht : ∃ y, E.enc s y = t
  · obtain ⟨y, rfl⟩ := ht
    rw [merge_apply_enc]
    dsimp only
    by_cases hy : y = x
    · subst hy
      simp only [QueryCache.cacheQuery_self, Option.map_some, cast_cast, cast_eq]
    · rw [QueryCache.cacheQuery_of_ne _ _ hy,
        QueryCache.cacheQuery_of_ne _ _ fun h ↦ hy (E.injective s h), merge_apply_enc]
  · rw [E.merge_apply_of_not_exists s _ ht,
      QueryCache.cacheQuery_of_ne _ _ fun h ↦ ht ⟨x, h.symm⟩, E.merge_apply_of_not_exists s _ ht]

/-- Filling the public cache at a point that encodes nothing fills the merged cache there. -/
theorem merge_cacheQuery_public (s : S) (st : SplitCache pub X R) {t : ι}
    (ht : ¬∃ x, E.enc s x = t) (u : pub.Range t) :
    E.merge s (st.1.cacheQuery t u, st.2) = (E.merge s st).cacheQuery t u := by
  refine QueryCache.ext fun t' ↦ ?_
  by_cases ht' : ∃ y, E.enc s y = t'
  · obtain ⟨y, rfl⟩ := ht'
    rw [merge_apply_enc, QueryCache.cacheQuery_of_ne _ _ fun h ↦ ht ⟨y, h⟩, merge_apply_enc]
  · rw [E.merge_apply_of_not_exists s _ ht']
    dsimp only
    by_cases h : t' = t
    · subst h
      simp only [QueryCache.cacheQuery_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ h, QueryCache.cacheQuery_of_ne _ _ h,
        E.merge_apply_of_not_exists s _ ht']

variable [∀ t, SampleableType (pub.Range t)]

/-- Answer a derivation query `x` by the public query at `E.enc s x`. -/
@[expose] def deriveImpl (s : S) :
    QueryImpl (pub.withDerivations X R) (OracleComp (unifSpec + pub)) := fun
  | .inl t => (unifSpec + pub).query t
  | .inr x => cast (E.range_eq s x) <$> (unifSpec + pub).query (.inr (E.enc s x))

omit [DecidableEq ι] [∀ t, SampleableType (pub.Range t)] in
/-- Lifting sampling and public queries into the derivation world and then answering through
`E.deriveImpl s` is the identity handler: a lifted program makes no derivation query. -/
theorem deriveImpl_comp_withDerivationsLift (s : S) :
    E.deriveImpl s ∘ₛ pub.withDerivationsLift X R = QueryImpl.id' (unifSpec + pub) := by
  funext t
  rcases t with n | t <;> rfl

omit [DecidableEq ι] [∀ t, SampleableType (pub.Range t)] in
/-- Answering a lifted probabilistic computation through `E.deriveImpl s` gives the same
computation, lifted into sampling and public queries. -/
theorem simulateQ_deriveImpl_liftM (s : S) {α : Type} (oa : ProbComp α) :
    simulateQ (E.deriveImpl s) (liftM oa : OracleComp (pub.withDerivations X R) α) =
      (liftM oa : OracleComp (unifSpec + pub) α) := by
  rw [QueryImpl.simulateQ_liftM_eq_of_query _ (fun t => liftM (unifSpec.query t)) fun _ => rfl]
  rfl

/-- The real game: derivations and public queries share one lazily sampled public cache. -/
@[expose] noncomputable def realImpl (s : S) :
    QueryImpl (pub.withDerivations X R) (StateT pub.QueryCache ProbComp) :=
  pub.romImpl ∘ₛ E.deriveImpl s

/-! ## The real game, query by query -/

/-- The real game forwards a uniform query and leaves the cache unchanged. -/
theorem realImpl_run_unif (s : S) (n : ℕ) (C : pub.QueryCache) :
    (E.realImpl s (.inl (.inl n))).run C =
      (fun u => (u, C)) <$> (unifSpec.query n : ProbComp _) := by
  simp [realImpl, deriveImpl, unifFwdImpl, bind_pure_comp]

/-- The real game answers a public query from its random oracle. -/
theorem realImpl_run_pub (s : S) (t : ι) (C : pub.QueryCache) :
    (E.realImpl s (.inl (.inr t))).run C = (pub.randomOracle t).run C := by
  simp only [realImpl, deriveImpl, QueryImpl.apply_compose, simulateQ_spec_query]
  rfl

/-- The real game answers a derivation `x` by the random oracle at `E.enc s x`. -/
theorem realImpl_run_derive (s : S) (x : X) (C : pub.QueryCache) :
    (E.realImpl s (.inr x)).run C =
      Prod.map (cast (E.range_eq s x)) id <$> (pub.randomOracle (E.enc s x)).run C := by
  simp only [realImpl, deriveImpl, QueryImpl.apply_compose, simulateQ_map, simulateQ_spec_query,
    StateT.run_map]
  rfl

/-! ## The coupled real game -/

variable [DecidableEq X]

/-- A public query at the encoded point `t = E.enc s x` in the coupled real game: read or
fill the derivation table at `x`, and raise the flag. -/
noncomputable def encodedStep (s : S) {t : ι} (x : X) (hx : E.enc s x = t)
    (st : SplitCache pub X R × Bool) : ProbComp (pub.Range t × (SplitCache pub X R × Bool)) :=
  match st.1.2 x with
  | some v => pure (cast (E.range_eq_of_enc_eq hx).symm v, (st.1, true))
  | none => do
      let u ← $ᵗ pub.Range t
      pure (u, ((st.1.1, st.1.2.cacheQuery x (cast (E.range_eq_of_enc_eq hx) u)), true))

open Classical in
/-- The real game on a split state: answers at encoded points live in the derivation table, all
other public answers in the public cache; a public query at an encoded point raises the flag.
Its samplers are those of the real game. -/
noncomputable def coupledImpl (s : S) :
    QueryImpl (pub.withDerivations X R) (StateT (SplitCache pub X R × Bool) ProbComp) := fun
  | .inl (.inl n) => StateT.mk fun st => (fun u => (u, st)) <$> (unifSpec.query n : ProbComp _)
  | .inl (.inr t) => StateT.mk fun st =>
      if h : ∃ x, E.enc s x = t then E.encodedStep s h.choose h.choose_spec st
      else (fun z => (z.1, ((z.2, st.1.2), st.2))) <$> (pub.randomOracle t).run st.1.1
  | .inr x => StateT.mk fun st =>
      match st.1.2 x with
      | some v => pure (v, st)
      | none => do
          let u ← $ᵗ pub.Range (E.enc s x)
          pure (cast (E.range_eq s x) u,
            ((st.1.1, st.1.2.cacheQuery x (cast (E.range_eq s x) u)), st.2))

/-- A public query of the coupled real game at a point `E.enc s x` is the encoded step at `x`. -/
theorem coupledImpl_run_of_enc_eq (s : S) {x : X} {t : ι} (hx : E.enc s x = t)
    (st : SplitCache pub X R × Bool) :
    (E.coupledImpl s (.inl (.inr t))).run st = E.encodedStep s x hx st := by
  simp only [coupledImpl, StateT.run_mk]
  have key : ∀ y (hy : E.enc s y = t), E.encodedStep s y hy st = E.encodedStep s x hx st := by
    intro y hy
    obtain rfl := E.injective s (hy.trans hx.symm)
    rfl
  split
  · exact key _ _
  · rename_i h
    exact absurd ⟨x, hx⟩ h

/-- A public query of the coupled real game at a point that encodes nothing is answered from the
public cache. -/
theorem coupledImpl_run_of_not_exists (s : S) {t : ι} (ht : ¬∃ x, E.enc s x = t)
    (st : SplitCache pub X R × Bool) :
    (E.coupledImpl s (.inl (.inr t))).run st =
      (fun z => (z.1, ((z.2, st.1.2), st.2))) <$> (pub.randomOracle t).run st.1.1 := by
  simp only [coupledImpl, StateT.run_mk]
  split
  · rename_i h
    exact absurd h ht
  · rfl

/-- Forgetting the flag and merging the split state turns the coupled game into the real one. -/
theorem map_run_simulateQ_coupledImpl (s : S) {α : Type}
    (oa : OracleComp (pub.withDerivations X R) α) (st : SplitCache pub X R × Bool) :
    Prod.map id (E.merge s ∘ Prod.fst) <$> (simulateQ (E.coupledImpl s) oa).run st =
      (simulateQ (E.realImpl s) oa).run (E.merge s st.1) := by
  refine map_run_simulateQ_eq_of_query_map_eq _ _ _ (fun t st ↦ ?_) oa st
  rcases t with (n | t) | x
  · simp only [coupledImpl, StateT.run_mk, realImpl_run_unif, Functor.map_map, Prod.map_apply,
      id_eq, Function.comp_apply]
    rfl
  · by_cases ht : ∃ x, E.enc s x = t
    · obtain ⟨x, rfl⟩ := ht
      rw [E.coupledImpl_run_of_enc_eq s rfl, realImpl_run_pub, randomOracle.run_eq,
        Function.comp_apply, merge_apply_enc]
      unfold encodedStep
      cases hT : st.1.2 x with
      | some v => simp
      | none =>
        simp only [Option.map_none, map_bind, map_pure, Prod.map_apply, id_eq]
        refine bind_congr fun u ↦ ?_
        rw [← merge_cacheQuery_table]
        rfl
    · rw [E.coupledImpl_run_of_not_exists s ht, realImpl_run_pub, randomOracle.run_eq,
        randomOracle.run_eq, Function.comp_apply, E.merge_apply_of_not_exists s _ ht]
      cases hc : st.1.1 t with
      | some v => simp
      | none =>
        simp only [map_bind, map_pure, Prod.map_apply, id_eq, Function.comp_apply]
        refine bind_congr fun u ↦ ?_
        rw [← E.merge_cacheQuery_public s _ ht]
  · rw [realImpl_run_derive, randomOracle.run_eq, Function.comp_apply, merge_apply_enc]
    simp only [coupledImpl, StateT.run_mk]
    cases hT : st.1.2 x with
    | some v => simp [cast_cast]
    | none =>
      simp only [Option.map_none, map_bind, map_pure, Prod.map_apply, id_eq]
      refine bind_congr fun u ↦ ?_
      rw [← merge_cacheQuery_table]
      rfl

/-! ## The ideal game and its flagged form -/

variable [SampleableType R]

variable (pub X R) in
/-- The ideal game: public queries read the public cache and derivations an independent table,
both lazily sampled; no secret enters it. -/
@[expose] noncomputable def idealImpl :
    QueryImpl (pub.withDerivations X R) (StateT (SplitCache pub X R) ProbComp) := fun
  | .inl (.inl n) => StateT.mk fun st => (fun u => (u, st)) <$> (unifSpec.query n : ProbComp _)
  | .inl (.inr t) => StateT.mk fun st =>
      (fun z => (z.1, (z.2, st.2))) <$> (pub.randomOracle t).run st.1
  | .inr x => StateT.mk fun st =>
      (fun z => (z.1, (st.1, z.2))) <$> ((X →ₒ R).randomOracle x).run st.2

/-- The ideal game with a flag, raised by every public query at a point encoded under `s`. -/
@[expose] noncomputable def flaggedIdealImpl (s : S) :
    QueryImpl (pub.withDerivations X R) (StateT (SplitCache pub X R × Bool) ProbComp) :=
  (idealImpl pub X R).extendState fun t _ _ _ f ↦ f || E.encodedQuery s t

/-- Forgetting the flag turns the flagged ideal game into the ideal one. -/
theorem map_run_simulateQ_flaggedIdealImpl (s : S) {α : Type}
    (oa : OracleComp (pub.withDerivations X R) α) (st : SplitCache pub X R) (f : Bool) :
    Prod.map id Prod.fst <$> (simulateQ (E.flaggedIdealImpl s) oa).run (st, f) =
      (simulateQ (idealImpl pub X R) oa).run st :=
  extendState_run_proj_eq _ _ oa st f

/-- Once raised, the flag of the flagged ideal game stays raised. -/
theorem flaggedIdealImpl_preservesInv (s : S) :
    QueryImpl.PreservesInv (E.flaggedIdealImpl s) fun st ↦ st.2 = true := by
  intro t st hst z hz
  simp only [flaggedIdealImpl, QueryImpl.extendState_apply, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff] at hz
  obtain ⟨_, -, rfl⟩ := hz
  simp [hst]

/-- Off the flag, the coupled real game and the flagged ideal game take identically distributed
steps: they differ only in the samplers of the derivation answers, both uniform on `R`, and on
public queries at encoded points, which raise the flag in both. -/
theorem agreeUntilBad_coupledImpl_flaggedIdealImpl (s : S) :
    QueryImpl.AgreeUntilBad (E.coupledImpl s) (E.flaggedIdealImpl s) fun st ↦ st.2 = true := by
  rintro t ⟨⟨c, T⟩, f⟩ hf Q
  simp only [Bool.not_eq_true] at hf
  subst hf
  rcases t with (n | t) | x
  · have h : (E.coupledImpl s (.inl (.inl n))).run ((c, T), false) =
        (E.flaggedIdealImpl s (.inl (.inl n))).run ((c, T), false) := by
      simp [coupledImpl, flaggedIdealImpl, idealImpl, encodedQuery]
    rw [h]
  · by_cases ht : ∃ x, E.enc s x = t
    · obtain ⟨x, rfl⟩ := ht
      refine (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hz' ↦ hz'.2 ?_).trans
        (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hz' ↦ hz'.2 ?_).symm
      · rw [E.coupledImpl_run_of_enc_eq s rfl] at hz
        unfold encodedStep at hz
        split at hz
        · simp only [support_pure, Set.mem_singleton_iff] at hz
          rw [hz]
        · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
          obtain ⟨_, -, rfl⟩ := hz
          rfl
      · simp only [flaggedIdealImpl, QueryImpl.extendState_apply, support_bind, support_pure,
          Set.mem_iUnion, Set.mem_singleton_iff] at hz
        obtain ⟨_, -, rfl⟩ := hz
        simp [encodedQuery]
    · have h : (E.coupledImpl s (.inl (.inr t))).run ((c, T), false) =
          (E.flaggedIdealImpl s (.inl (.inr t))).run ((c, T), false) := by
        rw [E.coupledImpl_run_of_not_exists s ht]
        simp [flaggedIdealImpl, idealImpl, encodedQuery, ht]
      rw [h]
  · cases hT : T x with
    | some v =>
      have h : (E.coupledImpl s (.inr x)).run ((c, T), false) =
          (E.flaggedIdealImpl s (.inr x)).run ((c, T), false) := by
        simp [coupledImpl, flaggedIdealImpl, idealImpl, hT, encodedQuery]
      rw [h]
    | none =>
      have h₁ : (E.coupledImpl s (.inr x)).run ((c, T), false) =
          (fun u ↦ (u, ((c, T.cacheQuery x u), false))) <$>
            (cast (E.range_eq s x) <$> ($ᵗ pub.Range (E.enc s x))) := by
        simp [coupledImpl, hT]
      have h₂ : (E.flaggedIdealImpl s (.inr x)).run ((c, T), false) =
          (fun u ↦ (u, ((c, T.cacheQuery x u), false))) <$> ($ᵗ R) := by
        simp [flaggedIdealImpl, idealImpl, hT, encodedQuery]
      rw [h₁, h₂, prEvent_map (cast (E.range_eq s x) <$> ($ᵗ pub.Range (E.enc s x))),
        prEvent_map ($ᵗ R), SampleableType.prEvent_map_cast_uniformSample]

/-! ## Real game against ideal game, for a fixed secret -/

/-- Coupled real game against the ideal game, for a fixed secret: an event of the coupled game's
output and split state, with the flag forgotten, is at most the same event in the ideal game plus
the chance that the flagged ideal game raises its flag. The split state exposes the derivation
table of the coupled game, which plays the role of the ideal game's independent table. -/
theorem prEvent_coupledImpl_le_add (s : S) {α : Type}
    (oa : OracleComp (pub.withDerivations X R) α) (P : α × SplitCache pub X R → Prop) :
    Pr{let z ← (simulateQ (E.coupledImpl s) oa).run ((∅, ∅), false)}[P (z.1, z.2.1)] ≤
      Pr{let z ← (simulateQ (idealImpl pub X R) oa).run (∅, ∅)}[P z] +
        Pr{let z ← (simulateQ (E.flaggedIdealImpl s) oa).run ((∅, ∅), false)}[z.2.2 = true] := by
  rw [← E.map_run_simulateQ_flaggedIdealImpl s oa (∅, ∅) false, prEvent_map]
  exact (E.agreeUntilBad_coupledImpl_flaggedIdealImpl s).prEvent_simulateQ_run_le_add_bad_right
    (E.flaggedIdealImpl_preservesInv s) oa _ fun z ↦ P (z.1, z.2.1)

/-- Real game against the ideal game, for a fixed secret: an event of the real game is at most
the event, read on the merged cache, in the ideal game, plus the chance that the flagged ideal
game makes a public query at an encoded point. -/
theorem prEvent_realImpl_le_add (s : S) {α : Type} (oa : OracleComp (pub.withDerivations X R) α)
    (P : α × pub.QueryCache → Prop) :
    Pr{let z ← (simulateQ (E.realImpl s) oa).run ∅}[P z] ≤
      Pr{let z ← (simulateQ (idealImpl pub X R) oa).run (∅, ∅)}[P (z.1, E.merge s z.2)] +
        Pr{let z ← (simulateQ (E.flaggedIdealImpl s) oa).run ((∅, ∅), false)}[z.2.2 = true] := by
  have h := E.map_run_simulateQ_coupledImpl s oa ((∅, ∅), false)
  rw [merge_empty] at h
  rw [← h, prEvent_map]
  exact E.prEvent_coupledImpl_le_add s oa fun z ↦ P (z.1, E.merge s z.2)

/-- Coupled real game against the ideal game, both extended by the same passive auxiliary state,
for a fixed secret: an event of the extended coupled game's output, split state and auxiliary
state, with the flag forgotten, is at most the same event in the extended ideal game plus the
chance that the flagged ideal game raises its flag. The auxiliary update `aux` reads the query,
its answer, the split state before and after the step and its own previous value, but not the
flag. -/
theorem prEvent_coupledImpl_extendState_le_add (s : S) {Q : Type} (r₀ : Q)
    (aux : (t : (pub.withDerivations X R).Domain) → SplitCache pub X R →
      (pub.withDerivations X R).Range t → SplitCache pub X R → Q → Q)
    {α : Type} (oa : OracleComp (pub.withDerivations X R) α)
    (P : α × SplitCache pub X R × Q → Prop) :
    Pr{
      let z ← (simulateQ ((E.coupledImpl s).extendState fun t st u st' r ↦
        aux t st.1 u st'.1 r) oa).run (((∅, ∅), false), r₀)}[P (z.1, z.2.1.1, z.2.2)] ≤
      Pr{let z ← (simulateQ ((idealImpl pub X R).extendState aux) oa).run ((∅, ∅), r₀)}[P z] +
        Pr{let z ← (simulateQ (E.flaggedIdealImpl s) oa).run ((∅, ∅), false)}[z.2.2 = true] := by
  let aux' : (t : (pub.withDerivations X R).Domain) → SplitCache pub X R × Bool →
      (pub.withDerivations X R).Range t → SplitCache pub X R × Bool → Q → Q :=
    fun t st u st' r ↦ aux t st.1 u st'.1 r
  have hideal : Prod.map id (fun st : (SplitCache pub X R × Bool) × Q ↦ (st.1.1, st.2)) <$>
      (simulateQ ((E.flaggedIdealImpl s).extendState aux') oa).run (((∅, ∅), false), r₀) =
      (simulateQ ((idealImpl pub X R).extendState aux) oa).run ((∅, ∅), r₀) := by
    refine map_run_simulateQ_eq_of_query_map_eq _ _ _ (fun t st ↦ ?_) oa _
    simp only [flaggedIdealImpl, QueryImpl.extendState_apply, bind_pure_comp, Functor.map_map,
      Prod.map_apply, id_eq, aux']
  rw [← hideal, prEvent_map,
    ← extendState_run_proj_eq (E.flaggedIdealImpl s) aux' oa ((∅, ∅), false) r₀, prEvent_map]
  exact ((E.agreeUntilBad_coupledImpl_flaggedIdealImpl s).extendState aux')
    |>.prEvent_simulateQ_run_le_add_bad_right ((E.flaggedIdealImpl_preservesInv s).extendState aux')
      oa _ fun z ↦ P (z.1, z.2.1.1, z.2.2)

/-! ## The flag and the public cache -/

/-- A step of the ideal game caches a public point exactly when the point was cached before the
step or is the point of a public query. -/
theorem isSome_fst_apply_iff_of_mem_support_idealImpl {t : (pub.withDerivations X R).Domain}
    {st : SplitCache pub X R} {w : (pub.withDerivations X R).Range t × SplitCache pub X R}
    (hw : w ∈ support ((idealImpl pub X R t).run st)) (t' : ι) :
    (w.2.1 t').isSome ↔ (st.1 t').isSome ∨ .inl (.inr t') = t := by
  rcases t with (n | t) | x
  · simp only [idealImpl, StateT.run_mk, support_map, Set.mem_image] at hw
    obtain ⟨u, -, rfl⟩ := hw
    simp only [Sum.inl.injEq, reduceCtorEq, or_false]
  · simp only [idealImpl, StateT.run_mk, support_map, Set.mem_image] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    rw [QueryImpl.withCaching_run_isSome_apply_iff _ hy, Sum.inl.injEq, Sum.inr.injEq]
  · simp only [idealImpl, StateT.run_mk, support_map, Set.mem_image] at hw
    obtain ⟨y, -, rfl⟩ := hw
    simp only [reduceCtorEq, or_false]

/-- From empty states, the flag of the flagged ideal game is raised exactly when the final public
cache holds a point encoded under `s`. -/
theorem flag_eq_true_iff_of_mem_support_flaggedIdealImpl (s : S) {α : Type}
    (oa : OracleComp (pub.withDerivations X R) α) {z : α × SplitCache pub X R × Bool}
    (hz : z ∈ support ((simulateQ (E.flaggedIdealImpl s) oa).run ((∅, ∅), false))) :
    z.2.2 = true ↔ ∃ x, (z.2.1.1 (E.enc s x)).isSome := by
  refine simulateQ_run_preservesInv (E.flaggedIdealImpl s)
    (fun st ↦ st.2 = true ↔ ∃ x, (st.1.1 (E.enc s x)).isSome) ?_ oa _ ?_ z hz
  · rintro t ⟨st, f⟩ hinv w hw
    rw [flaggedIdealImpl, QueryImpl.extendState_apply, mem_support_bind_iff] at hw
    obtain ⟨v, hv, hw⟩ := hw
    rw [support_pure, Set.mem_singleton_iff] at hw
    subst hw
    dsimp only
    simp only [Bool.or_eq_true, E.encodedQuery_eq_true_iff,
      isSome_fst_apply_iff_of_mem_support_idealImpl hv, exists_or]
    exact or_congr hinv Iff.rfl
  · simp only [Bool.false_eq_true, QueryCache.empty_apply, Option.isSome_none, exists_false]

/-- Under a query budget charging every public query at a point of a set `D`, the final public
cache of the ideal game, run from empty states, holds at most `q` points of `D`. -/
theorem encard_inter_setOf_isSome_le_of_mem_support_idealImpl {D : Set ι}
    {p : (pub.withDerivations X R).Domain → Prop} [DecidablePred p]
    (hp : ∀ t ∈ D, p (.inl (.inr t))) {α : Type} {oa : OracleComp (pub.withDerivations X R) α}
    {q : ℕ} (h : IsQueryBoundP oa p q) {z : α × SplitCache pub X R}
    (hz : z ∈ support ((simulateQ (idealImpl pub X R) oa).run (∅, ∅))) :
    (D ∩ {t | (z.2.1 t).isSome}).encard ≤ q := by
  let aux : (t : (pub.withDerivations X R).Domain) → SplitCache pub X R →
      (pub.withDerivations X R).Range t → SplitCache pub X R → ℕ → ℕ :=
    fun t _ _ _ n ↦ if p t then n + 1 else n
  rw [← extendState_run_proj_eq (idealImpl pub X R) aux oa (∅, ∅) 0, support_map] at hz
  obtain ⟨z, hz, rfl⟩ := hz
  have hcnt := h.cnt_le_of_mem_support_run_extendState (idealImpl pub X R)
    (fun t _ _ _ n ↦ by by_cases hpt : p t <;> simp only [aux, hpt, ↓reduceIte, add_zero, le_refl])
    hz
  refine (simulateQ_run_preservesInv ((idealImpl pub X R).extendState aux)
    (fun st ↦ (D ∩ {t | (st.1.1 t).isSome}).encard ≤ st.2) ?_ oa _ ?_ z hz).trans ?_
  · rintro t ⟨st, n⟩ hinv w hw
    rw [QueryImpl.extendState_apply, mem_support_bind_iff] at hw
    obtain ⟨v, hv, hw⟩ := hw
    rw [support_pure, Set.mem_singleton_iff] at hw
    subst hw
    dsimp only
    have hsub : D ∩ {t' | (v.2.1 t').isSome} ⊆
        D ∩ {t' | (st.1 t').isSome} ∪ D ∩ {t' | .inl (.inr t') = t} :=
      fun t' ⟨hD, ht'⟩ ↦
        ((isSome_fst_apply_iff_of_mem_support_idealImpl hv t').1 ht').imp (⟨hD, ·⟩) (⟨hD, ·⟩)
    refine (Set.encard_le_encard hsub).trans ((Set.encard_union_le _ _).trans ?_)
    by_cases hpt : p t
    · have hone : (D ∩ {t' | .inl (.inr t') = t}).encard ≤ 1 :=
        Set.encard_le_one_iff.2 fun a b ha hb ↦ Sum.inr.inj (Sum.inl.inj (ha.2.trans hb.2.symm))
      simp only [aux, hpt, ↓reduceIte, Nat.cast_add, Nat.cast_one]
      exact add_le_add hinv hone
    · have hemp : D ∩ {t' | .inl (.inr t') = t} = ∅ :=
        Set.eq_empty_of_forall_notMem fun t' ht' ↦ hpt (ht'.2 ▸ hp t' ht'.1)
      simp only [aux, hpt, ↓reduceIte, hemp, Set.encard_empty, add_zero]
      exact hinv
  · simp only [QueryCache.empty_apply, Option.isSome_none, Bool.false_eq_true, Set.ofPred_false,
      Set.inter_empty, Set.encard_empty, Nat.cast_zero, le_refl]
  · exact_mod_cast hcnt.trans_eq (zero_add q)

/-! ## Averaging over the secret -/

/-- Under a query budget charging every public query at an encodable point, the flagged ideal
game run under a secret drawn from `ms` raises its flag with probability at most `q * ε`, where
`ε` bounds, for every public point, the chance that it encodes some derivation under the
secret. -/
theorem prEvent_flaggedIdealImpl_le_mul {ms : ProbComp S} {ε : ℝ≥0∞}
    (hε : ∀ t, Pr{let s ← ms}[t ∈ Set.range (E.enc s)] ≤ ε)
    {p : (pub.withDerivations X R).Domain → Prop} [DecidablePred p]
    (hp : ∀ s x, p (.inl (.inr (E.enc s x)))) {α : Type}
    {oa : OracleComp (pub.withDerivations X R) α} {q : ℕ} (h : IsQueryBoundP oa p q) :
    Pr{
      let s ← ms
      let z ← (simulateQ (E.flaggedIdealImpl s) oa).run ((∅, ∅), false)}[z.2.2 = true] ≤
      q * ε := by
  have hflag : ∀ s, Pr{let z ← (simulateQ (E.flaggedIdealImpl s) oa).run ((∅, ∅), false)}[
      z.2.2 = true] = Pr{let w ← (simulateQ (idealImpl pub X R) oa).run (∅, ∅)}[
      ∃ x, (w.2.1 (E.enc s x)).isSome] := fun s ↦ by
    rw [← E.map_run_simulateQ_flaggedIdealImpl s oa (∅, ∅) false, prEvent_map]
    exact prEvent_congr_of_support _ _ _ fun z hz ↦
      E.flag_eq_true_iff_of_mem_support_flaggedIdealImpl s oa hz
  have hswap : Pr{
      let s ← ms
      let z ← (simulateQ (E.flaggedIdealImpl s) oa).run ((∅, ∅), false)}[z.2.2 = true] =
      Pr{
        let s ← ms
        let w ← (simulateQ (idealImpl pub X R) oa).run (∅, ∅)}[
        ∃ x, (w.2.1 (E.enc s x)).isSome] := by
    let _ : MeasurableSpace S := ⊤
    simp only [prEvent_bind_bind_eq_lintegral_of_discrete]
    exact lintegral_congr hflag
  rw [hswap, OracleComp.prEvent_bind_bind_swap]
  refine (le_of_eq ?_).trans (prEvent_bind_le_of_forall_le_of_support
    ((simulateQ (idealImpl pub X R) oa).run (∅, ∅))
    (fun w ↦ do let s ← ms; return ∃ x, (w.2.1 (E.enc s x)).isSome) id fun w hw ↦ ?_)
  · simp only [id_eq, bind_pure]
  simp only [id_eq, bind_pure]
  have hcard := encard_inter_setOf_isSome_le_of_mem_support_idealImpl
    (D := ⋃ s, Set.range (E.enc s)) (fun t ht ↦ by
      obtain ⟨s, x, rfl⟩ := Set.mem_iUnion.1 ht
      exact hp s x) h hw
  have hfin := Set.finite_of_encard_le_coe hcard
  calc Pr{let s ← ms}[∃ x, (w.2.1 (E.enc s x)).isSome]
      ≤ Pr{let s ← ms}[∃ t ∈ hfin.toFinset, t ∈ Set.range (E.enc s)] :=
        prEvent_mono _ _ _ fun s ⟨x, hx⟩ ↦
          ⟨E.enc s x, hfin.mem_toFinset.2 ⟨Set.mem_iUnion.2 ⟨s, x, rfl⟩, hx⟩, x, rfl⟩
    _ ≤ ∑ t ∈ hfin.toFinset, Pr{let s ← ms}[t ∈ Set.range (E.enc s)] :=
        prEvent_exists_finset_le _ _ _
    _ ≤ hfin.toFinset.card • ε := Finset.sum_le_card_nsmul _ _ _ fun t _ ↦ hε t
    _ ≤ q * ε := by
        rw [nsmul_eq_mul]
        gcongr
        rw [hfin.encard_eq_coe_toFinset_card] at hcard
        exact_mod_cast hcard

/-- Coupled real game against the ideal game, for a secret drawn from `ms` and under a query
budget charging every public query at an encodable point: an event of the secret and of the
coupled game's output and split state, with the flag forgotten, is at most the same event in the
ideal game plus `q * ε`, where `ε` bounds, for every public point, the chance that it encodes some
derivation under the secret. -/
theorem prEvent_coupledImpl_le_add_mul {ms : ProbComp S} {ε : ℝ≥0∞}
    (hε : ∀ t, Pr{let s ← ms}[t ∈ Set.range (E.enc s)] ≤ ε)
    {p : (pub.withDerivations X R).Domain → Prop} [DecidablePred p]
    (hp : ∀ s x, p (.inl (.inr (E.enc s x)))) {α : Type}
    {oa : OracleComp (pub.withDerivations X R) α} {q : ℕ} (h : IsQueryBoundP oa p q)
    (P : S → α × SplitCache pub X R → Prop) :
    Pr{
      let s ← ms
      let z ← (simulateQ (E.coupledImpl s) oa).run ((∅, ∅), false)}[P s (z.1, z.2.1)] ≤
      Pr{let s ← ms; let z ← (simulateQ (idealImpl pub X R) oa).run (∅, ∅)}[P s z] +
        q * ε := by
  let _ : MeasurableSpace S := ⊤
  refine le_trans ?_ (add_le_add le_rfl (E.prEvent_flaggedIdealImpl_le_mul hε hp h))
  simp only [prEvent_bind_bind_eq_lintegral_of_discrete]
  exact (lintegral_mono fun s ↦ E.prEvent_coupledImpl_le_add s oa (P s)).trans
    (lintegral_add_left Measurable.of_discrete _).le

/-- Coupled real game against the ideal game, both extended by the same passive auxiliary state,
for a secret drawn from `ms` and under a query budget charging every public query at an
encodable point: an event of the secret and of the extended coupled game's output, split state
and auxiliary state is at most the same event in the extended ideal game plus `q * ε`, where `ε`
bounds, for every public point, the chance that it encodes some derivation under the secret. The
auxiliary update `aux s` may read the secret, the query, its answer, the split state before and
after the step and its own previous value, but not the flag. -/
theorem prEvent_coupledImpl_extendState_le_add_mul {Q : Type} (r₀ : Q)
    (aux : S → (t : (pub.withDerivations X R).Domain) → SplitCache pub X R →
      (pub.withDerivations X R).Range t → SplitCache pub X R → Q → Q)
    {ms : ProbComp S} {ε : ℝ≥0∞} (hε : ∀ t, Pr{let s ← ms}[t ∈ Set.range (E.enc s)] ≤ ε)
    {p : (pub.withDerivations X R).Domain → Prop} [DecidablePred p]
    (hp : ∀ s x, p (.inl (.inr (E.enc s x)))) {α : Type}
    {oa : OracleComp (pub.withDerivations X R) α} {q : ℕ} (h : IsQueryBoundP oa p q)
    (P : S → α × SplitCache pub X R × Q → Prop) :
    Pr{
      let s ← ms
      let z ← (simulateQ ((E.coupledImpl s).extendState fun t st u st' r ↦
        aux s t st.1 u st'.1 r) oa).run (((∅, ∅), false), r₀)}[P s (z.1, z.2.1.1, z.2.2)] ≤
      Pr{
        let s ← ms
        let z ← (simulateQ ((idealImpl pub X R).extendState (aux s)) oa).run ((∅, ∅), r₀)}[
        P s z] + q * ε := by
  let _ : MeasurableSpace S := ⊤
  refine le_trans ?_ (add_le_add le_rfl (E.prEvent_flaggedIdealImpl_le_mul hε hp h))
  simp only [prEvent_bind_bind_eq_lintegral_of_discrete]
  exact (lintegral_mono fun s ↦
    E.prEvent_coupledImpl_extendState_le_add s r₀ (aux s) oa (P s)).trans
    (lintegral_add_left Measurable.of_discrete _).le

/-- Real game against the ideal game, for a secret drawn from `ms` and under a query budget
charging every public query at an encodable point: an event of the secret and of the real game is
at most the event, read on the merged cache, in the ideal game, plus `q * ε`, where `ε` bounds,
for every public point, the chance that it encodes some derivation under the secret. -/
theorem prEvent_realImpl_le_add_mul {ms : ProbComp S} {ε : ℝ≥0∞}
    (hε : ∀ t, Pr{let s ← ms}[t ∈ Set.range (E.enc s)] ≤ ε)
    {p : (pub.withDerivations X R).Domain → Prop} [DecidablePred p]
    (hp : ∀ s x, p (.inl (.inr (E.enc s x)))) {α : Type}
    {oa : OracleComp (pub.withDerivations X R) α} {q : ℕ} (h : IsQueryBoundP oa p q)
    (P : S → α × pub.QueryCache → Prop) :
    Pr{let s ← ms; let z ← (simulateQ (E.realImpl s) oa).run ∅}[P s z] ≤
      Pr{
        let s ← ms
        let z ← (simulateQ (idealImpl pub X R) oa).run (∅, ∅)}[P s (z.1, E.merge s z.2)] +
        q * ε := by
  have hs (s : S) : (simulateQ (E.realImpl s) oa).run ∅ =
      Prod.map id (E.merge s ∘ Prod.fst) <$>
        (simulateQ (E.coupledImpl s) oa).run ((∅, ∅), false) := by
    rw [E.map_run_simulateQ_coupledImpl s oa ((∅, ∅), false), merge_empty]
  simp only [hs, bind_map_left]
  exact E.prEvent_coupledImpl_le_add_mul hε hp h fun s z ↦ P s (z.1, E.merge s z.2)

end SecretEncoding

/-! ## Query budgets in the derivation world

A probabilistic computation lifted into the derivation world makes only uniform-sampling queries,
so it spends nothing of a budget for a predicate that no sampling query satisfies. -/

namespace OracleComp

/-- A probabilistic computation lifted into `pub.withDerivations X R` makes no `p`-query when no
uniform-sampling query satisfies `p`. -/
theorem isQueryBoundP_liftM_withDerivations {ι : Type} {pub : OracleSpec ι} {X R : Type}
    {p : (pub.withDerivations X R).Domain → Prop} [DecidablePred p]
    (hp : ∀ n, ¬ p (.inl (.inl n))) {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftM oa : OracleComp (pub.withDerivations X R) α) p 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp only [liftM_pure, isQueryBoundP_pure]
  | query_bind t k ih =>
      simp only [liftM_bind]
      refine isQueryBoundP_bind ?_ fun x _ => ih x
      exact (isQueryBoundP_query_iff _ _ _).2 fun h => (hp t h).elim

end OracleComp
